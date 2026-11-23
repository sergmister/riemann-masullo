module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.Ch09_HardySobolev.Sec3

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b

import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Hardy–Sobolev topologies on adelic theta spaces

Masullo, §10.1, pp. 434–438. The parameter S indexes the finite places, with all
archimedean places included. Compact nonempty intervals are given by ordered endpoints.
The ambient weighted L² spaces here use full quotient Tamagawa measure, as in (10.1.1.5).
The comparison maps below give the change of norm to the canonical spaces of §9.2.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ" => SIdeleQuotient F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "C₁" => (ideleClassNorm F).ker
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "μₛ" => sLocalQuotientTamagawaMeasure F S
local notation "μ𝔽₁" => normOneIdeleClassTamagawaMeasure F
local notation "μₛ₁" => sLocalNormOneQuotientMeasure F S

-- These are the Borel structures used when defining the Tamagawa measures.
local instance instIdeleClassMeasurableSpaceSec1 : MeasurableSpace C𝔽 := borel _
local instance instSIdeleQuotientMeasurableSpaceSec1 : MeasurableSpace Jₛ := borel _
local instance instNormOneSIdeleQuotientMeasurableSpaceSec1 : MeasurableSpace J₁ := borel _
local instance instSAdeleMeasurableSpaceSec1 : MeasurableSpace (SAdeleRing F S) :=
  instMeasurableSpaceSAdeleRing F S

local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "mₛ" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    Jₛ →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "W𝔽(" α ", " β ", " s ")" => CompactIntervalSobolev μ𝔽 (logNorm(m𝔽)) α β s
local notation "Wₛ(" α ", " β ", " s ")" => CompactIntervalSobolev μₛ (logNorm(mₛ)) α β s
local notation "Θₛ" => SLocalAdelicThetaSpace F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "Θ₀" => GlobalPolarFreeThetaSpace F
local notation "θ𝔽(" f ")" => adelicTheta (f : ℬ₀).val
local notation "θₛ(" f ")" => sLocalAdelicThetaOnClasses F S f
local notation "ρₛ" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose

/-- Paper: (10.1.1.1), p. 434. Weighted global polar-free theta functions are
continuous and have continuous derivatives of every order along every continuous
real one-parameter subgroup. The function realization is injective. -/
theorem globalPolarFreeTheta_directionallySmooth (a : ℝ) :
    ∃ E : Θ₀ →ₗ[ℂ] (C𝔽 → ℂ), Injective E ∧
      (∀ f : ℬ₀, E (Submodule.Quotient.mk f) = modulationWeight m𝔽 a (θ𝔽(f))) ∧
      ∀ u : Θ₀, Continuous (E u) ∧
        ∀ γ : Multiplicative ℝ →ₜ* C𝔽,
          (∀ (g : C𝔽) (k : ℕ), ContDiff ℝ k (fun t : ℝ ↦ E u (γ (Multiplicative.ofAdd t) * g))) ∧
          ∀ n : ℕ, Continuous (fun g : C𝔽 ↦
            iteratedDeriv n (fun t : ℝ ↦ E u (γ (Multiplicative.ofAdd t) * g)) 0) := by sorry

-- TODO(paper-gap): The assertion preceding (10.1.1.2) on p. 434 and the open
-- half-line on p. 435 require care. Every compact subinterval gives a finite norm.
-- The supremum over an unbounded interval can be infinite on a single theta test.

open Filter Topology in
/-- On a bounded set of polar tests, theta decays like any power of the norm at both ends
with a common constant, the unit circle included. -/
private theorem existsUnique_globalThetaSobolevEmbedding_decay (B : Set (SchwartzBruhat (Multiplicative 𝔸[F])))
    (hB : Bornology.IsVonNBounded ℂ B) (hpol : ∀ f ∈ B, f ∈ adelePolarSubspace F) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C𝔽,
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|) := by
  obtain ⟨C, hC, h⟩ := adelicTheta_decay_bounded_threshold_one (F := F) B hB N
  refine ⟨C, hC, fun f hf g ↦ ?_⟩
  have hz := (mem_adelePolarSubspace f).mp (hpol f hf)
  have hpos (g : C𝔽) : 0 < (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hoff (g : C𝔽) (hg : Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) ≠ 0) :
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|) := by
    refine (h f hf g).2.2 hz.1 hz.2 ?_
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr (abs_pos.mpr hg))
  by_cases hg : Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) = 0
  · -- approach g along a norm section
    let σ : ℝ → C𝔽 := fun t ↦
      g * QuotientGroup.mk (canonicalIdeleNormSection F (sobolevLogEquiv t))
    have hσc : Continuous σ := continuous_const.mul
      (QuotientGroup.continuous_mk.comp
        ((canonicalIdeleNormSection_continuous F).comp sobolevLogEquiv.continuous))
    have hσ0 : σ 0 = g := by
      have h1 : sobolevLogEquiv 0 = 1 := by
        apply Units.ext; apply NNReal.coe_injective
        have := sobolevLogEquiv_log 0
        rw [Real.log_eq_zero] at this
        rcases this with h0 | h1 | hm1
        · exact absurd h0 (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
        · simpa using h1
        · exact absurd hm1 (by linarith [NNReal.coe_nonneg ((sobolevLogEquiv 0).val)])
      simp only [σ, h1, map_one, QuotientGroup.mk_one, mul_one]
    have hlog (t : ℝ) : Real.log (((ideleClassNorm F (σ t) : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) + t := by
      have hs : ideleClassNorm F (QuotientGroup.mk (canonicalIdeleNormSection F
          (sobolevLogEquiv t))) = sobolevLogEquiv t :=
        canonicalIdeleNormSection_rightInverse F _
      simp only [σ, map_mul, hs, Units.val_mul, NNReal.coe_mul]
      rw [Real.log_mul (hpos g).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne',
        sobolevLogEquiv_log]
    have hb : Continuous fun t ↦ C * Real.exp (-(N : ℝ) * |Real.log (((ideleClassNorm F (σ t) : ℝ≥0ˣ) : ℝ≥0) : ℝ)|) := by
      simp only [hlog]
      fun_prop
    have ht : Tendsto σ (𝓝[≠] 0) (𝓝 g) := hσ0 ▸ hσc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim := ((adelicTheta f).continuous.norm.tendsto g).comp ht
    have hblim : Tendsto (fun t ↦ C * Real.exp (-(N : ℝ) * |Real.log (((ideleClassNorm F (σ t) : ℝ≥0ˣ) : ℝ≥0) : ℝ)|)) (𝓝[≠] 0)
        (𝓝 (C * Real.exp (-(N : ℝ) * |Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|))) := by
      have := (hb.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      simpa only [hσ0] using this
    refine le_of_tendsto_of_tendsto hlim hblim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine hoff (σ t) ?_
    rw [hlog, hg, zero_add]
    exact ht
  · exact hoff g hg

/-- The two-sided exponential of the log norm is integrable for the Tamagawa measure. -/
private theorem existsUnique_globalThetaSobolevEmbedding_integrable :
    Integrable (fun g : C𝔽 ↦ Real.exp (-|Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|)) μ𝔽 := by
  have : BorelSpace C𝔽 := ⟨rfl⟩
  have : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  have : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have : SecondCountableTopology C𝔽 := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  have : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have : (μ𝔽).Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  let m : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let L : C𝔽 → ℝ := fun g ↦ Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)
  have hLm : Measurable L :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  have hLinv (g : C𝔽) : L g⁻¹ = -L g := by
    simp only [L, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  have hS : MeasurableSet (L ⁻¹' Ici 0) := hLm measurableSet_Ici
  have h₁ := integrableOn_exp_neg_logModule m hm μ𝔽 one_pos 0
  have hpos : IntegrableOn (fun g ↦ Real.exp (-|L g|)) (L ⁻¹' Ici 0) μ𝔽 := by
    refine h₁.congr_fun (fun g hg ↦ ?_) hS
    have hg' : 0 ≤ L g := hg
    change Real.exp (-(1 * L g)) = Real.exp (-|L g|)
    rw [one_mul, abs_of_nonneg hg']
  have hneg : IntegrableOn (fun g ↦ Real.exp (-|L g|)) (L ⁻¹' Iic 0) μ𝔽 := by
    have hinv : MeasurePreserving (Inv.inv : C𝔽 → C𝔽) μ𝔽 μ𝔽 := Measure.measurePreserving_inv μ𝔽
    have e := (hinv.integrableOn_comp_preimage (MeasurableEquiv.inv C𝔽).measurableEmbedding
      (f := fun g ↦ Real.exp (-|L g|)) (s := L ⁻¹' Ici 0)).mpr hpos
    have hset : (Inv.inv : C𝔽 → C𝔽) ⁻¹' (L ⁻¹' Ici 0) = L ⁻¹' Iic 0 := by
      ext g
      simp only [mem_preimage, mem_Ici, mem_Iic, hLinv, Left.nonneg_neg_iff]
    have hfun : (fun g ↦ Real.exp (-|L g|)) ∘ (Inv.inv : C𝔽 → C𝔽) = fun g ↦ Real.exp (-|L g|) := by
      funext g
      simp only [comp_apply, hLinv, abs_neg]
    rwa [hset, hfun] at e
  have hU : L ⁻¹' Ici 0 ∪ L ⁻¹' Iic 0 = univ := by
    ext g
    simp only [mem_union, mem_preimage, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 (L g)
  have := hpos.union hneg
  rw [hU, integrableOn_univ] at this
  exact this

/-- With enough decay, the weight |g|^a, the theta bound and the interval density together are
dominated by exp(-|log |g||). -/
private theorem existsUnique_globalThetaSobolevEmbedding_real (a α β s C x : ℝ) (N : ℕ)
    (hs : 0 ≤ s) (hN : |a| + |α| + |β| + s + 1 ≤ N) :
    Real.exp (a * x) ^ 2 * (C * Real.exp (-(N : ℝ) * |x|)) ^ 2 * intervalSobolevDensity α β s x ≤
      C ^ 2 * Real.exp (-|x|) := by
  have hx := abs_nonneg x
  have hax : a * x ≤ |a| * |x| := (le_abs_self _).trans (abs_mul a x).le
  have hαx : α * x ≤ |α| * |x| := (le_abs_self _).trans (abs_mul α x).le
  have hβx : β * x ≤ |β| * |x| := (le_abs_self _).trans (abs_mul β x).le
  have h1 : Real.exp (a * x) ^ 2 ≤ Real.exp (2 * |a| * |x|) := by
    rw [sq, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : max (Real.exp (2 * α * x)) (Real.exp (2 * β * x)) ≤
      Real.exp (2 * (|α| + |β|) * |x|) := by
    refine max_le (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) <;>
      nlinarith [abs_nonneg α, abs_nonneg β]
  have h3 : (1 + x ^ 2) ^ (s / 2) ≤ Real.exp (s * |x|) := by
    have h31 : 1 + x ^ 2 ≤ Real.exp (2 * |x|) := by
      have := Real.add_one_le_exp |x|
      calc 1 + x ^ 2 ≤ (|x| + 1) ^ 2 := by nlinarith [sq_abs x]
        _ ≤ Real.exp |x| ^ 2 := by gcongr
        _ = Real.exp (2 * |x|) := by rw [sq, ← Real.exp_add]; ring_nf
    calc (1 + x ^ 2) ^ (s / 2) ≤ Real.exp (2 * |x|) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) h31 (by positivity)
      _ = Real.exp (s * |x|) := by rw [← Real.exp_mul]; ring_nf
  have h4 : (C * Real.exp (-(N : ℝ) * |x|)) ^ 2 = C ^ 2 * Real.exp (-(2 * N) * |x|) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  unfold intervalSobolevDensity
  rw [h4]
  calc _ ≤ Real.exp (2 * |a| * |x|) * (C ^ 2 * Real.exp (-(2 * N) * |x|)) *
        (Real.exp (2 * (|α| + |β|) * |x|) * Real.exp (s * |x|)) := by
        gcongr
    _ = C ^ 2 * Real.exp ((2 * |a| - 2 * N + 2 * (|α| + |β|) + s) * |x|) := by
        rw [show (2 * |a| - 2 * N + 2 * (|α| + |β|) + s) * |x| =
          2 * |a| * |x| + -(2 * N) * |x| + 2 * (|α| + |β|) * |x| + s * |x| by ring,
          Real.exp_add, Real.exp_add, Real.exp_add]
        ring
    _ ≤ C ^ 2 * Real.exp (-|x|) := by
        gcongr
        nlinarith [abs_nonneg a, abs_nonneg α, abs_nonneg β]

/-- A function dominated in the weighted L² sense by an integrable majorant belongs to the
weighted L² space. -/
private theorem existsUnique_globalThetaSobolevEmbedding_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : X → ℝ) (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) (φ : X → ℂ)
    (hφ : AEStronglyMeasurable φ μ) (H : X → ℝ) (hH : Integrable H μ) (q : ℝ)
    (hb : ∀ x, ‖φ x‖ ^ 2 * ρ x ≤ q ^ 2 * H x) :
    MemLp φ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
  have hν : μ.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) ≪ μ :=
    withDensity_absolutelyContinuous _ _
  refine (memLp_two_iff_integrable_sq_norm (hφ.mono_ac hν)).2 ?_
  refine (integrable_withDensity_iff hρ.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2 ?_
  refine (hH.const_mul (q ^ 2)).mono' ((hφ.norm.pow 2).mul
    hρ.ennreal_ofReal.ennreal_toReal.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
  rw [ENNReal.toReal_ofReal (hpos x).le,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hpos x).le)]
  exact hb x

/-- The weighted theta function of a test with two-sided decay is dominated pointwise by
exp(-|log |g||). -/
private theorem existsUnique_globalThetaSobolevEmbedding_pointwise (a α β s : ℝ) (hs : 0 ≤ s)
    (N : ℕ) (hN : |a| + |α| + |β| + s + 1 ≤ N) (C : ℝ) (f : (SchwartzBruhat (Multiplicative 𝔸[F])))
    (hf : ∀ g : C𝔽, ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|)) (g : C𝔽) :
    ‖modulationWeight (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
        C𝔽 →ₜ* ℝ≥0ˣ) a (adelicTheta f) g‖ ^ 2 *
      intervalSobolevDensity α β s (Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) ≤ C ^ 2 * Real.exp (-|Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|) := by
  have hn : 0 < (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hw : ‖modulationWeight (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
      C𝔽 →ₜ* ℝ≥0ˣ) a (adelicTheta f) g‖ =
        Real.exp (a * Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) * ‖adelicTheta f g‖ := by
    change ‖(((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f g‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _),
      Real.rpow_def_of_pos hn, mul_comm (Real.log _) a]
  have hd : 0 ≤ intervalSobolevDensity α β s (Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) := by
    unfold intervalSobolevDensity
    exact mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _)) (by positivity)
  refine le_trans ?_ (existsUnique_globalThetaSobolevEmbedding_real a α β s C _ N hs hN)
  rw [hw, mul_pow]
  gcongr
  exact hf g

/-- A linear family of functions that all lie in L² gives a linear map into L². -/
private theorem existsUnique_globalThetaSobolevEmbedding_toLp {V X : Type*} [AddCommGroup V]
    [Module ℂ V] [MeasurableSpace X] (ν : Measure X) (Ψ : V →ₗ[ℂ] (X → ℂ))
    (h : ∀ v, MemLp (Ψ v) 2 ν) :
    ∃ L : V →ₗ[ℂ] Lp ℂ 2 ν, ∀ v, (L v : X → ℂ) =ᵐ[ν] Ψ v := by
  have hadd (v w : V) : (h (v + w)).toLp (Ψ (v + w)) = (h v).toLp (Ψ v) + (h w).toLp (Ψ w) := by
    apply Lp.ext
    filter_upwards [(h (v + w)).coeFn_toLp, (h v).coeFn_toLp, (h w).coeFn_toLp,
      Lp.coeFn_add ((h v).toLp (Ψ v)) ((h w).toLp (Ψ w))] with x h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3, map_add, Pi.add_apply]
  have hsmul (c : ℂ) (v : V) : (h (c • v)).toLp (Ψ (c • v)) = c • (h v).toLp (Ψ v) := by
    apply Lp.ext
    filter_upwards [(h (c • v)).coeFn_toLp, (h v).coeFn_toLp,
      Lp.coeFn_smul c ((h v).toLp (Ψ v))] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, map_smul, Pi.smul_apply]
  let L : V →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun v ↦ (h v).toLp (Ψ v)
      map_add' := hadd
      map_smul' := hsmul }
  exact ⟨L, fun v ↦ (h v).coeFn_toLp⟩

/-- A continuous linear surjection onto ℂ² has a continuous linear projection onto its kernel.
Stated for an abstract space, so that it elaborates without unfolding the Schwartz–Bruhat
instances. -/
private theorem existsUnique_globalThetaSobolevEmbedding_proj_abstract {M : Type*}
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul ℂ M] (P : M →L[ℂ] ℂ × ℂ) (hP : Surjective P) :
    ∃ π : M →L[ℂ] M, (∀ f, P (π f) = 0) ∧ ∀ f, P f = 0 → π f = f := by
  obtain ⟨h₁, hh₁⟩ := hP (1, 0)
  obtain ⟨h₂, hh₂⟩ := hP (0, 1)
  let π : M →L[ℂ] M := ContinuousLinearMap.id ℂ M -
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp P).smulRight h₁ -
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp P).smulRight h₂
  have hπ (f : M) : π f = f - (P f).1 • h₁ - (P f).2 • h₂ := rfl
  refine ⟨π, fun f ↦ ?_, fun f hf ↦ ?_⟩
  · rw [hπ, map_sub, map_sub, map_smul, map_smul, hh₁, hh₂]
    ext <;> simp
  · rw [hπ, hf]
    simp

/-- A continuous linear projection of the adelic tests onto the polar subspace. -/
private theorem existsUnique_globalThetaSobolevEmbedding_proj :
    ∃ π : (SchwartzBruhat (Multiplicative 𝔸[F])) →L[ℂ] (SchwartzBruhat (Multiplicative 𝔸[F])), (∀ f, π f ∈ adelePolarSubspace F) ∧
      ∀ f ∈ adelePolarSubspace F, π f = f := by
  let : ContinuousSMul ℂ (SchwartzBruhat (Multiplicative 𝔸[F])) := (SchwartzBruhat.withSeminorms _).continuousSMul
  obtain ⟨π, h₁, h₂⟩ := existsUnique_globalThetaSobolevEmbedding_proj_abstract
    ⟨adelePolarValues (F := F), adelePolarValues_continuous⟩ adelePolarValues_surjective
  exact ⟨π, fun f ↦ LinearMap.mem_ker.mpr (h₁ f), fun f hf ↦ h₂ f (LinearMap.mem_ker.mp hf)⟩

/-- On a first-countable space, a linear map into a normed space that is bounded on the images
of bounded sets under a continuous linear map is continuous after that map. -/
private theorem existsUnique_globalThetaSobolevEmbedding_stage {E M V : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [FirstCountableTopology E] [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (i : E →L[ℂ] M) (Λ : M →ₗ[ℂ] V)
    (hΛ : ∀ B : Set M, Bornology.IsVonNBounded ℂ B → ∃ r, ∀ f ∈ B, ‖Λ f‖ ≤ r) :
    Continuous (Λ.comp (i : E →ₗ[ℂ] M)) := by
  refine (Λ.comp (i : E →ₗ[ℂ] M)).continuous_of_locally_bounded fun S hS ↦ ?_
  obtain ⟨r, hr⟩ := hΛ _ (hS.image i)
  refine (NormedSpace.isVonNBounded_iff ℂ).mpr (isBounded_iff_forall_norm_le.mpr ⟨r, ?_⟩)
  rintro _ ⟨f, hf, rfl⟩
  exact hr _ ⟨f, hf, rfl⟩

/-- A linear map from the adelic tests into a normed space that is bounded on bounded sets is
continuous: each elementary stage is metrizable. -/
private theorem existsUnique_globalThetaSobolevEmbedding_continuous {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (Λ : (SchwartzBruhat (Multiplicative 𝔸[F])) →ₗ[ℂ] V)
    (hΛ : ∀ B : Set (SchwartzBruhat (Multiplicative 𝔸[F])), Bornology.IsVonNBounded ℂ B → ∃ r, ∀ f ∈ B, ‖Λ f‖ ≤ r) :
    Continuous Λ := by
  let : LocallyCompactSpace (Multiplicative 𝔸[F]) := adeleGroupLocallyCompact F
  let : T2Space (Multiplicative 𝔸[F]) := adeleGroupT2 F
  apply SchwartzBruhat.continuous_of_continuous_comp_ofStage
  intro a e
  let : FirstCountableTopology (SchwartzBruhatStage e) :=
    elementarySchwartz_withSeminorms.firstCountableTopology
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  exact existsUnique_globalThetaSobolevEmbedding_stage
    ⟨SchwartzBruhat.ofStage a e, SchwartzBruhat.continuous_ofStage a e⟩ Λ hΛ

/-- Weighted theta of the polar projection is a continuous linear map from the adelic tests into
the weighted L² space; on polar tests it is the weighted theta function. -/
private theorem existsUnique_globalThetaSobolevEmbedding_clm (a α β s : ℝ) (hs : 0 ≤ s) :
    ∃ Λ : (SchwartzBruhat (Multiplicative 𝔸[F])) →L[ℂ] W𝔽(α, β, s), ∀ f ∈ adelePolarSubspace F,
      (Λ f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a (adelicTheta f) := by
  have : BorelSpace C𝔽 := ⟨rfl⟩
  have : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  have : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have : SecondCountableTopology C𝔽 := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  have : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  obtain ⟨π, hπP, hπid⟩ := existsUnique_globalThetaSobolevEmbedding_proj (F := F)
  let ρ : C𝔽 → ℝ := fun g ↦ if (false : Bool) then (intervalSobolevDensity α β s (logNorm(m𝔽) g))⁻¹
    else intervalSobolevDensity α β s (logNorm(m𝔽) g)
  have hρ (g : C𝔽) : ρ g = intervalSobolevDensity α β s (Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) := by
    simp only [ρ, Bool.false_eq_true, ite_false]
    rfl
  have hLc : Continuous fun g : C𝔽 ↦ Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hρpos (g : C𝔽) : 0 < ρ g := by
    rw [hρ]
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  have hρm : Measurable ρ := by
    have : ρ = fun g ↦ intervalSobolevDensity α β s (Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)) := funext hρ
    rw [this]
    unfold intervalSobolevDensity
    exact (by fun_prop : Continuous _).measurable
  let ν := (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (ρ g)
  have hμν : μ𝔽 ≪ ν := withDensity_absolutelyContinuous' hρm.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (hρpos g)).ne')
  let Ψ : (SchwartzBruhat (Multiplicative 𝔸[F])) →ₗ[ℂ] (C𝔽 → ℂ) := (modulationWeight m𝔽 a) ∘ₗ
    (ContinuousMap.coeFnLinearMap ℂ) ∘ₗ (adelicThetaLinearMap F) ∘ₗ π.toLinearMap
  have hΨ (f : (SchwartzBruhat (Multiplicative 𝔸[F]))) : Ψ f = modulationWeight m𝔽 a (adelicTheta (π f)) := rfl
  let N : ℕ := ⌈|a| + |α| + |β| + s + 1⌉₊
  have hN : |a| + |α| + |β| + s + 1 ≤ N := Nat.le_ceil _
  have H := existsUnique_globalThetaSobolevEmbedding_integrable (F := F)
  -- a bound on a bounded set of tests
  have hbound (B : Set (SchwartzBruhat (Multiplicative 𝔸[F]))) (hB : Bornology.IsVonNBounded ℂ B) :
      ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g, ‖Ψ f g‖ ^ 2 * ρ g ≤ C ^ 2 * Real.exp (-|Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|) := by
    obtain ⟨C, hC, hdec⟩ := existsUnique_globalThetaSobolevEmbedding_decay (π '' B)
      (hB.image π) (fun _ ⟨f, _, hf⟩ ↦ hf ▸ hπP f) N
    refine ⟨C, hC, fun f hf g ↦ ?_⟩
    rw [hρ, hΨ]
    exact existsUnique_globalThetaSobolevEmbedding_pointwise a α β s hs N hN C (π f)
      (hdec _ ⟨f, hf, rfl⟩) g
  have hcont (f : (SchwartzBruhat (Multiplicative 𝔸[F]))) : Continuous (Ψ f) := by
    rw [hΨ]
    exact (Complex.continuous_ofReal.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (m𝔽).continuous)).rpow_const fun g ↦
        Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')).mul (adelicTheta (π f)).continuous
  have hmem (f : (SchwartzBruhat (Multiplicative 𝔸[F]))) : MemLp (Ψ f) 2 ν := by
    obtain ⟨C, -, hC⟩ := hbound {f} (Bornology.isVonNBounded_singleton f)
    exact existsUnique_globalThetaSobolevEmbedding_memLp μ𝔽 ρ hρm hρpos (Ψ f)
      (hcont f).aestronglyMeasurable _ H C (hC f rfl)
  obtain ⟨L, hL⟩ := existsUnique_globalThetaSobolevEmbedding_toLp ν Ψ hmem
  have hrep (f : (SchwartzBruhat (Multiplicative 𝔸[F]))) : (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] Ψ f := hμν.ae_eq (hL f)
  have hLc : Continuous L := by
    refine existsUnique_globalThetaSobolevEmbedding_continuous L fun B hB ↦ ?_
    obtain ⟨C, hC, hCb⟩ := hbound B hB
    exact ⟨C * Real.sqrt (∫ g, Real.exp (-|Real.log (((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ)|) ∂μ𝔽), fun f hf ↦
      weightedL2_le_majorant hρm hρpos (L f) (Ψ f) (hrep f) _ H C hC.le (hCb f hf)⟩
  refine ⟨⟨L, hLc⟩, fun f hf ↦ (hrep f).trans ?_⟩
  rw [hΨ, hπid f hf]

/-- A continuous linear map that vanishes on a submodule exactly where a linear map does descends
to a unique injective continuous linear map of the quotient with a prescribed value on each
class. Stated for abstract modules, so that it elaborates without unfolding the Schwartz–Bruhat
instances. -/
private theorem existsUnique_globalThetaSobolevEmbedding_assemble {M N V : Type*}
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [AddCommGroup N] [Module ℂ N]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (P : Submodule ℂ M) (θ : M →ₗ[ℂ] N)
    (Λ : M →L[ℂ] V) (S : P → V → Prop) (hS : ∀ f : P, S f (Λ f))
    (huniq : ∀ f v w, S f v → S f w → v = w) (hker : ∀ f : P, θ f = 0 → Λ f = 0)
    (hinj : ∀ f : P, Λ f = 0 → θ f = 0) :
    ∃! E : (P ⧸ (LinearMap.ker θ).comap P.subtype) →L[ℂ] V,
      Injective E ∧ ∀ f : P, S f (E (Submodule.Quotient.mk f)) := by
  set Q := (LinearMap.ker θ).comap P.subtype
  let Λ₀ : P →L[ℂ] V := Λ.comp P.subtypeL
  have hQ : Q ≤ Λ₀.ker := fun f hf ↦ hker f hf
  let E := Q.liftQL Λ₀ hQ
  have hE (f : P) : E (Submodule.Quotient.mk f) = Λ f := rfl
  refine ⟨E, ⟨?_, fun f ↦ (hE f).symm ▸ hS f⟩, fun E' hE' ↦ ?_⟩
  · refine (injective_iff_map_eq_zero E).mpr fun x hx ↦ ?_
    induction x using Submodule.Quotient.induction_on with
    | H f => exact (Submodule.Quotient.mk_eq_zero Q).mpr (hinj f ((hE f).symm.trans hx))
  · refine ContinuousLinearMap.ext fun x ↦ ?_
    induction x using Submodule.Quotient.induction_on with
    | H f => exact huniq f _ _ (hE'.2 f) ((hE f).symm ▸ hS f)

/-- Two weighted L² classes with the same representative almost everywhere are equal. -/
private theorem existsUnique_globalThetaSobolevEmbedding_uniq {α β s : ℝ} (φ : C𝔽 → ℂ)
    (v w : W𝔽(α, β, s)) (hv : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] φ) (hw : (w : C𝔽 → ℂ) =ᵐ[μ𝔽] φ) : v = w :=
  Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq (hv.trans hw.symm))

/-- The Tamagawa measure is absolutely continuous with respect to the weighted measure, whose
density is positive. -/
private theorem existsUnique_globalThetaSobolevEmbedding_ac (α β s : ℝ) :
    μ𝔽 ≪ (μ𝔽).withDensity fun g ↦ ENNReal.ofReal
      (if (false : Bool) then (intervalSobolevDensity α β s (logNorm(m𝔽) g))⁻¹
        else intervalSobolevDensity α β s (logNorm(m𝔽) g)) := by
  have : BorelSpace C𝔽 := ⟨rfl⟩
  have : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  have : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have : SecondCountableTopology C𝔽 := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  have : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hl : Continuous fun g : C𝔽 ↦ Real.log (((m𝔽) g).val : ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  simp only [Bool.false_eq_true, ite_false]
  refine withDensity_absolutelyContinuous' ?_ (.of_forall fun g ↦ ?_)
  · unfold intervalSobolevDensity
    refine (((Real.continuous_exp.comp (continuous_const.mul hl)).max
      (Real.continuous_exp.comp (continuous_const.mul hl))).mul
      ((continuous_const.add (hl.pow 2)).rpow_const fun g ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')).measurable.ennreal_ofReal.aemeasurable
  · refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)

/-- The weighted theta class of a test whose theta vanishes is zero. -/
private theorem existsUnique_globalThetaSobolevEmbedding_ker {a α β s : ℝ}
    (Λ : (SchwartzBruhat (Multiplicative 𝔸[F])) →L[ℂ] W𝔽(α, β, s)) (f : (SchwartzBruhat (Multiplicative 𝔸[F])))
    (hΛ : (Λ f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a (adelicTheta f))
    (hf : adelicThetaLinearMap F f = 0) : Λ f = 0 := by
  have hθ : (adelicTheta f : C𝔽 → ℂ) = 0 :=
    congrArg (fun c : C(C𝔽, ℂ) ↦ (c : C𝔽 → ℂ)) hf
  have hzero : modulationWeight m𝔽 a (adelicTheta f) = 0 := by
    rw [hθ, map_zero]
  apply Lp.ext
  exact ((withDensity_absolutelyContinuous _ _).ae_eq (hzero ▸ hΛ)).trans
    (Lp.coeFn_zero _ _ _).symm

/-- A test whose weighted theta class is zero has vanishing theta. -/
private theorem existsUnique_globalThetaSobolevEmbedding_inj {a α β s : ℝ}
    (Λ : (SchwartzBruhat (Multiplicative 𝔸[F])) →L[ℂ] W𝔽(α, β, s)) (f : (SchwartzBruhat (Multiplicative 𝔸[F])))
    (hΛ : (Λ f : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a (adelicTheta f)) (hf : Λ f = 0) :
    adelicThetaLinearMap F f = 0 := by
  have : BorelSpace C𝔽 := ⟨rfl⟩
  have : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  have : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have : SecondCountableTopology C𝔽 := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  have : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have h0 : (0 : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a (adelicTheta f) := by
    rw [hf] at hΛ
    exact ((existsUnique_globalThetaSobolevEmbedding_ac α β s).ae_eq
      (Lp.coeFn_zero _ _ _)).symm.trans hΛ
  have h1 : (0 : C𝔽 → ℂ) =ᵐ[μ𝔽] adelicTheta f := by
    filter_upwards [h0] with g hg
    have hn : (((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) a).ne'
    have hg' : (0 : ℂ) = (((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) ^ a : ℝ) : ℂ) * adelicTheta f g := hg
    exact ((mul_eq_zero.mp hg'.symm).resolve_left hn).symm
  have h2 := (Continuous.ae_eq_iff_eq μ𝔽 continuous_zero (adelicTheta f).continuous).mp h1
  exact ContinuousMap.ext fun g ↦ (congrFun h2 g).symm

/-- Paper: (10.1.1.2), p. 434. Weighting the global polar-free theta function
gives a continuous injection into the compact-interval Sobolev space. -/
theorem existsUnique_globalThetaSobolevEmbedding (a α β s : ℝ) (_hI : α ≤ β) (_hs : 0 ≤ s) :
    ∃! E : Θ₀ →L[ℂ] W𝔽(α, β, s), Injective E ∧
      ∀ f : ℬ₀, (E (Submodule.Quotient.mk f) : C𝔽 → ℂ) =ᵐ[μ𝔽]
        modulationWeight m𝔽 a (θ𝔽(f)) := by
  obtain ⟨Λ, hΛ⟩ := existsUnique_globalThetaSobolevEmbedding_clm (F := F) a α β s _hs
  exact existsUnique_globalThetaSobolevEmbedding_assemble (adelePolarSubspace F)
    (adelicThetaLinearMap F) Λ
    (fun f v ↦ (v : C𝔽 → ℂ) =ᵐ[μ𝔽] modulationWeight m𝔽 a (θ𝔽(f))) (fun f ↦ hΛ f f.2)
    (fun f ↦ existsUnique_globalThetaSobolevEmbedding_uniq _)
    (fun f hf ↦ existsUnique_globalThetaSobolevEmbedding_ker Λ f (hΛ f f.2) hf)
    (fun f hf ↦ existsUnique_globalThetaSobolevEmbedding_inj Λ f (hΛ f f.2) hf)

local notation "E𝔽(" a ", " hI ", " hs ")" =>
  (existsUnique_globalThetaSobolevEmbedding (F := F) a _ _ _ hI hs).exists.choose

variable (F) in
/-- Paper: Definition 10.1.1.1(1), p. 434. Take the closure of the weighted
polar-free theta image in the compact-interval Sobolev space of idele classes. -/
abbrev globalThetaSobolev (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    Submodule ℂ W𝔽(α, β, s) :=
  (E𝔽(a, hI, hs).toLinearMap.range).topologicalClosure

local notation "H𝔽(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs

-- TODO(paper-gap): (10.1.1.5) requires a + α > 0. For ℚ with only the real place,
-- the Gaussian has theta value tending to 2 at norm zero, giving divergence at a + α = 0.

/-- On a group with a modulation, exp(-δ |log |g||) is integrable for an inversion-invariant
Haar measure. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_integrable {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.Regular] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun g ↦ Real.exp (-(δ * |Real.log ((m g).val : ℝ)|))) μ := by
  let L : G → ℝ := fun g ↦ Real.log ((m g).val : ℝ)
  have hLm : Measurable L :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  have hLinv (g : G) : L g⁻¹ = -L g := by
    simp only [L, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  have hS : MeasurableSet (L ⁻¹' Ici 0) := hLm measurableSet_Ici
  have h₁ := integrableOn_exp_neg_logModule m hm μ hδ 0
  have hpos : IntegrableOn (fun g ↦ Real.exp (-(δ * |L g|))) (L ⁻¹' Ici 0) μ := by
    refine h₁.congr_fun (fun g hg ↦ ?_) hS
    have hg' : 0 ≤ L g := hg
    change Real.exp (-(δ * L g)) = Real.exp (-(δ * |L g|))
    rw [abs_of_nonneg hg']
  have hneg : IntegrableOn (fun g ↦ Real.exp (-(δ * |L g|))) (L ⁻¹' Iic 0) μ := by
    have hinv : MeasurePreserving (Inv.inv : G → G) μ μ := Measure.measurePreserving_inv μ
    have e := (hinv.integrableOn_comp_preimage (MeasurableEquiv.inv G).measurableEmbedding
      (f := fun g ↦ Real.exp (-(δ * |L g|))) (s := L ⁻¹' Ici 0)).mpr hpos
    have hset : (Inv.inv : G → G) ⁻¹' (L ⁻¹' Ici 0) = L ⁻¹' Iic 0 := by
      ext g
      simp only [mem_preimage, mem_Ici, mem_Iic, hLinv, Left.nonneg_neg_iff]
    have hfun : (fun g ↦ Real.exp (-(δ * |L g|))) ∘ (Inv.inv : G → G) =
        fun g ↦ Real.exp (-(δ * |L g|)) := by
      funext g
      simp only [comp_apply, hLinv, abs_neg]
    rwa [hset, hfun] at e
  have hU : L ⁻¹' Ici 0 ∪ L ⁻¹' Iic 0 = univ := by
    ext g
    simp only [mem_union, mem_preimage, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 (L g)
  have := hpos.union hneg
  rw [hU, integrableOn_univ] at this
  exact this

/-- The polynomial factor of the interval density grows more slowly than any exponential. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_poly (s η x : ℝ) (hs : 0 ≤ s)
    (hη : 0 < η) : (1 + x ^ 2) ^ (s / 2) ≤ (1 + η⁻¹) ^ s * Real.exp (s * η * |x|) := by
  have hx := abs_nonneg x
  have h1 : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [sq_abs x]
  have h2 : 1 + |x| ≤ (1 + η⁻¹) * Real.exp (η * |x|) := by
    have he := Real.add_one_le_exp (η * |x|)
    have hone : 1 ≤ Real.exp (η * |x|) := Real.one_le_exp (by positivity)
    have hx' : |x| ≤ η⁻¹ * Real.exp (η * |x|) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hη]
      linarith
    nlinarith
  calc (1 + x ^ 2) ^ (s / 2) ≤ ((1 + |x|) ^ 2) ^ (s / 2) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
    _ = (1 + |x|) ^ s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
    _ ≤ ((1 + η⁻¹) * Real.exp (η * |x|)) ^ s :=
        Real.rpow_le_rpow (by positivity) h2 hs
    _ = (1 + η⁻¹) ^ s * Real.exp (s * η * |x|) := by
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
        ring_nf

/-- With the S-local bound, decay at large norm and growth no faster than |g|^(-(a+α)/2) at small
norm, the weight |g|^a and the interval density are dominated by exp(-δ|log |g||). -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_real (a α β s C x η : ℝ) (N : ℕ)
    (hs : 0 ≤ s) (hI : α ≤ β) (hN : |a| + |α| + |β| + s + 1 ≤ N) (hη : 0 < η) (hη1 : η ≤ 1)
    (hsη : s * η ≤ (a + α) / 2) (hp : 0 < a + α) :
    Real.exp (a * x) ^ 2 *
        (C * Real.exp (-(N : ℝ) * max x 0 - (a + α) / 2 * min x 0)) ^ 2 *
          intervalSobolevDensity α β s x ≤
      (1 + η⁻¹) ^ s * C ^ 2 * Real.exp (-(min 1 ((a + α) / 2) * |x|)) := by
  have hpoly := existsUnique_sLocalThetaSobolevEmbedding_poly s η x hs hη
  have hK : 0 ≤ (1 + η⁻¹) ^ s := by positivity
  have hsη0 : 0 ≤ s * η := mul_nonneg hs hη.le
  have hsη1 : s * η ≤ s := mul_le_of_le_one_right hs hη1
  unfold intervalSobolevDensity
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, min_eq_right hx, abs_of_nonneg hx]
    rw [abs_of_nonneg hx] at hpoly
    have hmax : max (Real.exp (2 * α * x)) (Real.exp (2 * β * x)) ≤
        Real.exp (2 * (|α| + |β|) * x) := by
      refine max_le (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) <;>
        nlinarith [le_abs_self α, le_abs_self β, abs_nonneg α, abs_nonneg β]
    calc _ ≤ Real.exp (a * x) ^ 2 * (C * Real.exp (-(N : ℝ) * x - (a + α) / 2 * 0)) ^ 2 *
          (Real.exp (2 * (|α| + |β|) * x) * ((1 + η⁻¹) ^ s * Real.exp (s * η * x))) := by
          gcongr
      _ = (1 + η⁻¹) ^ s * C ^ 2 *
          Real.exp ((2 * a - 2 * N + 2 * (|α| + |β|) + s * η) * x) := by
          rw [show (2 * a - 2 * N + 2 * (|α| + |β|) + s * η) * x =
            a * x + a * x + (-(N : ℝ) * x - (a + α) / 2 * 0) + (-(N : ℝ) * x - (a + α) / 2 * 0) +
              2 * (|α| + |β|) * x + s * η * x by ring]
          simp only [Real.exp_add]
          ring
      _ ≤ (1 + η⁻¹) ^ s * C ^ 2 * Real.exp (-(min 1 ((a + α) / 2) * x)) := by
          gcongr
          have hc : 2 * a - 2 * N + 2 * (|α| + |β|) + s * η ≤ -min 1 ((a + α) / 2) := by
            linarith [min_le_left 1 ((a + α) / 2), le_abs_self a]
          have := mul_le_mul_of_nonneg_right hc hx
          linarith
  · rw [max_eq_right hx, min_eq_left hx, abs_of_nonpos hx]
    rw [abs_of_nonpos hx] at hpoly
    have hmax : max (Real.exp (2 * α * x)) (Real.exp (2 * β * x)) = Real.exp (2 * α * x) :=
      max_eq_left (Real.exp_le_exp.mpr (by nlinarith))
    rw [hmax]
    calc _ ≤ Real.exp (a * x) ^ 2 * (C * Real.exp (-(N : ℝ) * 0 - (a + α) / 2 * x)) ^ 2 *
          (Real.exp (2 * α * x) * ((1 + η⁻¹) ^ s * Real.exp (s * η * -x))) := by
          gcongr
      _ = (1 + η⁻¹) ^ s * C ^ 2 * Real.exp ((a + α - s * η) * x) := by
          rw [show (a + α - s * η) * x =
            a * x + a * x + (-(N : ℝ) * 0 - (a + α) / 2 * x) + (-(N : ℝ) * 0 - (a + α) / 2 * x) +
              2 * α * x + s * η * -x by ring]
          simp only [Real.exp_add]
          ring
      _ ≤ (1 + η⁻¹) ^ s * C ^ 2 * Real.exp (-(min 1 ((a + α) / 2) * -x)) := by
          gcongr
          have := min_le_right 1 ((a + α) / 2)
          nlinarith

open Filter Topology in
/-- On a bounded set of tests, S-local theta decays like any power of the norm above norm one and
grows no faster than |g|^(-ε) below it, with a common constant, the unit circle included. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_decay (B : Set ℬₛ)
    (hB : Bornology.IsVonNBounded ℂ B) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Jₛ, ‖θₛ(f) g‖ ≤
      C * Real.exp (-(N : ℝ) * max (logNorm(mₛ) g) 0 - ε * min (logNorm(mₛ) g) 0) := by
  obtain ⟨K₁, hK₁, h₁⟩ := sLocalAdelicTheta_decay_bounded_threshold_one F S B hB N
  obtain ⟨K₂, hK₂, h₂⟩ := sLocalAdelicTheta_norm_pow_bounded_threshold_one F S ε hε B hB
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁, fun f hf g ↦ ?_⟩
  have hoff (g : Jₛ) (hg : logNorm(mₛ) g ≠ 0) : ‖θₛ(f) g‖ ≤
      max K₁ K₂ * Real.exp (-(N : ℝ) * max (logNorm(mₛ) g) 0 - ε * min (logNorm(mₛ) g) 0) := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    rw [sLocalAdelicThetaOnClasses_mk]
    set n : ℝ := ((sIdeleNorm F S h).val : ℝ) with hn_def
    have hn : 0 < n := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hL : logNorm(mₛ) (QuotientGroup.mk h : Jₛ) = Real.log n := rfl
    rw [hL] at hg ⊢
    rcases lt_or_gt_of_ne hg with hlt | hgt
    · have hn1 : n < 1 := (Real.log_neg_iff hn).mp hlt
      have h2 : ‖(n ^ ε) • sLocalAdelicTheta F S f h‖ ≤ K₂ := h₂ f hf h hn1
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le ε)] at h2
      rw [max_eq_right hlt.le, min_eq_left hlt.le]
      have hnε : 0 < n ^ ε := Real.rpow_pos_of_pos hn ε
      have he : Real.exp (-(N : ℝ) * 0 - ε * Real.log n) = (n ^ ε)⁻¹ := by
        rw [Real.rpow_def_of_pos hn, ← Real.exp_neg]
        ring_nf
      rw [he]
      calc ‖sLocalAdelicTheta F S f h‖ = (n ^ ε)⁻¹ * (n ^ ε * ‖sLocalAdelicTheta F S f h‖) := by
            field_simp
        _ ≤ (n ^ ε)⁻¹ * K₂ := by gcongr
        _ ≤ (n ^ ε)⁻¹ * max K₁ K₂ := by gcongr; exact le_max_right _ _
        _ = max K₁ K₂ * (n ^ ε)⁻¹ := mul_comm _ _
    · have hn1 : 1 < n := (Real.log_pos_iff hn.le).mp hgt
      have h1 : ‖sLocalAdelicTheta F S f h‖ ≤ K₁ * (n ^ N)⁻¹ := h₁ f hf h hn1
      rw [max_eq_left hgt.le, min_eq_right hgt.le]
      have he : Real.exp (-(N : ℝ) * Real.log n - ε * 0) = (n ^ N)⁻¹ := by
        rw [mul_zero, sub_zero, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn]
      rw [he]
      exact h1.trans (by gcongr; exact le_max_left _ _)
  by_cases hg : logNorm(mₛ) g = 0
  · obtain ⟨σ₀, hσ₀⟩ := sIdeleQuotientNorm_exists_section (F := F) (S := S)
    let σ : ℝ → Jₛ := fun t ↦ g * σ₀ (sobolevLogEquiv t)
    have hσc : Continuous σ :=
      continuous_const.mul (σ₀.continuous.comp sobolevLogEquiv.continuous)
    have h1 : sobolevLogEquiv 0 = 1 := by
      apply Units.ext; apply NNReal.coe_injective
      have := sobolevLogEquiv_log 0
      rw [Real.log_eq_zero] at this
      rcases this with h0 | h1 | hm1
      · exact absurd h0 (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
      · simpa using h1
      · exact absurd hm1 (by linarith [NNReal.coe_nonneg ((sobolevLogEquiv 0).val)])
    have hσ0 : σ 0 = g := by simp only [σ, h1, map_one, mul_one]
    have hlog (t : ℝ) : logNorm(mₛ) (σ t) = logNorm(mₛ) g + t := by
      change Real.log ((sIdeleQuotientNorm F S (g * σ₀ (sobolevLogEquiv t))).val : ℝ) = _
      rw [map_mul, hσ₀, Units.val_mul, NNReal.coe_mul,
        Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
          (NNReal.coe_pos.mpr (Units.zero_lt _)).ne', sobolevLogEquiv_log]
      rfl
    have hb : Continuous fun t : ℝ ↦ max K₁ K₂ * Real.exp (-(N : ℝ) * max (logNorm(mₛ) g + t) 0 -
        ε * min (logNorm(mₛ) g + t) 0) := by
      have hc : Continuous fun t : ℝ ↦ logNorm(mₛ) g + t := continuous_const.add continuous_id
      exact continuous_const.mul (Real.continuous_exp.comp
        ((continuous_const.mul (hc.max continuous_const)).sub
          (continuous_const.mul (hc.min continuous_const))))
    have ht : Tendsto σ (𝓝[≠] 0) (𝓝 g) :=
      hσ0 ▸ hσc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim := ((θₛ(f)).continuous.norm.tendsto g).comp ht
    have hblim := (hb.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simp only [add_zero] at hblim
    refine le_of_tendsto_of_tendsto hlim hblim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have := hoff (σ t) (by rw [hlog, hg, zero_add]; exact ht)
    rwa [hlog] at this
  · exact hoff g hg

/-- A continuous linear map that vanishes exactly where a linear map does descends to a unique
injective continuous linear map of the quotient by its kernel with a prescribed value on each
class. Stated for abstract modules, so that it elaborates without unfolding the Schwartz–Bruhat
instances. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_assemble {M N V : Type*}
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [AddCommGroup N] [Module ℂ N]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (θ : M →ₗ[ℂ] N) (Λ : M →L[ℂ] V)
    (P : M → V → Prop) (hP : ∀ f, P f (Λ f)) (huniq : ∀ f v w, P f v → P f w → v = w)
    (hker : ∀ f, θ f = 0 → Λ f = 0) (hinj : ∀ f, Λ f = 0 → θ f = 0) :
    ∃! E : (M ⧸ LinearMap.ker θ) →L[ℂ] V,
      Injective E ∧ ∀ f, P f (E (Submodule.Quotient.mk f)) := by
  let E := (LinearMap.ker θ).liftQL Λ fun f hf ↦ hker f hf
  have hE (f : M) : E (Submodule.Quotient.mk f) = Λ f := rfl
  refine ⟨E, ⟨?_, fun f ↦ (hE f).symm ▸ hP f⟩, fun E' hE' ↦ ?_⟩
  · refine (injective_iff_map_eq_zero E).mpr fun x hx ↦ ?_
    induction x using Submodule.Quotient.induction_on with
    | H f => exact (Submodule.Quotient.mk_eq_zero _).mpr (hinj f ((hE f).symm.trans hx))
  · refine ContinuousLinearMap.ext fun x ↦ ?_
    induction x using Submodule.Quotient.induction_on with
    | H f => exact huniq f _ _ (hE'.2 f) ((hE f).symm ▸ hP f)

/-- The topological facts about the S-idele quotient that the Haar measure arguments need. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_sinst :
    T2Space Jₛ ∧ LocallyCompactSpace Jₛ ∧ SecondCountableTopology Jₛ := by
  have : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have : SecondCountableTopology Iₛ := by
    let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    let (v : S) : SecondCountableTopology (v.val.adicCompletion F) := secondCountable_of_proper
    let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
      (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
    let : SecondCountableTopology ((v : S) → v.val.adicCompletion F) := inferInstance
    let : SecondCountableTopology (SAdeleRing F S) := inferInstanceAs
      (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
    exact (sIdeleGroup_description F S).1.secondCountableTopology
  have : IsClosed (_ : Set Iₛ) := isClosed_sProjectedDiagonal (F := F) (S := S)
  exact ⟨inferInstance, inferInstanceAs (LocallyCompactSpace (Iₛ ⧸ _)),
    inferInstanceAs (SecondCountableTopology (Iₛ ⧸ _))⟩

/-- A linear map from the S-local tests into a normed space that is bounded on bounded sets is
continuous: each elementary stage is metrizable. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_continuous {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (Λ : ℬₛ →ₗ[ℂ] V)
    (hΛ : ∀ B : Set ℬₛ, Bornology.IsVonNBounded ℂ B → ∃ r, ∀ f ∈ B, ‖Λ f‖ ≤ r) :
    Continuous Λ := by
  let (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  let : LocallyCompactSpace (SAdeleRing F S) := inferInstanceAs
    (LocallyCompactSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : T2Space (SAdeleRing F S) := inferInstanceAs
    (T2Space (((v : InfinitePlace F) → v.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) :=
    inferInstanceAs (LocallyCompactSpace (SAdeleRing F S))
  let : T2Space (Multiplicative (SAdeleRing F S)) := inferInstanceAs (T2Space (SAdeleRing F S))
  apply SchwartzBruhat.continuous_of_continuous_comp_ofStage
  intro a e
  let : FirstCountableTopology (SchwartzBruhatStage e) :=
    elementarySchwartz_withSeminorms.firstCountableTopology
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  exact existsUnique_globalThetaSobolevEmbedding_stage
    ⟨SchwartzBruhat.ofStage a e, SchwartzBruhat.continuous_ofStage a e⟩ Λ hΛ

/-- The S-idele quotient norm is a modulation. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_smod : IsModulation mₛ := by
  obtain ⟨σ₀, hσ₀⟩ := sIdeleQuotientNorm_exists_section (F := F) (S := S)
  refine ⟨isProperMap_sIdeleQuotientNorm F S, σ₀ (Units.mk0 2 two_ne_zero), fun h ↦ ?_⟩
  have h2 := (hσ₀ (Units.mk0 2 two_ne_zero)).symm.trans h
  have := congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) h2
  norm_num at this

/-- S-local theta on classes is linear in the test. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_slin :
    ∃ L₀ : ℬₛ →ₗ[ℂ] (Jₛ → ℂ), ∀ f, L₀ f = θₛ(f) := by
  refine ⟨{ toFun := fun f ↦ θₛ(f), map_add' := fun f f' ↦ ?_, map_smul' := fun c f ↦ ?_ },
    fun _ ↦ rfl⟩
  · funext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [Pi.add_apply, sLocalAdelicThetaOnClasses_mk, map_add, ContinuousMap.add_apply]
  · funext x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [Pi.smul_apply, sLocalAdelicThetaOnClasses_mk, map_smul, RingHom.id_apply,
      ContinuousMap.smul_apply]

/-- The weighted S-local theta function of a test with the S-local bound is dominated pointwise
by exp(-δ |log |g||). -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_spointwise (a α β s C η : ℝ) (N : ℕ)
    (hs : 0 ≤ s) (hI : α ≤ β) (hN : |a| + |α| + |β| + s + 1 ≤ N) (hη : 0 < η) (hη1 : η ≤ 1)
    (hsη : s * η ≤ (a + α) / 2) (hp : 0 < a + α) (f : ℬₛ)
    (hdec : ∀ g : Jₛ, ‖θₛ(f) g‖ ≤ C * Real.exp (-(N : ℝ) * max (logNorm(mₛ) g) 0 -
      (a + α) / 2 * min (logNorm(mₛ) g) 0)) (g : Jₛ) :
    ‖modulationWeight mₛ a (θₛ(f)) g‖ ^ 2 * intervalSobolevDensity α β s (logNorm(mₛ) g) ≤
      (Real.sqrt ((1 + η⁻¹) ^ s) * C) ^ 2 *
        Real.exp (-(min 1 ((a + α) / 2) * |logNorm(mₛ) g|)) := by
  have hn : 0 < (((mₛ) g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hw : ‖modulationWeight mₛ a (θₛ(f)) g‖ = Real.exp (a * logNorm(mₛ) g) * ‖θₛ(f) g‖ := by
    change ‖(((((mₛ) g).val : ℝ) ^ a : ℝ) : ℂ) * θₛ(f) g‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _),
      Real.rpow_def_of_pos hn, mul_comm (Real.log _) a]
  have hd : 0 ≤ intervalSobolevDensity α β s (logNorm(mₛ) g) := by
    unfold intervalSobolevDensity
    exact mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _)) (by positivity)
  rw [hw, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  refine le_trans ?_ (existsUnique_sLocalThetaSobolevEmbedding_real a α β s C
    (logNorm(mₛ) g) η N hs hI hN hη hη1 hsη hp)
  gcongr
  exact hdec g

/-- A linear family of functions dominated, uniformly on bounded sets, by an integrable majorant
in the weighted L² sense gives a continuous linear map into the weighted L² space, once linear
maps bounded on bounded sets are known to be continuous. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_build {M X : Type*} [AddCommGroup M]
    [Module ℂ M] [TopologicalSpace M] [MeasurableSpace X] (μ : Measure X) (ρ : X → ℝ)
    (hρm : Measurable ρ) (hρpos : ∀ x, 0 < ρ x) (H : X → ℝ) (hH : Integrable H μ)
    (Ψ : M →ₗ[ℂ] (X → ℂ)) (hΨm : ∀ f, AEStronglyMeasurable (Ψ f) μ)
    (hsing : ∀ f : M, Bornology.IsVonNBounded ℂ {f})
    (hbound : ∀ B : Set M, Bornology.IsVonNBounded ℂ B →
      ∃ q : ℝ, 0 ≤ q ∧ ∀ f ∈ B, ∀ x, ‖Ψ f x‖ ^ 2 * ρ x ≤ q ^ 2 * H x)
    (hcrit : ∀ Λ : M →ₗ[ℂ] Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)),
      (∀ B : Set M, Bornology.IsVonNBounded ℂ B → ∃ r, ∀ f ∈ B, ‖Λ f‖ ≤ r) → Continuous Λ) :
    ∃ Λ : M →L[ℂ] Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)),
      ∀ f, (Λ f : X → ℂ) =ᵐ[μ] Ψ f := by
  have hμν : μ ≪ μ.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hρm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hρpos x)).ne')
  have hmem (f : M) : MemLp (Ψ f) 2 (μ.withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
    obtain ⟨q, -, hq⟩ := hbound {f} (hsing f)
    exact existsUnique_globalThetaSobolevEmbedding_memLp μ ρ hρm hρpos (Ψ f) (hΨm f) H hH q
      (hq f rfl)
  obtain ⟨L, hL⟩ := existsUnique_globalThetaSobolevEmbedding_toLp _ Ψ hmem
  have hrep (f : M) : (L f : X → ℂ) =ᵐ[μ] Ψ f := hμν.ae_eq (hL f)
  refine ⟨⟨L, hcrit L fun B hB ↦ ?_⟩, hrep⟩
  obtain ⟨q, hq, hqb⟩ := hbound B hB
  exact ⟨q * Real.sqrt (∫ x, H x ∂μ), fun f hf ↦
    weightedL2_le_majorant hρm hρpos (L f) (Ψ f) (hrep f) H hH q hq (hqb f hf)⟩

/-- The density of the weighted S-local space is measurable, positive, and the interval density
of the log norm. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_sdens (α β s : ℝ) :
    Measurable (fun g : Jₛ ↦ if (false : Bool) then
      (intervalSobolevDensity α β s (logNorm(mₛ) g))⁻¹
        else intervalSobolevDensity α β s (logNorm(mₛ) g)) ∧
    ∀ g : Jₛ, 0 < intervalSobolevDensity α β s (logNorm(mₛ) g) := by
  have : BorelSpace Jₛ := ⟨rfl⟩
  have hl : Continuous fun g : Jₛ ↦ logNorm(mₛ) g :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  simp only [Bool.false_eq_true, ite_false]
  refine ⟨?_, fun g ↦ ?_⟩
  · unfold intervalSobolevDensity
    exact (((Real.continuous_exp.comp (continuous_const.mul hl)).max
      (Real.continuous_exp.comp (continuous_const.mul hl))).mul
      ((continuous_const.add (hl.pow 2)).rpow_const fun g ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')).measurable
  · unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)

/-- S-local weighted theta is a continuous linear map from the S-local tests into the weighted L²
space. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_clm (a α β s : ℝ) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) :
    ∃ Λ : ℬₛ →L[ℂ] Wₛ(α, β, s), ∀ f,
      (Λ f : Jₛ → ℂ) =ᵐ[μₛ] modulationWeight mₛ a (θₛ(f)) := by
  have hsi := existsUnique_sLocalThetaSobolevEmbedding_sinst (F := F) (S := S)
  have : T2Space Jₛ := hsi.1
  have : LocallyCompactSpace Jₛ := hsi.2.1
  have : SecondCountableTopology Jₛ := hsi.2.2
  have : BorelSpace Jₛ := ⟨rfl⟩
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)
  have : (μₛ).IsHaarMeasure := hW.1
  have : (μₛ).Regular := hW.2.1
  have hm := existsUnique_sLocalThetaSobolevEmbedding_smod (F := F) (S := S)
  have hden := existsUnique_sLocalThetaSobolevEmbedding_sdens (F := F) (S := S) α β s
  have hslin := existsUnique_sLocalThetaSobolevEmbedding_slin (F := F) (S := S)
  let Ψ : ℬₛ →ₗ[ℂ] (Jₛ → ℂ) := (modulationWeight mₛ a) ∘ₗ hslin.choose
  have hΨ (f : ℬₛ) : Ψ f = modulationWeight mₛ a (θₛ(f)) := by
    simp only [Ψ, LinearMap.comp_apply, hslin.choose_spec]
  let N : ℕ := ⌈|a| + |α| + |β| + s + 1⌉₊
  let η : ℝ := min 1 ((a + α) / (2 * (s + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hsη : s * η ≤ (a + α) / 2 := by
    calc s * η ≤ s * ((a + α) / (2 * (s + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hs
      _ = (a + α) / 2 * (s / (s + 1)) := by field_simp
      _ ≤ (a + α) / 2 := mul_le_of_le_one_right (half_pos hp).le
          ((div_le_one₀ (by linarith)).mpr (by linarith))
  have hδ : 0 < min 1 ((a + α) / 2) := lt_min one_pos (half_pos hp)
  have hcont (f : ℬₛ) : Continuous (Ψ f) := by
    rw [hΨ]
    exact (Complex.continuous_ofReal.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (mₛ).continuous)).rpow_const fun g ↦
        Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')).mul (θₛ(f)).continuous
  have hb := existsUnique_sLocalThetaSobolevEmbedding_build μₛ _ hden.1
    (fun g ↦ by simpa only [Bool.false_eq_true, ite_false] using hden.2 g) _
    (existsUnique_sLocalThetaSobolevEmbedding_integrable μₛ mₛ hm hδ) Ψ
    (fun f ↦ (hcont f).aestronglyMeasurable) Bornology.isVonNBounded_singleton
    (fun B hB ↦ by
      obtain ⟨C, hC, hdec⟩ := existsUnique_sLocalThetaSobolevEmbedding_decay B hB (half_pos hp) N
      refine ⟨Real.sqrt ((1 + η⁻¹) ^ s) * C, by positivity, fun f hf g ↦ ?_⟩
      simp only [Bool.false_eq_true, ite_false, hΨ]
      exact existsUnique_sLocalThetaSobolevEmbedding_spointwise a α β s C η N hs hI
        (Nat.le_ceil _) hη (min_le_left _ _) hsη hp f (hdec f hf) g)
    (fun Λ hΛ ↦ existsUnique_sLocalThetaSobolevEmbedding_continuous Λ hΛ)
  exact ⟨hb.choose, fun f ↦ (hb.choose_spec f).trans (by rw [hΨ])⟩

/-- The S-local Tamagawa measure is absolutely continuous with respect to the weighted measure,
whose density is positive. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_sac (α β s : ℝ) :
    μₛ ≪ (μₛ).withDensity fun g ↦ ENNReal.ofReal
      (if (false : Bool) then (intervalSobolevDensity α β s (logNorm(mₛ) g))⁻¹
        else intervalSobolevDensity α β s (logNorm(mₛ) g)) := by
  have hden := existsUnique_sLocalThetaSobolevEmbedding_sdens (F := F) (S := S) α β s
  refine withDensity_absolutelyContinuous' hden.1.ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr ?_).ne')
  simpa only [Bool.false_eq_true, ite_false] using hden.2 g

/-- The weighted S-local theta class of a test in the theta kernel is zero. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_sker {a α β s : ℝ}
    (Λ : ℬₛ →L[ℂ] Wₛ(α, β, s)) (f : ℬₛ)
    (hΛ : (Λ f : Jₛ → ℂ) =ᵐ[μₛ] modulationWeight mₛ a (θₛ(f)))
    (hf : sLocalAdelicTheta F S f = 0) : Λ f = 0 := by
  have hθ : (θₛ(f) : Jₛ → ℂ) = 0 := funext fun x ↦ by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    rw [sLocalAdelicThetaOnClasses_mk, hf]
    rfl
  have hzero : modulationWeight mₛ a (θₛ(f)) = 0 := by
    rw [hθ, map_zero]
  have h0 : (Λ f : Jₛ → ℂ) =ᵐ[μₛ] (0 : Jₛ → ℂ) := hΛ.trans (Filter.EventuallyEq.of_eq hzero)
  exact Lp.ext (((withDensity_absolutelyContinuous μₛ _).ae_eq h0).trans
    (Lp.coeFn_zero _ _ _).symm)

/-- A test whose weighted S-local theta class is zero lies in the theta kernel. -/
private theorem existsUnique_sLocalThetaSobolevEmbedding_sinj {a α β s : ℝ}
    (Λ : ℬₛ →L[ℂ] Wₛ(α, β, s)) (f : ℬₛ)
    (hΛ : (Λ f : Jₛ → ℂ) =ᵐ[μₛ] modulationWeight mₛ a (θₛ(f))) (hf : Λ f = 0) :
    sLocalAdelicTheta F S f = 0 := by
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)
  have : (μₛ).IsHaarMeasure := hW.1
  have h0 : (0 : Jₛ → ℂ) =ᵐ[μₛ] modulationWeight mₛ a (θₛ(f)) := by
    rw [hf] at hΛ
    exact ((existsUnique_sLocalThetaSobolevEmbedding_sac α β s).ae_eq
      (Lp.coeFn_zero _ _ _)).symm.trans hΛ
  have h1 : (0 : Jₛ → ℂ) =ᵐ[μₛ] θₛ(f) := by
    filter_upwards [h0] with g hg
    have hn : (((((mₛ) g).val : ℝ) ^ a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) a).ne'
    have hg' : (0 : ℂ) = (((((mₛ) g).val : ℝ) ^ a : ℝ) : ℂ) * θₛ(f) g := hg
    exact ((mul_eq_zero.mp hg'.symm).resolve_left hn).symm
  have h2 := (Continuous.ae_eq_iff_eq μₛ continuous_zero (θₛ(f)).continuous).mp h1
  exact ContinuousMap.ext fun h ↦ by
    rw [← sLocalAdelicThetaOnClasses_mk]
    exact (congrFun h2 _).symm

/-- Paper: Definition 10.1.1.1(2), p. 434. The weighted S-local theta embedding
sends a class to the almost-everywhere class of its weighted theta function.
Deviation: The smallest effective exponent a + α must be strictly positive. -/
theorem existsUnique_sLocalThetaSobolevEmbedding (a α β s : ℝ) (_ha : 0 < a)
    (_hI : α ≤ β) (_hs : 0 ≤ s) (_hpos : 0 < a + α) :
    ∃! E : Θₛ →L[ℂ] Wₛ(α, β, s), Injective E ∧
      ∀ f : ℬₛ, (E (Submodule.Quotient.mk f) : Jₛ → ℂ) =ᵐ[μₛ]
        modulationWeight mₛ a (θₛ(f)) := by
  have hΛ := existsUnique_sLocalThetaSobolevEmbedding_clm (F := F) (S := S) a α β s _hI _hs _hpos
  exact existsUnique_sLocalThetaSobolevEmbedding_assemble (sLocalAdelicTheta F S) hΛ.choose
    (fun f v ↦ (v : Jₛ → ℂ) =ᵐ[μₛ] modulationWeight mₛ a (θₛ(f))) hΛ.choose_spec
    (fun f v w hv hw ↦ Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq (hv.trans hw.symm)))
    (fun f hf ↦ existsUnique_sLocalThetaSobolevEmbedding_sker _ f (hΛ.choose_spec f) hf)
    (fun f hf ↦ existsUnique_sLocalThetaSobolevEmbedding_sinj _ f (hΛ.choose_spec f) hf)

local notation "Eₛ(" ha ", " hI ", " hs ", " hp ")" =>
  (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S) _ _ _ _ ha hI hs hp).exists.choose

variable (F S) in
/-- Paper: Definition 10.1.1.1(2), p. 434. The local norm completion is the
closure of the weighted theta image in the compact-interval Sobolev space.
Deviation: Require a + α > 0 for the norm to be finite. The closure model
uses quotient Haar measure, as in (10.1.1.5). -/
abbrev sLocalThetaSobolev {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β) (hs : 0 ≤ s)
    (hp : 0 < a + α) : Submodule ℂ Wₛ(α, β, s) :=
  (Eₛ(ha, hI, hs, hp).toLinearMap.range).topologicalClosure

local notation "Hₛ(" ha ", " hI ", " hs ", " hp ")" =>
  sLocalThetaSobolev F S ha hI hs hp
variable (F) in
/-- Paper: (10.1.2.3), p. 437. The global completion map sends a theta class to the
class of its norm-weighted theta function in the closed theta subspace. -/
def globalThetaSobolevInclusion (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    Θ₀ →L[ℂ] H𝔽(a, hI, hs) :=
  (E𝔽(a, hI, hs)).codRestrict (H𝔽(a, hI, hs))
    (fun u ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u))

variable (F S) in
/-- Paper: Definition 10.1.1.1(2), p. 434. The local completion map realizes a
theta class as its weighted theta function in the closed local theta subspace.
Deviation: The smallest effective exponent a + α is strictly positive. -/
def sLocalThetaSobolevInclusion {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) : Θₛ →L[ℂ] Hₛ(ha, hI, hs, hp) :=
  (Eₛ(ha, hI, hs, hp)).codRestrict (Hₛ(ha, hI, hs, hp))
    (fun u ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u))

local notation "j𝔽(" a ", " hI ", " hs ")" => globalThetaSobolevInclusion F a hI hs
local notation "jₛ(" ha ", " hI ", " hs ", " hp ")" => sLocalThetaSobolevInclusion F S ha hI hs hp

/-- Paper: Definition 10.1.1.1, p. 434. The weighted test-class embeddings have
dense image in their respective completions.
Deviation: Sanity checks for the closure models. -/
theorem globalThetaSobolev_dense (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    DenseRange (j𝔽(a, hI, hs)) := by
  intro x
  apply closure_subtype.mpr
  rw [← Set.range_comp]
  exact x.property

/-- Paper: Definition 10.1.1.1(2), p. 434. The weighted S-local test classes are
dense in the local Sobolev completion.
Deviation: Sanity check for the closure model at the admissible exponents. -/
theorem sLocalThetaSobolev_dense {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) :
    DenseRange (jₛ(ha, hI, hs, hp)) := by
  intro x
  have hr : Set.range (Eₛ(ha, hI, hs, hp)) =
      Subtype.val '' Set.range (jₛ(ha, hI, hs, hp)) :=
    Set.range_comp (Subtype.val : Hₛ(ha, hI, hs, hp) → Wₛ(α, β, s)) (jₛ(ha, hI, hs, hp))
  apply closure_subtype.mpr
  exact (congrArg (fun R : Set Wₛ(α, β, s) ↦ x.val ∈ closure R) hr).mp x.property

/-- translation of a weighted function extracts the inverse weight of the translating element. -/
private theorem exists_sLocalThetaSobolevUnweightedAction_weight {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (a : ℝ) (g x : G) (f : G → ℂ) :
    modulationWeight m a f (g⁻¹ * x) =
      (((m g).val : ℝ) ^ (-a) : ℝ) •
        modulationWeight m a (fun y ↦ f (g⁻¹ * y)) x := by
  have hm : ((m (g⁻¹ * x)).val : ℝ) = (((m g).val : ℝ))⁻¹ * ((m x).val : ℝ) := by
    simp
  change (((((m (g⁻¹ * x)).val : ℝ) ^ a : ℝ) : ℂ) * f (g⁻¹ * x)) =
    (((((m g).val : ℝ) ^ (-a) : ℝ) : ℂ) *
      (((((m x).val : ℝ) ^ a : ℝ) : ℂ) * f (g⁻¹ * x)))
  rw [hm, Real.mul_rpow (inv_nonneg.mpr (NNReal.coe_nonneg _)) (NNReal.coe_nonneg _),
    Real.inv_rpow (NNReal.coe_nonneg _), Real.rpow_neg (NNReal.coe_nonneg _),
    Complex.ofReal_mul, mul_assoc]
/-- transfer an almost-everywhere translation identity to a weighted L² class. -/
private theorem exists_sLocalThetaSobolevUnweightedAction_ae {G : Type*} [MeasurableSpace G]
    (μ ν : Measure G) (hν : ν ≪ μ) (r : G → G)
    (hr : QuasiMeasurePreserving r μ μ) (c : ℝ)
    (t u v : Lp ℂ 2 ν) (φ ψ : G → ℂ)
    (ht : (t : G → ℂ) =ᵐ[μ] fun x ↦ u (r x))
    (hu : (u : G → ℂ) =ᵐ[μ] φ)
    (hv : (v : G → ℂ) =ᵐ[μ] ψ)
    (hφ : ∀ x, φ (r x) = c • ψ x) : t = c • v := by
  have he : (t : G → ℂ) =ᵐ[μ] fun x ↦ c • v x := by
    filter_upwards [ht, hr.ae_eq_comp hu, hv] with x hx hx' hx''
    exact hx.trans ((hx').trans ((hφ x).trans (congrArg (c • ·) hx''.symm)))
  exact Lp.ext ((hν.ae_eq he).trans (Lp.coeFn_smul c v).symm)
/-- lift the translation identity from representatives to a quotient realization. -/
private theorem exists_sLocalThetaSobolevUnweightedAction_lift {G I B U : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] (μ ν : Measure G) (hν : ν ≪ μ)
    (m : G →ₜ* ℝ≥0ˣ) (a : ℝ)
    (π : I → G) (hπ : Surjective π) (q : B → U) (hq : Surjective q)
    (E : U → Lp ℂ 2 ν) (σ : G → U → U) (τ : G → Lp ℂ 2 ν → Lp ℂ 2 ν)
    (θ : B → G → ℂ) (T : I → B → B)
    (hE : ∀ f, (E (q f) : G → ℂ) =ᵐ[μ] modulationWeight m a (θ f))
    (hσ : ∀ g f, σ (π g) (q f) = q (T g f))
    (hτ : ∀ g u, (τ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x))
    (hθ : ∀ g f x, θ (T g f) x = θ f ((π g)⁻¹ * x))
    (hr : ∀ g : G, QuasiMeasurePreserving (fun x ↦ g⁻¹ * x) μ μ) :
    ∀ g u, τ g (E u) = (((m g).val : ℝ) ^ (-a) : ℝ) • E (σ g u) := by
  intro g u
  obtain ⟨v, rfl⟩ := hπ g
  obtain ⟨f, rfl⟩ := hq u
  rw [hσ]
  apply exists_sLocalThetaSobolevUnweightedAction_ae μ ν hν _ (hr (π v)) _ _ _ _ _ _ (hτ _ _) (hE f) (hE (T v f))
  intro x
  exact (exists_sLocalThetaSobolevUnweightedAction_weight m a (π v) x (θ f)).trans (congrArg
    (fun φ : G → ℂ ↦ (((m (π v)).val : ℝ) ^ (-a) : ℝ) • modulationWeight m a φ x)
    (funext (hθ v f)).symm)
/-- restrict a jointly continuous action to the closure of an invariant image. -/
private theorem exists_sLocalThetaSobolevUnweightedAction_restrict
    {G U W : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
    (E : U → W) (R : Submodule ℂ W)
    (hR : ∀ x, x ∈ R ↔ ∃ u, E u = x)
    (j : U → R.topologicalClosure) (hj : ∀ u, (j u : W) = E u) (σ : G → U → U)
    (τ : G →* (W →L[ℂ] W))
    (hc : Continuous fun p : G × W ↦ τ p.1 p.2)
    (hE : ∀ g u, τ g (E u) = E (σ g u)) :
    let H := R.topologicalClosure
    ∃ ρ : G →* (H →L[ℂ] H),
      (∀ g u, ((ρ g u : H) : W) = τ g u) ∧
      Continuous (fun p : G × H ↦ ρ p.1 p.2) ∧
      ∀ g u, ρ g (j u) =
        j (σ g u) := by
  intro H
  have hinv (g : G) : ∀ x ∈ H, τ g x ∈ H := by
    have hInv : R ∈ Module.End.invtSubmodule (τ g).toLinearMap := by
      rw [Module.End.mem_invtSubmodule_iff_map_le]
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      obtain ⟨u, rfl⟩ := (hR x).mp hx
      exact (hR _).mpr ⟨σ g u, (hE g u).symm⟩
    exact fun x hx ↦ Submodule.topologicalClosure_mem_invtSubmodule hInv hx
  let ρ : G →* (H →L[ℂ] H) :=
    { toFun := fun g ↦ (τ g).restrict (hinv g)
      map_one' := by
        ext u
        simp
      map_mul' := by
        intro g h
        ext u
        simp [map_mul] }
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro g u
    rfl
  · exact (hc.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · intro g u
    exact Subtype.ext ((congrArg (τ g) (hj u)).trans
      ((hE g u).trans (hj (σ g u)).symm))

/-- a continuous character cancels the scalar in the intertwining identity. -/
private theorem exists_sLocalThetaSobolevUnweightedAction_twist
    {G U W : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
    (E : U → W) (R : Submodule ℂ W)
    (hR : ∀ x, x ∈ R ↔ ∃ u, E u = x)
    (j : U → R.topologicalClosure) (hj : ∀ u, (j u : W) = E u) (σ : G → U → U)
    (τ : G →* (W →L[ℂ] W))
    (hcτ : Continuous fun p : G × W ↦ τ p.1 p.2)
    (c : G →* ℝ) (hc : Continuous c) (d : G → ℝ) (hcd : ∀ g, c g * d g = 1)
    (hE : ∀ g u, τ g (E u) = d g • E (σ g u)) :
    let H := R.topologicalClosure
    ∃ ρ : G →* (H →L[ℂ] H),
      Continuous (fun p : G × H ↦ ρ p.1 p.2) ∧
      ∀ g u, ρ g (j u) =
        j (σ g u) := by
  let τ' : G →* (W →L[ℂ] W) :=
    { toFun := fun g ↦ c g • τ g
      map_one' := by
        ext u
        simp
      map_mul' := by
        intro g h
        ext u
        change c (g * h) • τ (g * h) u = c g • τ g (c h • τ h u)
        rw [map_mul, map_mul, mul_smul]
        rw [(τ g).map_smul_of_tower]
        simp only [smul_smul]
        rfl }
  have hcτ' : Continuous (fun p : G × W ↦ τ' p.1 p.2) := by
    exact (hc.comp continuous_fst).smul hcτ
  have hE' (g : G) (u : U) : τ' g (E u) = E (σ g u) := by
    change c g • τ g (E u) = _
    rw [hE]
    simp only [smul_smul, hcd g, one_smul]
  obtain ⟨ρ, _, hρc, hρE⟩ := exists_sLocalThetaSobolevUnweightedAction_restrict E R hR j hj σ τ' hcτ' hE'
  exact ⟨ρ, hρc, hρE⟩

/-- real powers of a positive character form a continuous character with the inverse weight. -/
private theorem exists_sLocalThetaSobolevUnweightedAction_real_character {G : Type*} [Group G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (a : ℝ) :
    ∃ c : G →* ℝ, Continuous c ∧ ∀ g, c g * ((m g).val : ℝ) ^ (-a) = 1 := by
  let c : G →* ℝ :=
    { toFun := fun g ↦ ((m g).val : ℝ) ^ a
      map_one' := by simp
      map_mul' := by
        intro g h
        simp only [map_mul, Units.val_mul, NNReal.coe_mul]
        exact Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) }
  refine ⟨c, ?_, ?_⟩
  · exact (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).rpow_const
      (fun g ↦ Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  · intro g
    change ((m g).val : ℝ) ^ a * ((m g).val : ℝ) ^ (-a) = 1
    rw [← Real.rpow_add (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp

/-- Paper: Remark 10.1.1.2, pp. 434–435. The original S-local left action
extends jointly continuously to the norm completion via the completion map.
Deviation: The smallest effective exponent a + α is strictly positive. -/
theorem exists_sLocalThetaSobolevUnweightedAction {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    ∃ ρ : Jₛ →* (Hₛ(ha, hI, hs, hp) →L[ℂ] Hₛ(ha, hI, hs, hp)),
      Continuous (fun p : Jₛ × Hₛ(ha, hI, hs, hp) ↦ ρ p.1 p.2) ∧
      ∀ (g : Jₛ) (u : Θₛ), ρ g (jₛ(ha, hI, hs, hp) u) = jₛ(ha, hI, hs, hp) (ρₛ g u) := by
  let : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
  let : T2Space (SIdeleQuotient F S) := by
    let := isClosed_sProjectedDiagonal (F := F) (S := S)
    infer_instance
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  let : LocallyCompactSpace (SIdeleQuotient F S) := inferInstanceAs
    (LocallyCompactSpace ((SAdeleRing F S)ˣ ⧸ _))
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing F S) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F S)ˣ :=
    (sIdeleGroup_description F S).1.secondCountableTopology
  let : SecondCountableTopology (SIdeleQuotient F S) := inferInstanceAs
    (SecondCountableTopology ((SAdeleRing F S)ˣ ⧸ _))
  let : (sLocalQuotientTamagawaMeasure F S).IsHaarMeasure :=
    (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let μ := sLocalQuotientTamagawaMeasure F S
  let m : SIdeleQuotient F S →ₜ* ℝ≥0ˣ :=
    ⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩
  let E := (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S)
    a α β s ha hI hs hp).exists.choose
  let σ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
  let hchar := exists_sLocalThetaSobolevUnweightedAction_real_character (G := SIdeleQuotient F S) m a
  have hτc : Continuous (fun p : SIdeleQuotient F S ×
      CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) α β s ↦
      hardySobolevTranslation μ m α β s hI hs p.1 p.2) :=
    (exists_hardySobolevTranslation μ m α β s hI hs).choose_spec.2
  with_reducible_and_instances
    exact exists_sLocalThetaSobolevUnweightedAction_twist
      (G := SIdeleQuotient F S) (U := SLocalAdelicThetaSpace F S)
      (W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) α β s)
      (E := fun u ↦ E u) (R := E.toLinearMap.range) (hR := fun _ ↦ Iff.rfl)
      (j := fun u ↦ sLocalThetaSobolevInclusion F S ha hI hs hp u) (hj := fun _ ↦ rfl)
      (σ := fun g u ↦ σ g u)
      (τ := hardySobolevTranslation μ m α β s hI hs)
      hτc hchar.choose hchar.choose_spec.1
      (fun g ↦ ((m g).val : ℝ) ^ (-a)) hchar.choose_spec.2
      (exists_sLocalThetaSobolevUnweightedAction_lift μ _ (withDensity_absolutelyContinuous μ _) m a
        (QuotientGroup.mk : (SAdeleRing F S)ˣ → SIdeleQuotient F S) QuotientGroup.mk_surjective
        (Submodule.Quotient.mk : SchwartzBruhat (Multiplicative (SAdeleRing F S)) → SLocalAdelicThetaSpace F S)
        (Submodule.Quotient.mk_surjective _) E (fun g u ↦ σ g u)
        (fun g u ↦ hardySobolevTranslation μ m α β s hI hs g u)
        (fun f x ↦ sLocalAdelicThetaOnClasses F S f x) schwartzBruhatUnitTranslate
        (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S) a α β s ha hI hs hp).exists.choose_spec.2
        (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
        (hardySobolevTranslation_apply μ m α β s hI hs)
        (fun g f x ↦ sLocalTheta_translate_onClasses g f x)
        (fun g ↦ (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving))

/-- The modulation weight shifts the interval of the Sobolev density. -/
private theorem globalThetaSobolev_norm_density (a α β s l : ℝ) :
    Real.exp (a * l) ^ 2 * intervalSobolevDensity α β s l =
      intervalSobolevDensity (a + α) (a + β) s l := by
  unfold intervalSobolevDensity
  rw [← mul_assoc, mul_max_of_nonneg _ _ (by positivity), ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_add]
  congr 3 <;> push_cast <;> ring

/-- The norm of a weighted L² class represented by a weighted function, on an abstract
measure space. -/
private theorem globalThetaSobolev_norm_aux {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (r : G → ℝ) (hr : ∀ g, 0 < r g) (hrm : Measurable r) (a α β s : ℝ) (φ : G → ℂ)
    (u : CompactIntervalSobolev μ (fun g ↦ Real.log (r g)) α β s)
    (hu : (u : G → ℂ) =ᵐ[μ] fun g ↦ ((r g ^ a : ℝ) : ℂ) * φ g) :
    let w := fun g : G ↦ ‖φ g‖ ^ 2 * intervalSobolevDensity (a + α) (a + β) s (Real.log (r g))
    Integrable w μ ∧ ‖u‖ = Real.sqrt (∫ g, w g ∂μ) := by
  intro w
  set d : G → ℝ := fun g ↦ intervalSobolevDensity α β s (Real.log (r g)) with hd_def
  have hd0 (g : G) : 0 ≤ d g := by
    simp only [d, intervalSobolevDensity]
    exact mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _)) (by positivity)
  have hdm : Measurable d := by
    simp only [d, intervalSobolevDensity]
    fun_prop
  have hdm' : Measurable fun g ↦ ENNReal.ofReal (d g) := ENNReal.measurable_ofReal.comp hdm
  have hlt : ∀ᵐ g ∂μ, ENNReal.ofReal (d g) < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hpt : (fun g ↦ ENNReal.toReal (ENNReal.ofReal (d g)) • ‖(u : G → ℂ) g‖ ^ 2) =ᵐ[μ] w := by
    filter_upwards [hu] with g hg
    rw [hg, ENNReal.toReal_ofReal (hd0 g), smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hr g).le _), Real.rpow_def_of_pos (hr g),
      mul_comm (Real.log (r g)) a]
    simp only [w, d]
    rw [← globalThetaSobolev_norm_density a α β s]
    ring
  have hint : Integrable (fun g ↦ ‖(u : G → ℂ) g‖ ^ 2)
      (μ.withDensity fun g ↦ ENNReal.ofReal (d g)) :=
    (Lp.memLp u).integrable_norm_pow two_ne_zero
  have hw : Integrable w μ :=
    ((integrable_withDensity_iff_integrable_smul' hdm' hlt).mp hint).congr hpt
  refine ⟨hw, ?_⟩
  have hsq : ‖u‖ ^ 2 = ∫ g, ‖(u : G → ℂ) g‖ ^ 2 ∂(μ.withDensity fun g ↦ ENNReal.ofReal (d g)) := by
    rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    rw [integral_ofReal, RCLike.ofReal_re]
    rfl
  rw [← Real.sqrt_sq (norm_nonneg u), hsq,
    integral_withDensity_eq_integral_toReal_smul hdm' hlt, integral_congr_ae hpt]

/-- Paper: Lemma 10.1.1.3, p. 435. The continuous weighted embedding pulls
the ambient norm back to the norm in (10.1.1.6).
Deviation: Use the Haar measure on the full idele class group, denoted μ̄ in Appendix A.3. -/
theorem globalThetaSobolev_norm (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) (f : ℬ₀) :
    let w := fun g : C𝔽 ↦ ‖θ𝔽(f) g‖ ^ 2 *
      intervalSobolevDensity (a + α) (a + β) s (logNorm(m𝔽) g)
    Integrable w μ𝔽 ∧ ‖E𝔽(a, hI, hs) (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g, w g ∂μ𝔽) := by
  have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a α β s hI hs).exists.choose_spec.2 f
  have : BorelSpace C𝔽 := ⟨rfl⟩
  exact globalThetaSobolev_norm_aux μ𝔽 (fun g ↦ ((m𝔽 g).val : ℝ))
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable
    a α β s _ _ hE

/-- Paper: Lemma 10.1.1.3(1), p. 435. The global completion is a closed,
complete and separable subspace of the ambient Hilbert space. -/
theorem globalThetaSobolev_closed_complete_separable (a : ℝ) {α β s : ℝ}
    (hI : α ≤ β) (hs : 0 ≤ s) :
    IsClosed (H𝔽(a, hI, hs) : Set W𝔽(α, β, s)) ∧
      CompleteSpace (H𝔽(a, hI, hs)) ∧ TopologicalSpace.SeparableSpace (H𝔽(a, hI, hs)) := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : SecondCountableTopology C𝔽 := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : IsClosed (H𝔽(a, hI, hs) : Set W𝔽(α, β, s)) :=
    Submodule.isClosed_topologicalClosure _
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology W𝔽(α, β, s) := Lp.SecondCountableTopology
  exact ⟨hc, hc.completeSpace_coe, inferInstance⟩

local instance instIdeleClassBorelSpaceSec1 : BorelSpace C𝔽 := ⟨rfl⟩
local instance instSIdeleQuotientBorelSpaceSec1 : BorelSpace Jₛ := ⟨rfl⟩
local instance instIdeleClassT2Sec1 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSec1 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassSecondCountableSec1 : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))

local instance instSIdeleLocallyCompactSec1 : LocallyCompactSpace Iₛ :=
  (sIdeleGroup_description F S).2.2.1

set_option maxSynthPendingDepth 8 in
local instance instSIdeleSecondCountableSec1 : SecondCountableTopology Iₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F) := secondCountable_of_proper
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  let : SecondCountableTopology ((v : S) → v.val.adicCompletion F) := inferInstance
  let : SecondCountableTopology (SAdeleRing F S) := inferInstanceAs
    (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  exact (sIdeleGroup_description F S).1.secondCountableTopology

local instance instSIdeleQuotientT2Sec1 : T2Space Jₛ :=
  letI := isClosed_sProjectedDiagonal (F := F) (S := S)
  inferInstance

local instance instSIdeleQuotientLocallyCompactSec1 : LocallyCompactSpace Jₛ :=
  inferInstanceAs (LocallyCompactSpace (Iₛ ⧸ _))

local instance instSIdeleQuotientSecondCountableSec1 : SecondCountableTopology Jₛ :=
  inferInstanceAs (SecondCountableTopology (Iₛ ⧸ _))

local instance instIdeleClassHaarMeasureSec1 : Measure.IsHaarMeasure μ𝔽 :=
  (ideleClassTamagawaMeasure_isWeil F).1

local instance instSIdeleQuotientHaarMeasureSec1 : Measure.IsHaarMeasure μₛ :=
  (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1

open scoped ENNReal in
/-- Scaling a measure by a finite positive constant gives the same weighted L² space
with the norm scaled by the square root of the constant. -/
private theorem globalThetaAmbient_equiv_canonical_aux {G : Type*} [MeasurableSpace G]
    (μ ν : Measure G) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hμ : μ = c • ν)
    (d : G → ℝ≥0∞) (hdm : Measurable d) (hd : ∀ x, d x ≠ 0) :
    ∃ e : Lp ℂ 2 (μ.withDensity d) ≃L[ℂ] Lp ℂ 2 (ν.withDensity d),
      ∀ u, (e u : G → ℂ) =ᵐ[μ] u ∧ ‖u‖ = Real.sqrt c.toReal * ‖e u‖ := by
  subst hμ
  have hρ : (c • ν).withDensity d = c • ν.withDensity d := withDensity_smul_measure c d
  have hci : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  have hle : ν.withDensity d ≤ c⁻¹ • (c • ν).withDensity d := by
    rw [hρ, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  have hle' : (c • ν).withDensity d ≤ c • ν.withDensity d := hρ.le
  have mem₁ (u : Lp ℂ 2 ((c • ν).withDensity d)) : MemLp u 2 (ν.withDensity d) :=
    (Lp.memLp u).of_measure_le_smul hci hle
  have mem₂ (u : Lp ℂ 2 (ν.withDensity d)) : MemLp u 2 ((c • ν).withDensity d) :=
    (Lp.memLp u).of_measure_le_smul hct hle'
  have hsmul {p : G → Prop} (ρ : Measure G) : (∀ᵐ x ∂(c • ρ), p x) ↔ ∀ᵐ x ∂ρ, p x := by
    simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc0, false_or]
  have hae₁ {f g : G → ℂ} (h : f =ᵐ[(c • ν).withDensity d] g) : f =ᵐ[ν.withDensity d] g := by
    rw [hρ] at h
    exact (hsmul _).mp h
  have hae₂ {f g : G → ℂ} (h : f =ᵐ[ν.withDensity d] g) : f =ᵐ[(c • ν).withDensity d] g := by
    rw [hρ]
    exact (hsmul _).mpr h
  let T : Lp ℂ 2 ((c • ν).withDensity d) →ₗ[ℂ] Lp ℂ 2 (ν.withDensity d) :=
    { toFun := fun u ↦ (mem₁ u).toLp u
      map_add' := fun u v ↦ by
        apply Lp.ext
        filter_upwards [(mem₁ (u + v)).coeFn_toLp, (mem₁ u).coeFn_toLp, (mem₁ v).coeFn_toLp,
          Lp.coeFn_add ((mem₁ u).toLp u) ((mem₁ v).toLp v), hae₁ (Lp.coeFn_add u v)]
          with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]
      map_smul' := fun r u ↦ by
        apply Lp.ext
        filter_upwards [(mem₁ (r • u)).coeFn_toLp, (mem₁ u).coeFn_toLp,
          Lp.coeFn_smul r ((mem₁ u).toLp u), hae₁ (Lp.coeFn_smul r u)]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply] }
  let S : Lp ℂ 2 (ν.withDensity d) → Lp ℂ 2 ((c • ν).withDensity d) := fun u ↦ (mem₂ u).toLp u
  have hTS (u) : T (S u) = u := by
    apply Lp.ext
    filter_upwards [(mem₁ (S u)).coeFn_toLp, hae₁ (mem₂ u).coeFn_toLp] with x h1 h2
    exact h1.trans h2
  have hST (u) : S (T u) = u := by
    apply Lp.ext
    filter_upwards [(mem₂ (T u)).coeFn_toLp, hae₂ (mem₁ u).coeFn_toLp] with x h1 h2
    exact h1.trans h2
  have hnorm (u : Lp ℂ 2 ((c • ν).withDensity d)) : ‖u‖ = Real.sqrt c.toReal * ‖T u‖ := by
    have hsm (f : G → ℂ) : eLpNorm f 2 ((c • ν).withDensity d) =
        c ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm f 2 (ν.withDensity d) := by
      rw [hρ, eLpNorm_smul_measure_of_ne_zero hc0]
    have h1 : eLpNorm (T u : G → ℂ) 2 (ν.withDensity d) = eLpNorm (u : G → ℂ) 2 (ν.withDensity d) :=
      eLpNorm_congr_ae (mem₁ u).coeFn_toLp
    rw [Lp.norm_def, Lp.norm_def, h1, hsm, smul_eq_mul,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
    norm_num
  let e₀ : Lp ℂ 2 ((c • ν).withDensity d) ≃ₗ[ℂ] Lp ℂ 2 (ν.withDensity d) :=
    { T with invFun := S, left_inv := hST, right_inv := hTS }
  have hcpos : 0 < Real.sqrt c.toReal :=
    Real.sqrt_pos.mpr (ENNReal.toReal_pos hc0 hct)
  refine ⟨e₀.toContinuousLinearEquivOfBounds (Real.sqrt c.toReal)⁻¹ (Real.sqrt c.toReal)
    (fun u ↦ ?_) (fun u ↦ ?_), fun u ↦ ⟨?_, hnorm u⟩⟩
  · change ‖T u‖ ≤ _
    rw [hnorm u, ← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
  · change ‖S u‖ ≤ _
    rw [hnorm (S u), hTS]
  · change ((mem₁ u).toLp u : G → ℂ) =ᵐ[c • ν] u
    have h := (mem₁ u).coeFn_toLp
    rw [Filter.EventuallyEq, ae_withDensity_iff hdm] at h
    exact (hsmul _).mpr (h.mono fun x hx ↦ hx (hd x))

/-- Paper: Definition 10.1.1.1(1) and Lemma 10.1.1.3, pp. 434–435.
The identity on functions compares the Tamagawa norm with the canonical norm of §9.2.
Deviation: The two full Haar measures differ by the mass of the norm-one classes. -/
theorem globalThetaAmbient_equiv_canonical (hm : IsModulation m𝔽) (α β s : ℝ) :
    ∃ e : W𝔽(α, β, s) ≃L[ℂ] ModulatedIntervalSobolev m𝔽 hm α β s,
      ∀ u, (e u : C𝔽 → ℂ) =ᵐ[μ𝔽] u ∧
        ‖u‖ = Real.sqrt (Measure.real μ𝔽₁ univ) * ‖e u‖ := by
  have hμ := ideleClassTamagawaMeasure_eq_smul_canonical (F := F)
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : μ𝔽₁ univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : μ𝔽₁ univ ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hdm : Measurable fun g : C𝔽 ↦
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((m𝔽 g).val : ℝ)))) := by
    have hLm : Measurable fun g : C𝔽 ↦ Real.log (((m𝔽 g).val : ℝ)) :=
      ((NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
        fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
    unfold intervalSobolevDensity
    fun_prop
  have hd (g : C𝔽) :
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((m𝔽 g).val : ℝ)))) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  exact globalThetaAmbient_equiv_canonical_aux μ𝔽 (canonicalModulatedHaar m𝔽 hm)
    (μ𝔽₁ univ) hc0 hct hμ _ hdm hd

open scoped ENNReal in
/-- The S-local quotient Tamagawa measure is the canonical modulated Haar measure times the
mass of the norm-one quotient. Both measures give the band of norms in [1, e] the mass of
the norm-one part. -/
private theorem sLocalThetaAmbient_equiv_canonical_measure (hm : IsModulation mₛ) :
    μₛ = μₛ₁ univ • canonicalModulatedHaar mₛ hm := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  have : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : BorelSpace J₁ := ⟨rfl⟩
  have : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  -- A continuous section of the S-idelic norm and its image in the quotient.
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Iₛ := ⟨p.comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := thetaSection_rightInverse F S
  let σ : ℝ≥0ˣ →ₜ* Jₛ :=
    (⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩ : Iₛ →ₜ* Jₛ).comp τ
  have hσ : RightInverse σ mₛ := fun t ↦ (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  -- The band of norms between 1 and e has `dt/t`-mass one.
  let Sb : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  have hSm : MeasurableSet Sb :=
    (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
  have hPRS : positiveRealHaar Sb = 1 := by
    let T : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have hT : ((T.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have h := positiveRealHaar_interval T (by rw [hT]; exact Real.one_le_exp zero_le_one)
    rw [hT, Real.log_exp, ENNReal.ofReal_one] at h
    exact h
  let B : Set Jₛ := mₛ ⁻¹' Sb
  have hBm : MeasurableSet B := (mₛ).continuous.measurable hSm
  have hnorm (k : Jₛ) (hk : mₛ k = 1) (t : ℝ≥0ˣ) : k * σ t ∈ B ↔ t ∈ Sb := by
    change mₛ (k * σ t) ∈ Sb ↔ _
    rw [map_mul, hk, one_mul, hσ t]
  -- The canonical measure gives the band mass one.
  have hcanB : canonicalModulatedHaar mₛ hm B = 1 := by
    letI : MeasurableSpace (mₛ).toMonoidHom.ker := Subtype.instMeasurableSpace
    have : CompactSpace (mₛ).toMonoidHom.ker := isCompact_iff_compactSpace.mp hm.isCompact_ker
    let μ₀ : Measure (mₛ).toMonoidHom.ker := Measure.haarMeasure ⊤
    have hcan := canonicalModulatedHaar_eq_map_prod mₛ hm σ hσ μ₀ Measure.haarMeasure_self
    have hφ : Continuous fun z : (mₛ).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : Jₛ) * σ z.2 := by
      fun_prop
    rw [hcan, Measure.map_apply hφ.measurable hBm]
    have hpre : (fun z : (mₛ).toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : Jₛ) * σ z.2) ⁻¹' B =
        univ ×ˢ Sb := by
      ext ⟨k, t⟩
      simp only [mem_preimage, mem_prod, mem_univ, true_and]
      exact hnorm k k.property t
    rw [hpre, Measure.prod_prod, show μ₀ univ = 1 from Measure.haarMeasure_self, one_mul, hPRS]
  -- The quotient Tamagawa measure gives the band the mass of the norm-one part.
  have hμB : μₛ B = μₛ₁ univ := by
    have hJ := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
    have hφ : Continuous fun x : J₁ × ℝ≥0ˣ ↦ (x.1 : Jₛ) * QuotientGroup.mk (τ x.2) := by
      fun_prop
    rw [← hJ, Measure.map_apply hφ.measurable hBm]
    have hpre : (fun x : J₁ × ℝ≥0ˣ ↦ (x.1 : Jₛ) * QuotientGroup.mk (τ x.2)) ⁻¹' B =
        univ ×ˢ Sb := by
      ext ⟨k, t⟩
      simp only [mem_preimage, mem_prod, mem_univ, true_and]
      exact hnorm k k.property t
    rw [hpre, Measure.prod_prod, hPRS, mul_one]
  -- Compare the two Haar measures on the band.
  have : (canonicalModulatedHaar mₛ hm).IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar mₛ hm).exists).1
  have hscale := Measure.isMulLeftInvariant_eq_smul μₛ (canonicalModulatedHaar mₛ hm)
  set c := Measure.haarScalarFactor μₛ (canonicalModulatedHaar mₛ hm)
  have hc : (c : ℝ≥0∞) = μₛ₁ univ := by
    have h := congrArg (fun ν : Measure Jₛ ↦ ν B) hscale
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← hμB, h, hcanB, mul_one]
  exact hscale.trans (by rw [ENNReal.smul_def, hc])

/-- Paper: Definition 10.1.1.1(2) and Lemma 10.1.1.4, pp. 434–436.
The identity on S-local functions compares the norm in (10.1.1.5) with §9.2.
Deviation: The Tamagawa squared norm includes the mass of the norm-one quotient. -/
theorem sLocalThetaAmbient_equiv_canonical (hm : IsModulation mₛ) (α β s : ℝ) :
    ∃ e : Wₛ(α, β, s) ≃L[ℂ] ModulatedIntervalSobolev mₛ hm α β s,
      ∀ u, (e u : Jₛ → ℂ) =ᵐ[μₛ] u ∧
        ‖u‖ = Real.sqrt (Measure.real μₛ₁ univ) * ‖e u‖ := by
  have : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hc0 : μₛ₁ univ ≠ 0 := (isOpen_univ.measure_pos _ univ_nonempty).ne'
  have hct : μₛ₁ univ ≠ ⊤ := measure_ne_top _ _
  have hdm : Measurable fun g : Jₛ ↦
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((mₛ g).val : ℝ)))) := by
    have hLm : Measurable fun g : Jₛ ↦ Real.log (((mₛ g).val : ℝ)) :=
      ((NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ).continuous)).log
        fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
    unfold intervalSobolevDensity
    fun_prop
  have hd (g : Jₛ) :
      ENNReal.ofReal (intervalSobolevDensity α β s (Real.log (((mₛ g).val : ℝ)))) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  exact globalThetaAmbient_equiv_canonical_aux μₛ (canonicalModulatedHaar mₛ hm)
    (μₛ₁ univ) hc0 hct (sLocalThetaAmbient_equiv_canonical_measure hm) _ hdm hd

/-- Paper: Lemma 10.1.1.3(2), p. 435. Ambient left translation preserves the
global completion, acts jointly continuously there, and on weighted tests
has the factor |g|^(-a) multiplying the translated test. -/
theorem exists_globalThetaSobolevAction (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    ∃ ρ : C𝔽 →* (H𝔽(a, hI, hs) →L[ℂ] H𝔽(a, hI, hs)),
      (∀ g u, (ρ g u : W𝔽(α, β, s)) = hardySobolevTranslation μ𝔽 m𝔽 α β s hI hs g u) ∧
      Continuous (fun p : C𝔽 × H𝔽(a, hI, hs) ↦ ρ p.1 p.2) ∧
      ∀ (g : IdeleGroup (𝓞 F) F) (f : ℬ₀), ∃ f' : ℬ₀,
        f'.val = schwartzBruhatUnitTranslate g f.val ∧
          ρ (QuotientGroup.mk g) (j𝔽(a, hI, hs) (Submodule.Quotient.mk f)) =
            (((m𝔽 (QuotientGroup.mk g)).val : ℝ) ^ (-a) : ℝ) •
              j𝔽(a, hI, hs) (Submodule.Quotient.mk f') := by sorry

local notation "R𝔽(" a ", " hI ", " hs ")" =>
  (exists_globalThetaSobolevAction (F := F) a hI hs).choose

variable (F S) in
/-- Paper: Lemma 10.1.1.4(1), p. 435. The measure μ_{I,s} on the S-ideles
has the compact-interval Sobolev density in the logarithmic norm coordinate. -/
def sIdeleIntervalSobolevMeasure (α β s : ℝ) : Measure Iₛ :=
  (sMultiplicativeTamagawaMeasure F S).withDensity fun g ↦
    ENNReal.ofReal (intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)))

-- The density need not vanish at infinity, as the proof on p. 436 claims.
-- Continuity is enough for local boundedness and the Radon property.

/-- Paper: Lemma 10.1.1.4(1), p. 435. The interval density is one for I = {0},
s = 0, so the measure is the original multiplicative Tamagawa measure.
Deviation: Sanity check for the measure. -/
theorem sIdeleIntervalSobolevMeasure_zero :
    sIdeleIntervalSobolevMeasure F S 0 0 0 = sMultiplicativeTamagawaMeasure F S := by
  simp [sIdeleIntervalSobolevMeasure, intervalSobolevDensity]

/-- The density of the weighted S-idele measure is continuous. -/
private theorem sIdeleIntervalSobolevMeasure_regular_density (α β s : ℝ) :
    Continuous fun g : Iₛ ↦
      intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)) := by
  have hn : Continuous fun g : Iₛ ↦ ((sIdeleNorm F S g).val : ℝ) := by
    have h : Continuous fun g : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk g) :=
      (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  have hl : Continuous fun g : Iₛ ↦ Real.log ((sIdeleNorm F S g).val : ℝ) :=
    hn.log fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))).ne'
  unfold intervalSobolevDensity
  refine ((Real.continuous_exp.comp (continuous_const.mul hl)).max
    (Real.continuous_exp.comp (continuous_const.mul hl))).mul ?_
  exact (continuous_const.add (hl.pow 2)).rpow_const fun g ↦
    Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'

/-- Paper: Lemma 10.1.1.4(1), pp. 435–436. The weighted S-idele measure is
regular and finite on compact sets. -/
theorem sIdeleIntervalSobolevMeasure_regular (α β s : ℝ)
    (_hI : α ≤ β) (_hs : 0 ≤ s) :
    (sIdeleIntervalSobolevMeasure F S α β s).Regular := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have : (sMultiplicativeTamagawaMeasure F S).IsHaarMeasure :=
    sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  have : IsLocallyFiniteMeasure (sIdeleIntervalSobolevMeasure F S α β s) :=
    IsLocallyFiniteMeasure.withDensity_ofReal
      (sIdeleIntervalSobolevMeasure_regular_density α β s)
  infer_instance

/-- Paper: Lemma 10.1.1.4(1), pp. 435–436. The weighted S-idele measure is
invariant under left translation by the projected diagonal S-units. -/
theorem sIdeleIntervalSobolevMeasure_invariant (α β s : ℝ)
    (_hI : α ≤ β) (_hs : 0 ≤ s) :
    let ν := sIdeleIntervalSobolevMeasure F S α β s
    ∀ u : Iₛ, (QuotientGroup.mk u : Jₛ) = 1 →
      MeasurePreserving (fun g : Iₛ ↦ u * g) ν ν := by
  intro ν u hu
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have : (sMultiplicativeTamagawaMeasure F S).IsHaarMeasure :=
    sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  have hnu : sIdeleNorm F S u = 1 := by rw [← sIdeleQuotientNorm_mk, hu, map_one]
  have hmeas : Measurable fun g : Iₛ ↦ u * g := measurable_const_mul u
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [Measure.map_apply hmeas hA]
  simp only [ν, sIdeleIntervalSobolevMeasure, withDensity_apply _ hA,
    withDensity_apply _ (hmeas hA)]
  rw [← lintegral_indicator (hmeas hA), ← lintegral_indicator hA]
  conv_rhs => rw [← lintegral_mul_left_eq_self _ u]
  congr 1
  funext g
  simp only [indicator, map_mul, hnu, one_mul]
  rfl

/-- Paper: Lemma 10.1.1.4(2), pp. 435–436. On the local test classes the
subspace norm is (10.1.1.7) and is continuous for the theta quotient topology.
Deviation: Use μ̄_S on J_{F,S}, as in (10.1.1.5) and Appendix A.3. The formula
also applies whenever the smallest effective exponent a + α is positive. -/
theorem sLocalThetaSobolev_norm {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β)
    (hs : 0 ≤ s) (hp : 0 < a + α) (f : ℬₛ) :
    let w := fun g : Jₛ ↦ ‖θₛ(f) g‖ ^ 2 *
      intervalSobolevDensity (a + α) (a + β) s (logNorm(mₛ) g)
    Integrable w μₛ ∧ ‖Eₛ(ha, hI, hs, hp) (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g, w g ∂μₛ) := by
  have hE := (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S) a α β s ha hI hs
    hp).exists.choose_spec.2 f
  exact globalThetaSobolev_norm_aux μₛ (fun g ↦ ((mₛ g).val : ℝ))
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ).continuous)).measurable
    a α β s _ _ hE

/-- Paper: Lemma 10.1.1.4(3), p. 436. The local completion is a closed,
complete and separable subspace of the ambient Hilbert space. -/
theorem sLocalThetaSobolev_closed_complete_separable {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    IsClosed (Hₛ(ha, hI, hs, hp) : Set Wₛ(α, β, s)) ∧
      CompleteSpace (Hₛ(ha, hI, hs, hp)) ∧
      TopologicalSpace.SeparableSpace (Hₛ(ha, hI, hs, hp)) := by
  have hc : IsClosed (Hₛ(ha, hI, hs, hp) : Set Wₛ(α, β, s)) :=
    Submodule.isClosed_topologicalClosure _
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology Wₛ(α, β, s) := Lp.SecondCountableTopology
  exact ⟨hc, hc.completeSpace_coe, inferInstance⟩

/-- twist an extended action and identify it with the ambient action on a dense image. -/
private theorem exists_sLocalThetaSobolevAction_twist {G U H W : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
    (ι : H →L[ℂ] W) (j : U → H) (hj : DenseRange j) (E : U → W)
    (hι : ∀ u, ι (j u) = E u) (σ : G → U → U)
    (R : G →* (H →L[ℂ] H)) (hRc : Continuous fun p : G × H ↦ R p.1 p.2)
    (hRj : ∀ g u, R g (j u) = j (σ g u))
    (τ : G →* (W →L[ℂ] W)) (m : G →ₜ* ℝ≥0ˣ) (a : ℝ)
    (hE : ∀ g u, τ g (E u) = ((m g).val : ℝ) ^ a • E (σ g u)) :
    ∃ ρ : G →* (H →L[ℂ] H),
      (∀ g u, ι (ρ g u) = τ g (ι u)) ∧
      Continuous (fun p : G × H ↦ ρ p.1 p.2) ∧
      ∀ g u, ρ g (j u) = ((m g).val : ℝ) ^ a • j (σ g u) := by
  let c : G →* ℝ :=
    { toFun := fun g ↦ ((m g).val : ℝ) ^ a
      map_one' := by simp
      map_mul' := by
        intro g h
        simp only [map_mul, Units.val_mul, NNReal.coe_mul]
        exact Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) }
  have hc : Continuous c :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).rpow_const
      (fun g ↦ Or.inl (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  let ρ : G →* (H →L[ℂ] H) :=
    { toFun := fun g ↦ c g • R g
      map_one' := by ext u; simp
      map_mul' := by
        intro g h
        ext u
        change c (g * h) • R (g * h) u = c g • R g (c h • R h u)
        rw [map_mul, map_mul, mul_smul, (R g).map_smul_of_tower]
        rfl }
  refine ⟨ρ, ?_, (hc.comp continuous_fst).smul hRc, ?_⟩
  · intro g u
    have h : (fun x ↦ ι (ρ g x)) = (fun x ↦ τ g (ι x)) := by
      apply hj.equalizer (ι.continuous.comp (ρ g).continuous) ((τ g).continuous.comp ι.continuous)
      funext v
      change ι (c g • R g (j v)) = τ g (ι (j v))
      rw [ι.map_smul_of_tower, hRj, hι, hι, hE]
      rfl
    exact congrFun h u
  · intro g u
    change c g • R g (j u) = _
    rw [hRj]
    rfl
/-- Paper: Lemma 10.1.1.4(4), p. 436. Ambient left translation preserves the
S-local completion, acts jointly continuously there, and on weighted classes
it acts by translated theta classes times the factor |g|^(-a). -/
theorem exists_sLocalThetaSobolevAction {a α β s : ℝ} (ha : 0 < a)
    (hI : α ≤ β) (hs : 0 ≤ s) (hp : 0 < a + α) :
    ∃ ρ : Jₛ →* (Hₛ(ha, hI, hs, hp) →L[ℂ] Hₛ(ha, hI, hs, hp)),
      (∀ g u, (ρ g u : Wₛ(α, β, s)) = hardySobolevTranslation μₛ mₛ α β s hI hs g u) ∧
      Continuous (fun p : Jₛ × Hₛ(ha, hI, hs, hp) ↦ ρ p.1 p.2) ∧
      ∀ (g : Jₛ) (u : Θₛ), ρ g (jₛ(ha, hI, hs, hp) u) =
        (((mₛ g).val : ℝ) ^ (-a) : ℝ) • jₛ(ha, hI, hs, hp) (ρₛ g u) := by
  let μ := μₛ
  let m := mₛ
  let E := (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S)
    a α β s ha hI hs hp).exists.choose
  let σ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
  let hR := exists_sLocalThetaSobolevUnweightedAction (F := F) (S := S) ha hI hs hp
  with_reducible_and_instances
    simpa only [Submodule.subtypeL_apply] using exists_sLocalThetaSobolevAction_twist (G := SIdeleQuotient F S) (U := SLocalAdelicThetaSpace F S)
      (H := sLocalThetaSobolev F S ha hI hs hp)
      (W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) α β s)
      (ι := (sLocalThetaSobolev F S ha hI hs hp).subtypeL)
      (j := fun u ↦ sLocalThetaSobolevInclusion F S ha hI hs hp u)
      (sLocalThetaSobolev_dense ha hI hs hp) (fun u ↦ E u) (fun _ ↦ rfl)
      (fun g u ↦ σ g u) hR.choose hR.choose_spec.1 hR.choose_spec.2
      (hardySobolevTranslation μ m α β s hI hs) m (-a)
      (exists_sLocalThetaSobolevUnweightedAction_lift μ _ (withDensity_absolutelyContinuous μ _) m a
        (QuotientGroup.mk : (SAdeleRing F S)ˣ → SIdeleQuotient F S) QuotientGroup.mk_surjective
        (Submodule.Quotient.mk : SchwartzBruhat (Multiplicative (SAdeleRing F S)) → SLocalAdelicThetaSpace F S)
        (Submodule.Quotient.mk_surjective _) E (fun g u ↦ σ g u)
        (fun g u ↦ hardySobolevTranslation μ m α β s hI hs g u)
        (fun f x ↦ sLocalAdelicThetaOnClasses F S f x) schwartzBruhatUnitTranslate
        (existsUnique_sLocalThetaSobolevEmbedding (F := F) (S := S) a α β s ha hI hs hp).exists.choose_spec.2
        (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
        (hardySobolevTranslation_apply μ m α β s hI hs)
        (fun g f x ↦ sLocalTheta_translate_onClasses g f x)
        (fun g ↦ (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving))

local notation "Rₛ(" ha ", " hI ", " hs ", " hp ")" =>
  (exists_sLocalThetaSobolevAction (F := F) (S := S) ha hI hs hp).choose


/-- Paper: §10.1.1, p. 436. The paper's pairing on the weighted S-idelic
L² space is the integral of the first function times the conjugate of the second.
Deviation: Swap the arguments of Mathlib's conjugate-linear-first inner product. -/
theorem sIdeleIntervalSobolev_inner (α β s : ℝ)
    (u v : Lp ℂ 2 (sIdeleIntervalSobolevMeasure F S α β s)) :
    inner ℂ v u =
      ∫ g : Iₛ, u g * star (v g) ∂(sIdeleIntervalSobolevMeasure F S α β s) := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, starRingEnd_apply]

-- TODO(paper-gap): The global spaces in Proposition 10.1.1.5 drop the subscript 0.
-- At weight zero the usual rational adelic Gaussian does not have square-integrable theta.
-- The raw averages from (10.1.1.8) and (10.1.1.9) carry the norm-one Haar mass.

section GlobalIsotypes

variable {a α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s)

local notation "H" => ↥(H𝔽(a, hI, hs))
local notation "ρ₁" => (R𝔽(a, hI, hs)).comp (ideleClassNorm F).ker.subtype
local notation "Hω(" ω ")" => actionIsotype ρ₁ ω

section

universe u v

/-- The compact-group average, restricted to its isotype, is a unique open surjection. -/
private theorem existsUnique_thetaSobolevAverage_of_compact
    {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [T2Space N] [CompactSpace N] [MeasurableSpace N] [BorelSpace N]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure N) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2) (ω : PontryaginDual N) :
    ∃! A : E →L[ℂ] actionIsotype (ρ.comp N.subtype) ω,
      IsPettisIsotypicAverageOn μ univ (ρ.comp N.subtype) ω
        ((actionIsotype (ρ.comp N.subtype) ω).subtypeL.comp A) ∧
      Surjective A ∧ IsOpenMap A := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hc : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  obtain ⟨P, hP, huniq⟩ := existsUnique_globalThetaIsotypicAverage_of_compact N hc μ ρ hρ ω
  have hcρ : Continuous (fun p : N × E ↦ (ρ.comp N.subtype) p.1 p.2) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hr := compactActionAverage_range μ (ρ.comp N.subtype) hcρ ω P hP
  let V := actionIsotype (ρ.comp N.subtype) ω
  have hmem (x : E) : P x ∈ V := by
    change P x ∈ actionIsotype (ρ.comp N.subtype) ω
    rw [← hr]
    exact LinearMap.mem_range_self P.toLinearMap x
  let A : E →L[ℂ] V := P.codRestrict V hmem
  have hcomp : V.subtypeL.comp A = P := by ext; rfl
  have hsurj : Surjective A := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (show x ∈ LinearMap.range P.toLinearMap from hr.symm ▸ hx)
    exact ⟨y, Subtype.ext hy⟩
  obtain ⟨e, he⟩ := compactActionAverage_quotient_equiv μ (ρ.comp N.subtype) hcρ ω P hP
  have hA : (A : E → V) = e ∘ P.ker.mkQ := by
    funext x
    exact Subtype.ext (he x).symm
  refine ⟨A, ⟨by rwa [hcomp], hsurj, ?_⟩, ?_⟩
  · rw [hA]
    exact e.isOpenMap.comp P.ker.isOpenMap_mkQ
  · intro B hB
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (huniq _ hB.1) x

end

/-- Paper: Proposition 10.1.1.5(1), p. 436. The global Pettis average for the
norm-one Tamagawa measure is a continuous open linear surjection onto its isotype.
Deviation: Use polar-free global theta functions, as in Definition 10.1.1.1(1). -/
theorem existsUnique_globalThetaSobolevAverage (ω : PontryaginDual C₁) :
    ∃! P : H →L[ℂ] Hω(ω),
      IsPettisIsotypicAverageOn μ𝔽₁ univ ρ₁ ω ((Hω(ω)).subtypeL.comp P) ∧
      Surjective P ∧ IsOpenMap P := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : CompleteSpace H := (globalThetaSobolev_closed_complete_separable a hI hs).2.1
  with_reducible_and_instances
    exact existsUnique_thetaSobolevAverage_of_compact (E := H) (ideleClassNorm F).ker
      μ𝔽₁ (R𝔽(a, hI, hs)) (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.2.1 ω

local notation "P(" ω ")" =>
  (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose

/-- Paper: Proposition 10.1.1.5(1), pp. 436–437. The global isotype completes
the polar-free homogeneous classes of §6.3 with their weighted function norm.
On representatives its inclusion is the unnormalized homogeneous theta function.
Deviation: The global domain uses polar-free tests. -/
theorem exists_globalHomogeneousThetaSobolevInclusion (ω : PontryaginDual C₁) :
    ∃ j : ↥(globalPolarFreeThetaSubmodule (F := F) ω) →L[ℂ] Hω(ω),
      Injective j ∧ DenseRange j ∧
       ∀ (f : ℬ₀) (x : globalPolarFreeThetaSubmodule (F := F) ω),
        x.val = Submodule.Quotient.mk f.val →
          j x = P(ω) (j𝔽(a, hI, hs) (Submodule.Quotient.mk f)) ∧
          ((j x).val.val : C𝔽 → ℂ) =ᵐ[μ𝔽]
            modulationWeight m𝔽 a (homogeneousAdelicTheta ω f.val) := by sorry

section

universe u v

/-- The kernel of a compact isotypic average is the closed span of twisted differences. -/
private theorem thetaSobolevAverage_quotient_equiv_of_compact
    {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2) (ω : PontryaginDual G)
    (P : E →L[ℂ] actionIsotype ρ ω)
    (hP : IsPettisIsotypicAverageOn μ univ ρ ω ((actionIsotype ρ ω).subtypeL.comp P)) :
    let D := (Submodule.span ℂ (range (fun p : G × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2))).topologicalClosure
    ∃ T : (E ⧸ D) ≃L[ℂ] actionIsotype ρ ω, ∀ u, T (D.mkQ u) = P u := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let Q := (actionIsotype ρ ω).subtypeL.comp P
  have hker := compactActionAverage_ker μ ρ hρ ω Q hP
  obtain ⟨e, he⟩ := compactActionAverage_quotient_equiv μ ρ hρ ω Q hP
  dsimp only
  rw [← hker]
  exact ⟨e, fun u ↦ Subtype.ext (he u)⟩

end

/-- Paper: Proposition 10.1.1.5(1), p. 437. The global raw average induces a
topological linear isomorphism from the completed homogeneous quotient to the isotype.
Deviation: Use polar-free tests. The completed coinvariant quotient is realized by
dividing the completed space by the closed span of the twisted differences. -/
theorem globalThetaSobolevAverage_quotient_equiv (ω : PontryaginDual C₁) :
    let D := (Submodule.span ℂ (range (fun p : C₁ × H ↦
      p.2 - star (ω p.1 : ℂ) • ρ₁ p.1 p.2))).topologicalClosure
    ∃ T : (H ⧸ D) ≃L[ℂ] Hω(ω), ∀ u : H, T (D.mkQ u) = P(ω) u := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (μ𝔽₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hρ : Continuous (fun p : C₁ × H ↦ ρ₁ p.1 p.2) :=
    (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.2.1.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  with_reducible_and_instances
    exact thetaSobolevAverage_quotient_equiv_of_compact μ𝔽₁ ρ₁ hρ ω (P(ω))
      (existsUnique_globalThetaSobolevAverage (F := F) (a := a) hI hs ω).exists.choose_spec.1

/-- Paper: Proposition 10.1.1.5(2), p. 437. The global coordinate map is a
continuous injection into the product and factors through the isometric Hilbert sum.
Deviation: Use the polar-free space and divide each raw average by the mass of
the norm-one Tamagawa measure. The homogeneous targets are identified with their isotypes. -/
theorem globalThetaSobolev_isotypeDecomposition :
    ∃ (Pprod : H →L[ℂ] (∀ ω : PontryaginDual C₁, Hω(ω)))
      (T : H ≃ₗᵢ[ℂ] lp (fun ω : PontryaginDual C₁ ↦ ↥(Hω(ω))) 2),
      Injective Pprod ∧ ∀ (u : H) (ω : PontryaginDual C₁),
        Pprod u ω = T u ω ∧ T u ω = (Measure.real μ𝔽₁ univ)⁻¹ • P(ω) u := by sorry

end GlobalIsotypes

section SLocalIsotypes

variable {a α β s : ℝ} (ha : 0 < a) (hI : α ≤ β) (hs : 0 ≤ s) (hα : 0 < α)

local notation "hp" => (add_pos ha hα)
local notation "H" => ↥(Hₛ(ha, hI, hs, hp))
local notation "ρ₁" => (Rₛ(ha, hI, hs, hp)).comp (sIdeleQuotientNorm F S).ker.subtype
local notation "Hω(" ω ")" => actionIsotype ρ₁ ω

/-- Paper: Proposition 10.1.1.5(1), pp. 436–437. The S-local Pettis average for
the norm-one quotient measure is a continuous open linear surjection onto its isotype.
Deviation: The letter a represents the local weight b of the proposition. -/
theorem existsUnique_sLocalThetaSobolevAverage (ω : PontryaginDual J₁) :
    ∃! P : H →L[ℂ] Hω(ω),
      IsPettisIsotypicAverageOn μₛ₁ univ ρ₁ ω ((Hω(ω)).subtypeL.comp P) ∧
      Surjective P ∧ IsOpenMap P := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : CompleteSpace H := (sLocalThetaSobolev_closed_complete_separable ha hI hs hp).2.1
  with_reducible_and_instances
    exact existsUnique_thetaSobolevAverage_of_compact (E := H) (sIdeleQuotientNorm F S).ker
      μₛ₁ (Rₛ(ha, hI, hs, hp))
      (exists_sLocalThetaSobolevAction (F := F) (S := S) ha hI hs hp).choose_spec.2.1 ω

local notation "P(" ω ")" =>
  (existsUnique_sLocalThetaSobolevAverage (F := F) (S := S) ha hI hs hα ω).exists.choose

/-- Paper: Proposition 10.1.1.5(1), pp. 436–437. The S-local isotype completes
the homogeneous classes of §5.2 with their weighted function norm. Its test-class
inclusion is given by the unnormalized S-local homogeneous theta function. -/
theorem exists_sLocalHomogeneousThetaSobolevInclusion (ω : PontryaginDual J₁) :
    ∃ j : SLocalHomogeneousThetaSpace F S ω →L[ℂ] Hω(ω),
      Injective j ∧ DenseRange j ∧ ∀ f : ℬₛ,
        j (Submodule.Quotient.mk f) = P(ω) (jₛ(ha, hI, hs, hp) (Submodule.Quotient.mk f)) ∧
        ((j (Submodule.Quotient.mk f)).val.val : Jₛ → ℂ) =ᵐ[μₛ]
          modulationWeight mₛ a (sLocalHomogeneousAdelicThetaLinearMap F S ω f) := by sorry

/-- Paper: Proposition 10.1.1.5(1), p. 437. The S-local raw average induces a
topological linear isomorphism from the completed homogeneous quotient to the isotype.
Deviation: The completed coinvariant quotient is realized by dividing the completed
space by the closed span of the twisted differences. -/
theorem sLocalThetaSobolevAverage_quotient_equiv (ω : PontryaginDual J₁) :
    let D := (Submodule.span ℂ (range (fun p : J₁ × H ↦
      p.2 - star (ω p.1 : ℂ) • ρ₁ p.1 p.2))).topologicalClosure
    ∃ T : (H ⧸ D) ≃L[ℂ] Hω(ω), ∀ u : H, T (D.mkQ u) = P(ω) u := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (μₛ₁).IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hρ : Continuous (fun p : J₁ × H ↦ ρ₁ p.1 p.2) :=
    (exists_sLocalThetaSobolevAction (F := F) (S := S) ha hI hs hp).choose_spec.2.1.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  with_reducible_and_instances
    exact thetaSobolevAverage_quotient_equiv_of_compact μₛ₁ ρ₁ hρ ω (P(ω))
      (existsUnique_sLocalThetaSobolevAverage (F := F) (S := S) ha hI hs hα ω).exists.choose_spec.1

/-- Paper: Proposition 10.1.1.5(2), p. 437. The S-local coordinate map is a
continuous injection into the product and factors through the isometric Hilbert sum.
Deviation: Divide each raw average by the mass of the norm-one quotient measure.
The homogeneous targets are identified with their isotypes. -/
theorem sLocalThetaSobolev_isotypeDecomposition :
    ∃ (Pprod : H →L[ℂ] (∀ ω : PontryaginDual J₁, Hω(ω)))
      (T : H ≃ₗᵢ[ℂ] lp (fun ω : PontryaginDual J₁ ↦ ↥(Hω(ω))) 2),
      Injective Pprod ∧ ∀ (u : H) (ω : PontryaginDual J₁),
        Pprod u ω = T u ω ∧ T u ω = (Measure.real μₛ₁ univ)⁻¹ • P(ω) u := by sorry

end SLocalIsotypes

section Fourier

-- TODO(paper-gap): The ambient inversion automorphism in Theorem 10.1.2.1
-- fails for nonsymmetric I. The types in (10.1.2.5) also swap the weight labels.

/-- Reflecting the logarithmic coordinate reflects the interval of the density. -/
private theorem ideleClassSobolevInversion_density (α β s x : ℝ) :
    intervalSobolevDensity α β s (-x) = intervalSobolevDensity (-β) (-α) s x := by
  unfold intervalSobolevDensity
  rw [max_comm, neg_sq]
  congr 3 <;> ring

/-- Inversion carries the reflected weighted measure to the weighted measure. -/
private theorem ideleClassSobolevInversion_measurePreserving {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (L : G → ℝ)
    (hL : ∀ g, L g⁻¹ = - L g) (α β s : ℝ) :
    MeasurePreserving Inv.inv
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-β) (-α) s (L x)))
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity α β s (L x))) := by
  refine ⟨measurable_inv, ?_⟩
  ext A hA
  rw [Measure.map_apply measurable_inv hA, withDensity_apply _ hA,
    withDensity_apply _ (measurable_inv hA), ← lintegral_indicator hA,
    ← lintegral_indicator (measurable_inv hA), ← lintegral_inv_eq_self]
  congr 1
  funext g
  simp only [Set.indicator, hL, neg_neg, ideleClassSobolevInversion_density]
  classical
  exact if_congr (by simp) rfl rfl

/-- Inversion as an isometry between weighted L² spaces for reflected intervals, on an
abstract group with an inversion-invariant measure. -/
private theorem ideleClassSobolevInversion_aux {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (L : G → ℝ)
    (hLm : Measurable L) (hL : ∀ g, L g⁻¹ = - L g) (α β s : ℝ) :
    ∃! J : CompactIntervalSobolev μ L α β s ≃ₗᵢ[ℂ] CompactIntervalSobolev μ L (-β) (-α) s,
      ∀ u, (J u : G → ℂ) =ᵐ[μ] fun g ↦ u g⁻¹ := by
  have h := ideleClassSobolevInversion_measurePreserving μ L hL α β s
  have h' : MeasurePreserving Inv.inv
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity α β s (L x)))
      (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-β) (-α) s (L x))) := by
    simpa only [neg_neg] using ideleClassSobolevInversion_measurePreserving μ L hL (-β) (-α) s
  have hpos (a b : ℝ) (x : G) : ENNReal.ofReal (intervalSobolevDensity a b s (L x)) ≠ 0 := by
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  have hmeas (a b : ℝ) :
      Measurable fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (L x)) := by
    unfold intervalSobolevDensity
    fun_prop
  -- almost-everywhere statements for the weighted measure give ones for μ
  have hae (a b : ℝ) {f g : G → ℂ}
      (hfg : f =ᵐ[μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (L x))] g) :
      f =ᵐ[μ] g := by
    rw [Filter.EventuallyEq, ae_withDensity_iff (hmeas a b)] at hfg
    filter_upwards [hfg] with x hx using hx (hpos a b x)
  let T := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ Inv.inv h
  let T' := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ Inv.inv h'
  have hTT' (u) : T (T' u) = u := by
    apply Lp.ext
    refine (Lp.coeFn_compMeasurePreserving _ h).trans ?_
    refine ((h.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving u h'))).trans ?_
    filter_upwards with x
    simp
  have hT'T (u) : T' (T u) = u := by
    apply Lp.ext
    refine (Lp.coeFn_compMeasurePreserving _ h').trans ?_
    refine ((h'.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving u h))).trans ?_
    filter_upwards with x
    simp
  let J : CompactIntervalSobolev μ L α β s ≃ₗᵢ[ℂ] CompactIntervalSobolev μ L (-β) (-α) s :=
    { toLinearEquiv := LinearEquiv.ofLinearMap T.toLinearMap T'.toLinearMap
        (LinearMap.ext hTT') (LinearMap.ext hT'T)
      norm_map' := T.norm_map }
  refine ⟨J, fun u ↦ hae (-β) (-α) (Lp.coeFn_compMeasurePreserving u h), ?_⟩
  intro J₂ hJ₂
  refine LinearIsometryEquiv.ext fun u ↦ Lp.ext ?_
  have h₁ := hJ₂ u
  have h₂ := hae (-β) (-α) (Lp.coeFn_compMeasurePreserving u h)
  exact (withDensity_absolutelyContinuous _ _).ae_le (h₁.trans h₂.symm)

/-- Paper: Theorem 10.1.2.1, p. 437. Inversion gives an isometric linear
equivalence of the ambient Sobolev spaces for opposite intervals.
Deviation: The target interval is [-β,-α]. Inversion is an automorphism at I = -I. -/
theorem existsUnique_ideleClassSobolevInversion (α β s : ℝ) (_hI : α ≤ β) (_hs : 0 ≤ s) :
    ∃! J : W𝔽(α, β, s) ≃ₗᵢ[ℂ] W𝔽(-β, -α, s),
      ∀ u, (J u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ u g⁻¹ := by
  have : (μ𝔽).Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hLm : Measurable fun g : C𝔽 ↦ Real.log (((m𝔽 g).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne').measurable
  exact ideleClassSobolevInversion_aux μ𝔽 _ hLm
    (fun g ↦ by simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]) α β s

local notation "J𝔽(" hI ", " hs ")" =>
  (existsUnique_ideleClassSobolevInversion (F := F) _ _ _ hI hs).exists.choose

/-- If a constant is bounded by `K / r` for arbitrarily large `r`, it vanishes. -/
private theorem adelePolarSubspace_fourier_eq_zero (c : ℂ) (K T : ℝ)
    (h : ∀ R : ℝ, T < R → ‖c‖ ≤ K * R⁻¹) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set R : ℝ := max (T + 1) ((|K| + 1) / ‖c‖ + 1) with hR
  have hR1 : T < R := (lt_add_one T).trans_le (le_max_left _ _)
  have hR2 : (|K| + 1) / ‖c‖ < R := (lt_add_one _).trans_le (le_max_right _ _)
  have hR0 : 0 < R := (div_pos (by positivity) hpos).trans hR2
  have h1 := h R hR1
  have h2 : K * R⁻¹ < ‖c‖ := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hR0]
    rw [div_lt_iff₀ hpos] at hR2
    nlinarith [le_abs_self K]
  linarith

/-- Riemann–Roch for a theta transform, together with decay at large norm, forces the
double Fourier transform of a test with two vanishing polar values to vanish at zero.
Stated for abstract data, so that it elaborates without unfolding the adelic types. -/
private theorem adelePolarSubspace_fourier_abstract {B X : Type*} [InvolutiveInv X]
    (Θ : B → X → ℂ) (Fo : B → B) (e : B → ℂ) (n : X → ℝ)
    (hn : ∀ g, n g⁻¹ = (n g)⁻¹) (hpos : ∀ g, 0 < n g)
    (hRR : ∀ f g, Θ f g = (n g)⁻¹ • Θ (Fo f) g⁻¹ + (n g)⁻¹ • e (Fo f) - e f)
    (hdec : ∀ f, ∃ K T : ℝ, 0 < K ∧ 0 < T ∧ ∀ g, T < n g → ‖Θ f g‖ ≤ K * ((n g) ^ 1)⁻¹)
    (hsurj : ∀ R : ℝ, 0 < R → ∃ g, n g = R)
    (f : B) (hf0 : e f = 0) (hF0 : e (Fo f) = 0) : e (Fo (Fo f)) = 0 := by
  have hid (g : X) : Θ f g = Θ (Fo (Fo f)) g + e (Fo (Fo f)) := by
    have h1 := hRR f g
    have h2 := hRR (Fo f) g⁻¹
    have hr : n g ≠ 0 := (hpos g).ne'
    simp only [hf0, hF0, smul_zero, add_zero, sub_zero, inv_inv, hn] at h1 h2
    rw [h1, h2, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hr, one_smul, one_smul]
  obtain ⟨K₁, T₁, -, -, hd₁⟩ := hdec f
  obtain ⟨K₂, T₂, -, -, hd₂⟩ := hdec (Fo (Fo f))
  refine adelePolarSubspace_fourier_eq_zero _ (K₁ + K₂) (max T₁ (max T₂ 0)) fun R hR ↦ ?_
  have hR0 : 0 < R := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hR)
  obtain ⟨g, hgR⟩ := hsurj R hR0
  have hT₁ : T₁ < n g := hgR ▸ (le_max_left _ _).trans_lt hR
  have hT₂ : T₂ < n g := hgR ▸ (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hR)
  have e₁ := hd₁ g hT₁
  have e₂ := hd₂ g hT₂
  rw [hgR, pow_one] at e₁ e₂
  rw [eq_sub_of_add_eq' (hid g).symm]
  calc _ ≤ ‖Θ f g‖ + ‖Θ (Fo (Fo f)) g‖ := norm_sub_le _ _
    _ ≤ K₁ * R⁻¹ + K₂ * R⁻¹ := add_le_add e₁ e₂
    _ = _ := by ring

/-- Paper: (10.1.2.2)–(10.1.2.4), pp. 437–438. Fourier transform preserves
the polar-free test space, so the global theta Fourier transform restricts to it. -/
theorem adelePolarSubspace_fourier (f : ℬ₀) :
    adeleSchwartzFourier f.val ∈ adelePolarSubspace F := by
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  rw [mem_adelePolarSubspace]
  refine ⟨hz.2, ?_⟩
  have hsurj : Surjective (ideleClassNorm F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  have hn (g : C𝔽) :
      ((ideleClassNorm F g⁻¹ : NNReal) : ℝ) = ((ideleClassNorm F g : NNReal) : ℝ)⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have hR (R : ℝ) (hR : 0 < R) :
      ∃ g : C𝔽, ((ideleClassNorm F g : NNReal) : ℝ) = R := by
    obtain ⟨g, hg⟩ := hsurj (Units.mk0 R.toNNReal (by simpa using hR))
    exact ⟨g, by rw [hg, Units.val_mk0, Real.coe_toNNReal _ hR.le]⟩
  have hRR := adelicTheta_riemannRoch (F := F)
  have hdec := fun f ↦ adelicTheta_decay_large (F := F) f 1
  exact adelePolarSubspace_fourier_abstract (fun f g ↦ adelicTheta (F := F) f g)
    adeleSchwartzFourier (fun f ↦ f (Multiplicative.ofAdd 0))
    (fun g ↦ ((ideleClassNorm F g : NNReal) : ℝ)) hn hpos hRR hdec hR f.val hz.1 hz.2

local notation "fourier₀(" f ")" =>
  (⟨adeleSchwartzFourier (f : ℬ₀).val, adelePolarSubspace_fourier f⟩ : ℬ₀)

/-- Paper: (10.1.2.4), p. 438. The weight-a theta function of the Fourier test
equals inversion of the theta function at complementary weight 1-a. -/
theorem globalThetaSobolev_fourier_weight (a : ℝ) (f : ℬ₀) (g : C𝔽) :
    modulationWeight m𝔽 a (θ𝔽(fourier₀(f))) g =
      modulationWeight m𝔽 (1 - a) (θ𝔽(f)) g⁻¹ := by
  have weights (r t : ℝ) (x y : ℂ) (hr : 0 < r) (ht : t = r⁻¹) (hy : y = r • x) :
      (↑(r ^ a) : ℂ) * x = (↑(t ^ (1 - a)) : ℂ) * y := by
    have hpow : (r⁻¹) ^ (1 - a) * r = r ^ a := by
      rw [← Real.rpow_neg_eq_inv_rpow]
      calc
        _ = r ^ (-(1 - a)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = r ^ a := by
          rw [← Real.rpow_add hr]
          congr 1
          ring
    rw [ht, hy, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hpow]
  let r : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have hinv : ((ideleClassNorm F g⁻¹).val : ℝ) = r⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, r]
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  have hθ : adelicTheta (F := F) f.val g⁻¹ =
      r • adelicTheta (F := F) (adeleSchwartzFourier (F := F) f.val) g := by
    simpa only [hz.1, hz.2, smul_zero, add_zero, sub_zero, inv_inv, hinv]
      using adelicTheta_riemannRoch (F := F) f.val g⁻¹
  exact weights r ((ideleClassNorm F g⁻¹).val : ℝ) _ _ hr hinv hθ

/-- A continuous linear map that preserves a submodule, preserves the kernel of a linear map
on it, and is an involution modulo that kernel induces a unique continuous linear automorphism
of the quotient. Stated for abstract modules, so that it elaborates without unfolding the
Schwartz–Bruhat instances. -/
private theorem existsUnique_globalPolarFreeThetaFourier_quotient {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [AddCommGroup N] [Module ℂ N]
    (P : Submodule ℂ M) (θ : M →ₗ[ℂ] N) (Φ : M →L[ℂ] M) (φ : M → M) (hΦ : ∀ f, Φ f = φ f)
    (hP : ∀ f : P, φ f ∈ P) (hker : ∀ f : P, θ f = 0 → θ (φ f) = 0)
    (hinv : ∀ f : P, θ (φ (φ f)) = θ f) :
    ∃! T : (P ⧸ (LinearMap.ker θ).comap P.subtype) ≃L[ℂ]
        (P ⧸ (LinearMap.ker θ).comap P.subtype),
      ∀ f : P, T (Submodule.Quotient.mk f) = Submodule.Quotient.mk ⟨φ f, hP f⟩ := by
  set Q := (LinearMap.ker θ).comap P.subtype
  let Φ₀ : P →L[ℂ] P := (Φ.comp P.subtypeL).codRestrict P fun f ↦ by
    rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hΦ]
    exact hP f
  have hΦ₀ (f : P) : Φ₀ f = ⟨φ f, hP f⟩ := Subtype.ext (hΦ f)
  have hQ : Q ≤ (Q.mkQL.comp Φ₀).ker := by
    intro f hf
    change Q.mkQ (Φ₀ f) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hΦ₀]
    exact hker f hf
  let T₀ := Q.liftQL (Q.mkQL.comp Φ₀) hQ
  have hT₀ (f : P) : T₀ (Submodule.Quotient.mk f) = Submodule.Quotient.mk ⟨φ f, hP f⟩ := by
    change Q.mkQ (Φ₀ f) = _
    rw [hΦ₀]
    rfl
  have hTT (x : P ⧸ Q) : T₀ (T₀ x) = x := by
    refine Submodule.Quotient.induction_on _ x fun f ↦ ?_
    rw [hT₀, hT₀, Submodule.Quotient.eq, Submodule.mem_comap, LinearMap.mem_ker, map_sub,
      map_sub]
    change θ (φ (φ f)) - θ f = 0
    rw [hinv, sub_self]
  refine ⟨ContinuousLinearEquiv.equivOfInverse T₀ T₀ hTT hTT, hT₀, fun T hT ↦ ?_⟩
  refine ContinuousLinearEquiv.ext (funext fun x ↦ ?_)
  refine Submodule.Quotient.induction_on _ x fun f ↦ ?_
  exact (hT f).trans (hT₀ f).symm

/-- Riemann–Roch for a theta transform, for a test whose polar values vanish together with
those of its Fourier transform: the Fourier transform preserves vanishing of theta, and the
double Fourier transform has the same theta. Stated for abstract data, so that it elaborates
without unfolding the adelic types. -/
private theorem existsUnique_globalPolarFreeThetaFourier_rr {B X : Type*} [InvolutiveInv X]
    (Θ : B → X → ℂ) (Fo : B → B) (e : B → ℂ) (n : X → ℝ)
    (hn : ∀ g, n g⁻¹ = (n g)⁻¹) (hpos : ∀ g, 0 < n g)
    (hRR : ∀ f g, Θ f g = (n g)⁻¹ • Θ (Fo f) g⁻¹ + (n g)⁻¹ • e (Fo f) - e f)
    (f : B) (hf0 : e f = 0) (hF0 : e (Fo f) = 0) :
    ((∀ g, Θ f g = 0) → ∀ g, Θ (Fo f) g = 0) ∧
      (e (Fo (Fo f)) = 0 → ∀ g, Θ (Fo (Fo f)) g = Θ f g) := by
  refine ⟨fun hΘ g ↦ ?_, fun hFF0 g ↦ ?_⟩
  · have h := hRR f g⁻¹
    simp only [hf0, hF0, smul_zero, add_zero, sub_zero, inv_inv, hn, hΘ] at h
    exact (smul_eq_zero.mp h.symm).resolve_left (hpos g).ne'
  · have h1 := hRR f g
    have h2 := hRR (Fo f) g⁻¹
    have hr : n g ≠ 0 := (hpos g).ne'
    simp only [hf0, hF0, smul_zero, add_zero, sub_zero, inv_inv, hn] at h1 h2
    rw [h1, h2, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hr, one_smul, one_smul, hFF0,
      add_zero]

/-- The Fourier transform of a polar-free test whose theta vanishes has vanishing theta. -/
private theorem existsUnique_globalPolarFreeThetaFourier_ker (f : ℬ₀)
    (hf : adelicThetaLinearMap F f.val = 0) :
    adelicThetaLinearMap F (adeleSchwartzFourier f.val) = 0 := by
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  have hn (g : C𝔽) :
      ((ideleClassNorm F g⁻¹ : NNReal) : ℝ) = ((ideleClassNorm F g : NNReal) : ℝ)⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have h := (existsUnique_globalPolarFreeThetaFourier_rr (fun f g ↦ adelicTheta (F := F) f g)
    adeleSchwartzFourier (fun f ↦ f (Multiplicative.ofAdd 0))
    (fun g ↦ ((ideleClassNorm F g : NNReal) : ℝ)) hn hpos (adelicTheta_riemannRoch (F := F))
    f.val hz.1 hz.2).1 fun g ↦ DFunLike.congr_fun hf g
  exact ContinuousMap.ext h

/-- The double Fourier transform of a polar-free test has the same theta. -/
private theorem existsUnique_globalPolarFreeThetaFourier_inv (f : ℬ₀) :
    adelicThetaLinearMap F (adeleSchwartzFourier (adeleSchwartzFourier f.val)) =
      adelicThetaLinearMap F f.val := by
  have hz := (mem_adelePolarSubspace (F := F) f.val).mp f.property
  have hz' := (mem_adelePolarSubspace (F := F) (adeleSchwartzFourier f.val)).mp
    (adelePolarSubspace_fourier f)
  have hn (g : C𝔽) :
      ((ideleClassNorm F g⁻¹ : NNReal) : ℝ) = ((ideleClassNorm F g : NNReal) : ℝ)⁻¹ := by
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have h := (existsUnique_globalPolarFreeThetaFourier_rr (fun f g ↦ adelicTheta (F := F) f g)
    adeleSchwartzFourier (fun f ↦ f (Multiplicative.ofAdd 0))
    (fun g ↦ ((ideleClassNorm F g : NNReal) : ℝ)) hn hpos (adelicTheta_riemannRoch (F := F))
    f.val hz.1 hz.2).2 hz'.2
  exact ContinuousMap.ext h

/-- Paper: Theorem 10.1.2.1, pp. 437–438. The polar-free theta quotient has the
continuous Fourier automorphism induced by the adelic transform of its tests. -/
theorem existsUnique_globalPolarFreeThetaFourier :
    ∃! T : Θ₀ ≃L[ℂ] Θ₀, ∀ f : ℬ₀,
      T (Submodule.Quotient.mk f) = Submodule.Quotient.mk (fourier₀(f)) := by
  obtain ⟨Φ, hΦ⟩ := exists_adeleFourier_clm (F := F)
  exact existsUnique_globalPolarFreeThetaFourier_quotient (adelePolarSubspace F)
    (adelicThetaLinearMap F) Φ adeleSchwartzFourier hΦ adelePolarSubspace_fourier
    existsUnique_globalPolarFreeThetaFourier_ker existsUnique_globalPolarFreeThetaFourier_inv

local notation "Fourier𝔽" => (existsUnique_globalPolarFreeThetaFourier (F := F)).exists.choose

/-- A map that intertwines two maps through a surjection of their common domain sends the
range of the first onto the range of the second. -/
private theorem exists_globalThetaSobolevInversion_image {X W₁ W₂ : Type*} (k : W₁ → W₂)
    (e₁ : X → W₁) (e₂ : X → W₂) (Fo : X → X) (hFo : Surjective Fo)
    (h : ∀ x, k (e₁ x) = e₂ (Fo x)) : k '' range e₁ = range e₂ := by
  rw [← range_comp]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Fo x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hFo x
    exact ⟨z, h z⟩

/-- Inversion carries the weight-a theta embedding of a polar-free test to the weight-(1-a)
theta embedding of its Fourier transform. -/
private theorem exists_globalThetaSobolevInversion_mk (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) (f : ℬ₀) :
    J𝔽(hI, hs) (E𝔽(a, hI, hs) (Submodule.Quotient.mk f)) =
      E𝔽(1 - a, neg_le_neg hI, hs) (Submodule.Quotient.mk (fourier₀(f))) := by
  have : (μ𝔽).Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hinvMP : MeasurePreserving (fun g : C𝔽 ↦ g⁻¹) μ𝔽 μ𝔽 := Measure.measurePreserving_inv μ𝔽
  have hK := (existsUnique_ideleClassSobolevInversion (F := F) α β s hI hs).exists.choose_spec
  have hE₁ := (existsUnique_globalThetaSobolevEmbedding (F := F) a α β s hI hs).exists.choose_spec.2
  have hE₂ := (existsUnique_globalThetaSobolevEmbedding (F := F) (1 - a) (-β) (-α) s
    (neg_le_neg hI) hs).exists.choose_spec.2
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have h₂ := hinvMP.quasiMeasurePreserving.ae_eq_comp (hE₁ f)
  filter_upwards [hK (E𝔽(a, hI, hs) (Submodule.Quotient.mk f)), h₂, hE₂ (fourier₀(f))]
    with g hg h₂ h₃
  rw [hg, h₃]
  refine h₂.trans ?_
  have hw := globalThetaSobolev_fourier_weight (F := F) (1 - a) f g
  rw [sub_sub_cancel] at hw
  exact hw.symm

/-- Inversion intertwines the weight-a and weight-(1-a) theta embeddings with the Fourier
automorphism of the polar-free theta space. -/
private theorem exists_globalThetaSobolevInversion_key (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) (u : Θ₀) :
    J𝔽(hI, hs) (E𝔽(a, hI, hs) u) = E𝔽(1 - a, neg_le_neg hI, hs) (Fourier𝔽 u) := by
  have hFo := (existsUnique_globalPolarFreeThetaFourier (F := F)).exists.choose_spec
  induction u using Quot.ind with
  | mk f =>
    exact (exists_globalThetaSobolevInversion_mk a hI hs f).trans
      (congrArg (E𝔽(1 - a, neg_le_neg hI, hs)) (hFo f).symm)

/-- Paper: Theorem 10.1.2.1, (10.1.2.1), and (10.1.2.5), pp. 437–438.
Ambient inversion restricts to an isometric equivalence of the weighted theta
completions and intertwines the weighted embeddings with Fourier transform.
Deviation: The target uses weight 1-a and reflected interval [-β,-α]. In the
commuting diagram each horizontal arrow uses the weight of its own target. -/
theorem exists_globalThetaSobolevInversion (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s) :
    ∃ J : H𝔽(a, hI, hs) ≃ₗᵢ[ℂ] H𝔽(1 - a, neg_le_neg hI, hs),
      (∀ u, (J u : W𝔽(-β, -α, s)) = J𝔽(hI, hs) u) ∧
      ∀ u : Θ₀, J (j𝔽(a, hI, hs) u) =
        j𝔽(1 - a, neg_le_neg hI, hs) (Fourier𝔽 u) := by
  refine ⟨((J𝔽(hI, hs)).submoduleMap _).trans (LinearIsometryEquiv.ofEq _ _ ?_),
    fun _ ↦ rfl, fun u ↦ Subtype.ext (exists_globalThetaSobolevInversion_key a hI hs u)⟩
  apply SetLike.coe_injective
  rw [Submodule.map_coe, Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe]
  change (J𝔽(hI, hs)).toHomeomorph '' closure (range (E𝔽(a, hI, hs))) =
    closure (range (E𝔽(1 - a, neg_le_neg hI, hs)))
  rw [Homeomorph.image_closure]
  exact congrArg closure (exists_globalThetaSobolevInversion_image _ _ _ _ (Fourier𝔽).surjective
    (exists_globalThetaSobolevInversion_key a hI hs))

/-- Inversion intertwines left translation by `g` with left translation by `g⁻¹`, for
closed subspaces of weighted L² spaces over an abstract commutative group. -/
private theorem globalThetaSobolevInversion_mem_isotype_key {G : Type*} [CommGroup G]
    [MeasurableSpace G] (μ : Measure G) {ν₁ : Measure G} (ν₂ : Measure G) (hν₂ : ν₂ ≪ μ)
    (hinv : Measure.QuasiMeasurePreserving (fun x : G ↦ x⁻¹) μ μ)
    (hmul : ∀ g : G, Measure.QuasiMeasurePreserving (fun x ↦ g * x) μ μ)
    (H₁ : Submodule ℂ (Lp ℂ 2 ν₁)) (H₂ : Submodule ℂ (Lp ℂ 2 ν₂))
    (Jamb : Lp ℂ 2 ν₁ → Lp ℂ 2 ν₂) (hJamb : ∀ v, (Jamb v : G → ℂ) =ᵐ[μ] fun x ↦ v x⁻¹)
    (J : H₁ ≃ₗᵢ[ℂ] H₂) (hJ : ∀ u, (J u : Lp ℂ 2 ν₂) = Jamb u)
    (T₁ : G → Lp ℂ 2 ν₁ → Lp ℂ 2 ν₁) (hT₁ : ∀ g v, (T₁ g v : G → ℂ) =ᵐ[μ] fun x ↦ v (g⁻¹ * x))
    (T₂ : G → Lp ℂ 2 ν₂ → Lp ℂ 2 ν₂) (hT₂ : ∀ g v, (T₂ g v : G → ℂ) =ᵐ[μ] fun x ↦ v (g⁻¹ * x))
    (ρ₁ : G →* (H₁ →L[ℂ] H₁)) (hρ₁ : ∀ g u, (ρ₁ g u : Lp ℂ 2 ν₁) = T₁ g u)
    (ρ₂ : G →* (H₂ →L[ℂ] H₂)) (hρ₂ : ∀ g u, (ρ₂ g u : Lp ℂ 2 ν₂) = T₂ g u)
    (g : G) (v : H₁) : J (ρ₁ g v) = ρ₂ g⁻¹ (J v) := by
  apply Subtype.ext
  rw [hJ, hρ₂, hJ, hρ₁]
  apply Lp.ext
  apply hν₂.ae_le
  have e₁ := hJamb (T₁ g v)
  have e₂ := hT₂ g⁻¹ (Jamb v)
  have e₃ := Measure.QuasiMeasurePreserving.ae hinv (hT₁ g v)
  have e₄ := Measure.QuasiMeasurePreserving.ae (hmul g) (hJamb v)
  filter_upwards [e₁, e₂, e₃, e₄] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, inv_inv, h₃, h₄, mul_inv, mul_comm]

/-- An intertwiner of `g` with `g⁻¹` carries the isotype of a character to the isotype of
the inverse character, stated for abstract spaces. -/
private theorem globalThetaSobolevInversion_mem_isotype_iff {G K E₁ E₂ : Type*} [CommGroup G]
    [CommGroup K] [TopologicalSpace K] [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℂ E₂] (J : E₁ ≃ₗᵢ[ℂ] E₂) (ρ₁ : G →* (E₁ →L[ℂ] E₁))
    (ρ₂ : G →* (E₂ →L[ℂ] E₂)) (key : ∀ g v, J (ρ₁ g v) = ρ₂ g⁻¹ (J v)) (ι : K →* G)
    (ω : PontryaginDual K) (u : E₁) :
    J u ∈ actionIsotype (ρ₂.comp ι) ω⁻¹ ↔ u ∈ actionIsotype (ρ₁.comp ι) ω := by
  have hω (k : K) : ((ω⁻¹ : PontryaginDual K) k) = (ω k)⁻¹ := rfl
  rw [mem_actionIsotype, mem_actionIsotype]
  simp only [MonoidHom.comp_apply]
  constructor
  · intro h k
    apply J.injective
    rw [key, J.map_smul, ← map_inv, h, hω, map_inv, inv_inv]
  · intro h k
    rw [show ι k = (ι k⁻¹)⁻¹ by rw [map_inv, inv_inv], ← key, h, J.map_smul, hω, map_inv]

/-- Paper: Theorem 10.1.2.1, p. 437. The induced inversion sends each norm-one
isotype onto the inverse-character isotype of the reflected completion. -/
theorem globalThetaSobolevInversion_mem_isotype (a : ℝ) {α β s : ℝ} (hI : α ≤ β)
    (hs : 0 ≤ s) (ω : PontryaginDual C₁) (u : H𝔽(a, hI, hs)) :
    let J := (exists_globalThetaSobolevInversion (F := F) a hI hs).choose
    J u ∈ actionIsotype ((R𝔽(1 - a, neg_le_neg hI, hs)).comp (ideleClassNorm F).ker.subtype) ω⁻¹ ↔
      u ∈ actionIsotype ((R𝔽(a, hI, hs)).comp (ideleClassNorm F).ker.subtype) ω := by
  intro J
  have : (μ𝔽).Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  have hinvMP : MeasurePreserving (fun g : C𝔽 ↦ g⁻¹) μ𝔽 μ𝔽 := Measure.measurePreserving_inv μ𝔽
  have hJ := (exists_globalThetaSobolevInversion (F := F) a hI hs).choose_spec.1
  have hR := (exists_globalThetaSobolevAction (F := F) a hI hs).choose_spec.1
  have hR' := (exists_globalThetaSobolevAction (F := F) (1 - a) (neg_le_neg hI) hs).choose_spec.1
  have hinv := (existsUnique_ideleClassSobolevInversion (F := F) α β s hI hs).exists.choose_spec
  have hT₁ := hardySobolevTranslation_apply μ𝔽 m𝔽 α β s hI hs
  have hT₂ := hardySobolevTranslation_apply μ𝔽 m𝔽 (-β) (-α) s (neg_le_neg hI) hs
  have key := globalThetaSobolevInversion_mem_isotype_key μ𝔽 _
    (withDensity_absolutelyContinuous μ𝔽 _) hinvMP.quasiMeasurePreserving
    (fun g ↦ (measurePreserving_mul_left μ𝔽 g).quasiMeasurePreserving) _ _ _ hinv J hJ _ hT₁ _ hT₂
    _ hR _ hR'
  exact globalThetaSobolevInversion_mem_isotype_iff J _ _ key (ideleClassNorm F).ker.subtype ω u

-- TODO(paper-gap): The unbounded multiplier argument on p. 438 is on the ambient W_I^s,
-- whereas necessity in the theorem needs unboundedness on the weighted theta subspace.

/-- Paper: Theorem 10.1.2.1(1)–(2), (10.1.2.2), pp. 437–438. On a symmetric compact
interval, the global Fourier transform extends uniquely to a continuous linear
automorphism of the same weighted completion exactly at weight one half. -/
theorem globalThetaSobolev_fourier_extension_iff (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let hI := (neg_nonpos.mpr hα).trans hα
    (∃! T : H𝔽(a, hI, hs) ≃L[ℂ] H𝔽(a, hI, hs), ∀ u : Θ₀,
      T (j𝔽(a, hI, hs) u) = j𝔽(a, hI, hs) (Fourier𝔽 u)) ↔ a = 1 / 2 := by sorry

-- TODO(paper-gap): The announcement on p. 435 extends beyond the degree-zero
-- local result on p. 438. For ℚ and S = {∞}, at a = 1/2, I = {0}, the even
-- Gaussians exp(-πx²) cos(2πNx) have bounded input norms for each s > 0.
-- Their Fourier transforms have a Gaussian peak at N, with squared weighted
-- norm bounded below by a positive constant times (log N)^s.

/-- Paper: (10.1.2.6), p. 438. The local weighted L² completion of §5.4
identifies isometrically with the degree-zero Sobolev completion at weight one half.
On test representatives the isometry multiplies by the square root of the norm. -/
theorem sLocalThetaSobolev_halfWeight_equiv :
    let ha : (0 : ℝ) < 1 / 2 := one_half_pos
    let hp : (0 : ℝ) < 1 / 2 + 0 := add_pos_of_pos_of_nonneg ha le_rfl
    ∃ T : SLocalThetaL2 F S ≃ₗᵢ[ℂ] Hₛ(ha, le_refl (0 : ℝ), le_refl (0 : ℝ), hp),
      ∀ u : SLocalThetaL2 F S,
        ((T u).val : Jₛ → ℂ) =ᵐ[μₛ] modulationWeight mₛ (1 / 2) (⇑u.val) := by sorry

end Fourier

end RiemannMasullo
