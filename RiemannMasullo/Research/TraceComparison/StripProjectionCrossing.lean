module
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec2

/-! # Orthogonal projections as a zero enters the strip

A surviving boundary moment separates the actual theta closure from every
narrower one on a single physical function. The square-root weight ratio
converges from below in the fixed boundary-width Hilbert space.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "K" => (ideleClassNorm F).ker
local notation "μ" => ideleClassTamagawaMeasure F
local notation "wμ(" α "," s "," dual ")" => intervalSobolevMeasure μ (logIdeleClassNorm F) (-α) α s dual
local notation "W(" α "," s ")" => CompactIntervalSobolev μ (logIdeleClassNorm F) (-α) α s
local notation "Θ(" a "," h "," hs ")" => globalThetaSobolev F a (neg_le_self h) hs

private theorem base_ac_weight (α s : ℝ) (b : Bool) : μ ≪ wμ(α,s,b) := by
  have hN : Continuous (fun g : C ↦ (((ideleClassNorm F g).val : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hm : Measurable (logIdeleClassNorm F) := Real.measurable_log.comp hN.measurable
  have hD : Measurable (fun g : C ↦ intervalSobolevDensity (-α) α s (logIdeleClassNorm F g)) := by
    unfold intervalSobolevDensity
    change Measurable (fun g ↦ max (Real.exp (2 * -α * logIdeleClassNorm F g))
      (Real.exp (2*α*logIdeleClassNorm F g)) * (1+(logIdeleClassNorm F g)^2)^(s/2))
    fun_prop (disch := exact hm)
  have hp (g : C) : 0 < intervalSobolevDensity (-α) α s (logIdeleClassNorm F g) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  cases b
  · exact withDensity_absolutelyContinuous' hD.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp g))
  · exact withDensity_absolutelyContinuous' hD.inv.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (hp g)))

private theorem sym_density {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2*α*|x|) * (1+x^2)^(s/2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem narrow_measure_le {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (s : ℝ) :
    wμ(α,s,false) ≤ wμ(β,s,false) := by
  apply withDensity_mono (.of_forall fun g ↦ ?_)
  apply ENNReal.ofReal_le_ofReal
  change intervalSobolevDensity (-α) α s _ ≤ intervalSobolevDensity (-β) β s _
  rw [sym_density hα,sym_density (hα.trans hαβ)]
  gcongr

private theorem strip_le_order (α s b : ℝ) (N : ℕ) : spectralStripMultiplicity α s b N ≤ N := by
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _

/-- Paper: Theorem 10.2.2.1, p. 446. A surviving edge jet gives a physical function killed by every narrower spectral
orthogonal projector, whose class in the edge-width space has nonzero projection. -/
theorem spectralProjection_crossing_witness (χ : PontryaginDual K → PontryaginDual C)
    (hχ : IsSpectralBasepointChoice χ) {a β s : ℝ} (hβ : 0 < β) (hs : 0 ≤ s)
    (i : SpectralStripJetIndex χ a β s) (hi : |i.val.2.1| = β) :
    ∃ y : W(β,s), spectralProjection (F := F) a hβ.le hs y ≠ 0 ∧
      ∀ α : ℝ, ∀ hα : 0 ≤ α, α < β → ∃ x : W(α,s),
        (x : C → ℂ) =ᵐ[μ] (y : C → ℂ) ∧ spectralProjection (F := F) a hα hs x = 0 := by
  classical
  obtain ⟨y,hy⟩ := spectralStripJet_singleInterpolant χ hχ hβ.le hs i
  have hyn : y ∉ Θ(a,hβ.le,hs) := by
    intro h
    have H := spectralStripJet_commonKernel_forward χ hβ.le hs y h i
    rw [hy,ite_eq_left rfl] at H
    exact one_ne_zero H
  refine ⟨y,fun h ↦ hyn ?_,fun α hα hlt ↦ ?_⟩
  · have H := (Θ(a,hβ.le,hs)).starProjection_add_starProjection_orthogonal y
    rw [show (Θ(a,hβ.le,hs)).orthogonal.starProjection y = 0 from h,add_zero] at H
    exact (Θ(a,hβ.le,hs)).starProjection_eq_self_iff.mp H
  · have hmem := (Lp.memLp y).mono_measure (narrow_measure_le (F := F) hα hlt.le s)
    let x : W(α,s) := hmem.toLp (y : C → ℂ)
    have hx : (x : C → ℂ) =ᵐ[μ] (y : C → ℂ) :=
      (base_ac_weight (F := F) α s false).ae_eq hmem.coeFn_toLp
    refine ⟨x,hx,Submodule.starProjection_orthogonal_apply_eq_zero ?_⟩
    apply (spectralStripJet_commonKernel χ hχ hα hs x).mpr
    intro j
    have hj := (j.mem_strip_order_pos hα).1
    let j' : SpectralStripJetIndex χ a β s := ⟨j.val,by
      rw [spectralStripMultiplicity_interior ⟨by linarith [hj.1], by linarith [hj.2]⟩]
      exact j.property.trans_le (strip_le_order _ _ _ _)⟩
    have hne : j' ≠ i := by
      intro h
      have he := congrArg (fun z : SpectralStripJetIndex χ a β s ↦ |z.val.2.1|) h
      have hh : |j.val.2.1| < β := (abs_le.mpr hj).trans_lt hlt
      exact hh.ne (he.trans hi)
    have hjα := (base_ac_weight (F := F) α s true).ae_eq (spectralStripJet_memLp χ hα hs j).coeFn_toLp
    have hjβ := (base_ac_weight (F := F) β s true).ae_eq (spectralStripJet_memLp χ hβ.le hs j').coeFn_toLp
    have hpair := integral_congr_ae (hx.mul (hjα.trans hjβ.symm))
    exact hpair.trans ((hy j').trans (ite_eq_right hne))

/-- Paper: Theorem 10.2.2.1, p. 446. A positive divisor at any off-center Hecke zero forces the zeroth-order crossing
in every Sobolev order greater than one. The same physical class works at all
narrower widths. -/
theorem spectralProjection_offCenterZero_witness (χ : PontryaginDual K → PontryaginDual C)
    (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual K) (a : ℝ) (z : ℂ)
    (ho : 0 < MeromorphicOn.divisor (continuedCompletedHeckeL (χ ω)) univ z)
    (hneq : z.re ≠ a) {s : ℝ} (hs : 1 < s) :
    let β := |z.re-a|
    ∃ y : W(β,s), spectralProjection (F := F) a (abs_nonneg _) (zero_le_one.trans hs.le) y ≠ 0 ∧
      ∀ α : ℝ, ∀ hα : 0 ≤ α, α < β → ∃ x : W(α,s),
        (x : C → ℂ) =ᵐ[μ] (y : C → ℂ) ∧ spectralProjection (F := F) a hα (zero_le_one.trans hs.le) x = 0 := by
  intro β
  let b := z.re-a
  have hβ : 0 < β := abs_pos.mpr (sub_ne_zero.mpr hneq)
  have hedge : b = -β ∨ b = β := by
    rcases le_total 0 b with h | h
    · exact Or.inr (abs_of_nonneg h).symm
    · exact Or.inl (by change b = -|b|; rw [abs_of_nonpos h,neg_neg])
  have hz : ((a+b : ℝ) : ℂ) + (z.im : ℂ)*Complex.I = z := by
    apply Complex.ext <;> simp [b]
  let i : SpectralStripJetIndex χ a β s := ⟨(ω,b,z.im,0),by
    change 0 < spectralStripMultiplicity β s b
      ((meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (((a+b : ℝ) : ℂ) + (z.im:ℂ)*Complex.I)).untop₀.toNat)
    rw [hz,spectralStripMultiplicity_boundary hβ.le hedge,lt_spectralBoundaryMultiplicity]
    rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn (mem_univ _)] at ho
    exact ⟨by omega, by exact_mod_cast (by linarith : (0:ℝ)<(s-1)/2)⟩⟩
  exact spectralProjection_crossing_witness χ hχ hβ (zero_le_one.trans hs.le) i rfl

/-- In the fixed width-β L² coordinate, the same physical vector at width α is
multiplied by the square-root density ratio exp((α−β)|r|). The squared L²
distance of this vector to its edge value tends to zero from below. -/
theorem width_frame_squared_error_tendsto {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (r : X → ℝ) (hr : Measurable r) (y : Lp ℂ 2 ν) (β : ℝ) :
    Tendsto (fun α : ℝ ↦ ∫ x, (Real.exp ((α-β)*|r x|)-1)^2 * ‖y x‖^2 ∂ν)
      (𝓝[≤] β) (𝓝 0) := by
  have hdom : Integrable (fun x ↦ ‖y x‖^2) ν := (Lp.memLp y).integrable_norm_pow two_ne_zero
  have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[≤] β)
    (F := fun α x ↦ (Real.exp ((α-β)*|r x|)-1)^2 * ‖y x‖^2) (f := fun _ ↦ (0 : ℝ))
    (fun x ↦ ‖y x‖^2) ?_ ?_ hdom ?_
  · simpa only [integral_zero] using h
  · exact .of_forall fun α ↦ by
      have hc : Measurable (fun x ↦ (Real.exp ((α-β)*|r x|)-1)^2) := by fun_prop
      exact hc.aestronglyMeasurable.mul hdom.aestronglyMeasurable
  · filter_upwards [show ∀ᶠ α in 𝓝[≤] β, α ≤ β from self_mem_nhdsWithin] with α hα
    exact .of_forall fun x ↦ by
      have hle : Real.exp ((α-β)*|r x|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hα) (abs_nonneg _))
      have hsq : (Real.exp ((α-β)*|r x|)-1)^2 ≤ 1 := by
        nlinarith [mul_nonneg (Real.exp_pos ((α-β)*|r x|)).le (sub_nonneg.mpr hle)]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) hsq
  · exact .of_forall fun x ↦ by
      have hc : Continuous (fun α : ℝ ↦ (Real.exp ((α-β)*|r x|)-1)^2 * ‖y x‖^2) := by fun_prop
      simpa using (hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := β) (s := Iic β)))

end RiemannMasullo.StripNuclearity
