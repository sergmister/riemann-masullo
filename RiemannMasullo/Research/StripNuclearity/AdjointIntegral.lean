module
public import RiemannMasullo.Research.StripNuclearity.Physical
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Convolution

/-!
# Weighted Hilbert adjoints of radial convolution

Compact test profiles are dense in the weighted space, and Fubini identifies
the adjoint there with the conjugate reflected kernel between reciprocal
Hilbert weights.
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory Set
open scoped Topology ComplexConjugate Convolution ContDiff

namespace RiemannMasullo.StripNuclearity

/-- Integrating a radial convolution against a compact profile transfers
the translate to the other factor with the opposite sign. -/
theorem compact_convolution_transpose (κ f g : ℝ → ℂ)
    (hκ : Continuous κ) (hk : HasCompactSupport κ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, g x * ∫ t : ℝ, κ t*f (x-t)) =
      ∫ y : ℝ, f y * ∫ t : ℝ, κ t * g (y+t) := by
  let Q (x t : ℝ) := g x*(κ t*f (x-t))
  let U (t y : ℝ) := f y*(κ t*g (y+t))
  have hQ : Integrable (uncurry Q) (volume.prod volume) := by
    have hc : Continuous (uncurry Q) := by dsimp [Q,uncurry]; fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (hgc.prod hk)
    rintro ⟨x,t⟩ h
    change g x * (κ t*f (x-t)) = 0
    by_cases hx : x ∈ tsupport g
    · have ht : t ∉ tsupport κ := fun ht ↦ h ⟨hx,ht⟩
      rw [image_eq_zero_of_notMem_tsupport ht,zero_mul,mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hU : Integrable (uncurry U) (volume.prod volume) := by
    have hc : Continuous (uncurry U) := by dsimp [U,uncurry]; fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (hk.prod hfc)
    rintro ⟨t,y⟩ h
    change f y * (κ t*g (y+t)) = 0
    by_cases ht : t ∈ tsupport κ
    · have hy : y ∉ tsupport f := fun hy ↦ h ⟨ht,hy⟩
      rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport ht,zero_mul,mul_zero]
  calc
    _ = ∫ x : ℝ, ∫ t : ℝ, Q x t := by simp only [Q, integral_const_mul]
    _ = ∫ t : ℝ, ∫ x : ℝ, Q x t := integral_integral_swap hQ
    _ = ∫ t : ℝ, ∫ y : ℝ, U t y := by
      refine integral_congr_ae (.of_forall fun t ↦ ?_)
      change (∫ x : ℝ, Q x t) = ∫ y : ℝ, U t y
      rw [← integral_add_right_eq_self (fun x : ℝ ↦ Q x t) t (μ := volume)]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      dsimp [Q,U]
      rw [add_sub_cancel_right]
      ring
    _ = ∫ y : ℝ, ∫ t : ℝ, U t y := integral_integral_swap hU
    _ = _ := by simp only [U,integral_const_mul]

/-- The numerator of the adjoint kernel uses the conjugate reflected convolution
kernel and the original Hilbert weight on the input. -/
theorem compact_weighted_convolution_transpose {w : ℝ → ℝ} (hw : Continuous w)
    (κ f u : ℝ → ℂ) (hκ : Continuous κ) (hk : HasCompactSupport κ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hu : Continuous u) (huc : HasCompactSupport u) :
    let L := ContinuousLinearMap.mul ℝ ℂ
    let gew := fun x : ℝ ↦ (w x : ℂ)*u x
    let kr := fun x : ℝ ↦ conj (κ (-x))
    (∫ x : ℝ, ((w x : ℂ)*conj (u x)) * ∫ t : ℝ, κ t*f (x-t)) =
      ∫ y : ℝ, f y * conj ((gew ⋆[L,volume] kr) y) := by
  intro L gew kr
  let g (x : ℝ) := (w x : ℂ)*conj (u x)
  have hgc : Continuous g := (Complex.continuous_ofReal.comp hw).mul (Complex.continuous_conj.comp hu)
  have hgs : HasCompactSupport g := by
    apply HasCompactSupport.intro huc
    intro x hx
    simp [g,image_eq_zero_of_notMem_tsupport hx]
  rw [compact_convolution_transpose κ f g hκ hk hf hfc hgc hgs]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change f y*(∫ t : ℝ, κ t*g (y+t)) = f y*conj ((gew ⋆[L,volume] kr) y)
  apply congrArg (f y * ·)
  change (∫ t : ℝ, κ t*g (y+t)) = conj (∫ x : ℝ, gew x*kr (y-x))
  rw [← integral_conj, ← integral_add_right_eq_self (fun x : ℝ ↦ conj (gew x*kr (y-x))) y
    (μ := volume)]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  dsimp [g,gew,kr]
  simp only [show t+y = y+t by ring, show -(y-(y+t)) = t by ring, map_mul,
    Complex.conj_ofReal, Complex.conj_conj]
  ring

private theorem weighted_inner {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 < w x)
    (u v : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (w x))) :
    inner ℂ u v = ∫ x : ℝ, ((w x : ℂ)*conj (u x))*v x := by
  rw [L2.inner_def, integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
    (.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [ENNReal.toReal_ofReal (hp x).le, RCLike.inner_apply, Complex.real_smul]
  ring

/-- On a compact continuous representative the Hilbert adjoint of ordinary
convolution is the reflected conjugated kernel acting between the Hilbert
weight and its reciprocal. -/
theorem weighted_convolution_adjoint_compact {w : ℝ → ℝ} (hw : Continuous w)
    (hp : ∀ x, 0 < w x) (κ : ℝ → ℂ) (hκ : Continuous κ) (hk : HasCompactSupport κ) :
    let ν := volume.withDensity fun x ↦ ENNReal.ofReal (w x)
    let E := Lp ℂ 2 ν
    let L := ContinuousLinearMap.mul ℝ ℂ
    ∀ (A : E →L[ℂ] E)
      (_ : ∀ f, ∀ᵐ x ∂volume, A f x = ∫ t : ℝ, κ t * f (x-t))
      (u : E) (g : ℝ → ℂ) (_ : Continuous g) (_ : HasCompactSupport g)
      (_ : (u : ℝ → ℂ) =ᵐ[volume] g),
      (A.adjoint u : ℝ → ℂ) =ᵐ[volume] fun x ↦ ((w x : ℂ)⁻¹) *
        ((fun y : ℝ ↦ (w y : ℂ)*g y) ⋆[L,volume] (fun t : ℝ ↦ conj (κ (-t)))) x := by
  intro ν E L A hA u g hgc hgs hu
  let : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hbase : volume ≪ ν := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  let G (x : ℝ) := (w x : ℂ)*g x
  let kr (x : ℝ) := conj (κ (-x))
  let V (x : ℝ) := ((w x : ℂ)⁻¹) * (G ⋆[L,volume] kr) x
  have hGc : Continuous G := (Complex.continuous_ofReal.comp hw).mul hgc
  have hGs : HasCompactSupport G := hgs.mul_left
  have hkc : Continuous kr := Complex.continuous_conj.comp (hκ.comp continuous_neg)
  have hks : HasCompactSupport kr := by
    have h : HasCompactSupport (fun x : ℝ ↦ κ (-x)) := hk.comp_homeomorph (Homeomorph.neg ℝ)
    exact h.comp_left (show conj (0 : ℂ) = 0 from map_zero _)
  have hVc : Continuous V := ((Complex.continuous_ofReal.comp hw).inv₀
    fun x ↦ Complex.ofReal_ne_zero.mpr (hp x).ne').mul
      (hks.continuous_convolution_right L hGc.locallyIntegrable hkc)
  have hVs : HasCompactSupport V := (hGs.convolution L hks).mul_left
  have hVlp : MemLp V 2 ν := hVc.memLp_of_hasCompactSupport hVs
  let v : E := hVlp.toLp V
  have hv : (v : ℝ → ℂ) =ᵐ[volume] V := hbase.ae_eq hVlp.coeFn_toLp
  have he : A.adjoint u = v := by
    apply ext_inner_right ℂ
    let S := {z : E | ∃ f : ℝ → ℂ, (z : ℝ → ℂ) =ᵐ[ν] f ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f}
    have hd : Dense S := Lp.dense_hasCompactSupport_contDiff (by norm_num)
    have hclosed : IsClosed {z : E | inner ℂ (A.adjoint u) z = inner ℂ v z} :=
      isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    refine fun z ↦ closure_minimal (s := S) ?_ hclosed (hd z)
    rintro f ⟨φ, hφ, hφs, hφd⟩
    have hφv := hbase.ae_eq hφ
    have hAf : (A f : ℝ → ℂ) =ᵐ[volume] fun x ↦ ∫ t : ℝ, κ t * φ (x-t) := by
      filter_upwards [hA f] with x hx
      refine hx.trans (integral_congr_ae ?_)
      exact ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae_eq_comp hφv).mono
        fun t ht ↦ congrArg (κ t * ·) ht
    change inner ℂ (A.adjoint u) f = inner ℂ v f
    rw [A.adjoint_inner_left,weighted_inner hw hp,weighted_inner hw hp]
    calc
      _ = ∫ x : ℝ, ((w x : ℂ)*conj (g x))*(∫ t : ℝ, κ t * φ (x-t)) := by
        apply integral_congr_ae
        filter_upwards [hu,hAf] with x hx hy
        rw [hx,hy]
      _ = ∫ y : ℝ, φ y * conj ((G ⋆[L,volume] kr) y) :=
        compact_weighted_convolution_transpose hw κ φ g hκ hk hφd.continuous hφs hgc hgs
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hv,hφv] with x h1 h2
        rw [h1,h2]
        dsimp only [V]
        rw [map_mul, map_inv₀, Complex.conj_ofReal]
        have hz : (w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hp x).ne'
        field_simp
  rwa [he]

end RiemannMasullo.StripNuclearity
