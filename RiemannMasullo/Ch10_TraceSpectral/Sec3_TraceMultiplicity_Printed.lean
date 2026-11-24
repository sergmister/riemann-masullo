module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3

import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # The line and strip trace formulas with the printed multiplicity -/

@[expose] public noncomputable section

open MeasureTheory NumberField Set

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "orderAt(" F ", " χ ", " z ")" =>
  meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mellinAt(" F ", " φ ", " χ ", " z ")" =>
  ∫ g, (φ : BruhatCompactSupport C𝔽(F)).val g * ideleClassNormTwist (F := F) χ z g
    ∂ideleClassTamagawaMeasure F

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.3)–(10.3.1.4), p. 448. As printed:
For every number field, basepoint choice, real a, degree s > 1 and test, the
line convolution has trace given by the sum over all Hecke zeros on the line,
counted with the minimum of their order and the printed floor. The trace-class
witness gives meaning to the trace on the left. See `spectralLineConvolution_trace`
and ERRATA F239. -/
def Printed.spectralLineConvolution_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a s : ℝ) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F)),
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let H := spectralSobolevQuotient F a hI hs₀
      let Z := {z : PontryaginDual C₁(F) × ℝ // 0 < orderAt(F, χ z.1, shift(a, z.2))}
      let term (z : Z) :=
        let n := (orderAt(F, χ z.val.1, shift(a, z.val.2))).untop₀.toNat
        let count := min n (Nat.floor ((s - 1) / 2 + 1))
        (count : ℂ) * mellinAt(F, φ, χ z.val.1, shift(0, z.val.2))
      ∃ T : nuclearEndomorphisms H,
        T.val = spectralConvolution (F := F) a hI hs₀ φ ∧ HasSum term (hilbertTrace T)

/-- Haar invariance and Fubini: the pairing of a convolution of two continuous compactly
supported kernels with a continuous multiplicative function is the product of the pairings. -/
private theorem spectralLineConvolution_trace_false_pairing {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] {f g D : G → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (hD : Continuous D)
    (hmul : ∀ x y, D (x * y) = D x * D y) :
    (∫ x, lcaConvolution μ f g x * D x ∂μ) = (∫ x, f x * D x ∂μ) * ∫ x, g x * D x ∂μ := by
  let S := (fun p : G × G ↦ p.1 * p.2) '' (tsupport f ×ˢ tsupport g)
  have hS : IsCompact S := (hfc.prod hgc).image (by fun_prop)
  have hs {t x : G} (h : f t * g (t⁻¹ * x) ≠ 0) : t ∈ tsupport f ∧ x ∈ S :=
    ⟨subset_tsupport _ (left_ne_zero_of_mul h), ⟨(t, t⁻¹ * x),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), subset_tsupport _ (right_ne_zero_of_mul h)⟩,
      mul_inv_cancel_left _ _⟩⟩
  let Q (x t : G) := f t * g (t⁻¹ * x) * D x
  have hQc : Continuous (Function.uncurry Q) :=
    ((hf.comp continuous_snd).mul (hg.comp (continuous_snd.inv.mul continuous_fst))).mul
      (hD.comp continuous_fst)
  have hQk : HasCompactSupport (Function.uncurry Q) := by
    apply HasCompactSupport.of_support_subset_isCompact (hS.prod hfc)
    intro p hp
    have h : f p.2 * g (p.2⁻¹ * p.1) ≠ 0 := left_ne_zero_of_mul hp
    exact ⟨(hs h).2, (hs h).1⟩
  calc
    _ = ∫ x, ∫ t, Q x t ∂μ ∂μ := by simp only [Q, integral_mul_const, lcaConvolution]
    _ = ∫ t, ∫ x, Q x t ∂μ ∂μ := integral_integral_swap (hQc.integrable_of_hasCompactSupport hQk)
    _ = ∫ t, (f t * D t) * (∫ y, g y * D y ∂μ) ∂μ := by
      congr with t
      rw [← integral_mul_left_eq_self (fun x ↦ Q x t) t, ← integral_const_mul]
      congr with y
      simp only [Q, inv_mul_cancel_left, hmul]
      ring
    _ = _ := integral_mul_const _ _

/-- A kernel and a multiplier that both turn inversion into conjugation pair to a real number,
since Haar measure on a commutative group is inversion invariant. -/
private theorem spectralLineConvolution_trace_false_real {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] {f D : G → ℂ}
    (hf : ∀ x, f x⁻¹ = starRingEnd ℂ (f x)) (hD : ∀ x, D x⁻¹ = starRingEnd ℂ (D x)) :
    (∫ x, f x * D x ∂μ).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← integral_conj, ← integral_inv_eq_self (fun x ↦ f x * D x) μ]
  exact integral_congr_ae (.of_forall fun x ↦ by simp only [hf, hD, map_mul])

/-- The convolution square of a test function is a test function. -/
private theorem spectralLineConvolution_trace_false_square {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] (φ : BruhatCompactSupport G) :
    ∃ θ : BruhatCompactSupport G, θ.val = lcaConvolution μ φ.val φ.val := by
  let : PolynormableSpace ℂ ℂ := (norm_withSeminorms ℂ ℂ).toPolynormableSpace
  obtain ⟨θ, hθ, -⟩ := bruhatRegularizedAction_convolution μ (1 : G →* (ℂ →L[ℂ] ℂ))
    (show Continuous (fun p : G × ℂ ↦ p.2) from continuous_snd) φ φ
  exact ⟨θ, hθ⟩

/-- For a unitary character and a real ordinate there is a test whose Fourier–Mellin samples
at all unitary twists are nonnegative reals, with a positive sample at the given twist. It is
the convolution square of the conjugate twist times an even bump in the log norm. -/
private theorem spectralLineConvolution_trace_false_test (F : Type) [Field F] [NumberField F]
    (η : PontryaginDual C𝔽(F)) (t₀ : ℝ) :
    ∃ θ : BruhatCompactSupport C𝔽(F),
      (∀ (ψ : PontryaginDual C𝔽(F)) (t : ℝ),
        (mellinAt(F, θ, ψ, shift(0, t))).im = 0 ∧ 0 ≤ (mellinAt(F, θ, ψ, shift(0, t))).re) ∧
      0 < (mellinAt(F, θ, η, shift(0, t₀))).re := by
  let μ := ideleClassTamagawaMeasure F
  let u (x : C𝔽(F)) : ℝ := Real.log ((ideleClassNorm F x).val : ℝ)
  let B : ContDiffBump (0 : ℝ) := default
  let g (y : ℝ) : ℂ := Complex.exp ((y : ℂ) * (-(t₀ : ℂ) * Complex.I)) * (B y : ℂ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)).mul
      (Complex.ofRealCLM.contDiff.comp B.contDiff)
  have hgc : HasCompactSupport g :=
    (B.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) η⁻¹ g hg hgc
  obtain ⟨θ, hθ⟩ := spectralLineConvolution_trace_false_square μ φ
  have hφc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hN (x : C𝔽(F)) : 0 < ((ideleClassNorm F x).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hu (x : C𝔽(F)) : u x⁻¹ = -u x := by
    simp only [u, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  have hginv (y : ℝ) : g (-y) = starRingEnd ℂ (g y) := by
    simp only [g, B.neg, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I,
      map_neg, Complex.ofReal_neg]
    ring_nf
  have hφinv (x : C𝔽(F)) : φ.val x⁻¹ = starRingEnd ℂ (φ.val x) := by
    rw [hφ, hφ, map_mul, ← hginv, ← Circle.coe_inv_eq_conj, ← map_inv]
    exact congrArg _ (congrArg g (hu x))
  let D (ψ : PontryaginDual C𝔽(F)) (t : ℝ) (x : C𝔽(F)) : ℂ :=
    ideleClassNormTwist (F := F) ψ (shift(0, t)) x
  have hDexp (ψ : PontryaginDual C𝔽(F)) (t : ℝ) (x : C𝔽(F)) :
      D ψ t x = (ψ x : ℂ) * Complex.exp ((u x : ℂ) * ((t : ℂ) * Complex.I)) := by
    change (ψ x : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ (shift(0, t)) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hN x).ne'),
      ← Complex.ofReal_log (hN x).le, Complex.ofReal_zero, zero_add]
  have hDnorm (ψ : PontryaginDual C𝔽(F)) (t : ℝ) (x : C𝔽(F)) : ‖D ψ t x‖ = 1 := by
    rw [hDexp, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp]
    simp
  have hDc (ψ : PontryaginDual C𝔽(F)) (t : ℝ) : Continuous (D ψ t) :=
    (ideleClassNormTwist (F := F) ψ (shift(0, t))).continuous
  have hDmul (ψ : PontryaginDual C𝔽(F)) (t : ℝ) (x y : C𝔽(F)) :
      D ψ t (x * y) = D ψ t x * D ψ t y := map_mul _ x y
  have hDinv (ψ : PontryaginDual C𝔽(F)) (t : ℝ) (x : C𝔽(F)) :
      D ψ t x⁻¹ = starRingEnd ℂ (D ψ t x) := by
    have h1 : D ψ t x * D ψ t x⁻¹ = 1 := by
      rw [← hDmul, mul_inv_cancel]
      exact map_one _
    rw [← Complex.inv_eq_conj (hDnorm ψ t x)]
    exact eq_inv_of_mul_eq_one_right h1
  have key (ψ : PontryaginDual C𝔽(F)) (t : ℝ) : mellinAt(F, θ, ψ, shift(0, t)) =
      (∫ x, φ.val x * D ψ t x ∂μ) * ∫ x, φ.val x * D ψ t x ∂μ := by
    rw [hθ]
    exact spectralLineConvolution_trace_false_pairing μ hφc hφc φ.property.2 φ.property.2
      (hDc ψ t) (hDmul ψ t)
  have him (ψ : PontryaginDual C𝔽(F)) (t : ℝ) : (∫ x, φ.val x * D ψ t x ∂μ).im = 0 :=
    spectralLineConvolution_trace_false_real μ hφinv (hDinv ψ t)
  refine ⟨θ, fun ψ t ↦ ?_, ?_⟩
  · rw [key, Complex.mul_im, Complex.mul_re, him]
    constructor
    · ring
    · nlinarith [mul_self_nonneg (∫ x, φ.val x * D ψ t x ∂μ).re]
  · have hval (x : C𝔽(F)) : φ.val x * D η t₀ x = ((B (u x) : ℝ) : ℂ) := by
      rw [hφ, hDexp]
      change ((η x)⁻¹ : Circle) *
          (Complex.exp ((u x : ℂ) * (-(t₀ : ℂ) * Complex.I)) * (B (u x) : ℂ)) *
        ((η x : ℂ) * Complex.exp ((u x : ℂ) * ((t₀ : ℂ) * Complex.I))) = _
      have h1 : (((η x)⁻¹ : Circle) : ℂ) * (η x : ℂ) = 1 := by
        rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
      have h2 : Complex.exp ((u x : ℂ) * (-(t₀ : ℂ) * Complex.I)) *
          Complex.exp ((u x : ℂ) * ((t₀ : ℂ) * Complex.I)) = 1 := by
        rw [← Complex.exp_add, show (u x : ℂ) * (-(t₀ : ℂ) * Complex.I) +
          (u x : ℂ) * ((t₀ : ℂ) * Complex.I) = 0 by ring, Complex.exp_zero]
      linear_combination (B (u x) : ℂ) * Complex.exp ((u x : ℂ) * (-(t₀ : ℂ) * Complex.I)) *
        Complex.exp ((u x : ℂ) * ((t₀ : ℂ) * Complex.I)) * h1 + (B (u x) : ℂ) * h2
    have hint : (∫ x, φ.val x * D η t₀ x ∂μ) = ((∫ x, B (u x) ∂μ : ℝ) : ℂ) :=
      (integral_congr_ae (.of_forall hval)).trans integral_ofReal
    have hucont : Continuous u :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp
        (isProperMap_ideleClassNorm F).continuous)).log fun x ↦ (hN x).ne'
    have hBc : HasCompactSupport (fun x : C𝔽(F) ↦ B (u x)) := by
      have h := (φ.property.2.mul_right (f' := D η t₀)).comp_left (g := Complex.re) Complex.zero_re
      have he : (Complex.re ∘ (φ.val * D η t₀)) = fun x : C𝔽(F) ↦ B (u x) := by
        funext x
        change (φ.val x * D η t₀ x).re = _
        rw [hval, Complex.ofReal_re]
      rwa [he] at h
    have hpos : 0 < ∫ x, B (u x) ∂μ := by
      apply Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 1)
        (B.continuous.comp hucont) hBc (fun x ↦ B.nonneg)
      have h1 : u 1 = 0 := by simp [u]
      change B (u 1) ≠ 0
      rw [h1]
      exact (B.pos_of_mem_ball (Metric.mem_ball_self B.rOut_pos)).ne'
    rw [key, hint, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos hpos hpos

/-- Some completed Hecke L-function has a zero of order at least two on some vertical line,
for some basepoint choice. `Ch10_TraceSpectral/Sec2_Printed.lean` proves this privately for
the trivial character of the splitting field of X³ − 2, as
`spectralLineJet_memLp_false_multipleZero`, and its public `Printed.spectralLineJet_memLp_false`
gives the present form through `spectralLineJet_memLp`. Neither is available here, since
a file of printed claims has no importers. -/
private theorem spectralLineConvolution_trace_false_multipleZero :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F)
      (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)) (_ : IsSpectralBasepointChoice (F := F) χ)
      (a : ℝ) (ω : PontryaginDual C₁(F)) (t : ℝ),
      2 ≤ (orderAt(F, χ ω, shift(a, t))).untop₀.toNat := by sorry

/-- A zero of order at least two on the line refutes the printed floor multiplicity at
Sobolev degree three. The trace of any nuclear convolution is the sum with the strict cutoff,
so the printed sum would exceed it by the samples at the multiple zeros. For the test of
`spectralLineConvolution_trace_false_test` these are nonnegative with one positive. -/
private theorem spectralLineConvolution_trace_false_of_multipleZero (F : Type) [Field F]
    [NumberField F] (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F))
    (hχ : IsSpectralBasepointChoice (F := F) χ) (a : ℝ) (ω₀ : PontryaginDual C₁(F)) (t₀ : ℝ)
    (h2 : 2 ≤ (orderAt(F, χ ω₀, shift(a, t₀))).untop₀.toNat) :
    ¬ Printed.spectralLineConvolution_trace := by
  intro hall
  obtain ⟨θ, hnn, hpos⟩ := spectralLineConvolution_trace_false_test F (χ ω₀) t₀
  have hs : (1 : ℝ) < 3 := by norm_num
  obtain ⟨T, hT, hp⟩ := hall F χ hχ a 3 hs θ
  have hc := (spectralLineConvolution_trace (F := F) a χ hχ hs θ T hT).2
  let Z := {z : PontryaginDual C₁(F) × ℝ // 0 < orderAt(F, χ z.1, shift(a, z.2))}
  let n (z : Z) : ℕ := (orderAt(F, χ z.val.1, shift(a, z.val.2))).untop₀.toNat
  let J (z : Z) : ℂ := mellinAt(F, θ, χ z.val.1, shift(0, z.val.2))
  let f (z : Z) : ℝ := (((min (n z) 2 : ℕ) : ℝ) - ((min (n z) 1 : ℕ) : ℝ)) * (J z).re
  have hfl : Nat.floor (((3 : ℝ) - 1) / 2 + 1) = 2 := by
    rw [show ((3 : ℝ) - 1) / 2 + 1 = ((2 : ℕ) : ℝ) by norm_num, Nat.floor_natCast]
  have hcl : Nat.ceil (((3 : ℝ) - 1) / 2) = 1 := by
    rw [show ((3 : ℝ) - 1) / 2 = ((1 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
  have hp' : HasSum (fun z : Z ↦ ((min (n z) (Nat.floor (((3 : ℝ) - 1) / 2 + 1)) : ℕ) : ℂ) * J z)
      (hilbertTrace T) := hp
  have hc' : HasSum (fun z : Z ↦ ((min (n z) (Nat.ceil (((3 : ℝ) - 1) / 2)) : ℕ) : ℂ) * J z)
      (hilbertTrace T) :=
    hc.congr_fun fun z ↦ congrArg (((min (n z) (Nat.ceil (((3 : ℝ) - 1) / 2)) : ℕ) : ℂ) * ·)
      (spectralConvolution_mellin_integrable (F := F) θ (χ z.val.1) (shift(0, z.val.2))).2.symm
  have hJ (z : Z) : J z = ((J z).re : ℂ) := Complex.ext rfl (hnn (χ z.val.1) z.val.2).1
  have hdiff : HasSum (fun z : Z ↦ ((f z : ℝ) : ℂ)) 0 := by
    have h := hp'.sub hc'
    rw [sub_self, hfl, hcl] at h
    refine h.congr_fun fun z ↦ ?_
    conv_rhs => rw [hJ z]
    simp only [f]
    rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_natCast]
    ring
  have hf0 (z : Z) : 0 ≤ f z :=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast min_le_min_left (n z) one_le_two))
      (hnn (χ z.val.1) z.val.2).2
  have hzero := (hasSum_zero_iff_of_nonneg hf0).mp (Complex.hasSum_ofReal.mp hdiff)
  have key : ∀ o : WithTop ℤ, 0 < o.untop₀.toNat → 0 < o := by
    intro o h
    cases o with
    | top => simp at h
    | coe m =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < m)
  let z₀ : Z := ⟨(ω₀, t₀), key (orderAt(F, χ ω₀, shift(a, t₀))) (by omega)⟩
  have hz₀ : f z₀ = (J z₀).re := by
    have hn : 2 ≤ n z₀ := h2
    simp only [f, min_eq_right hn, min_eq_right (one_le_two.trans hn)]
    norm_num
  have h0 : f z₀ = 0 := congrFun hzero z₀
  rw [hz₀] at h0
  exact hpos.ne' h0

/-- Paper: Theorem 10.3.1.1(2), p. 448. Let F be the splitting field of X³−2
and K = ℚ(ζ₃). The two nontrivial characters of Gal(F/K) have the same Hecke
L-function by conjugation. Take a common critical-strip zero β+iγ. It has
order at least two for the trivial character of F. Set a = β and s = 3 and
choose the trivial representative on the norm-one trivial type. Use the radial
autocorrelation of b(x) = exp(−iγx) η(x), where η is a nonzero nonnegative smooth
bump in (1, 2). Divide by the norm-one volume to give multiplier B = |b̂|² on that
type and zero elsewhere. To bound the actual trace, take the standard adelic Gaussian
with finite integer indicators and apply (1−D)(1−cD), where D dilates the argument
by an idele of norm c > 1. This kills its value at zero and its additive integral.
Its Mellin factor Λ_F(z)(1−c^(−z))(1−c^(1−z))
forces dual support in the trivial-type zero set on the line. Nonzero eigenvalues
have generalized eigenspaces supported where B takes that eigenvalue. Only the
constant jet at each point has finite dual norm at s = 3. The printed sum
counts at least one extra positive term B(γ). -/
theorem Printed.spectralLineConvolution_trace_false :
    ¬ Printed.spectralLineConvolution_trace := by
  obtain ⟨F, _, _, χ, hχ, a, ω₀, t₀, h2⟩ := spectralLineConvolution_trace_false_multipleZero
  exact spectralLineConvolution_trace_false_of_multipleZero F χ hχ a ω₀ t₀ h2

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.3)–(10.3.2.4), p. 454. As printed:
For every number field, basepoint choice, closed symmetric strip, degree s > 1 and
test, the strip convolution has trace given by the sum over all strip zeros with
full order inside and the printed floor truncation at either edge. The trace-class
witness gives meaning to the trace on the left. See `spectralStripConvolution_trace`
and ERRATA F240. -/
def Printed.spectralStripConvolution_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F)),
      let hI := (neg_nonpos.mpr hα).trans hα
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let H := spectralSobolevQuotient F a hI hs₀
      let Z := {z : PontryaginDual C₁(F) × ℝ × ℝ //
        z.2.1 ∈ Icc (-α) α ∧ 0 < orderAt(F, χ z.1, shift(a + z.2.1, z.2.2))}
      let term (z : Z) :=
        let b := z.val.2.1
        let t := z.val.2.2
        let n := (orderAt(F, χ z.val.1, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min n (Nat.floor ((s - 1) / 2 + 1)) else n
        (count : ℂ) * mellinAt(F, φ, χ z.val.1, shift(b, t))
      ∃ T : nuclearEndomorphisms H,
        T.val = spectralConvolution (F := F) a hI hs₀ φ ∧ HasSum term (hilbertTrace T)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Use the splitting field of X³−2 and the
multiple trivial-type zero β+iγ from the line case. Choose the trivial representative,
s = 3, α = 1 and a = β−1. With x the log norm, take the radial test
V⁻¹ exp(−iγx) v(x), where V is the norm-one volume and v is a nonzero nonnegative
smooth bump supported in (1, 2). Its multiplier reaches its unique maximum modulus R
at the upper-edge zero. Applying the printed formula to the convolution powers gives
normalized traces tending to 2. For a peripheral generalized eigenvector of the
transpose, factoring out exp((1+iγ)x) gives the positive-shift averaging equation
with density v(y) exp(y)/R. The equation and dual norm give growth at most polynomial,
and the Fourier transform of the averaging density has modulus one only at zero.
Only constants then meet the dual norm at s = 3. Thus the peripheral algebraic
multiplicity is at most one, contradicting the printed limit of 2. -/
theorem Printed.spectralStripConvolution_trace_false :
    ¬ Printed.spectralStripConvolution_trace := by
  classical
  intro hall
  apply Printed.spectralLineConvolution_trace_false
  intro F _ _ χ hχ a s hs φ
  let L := {z : PontryaginDual C₁(F) × ℝ // 0 < orderAt(F, χ z.1, shift(a, z.2))}
  let term (z : L) := ((min (orderAt(F, χ z.val.1, shift(a, z.val.2))).untop₀.toNat
    (Nat.floor ((s - 1) / 2 + 1)) : ℕ) : ℂ) * mellinAt(F, φ, χ z.val.1, shift(0, z.val.2))
  let P (l : ℝ) (hl : l ≤ 0) : Prop :=
    ∃ T : nuclearEndomorphisms (spectralSobolevQuotient F a hl (zero_lt_one.trans hs).le),
      T.val = spectralConvolution (F := F) a hl (zero_lt_one.trans hs).le φ ∧
      HasSum term (hilbertTrace T)
  have transport (l : ℝ) (hl : l ≤ 0) (he : l = 0) (hp : P l hl) : P 0 le_rfl := by
    subst l
    exact hp
  apply transport _ ((neg_nonpos.mpr (le_refl (0 : ℝ))).trans le_rfl) neg_zero
  let Z := {z : PontryaginDual C₁(F) × ℝ × ℝ //
    z.2.1 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < orderAt(F, χ z.1, shift(a + z.2.1, z.2.2))}
  have hoff (z : Z) : z.val.2.1 = 0 := by simpa using z.property.1
  let e : L ≃ Z :=
    { toFun := fun z ↦ ⟨(z.val.1, 0, z.val.2), by simp, by simpa only [add_zero] using z.property⟩
      invFun := fun z ↦ ⟨(z.val.1, z.val.2.2), by simpa only [hoff z, add_zero] using z.property.2⟩
      left_inv := fun z ↦ Subtype.ext rfl
      right_inv := fun z ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hoff z).symm rfl)) }
  obtain ⟨T, hT, hsum⟩ := hall F χ hχ a 0 s le_rfl hs φ
  refine ⟨T, hT, ?_⟩
  let u (z : Z) :=
    let b := z.val.2.1
    let t := z.val.2.2
    let n := (orderAt(F, χ z.val.1, shift(a + b, t))).untop₀.toNat
    ((if b = -0 ∨ b = 0 then min n (Nat.floor ((s - 1) / 2 + 1)) else n : ℕ) : ℂ) *
      mellinAt(F, φ, χ z.val.1, shift(b, t))
  have hu : HasSum u (hilbertTrace T) := hsum
  have heq (z : L) : u (e z) = term z := by simp only [u, e, Equiv.coe_fn_mk, add_zero, or_true, ite_true, term]
  exact (e.hasSum_iff.mpr hu).congr_fun (fun z ↦ (heq z).symm)

end RiemannMasullo
