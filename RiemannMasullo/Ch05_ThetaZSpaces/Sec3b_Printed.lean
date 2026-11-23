module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# §5.3.3–5.3.4: statements that are false as printed

The repaired statements are in `Sec3b.lean`. Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set Topology
open scoped ContDiff NNReal NumberField.AdeleRing SchwartzMap TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

/-- Paper: Example 5.3.3.1, p. 249. As printed: On every nonempty interval of exponents I,
the logarithmic profiles in the weighted space are precisely the smooth functions for which
the values of each twisted profile decay faster than every inverse power at both ends.
The repaired statement is `positiveRealExponentialDecay_log_equiv`. See ERRATA F52. -/
def Printed.positiveRealExponentialDecay_valueDecay : Prop :=
  ∀ (I : Set ℝ), OrdConnected I → I.Nonempty → ∀ (f : ℝ → ℂ),
    f ∈ logExponentialDecaySubmodule I ↔
      ContDiff ℝ (∞) f ∧ ∀ a ∈ I, ∀ k : ℝ, 0 < k →
        Tendsto (fun x : ℝ ↦ ‖x‖ ^ k * ‖logExponentialWeight a f x‖) (cocompact ℝ) (𝓝 0)

/-- The profile `exp(−x²) sin(exp(2x²))` has derivative `4x exp(x²)` wherever
`exp(2x²)` is a multiple of `2π`. -/
private theorem Printed.positiveRealExponentialDecay_valueDecay_hasDerivAt (x : ℝ) (n : ℕ)
    (hx : Real.exp (2 * x ^ 2) = n * (2 * Real.pi)) :
    HasDerivAt (fun x : ℝ ↦ Real.exp (-x ^ 2) * Real.sin (Real.exp (2 * x ^ 2)))
      (4 * x * Real.exp (x ^ 2)) x := by
  have ha : HasDerivAt (fun x : ℝ ↦ -x ^ 2) (-(2 * x)) x := by
    convert (hasDerivAt_pow 2 x).neg using 1
    simp
  have hb : HasDerivAt (fun x : ℝ ↦ 2 * x ^ 2) (2 * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul 2
  convert ha.exp.mul hb.exp.sin using 1
  have hsin : Real.sin (Real.exp (2 * x ^ 2)) = 0 := by
    rw [hx, show (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  have hcos : Real.cos (Real.exp (2 * x ^ 2)) = 1 := by
    rw [hx]
    exact Real.cos_nat_mul_two_pi n
  rw [hsin, hcos, show Real.exp (x ^ 2) = Real.exp (-x ^ 2) * Real.exp (2 * x ^ 2) by
    rw [← Real.exp_add]; ring_nf]
  ring

/-- For every bound there is a point beyond it where `exp(2x²)` is a multiple of `2π`. -/
private theorem Printed.positiveRealExponentialDecay_valueDecay_points (C : ℝ) :
    ∃ (x : ℝ) (n : ℕ), C < x ∧ 0 ≤ x ∧ Real.exp (2 * x ^ 2) = n * (2 * Real.pi) := by
  set D := max C 0
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (2 * D ^ 2))
  have hpi : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn
  have hN : Real.exp (2 * D ^ 2) < n * (2 * Real.pi) := by nlinarith
  have hNpos : (0 : ℝ) < n * (2 * Real.pi) := by positivity
  refine ⟨Real.sqrt (Real.log (n * (2 * Real.pi)) / 2), n, ?_, Real.sqrt_nonneg _, ?_⟩
  · have hlog : 2 * D ^ 2 < Real.log (n * (2 * Real.pi)) := by
      rw [Real.lt_log_iff_exp_lt hNpos]
      exact hN
    have hD : D < Real.sqrt (Real.log (n * (2 * Real.pi)) / 2) :=
      Real.lt_sqrt (le_max_right C 0) |>.mpr (by linarith)
    exact lt_of_le_of_lt (le_max_left C 0) hD
  · have hlog0 : 0 ≤ Real.log (n * (2 * Real.pi)) / 2 := by
      have : 0 < Real.log (n * (2 * Real.pi)) := by
        rw [Real.lt_log_iff_exp_lt hNpos, Real.exp_zero]
        nlinarith [Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 2 * D ^ 2 + 1 by positivity),
          Real.add_one_le_exp (2 * D ^ 2)]
      positivity
    rw [Real.sq_sqrt hlog0, show 2 * (Real.log (n * (2 * Real.pi)) / 2) =
      Real.log (n * (2 * Real.pi)) by ring, Real.exp_log hNpos]

/-- Paper: Example 5.3.3.1, p. 249. Take I = ℝ and
f(x) = exp(−x²) sin(exp(2x²)). The Gaussian bounds every twisted value, while at
x = √(log(2πn)/2) for positive integers n the derivative is 4x exp(x²). Even the
twist with exponent zero fails the Schwartz derivative bounds. -/
theorem Printed.positiveRealExponentialDecay_valueDecay_false :
    ¬ Printed.positiveRealExponentialDecay_valueDecay := by
  intro h
  let r : ℝ → ℝ := fun x ↦ Real.exp (-x ^ 2) * Real.sin (Real.exp (2 * x ^ 2))
  have hr : ContDiff ℝ (∞) r :=
    ((contDiff_id.pow 2).neg.exp).mul ((contDiff_const.mul (contDiff_id.pow 2)).exp.sin)
  have hf : ContDiff ℝ (∞) (fun x ↦ (r x : ℂ)) := Complex.ofRealCLM.contDiff.comp hr
  have hdecay : ∀ a ∈ ({0} : Set ℝ), ∀ k : ℝ, 0 < k →
      Tendsto (fun x : ℝ ↦ ‖x‖ ^ k * ‖logExponentialWeight a (fun x ↦ (r x : ℂ)) x‖)
        (cocompact ℝ) (𝓝 0) := by
    rintro a rfl k -
    rw [logExponentialWeight_zero]
    refine squeeze_zero (fun x ↦ by positivity) (fun x ↦ ?_)
      (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact one_pos k)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, neg_one_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_mul, Real.abs_exp]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have hmem := (h {0} ordConnected_singleton (singleton_nonempty 0) _).mpr ⟨hf, hdecay⟩
  obtain ⟨g, hg⟩ := (Submodule.mem_iInf _).mp hmem ⟨0, rfl⟩
  have hgf : (g : ℝ → ℂ) = fun x ↦ (r x : ℂ) := hg.trans (logExponentialWeight_zero _)
  obtain ⟨C, -, hC⟩ := g.decay 0 1
  obtain ⟨x, n, hxC, hx0, hx⟩ := Printed.positiveRealExponentialDecay_valueDecay_points C
  have hd := (Printed.positiveRealExponentialDecay_valueDecay_hasDerivAt x n hx).ofReal_comp
  have hb := hC x
  rw [pow_zero, one_mul, norm_iteratedFDeriv_one, ← norm_deriv_eq_norm_fderiv, hgf,
    hd.deriv, Complex.norm_real, Real.norm_eq_abs] at hb
  have h4 : x ≤ 4 * x * Real.exp (x ^ 2) := by
    nlinarith [Real.one_le_exp (sq_nonneg x)]
  rw [abs_of_nonneg (by positivity)] at hb
  linarith

local notation "complexDecay(" I ")" => ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) I
local notation "zeroExtension(" f ")" =>
  (fun x ↦ if hx : x ≠ 0 then f (Units.mk0 x hx) else (0 : ℂ))

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250. As printed: For every m ≥ 0 and a < 0,
the first holomorphic Wirtinger derivative is continuous from the complex multiplicative
space of weights (a, ∞) to the one of weights (a + m, ∞). This is the assertion for ∂z.
The repaired statement is `iteratedWirtinger_exponentialDecay`. See ERRATA F53. -/
def Printed.wirtinger_exponentialDecay : Prop :=
  ∀ (m : ℕ) (a : ℝ), a < 0 →
    ∃ D : complexDecay(Ioi a) →L[ℂ] complexDecay(Ioi (a + m)),
      ∀ f z, (D f).val z = wirtingerDeriv zeroExtension(f.val) z.val

/-- Every Schwartz–Bruhat function on the complex units is bounded. -/
private theorem Printed.wirtinger_exponentialDecay_bounded (f : ℂˣ → ℂ)
    (hf : f ∈ schwartzBruhatSubmodule ℂˣ) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f).mp hf
  refine ⟨(elementarySchwartzBound s.val (0, 0, 0, 0)).toReal, fun x ↦ ?_⟩
  rw [← hs, schwartzBruhatStageRealization_apply]
  split_ifs
  · change (‖s _‖₊ : ENNReal).toReal ≤ _
    apply ENNReal.toReal_mono (s.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun w ↦ (‖s w‖₊ : ENNReal)) _
  · rw [norm_zero]
    exact ENNReal.toReal_nonneg

/-- The Wirtinger derivative of `|z|² exp(−|z|²)` at a real point `t` is
`t (1 − t²) exp(−t²)`. -/
private theorem Printed.wirtinger_exponentialDecay_deriv (t : ℝ) :
    wirtingerDeriv (fun x : ℂ ↦ ((‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) : ℝ) : ℂ)) (t : ℂ) =
      ((t * ((1 - t ^ 2) * Real.exp (-t ^ 2)) : ℝ) : ℂ) := by
  have hφ : HasDerivAt (fun s : ℝ ↦ s * Real.exp (-s)) ((1 - ‖(t : ℂ)‖ ^ 2) *
      Real.exp (-‖(t : ℂ)‖ ^ 2)) (‖(t : ℂ)‖ ^ 2) :=
    ((hasDerivAt_id' _).mul ((hasDerivAt_id' _).neg.exp)).congr_deriv
      (by simp only [Pi.neg_apply]; ring)
  have hn := (hasStrictFDerivAt_norm_sq (t : ℂ)).hasFDerivAt
  have hc := Complex.ofRealCLM.hasFDerivAt.comp (t : ℂ) (hφ.comp_hasFDerivAt (t : ℂ) hn)
  have hfun : (fun x : ℂ ↦ ((‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ ((fun s : ℝ ↦ s * Real.exp (-s)) ∘ fun x : ℂ ↦ ‖x‖ ^ 2) := by
    funext x; simp
  rw [wirtingerDeriv, hfun, hc.fderiv]
  simp [Complex.inner]
  ring

/-- For every bound there is a small positive `t` with `t^(−1/2) (1 − t²) exp(−t²)`
above it. -/
private theorem Printed.wirtinger_exponentialDecay_point (C : ℝ) :
    ∃ t : ℝ, 0 < t ∧ C < (t ^ 2) ^ (-(3 / 4) : ℝ) * (t * ((1 - t ^ 2) * Real.exp (-t ^ 2))) := by
  set s := 2 * max C 1
  have hs : 2 ≤ s := by have := le_max_right C 1; linarith
  have hs0 : 0 < s := by linarith
  refine ⟨1 / s ^ 2, by positivity, ?_⟩
  have hpow : ((1 / s ^ 2) ^ 2) ^ (-(3 / 4) : ℝ) = s ^ 3 := by
    rw [show (1 / s ^ 2) ^ 2 = (s ^ 4)⁻¹ by ring, Real.inv_rpow (by positivity),
      Real.rpow_neg (by positivity), inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    norm_num
  rw [hpow]
  set t := 1 / s ^ 2 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 4 := by
    rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hexp : 3 / 4 ≤ Real.exp (-t ^ 2) := by
    nlinarith [Real.add_one_le_exp (-t ^ 2)]
  have h1 : 3 / 4 ≤ 1 - t ^ 2 := by nlinarith
  have h9 : 9 / 16 ≤ (1 - t ^ 2) * Real.exp (-t ^ 2) := by
    have := mul_le_mul h1 hexp (by norm_num) (by linarith)
    linarith
  have hst : s ^ 3 * t = s := by rw [ht]; field_simp
  rw [← mul_assoc, hst]
  nlinarith [le_max_left C 1]

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250. Take m = 0, a = −1/4 and a smooth
radial cutoff of |z|^(3/4), equal to |z|^(3/4) near zero and zero for |z| ≥ 2.
Each source twist has exponent 2b + 3/4 > 0 at zero. The first holomorphic derivative
has modulus (3/8)|z|^(−1/4) near zero, so the target twist with b = 0 is unbounded.

The Lean proof takes m = 0, a = −1 and `|z|² exp(−|z|²)`, the restriction of a Gaussian
multiplied by the modulation: its twists with exponents above −1 are twists of the Gaussian
with positive exponents. Its holomorphic derivative has modulus `|z| (1 − |z|²) exp(−|z|²)`,
so the target twist with exponent −3/4 is unbounded near zero. -/
theorem Printed.wirtinger_exponentialDecay_false :
    ¬ Printed.wirtinger_exponentialDecay := by
  intro h
  obtain ⟨D, hD⟩ := h 0 (-1) (by norm_num)
  obtain ⟨R, -, hR⟩ := complexSchwartz_restrict_positiveDecay
  let m := archimedeanUnitModulation ℂ 2
  let γ : 𝓢(ℂ, ℂ) := (SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM
  have hγ (z : ℂ) : γ z = ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
    simp [γ, SchwartzMap.postcompCLM_apply]
  let g := R γ
  have hm (z : ℂˣ) : ((m z).val : ℝ) = ‖(z : ℂ)‖ ^ 2 := archimedeanUnitModulation_apply ℂ 2 z
  let hfun : ℂˣ → ℂ := fun z ↦ (((m z).val : ℝ) : ℂ) * g.val z
  have hmem : hfun ∈ modulatedExponentialDecaySubmodule m (Ioi (-1)) := by
    rw [modulatedExponentialDecaySubmodule, Submodule.mem_iInf]
    rintro ⟨b, hb⟩
    have hb' : b + 1 ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi] at hb ⊢; linarith
    have key := modulationWeight_mem_schwartzBruhat m (Ioi 0) ⟨b + 1, hb'⟩ g
    show modulationWeight m b hfun ∈ schwartzBruhatSubmodule ℂˣ
    convert key using 1
    funext z
    have hpos : (0 : ℝ) < ((m z).val : ℝ) := by
      rw [hm]; exact pow_pos (norm_pos_iff.mpr z.ne_zero) 2
    show ((((m z).val : ℝ) ^ b : ℝ) : ℂ) * ((((m z).val : ℝ) : ℂ) * g.val z) =
      ((((m z).val : ℝ) ^ (b + 1) : ℝ) : ℂ) * g.val z
    rw [Real.rpow_add hpos, Real.rpow_one]
    push_cast
    ring
  let H : complexDecay(Ioi (-1)) := ⟨hfun, hmem⟩
  have hzero : zeroExtension(H.val) =
      fun x : ℂ ↦ ((‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) : ℝ) : ℂ) := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · simp only [ne_eq, hx, not_false_eq_true, ↓reduceDIte]
      change (((m (Units.mk0 x hx)).val : ℝ) : ℂ) * (R γ).val (Units.mk0 x hx) = _
      rw [hR, hm, Units.val_mk0, hγ]
      push_cast
      ring
  have hDmem := modulationWeight_mem_schwartzBruhat m (Ioi (-1 + ((0 : ℕ) : ℝ)))
    ⟨-(3 / 4), by norm_num⟩ (D H)
  obtain ⟨C, hC⟩ := Printed.wirtinger_exponentialDecay_bounded _ hDmem
  obtain ⟨t, ht, htC⟩ := Printed.wirtinger_exponentialDecay_point C
  set z : ℂˣ := Units.mk0 (t : ℂ) (Complex.ofReal_ne_zero.mpr ht.ne') with hz
  have hb : ‖((((m z).val : ℝ) ^ (-(3 / 4) : ℝ) : ℝ) : ℂ) * (D H).val z‖ ≤ C := hC z
  rw [hD, hzero, hz, Units.val_mk0, Printed.wirtinger_exponentialDecay_deriv, hm, Units.val_mk0,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs] at hb
  exact absurd (htC.trans_le (le_abs_self _)) (not_lt.mpr hb)

local notation "realDecay(" I ")" => ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) I

/-- Paper: Lemma 5.3.3.3(2), p. 252. As printed: For any numbers of real and complex
coordinates and any nonempty open interval I, the projective tensor product of the
one-coordinate weighted spaces embeds topologically in the product space of (5.3.3.6)
by multiplying the pure factors. The repaired statement is `archimedeanWeightedSchwartz_tensor`.
See ERRATA F54. -/
def Printed.archimedeanWeightedSchwartz_tensor : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (I : Set ℝ), IsOpen I → OrdConnected I → I.Nonempty →
    let R := realDecay(I)
    let C := complexDecay(I)
    let T := ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ R))
      (FiniteProjectiveTensor (fun _ : κ ↦ C))
    ∃ L : T →L[ℂ] ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I,
      IsEmbedding L ∧ ∀ (f : ι → R) (g : κ → C) (u : (ι → ℝˣ) × (κ → ℂˣ)),
        (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u =
          (∏ i, (f i).val (u.1 i)) * ∏ j, (g j).val (u.2 j)

private theorem archimedeanWeightedSchwartzSubmodule_anti
    {ι κ : Type*} [Fintype ι] [Fintype κ] {I J : Set ℝ}
    (h : insert 0 I ⊆ insert 0 J) :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) J ≤
      archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I := by
  intro f hf
  rw [archimedeanWeightedSchwartzSubmodule] at hf ⊢
  exact (Submodule.mem_iInf _).2 fun a ↦
    (Submodule.mem_iInf _).1 hf ⟨fun i ↦ ⟨(a.1 i).val, h (a.1 i).property⟩,
      fun j ↦ ⟨(a.2 j).val, h (a.2 j).property⟩⟩

private theorem isCompact_lcaDualAnnihilator_of_isOpen {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup (PontryaginDual G))
    (hH : IsOpen (H : Set (PontryaginDual G))) :
    IsCompact (lcaDualAnnihilator H : Set G) := by
  have hCompact := isCompact_lcaAnnihilator H hH
  convert (isClosedEmbedding_pontryaginDual_eval (G := G)).isCompact_preimage hCompact using 1
  ext x
  exact (mem_lcaDualAnnihilator_iff H x).trans
    (mem_lcaAnnihilator_iff H (pontryaginDual_eval x)).symm

private theorem compact_bruhat_kernel_aux {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (a : BruhatStructuralPair G) :
    IsCompact ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G) := by
  let k := OrderDual.ofDual a.val.2
  change IsCompact (k : Set G)
  rw [← lcaDualAnnihilator_annihilator k a.property.2.2.1.1]
  exact isCompact_lcaDualAnnihilator_of_isOpen _ a.property.2.2.1.2.1

private def slicePoint (t : ℝ) : (Unit → ℝˣ) × (Empty → ℂˣ) :=
  (fun _ ↦ Units.mk0 (Real.exp t) (Real.exp_pos t).ne', fun j ↦ Empty.elim j)

private def unitNormModulation : ((Unit → ℝˣ) × (Empty → ℂˣ)) →ₜ* ℝ≥0ˣ :=
  { toFun := fun y ↦ archimedeanUnitModulation ℝ 1 (y.1 ())
    map_one' := by simp
    map_mul' := by intro y z; simp [map_mul]
    continuous_toFun :=
      (continuous_archimedeanUnitModulation ℝ 1).comp
        ((continuous_apply ()).comp (continuous_fst :
          Continuous (Prod.fst : ((Unit → ℝˣ) × (Empty → ℂˣ)) → (Unit → ℝˣ)))) }

private def unitLogNorm : ((Unit → ℝˣ) × (Empty → ℂˣ)) →* Multiplicative ℝ :=
  { toFun := fun y ↦ Multiplicative.ofAdd (Real.log ‖(y.1 ()).val‖)
    map_one' := by simp
    map_mul' := by
      intro y z
      simp only [Prod.fst_mul, Pi.mul_apply, Units.val_mul, norm_mul]
      rw [Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero (y.1 ())))
        (norm_ne_zero_iff.mpr (Units.ne_zero (z.1 ())))]
      simp }

private theorem continuous_unitLogNorm : Continuous unitLogNorm := by
  show Continuous (fun y : (Unit → ℝˣ) × (Empty → ℂˣ) ↦
    Multiplicative.ofAdd (Real.log ‖(y.1 ()).val‖))
  have hg : Continuous (fun y : (Unit → ℝˣ) × (Empty → ℂˣ) ↦ ‖(y.1 ()).val‖) :=
    continuous_norm.comp (Units.continuous_val.comp
      ((continuous_apply ()).comp (continuous_fst :
        Continuous (Prod.fst : ((Unit → ℝˣ) × (Empty → ℂˣ)) → (Unit → ℝˣ)))))
  have hmem : ∀ y : (Unit → ℝˣ) × (Empty → ℂˣ), ‖(y.1 ()).val‖ ∈ ({0} : Set ℝ)ᶜ :=
    fun y ↦ norm_ne_zero_iff.mpr (Units.ne_zero (y.1 ()))
  have hlog : Continuous (fun y : (Unit → ℝˣ) × (Empty → ℂˣ) ↦ Real.log ‖(y.1 ()).val‖) := by
    simpa only [Function.comp_def] using Real.continuousOn_log.comp_continuous hg hmem
  exact continuous_ofAdd.comp hlog

private lemma unitLogNorm_slicePoint (t : ℝ) : (unitLogNorm (slicePoint t)).toAdd = t := by
  show Real.log ‖((slicePoint t).1 ()).val‖ = t
  rw [slicePoint, Units.val_mk0, Real.norm_of_nonneg (Real.exp_pos t).le, Real.log_exp]

private lemma norm_le_div_of_decay
    {f : ((Unit → ℝˣ) × (Empty → ℂˣ)) → ℂ} {C : ℝ}
    (hC : ∀ y, ‖f y‖ * ‖(unitLogNorm y).toAdd‖ ^ 1 ≤ C)
    (t : ℝ) (ht : t < 0) :
    ‖f (slicePoint t)‖ ≤ C / |t| := by
  have h := hC (slicePoint t)
  rw [unitLogNorm_slicePoint t, pow_one, Real.norm_eq_abs] at h
  exact (le_div_iff₀ (abs_pos.mpr ht.ne)).mpr h

private lemma tendsto_zero_of_nonneg_le_div {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ t, 0 ≤ f t)
    (hft : ∀ᶠ t in atBot, f t ≤ C / |t|) :
    Tendsto f atBot (𝓝 0) := by
  have hdiv : Tendsto (fun x : ℝ ↦ C / x) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := C)).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa [div_eq_mul_inv] using h
  exact squeeze_zero' (Eventually.of_forall hf) hft (hdiv.comp tendsto_abs_atBot_atTop)

private theorem schwartzBruhat_slice_exp_tendsto_zero
    (F : SchwartzBruhat ((Unit → ℝˣ) × (Empty → ℂˣ))) :
    Tendsto (fun t : ℝ ↦ F (slicePoint t)) atBot (𝓝 0) := by
  obtain ⟨a, e, s, hs⟩ :=
    (mem_schwartzBruhatSubmodule_iff (F : (Unit → ℝˣ) × (Empty → ℂˣ) → ℂ)).1 F.property
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hk : IsCompact ((OrderDual.ofDual a.val.2 : Subgroup ((Unit → ℝˣ) × (Empty → ℂˣ))) :
      Set ((Unit → ℝˣ) × (Empty → ℂˣ))) := compact_bruhat_kernel_aux a
  have hker : ∀ u ∈ OrderDual.ofDual a.val.2, unitLogNorm u = 1 := by
    intro u hu
    have hμ : unitNormModulation u = 1 :=
      (compactSubgroup_le_modulation_ker (m := unitNormModulation)
        (OrderDual.ofDual a.val.2) hk) hu
    have hnorm : ‖(u.1 ()).val‖ = 1 := by
      change archimedeanUnitModulation ℝ 1 (u.1 ()) = 1 at hμ
      have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hμ
      have h2 := archimedeanUnitModulation_apply ℝ 1 (u.1 ())
      rw [h2, pow_one] at h
      simpa using h
    show Multiplicative.ofAdd (Real.log ‖(u.1 ()).val‖) = 1
    rw [hnorm, Real.log_one]
    rfl
  obtain ⟨C, -, hC⟩ :=
    schwartzBruhatStage_exists_norm_decay a e s unitLogNorm continuous_unitLogNorm hker 1
  have hbound (t : ℝ) (ht : t < 0) : ‖F (slicePoint t)‖ ≤ C / |t| := by
    rw [congrFun hs.symm (slicePoint t)]
    exact norm_le_div_of_decay hC t ht
  refine tendsto_zero_of_nonneg_le_div (f := fun t : ℝ ↦ ‖F (slicePoint t)‖) (C := C)
    (fun t ↦ norm_nonneg _) ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
  exact hbound t ht

/-- Paper: Lemma 5.3.3.3(2), p. 252. Take one real factor, no complex factors, and
I = (0, ∞). The restriction of the Gaussian exp(−πx²) to ℝˣ meets every positive twist.
Its product with the empty tensor has logarithmic profile tending to one at −∞, contrary
to the unweighted Schwartz condition of (5.3.3.6). -/
theorem Printed.archimedeanWeightedSchwartz_tensor_false :
    ¬ Printed.archimedeanWeightedSchwartz_tensor := by
  intro h
  obtain ⟨R, -, hRval⟩ := realSchwartz_restrict_positiveDecay
  obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := ℝ) Real.pi Real.pi_pos
  let f : Unit → ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) (Ioi 0) :=
    fun _ ↦ R g
  let gC : Empty → ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) (Ioi 0) :=
    fun j ↦ Empty.elim j
  obtain ⟨L, -, hL⟩ := h Unit Empty (Ioi 0) isOpen_Ioi ordConnected_Ioi ⟨1, by norm_num⟩
  let H : (Unit → ℝˣ) × (Empty → ℂˣ) → ℂ := fun u ↦ g ((u.1 ()).val)
  let pure :
      ProjectiveTensor
        (FiniteProjectiveTensor fun _ : Unit ↦
          ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) (Ioi 0))
        (FiniteProjectiveTensor fun _ : Empty ↦
          ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) (Ioi 0)) :=
    (⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, gC j)
  have hval : (L pure).val = H := by
    funext u
    rw [hL f gC u]
    simp [f, gC, H, hRval g (u.1 ())]
  have hle : archimedeanWeightedSchwartzSubmodule (ι := Unit) (κ := Empty) (Ioi 0) ≤
      schwartzBruhatSubmodule ((Unit → ℝˣ) × (Empty → ℂˣ)) := by
    rw [← archimedeanWeightedSchwartzSubmodule_singleton_zero (ι := Unit) (κ := Empty)]
    exact archimedeanWeightedSchwartzSubmodule_anti (I := ({0} : Set ℝ)) (J := Ioi 0) (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl)
  have hmem : H ∈ schwartzBruhatSubmodule ((Unit → ℝˣ) × (Empty → ℂˣ)) := by
    have hLmem : (L pure).val ∈
        archimedeanWeightedSchwartzSubmodule (ι := Unit) (κ := Empty) (Ioi 0) :=
      (L pure).property
    rw [hval] at hLmem
    exact hle hLmem
  have hlim0 : Tendsto (fun t : ℝ ↦ H (slicePoint t)) atBot (𝓝 0) :=
    schwartzBruhat_slice_exp_tendsto_zero ⟨H, hmem⟩
  have hlim1 : Tendsto (fun t : ℝ ↦ H (slicePoint t)) atBot (𝓝 1) := by
    have hH : (fun t : ℝ ↦ H (slicePoint t)) =
        fun t : ℝ ↦ (Real.exp (-Real.pi * ‖Real.exp t‖ ^ 2) : ℂ) := by
      funext t
      simp [H, slicePoint, Units.val_mk0, hg]
    rw [hH]
    have hsq : Tendsto (fun t : ℝ ↦ ‖Real.exp t‖ ^ 2) atBot (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.norm.pow 2)
    have harg : Tendsto (fun t : ℝ ↦ -Real.pi * ‖Real.exp t‖ ^ 2) atBot (𝓝 0) := by
      have h := (tendsto_const_nhds (x := (-Real.pi : ℝ))).mul hsq
      simpa [neg_mul] using h
    have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-Real.pi * ‖Real.exp t‖ ^ 2))
        atBot (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp harg
      simpa [Function.comp_def] using this
    have h := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hexp
    simpa only [Function.comp_def, Complex.ofReal_one] using h
  have hone : (0 : ℂ) = 1 := tendsto_nhds_unique hlim0 hlim1
  norm_num at hone

/-- Paper: Proposition 5.3.3.4(1), p. 258. As printed: For every real Schwartz test and
sign parity, shifting the Mellin exponent by n and the sign parity by n modulo two keeps
the same meromorphic transform of that test. The repaired statement is
`realArchimedeanMellin_monomial`. See ERRATA F55. -/
def Printed.realArchimedeanMellin_monomial : Prop :=
  ∀ (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)),
    ∀ᶠ s : ℂ in codiscrete ℂ,
      realArchimedeanMellin f ε s = realArchimedeanMellin f (Fin.ofNat 2 (ε.val + n)) (s + n)

open MeasureTheory in
/-- Paper: Proposition 5.3.3.4(1), p. 258. Take n = 1, the trivial sign parity and
f(x) = exp(−πx²). At s = 1 the even Mellin integral is strictly positive. The shifted
odd profile vanishes identically. Both sides are analytic near s = 1. -/
theorem Printed.realArchimedeanMellin_monomial_false :
    ¬ Printed.realArchimedeanMellin_monomial := by
  intro h
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport (fun x ↦ (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : 𝓢(ℝ, ℂ) := hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf (x : ℝ) : f x = (b x : ℂ) := rfl
  have hev : ∀ᶠ s : ℂ in 𝓝[≠] 1, realArchimedeanMellin f 0 s =
      realArchimedeanMellin f (Fin.ofNat 2 ((0 : Fin 2).val + 1)) (s + ((1 : ℕ) : ℂ)) :=
    nhdsNE_le_codiscrete 1 (h 1 0 f)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  set σ : ℝ := 1 + ε / 2 with hσ_def
  have hσ1 : 1 < σ := by rw [hσ_def]; linarith
  have hmem : dist (σ : ℂ) 1 < ε := by
    rw [Complex.dist_eq, show (σ : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) by rw [hσ_def]; push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hne : (σ : ℂ) ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  have heq := hball hmem hne
  have hfin : Fin.ofNat 2 ((0 : Fin 2).val + 1) = 1 := rfl
  rw [hfin, Nat.cast_one] at heq
  -- the odd profile of the even bump vanishes
  have hR : realArchimedeanMellin f 1 ((σ : ℂ) + 1) = 0 := by
    rw [realArchimedeanMellin_eq_integral f 1 _ (by simp; linarith)]
    have hz : (fun t : ℝ ↦ f t + (-1 : ℂ) ^ (1 : Fin 2).val * f (-t)) = fun _ ↦ 0 := by
      funext t
      rw [hf, hf, b.neg]
      simp
    rw [hz]
    simp [mellin]
  -- the even profile has a positive Mellin integral at σ
  let r : ℝ → ℝ := fun t ↦ t ^ (σ - 1) * (2 * b t)
  have hrc : Continuous r :=
    (Real.continuous_rpow_const (by linarith)).mul (continuous_const.mul b.continuous)
  have hrs : HasCompactSupport r := (b.hasCompactSupport.mul_left).mul_left
  have hL : realArchimedeanMellin f 0 (σ : ℂ) = ((∫ t in Ioi (0 : ℝ), r t : ℝ) : ℂ) := by
    rw [realArchimedeanMellin_eq_integral f 0 _ (by simp; linarith), mellin,
      ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [hf, hf, b.neg]
    simp only [r, Fin.val_zero, pow_zero, one_mul, smul_eq_mul]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht)]
    push_cast
    ring
  have hpos : 0 < ∫ t in Ioi (0 : ℝ), r t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · refine lt_of_lt_of_le (by simp : (0 : ENNReal) < MeasureTheory.volume (Ioo (0 : ℝ) 1))
        (MeasureTheory.measure_mono fun t ht ↦ ⟨?_, ht.1⟩)
      have hb : 0 < b t := b.pos_of_mem_ball (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
        exact ht.2.trans one_lt_two)
      exact (mul_pos (Real.rpow_pos_of_pos ht.1 _) (mul_pos two_pos hb)).ne'
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (mul_nonneg zero_le_two (b.nonneg' t))
    · exact (hrc.integrable_of_hasCompactSupport hrs).integrableOn
  rw [hL, hR] at heq
  exact hpos.ne' (Complex.ofReal_eq_zero.mp heq)

section SAdele

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" A ")" => SchwartzBruhat (Multiplicative A)
local notation "RealPlaces(" F ")" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces(" F ")" => {w : InfinitePlace F // w.IsComplex}
local notation "RealModels(" F ")" => ((w : RealPlaces(F)) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels(" F ")" => ((w : ComplexPlaces(F)) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
local notation "ArchCoordinates(" F ")" => ((RealPlaces(F) → ℝ) × (ComplexPlaces(F) → ℂ))

open Classical in
/-- Paper: Definition 5.3.4.1, p. 259. As printed: For every number field and finite set
of places containing the archimedean places, the polar-free tensor factors give additive
S-adelic Schwartz–Bruhat functions. This is the inclusion in (5.3.4.1) on pure tensors, with
finite multiplicative factors extended by zero. The repaired declarations are `sAdelePolarFree`,
`sAdelePolarFree_eq_span_tmul` and `exists_finitePlaceSchwartz_zeroExtension_iff`.
See ERRATA F56. -/
def Printed.sAdelePolarFree_inclusion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F))
    (r : RealModels(F)) (c : ComplexModels(F))
    (f : archimedeanFlatSchwartz (ι := RealPlaces(F)) (κ := ComplexPlaces(F)))
    (g : ∀ v : S, SchwartzBruhat (v.val.adicCompletion F)ˣ),
    ∃ h : ℬ(SAdeleRing F S),
      ∀ (x : ArchCoordinates(F)) (y : (v : S) → v.val.adicCompletion F),
        let xArch : InfiniteAdeleRing F := fun w ↦
          if hw : w.IsReal then (r ⟨w, hw⟩).val.symm (x.1 ⟨w, hw⟩)
          else
            let w' : ComplexPlaces(F) := ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
            (c w').val.symm (x.2 w')
        h (Multiplicative.ofAdd (xArch, y)) = f.val x * ∏ v : S, zeroExtension(g v) (y v)

/-- Paper: Definition 5.3.4.1, p. 259. Take ℚ with its real and 3-adic places. Take a
nonzero smooth real bump supported in (1, 2) and the 3-adic multiplicative test
g(3ᵏu) = 3⁻ᵏ for k ≥ 0 and zero for k < 0, where u is an integer unit. Its shell sequence
is Schwartz. At any real point where the bump is nonzero, the finite slice of the prescribed
product vanishes at zero and is nonzero at every 3ᵏ for k ≥ 0, violating local constancy. -/
theorem Printed.sAdelePolarFree_inclusion_false :
    ¬ Printed.sAdelePolarFree_inclusion := by
  sorry

/-- Paper: Lemma 5.3.4.2(2), proof, p. 260. As printed: For every number field, finite set
of places containing the archimedean places and place in the set, restriction of S-idele
quotient quasi-characters onto the local quasi-character space is surjective. This is the
surjectivity assertion also made for the archimedean places in Proposition 5.3.4.5(2).
`sLocalArchimedeanPoleMultiplicity` uses the actual restrictions. See ERRATA F57. -/
def Printed.sLocalRestriction_surjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)),
    (∀ w : InfinitePlace F, Function.Surjective (sLocalInfiniteRestriction (S := S) w)) ∧
    ∀ v : S, Function.Surjective (sLocalFiniteRestriction v)

/-- A real place carries the sign quasi-character, which is `-1` at `-1`. -/
private theorem Printed.sLocalRestriction_surjective_sign {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ c : QuasiCharacter w.Completionˣ, c (-1) = -1 := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have he : Continuous (fun x : w.Completion ↦ e x) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  have hne (g : w.Completionˣ) : e (g : w.Completion) ≠ 0 := (map_ne_zero e).mpr g.ne_zero
  let φ : w.Completionˣ → ℂ := fun g ↦ ((e g / abs (e g) : ℝ) : ℂ)
  have hφ1 : φ 1 = 1 := by simp [φ]
  have hφm : ∀ a b, φ (a * b) = φ a * φ b := by
    intro a b
    simp only [φ, Units.val_mul, map_mul, abs_mul, mul_div_mul_comm, Complex.ofReal_mul]
  have hφc : Continuous φ := Complex.continuous_ofReal.comp ((he.comp Units.continuous_val).div
      (he.comp Units.continuous_val).abs fun g ↦ abs_ne_zero.mpr (hne g))
  refine ⟨⟨⟨⟨φ, hφ1⟩, hφm⟩, hφc⟩, ?_⟩
  change φ (-1) = -1
  simp [φ]

/-- Over `ℚ` with no finite places, the local unit `-1` at the real place is the diagonal
S-unit `-1`, so every S-local quasi-character restricts to `1` there. -/
private theorem Printed.sLocalRestriction_surjective_neg_one
    (c : QuasiCharacter (SIdeleQuotient ℚ ∅)) :
    sLocalInfiniteRestriction (default : InfinitePlace ℚ) c (-1) = 1 := by
  obtain ⟨g, hg, hgv⟩ : ∃ g : (SAdeleRing ℚ (∅ : Finset V(ℚ)))ˣ,
      sLocalInfiniteRestriction (default : InfinitePlace ℚ) c (-1) = c (QuotientGroup.mk g) ∧
      (g : SAdeleRing ℚ (∅ : Finset V(ℚ))) = -1 := by
    refine ⟨_, rfl, Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)⟩
    · rw [Subsingleton.elim v default]
      change ((@Pi.mulSingle (InfinitePlace ℚ) (fun v ↦ v.Completionˣ) _ (Classical.decEq _)
        default (-1) default : (default : InfinitePlace ℚ).Completionˣ) :
          (default : InfinitePlace ℚ).Completion) = _
      simp only [Pi.mulSingle_eq_same, Units.val_neg, Units.val_one]
      rfl
    · exact absurd v.2 (Finset.notMem_empty _)
  have hg1 : (QuotientGroup.mk g : SIdeleQuotient ℚ ∅) = 1 := by
    rw [sIdeleQuotient_mk_eq_one]
    refine ⟨-1, Units.ext ?_⟩
    rw [hgv]
    simp
  rw [hg, hg1, map_one]

/-- Paper: Lemma 5.3.4.2(2), proof, p. 260. For ℚ and the set consisting of the real place,
the local unit −1 maps to the identity of the S-idele quotient because it is the diagonal
S-unit −1. The local sign character takes value −1 there and so lies outside the image. -/
theorem Printed.sLocalRestriction_surjective_false :
    ¬ Printed.sLocalRestriction_surjective := by
  intro h
  have hw : (default : InfinitePlace ℚ).IsReal := by
    rw [Subsingleton.elim default Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  obtain ⟨σ, hσ⟩ := Printed.sLocalRestriction_surjective_sign _ hw
  obtain ⟨c, hc⟩ := (h ℚ ∅).1 default σ
  have h1 := DFunLike.congr_fun hc (-1)
  rw [hσ, Printed.sLocalRestriction_surjective_neg_one c] at h1
  norm_num at h1

local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "chart(" F ", " S ", " χ ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)

/-- Paper: Proposition 5.3.4.5(2), p. 264. On the reading that the listed poles occur
with their multiplicities, every point of (5.3.4.13) is a pole after applying all finite
principal values to any S-adelic test. This isolates occurrence from the multiplicity formula.
The repaired statements are `sLocalIdelicZFunction_principalValue_pole_bound` and
`exists_sLocalIdelicZFunction_principalValue_attaining_poles`. See ERRATA F58. -/
def Printed.sLocalIdelicZFunction_principalValue_has_poles : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F))
    (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ(F, S)) (s : ℂ),
    0 < sLocalArchimedeanPoleMultiplicity χ s →
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chart(F, S, χ) z)) s < 0

/-- At a real place the twisted trivial S-local character has Euler factor `Γℝ`. -/
private theorem Printed.sLocalPoles_trivial_real (F : Type) [Field F] [NumberField F]
    (S : Finset V(F)) (w : InfinitePlace F) (hw : w.IsReal) (z : ℂ) :
    infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chart(F, S, (1 : PontryaginDual Jₛ(F, S))) z)) =
      Complex.Gammaℝ z := by
  have hval (g : w.Completionˣ) :
      sLocalInfiniteRestriction w (chart(F, S, (1 : PontryaginDual Jₛ(F, S))) z) g =
      (((((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
        (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z :=
    sLocalInfiniteRestriction_normTwist w z g
  have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w
      (chart(F, S, (1 : PontryaginDual Jₛ(F, S))) z)
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) =
      (‖(x : ℝ)‖ : ℂ) ^ (z : ℂ) *
        (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ ((0 : Fin 2) : Fin 2).val := by
    intro x
    have hn : ‖((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (x : ℝ) :
        w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) (x : ℝ)
    rw [hval]
    simp [InfinitePlace.mult, hw, hn]
  have h := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w
    (chart(F, S, (1 : PontryaginDual Jₛ(F, S))) z))).unique
    (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (z, 0)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, h, Fin.val_zero,
    Nat.cast_zero, add_zero]

/-- Over `ℚ` with no finite places, the Euler factor of the twisted trivial character at the
real place has a pole at `0`. -/
private theorem Printed.sLocalPoles_rat_order_neg :
    meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor (default : InfinitePlace ℚ)
      (sLocalInfiniteRestriction default
        (chart(ℚ, (∅ : Finset V(ℚ)), (1 : PontryaginDual Jₛ(ℚ, ∅))) z))) 0 < 0 := by
  have hw : (default : InfinitePlace ℚ).IsReal := by
    rw [Subsingleton.elim default Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  have hfun : (fun z ↦ infiniteLocalEulerFactor (default : InfinitePlace ℚ)
      (sLocalInfiniteRestriction default
        (chart(ℚ, (∅ : Finset V(ℚ)), (1 : PontryaginDual Jₛ(ℚ, ∅))) z))) =
      fun z ↦ ((Complex.Gammaℝ z)⁻¹)⁻¹ :=
    funext fun z ↦ by rw [Printed.sLocalPoles_trivial_real ℚ ∅ default hw z, inv_inv]
  rw [hfun]
  set h : ℂ → ℂ := fun z ↦ (Complex.Gammaℝ z)⁻¹ with hh_def
  have hh : AnalyticAt ℂ h 0 := Complex.differentiable_Gammaℝ_inv.analyticAt 0
  have h0 : h 0 = 0 := by simp [hh_def, Complex.Gammaℝ]
  have hpos : ∀ x : ℝ, 0 < x → h x ≠ 0 := fun x hx ↦
    inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hx))
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), h z = 0 := by
    intro hev
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine hpos (ε / 2) (by linarith) (hball ?_)
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  rw [show meromorphicOrderAt (fun z ↦ (h z)⁻¹) 0 = -meromorphicOrderAt h 0 from
      meromorphicOrderAt_inv, hh.meromorphicOrderAt_eq]
  have h1 : analyticOrderAt h 0 ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    simp [hh, h0]
  have h2 : analyticOrderAt h 0 ≠ ⊤ := by rwa [Ne, analyticOrderAt_eq_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h2
  rw [← hn] at h1 ⊢
  have : (0 : ℕ) < n := Nat.pos_of_ne_zero (by exact_mod_cast h1)
  simp only [ENat.map_natCast]
  exact_mod_cast (by omega : -(n : ℤ) < 0)

/-- Over `ℚ` with no finite places, the trivial norm-twist line has a positive archimedean
pole multiplicity at `0`. -/
private theorem Printed.sLocalPoles_rat_multiplicity_pos :
    0 < sLocalArchimedeanPoleMultiplicity (F := ℚ) (S := ∅)
      (1 : PontryaginDual Jₛ(ℚ, ∅)) 0 :=
  (sLocalArchimedeanPoleMultiplicity_pos_iff _ _).mpr ⟨default, Printed.sLocalPoles_rat_order_neg⟩

/-- The S-local Z-function of the zero test vanishes. -/
private theorem Printed.sLocalIdelicZFunction_zero (F : Type) [Field F] [NumberField F]
    (S : Finset V(F)) : sLocalIdelicZFunction (0 : ℬ(SAdeleRing F S)) = 0 := by
  have hu := sLocalIdelicZetaIntegral_exists_continuation (F := F) (S := S) 0
  refine hu.unique ⟨sLocalIdelicZFunction_meromorphic 0, sLocalIdelicZFunction_eq_integral 0⟩
    ⟨fun χ ↦ ?_, fun c _ ↦ ?_⟩
  · exact (analyticOnNhd_const (v := (0 : ℂ))).meromorphicNFOn
  · simp [sLocalIdelicZetaIntegral]

/-- Paper: Proposition 5.3.4.5(2), p. 264. For ℚ with only the real place, take the
trivial character at s = 0 and a nonzero even, nonnegative smooth bump supported on
1 < |x| < 2. There are no finite principal values to apply. The Mellin transform is entire,
while the real Euler factor Γℝ(s) has a simple pole at zero. -/
theorem Printed.sLocalIdelicZFunction_principalValue_has_poles_false :
    ¬ Printed.sLocalIdelicZFunction_principalValue_has_poles := by
  intro h
  have h1 := h ℚ ∅ 0 1 0 Printed.sLocalPoles_rat_multiplicity_pos
  rw [map_zero, Printed.sLocalIdelicZFunction_zero] at h1
  simp only [Pi.zero_apply] at h1
  rw [show meromorphicOrderAt (fun _ : ℂ ↦ (0 : ℂ)) 0 = ⊤ from
    meromorphicOrderAt_eq_top_iff.mpr (Eventually.of_forall fun _ ↦ rfl)] at h1
  exact not_top_lt h1

/-- Paper: Proposition 5.3.4.5(2), p. 264. As printed: At each point in the union of pulled-back
archimedean pole sets, the sum of the signed orders of the local Euler factors is the value
of a natural-valued multiplicity function, as in (5.3.4.14). The sum is compared with the
multiplicity after coercing the latter to signed orders. The repaired statement is
`sLocalArchimedeanPoleMultiplicity_eq_sum`. See ERRATA F59. -/
def Printed.sLocalArchimedeanPoleMultiplicity_eq_sum : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V(F)) (χ : PontryaginDual Jₛ(F, S)),
    ∃ N : {s : ℂ // 0 < sLocalArchimedeanPoleMultiplicity χ s} → ℕ,
      ∀ s, (↑(N s : ℤ) : WithTop ℤ) = ∑ w : InfinitePlace F,
        meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
          (sLocalInfiniteRestriction w (chart(F, S, χ) z))) s.val

/-- Paper: Proposition 5.3.4.5(2), p. 264. Take ℚ with only the real place and the trivial
norm-twist line at s = 0. Its Euler factor Γℝ(s) has a simple pole, so the sole summand is
−1 in the divisor convention of (7.1.2.1). No natural multiplicity has this signed value. -/
theorem Printed.sLocalArchimedeanPoleMultiplicity_eq_sum_false :
    ¬ Printed.sLocalArchimedeanPoleMultiplicity_eq_sum := by
  intro h
  obtain ⟨N, hN⟩ := h ℚ ∅ 1
  have h1 := hN ⟨0, Printed.sLocalPoles_rat_multiplicity_pos⟩
  rw [Fintype.sum_unique] at h1
  have h2 := Printed.sLocalPoles_rat_order_neg
  rw [← h1] at h2
  exact absurd h2 (not_lt.mpr (by exact_mod_cast (N _).zero_le))

end SAdele

end RiemannMasullo
