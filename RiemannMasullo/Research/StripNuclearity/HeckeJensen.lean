module

public import RiemannMasullo.AppB_AnalyticNT.Sec1
public import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.Research.StripNuclearity.HeckePairedDivisor
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! # Uniform Jensen bounds for finite Hecke L-functions

The finite Euler products give a field-dependent upper and lower bound on
`Re s ≥ 2`. On the opposite edge the needed estimate is a bound for the
actual finite L-function on `Re s = −3/2`.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain Metric NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

private theorem eulerFactor_bounds (χ : U) (v : HeightOneSpectrum (𝓞 F))
    (s : ℂ) (hs : 2 ≤ s.re) :
    let u := 2 * (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ))
    Real.exp (-u) ≤ ‖finiteHeckeEulerFactor χ v s‖ ∧
      ‖finiteHeckeEulerFactor χ v s‖ ≤ Real.exp u := by
  classical
  let q : ℝ := v.asIdeal.absNorm
  let a := q ^ (-(2 : ℝ))
  have hq : 2 ≤ q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.two_le_absNorm_nnreal v
  have hq₁ : 1 ≤ q := by linarith
  have hq₀ : 0 < q := by linarith
  have ha : 0 ≤ a := Real.rpow_nonneg hq₀.le _
  have hhalf : a ≤ 1 / 2 := calc
    a ≤ q ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hq₁ (by norm_num)
    _ = 1 / q := by rw [Real.rpow_neg hq₀.le, Real.rpow_one, one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by norm_num) hq
  have hexp : 1 + 2 * a ≤ Real.exp (2 * a) := by linarith [Real.add_one_le_exp (2 * a)]
  change Real.exp (-(2 * a)) ≤ _ ∧ _ ≤ Real.exp (2 * a)
  rw [finiteHeckeEulerFactor]
  split_ifs
  · let z := (ideleClassNormTwist χ 0).localValue v * (q : ℂ) ^ (-s)
    have hz : ‖z‖ ≤ a := by
      rw [show ‖z‖ = q ^ (-s.re) by
        simp [z, norm_ideleClassNormTwist_zero_localValue,
          Complex.norm_cpow_eq_rpow_re_of_pos hq₀]]
      exact Real.rpow_le_rpow_of_exponent_le hq₁ (neg_le_neg hs)
    have hd : 1 - a ≤ ‖1 - z‖ := by
      have h := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at h
      linarith
    have hp : 0 < ‖1 - z‖ := by linarith
    change Real.exp (-(2*a)) ≤ ‖(1 - z)⁻¹‖ ∧ ‖(1-z)⁻¹‖ ≤ _
    simp only [norm_inv, Real.exp_neg]
    constructor
    · apply (inv_le_inv₀ (Real.exp_pos _) hp).2
      have hu := norm_sub_le (1 : ℂ) z
      rw [norm_one] at hu
      linarith
    · apply le_trans _ hexp
      rw [inv_le_iff_one_le_mul₀ hp]
      nlinarith [mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ 1 + 2*a),
        mul_nonneg ha (by linarith : 0 ≤ 1 - 2*a)]
  · simp only [norm_one]
    constructor
    · exact Real.exp_le_one_iff.mpr (by linarith)
    · exact Real.one_le_exp_iff.mpr (by linarith)

/-- Paper: Lemma 3.2.1.1, p. 123. On `Re s ≥ 2`, both the finite Euler product
and its reciprocal have a common bound depending only on the number field. -/
theorem exists_uniform_finiteHeckeL_right_bounds (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (s : halfPlane),
      2 ≤ (s : ℂ).re → C⁻¹ ≤ ‖finiteHeckeL χ s‖ ∧ ‖finiteHeckeL χ s‖ ≤ C := by
  classical
  let u (v : HeightOneSpectrum (𝓞 F)) := 2 * (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ))
  have hu : Summable u := ((summable_absNorm_rpow F (by norm_num : (1 : ℝ) < 2)).comp_injective
    (fun v w (h : (v : HeightOneSpectrum (𝓞 F)).asIdeal = w.asIdeal) ↦
      HeightOneSpectrum.ext h)).mul_left 2
  have hpos (v) : 0 ≤ u v := by dsimp [u]; positivity
  refine ⟨Real.exp (∑' v, u v), Real.one_le_exp_iff.mpr (tsum_nonneg hpos), fun χ s hs ↦ ?_⟩
  have hl := (finiteHeckeL_hasProd χ s).norm
  have hS (S : Finset (HeightOneSpectrum (𝓞 F))) := hu.sum_le_tsum S (fun v _ ↦ hpos v)
  constructor
  · apply ge_of_tendsto hl
    apply Eventually.of_forall
    intro S
    rw [← Real.exp_neg, norm_prod]
    calc
      Real.exp (-(∑' v, u v)) ≤ Real.exp (-(∑ v ∈ S, u v)) :=
        Real.exp_le_exp.mpr (neg_le_neg (hS S))
      _ = ∏ v ∈ S, Real.exp (-u v) := by rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le)
        (fun v _ ↦ (eulerFactor_bounds χ v s hs).1)
  · apply le_of_tendsto hl
    apply Eventually.of_forall
    intro S
    rw [norm_prod]
    calc
      _ ≤ ∏ v ∈ S, Real.exp (u v) := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun v _ ↦ (eulerFactor_bounds χ v s hs).2)
      _ = Real.exp (∑ v ∈ S, u v) := (Real.exp_sum S u).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hS S)


local notation "stripFilter" =>
  comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-(3/2 : ℝ)) (11/2))

/-- A boundary polynomial estimate extends across the Jensen strip without
using the (possibly character-dependent) constants in a polynomial growth
estimate at infinity. Division by `(z+3)^d` makes the boundary bound constant. -/
private theorem polynomial_bound_on_jensen_strip (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (M : ℝ) (hg : f =O[stripFilter] fun z : ℂ ↦ |z.im| ^ M)
    (d : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ z : ℂ, z.re = -(3/2 : ℝ) ∨ z.re = 11/2 →
      ‖f z‖ ≤ A * (1 + |z.im|) ^ d)
    (z : ℂ) (hz₀ : -(3/2 : ℝ) ≤ z.re) (hz₁ : z.re ≤ 11/2) :
    ‖f z‖ ≤ A * (2 * ‖z + 3‖) ^ d := by
  let Q (w : ℂ) := f w / (w + 3) ^ d
  have hbase (w : ℂ) (hw : -(3/2 : ℝ) ≤ w.re) : 1 ≤ ‖w + 3‖ := by
    have h := Complex.re_le_norm (w + 3)
    norm_num at h
    linarith
  have hQ (w : ℂ) : ‖Q w‖ = ‖f w‖ / ‖w + 3‖ ^ d := by simp [Q, norm_pow]
  have hD : DiffContOnCl ℂ Q (Complex.re ⁻¹' Ioo (-(3/2 : ℝ)) (11/2)) := by
    apply DifferentiableOn.diffContOnCl
    have hincl : closure (Complex.re ⁻¹' Ioo (-(3/2 : ℝ)) (11/2)) ⊆
        Complex.re ⁻¹' Icc (-(3/2 : ℝ)) (11/2) :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
    intro w hw
    apply (hf w).differentiableWithinAt.div
      (by fun_prop : DifferentiableAt ℂ (fun x : ℂ ↦ (x + 3) ^ d) w).differentiableWithinAt
    exact pow_ne_zero _ (norm_ne_zero_iff.mp (zero_lt_one.trans_le (hbase _ (hincl hw).1)).ne')
  have hO : Q =O[stripFilter] f := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    apply eventually_inf_principal.mpr
    exact Eventually.of_forall fun w hw ↦ by
      rw [hQ, one_mul]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ (hbase w hw.1.le))
  have hc : 0 < Real.pi / 14 := by positivity
  have ht : Tendsto (fun w : ℂ ↦ |w.im|) stripFilter atTop := tendsto_inf_left tendsto_comap
  have hdouble : (fun t : ℝ ↦ Real.exp ((Real.pi / 14) * t)) =O[atTop]
      fun t : ℝ ↦ Real.exp (1 * Real.exp ((Real.pi / 14) * t)) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ ?_)
    simp only [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    linarith [Real.add_one_le_exp ((Real.pi / 14) * t)]
  have hBE (w : ℂ) (hw : w.re = -(3/2 : ℝ) ∨ w.re = 11/2) : ‖Q w‖ ≤ A * 2 ^ d := by
    have hw' : -(3/2 : ℝ) ≤ w.re := by rcases hw with h | h <;> linarith
    have hn := hbase w hw'
    have him : |w.im| ≤ ‖w + 3‖ := by simpa using Complex.abs_im_le_norm (w + 3)
    rw [hQ, div_le_iff₀ (pow_pos (zero_lt_one.trans_le hn) d)]
    calc
      ‖f w‖ ≤ A * (1 + |w.im|) ^ d := hb _ hw
      _ ≤ A * (2 * ‖w + 3‖) ^ d := by
        gcongr
        linarith
      _ = _ := by rw [mul_pow, mul_assoc]
  have hq := PhragmenLindelof.vertical_strip (f := Q) hD
    ⟨Real.pi / 14, by ring_nf; linarith [Real.pi_pos], 1, hO.trans (hg.trans
      (((isLittleO_rpow_exp_pos_mul_atTop M hc).isBigO.trans hdouble).comp_tendsto ht))⟩
    (fun w hw ↦ hBE w (Or.inl hw)) (fun w hw ↦ hBE w (Or.inr hw)) hz₀ hz₁
  rw [hQ, div_le_iff₀ (pow_pos (zero_lt_one.trans_le (hbase z hz₀)) d)] at hq
  simpa only [mul_pow, mul_assoc] using hq


private theorem jensen_window {Λ L : ℂ → ℂ} (hΛ : MeromorphicOn Λ univ)
    (hD : Differentiable ℂ L) (ho : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    {M : ℝ} (hpoly : L =O[stripFilter] fun z : ℂ ↦ |z.im| ^ M)
    {C : ℝ} (hC : 1 ≤ C) (hr : ∀ z : ℂ, 2 ≤ z.re → C⁻¹ ≤ ‖L z‖ ∧ ‖L z‖ ≤ C)
    (d : ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hleft : ∀ z : ℂ, z.re = -(3/2 : ℝ) → ‖L z‖ ≤ A * (1 + |z.im|) ^ d)
    (T : ℝ) (S : Finset ℂ) (hS : ∀ z ∈ S, 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im - T| ≤ 1) :
    ∑ z ∈ S, (MeromorphicOn.divisor Λ univ z : ℝ) ≤
      Real.log (C ^ 2 * A * (18 + 2 * |T|) ^ d) / Real.log (7 / 6) := by
  let c : ℂ := ⟨2, T⟩
  have hc₀ : 0 < C := zero_lt_one.trans_le hC
  have hAc : 0 ≤ C * A := mul_nonneg hc₀.le (zero_le_one.trans hA)
  have hbound (z : ℂ) (hz : z.re = -(3/2 : ℝ) ∨ z.re = 11/2) :
      ‖L z‖ ≤ C * A * (1 + |z.im|) ^ d := by
    have hp : 1 ≤ (1 + |z.im|) ^ d := one_le_pow₀ (by linarith [abs_nonneg z.im])
    rcases hz with hz | hz
    · apply (hleft z hz).trans
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (zero_le_one.trans hA) hC)
        (zero_le_one.trans hp)
    · exact (hr z (by linarith)).2.trans
        ((le_mul_of_one_le_right hc₀.le hA).trans (le_mul_of_one_le_right hAc hp))
  have hglobal := polynomial_bound_on_jensen_strip L hD M hpoly d hAc hbound
  have hcenter : C⁻¹ ≤ ‖L c‖ := (hr c (by rfl)).1
  have hcp : 0 < ‖L c‖ := (inv_pos.mpr hc₀).trans_le hcenter
  have hratio (z : ℂ) (hz : z ∈ closedBall c (7/2)) :
      ‖L z / L c‖ ≤ C ^ 2 * A * (18 + 2 * |T|) ^ d := by
    have hzc : ‖z - c‖ ≤ 7/2 := by simpa [dist_eq_norm] using hz
    have hRe := (Complex.abs_re_le_norm (z-c)).trans hzc
    have hline : |z.re - 2| ≤ 7/2 := hRe
    obtain ⟨h₀, h₁⟩ := abs_le.mp hline
    have hnorm : ‖z + 3‖ ≤ 9 + |T| := calc
      ‖z + 3‖ = ‖(z - c) + (c + 3)‖ := by congr 1; abel
      _ ≤ ‖z - c‖ + ‖c + 3‖ := norm_add_le _ _
      _ ≤ 9 + |T| := by
        have he := Complex.norm_le_abs_re_add_abs_im (c + 3)
        norm_num [c] at he
        linarith
    have hn := hglobal z (by linarith) (by linarith)
    have hpow : (2 * ‖z + 3‖) ^ d ≤ (18 + 2 * |T|) ^ d := by gcongr; linarith
    have hi : ‖L c‖⁻¹ ≤ C := by simpa using (inv_le_inv₀ hcp (inv_pos.mpr hc₀)).2 hcenter
    rw [norm_div, div_eq_mul_inv]
    calc
      ‖L z‖ * ‖L c‖⁻¹ ≤ (C * A * (18 + 2 * |T|) ^ d) * C :=
        mul_le_mul (hn.trans (mul_le_mul_of_nonneg_left hpow hAc)) hi (inv_nonneg.mpr hcp.le) (by positivity)
      _ = _ := by ring
  have hsubset (z : ℂ) (hz : z ∈ S) : z ∈ closedBall c 3 := by
    obtain ⟨hz₀, hz₁, ht⟩ := hS z hz
    have he := Complex.norm_le_abs_re_add_abs_im (z - c)
    rw [mem_closedBall, dist_eq_norm]
    change ‖z - c‖ ≤ |z.re - 2| + |z.im - T| at he
    rw [abs_of_nonpos (by linarith : z.re - 2 ≤ 0)] at he
    linarith
  have h := sum_divisor_le_log_of_disk_bound hΛ ho
    (by norm_num : 0 < (3 : ℝ)) (by norm_num : (3 : ℝ) < 7/2)
    (fun z _ ↦ hD.analyticAt z) (norm_pos_iff.mp hcp) hratio S hsubset
  convert h using 2
  norm_num


private def finitePart (χ : U) (z : ℂ) : ℂ :=
  continuedCompletedHeckeL χ z * (heckeGammaFactor χ z)⁻¹

private theorem finitePart_data (χ : U)
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Differentiable ℂ (finitePart χ) ∧
    (∀ z : halfPlane, finitePart χ z = finiteHeckeL χ z) ∧
    (∀ z, meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt (finitePart χ) z) ∧
    ∃ M : ℝ, 0 < M ∧ finitePart χ =O[stripFilter] fun z : ℂ ↦ |z.im| ^ M := by
  let Λ := continuedCompletedHeckeL χ

  obtain ⟨hΛ, hv⟩ := continuedCompletedHeckeL_spec χ
  have hDΛ : Differentiable ℂ Λ := completedHeckeL_continuation_entire χ Λ hΛ hv hχ
  have hD : Differentiable ℂ (finitePart χ) := hDΛ.mul (differentiable_inv_heckeGammaFactor χ)
  have hseries (z : halfPlane) : finitePart χ z = finiteHeckeL χ z := by
    have hn := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans z.property)
    change continuedCompletedHeckeL χ z * _ = _
    rw [hv z, completedHeckeL, finiteHeckeL]
    rw [mul_comm (heckeGammaFactor χ z), mul_assoc, mul_inv_cancel₀ hn, mul_one]
  have ho (z : ℂ) : meromorphicOrderAt Λ z ≤ meromorphicOrderAt (finitePart χ) z := by
    change meromorphicOrderAt Λ z ≤ meromorphicOrderAt (Λ * (fun w ↦ (heckeGammaFactor χ w)⁻¹)) z
    rw [meromorphicOrderAt_mul (hΛ (mem_univ _)).meromorphicAt
      ((differentiable_inv_heckeGammaFactor χ).analyticAt z).meromorphicAt]
    exact le_add_of_nonneg_right ((differentiable_inv_heckeGammaFactor χ).analyticAt z).meromorphicOrderAt_nonneg

  obtain ⟨M, hM, hpoly⟩ := finiteHeckeL_continuation_isBigO_rpow χ (finitePart χ)
    (fun _ _ ↦ (hD.analyticAt _).meromorphicNFAt) hseries (-(3/2)) (11/2) (by norm_num)
  exact ⟨hD, hseries, ho, M, hM, hpoly.mono
    (inf_le_inf_left _ (principal_mono.mpr (preimage_mono Ioo_subset_Icc_self)))⟩

private theorem finitePart_right (χ : U) (hseries : ∀ z : halfPlane, finitePart χ z = finiteHeckeL χ z)
    {C : ℝ} (h : ∀ s : halfPlane, 2 ≤ (s : ℂ).re → C⁻¹ ≤ ‖finiteHeckeL χ s‖ ∧ ‖finiteHeckeL χ s‖ ≤ C)
    (z : ℂ) (hz : 2 ≤ z.re) : C⁻¹ ≤ ‖finitePart χ z‖ ∧ ‖finitePart χ z‖ ≤ C := by
  have hz' : 1 < z.re := one_lt_two.trans_le hz
  rw [hseries ⟨z, hz'⟩]
  exact h ⟨z, hz'⟩ hz

/-- For nontrivial norm-one characters, a polynomial bound for the finite
L-function on the single line `Re s = −3/2` gives a logarithmic zero count
in every unit-height window of the critical strip. The constant `C` is uniform
in the character, the height, and the input boundary estimate. The sum counts
the multiplicities of the actual completed Hecke divisor. -/
theorem exists_uniform_heckeZeroWindow_of_left_bound (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      ∀ (d : ℕ) (A : ℝ), 1 ≤ A →
      (∀ z : ℂ, z.re = -(3/2 : ℝ) →
        ‖continuedCompletedHeckeL χ z / heckeGammaFactor χ z‖ ≤ A * (1 + |z.im|) ^ d) →
      ∀ (T : ℝ) (S : Finset ℂ), (∀ z ∈ S, 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im - T| ≤ 1) →
        ∑ z ∈ S, (MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z : ℝ) ≤
          Real.log (C ^ 2 * A * (18 + 2 * |T|) ^ d) / Real.log (7 / 6) := by
  obtain ⟨C, hC, hEuler⟩ := exists_uniform_finiteHeckeL_right_bounds F
  refine ⟨C, hC, fun χ hχ d A hA hleft T S hS ↦ ?_⟩

  obtain ⟨hD, hv, ho, M, _, hp⟩ := finitePart_data χ hχ
  exact jensen_window (continuedCompletedHeckeL_spec χ).1.meromorphicOn hD ho hp hC
    (finitePart_right χ hv (hEuler χ)) d A hA (by simpa [finitePart, div_eq_mul_inv] using hleft)
    T S hS


/-- The same zero window estimate follows from the boundary magnitude of the
product of the two dual finite L-functions. This choice cancels the constant
in the functional equation, and includes the zeros of either factor with their orders. -/
theorem exists_uniform_heckeZeroWindow_of_paired_left_bound (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      ∀ (d : ℕ) (A : ℝ), 1 ≤ A →
      (∀ z : ℂ, z.re = -(3/2 : ℝ) →
        ‖(continuedCompletedHeckeL χ z / heckeGammaFactor χ z) *
          (continuedCompletedHeckeL χ⁻¹ z / heckeGammaFactor χ⁻¹ z)‖ ≤ A * (1 + |z.im|) ^ d) →
      ∀ (T : ℝ) (S : Finset ℂ), (∀ z ∈ S, 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im - T| ≤ 1) →
        ∑ z ∈ S, (MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z : ℝ) ≤
          Real.log (C ^ 2 * A * (18 + 2 * |T|) ^ d) / Real.log (7 / 6) := by
  obtain ⟨C, hC, hEuler⟩ := exists_uniform_finiteHeckeL_right_bounds F
  refine ⟨C ^ 2, one_le_pow₀ hC, fun χ hχ d A hA hb T S hS ↦ ?_⟩
  have hdual : χ⁻¹.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := by
    intro he
    apply hχ
    apply MonoidHom.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change (χ x.val)⁻¹ = 1 at hx
    change χ x.val = 1
    exact inv_eq_one.mp hx
  obtain ⟨hD, hv, ho, M, hM, hg⟩ := finitePart_data χ hχ
  obtain ⟨hD', hv', _, N, hN, hg'⟩ := finitePart_data χ⁻¹ hdual
  let P := finitePart χ * finitePart χ⁻¹
  have horder (z : ℂ) : meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt P z := by
    rw [show meromorphicOrderAt P z = _ from meromorphicOrderAt_mul
      (hD.analyticAt z).meromorphicAt (hD'.analyticAt z).meromorphicAt]
    exact (ho z).trans (le_add_of_nonneg_right (hD'.analyticAt z).meromorphicOrderAt_nonneg)
  have hp : P =O[stripFilter] fun z : ℂ ↦ |z.im| ^ (M + N) := by
    apply (hg.mul hg').congr' (Eventually.of_forall fun _ ↦ rfl)
    exact Eventually.of_forall fun z ↦ (Real.rpow_add_of_nonneg (abs_nonneg z.im) hM.le hN.le).symm
  have hr (z : ℂ) (hz : 2 ≤ z.re) : (C ^ 2)⁻¹ ≤ ‖P z‖ ∧ ‖P z‖ ≤ C ^ 2 := by
    obtain ⟨hx, hy⟩ := finitePart_right χ hv (hEuler χ) z hz
    obtain ⟨hx', hy'⟩ := finitePart_right χ⁻¹ hv' (hEuler χ⁻¹) z hz
    rw [show ‖P z‖ = _ from norm_mul (finitePart χ z) (finitePart χ⁻¹ z), sq, mul_inv]
    exact ⟨mul_le_mul hx hx' (inv_nonneg.mpr (zero_le_one.trans hC)) (norm_nonneg _),
      mul_le_mul hy hy' (norm_nonneg _) (zero_le_one.trans hC)⟩
  exact jensen_window (continuedCompletedHeckeL_spec χ).1.meromorphicOn (hD.mul hD') horder hp
    (one_le_pow₀ hC) hr d A hA (by simpa [P, finitePart, div_eq_mul_inv] using hb) T S hS


private theorem window_log_le_sqrt {C A : ℝ} (hC : 1 ≤ C) (hA : 1 ≤ A)
    (d : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    Real.log (C ^ 2 * A * (18 + 2 * u) ^ d) / Real.log (7/6) ≤
      ((2 * Real.log C + Real.log A + (d : ℝ) * (Real.log 18 + 2)) / Real.log (7/6)) *
        (u + 1) ^ (1/2 : ℝ) := by
  let W := (u + 1) ^ (1/2 : ℝ)
  have hpos : 0 < u + 1 := by linarith
  have hW : 1 ≤ W := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog : Real.log (u+1) ≤ 2 * W := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos (1/2 : ℝ))
    rw [Real.log_rpow hpos] at h
    dsimp [W]
    linarith
  have h18 : 0 ≤ Real.log 18 := Real.log_nonneg (by norm_num)
  have hlin : Real.log (18 + 2*u) ≤ (Real.log 18 + 2) * W := calc
    _ ≤ Real.log (18 * (u+1)) := Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 18 + Real.log (u+1) := Real.log_mul (by norm_num) hpos.ne'
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hW h18]
  have hCA : 0 ≤ 2 * Real.log C + Real.log A := by
    linarith [Real.log_nonneg hC, Real.log_nonneg hA]
  have hcp : 0 < C := zero_lt_one.trans_le hC
  have hap : 0 < A := zero_lt_one.trans_le hA
  have hbase : 0 < 18 + 2*u := by positivity
  rw [Real.log_mul (mul_pos (sq_pos_of_pos hcp) hap).ne' (pow_pos hbase d).ne',
    Real.log_mul (sq_pos_of_pos hcp).ne' hap.ne', Real.log_pow, Real.log_pow]
  push_cast
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
  change 2 * Real.log C + Real.log A + (d : ℝ) * Real.log (18 + 2*u) ≤ _ * W
  nlinarith [mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg (α := ℝ) d),
    mul_le_mul_of_nonneg_left hW hCA]

/-- A bound on the product of the two finite L-functions at the left edge
controls the entire inverse-square-weighted mass of the actual positive
completed divisor. The field constant is independent of the character and of
the coefficient and degree in the boundary estimate. -/
theorem exists_uniform_heckeZeroMass_of_paired_left_bound (F : Type*) [Field F] [NumberField F] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
      χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      ∀ (d : ℕ) (A : ℝ), 1 ≤ A →
      (∀ z : ℂ, z.re = -(3/2 : ℝ) →
        ‖(continuedCompletedHeckeL χ z / heckeGammaFactor χ z) *
          (continuedCompletedHeckeL χ⁻¹ z / heckeGammaFactor χ⁻¹ z)‖ ≤ A * (1 + |z.im|) ^ d) →
      let mass := fun z : ℂ ↦ ((MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z).toNat : ℝ) /
        (1 + |z.im|) ^ 2
      Summable mass ∧ ∑' z, mass z ≤ K * (1 + Real.log A + (d : ℝ)) := by
  classical
  obtain ⟨C, hC, hwindow⟩ := exists_uniform_heckeZeroWindow_of_paired_left_bound F
  let H := 2 * Real.log C + Real.log 18 + 3
  let Z := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
  let Δ := Real.log (7/6)
  have hΔ : 0 < Δ := Real.log_pos (by norm_num)
  have hZ : 0 ≤ Z := tsum_nonneg fun _ ↦ by positivity
  have h₁₈ : 0 ≤ Real.log 18 := Real.log_nonneg (by norm_num)
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hC]
  refine ⟨2 * H / Δ * Z, by positivity [show 0 < H from zero_lt_one.trans_le hH],
    fun χ hχ d A hA hb ↦ ?_⟩
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
  let m (z : ℂ) : ℝ := (D z).toNat
  let B := (2 * Real.log C + Real.log A + (d : ℝ) * (Real.log 18 + 2)) / Δ
  have hW (t : ℝ) (S : Finset ℂ) (hs : ∀ z ∈ S, |z.im - t| ≤ 1) :
      ∑ z ∈ S, m z ≤ B * (|t| + 1) ^ (1/2 : ℝ) := by
    have heq : (∑ z ∈ S, m z) = ∑ z ∈ S.filter (fun z ↦ 0 < D z), (D z : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs with hz
      · dsimp [m]
        exact_mod_cast (Int.toNat_of_nonneg hz.le)
      · simp [m, Int.toNat_of_nonpos (le_of_not_gt hz)]
    rw [heq]
    apply (hwindow χ hχ d A hA hb t _ ?_).trans (window_log_le_sqrt hC hA d |t| (abs_nonneg t))
    intro z hz
    obtain ⟨hz, hD⟩ := Finset.mem_filter.mp hz
    have hin := heckePositiveDivisor_open_strip χ hD
    exact ⟨hin.1.le, hin.2.le, hs z hz⟩
  have hbin (n : ℕ) (S : Finset ℂ) (hs : ∀ z ∈ S, ⌊|z.im|⌋₊ = n) :
      ∑ z ∈ S, m z ≤ (2*B) * ((n : ℝ) + 1) ^ (1/2 : ℝ) := by
    have hrange (z : ℂ) (hz : z ∈ S) : (n : ℝ) ≤ |z.im| ∧ |z.im| < (n : ℝ) + 1 := by
      rw [← hs z hz]
      exact ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
    let pos (z : ℂ) := 0 ≤ z.im
    have hp := hW n (S.filter pos) (by
      intro z hz
      obtain ⟨hz, hpos⟩ := Finset.mem_filter.mp hz
      have h := hrange z hz
      rw [abs_of_nonneg (show 0 ≤ z.im from hpos)] at h
      exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)
    have hn := hW (-(n : ℝ)) (S.filter (fun z ↦ ¬pos z)) (by
      intro z hz
      obtain ⟨hz, hneg⟩ := Finset.mem_filter.mp hz
      have h := hrange z hz
      rw [abs_of_neg (lt_of_not_ge (show ¬0 ≤ z.im from hneg))] at h
      exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩)
    rw [← Finset.sum_filter_add_sum_filter_not S pos m]
    simp only [abs_neg, Nat.abs_cast] at hp hn
    linarith
  obtain ⟨hsm, hm⟩ := tsum_zeroWeights_le_of_bins Complex.im m (fun _ ↦ Nat.cast_nonneg _) (2*B) hbin
  refine ⟨hsm, hm.trans ?_⟩
  change 2 * B * Z ≤ 2 * H / Δ * Z * (1 + Real.log A + (d : ℝ))
  have hlin : 2 * Real.log C + Real.log A + (d : ℝ) * (Real.log 18 + 2) ≤
      H * (1 + Real.log A + (d : ℝ)) := by
    have hbase : 2 * Real.log C ≤ H := by dsimp [H]; linarith
    have hd : Real.log 18 + 2 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hC]
    nlinarith [mul_le_mul_of_nonneg_right hH (Real.log_nonneg hA),
      mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) d)]
  calc
    2 * B * Z ≤ 2 * (H * (1 + Real.log A + (d : ℝ)) / Δ) * Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlin hΔ.le)
        (by norm_num)) hZ
    _ = _ := by ring

end RiemannMasullo.StripNuclearity
