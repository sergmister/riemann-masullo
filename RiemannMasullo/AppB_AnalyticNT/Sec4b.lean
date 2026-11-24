module

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
import RiemannMasullo.AppB_AnalyticNT.Sec1
public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec4a
public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.ForMathlib.Analysis.Complex.LandauLemma
import RiemannMasullo.ForMathlib.Analysis.Fourier.Log
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.WeightedIntegral
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import all RiemannMasullo.AppB_AnalyticNT.Sec2
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.DigammaIntegral
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Digamma
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Topology.Algebra.IsOpenUnits
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.External.Grh.Props.HeckeContourReflection

/-!
# Explicit formulas for Hecke L-functions

Masullo, §§B.4.2–B.4.4, pp. 614–626. The Schwartz test on the positive
real line is written in its logarithmic coordinate.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "halfPlane" => (Complex.re ⁻¹' Ioi (1 : ℝ))
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0
local notation "logMellin" => (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

section MellinExplicitFormula

-- TODO(paper-gap): The unnumbered residue identity on p. 614 reverses the
-- signs in (B.4.2.2). Poles are present only for norm characters and may be shifted.

/-- Helper for `hasSlowGrowthNearPoles_completedHeckeL_logDeriv`: a function analytic at
every point of a closed horizontal segment is differentiable on a thin open strip around it. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_tube {f : ℂ → ℂ} {a b t : ℝ}
    (h : ∀ σ ∈ Icc a b, AnalyticAt ℂ f ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    ∃ δ > (0 : ℝ), DifferentiableOn ℂ f
      (Complex.re ⁻¹' Ioo a b ∩ Complex.im ⁻¹' Ioo (t - δ) (t + δ)) := by
  let K : Set ℂ := (fun σ : ℝ ↦ (σ : ℂ) + (t : ℂ) * Complex.I) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKt : K ⊆ {z | AnalyticAt ℂ f z} := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact h σ hσ
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open (isOpen_analyticAt ℂ f) hKt
  refine ⟨δ, hδ, fun z hz ↦ ?_⟩
  have hmem : z ∈ Metric.thickening δ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(z.re : ℂ) + (t : ℂ) * Complex.I, ⟨z.re, Ioo_subset_Icc_self hz.1, rfl⟩, ?_⟩
    rw [Complex.dist_eq]
    have he : z - ((z.re : ℂ) + (t : ℂ) * Complex.I) = (((z.im - t : ℝ)) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have := hz.2
    simp only [mem_preimage, mem_Ioo] at this
    constructor <;> linarith
  exact (hsub hmem : AnalyticAt ℂ f z).differentiableAt.differentiableWithinAt

/-- Helper for `hasSlowGrowthNearPoles_completedHeckeL_logDeriv`: good heights near the
integers on both tails, together with the vertical-line clause, give a witness.
The finitely many indices near zero are sent to good heights by a monotone clamp. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_assemble {f : ℂ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : MeromorphicOn f (Complex.re ⁻¹' Ioo a b)) (T : ℤ → ℝ)
    (hT : Monotone T) (A β : ℝ) (hA : 0 < A) (hβ : 0 < β)
    (hgood : ∀ᶠ k : ℤ in comap abs atTop, |T k - k| ≤ 1 ∧
      ∀ σ ∈ Icc a b, AnalyticAt ℂ f ((σ : ℂ) + (T k : ℂ) * Complex.I) ∧
        ‖f ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ ≤ A * |T k| ^ β)
    (hvert : ∃ ε₁ ε₂ : ℝ, 0 < ε₁ ∧ ε₁ < ε₂ ∧ ε₂ < (b - a) / 2 ∧
      ∀ σ ∈ ({a + ε₁, b - ε₂} : Set ℝ),
        Continuous (fun y : ℝ ↦ f ((σ : ℂ) + (y : ℂ) * Complex.I)) ∧
          ∃ γ > (0 : ℝ), (fun y : ℝ ↦ f ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[comap abs atTop]
            (fun y : ℝ ↦ |y| ^ γ)) :
    HasSlowGrowthNearPoles f a b := by
  obtain ⟨N₀, hN₀⟩ := (atTop_basis.comap (abs : ℤ → ℤ)).eventually_iff.mp hgood
  simp only [mem_preimage, mem_Ici, true_and] at hN₀
  set N : ℤ := max N₀ 1 with hNdef
  have hN1 : 1 ≤ N := le_max_right _ _
  have hP : ∀ k : ℤ, N ≤ |k| → _ := fun k hk ↦ hN₀ (le_trans (le_max_left _ _) hk)
  let c : ℤ → ℤ := fun k ↦ if 0 ≤ k then max k N else min k (-(N + 2))
  have hc_abs : ∀ k, N ≤ |c k| := by
    intro k
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg (show 0 ≤ max k N by omega)]; omega
    · rw [abs_of_neg (show min k (-(N + 2)) < 0 by omega)]; omega
  have hc_ge : ∀ k, |k| ≤ |c k| := by
    intro k
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg h, abs_of_nonneg (show 0 ≤ max k N by omega)]; omega
    · rw [abs_of_neg (show k < 0 by omega),
        abs_of_neg (show min k (-(N + 2)) < 0 by omega)]; omega
  have hc_le : ∀ k, |c k| ≤ max |k| (N + 2) := by
    intro k
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg h, abs_of_nonneg (show 0 ≤ max k N by omega)]; omega
    · rw [abs_of_neg (show k < 0 by omega),
        abs_of_neg (show min k (-(N + 2)) < 0 by omega)]; omega
  have hc_mono : Monotone c := by
    intro i j hij
    simp only [c]
    split_ifs <;> omega
  have hc_eq : ∀ k, N + 2 ≤ |k| → c k = k := by
    intro k hk
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg h] at hk; omega
    · rw [abs_of_neg (by omega)] at hk; omega
  set T' : ℤ → ℝ := fun k ↦ T (c k) with hT'
  have hnear : ∀ k, |T' k - c k| ≤ 1 := fun k ↦ (hP (c k) (hc_abs k)).1
  have hnear' : ∀ k, (c k : ℝ) - 1 ≤ T' k ∧ T' k ≤ c k + 1 := fun k ↦ by
    have := abs_le.mp (hnear k); constructor <;> linarith [this.1, this.2]
  have hT'mono : Monotone T' := hT.comp hc_mono
  have hpos : ∀ n : ℕ, 0 ≤ T' n := by
    intro n
    have h1 : c n = max (n : ℤ) N := by simp [c]
    have h2 : (N : ℝ) ≤ c n := by rw [h1]; exact_mod_cast le_max_right _ _
    have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith [(hnear' n).1]
  have hneg : ∀ n : ℕ, 1 ≤ n → T' (-(n : ℤ)) ≤ -(N + 1) := by
    intro n hn
    have h1 : c (-(n : ℤ)) = min (-(n : ℤ)) (-(N + 2)) := by
      simp only [c]; rw [ite_eq_right_iff.mpr (by omega)]
    have h2 : (c (-(n : ℤ)) : ℝ) ≤ -(N + 2) := by
      rw [h1]; exact_mod_cast min_le_right _ _
    linarith [(hnear' (-(n : ℤ))).2]
  refine ⟨T', hab, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvert⟩
  · -- positive tail
    intro m n hmn
    simp only
    rw [abs_of_nonneg (hpos m), abs_of_nonneg (hpos n)]
    exact hT'mono (by exact_mod_cast hmn)
  · -- negative tail
    intro m n hmn
    simp only
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact le_rfl
      · have h0 : T' (-((0 : ℕ) : ℤ)) ≤ N + 1 := by
          have h1 : c (-((0 : ℕ) : ℤ)) = N := by simp [c]; omega
          have := (hnear' (-((0 : ℕ) : ℤ))).2
          rw [h1] at this; exact this
        have h0' : 0 ≤ T' (-((0 : ℕ) : ℤ)) := by simpa using hpos 0
        have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        rw [abs_of_nonneg h0', abs_of_neg (show T' (-(n : ℤ)) < 0 by linarith [hneg n hn])]
        linarith [hneg n hn]
    · have hn : 1 ≤ n := le_trans hm hmn
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      rw [abs_of_neg (show T' (-(m : ℤ)) < 0 by linarith [hneg m hm]),
        abs_of_neg (show T' (-(n : ℤ)) < 0 by linarith [hneg n hn])]
      have : T' (-(n : ℤ)) ≤ T' (-(m : ℤ)) := hT'mono (by omega)
      linarith
  · -- divergence
    have hlow : ∀ k : ℤ, |(k : ℝ)| - 1 ≤ |T' k| := fun k ↦ by
      have h1 : |(k : ℝ)| ≤ |(c k : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast hc_ge k
      have h3 := abs_sub_abs_le_abs_sub (c k : ℝ) (T' k)
      rw [abs_sub_comm] at h3
      linarith [hnear k]
    have h1 : Tendsto (fun k : ℤ ↦ |(k : ℝ)| - 1) (comap abs atTop) atTop := by
      have h0 := (tendsto_intCast_atTop_atTop (R := ℝ)).comp
        (Filter.tendsto_comap (f := (abs : ℤ → ℤ)) (x := atTop))
      have h2 : Tendsto (fun k : ℤ ↦ |(k : ℝ)|) (comap abs atTop) atTop :=
        h0.congr fun k ↦ by simp
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-1 : ℝ) h2
    exact tendsto_atTop_mono hlow h1
  · refine ⟨1, one_pos, Asymptotics.IsBigO.of_bound 2 ?_⟩
    filter_upwards [(atTop_basis.comap (abs : ℤ → ℤ)).eventually_iff.mpr
      ⟨N + 2, trivial, fun k hk ↦ hk⟩] with k hk
    simp only [mem_preimage, mem_Ici] at hk
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    have hck := hc_eq k hk
    have h := hnear k
    rw [hck] at h
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast (by omega : (1 : ℤ) ≤ |k|)
    have h3 := abs_sub_abs_le_abs_sub (T' k) (k : ℝ)
    linarith
  · refine ⟨1 / 2, 1, by norm_num, one_pos, ?_⟩
    filter_upwards [(atTop_basis.comap (abs : ℤ → ℤ)).eventually_iff.mpr
      ⟨N + 2, trivial, fun k hk ↦ hk⟩] with k hk
    simp only [mem_preimage, mem_Ici] at hk
    rw [Real.rpow_one]
    have h := hnear k
    rw [hc_eq k hk] at h
    have hk1 : (2 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast (by omega : (2 : ℤ) ≤ |k|)
    have h3 := abs_sub_abs_le_abs_sub (k : ℝ) (T' k)
    rw [abs_sub_comm] at h3
    linarith
  · intro k
    exact hasSlowGrowthNearPoles_completedHeckeL_logDeriv_tube
      (fun σ hσ ↦ ((hP (c k) (hc_abs k)).2 σ hσ).1)
  · refine ⟨β, A * ((N : ℝ) + 3) ^ β, hβ, by positivity, fun k hk σ hσ ↦ ?_⟩
    have h := ((hP (c k) (hc_abs k)).2 σ (Ioo_subset_Icc_self hσ)).2
    refine h.trans ?_
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    have hcl : |(c k : ℝ)| ≤ max |(k : ℝ)| ((N : ℝ) + 2) := by
      rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast hc_le k
    have h3 := abs_sub_abs_le_abs_sub (T' k) (c k : ℝ)
    have hT1 : |T' k| ≤ ((N : ℝ) + 3) * |(k : ℝ)| := by
      have hN : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : (0 : ℤ) ≤ N)
      have : max |(k : ℝ)| ((N : ℝ) + 2) ≤ ((N : ℝ) + 2) * |(k : ℝ)| := by
        apply max_le <;> nlinarith
      nlinarith [hnear k]
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (abs_nonneg _)]
    gcongr

section HorizontalHeights

open Metric

/-- A unit interval contains a point separated from the imaginary parts of a finite set. -/
private theorem completedHeckeL_height_avoid (S : Finset ℂ) (k W : ℝ)
    (hW : (S.card : ℝ) ≤ W) :
    ∃ t ∈ Icc (k - 1 / 2) (k + 1 / 2), ∀ ρ ∈ S, 1 / (4 * (W + 1)) ≤ |t - ρ.im| := by
  let δ := 1 / (4 * (W + 1))
  let J (ρ : ℂ) := Ioo (ρ.im - δ) (ρ.im + δ)
  let K := Icc (k - 1 / 2) (k + 1 / 2)
  have hW₀ : 0 ≤ W := (Nat.cast_nonneg _).trans hW
  have hδ : 0 < δ := by positivity
  by_contra! h
  have hK : K ⊆ ⋃ ρ ∈ S, J ρ := by
    intro t ht
    obtain ⟨ρ, hρ, ha⟩ := h t ht
    refine mem_iUnion₂.mpr ⟨ρ, hρ, ?_⟩
    have he := abs_lt.mp ha
    change ρ.im - δ < t ∧ t < ρ.im + δ
    constructor <;> linarith
  have hvol (ρ : ℂ) : volume (J ρ) = ENNReal.ofReal (2 * δ) := by
    change volume (Ioo (ρ.im - δ) (ρ.im + δ)) = _
    rw [Real.volume_Ioo]
    congr 1
    ring
  have h₁ := (measure_mono (μ := volume) hK).trans (measure_biUnion_finset_le S J)
  have hKvol : volume K = ENNReal.ofReal 1 := by
    change volume (Icc (k - 1 / 2) (k + 1 / 2)) = _
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [hKvol, Finset.sum_congr rfl (fun ρ _ ↦ hvol ρ), Finset.sum_const,
    ← ENNReal.ofReal_nsmul, nsmul_eq_mul] at h₁
  have h₂ : 1 ≤ (S.card : ℝ) * (2 * δ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h₁
  have h₃ := h₂.trans (mul_le_mul_of_nonneg_right hW (by positivity : 0 ≤ 2 * δ))
  dsimp [δ] at h₃
  have h₄ : W * (2 * (1 / (4 * (W + 1)))) = W / (2 * (W + 1)) := by
    have hp : W + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [h₄, le_div_iff₀ (by positivity)] at h₃
  linarith

/-- At the nearby heights, polynomial control of the normalized logarithmic maximum
on discs gives a uniform bound across the closed strip. -/
private theorem completedHeckeL_height_local {f : ℂ → ℂ} (k B : ℝ)
    (hB : 1 < B)
    (hf : AnalyticOnNhd ℂ f (closedBall ⟨2, k⟩ 6)) (hc : f ⟨2, k⟩ ≠ 0)
    (hbound : ∀ u ∈ closedBall ⟨2, k⟩ 6, ‖f u / f ⟨2, k⟩‖ ≤ B) :
    ∃ t ∈ Icc (k - 1 / 2) (k + 1 / 2),
      ∀ σ ∈ Icc (-1 : ℝ) 2,
        AnalyticAt ℂ (logDeriv f) ⟨σ, t⟩ ∧
          ‖logDeriv f ⟨σ, t⟩‖ ≤
            landauConstant 4 5 (11 / 2) 6 * Real.log B +
              4 * (Real.log B / Real.log (6 / 5)) * (Real.log B / Real.log (6 / 5) + 1) := by
  classical
  let c : ℂ := ⟨2, k⟩
  have hf' : AnalyticOnNhd ℂ f (closedBall c 5) :=
    hf.mono (closedBall_subset_closedBall (by norm_num))
  let S := (finite_zeros_closedBall (by norm_num) hf' hc).toFinset
  have hS (ρ : ℂ) : ρ ∈ S ↔ ρ ∈ closedBall c 5 ∧ f ρ = 0 := by simp [S]
  have hnonzero {ρ : ℂ} (hρ : f ρ ≠ 0) : analyticOrderNatAt f ρ = 0 := by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hρ)]
  have hpositive (ρ : ℂ) (hρ : ρ ∈ S) : 1 ≤ analyticOrderNatAt f ρ := by
    obtain ⟨hb, hz⟩ := (hS ρ).mp hρ
    have ht := hf'.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c 5).isPreconnected
      (x := c) (mem_closedBall_self (by norm_num)) hb (by
        have he : analyticOrderAt f c = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hc)
        simp [he])
    have hzero : analyticOrderAt f ρ ≠ 0 := by
      rw [ne_eq, analyticOrderAt_eq_zero]
      exact not_or_intro (not_not_intro (hf' ρ hb)) (not_not_intro hz)
    have he := ENat.natCast_toNat ht
    change ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) = analyticOrderAt f ρ at he
    by_contra! hn
    have hn' : analyticOrderNatAt f ρ = 0 := by omega
    rw [hn'] at he
    exact hzero (by simpa using he.symm)
  have hsum {M : Type} [AddCommMonoid M] (φ : ℂ → M)
      (hφ : ∀ ρ, analyticOrderNatAt f ρ = 0 → φ ρ = 0) :
      ∑ᶠ ρ ∈ closedBall c 5, φ ρ = ∑ ρ ∈ S, φ ρ := by
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_inter_support_eq' _ _ _ fun ρ hρ ↦ ?_
    have hn : f ρ = 0 := by
      by_contra h
      exact hρ (hφ ρ (hnonzero h))
    simp [hS, hn]
  let W := Real.log B / Real.log (6 / 5)
  have hW : (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) ≤ W := by
    rw [← hsum (fun ρ ↦ (analyticOrderNatAt f ρ : ℝ)) (fun _ ho ↦ by simp [ho])]
    exact landau_sum_analyticOrderNatAt_le (by norm_num) (by norm_num) hf hc hbound
  have hcard : (S.card : ℝ) ≤ W := by
    refine le_trans ?_ hW
    calc
      (S.card : ℝ) = ∑ _ρ ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun ρ hρ ↦ by exact_mod_cast hpositive ρ hρ)
  obtain ⟨t, ht, havoid⟩ := completedHeckeL_height_avoid S k W hcard
  let δ := 1 / (4 * (W + 1))
  have hW₀ : 0 ≤ W := (Nat.cast_nonneg _).trans hcard
  have hδ : 0 < δ := by positivity
  refine ⟨t, ht, fun σ hσ ↦ ?_⟩
  let z : ℂ := ⟨σ, t⟩
  have hz : z ∈ closedBall c 4 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hzr : z - c = ((σ - 2 : ℝ) : ℂ) + ((t - k : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [z, c, Complex.sub_re, Complex.sub_im]
    rw [hzr]
    refine norm_add_le _ _ |>.trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr hσ.2)]
    have ht' : |t - k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith [hσ.1]
  have hz' : z ∈ closedBall c 5 := closedBall_subset_closedBall (by norm_num) hz
  have hsep (ρ : ℂ) (hρ : ρ ∈ S) : δ ≤ ‖z - ρ‖ :=
    (havoid ρ hρ).trans (by simpa [z] using Complex.abs_im_le_norm (z - ρ))
  have hfz : f z ≠ 0 := by
    intro he
    have h := hsep z ((hS z).mpr ⟨hz', he⟩)
    exact (not_le_of_gt hδ) (by simpa using h)
  refine ⟨(hf' z hz').deriv.div (hf' z hz') hfz, ?_⟩
  have hld := landau_norm_logDeriv_sub_le hB (by norm_num : (0 : ℝ) < 4)
    (by norm_num : (4 : ℝ) < 5) (by norm_num : (5 : ℝ) < 11 / 2)
    (by norm_num : (11 / 2 : ℝ) < 6) hf hc hbound hz hfz
  let P (ρ : ℂ) := (analyticOrderNatAt f ρ : ℂ) / (z - ρ)
  rw [show (∑ᶠ ρ ∈ closedBall c 5, ((analyticOrderNatAt f ρ : ℂ) / (z - ρ))) =
      ∑ ρ ∈ S, P ρ from hsum P (fun ρ hρ ↦ by simp [P, hρ])] at hld
  have hP : ‖∑ ρ ∈ S, P ρ‖ ≤ 4 * W * (W + 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ) / δ := by
        refine Finset.sum_le_sum fun ρ hρ ↦ ?_
        change ‖(analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ _
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep ρ hρ)
      _ = (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) / δ := (Finset.sum_div _ _ _).symm
      _ ≤ W / δ := div_le_div_of_nonneg_right hW hδ.le
      _ = _ := by rw [show δ = (4 * (W + 1))⁻¹ by simp [δ], div_inv_eq_mul]; ring
  have h := norm_add_le (logDeriv f z - ∑ ρ ∈ S, P ρ) (∑ ρ ∈ S, P ρ)
  rw [sub_add_cancel] at h
  exact h.trans (add_le_add hld hP)

/-- A normalized disc bound at large heights gives polynomial estimates at a
monotone sequence within half a unit of each integer. -/
private theorem completedHeckeL_heights_of_discs {f : ℂ → ℂ} (C : ℝ) (hC : 0 < C)
    (h : ∀ᶠ k : ℝ in comap abs atTop,
      AnalyticOnNhd ℂ f (closedBall ⟨2, k⟩ 6) ∧ f ⟨2, k⟩ ≠ 0 ∧
        ∀ u ∈ closedBall (⟨2, k⟩ : ℂ) 6, ‖f u / f ⟨2, k⟩‖ ≤ Real.exp (C * (1 + |k|))) :
    ∃ T : ℤ → ℝ, Monotone T ∧ ∃ A β : ℝ, 0 < A ∧ 0 < β ∧
      ∀ᶠ k : ℤ in comap abs atTop, |T k - k| ≤ 1 ∧
        ∀ σ ∈ Icc (-1 : ℝ) 2,
          AnalyticAt ℂ (logDeriv f) ((σ : ℂ) + (T k : ℂ) * Complex.I) ∧
            ‖logDeriv f ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ ≤ A * |T k| ^ β := by
  classical
  let D := landauConstant 4 5 (11 / 2) 6
  let d := Real.log (6 / 5)
  have hD : 0 < D := landauConstant_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : 0 < d := Real.log_pos (by norm_num)
  let Q := 3 * C / d
  have hQ : 0 < Q := by positivity
  let A := D * (3 * C) + 4 * Q * (Q + 1)
  have hA : 0 < A := by positivity
  let Good (k : ℤ) (t : ℝ) :=
    t ∈ Icc ((k : ℝ) - 1 / 2) (k + 1 / 2) ∧ ∀ σ ∈ Icc (-1 : ℝ) 2,
      AnalyticAt ℂ (logDeriv f) (⟨σ, t⟩ : ℂ) ∧ ‖logDeriv f ⟨σ, t⟩‖ ≤ A * |t| ^ 2
  have htend : Tendsto (fun k : ℤ ↦ (k : ℝ)) (comap abs atTop) (comap abs atTop) := by
    apply tendsto_comap_iff.mpr
    exact ((tendsto_intCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_comap (f := (abs : ℤ → ℤ)) (x := atTop))).congr fun k ↦ by
        exact Int.cast_abs
  have hGood : ∀ᶠ k : ℤ in comap abs atTop, ∃ t, Good k t := by
    filter_upwards [htend.eventually h,
      htend.eventually (tendsto_comap.eventually (eventually_ge_atTop (2 : ℝ)))] with k hk hk₂
    change 2 ≤ |(k : ℝ)| at hk₂
    let B := Real.exp (C * (1 + |(k : ℝ)|))
    have hB : 1 < B := Real.one_lt_exp_iff.mpr (by positivity)
    obtain ⟨t, ht, hlocal⟩ := completedHeckeL_height_local (k : ℝ) B hB hk.1 hk.2.1 hk.2.2
    have hnear : |t - (k : ℝ)| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hheight := (abs_sub_abs_le_abs_sub (k : ℝ) t).trans (by simpa [abs_sub_comm] using hnear)
    have ht₁ : 1 ≤ |t| := by linarith
    have hlog : Real.log B ≤ (3 * C) * |t| := by
      rw [show Real.log B = C * (1 + |(k : ℝ)|) by exact Real.log_exp _]
      exact (by nlinarith : C * (1 + |(k : ℝ)|) ≤ C * (3 * |t|)).trans_eq (by ring)
    have hdiv : Real.log B / d ≤ Q * |t| := by
      exact (div_le_div_of_nonneg_right hlog hd.le).trans_eq (by dsimp [Q]; ring)
    have hdiv₁ : Real.log B / d + 1 ≤ (Q + 1) * |t| := by nlinarith
    have hdiv₀ : 0 ≤ Real.log B / d := div_nonneg (Real.log_nonneg hB.le) hd.le
    refine ⟨t, ht, fun σ hσ ↦ ⟨(hlocal σ hσ).1, (hlocal σ hσ).2.trans ?_⟩⟩
    change D * Real.log B + 4 * (Real.log B / d) * (Real.log B / d + 1) ≤ A * |t| ^ 2
    calc
      _ ≤ D * ((3 * C) * |t|) + 4 * (Q * |t|) * ((Q + 1) * |t|) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hlog hD.le)
          (mul_le_mul (mul_le_mul_of_nonneg_left hdiv (by norm_num)) hdiv₁ (by positivity) (by positivity))
      _ ≤ _ := by
        have ht₂ := mul_le_mul_of_nonneg_left ht₁ (show 0 ≤ D * (3 * C) * |t| by positivity)
        dsimp [A]
        nlinarith
  let T (k : ℤ) := if h : ∃ t, Good k t then h.choose else (k : ℝ)
  have hNear (k : ℤ) : T k ∈ Icc ((k : ℝ) - 1 / 2) (k + 1 / 2) := by
    dsimp only [T]
    split_ifs with h
    · exact h.choose_spec.1
    · constructor <;> linarith
  have hMono : Monotone T := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show i + 1 ≤ j by omega)
    linarith [(hNear i).2, (hNear j).1]
  refine ⟨T, hMono, A, 2, hA, by norm_num, ?_⟩
  filter_upwards [hGood] with k hk
  have hTk : Good k (T k) := by
    dsimp only [T]
    rw [dite_eq_left hk]
    exact hk.choose_spec
  refine ⟨abs_le.mpr ⟨by linarith [hTk.1.1], by linarith [hTk.1.2]⟩, fun σ hσ ↦ ?_⟩
  have he : (σ : ℂ) + (T k : ℂ) * Complex.I = ⟨σ, T k⟩ := by
    apply Complex.ext <;> simp
  rw [he, Real.rpow_two]
  exact hTk.2 σ hσ

/-- The two possible poles are below a fixed absolute height. -/
private theorem completedHeckeL_height_analytic (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    ∀ᶠ t : ℝ in comap abs atTop, AnalyticOnNhd ℂ L (closedBall ⟨2, t⟩ 6) := by
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨p, hp, -⟩ := completedHeckeL_continuation_simplePoles χ L hL hAgree hχ
    filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (|p| + 7))] with t ht
    intro u hu
    have hdist : |u.im - t| ≤ 6 := by
      have h := Complex.abs_im_le_norm (u - (⟨2, t⟩ : ℂ))
      rw [Complex.sub_im] at h
      exact h.trans (by simpa [mem_closedBall, Complex.dist_eq] using hu)
    have hdiff' := abs_sub_abs_le_abs_sub t u.im
    rw [abs_sub_comm t u.im] at hdiff'
    have ht' : |p| + 7 ≤ |t| := ht
    have hne : u.im ≠ p := by
      intro hu
      rw [hu] at hdist hdiff'
      linarith
    apply hp.2.2.2 u
    have h₁ : u ≠ Complex.I * (p : ℂ) := fun h ↦ hne (by
      simpa [Complex.mul_im] using congrArg Complex.im h)
    have h₂ : u ≠ 1 + Complex.I * (p : ℂ) := fun h ↦ hne (by
      simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im h)
    simp [h₁, h₂]
  · have h := completedHeckeL_continuation_entire χ L hL hAgree hχ
    exact Eventually.of_forall fun _ u _ ↦ h.differentiableOn.analyticOnNhd isOpen_univ u (mem_univ u)

/-- Paper: §B.4.2.1, p. 614 (citing Lang, Ch. XVII, Prop. 2.3, Cor. 2.5, Prop. 2.7).
The logarithmic derivative of the completed function is polynomially bounded on
horizontal segments of the strip at a monotone sequence of heights, one within distance
one of each large integer, and is analytic along those segments.
Deviation: The heights are the horizontal part of Definition B.3.1.1, stated on both tails
at once; the segments are closed and run from `1 - a` to `a`. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_heights (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (ha : 1 < a) (haMax : a ≤ 2) :
    ∃ T : ℤ → ℝ, Monotone T ∧ ∃ A β : ℝ, 0 < A ∧ 0 < β ∧
      ∀ᶠ k : ℤ in comap abs atTop, |T k - k| ≤ 1 ∧
        ∀ σ ∈ Icc (1 - a) a,
          AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (T k : ℂ) * Complex.I) ∧
            ‖logDeriv L ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ ≤ A * |T k| ^ β := by
  obtain ⟨C, hC, hDisc⟩ :=
    completedHeckeL_continuation_disc_bound χ L hL hAgree 2 6 (by norm_num) (by norm_num)
  obtain ⟨T, hT, A, β, hA, hβ, hGood⟩ := completedHeckeL_heights_of_discs C hC
    ((completedHeckeL_height_analytic χ L hL hAgree).and hDisc)
  refine ⟨T, hT, A, β, hA, hβ, hGood.mono fun k hk ↦ ⟨hk.1, fun σ hσ ↦ hk.2 σ ?_⟩⟩
  have hleft : 1 - a ∈ Icc (-1 : ℝ) 0 := ⟨by linarith only [haMax], sub_nonpos.mpr ha.le⟩
  exact ⟨hleft.1.trans hσ.1, hσ.2.trans haMax⟩

end HorizontalHeights

local notation "finiteSeries(" χ ")" => LSeries (χ₀(χ)).LFunction

private theorem completedHeckeL_logDeriv_abscissa (χ : U[F]) {z : ℂ} (hz : 1 < z.re) :
    LSeries.abscissaOfAbsConv (χ₀(χ)).LFunction < (z.re : EReal) := by
  obtain ⟨r, hr, hrz⟩ := exists_between hz
  exact (finiteHeckeL_seriesSummable χ ⟨(r : ℂ), by simpa using hr⟩).abscissaOfAbsConv_le.trans_lt
    (by exact_mod_cast hrz)

/-- A positive lower bound from the Euler product, uniform on a line to the right of one. -/
private theorem completedHeckeL_logDeriv_finite_lower (χ : U[F]) (σ : ℝ) (hσ : 1 < σ)
    (z : ℂ) (hz : z.re = σ) :
    Real.exp (-(∑' v : Primes(F), q(v) ^ (-σ))) ≤ ‖finiteSeries(χ) z‖ := by
  have hz' : 1 < z.re := hz ▸ hσ
  let E (v : Primes(F)) := finiteHeckeEulerFactor χ v z
  let r (v : Primes(F)) := q(v) ^ (-σ)
  have hp : HasProd E (finiteSeries(χ) z) := finiteHeckeL_hasProd χ ⟨z, hz'⟩
  have hsum : Summable r :=
    (summable_absNorm_rpow F hσ).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hnonneg (v : Primes(F)) : 0 ≤ r v := by positivity
  have hlocal (v : Primes(F)) : Real.exp (-r v) ≤ ‖E v‖ := by
    have hv : (1 : ℝ) < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    unfold E finiteHeckeEulerFactor
    split_ifs
    · let u := (χ₀(χ)).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-z)
      change Real.exp (-r v) ≤ ‖(1 - u)⁻¹‖
      have hu : ‖u‖ = r v := by
        dsimp only [u, r]
        rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hv), Complex.neg_re, hz]
      have hu' : ‖u‖ < 1 := by
        rw [hu]
        exact Real.rpow_lt_one_of_one_lt_of_neg hv (by linarith)
      have hne : 1 - u ≠ 0 := fun h ↦ hu'.ne (by rw [← sub_eq_zero.mp h, norm_one])
      rw [norm_inv, Real.exp_neg]
      apply (inv_le_inv₀ (Real.exp_pos _) (norm_pos_iff.mpr hne)).2
      calc
        ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ Real.exp (r v) := by rw [norm_one, hu, add_comm]; exact Real.add_one_le_exp _
    · rw [norm_one]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnonneg v))
  apply ge_of_tendsto' hp.norm
  intro T
  rw [norm_prod]
  calc
    _ ≤ Real.exp (∑ v ∈ T, -r v) := by
      rw [Finset.sum_neg_distrib]
      exact Real.exp_le_exp.mpr (neg_le_neg (hsum.sum_le_tsum T fun v _ ↦ hnonneg v))
    _ = ∏ v ∈ T, Real.exp (-r v) := Real.exp_sum _ _
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) (fun v _ ↦ hlocal v)

private theorem completedHeckeL_logDeriv_finite_bound (χ : U[F]) (σ : ℝ) (hσ : 1 < σ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re = σ → ‖logDeriv (finiteSeries(χ)) z‖ ≤ C := by
  let c := (χ₀(χ)).LFunction
  let a := ∑' n, ‖LSeries.term (LSeries.logMul c) (σ : ℂ) n‖
  let b := Real.exp (∑' v : Primes(F), q(v) ^ (-σ))
  have ha : 0 ≤ a := tsum_nonneg (fun _ ↦ norm_nonneg _)
  have hb : 0 < b := Real.exp_pos _
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have hsσ : Summable (fun n ↦ ‖LSeries.term (LSeries.logMul c) (σ : ℂ) n‖) :=
    (LSeriesSummable_logMul_of_lt_re (completedHeckeL_logDeriv_abscissa χ hσ')).norm
  refine ⟨a * b, mul_nonneg ha hb.le, fun z hz ↦ ?_⟩
  have hz' : 1 < z.re := hz ▸ hσ
  have hc := completedHeckeL_logDeriv_abscissa χ hz'
  have hs : Summable (fun n ↦ ‖LSeries.term (LSeries.logMul c) z n‖) :=
    (LSeriesSummable_logMul_of_lt_re hc).norm
  have hA : ‖LSeries (LSeries.logMul c) z‖ ≤ a :=
    (norm_tsum_le_tsum_norm hs).trans
      (hs.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re (LSeries.logMul c) (by simpa using hz.ge)) hsσ)
  have hLower := completedHeckeL_logDeriv_finite_lower χ σ hσ z hz
  have hB : ‖(finiteSeries(χ) z)⁻¹‖ ≤ b := by
    rw [norm_inv]
    calc
      _ ≤ (Real.exp (-(∑' v : Primes(F), q(v) ^ (-σ))))⁻¹ :=
        (inv_le_inv₀ ((Real.exp_pos _).trans_le hLower) (Real.exp_pos _)).2 hLower
      _ = b := by rw [Real.exp_neg, inv_inv]
  rw [logDeriv_apply, LSeries_deriv hc, div_eq_mul_inv, norm_mul, norm_neg]
  exact mul_le_mul hA hB (norm_nonneg _) ha

/-- The logarithmic derivative of the shifted real gamma factor on its right half-plane. -/
private theorem realHeckeArchimedean_mellinLogDeriv_gamma (b s : ℂ) (h : 0 < ((s + b) / 2).re) :
    logDeriv (fun w ↦ Complex.Gammaℝ (w + b)) s =
      (Complex.digamma ((s + b) / 2) - (Real.log Real.pi : ℂ)) / 2 := by
  let z (w : ℂ) := (w + b) / 2
  let E (w : ℂ) := Complex.exp (-(Real.log Real.pi : ℂ) * z w)
  have hf : (fun w ↦ Complex.Gammaℝ (w + b)) = fun w ↦ E w * Complex.Gamma (z w) := by
    funext w
    rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      ← Complex.ofReal_log Real.pi_pos.le]
    simp only [E, z, neg_div, neg_mul, mul_neg]
  have hz : HasDerivAt z (1 / 2) s := ((hasDerivAt_id s).add_const b).div_const 2
  have hE := (hz.const_mul (-(Real.log Real.pi : ℂ))).cexp
  have hG := (Complex.hasDerivAt_Gamma_of_re_pos h).differentiableAt
  rw [hf, logDeriv_fun_mul (f := E) (g := fun w ↦ Complex.Gamma (z w)) s
    (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero_of_re_pos h) hE.differentiableAt
    (hG.comp s hz.differentiableAt), hz.logDeriv_Gamma (fun m he ↦ by
      have := congrArg Complex.re he
      simp [z] at this h
      linarith [show (0 : ℝ) ≤ m by positivity])]
  rw [logDeriv_apply, show deriv E s = E s * (-(Real.log Real.pi : ℂ) * (1 / 2)) from hE.deriv,
    mul_div_cancel_left₀ _ (show E s ≠ 0 from Complex.exp_ne_zero _)]
  dsimp [z]
  ring

/-- The Gauss kernel bound gives a digamma bound linear in the absolute height. -/
private theorem completedHeckeL_logDeriv_digamma_bound (u : ℝ) (hu : 0 < u) :
    ∃ C ≥ (0 : ℝ), ∀ v : ℝ,
      ‖Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C * (1 + |v|) := by
  let m := min 1 u
  have hm : 0 < m := lt_min one_pos hu
  let K (x : ℝ) := (1 + x) * Real.exp (-m * x)
  have hExp := integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) 0
  have hxExp : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-m * x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) one_pos hm)
  have hK : IntegrableOn K (Ioi 0) := by
    simpa only [K, Pi.add_def, add_mul, one_mul] using hExp.add hxExp
  let A := ∫ x in Ioi (0 : ℝ), K x
  have ha : 0 ≤ A := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact mul_nonneg (by linarith [show 0 < x from hx]) (Real.exp_pos _).le
  let D := ‖Complex.digamma 1‖
  have hd : 0 ≤ D := norm_nonneg _
  refine ⟨(1 + |1 - u|) * A + D, by positivity, fun v ↦ ?_⟩
  let w : ℂ := (u : ℂ) + (v : ℂ) * Complex.I
  have hw : 0 < (w / (1 : ℂ)).re := by simpa [w] using hu
  have hG := (integral_gaussDigammaDifferenceKernel (d := 1) (w := w) one_pos (by simpa using hw)).2
  simp only [Complex.ofReal_one, div_one] at hG
  have hB : ‖∫ x in Ioi (0 : ℝ), gaussDigammaDifferenceKernel 1 w x‖ ≤ (|1 - u| + |v|) * A := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hK.const_mul _) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    simpa only [K, m, div_one] using
      (norm_gaussDigammaDifferenceKernel_le (d := 1) (u := u) (v := v) one_pos (show 0 < x from hx))
  change ‖Complex.digamma w‖ ≤ _
  calc
    _ ≤ ‖Complex.digamma w - Complex.digamma 1‖ + D :=
      (norm_le_insert' (Complex.digamma w) (Complex.digamma 1)).trans_eq (add_comm _ _)
    _ ≤ (|1 - u| + |v|) * A + D := add_le_add (hG ▸ hB) (le_refl D)
    _ ≤ _ := by
      have h₁ := mul_nonneg (mul_nonneg (abs_nonneg (1 - u)) ha) (abs_nonneg v)
      have h₂ := mul_nonneg hd (abs_nonneg v)
      nlinarith

private theorem completedHeckeL_logDeriv_GammaR_regular (b s : ℂ) (h : 0 < (s + b).re) :
    Complex.Gammaℝ (s + b) ≠ 0 ∧ DifferentiableAt ℂ (fun z ↦ Complex.Gammaℝ (z + b)) s := by
  have hn := Complex.Gammaℝ_ne_zero_of_re_pos h
  have hD := Complex.differentiable_Gammaℝ_inv.differentiableAt (x := s + b)
  have hI : DifferentiableAt ℂ (fun z ↦ ((Complex.Gammaℝ z)⁻¹)⁻¹) (s + b) :=
    hD.inv (inv_ne_zero hn)
  exact ⟨hn, (show DifferentiableAt ℂ Complex.Gammaℝ (s + b) from
    by simpa only [inv_inv] using hI).comp s (differentiableAt_id.add_const b)⟩

private theorem completedHeckeL_logDeriv_GammaR_bound (σ : ℝ) (b : ℂ) (h : 0 < σ + b.re) :
    ∃ C ≥ (0 : ℝ), ∀ y : ℝ,
      ‖logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        C * (1 + |y|) := by
  let u := (σ + b.re) / 2
  obtain ⟨A, hA, hD⟩ := completedHeckeL_logDeriv_digamma_bound u (half_pos h)
  let C := A * (1 + |b.im|) + ‖(Real.log Real.pi : ℂ)‖
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, fun y ↦ ?_⟩
  let s := (σ : ℂ) + (y : ℂ) * Complex.I
  have hs : (s + b) / 2 = (u : ℂ) + (((y + b.im) / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [s, u, Complex.div_ofNat_re, Complex.div_ofNat_im]
  have hpos : 0 < ((s + b) / 2).re := by
    rw [hs]
    simpa using (show 0 < u from half_pos h)
  have hv : |(y + b.im) / 2| ≤ |y| + |b.im| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le y b.im, abs_nonneg (y + b.im)]
  change ‖logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) s‖ ≤ _
  rw [realHeckeArchimedean_mellinLogDeriv_gamma b s hpos, norm_div, hs, Complex.norm_ofNat]
  apply (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans
  refine (norm_sub_le _ _).trans ?_
  have hD' := (hD ((y + b.im) / 2)).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hv) hA)
  refine (add_le_add hD' (le_refl _)).trans ?_
  unfold C
  have h₁ := mul_nonneg (mul_nonneg hA (abs_nonneg b.im)) (abs_nonneg y)
  have h₂ := mul_nonneg (norm_nonneg (Real.log Real.pi : ℂ)) (abs_nonneg y)
  nlinarith
private theorem completedHeckeL_logDeriv_GammaC_split (b s : ℂ) (h : 0 < (s + b).re) :
    (Complex.Gammaℂ (s + b) / 2 ≠ 0 ∧
      DifferentiableAt ℂ (fun z ↦ Complex.Gammaℂ (z + b) / 2) s) ∧
    logDeriv (fun z ↦ Complex.Gammaℂ (z + b) / 2) s =
      logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) s +
      logDeriv (fun z ↦ Complex.Gammaℝ (z + (b + 1))) s := by
  have h₁ : 0 < (s + (b + 1)).re := by
    rw [← add_assoc, Complex.add_re, Complex.one_re]
    positivity
  have hR := completedHeckeL_logDeriv_GammaR_regular b s h
  have hR₁ := completedHeckeL_logDeriv_GammaR_regular (b + 1) s h₁
  have he : (fun z ↦ Complex.Gammaℂ (z + b) / 2) =
      fun z ↦ (Complex.Gammaℝ (z + b) * Complex.Gammaℝ (z + (b + 1))) * (2 : ℂ)⁻¹ := by
    funext z
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one, div_eq_mul_inv, add_assoc]
  rw [show Complex.Gammaℂ (s + b) / 2 = _ from congrFun he s, he]
  refine ⟨⟨mul_ne_zero (mul_ne_zero hR.1 hR₁.1) (inv_ne_zero two_ne_zero),
    (hR.2.mul hR₁.2).mul_const _⟩, ?_⟩
  rw [logDeriv_mul_const _ _ (inv_ne_zero two_ne_zero)]
  exact logDeriv_fun_mul _ hR.1 hR₁.1 hR.2 hR₁.2

private theorem completedHeckeL_logDeriv_gammaFactor_bound (χ : U[F]) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C ≥ (0 : ℝ), ∀ y : ℝ,
      ‖logDeriv (heckeGammaFactor χ) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * (1 + |y|) := by
  let G (v : InfinitePlace F) (s : ℂ) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
    else
      let a := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2
  let s (y : ℝ) : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
  have hh (v : InfinitePlace F) : ∃ C ≥ (0 : ℝ), ∀ y,
      G v (s y) ≠ 0 ∧ DifferentiableAt ℂ (G v) (s y) ∧
        ‖logDeriv (G v) (s y)‖ ≤ C * (1 + |y|) := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      let b := a.1 + (a.2.val : ℂ)
      have h0 : 0 ≤ b.re := by
        have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
        change a.1.re = 0 at ha
        simp only [b, Complex.add_re, Complex.natCast_re, ha, zero_add]
        positivity
      have he : G v = fun z ↦ Complex.Gammaℝ (z + b) := by
        funext z
        simp only [G, dite_eq_left hv, b, a, add_assoc]
      obtain ⟨C, hC, hG⟩ := completedHeckeL_logDeriv_GammaR_bound σ b (add_pos_of_pos_of_nonneg hσ h0)
      have hpos (y : ℝ) : 0 < (s y + b).re := by
        simpa [s] using add_pos_of_pos_of_nonneg hσ h0
      refine ⟨C, hC, fun y ↦ ?_⟩
      rw [he]
      have ht := completedHeckeL_logDeriv_GammaR_regular b (s y) (hpos y)
      exact ⟨ht.1, ht.2, hG y⟩
    · let hw := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let a := (complexHeckeCharacter_parameters χ v hw).exists.choose
      let b := a.1 + (a.2.natAbs : ℂ) / 2
      have h0 : 0 ≤ b.re := by
        have ha := (complexHeckeCharacter_parameters χ v hw).exists.choose_spec.1
        change a.1.re = 0 at ha
        simp only [b, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, ha, zero_add]
        positivity
      have he : G v = fun z ↦ Complex.Gammaℂ (z + b) / 2 := by
        funext z
        simp only [G, dite_eq_right hv, b, a, add_assoc]
      obtain ⟨C, hC, hG⟩ := completedHeckeL_logDeriv_GammaR_bound σ b (add_pos_of_pos_of_nonneg hσ h0)
      obtain ⟨D, hD, hG'⟩ := completedHeckeL_logDeriv_GammaR_bound σ (b + 1) (by
        rw [Complex.add_re, Complex.one_re]
        positivity)
      refine ⟨C + D, add_nonneg hC hD, fun y ↦ ?_⟩
      have hpos : 0 < (s y + b).re := by simpa [s] using add_pos_of_pos_of_nonneg hσ h0
      have hs := completedHeckeL_logDeriv_GammaC_split b (s y) hpos
      rw [he]
      refine ⟨hs.1.1, hs.1.2, ?_⟩
      rw [hs.2, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hG y) (hG' y))
  choose C hC hG using hh
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ ↦ hC v, fun y ↦ ?_⟩
  change ‖logDeriv (fun z ↦ ∏ v, G v z) (s y)‖ ≤ _
  rw [logDeriv_fun_prod (fun v _ ↦ (hG v y).1) (fun v _ ↦ (hG v y).2.1), Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ (hG v y).2.2)

/-- On the right half-plane the continuation agrees with its holomorphic product,
whose two factors are nonzero. -/
private theorem completedHeckeL_logDeriv_right_local (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (logDeriv L) z ∧
      logDeriv L z = logDeriv (heckeGammaFactor χ) z + logDeriv (finiteSeries(χ)) z := by
  have hEq : L =ᶠ[𝓝 z] fun w ↦ heckeGammaFactor χ w * finiteSeries(χ) w := by
    have hopen : IsOpen halfPlane := isOpen_Ioi.preimage Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show z ∈ halfPlane from hz)] with w hw
    exact hAgree ⟨w, hw⟩
  have hG₀ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)
  have hF₀ : finiteSeries(χ) z ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos _).trans_le
      (completedHeckeL_logDeriv_finite_lower χ z.re hz z rfl))
  have hL₀ : L z ≠ 0 := hEq.eq_of_nhds ▸ mul_ne_zero hG₀ hF₀
  have hNF : MeromorphicNFAt L z := hL (mem_univ z)
  have hA := hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (le_of_eq (hNF.meromorphicOrderAt_eq_zero_iff.mpr hL₀).symm)
  have hG := differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans hz)
  have hF := (LSeries_hasDerivAt (completedHeckeL_logDeriv_abscissa χ hz)).differentiableAt
  refine ⟨hA.deriv.div hA hL₀, ?_⟩
  exact (logDeriv_congr_nhds hEq).eq_of_nhds.trans (logDeriv_fun_mul _ hG₀ hF₀ hG hF)

/-- Paper: §B.4.2.1, p. 614 (citing Lang, Ch. XVII). On a vertical line to the right
of `Re(s) = 1` the logarithmic derivative of the completed function is continuous and
grows at most polynomially in the height.
Deviation: One of the two interior lines of Definition B.3.1.1, for `1 < σ ≤ 2`. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (σ : ℝ) (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    Continuous (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) ∧
      ∃ γ > (0 : ℝ), (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[comap abs atTop]
        (fun y : ℝ ↦ |y| ^ γ) := by
  have hσRange : σ ∈ Ioc (1 : ℝ) 2 := ⟨hσ, hσ2⟩
  let s (y : ℝ) := (σ : ℂ) + (y : ℂ) * Complex.I
  have hs (y : ℝ) : (s y).re = σ := by simp [s]
  have hloc (y : ℝ) := completedHeckeL_logDeriv_right_local χ L hL hAgree
    (show 1 < (s y).re from (hs y).symm ▸ hσ)
  refine ⟨continuous_iff_continuousAt.mpr fun y ↦ (hloc y).1.continuousAt.comp (by fun_prop), ?_⟩
  obtain ⟨C, hC, hG⟩ := completedHeckeL_logDeriv_gammaFactor_bound χ σ (zero_lt_one.trans hσRange.1)
  obtain ⟨D, hD, hF⟩ := completedHeckeL_logDeriv_finite_bound χ σ hσ
  refine ⟨1, one_pos, Asymptotics.IsBigO.of_bound (2 * C + D) ?_⟩
  filter_upwards [(eventually_ge_atTop (1 : ℝ)).comap abs] with y hy
  change ‖logDeriv L (s y)‖ ≤ _
  rw [(hloc y).2, Real.rpow_one, Real.norm_eq_abs, abs_abs]
  refine (norm_add_le _ _).trans ((add_le_add (hG y) (hF (s y) (hs y))).trans ?_)
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hy), mul_nonneg hD (sub_nonneg.mpr hy)]

/-- Paper: §B.4.2.1, p. 614 (citing Lang, Ch. XVII, and (B.4.2.3)). On a vertical line
to the left of `Re(s) = 0` the logarithmic derivative of the completed function is
continuous and grows at most polynomially in the height.
Deviation: One of the two interior lines of Definition B.3.1.1, for `-1 ≤ σ < 0`.
By the functional equation it reduces to the dual character on the line `1 - σ`. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_left (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (σ : ℝ) (hσ : -1 ≤ σ) (hσ0 : σ < 0) :
    Continuous (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) ∧
      ∃ γ > (0 : ℝ), (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[comap abs atTop]
        (fun y : ℝ ↦ |y| ^ γ) := by
  obtain ⟨Ldual, hLdual, hDualAgree⟩ := completedHeckeL_exists_continuation χ⁻¹
  obtain ⟨fArch, fArchDual, c, hc, hFourier, hArch, hArchDual⟩ :=
    exists_archimedeanHeckeTest_fourier χ
  obtain ⟨f, a, b, q, ha, hb, hq, hf, hFourierIntegral⟩ :=
    exists_globalHeckeTest_fourier χ fArch fArchDual c hc hFourier
  let B (s : ℂ) := b * (q : ℂ) ^ s
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hB : Differentiable ℂ B :=
    (differentiable_id.const_cpow (Or.inl hq₀)).const_mul b
  have hB₀ (s : ℂ) : B s ≠ 0 :=
    mul_ne_zero hb (fun hz ↦ hq₀ ((Complex.cpow_eq_zero_iff _ _).mp hz).1)
  have hZ := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral f χ L (fun _ ↦ a)
    hL hAgree (differentiable_const a) (fun _ ↦ ha) (fun s ↦ by
      rw [hf s, hArch s]
      rfl)
  have hZdual := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral
    (adeleSchwartzFourier f) χ⁻¹ Ldual B hLdual hDualAgree hB hB₀ (fun s ↦ by
      rw [hFourierIntegral s, hArchDual s]
      rfl)
  have hFE (s : ℂ) : L s = (a⁻¹ * B (1 - s)) * Ldual (1 - s) := by
    have hEq := globalIdelicZFunction_functionalEquation f (ideleClassNormTwist χ s)
    rw [dualQuasiCharacter_ideleClassNormTwist, hZ s, hZdual (1 - s)] at hEq
    calc
      L s = a⁻¹ * (a * L s) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      _ = a⁻¹ * (B (1 - s) * Ldual (1 - s)) := by rw [hEq]
      _ = (a⁻¹ * B (1 - s)) * Ldual (1 - s) := by ring
  let E (s : ℂ) : ℂ := a⁻¹ * B (1 - s)
  have hE₀ (s : ℂ) : E s ≠ 0 := mul_ne_zero (inv_ne_zero ha) (hB₀ (1 - s))
  have hEderiv (s : ℂ) : HasDerivAt E (E s * (-Complex.log (q : ℂ))) s := by
    have hsub : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) s :=
      (hasDerivAt_id s).const_sub (1 : ℂ)
    have hpow : HasDerivAt (fun z : ℂ ↦ (q : ℂ) ^ (1 - z))
        ((q : ℂ) ^ (1 - s) * Complex.log (q : ℂ) * (-1)) s :=
      HasDerivAt.const_cpow (c := (q : ℂ)) hsub (Or.inl hq₀)
    have hmul := (hpow.const_mul b).const_mul a⁻¹
    refine hmul.congr_deriv ?_
    dsimp only [E, B]
    ring
  have hlogE (s : ℂ) : logDeriv E s = -Complex.log (q : ℂ) := by
    rw [logDeriv_apply, (hEderiv s).deriv, mul_div_cancel_left₀ _ (hE₀ s)]
  have hDualAnalytic : ∀ w : ℂ, 1 < w.re → AnalyticAt ℂ Ldual w := by
    intro w hw
    by_cases hχ : (χ⁻¹).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ht, -⟩ :=
        completedHeckeL_continuation_simplePoles χ⁻¹ Ldual hLdual hDualAgree hχ
      rcases ht with ⟨-, -, -, han⟩
      refine han _ ?_
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
      · have hre : w.re = 0 := by simp [he, Complex.mul_re]
        linarith
      · have hre : w.re = 1 := by simp [he, Complex.mul_re]
        linarith
    · exact (completedHeckeL_continuation_entire χ⁻¹ Ldual hLdual hDualAgree hχ).analyticAt w
  have hDualNeZero : ∀ w : ℂ, 1 < w.re → Ldual w ≠ 0 := by
    intro w hw
    let w' : halfPlane := ⟨w, hw⟩
    rw [show Ldual w = completedHeckeL χ⁻¹ w' from hDualAgree w', completedHeckeL]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ⁻¹ (zero_lt_one.trans hw))
      (finiteHeckeL_ne_zero_of_one_lt_re χ⁻¹ w')
  have hLogDeriv_eq : ∀ s : ℂ, s.re < 0 →
      logDeriv L s = -Complex.log (q : ℂ) - logDeriv Ldual (1 - s) := by
    intro s hs
    have h1s : 1 < (1 - s).re := by simp [Complex.sub_re]; linarith
    have han := hDualAnalytic (1 - s) h1s
    have hne := hDualNeZero (1 - s) h1s
    have hsub : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) s :=
      (hasDerivAt_id s).const_sub (1 : ℂ)
    have hcomp : HasDerivAt (fun z : ℂ ↦ Ldual (1 - z)) (deriv Ldual (1 - s) * (-1)) s :=
      han.differentiableAt.hasDerivAt.comp s hsub
    have hLfun : L = fun z : ℂ ↦ E z * Ldual (1 - z) := funext hFE
    rw [hLfun, logDeriv_fun_mul (f := E) (g := fun z : ℂ ↦ Ldual (1 - z)) s
      (hE₀ s) hne (hEderiv s).differentiableAt hcomp.differentiableAt,
      hlogE s, logDeriv_apply, logDeriv_apply, hcomp.deriv]
    ring
  have hLine_eq (y : ℝ) :
      logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I) =
        -Complex.log (q : ℂ) - logDeriv Ldual (((1 - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
    have hs : ((σ : ℂ) + (y : ℂ) * Complex.I).re < 0 := by
      simpa [Complex.add_re, Complex.mul_re] using hσ0
    rw [hLogDeriv_eq _ hs]
    congr 2
    push_cast
    ring
  obtain ⟨hContR, γ, hγ, hBigOR⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right
    χ⁻¹ Ldual hLdual hDualAgree (1 - σ) (by linarith) (by linarith)
  refine ⟨?_, γ, hγ, ?_⟩
  · simp_rw [hLine_eq]
    exact continuous_const.sub (hContR.comp continuous_neg)
  · simp_rw [hLine_eq]
    have htend : Tendsto (fun y : ℝ ↦ -y) (comap abs atTop) (comap abs atTop) :=
      Filter.tendsto_comap_iff.mpr <|
        Filter.tendsto_comap.congr fun y ↦ (abs_neg y).symm
    have h1 : (fun y : ℝ ↦ logDeriv Ldual (((1 - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I))
        =O[comap abs atTop] (fun y : ℝ ↦ |y| ^ γ) := by
      simpa only [Function.comp_def, abs_neg] using hBigOR.comp_tendsto htend
    have hconst : (fun _ : ℝ ↦ -Complex.log (q : ℂ)) =O[comap abs atTop] (fun y : ℝ ↦ |y| ^ γ) := by
      refine Asymptotics.IsBigO.of_bound ‖Complex.log (q : ℂ)‖ ?_
      filter_upwards [(atTop_basis.comap (abs : ℝ → ℝ)).eventually_iff.mpr ⟨1, trivial, fun y hy ↦ hy⟩]
        with y hy
      simp only [mem_preimage, mem_Ici] at hy
      rw [norm_neg, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
      exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow hy hγ.le)
    exact hconst.sub h1

/-- Paper: §B.4.2.1, p. 614. The logarithmic derivative of the completed
function has slow growth near its poles on the strip used for the residue formula.
Deviation: Uses the repaired height bounds of Definition B.3.1.1. -/
theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv (χ : U[F]) (L : ℂ → ℂ)
    (_hL : MeromorphicNFOn L univ) (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (_ha : 1 < a) (_haMax : a ≤ 2) :
    HasSlowGrowthNearPoles (logDeriv L) (1 - a) a := by
  obtain ⟨T, hT, A, β, hA, hβ, hgood⟩ :=
    hasSlowGrowthNearPoles_completedHeckeL_logDeriv_heights χ L _hL _hAgree a _ha _haMax
  refine hasSlowGrowthNearPoles_completedHeckeL_logDeriv_assemble (by linarith)
    ((_hL.meromorphicOn.logDeriv).mono_set (subset_univ _)) T hT A β hA hβ hgood
    ⟨(a - 1) / 3, (a - 1) / 2, by linarith, by linarith, by linarith, ?_⟩
  intro σ hσ
  rcases hσ with rfl | rfl
  · exact hasSlowGrowthNearPoles_completedHeckeL_logDeriv_left χ L _hL _hAgree _
      (by linarith) (by linarith)
  · exact hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right χ L _hL _hAgree _
      (by linarith) (by linarith)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the continuation has order zero to the
right of `Re s = 1`: no poles there by Proposition 3.2.1.3(1)–(2), no zeros by (4). -/
private theorem hasSum_heckeAsymptoticResidue_order_right (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) (hρ : 1 < ρ.re) : meromorphicOrderAt L ρ = 0 := by
  have hnonneg : 0 ≤ meromorphicOrderAt L ρ := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨-, -, -, han⟩, -⟩ :=
        completedHeckeL_continuation_simplePoles χ L hL hAgree hχ
      refine (han ρ ?_).meromorphicOrderAt_nonneg
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
    · exact ((completedHeckeL_continuation_entire χ L hL hAgree hχ).analyticAt
        ρ).meromorphicOrderAt_nonneg
  refine le_antisymm ?_ hnonneg
  by_contra! hpos
  exact absurd (completedHeckeL_continuation_zeros χ L hL hAgree (by linarith) hpos)
    (by linarith)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the continuation has order zero to the
left of `Re s = 0`, by the functional equation and the previous lemma for the dual. -/
private theorem hasSum_heckeAsymptoticResidue_order_left (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) (hρ : ρ.re < 0) : meromorphicOrderAt L ρ = 0 := by
  obtain ⟨Ldual, hLdual, hDualAgree⟩ := completedHeckeL_exists_continuation χ⁻¹
  obtain ⟨ε, -, -, hFE⟩ :=
    completedHeckeL_continuation_functionalEquation χ L Ldual hL hAgree hLdual hDualAgree
  have hdual : meromorphicOrderAt Ldual (1 - ρ) = 0 :=
    hasSum_heckeAsymptoticResidue_order_right χ⁻¹ Ldual hLdual hDualAgree (1 - ρ)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hne : Ldual (1 - ρ) ≠ 0 :=
    (hLdual (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp hdual
  rw [hFE ρ] at hne
  exact (hL (mem_univ ρ)).meromorphicOrderAt_eq_zero_iff.mpr (right_ne_zero_of_mul hne)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the continuation is not identically zero. -/
private theorem hasSum_heckeAsymptoticResidue_order_ne_top (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) : meromorphicOrderAt L ρ ≠ ⊤ := by
  intro htop
  have h2 := hL.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ ρ) (mem_univ (2 : ℂ)) htop
  rw [hasSum_heckeAsymptoticResidue_order_right χ L hL hAgree 2 (by norm_num)] at h2
  exact WithTop.zero_ne_top h2

/-- Helper for `hasSum_heckeAsymptoticResidue`: zeros and poles lie in the closed strip
`0 ≤ Re s ≤ 1`. -/
private theorem hasSum_heckeAsymptoticResidue_re_mem (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) (hρ : meromorphicOrderAt L ρ ≠ 0) : ρ.re ∈ Icc 0 1 := by
  by_contra h
  simp only [mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · exact hρ (hasSum_heckeAsymptoticResidue_order_left χ L hL hAgree ρ h)
  · exact hρ (hasSum_heckeAsymptoticResidue_order_right χ L hL hAgree ρ h)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the logarithmic derivative has a pole
exactly at the zeros and poles of the continuation. -/
private theorem hasSum_heckeAsymptoticResidue_logDeriv_order_neg_iff (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) : meromorphicOrderAt (logDeriv L) ρ < 0 ↔ meromorphicOrderAt L ρ ≠ 0 := by
  constructor
  · intro h h0
    exact absurd (meromorphicOrderAt_logDeriv_nonneg (hL (mem_univ ρ)).meromorphicAt h0)
      (not_le.mpr h)
  · intro h
    rw [meromorphicOrderAt_logDeriv_eq_neg_one h
      (hasSum_heckeAsymptoticResidue_order_ne_top χ L hL hAgree ρ)]
    exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- Helper for `hasSum_heckeAsymptoticResidue`: poles are simple and at most two. -/
private theorem hasSum_heckeAsymptoticResidue_poles (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    ∃ P : Finset ℂ, P.card ≤ 2 ∧
      ∀ ρ, meromorphicOrderAt L ρ < 0 → ρ ∈ P ∧ meromorphicOrderAt L ρ = -1 := by
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨-, h0, h1, han⟩, -⟩ :=
      completedHeckeL_continuation_simplePoles χ L hL hAgree hχ
    refine ⟨{Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}, Finset.card_le_two, fun ρ hρ ↦ ?_⟩
    by_cases hmem : ρ ∈ ({Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)} : Set ℂ)
    · refine ⟨by simpa using hmem, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl
      · exact h0
      · exact h1
    · exact absurd (han ρ hmem).meromorphicOrderAt_nonneg (not_le.mpr hρ)
  · refine ⟨∅, by simp, fun ρ hρ ↦ ?_⟩
    exact absurd ((completedHeckeL_continuation_entire χ L hL hAgree hχ).analyticAt
      ρ).meromorphicOrderAt_nonneg (not_le.mpr hρ)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the absolute orders exceed the signed
orders by at most `4` on every finite set, since the poles are simple and at most two. -/
private theorem hasSum_heckeAsymptoticResidue_abs_sum_le (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (s : Finset ℂ) :
    (∑ ρ ∈ s, (|(meromorphicOrderAt L ρ).untop₀| : ℝ)) ≤
      (∑ ρ ∈ s, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + 4 := by
  obtain ⟨P, hP, hpole⟩ := hasSum_heckeAsymptoticResidue_poles χ L hL hAgree
  have key : ∀ ρ, (|(meromorphicOrderAt L ρ).untop₀| : ℝ) ≤
      ((meromorphicOrderAt L ρ).untop₀ : ℝ) + if ρ ∈ P then 2 else 0 := by
    intro ρ
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (hasSum_heckeAsymptoticResidue_order_ne_top χ L hL hAgree ρ)
    by_cases hneg : meromorphicOrderAt L ρ < 0
    · obtain ⟨hmem, hord⟩ := hpole ρ hneg
      rw [hord, ite_eq_left hmem]
      norm_num
    · have h0 : 0 ≤ n := by
        rw [← hn] at hneg
        exact_mod_cast not_lt.mp hneg
      rw [← hn, WithTop.untop₀_coe]
      have : (0 : ℝ) ≤ if ρ ∈ P then 2 else 0 := by split_ifs <;> norm_num
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      linarith
  calc (∑ ρ ∈ s, (|(meromorphicOrderAt L ρ).untop₀| : ℝ))
      ≤ ∑ ρ ∈ s, (((meromorphicOrderAt L ρ).untop₀ : ℝ) + if ρ ∈ P then 2 else 0) :=
        Finset.sum_le_sum fun ρ _ ↦ key ρ
    _ = (∑ ρ ∈ s, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + ∑ ρ ∈ s ∩ P, (2 : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
    _ ≤ (∑ ρ ∈ s, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : ((s ∩ P).card : ℝ) ≤ 2 := by
          exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans hP
        linarith

/-- Helper for `hasSum_heckeAsymptoticResidue`: the circle residue depends only on the germ
on a punctured neighbourhood. -/
private theorem hasSum_heckeAsymptoticResidue_residue_congr {f g : ℂ → ℂ} {ρ : ℂ}
    (h : f =ᶠ[𝓝[≠] ρ] g) : complexResidue f ρ = complexResidue g ρ := by
  obtain ⟨R, hR, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h
  unfold complexResidue Filter.limUnder
  apply congrArg Filter.lim
  apply Filter.map_congr
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  congr 1
  apply circleIntegral.integral_congr hr.1.le
  intro z hz
  have hdist := Metric.mem_sphere.mp hz
  refine hEq ⟨Metric.mem_ball.mpr (hdist.trans_lt hr.2), mem_compl_singleton_iff.mpr ?_⟩
  rintro rfl
  exact hr.1.ne (by simpa using hdist)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the residue of `Φ · L'/L` at a point is the
order of `L` there times `Φ`. -/
private theorem hasSum_heckeAsymptoticResidue_residue (Φ L : ℂ → ℂ) (ρ : ℂ)
    (hΦ : AnalyticAt ℂ Φ ρ) (hL : MeromorphicAt L ρ) (hne : meromorphicOrderAt L ρ ≠ ⊤) :
    complexResidue (fun z ↦ Φ z * logDeriv L z) ρ =
      ((meromorphicOrderAt L ρ).untop₀ : ℂ) * Φ ρ := by
  obtain ⟨g, hg, hgρ, hLg⟩ := (meromorphicOrderAt_ne_top_iff hL).mp hne
  set n : ℤ := (meromorphicOrderAt L ρ).untop₀ with hn
  have hgne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hgρ
  have hlog : ∀ᶠ z in 𝓝[≠] ρ, logDeriv L z = (n : ℂ) / (z - ρ) + logDeriv g z := by
    filter_upwards [logDeriv_congr_nhdsNE hLg, hgne.filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hgz hgan hzρ
    have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    simp only [smul_eq_mul] at hz
    rw [hz]
    have hpow : logDeriv (fun w : ℂ ↦ (w - ρ) ^ n) z = (n : ℂ) / (z - ρ) := by
      have hcomp := logDeriv_comp (f := fun w : ℂ ↦ w ^ n) (g := fun w : ℂ ↦ w - ρ) (x := z)
        (differentiableAt_zpow.mpr (Or.inl hzρ')) (differentiableAt_id.sub_const ρ)
      simp only [Function.comp_def] at hcomp
      rw [hcomp, logDeriv_zpow, deriv_sub_const, deriv_id'', mul_one]
    rw [← hpow]
    exact logDeriv_fun_mul z (zpow_ne_zero n hzρ') hgz
      ((differentiableAt_id.sub_const ρ).zpow (Or.inl hzρ')) hgan.differentiableAt
  have hH : (fun z ↦ Φ z * logDeriv L z) =ᶠ[𝓝[≠] ρ]
      fun z ↦ (Φ z * ((n : ℂ) + (z - ρ) * logDeriv g z)) / (z - ρ) := by
    filter_upwards [hlog, self_mem_nhdsWithin] with z hz hzρ
    have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    rw [hz]
    field_simp
  rw [hasSum_heckeAsymptoticResidue_residue_congr hH,
    complexResidue_div_sub (g := fun z ↦ Φ z * ((n : ℂ) + (z - ρ) * logDeriv g z)) ?_]
  · simp [mul_comm]
  · exact hΦ.mul (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul
      (hg.deriv.div hg hgρ)))

/-- Helper for `hasSum_heckeAsymptoticResidue`: the rectangle identity for `Φ · L'/L` on
`[1 - a, a] × [t₁, t₂]` when `L'/L` is analytic on the two horizontal edges. -/
private theorem hasSum_heckeAsymptoticResidue_rectangle (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (ha : 1 < a) (Φ : ℂ → ℂ) (hΦ : Differentiable ℂ Φ) (t₁ t₂ : ℝ) (ht : t₁ < t₂)
    (hAn : ∀ σ ∈ Icc (1 - a) a, AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t₁ : ℂ) * Complex.I) ∧
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t₂ : ℂ) * Complex.I))
    (S : Finset ℂ) (hS : ∀ ρ, ρ ∈ S ↔ ρ.re ∈ Ioo (1 - a) a ∧ ρ.im ∈ Ioo t₁ t₂ ∧
      meromorphicOrderAt L ρ ≠ 0) :
    (∫ x in (1 - a)..a, Φ ((x : ℂ) + (t₁ : ℂ) * Complex.I) *
        logDeriv L ((x : ℂ) + (t₁ : ℂ) * Complex.I)) -
      (∫ x in (1 - a)..a, Φ ((x : ℂ) + (t₂ : ℂ) * Complex.I) *
        logDeriv L ((x : ℂ) + (t₂ : ℂ) * Complex.I)) +
      Complex.I * (∫ y in t₁..t₂, Φ ((a : ℂ) + (y : ℂ) * Complex.I) *
        logDeriv L ((a : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in t₁..t₂, Φ (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
        logDeriv L (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      twoPiI * ∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * Φ ρ := by
  have hmer : MeromorphicOn (fun z ↦ Φ z * logDeriv L z) (Icc (1 - a) a ×ℂ Icc t₁ t₂) :=
    fun z _ ↦ (hΦ.analyticAt z).meromorphicAt.mul (hL.meromorphicOn.logDeriv z (mem_univ z))
  have hne (ρ : ℂ) := hasSum_heckeAsymptoticResidue_order_ne_top χ L hL hAgree ρ
  refine (rectangleIntegral_eq_sum_complexResidue (g := fun z ↦ Φ z * logDeriv L z)
    (by linarith) ht S hmer ?_ ?_).trans ?_
  · intro ρ hρ
    obtain ⟨h1, h2, -⟩ := (hS ρ).mp hρ
    exact Complex.mem_reProdIm.mpr ⟨h1, h2⟩
  · intro ρ hρ hρS
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hρ
    have hΦρ : 0 ≤ meromorphicOrderAt Φ ρ := (hΦ.analyticAt ρ).meromorphicOrderAt_nonneg
    rw [show (fun z ↦ Φ z * logDeriv L z) = Φ * logDeriv L from rfl,
      meromorphicOrderAt_mul (hΦ.analyticAt ρ).meromorphicAt
        (hL.meromorphicOn.logDeriv ρ (mem_univ ρ))]
    refine add_nonneg hΦρ ?_
    by_cases h0 : meromorphicOrderAt L ρ = 0
    · exact meromorphicOrderAt_logDeriv_nonneg (hL (mem_univ ρ)).meromorphicAt h0
    have hre' : ρ.re ∈ Ioo (1 - a) a := by
      rcases hre.1.eq_or_lt with h | h
      · exact absurd (hasSum_heckeAsymptoticResidue_order_left χ L hL hAgree ρ
          (by rw [← h]; linarith)) h0
      rcases hre.2.eq_or_lt with h' | h'
      · exact absurd (hasSum_heckeAsymptoticResidue_order_right χ L hL hAgree ρ
          (by rw [h']; exact ha)) h0
      exact ⟨h, h'⟩
    have him' : ρ.im = t₁ ∨ ρ.im = t₂ := by
      by_contra hcon
      exact hρS ((hS ρ).mpr ⟨hre', ⟨lt_of_le_of_ne him.1 fun h ↦ hcon (Or.inl h.symm),
        lt_of_le_of_ne him.2 fun h ↦ hcon (Or.inr h)⟩, h0⟩)
    have hIcc : ρ.re ∈ Icc (1 - a) a := ⟨hre'.1.le, hre'.2.le⟩
    rcases him' with h | h
    · have := (hAn ρ.re hIcc).1.meromorphicOrderAt_nonneg
      rwa [← h, Complex.re_add_im] at this
    · have := (hAn ρ.re hIcc).2.meromorphicOrderAt_nonneg
      rwa [← h, Complex.re_add_im] at this
  · congr 1
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    exact hasSum_heckeAsymptoticResidue_residue Φ L ρ (hΦ.analyticAt ρ)
      (hL (mem_univ ρ)).meromorphicAt (hne ρ)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the signed divisor sum over the open rectangle
`(1 - a, a) × (t₁, t₂)` is bounded by the boundary integrals of `L'/L` (argument principle). -/
private theorem hasSum_heckeAsymptoticResidue_count (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (ha : 1 < a) (t₁ t₂ : ℝ) (ht : t₁ < t₂) (M M' : ℝ)
    (hAn : ∀ σ ∈ Icc (1 - a) a, ∀ t ∈ ({t₁, t₂} : Set ℝ),
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t : ℂ) * Complex.I) ∧
        ‖logDeriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M)
    (hVert : ∀ σ ∈ ({1 - a, a} : Set ℝ), ∀ y ∈ Icc t₁ t₂,
      ‖logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M')
    (S : Finset ℂ) (hS : ∀ ρ, ρ ∈ S ↔ ρ.re ∈ Ioo (1 - a) a ∧ ρ.im ∈ Ioo t₁ t₂ ∧
      meromorphicOrderAt L ρ ≠ 0) :
    (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) ≤
      (2 * (2 * a - 1) * M + 2 * (t₂ - t₁) * M') / (2 * Real.pi) := by
  have hrect := hasSum_heckeAsymptoticResidue_rectangle χ L hL hAgree a ha (fun _ ↦ 1)
    (differentiable_const 1) t₁ t₂ ht
    (fun σ hσ ↦ ⟨(hAn σ hσ t₁ (by simp)).1, (hAn σ hσ t₂ (by simp)).1⟩) S hS
  simp only [one_mul, mul_one] at hrect
  have hIcc : Set.uIoc (1 - a) a ⊆ Icc (1 - a) a := by
    rw [uIoc_of_le (by linarith)]; exact Ioc_subset_Icc_self
  have hIcc' : Set.uIoc t₁ t₂ ⊆ Icc t₁ t₂ := by
    rw [uIoc_of_le ht.le]; exact Ioc_subset_Icc_self
  have hh (t : ℝ) (htt : t ∈ ({t₁, t₂} : Set ℝ)) :
      ‖∫ x in (1 - a)..a, logDeriv L ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (2 * a - 1) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ ↦ logDeriv L ((x : ℂ) + (t : ℂ) * Complex.I)) (a := 1 - a) (b := a)
      (C := M) (fun x hx ↦ (hAn x (hIcc hx) t htt).2)
    rwa [show |a - (1 - a)| = 2 * a - 1 by rw [abs_of_pos (by linarith)]; ring] at this
  have hv (σ : ℝ) (hσ : σ ∈ ({1 - a, a} : Set ℝ)) :
      ‖∫ y in t₁..t₂, logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M' * (t₂ - t₁) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) (a := t₁) (b := t₂)
      (C := M') (fun y hy ↦ hVert σ hσ y (hIcc' hy))
    rwa [abs_of_pos (by linarith)] at this
  have hnorm : ‖twoPiI * ∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ ≤
      2 * (2 * a - 1) * M + 2 * (t₂ - t₁) * M' := by
    rw [← hrect]
    calc _ ≤ ‖∫ x in (1 - a)..a, logDeriv L ((x : ℂ) + (t₁ : ℂ) * Complex.I)‖ +
          ‖∫ x in (1 - a)..a, logDeriv L ((x : ℂ) + (t₂ : ℂ) * Complex.I)‖ +
          ‖Complex.I * ∫ y in t₁..t₂, logDeriv L ((a : ℂ) + (y : ℂ) * Complex.I)‖ +
          ‖Complex.I * ∫ y in t₁..t₂,
            logDeriv L (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ M * (2 * a - 1) + M * (2 * a - 1) + M' * (t₂ - t₁) + M' * (t₂ - t₁) := by
          gcongr
          · exact hh t₁ (by simp)
          · exact hh t₂ (by simp)
          · rw [norm_mul, Complex.norm_I, one_mul]; exact hv a (by simp)
          · rw [norm_mul, Complex.norm_I, one_mul]; exact hv (1 - a) (by simp)
      _ = _ := by ring
  have h2pi : ‖twoPiI‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [norm_mul, h2pi] at hnorm
  have hcast : (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) ≤
      ‖∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ := by
    have h1 : (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) =
        (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)).re := by
      simp [Complex.re_sum]
    rw [h1]
    exact Complex.re_le_norm _
  rw [le_div_iff₀ (by positivity)]
  calc (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) * (2 * Real.pi)
      ≤ ‖∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ * (2 * Real.pi) := by gcongr
    _ = 2 * Real.pi * ‖∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ := mul_comm _ _
    _ ≤ _ := hnorm

/-- Helper for `hasSum_heckeAsymptoticResidue`: a continuous trace with polynomial growth at
infinity is polynomially bounded everywhere. -/
private theorem hasSum_heckeAsymptoticResidue_trace_bound (g : ℝ → ℂ) (hcont : Continuous g)
    (γ : ℝ) (hγ : 0 < γ) (hO : g =O[comap abs atTop] fun y : ℝ ↦ |y| ^ γ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, ‖g y‖ ≤ D * (1 + |y|) ^ γ := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hO
  rw [Filter.eventually_comap] at hc
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -y₀) (b := y₀)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M₀ 0 + max c 0, by positivity, fun y ↦ ?_⟩
  have h1 : (1 : ℝ) ≤ (1 + |y|) ^ γ := Real.one_le_rpow (by linarith [abs_nonneg y]) hγ.le
  have h2 : |y| ^ γ ≤ (1 + |y|) ^ γ := Real.rpow_le_rpow (abs_nonneg y) (by linarith) hγ.le
  by_cases hy : y₀ ≤ |y|
  · have := hy₀ |y| hy y rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) γ)] at this
    calc ‖g y‖ ≤ c * |y| ^ γ := this
      _ ≤ max c 0 * (1 + |y|) ^ γ :=
          mul_le_mul (le_max_left _ _) h2 (by positivity) (le_max_right _ _)
      _ ≤ (max M₀ 0 + max c 0) * (1 + |y|) ^ γ := by
          gcongr; linarith [le_max_right M₀ 0]
  · have hmem : y ∈ Icc (-y₀) y₀ := abs_le.mp (not_le.mp hy).le
    calc ‖g y‖ ≤ M₀ := hM₀ y hmem
      _ ≤ max M₀ 0 * (1 + |y|) ^ γ :=
          (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) h1)
      _ ≤ (max M₀ 0 + max c 0) * (1 + |y|) ^ γ := by
          gcongr; linarith [le_max_right c 0]

/-- Helper for `hasSum_heckeAsymptoticResidue`: a polynomial bound on the absolute orders in
height windows and rapid decay of the test give absolute summability of the divisor sum. -/
private theorem hasSum_heckeAsymptoticResidue_summable_of_count (n : ℂ → ℤ) (Φ : ℂ → ℂ)
    (B C c : ℝ) (hc : 1 ≤ c) (m N : ℕ) (hN : m + 2 ≤ N)
    (hΦ : ∀ ρ, n ρ ≠ 0 → ‖Φ ρ‖ ≤ C / (1 + |ρ.im|) ^ N)
    (hcount : ∀ k : ℕ, ∀ s : Finset ℂ, (∀ ρ ∈ s, n ρ ≠ 0 ∧ |ρ.im| ≤ k) →
      (∑ ρ ∈ s, (|n ρ| : ℝ)) ≤ B * ((k : ℝ) + c) ^ m) :
    Summable (fun ρ : ℂ ↦ (n ρ : ℂ) * Φ ρ) := by
  have hB : 0 ≤ B := by
    have := hcount 0 ∅ (by simp)
    simp only [Finset.sum_empty, Nat.cast_zero, zero_add] at this
    exact (mul_nonneg_iff_of_pos_right (pow_pos (by linarith) m)).mp this
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hΦ' : ∀ ρ, n ρ ≠ 0 → ‖Φ ρ‖ ≤ C' / (1 + |ρ.im|) ^ N := fun ρ h ↦
    (hΦ ρ h).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsum2 : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  set K : ℝ := B * (C' * 2 ^ N * c ^ m) with hK
  have hK0 : 0 ≤ K := by positivity
  rw [← summable_norm_iff]
  refine summable_of_sum_le (fun ρ ↦ norm_nonneg _)
    (c := K * ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2) fun s ↦ ?_
  set s' := s.filter (fun ρ ↦ n ρ ≠ 0) with hs'
  have hss' : ∑ ρ ∈ s, ‖(n ρ : ℂ) * Φ ρ‖ = ∑ ρ ∈ s', ‖(n ρ : ℂ) * Φ ρ‖ := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    split_ifs with h
    · rfl
    · simp [not_not.mp h]
  rw [hss']
  set κ : ℂ → ℕ := fun ρ ↦ ⌈|ρ.im|⌉₊ with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (t := s'.image κ) (g := κ)
    (fun ρ hρ ↦ Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ j ∈ s'.image κ, (∑ ρ ∈ s' with κ ρ = j, ‖(n ρ : ℂ) * Φ ρ‖) ≤
      K * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j _
    have hmem : ∀ ρ ∈ s'.filter (fun ρ ↦ κ ρ = j), n ρ ≠ 0 ∧ |ρ.im| ≤ j := by
      intro ρ hρ
      obtain ⟨hρs, hρj⟩ := Finset.mem_filter.mp hρ
      refine ⟨(Finset.mem_filter.mp hρs).2, ?_⟩
      rw [← hρj]
      exact Nat.le_ceil _
    have hΦj : ∀ ρ ∈ s'.filter (fun ρ ↦ κ ρ = j), ‖Φ ρ‖ ≤ C' * 2 ^ N / ((j : ℝ) + 1) ^ N := by
      intro ρ hρ
      obtain ⟨hn, -⟩ := hmem ρ hρ
      have hj : (j : ℝ) < |ρ.im| + 1 := by
        rw [← (Finset.mem_filter.mp hρ).2]
        exact Nat.ceil_lt_add_one (abs_nonneg _)
      have hle : (j : ℝ) + 1 ≤ 2 * (1 + |ρ.im|) := by linarith [abs_nonneg ρ.im]
      calc ‖Φ ρ‖ ≤ C' / (1 + |ρ.im|) ^ N := hΦ' ρ hn
        _ = C' * 2 ^ N / (2 * (1 + |ρ.im|)) ^ N := by
          rw [mul_pow]
          field_simp
        _ ≤ C' * 2 ^ N / ((j : ℝ) + 1) ^ N := by gcongr
    calc (∑ ρ ∈ s' with κ ρ = j, ‖(n ρ : ℂ) * Φ ρ‖)
        ≤ ∑ ρ ∈ s' with κ ρ = j, (|n ρ| : ℝ) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
          refine Finset.sum_le_sum fun ρ hρ ↦ ?_
          rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul_of_nonneg_left (hΦj ρ hρ) (abs_nonneg _)
      _ = (∑ ρ ∈ s' with κ ρ = j, (|n ρ| : ℝ)) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
          rw [Finset.sum_mul]
      _ ≤ (B * ((j : ℝ) + c) ^ m) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
          gcongr
          exact hcount j _ hmem
      _ ≤ K * (1 / ((j : ℝ) + 1) ^ 2) := by
          have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [j.cast_nonneg (α := ℝ)]
          have h1 : ((j : ℝ) + c) ^ m ≤ c ^ m * ((j : ℝ) + 1) ^ m := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) (by nlinarith [j.cast_nonneg (α := ℝ)]) m
          have h2 : ((j : ℝ) + 1) ^ m * ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ N := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hj1 hN
          have hpos : 0 < ((j : ℝ) + 1) ^ N := by positivity
          have hpos2 : 0 < ((j : ℝ) + 1) ^ 2 := by positivity
          have h3 : ((j : ℝ) + 1) ^ m / ((j : ℝ) + 1) ^ N ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
            rw [div_le_div_iff₀ hpos hpos2, one_mul]
            exact h2
          calc B * ((j : ℝ) + c) ^ m * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N)
              ≤ B * (c ^ m * ((j : ℝ) + 1) ^ m) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
                gcongr
            _ = K * (((j : ℝ) + 1) ^ m / ((j : ℝ) + 1) ^ N) := by rw [hK]; ring
            _ ≤ K * (1 / ((j : ℝ) + 1) ^ 2) := by gcongr
  calc (∑ j ∈ s'.image κ, ∑ ρ ∈ s' with κ ρ = j, ‖(n ρ : ℂ) * Φ ρ‖)
      ≤ ∑ j ∈ s'.image κ, K * (1 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum hfiber
    _ = K * ∑ j ∈ s'.image κ, 1 / ((j : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ K * ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2 := by
        gcongr
        exact hsum2.sum_le_tsum _ (fun j _ ↦ by positivity)

/-- Paper: Equation (B.4.2.2), p. 614. The right vertical integral minus the
left vertical integral is the signed divisor sum of Mellin values.
Deviation: The meromorphic order includes the actual poles and zero multiplicities.
The unordered sum strengthens the rectangular limit and uses zero counting for fixed χ. -/
theorem hasSum_heckeAsymptoticResidue (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (_ha : 1 < a) (_haMax : a ≤ 2) :
    let H := fun s ↦ logMellin f s * logDeriv L s
    Complex.VerticalIntegrable H a ∧ Complex.VerticalIntegrable H (1 - a) ∧
      HasSum (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f ρ)
        ((verticalLineIntegral H a - verticalLineIntegral H (1 - a)) / twoPiI) := by
  intro H
  have hΦd : Differentiable ℂ (logMellin f) := differentiable_mellin_of_exponentialDecay f _hf
  obtain ⟨hcontR, γR, hγR, hOR⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right χ L _hL _hAgree a _ha _haMax
  obtain ⟨hcontL, γL, hγL, hOL⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_left χ L _hL _hAgree (1 - a) (by linarith) (by linarith)
  have hΦstrip : UniformlySchwartzOnStrip (logMellin f) (1 - a - 1) (a + 1) :=
    uniformlySchwartzOnStrip_mellin_of_exponentialDecay f _hf _ _ (by linarith)
  have hintR : Complex.VerticalIntegrable H a :=
    verticalIntegrable_mul_of_polynomialGrowth hΦstrip ⟨by linarith, by linarith⟩ hcontR
      ⟨γR, hγR, hOR⟩
  have hintL : Complex.VerticalIntegrable H (1 - a) :=
    verticalIntegrable_mul_of_polynomialGrowth hΦstrip ⟨by linarith, by linarith⟩ hcontL
      ⟨γL, hγL, hOL⟩
  refine ⟨hintR, hintL, ?_⟩
  -- Orders and the divisor.
  have hne : ∀ ρ, meromorphicOrderAt L ρ ≠ ⊤ :=
    hasSum_heckeAsymptoticResidue_order_ne_top χ L _hL _hAgree
  have hre : ∀ ρ, meromorphicOrderAt L ρ ≠ 0 → ρ.re ∈ Icc 0 1 :=
    hasSum_heckeAsymptoticResidue_re_mem χ L _hL _hAgree
  have hdiv : ∀ ρ, (MeromorphicOn.divisor L univ ρ : ℂ) =
      ((meromorphicOrderAt L ρ).untop₀ : ℂ) := fun ρ ↦ by
    rw [MeromorphicOn.divisor_apply _hL.meromorphicOn (mem_univ ρ)]
  simp_rw [hdiv]
  -- The selected heights.
  obtain ⟨T, hTmono, A, β, hA, hβ, hgood⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_heights χ L _hL _hAgree a _ha _haMax
  rw [Filter.eventually_comap] at hgood
  obtain ⟨b₀, hb₀⟩ := Filter.eventually_atTop.mp hgood
  obtain ⟨k₁, hk₁b, hk₁2⟩ : ∃ k₁ : ℕ, b₀ ≤ (k₁ : ℤ) ∧ 2 ≤ k₁ :=
    ⟨max b₀.toNat 2, (Int.self_le_toNat b₀).trans (by exact_mod_cast le_max_left _ _),
      le_max_right _ _⟩
  have hgood' : ∀ j : ℤ, (k₁ : ℤ) ≤ |j| → |T j - j| ≤ 1 ∧ ∀ σ ∈ Icc (1 - a) a,
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (T j : ℂ) * Complex.I) ∧
        ‖logDeriv L ((σ : ℂ) + (T j : ℂ) * Complex.I)‖ ≤ A * |T j| ^ β :=
    fun j hj ↦ hb₀ |j| (hk₁b.trans hj) j rfl
  set up : ℕ → ℝ := fun k ↦ T ((k + k₁ : ℕ) : ℤ) with hup
  set lo : ℕ → ℝ := fun k ↦ T (-((k + k₁ : ℕ) : ℤ)) with hlo
  have hupG (k : ℕ) := hgood' ((k + k₁ : ℕ) : ℤ)
    (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast Nat.le_add_left k₁ k)
  have hloG (k : ℕ) := hgood' (-((k + k₁ : ℕ) : ℤ))
    (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact_mod_cast Nat.le_add_left k₁ k)
  have hupB (k : ℕ) : (k : ℝ) + k₁ - 1 ≤ up k ∧ up k ≤ (k : ℝ) + k₁ + 1 := by
    have := abs_le.mp (hupG k).1
    rw [Int.cast_natCast, Nat.cast_add (R := ℝ)] at this
    show (k : ℝ) + k₁ - 1 ≤ T ((k + k₁ : ℕ) : ℤ) ∧ T ((k + k₁ : ℕ) : ℤ) ≤ (k : ℝ) + k₁ + 1
    constructor <;> linarith [this.1, this.2]
  have hloB (k : ℕ) : -((k : ℝ) + k₁) - 1 ≤ lo k ∧ lo k ≤ -((k : ℝ) + k₁) + 1 := by
    have := abs_le.mp (hloG k).1
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_add (R := ℝ)] at this
    show -((k : ℝ) + k₁) - 1 ≤ T (-((k + k₁ : ℕ) : ℤ)) ∧
      T (-((k + k₁ : ℕ) : ℤ)) ≤ -((k : ℝ) + k₁) + 1
    constructor <;> linarith [this.1, this.2]
  have hk₁R : (2 : ℝ) ≤ k₁ := by exact_mod_cast hk₁2
  have hupPos (k : ℕ) : 1 ≤ up k := by linarith [(hupB k).1, k.cast_nonneg (α := ℝ)]
  have hloNeg (k : ℕ) : lo k ≤ -1 := by linarith [(hloB k).2, k.cast_nonneg (α := ℝ)]
  have hlt (k : ℕ) : lo k < up k := by linarith [hupPos k, hloNeg k]
  have hupMono : Monotone up := fun i j hij ↦
    hTmono (by exact_mod_cast Nat.add_le_add_right hij k₁)
  have hloAnti : Antitone lo := fun i j hij ↦
    hTmono (by rw [neg_le_neg_iff]; exact_mod_cast Nat.add_le_add_right hij k₁)
  have hupTop : Tendsto up atTop atTop := by
    refine tendsto_atTop_mono (fun k ↦ (hupB k).1) ?_
    refine (tendsto_atTop_add_const_right atTop ((k₁ : ℝ) - 1)
      (tendsto_natCast_atTop_atTop (R := ℝ))).congr fun k ↦ ?_
    ring
  have hloBot : Tendsto lo atTop atBot := by
    refine tendsto_atBot_mono (fun k ↦ (hloB k).2) ?_
    refine (tendsto_atBot_add_const_right atTop (1 - (k₁ : ℝ))
      (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).congr fun k ↦ ?_
    simp only [Function.comp_apply]
    ring
  -- The finite sets of zeros and poles in the rectangles.
  have hmerStrip : MeromorphicOn (logDeriv L) (Complex.re ⁻¹' Ioo (1 - a - 1) (a + 1)) :=
    (_hL.meromorphicOn.logDeriv).mono_set (subset_univ _)
  let Z : ℕ → Finset ℂ := fun k ↦ (finite_rectanglePoles (f := logDeriv L) (σ₁ := 1 - a)
    (σ₂ := a) (t₁ := lo k) (t₂ := up k) hmerStrip (by linarith) (by linarith)).toFinset
  have hZ : ∀ k ρ, ρ ∈ Z k ↔ ρ.re ∈ Ioo (1 - a) a ∧ ρ.im ∈ Ioo (lo k) (up k) ∧
      meromorphicOrderAt L ρ ≠ 0 := by
    intro k ρ
    simp only [Z, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
      hasSum_heckeAsymptoticResidue_logDeriv_order_neg_iff χ L _hL _hAgree ρ
  have hZmono : Monotone Z := by
    intro i j hij ρ hρ
    obtain ⟨h1, h2, h3⟩ := (hZ i ρ).mp hρ
    exact (hZ j ρ).mpr ⟨h1, ⟨(hloAnti hij).trans_lt h2.1, h2.2.trans_le (hupMono hij)⟩, h3⟩
  -- Polynomial bounds on the edges of the rectangles.
  have hAbs (k : ℕ) (j : ℤ) (hj : j = ((k + k₁ : ℕ) : ℤ) ∨ j = -((k + k₁ : ℕ) : ℤ)) :
      |T j| ≤ (k : ℝ) + k₁ + 1 := by
    rcases hj with rfl | rfl
    · rw [abs_of_pos (by linarith [hupPos k])]
      exact (hupB k).2
    · rw [abs_of_neg (by linarith [hloNeg k])]
      linarith [(hloB k).1]
  have hEdge (k : ℕ) : ∀ σ ∈ Icc (1 - a) a, ∀ t ∈ ({lo k, up k} : Set ℝ),
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t : ℂ) * Complex.I) ∧
        ‖logDeriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * ((k : ℝ) + k₁ + 1) ^ β := by
    intro σ hσ t ht
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · refine ⟨((hloG k).2 σ hσ).1, ((hloG k).2 σ hσ).2.trans ?_⟩
      gcongr
      exact hAbs k _ (Or.inr rfl)
    · refine ⟨((hupG k).2 σ hσ).1, ((hupG k).2 σ hσ).2.trans ?_⟩
      gcongr
      exact hAbs k _ (Or.inl rfl)
  obtain ⟨DR, hDR, hDRb⟩ := hasSum_heckeAsymptoticResidue_trace_bound _ hcontR γR hγR hOR
  obtain ⟨DL, hDL, hDLb⟩ := hasSum_heckeAsymptoticResidue_trace_bound _ hcontL γL hγL hOL
  set D := max DR DL with hD
  set γ := max γR γL with hγ
  have hγ0 : 0 < γ := lt_max_of_lt_left hγR
  have hVert : ∀ σ ∈ ({1 - a, a} : Set ℝ), ∀ y : ℝ,
      ‖logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ D * (1 + |y|) ^ γ := by
    intro σ hσ y
    have h1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
    simp only [mem_insert_iff, mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl
    · exact (hDLb y).trans (mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le h1 (le_max_right _ _)) (by positivity)
        (le_max_of_le_left hDR))
    · exact (hDRb y).trans (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)) (by positivity)
        (le_max_of_le_left hDR))
  -- The counting bound.
  set m₁ : ℕ := ⌈β⌉₊ with hm₁
  set m₂ : ℕ := ⌈γ⌉₊ with hm₂
  set m : ℕ := max m₁ (m₂ + 1) with hm
  set B₀ : ℝ := (6 * A + 4 * D) / (2 * Real.pi) with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hcountZ (k : ℕ) : (∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) ≤
      B₀ * ((k : ℝ) + k₁ + 2) ^ m := by
    set K : ℝ := (k : ℝ) + k₁ + 2 with hK
    have hK1 : (1 : ℝ) ≤ K := by linarith [k.cast_nonneg (α := ℝ)]
    have hVertK : ∀ σ ∈ ({1 - a, a} : Set ℝ), ∀ y ∈ Icc (lo k) (up k),
        ‖logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ D * K ^ γ := by
      intro σ hσ y hy
      refine (hVert σ hσ y).trans ?_
      gcongr
      rw [hK]
      have : |y| ≤ (k : ℝ) + k₁ + 1 := abs_le.mpr ⟨by linarith [(hloB k).1, hy.1],
        by linarith [(hupB k).2, hy.2]⟩
      linarith
    have hcount := hasSum_heckeAsymptoticResidue_count χ L _hL _hAgree a _ha (lo k) (up k)
      (hlt k) _ _ (hEdge k) hVertK (Z k) (hZ k)
    refine hcount.trans ?_
    rw [hB₀, div_mul_eq_mul_div]
    gcongr
    have hβm : ((k : ℝ) + k₁ + 1) ^ β ≤ K ^ m := by
      calc ((k : ℝ) + k₁ + 1) ^ β ≤ K ^ β :=
            Real.rpow_le_rpow (by positivity) (by rw [hK]; linarith) hβ.le
        _ ≤ K ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1
            ((Nat.le_ceil β).trans (by exact_mod_cast le_max_left m₁ (m₂ + 1)))
        _ = K ^ m := Real.rpow_natCast _ _
    have hγm : (up k - lo k) * K ^ γ ≤ 2 * K ^ m := by
      have h1 : up k - lo k ≤ 2 * K := by rw [hK]; linarith [(hupB k).2, (hloB k).1]
      have h2 : K * K ^ γ ≤ K ^ m := by
        calc K * K ^ γ = K ^ ((1 : ℝ) + γ) := by
              rw [Real.rpow_add (by linarith), Real.rpow_one]
          _ ≤ K ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1 (by
              have : γ ≤ m₂ := Nat.le_ceil γ
              have : ((m₂ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast le_max_right m₁ (m₂ + 1)
              push_cast at this
              linarith)
          _ = K ^ m := Real.rpow_natCast _ _
      calc (up k - lo k) * K ^ γ ≤ 2 * K * K ^ γ := by gcongr
        _ = 2 * (K * K ^ γ) := by ring
        _ ≤ 2 * K ^ m := by gcongr
    have ha3 : 2 * a - 1 ≤ 3 := by linarith
    have hKm : 0 ≤ K ^ m := by positivity
    have hAK : 0 ≤ A * K ^ m := by positivity
    have hD0 : 0 ≤ D := le_max_of_le_left hDR
    have h1 : 2 * (2 * a - 1) * (A * ((k : ℝ) + k₁ + 1) ^ β) ≤ 2 * 3 * (A * K ^ m) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hβm hA.le) (by positivity)
        (by norm_num)
    have h2 : 2 * (up k - lo k) * (D * K ^ γ) ≤ 2 * (D * (2 * K ^ m)) := by
      calc 2 * (up k - lo k) * (D * K ^ γ) = 2 * D * ((up k - lo k) * K ^ γ) := by ring
        _ ≤ 2 * D * (2 * K ^ m) := mul_le_mul_of_nonneg_left hγm (by positivity)
        _ = 2 * (D * (2 * K ^ m)) := by ring
    calc 2 * (2 * a - 1) * (A * ((k : ℝ) + k₁ + 1) ^ β) + 2 * (up k - lo k) * (D * K ^ γ)
        ≤ 2 * 3 * (A * K ^ m) + 2 * (D * (2 * K ^ m)) := add_le_add h1 h2
      _ = (6 * A + 4 * D) * K ^ m := by ring
  -- Rapid decay of the Mellin transform on the closed strip.
  set N : ℕ := m + 2 with hN
  obtain ⟨C₁, hC₁, hbound⟩ := mellin_heightBound_of_exponentialDecay f _hf 0 1 zero_lt_one N
    (by omega)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact
    (Icc (0 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn hΦd.continuous.continuousOn
  have hdecay : ∀ ρ, (meromorphicOrderAt L ρ).untop₀ ≠ 0 →
      ‖logMellin f ρ‖ ≤ 2 ^ N * max C₁ M₀ / (1 + |ρ.im|) ^ N := by
    intro ρ hρ
    have hρ' : meromorphicOrderAt L ρ ≠ 0 := by
      intro h; apply hρ; rw [h]; rfl
    have hreρ := hre ρ hρ'
    have hρeq : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
    have hpos : 0 < (1 + |ρ.im|) ^ N := by positivity
    by_cases him : 1 ≤ |ρ.im|
    · have hy : ρ.im ≠ 0 := by
        intro h; rw [h, abs_zero] at him; linarith
      have h1 := hbound ρ.re hreρ ρ.im hy
      simp only [Complex.re_add_im] at h1
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by positivity) hpos]
      have h2 : (1 + |ρ.im|) ^ N ≤ (2 * |ρ.im|) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith) N
      calc C₁ * (1 + |ρ.im|) ^ N ≤ C₁ * (2 * |ρ.im|) ^ N := by gcongr
        _ = 2 ^ N * C₁ * |ρ.im| ^ N := by rw [mul_pow]; ring
        _ ≤ 2 ^ N * max C₁ M₀ * |ρ.im| ^ N := by gcongr; exact le_max_left _ _
    · have hmem : ρ ∈ Icc (0 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1 :=
        Complex.mem_reProdIm.mpr ⟨hreρ, abs_le.mp (not_le.mp him).le⟩
      have h1 := hM₀ ρ hmem
      refine h1.trans ?_
      rw [le_div_iff₀ hpos]
      have h2 : (1 + |ρ.im|) ^ N ≤ 2 ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith [not_le.mp him]) N
      have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans h1
      calc M₀ * (1 + |ρ.im|) ^ N ≤ M₀ * 2 ^ N := by gcongr
        _ ≤ 2 ^ N * max C₁ M₀ := by rw [mul_comm]; gcongr; exact le_max_right _ _
  -- Summability.
  have hsum : Summable (fun ρ : ℂ ↦ ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ) := by
    refine hasSum_heckeAsymptoticResidue_summable_of_count
      (fun ρ ↦ (meromorphicOrderAt L ρ).untop₀) (logMellin f) (B₀ + 4) (2 ^ N * max C₁ M₀)
      ((k₁ : ℝ) + 4) (by linarith) m N le_rfl hdecay ?_
    intro k s hs
    have hsub : s ⊆ Z (k + 2) := by
      intro ρ hρ
      obtain ⟨h0, him⟩ := hs ρ hρ
      have h0' : meromorphicOrderAt L ρ ≠ 0 := by
        intro h; apply h0; rw [h]; rfl
      have hreρ := hre ρ h0'
      refine (hZ (k + 2) ρ).mpr ⟨⟨by linarith [hreρ.1], by linarith [hreρ.2]⟩, ⟨?_, ?_⟩, h0'⟩
      · have := (hloB (k + 2)).2
        push_cast at this
        linarith [abs_le.mp him]
      · have := (hupB (k + 2)).1
        push_cast at this
        linarith [abs_le.mp him]
    calc (∑ ρ ∈ s, (|(meromorphicOrderAt L ρ).untop₀| : ℝ))
        ≤ ∑ ρ ∈ Z (k + 2), (|(meromorphicOrderAt L ρ).untop₀| : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ abs_nonneg _
      _ ≤ (∑ ρ ∈ Z (k + 2), ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + 4 :=
          hasSum_heckeAsymptoticResidue_abs_sum_le χ L _hL _hAgree _
      _ ≤ B₀ * (((k + 2 : ℕ) : ℝ) + k₁ + 2) ^ m + 4 := by gcongr; exact hcountZ (k + 2)
      _ ≤ (B₀ + 4) * ((k : ℝ) + ((k₁ : ℝ) + 4)) ^ m := by
          have h1 : (1 : ℝ) ≤ ((k : ℝ) + ((k₁ : ℝ) + 4)) ^ m :=
            one_le_pow₀ (by linarith [k.cast_nonneg (α := ℝ)])
          have h2 : (((k + 2 : ℕ) : ℝ) + k₁ + 2) = (k : ℝ) + ((k₁ : ℝ) + 4) := by push_cast; ring
          rw [h2]
          nlinarith
  -- The rectangle identity for the Mellin test.
  have hrectΦ (k : ℕ) : ∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ =
      ((∫ x in (1 - a)..a, H ((x : ℂ) + (lo k : ℂ) * Complex.I)) -
        (∫ x in (1 - a)..a, H ((x : ℂ) + (up k : ℂ) * Complex.I)) +
        Complex.I * (∫ y in lo k..up k, H ((a : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in lo k..up k, H (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I))) /
          twoPiI := by
    have htwoPiI : twoPiI ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [eq_div_iff htwoPiI, mul_comm]
    exact (hasSum_heckeAsymptoticResidue_rectangle χ L _hL _hAgree a _ha (logMellin f) hΦd
      (lo k) (up k) (hlt k) (fun σ hσ ↦ ⟨(hEdge k σ hσ (lo k) (by simp)).1,
        (hEdge k σ hσ (up k) (by simp)).1⟩) (Z k) (hZ k)).symm
  -- The horizontal edges vanish in the limit.
  set N₂ : ℕ := m₁ + 1 with hN₂
  obtain ⟨C₂, hC₂, hbound₂⟩ := mellin_heightBound_of_exponentialDecay f _hf (1 - a) a
    (by linarith) N₂ (by omega)
  have hhoriz (t : ℝ) (ht1 : 1 ≤ |t|)
      (hAnt : ∀ σ ∈ Icc (1 - a) a,
        ‖logDeriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * |t| ^ β) :
      ‖∫ x in (1 - a)..a, H ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (2 * a - 1) * (C₂ * A) / |t| := by
    have ht0 : t ≠ 0 := by
      intro h; rw [h, abs_zero] at ht1; linarith
    have hIcc : Set.uIoc (1 - a) a ⊆ Icc (1 - a) a := by
      rw [uIoc_of_le (by linarith)]; exact Ioc_subset_Icc_self
    have hpt : ∀ x ∈ Set.uIoc (1 - a) a,
        ‖H ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₂ * A / |t| := by
      intro x hx
      have hx' := hIcc hx
      have h1 := hbound₂ x hx' t ht0
      simp only at h1
      have h2 := hAnt x hx'
      have hβ' : |t| ^ β ≤ |t| ^ m₁ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil β)
      have habs : 0 < |t| := by linarith
      calc ‖H ((x : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖logMellin f ((x : ℂ) + (t : ℂ) * Complex.I)‖ *
              ‖logDeriv L ((x : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
        _ ≤ (C₂ / |t| ^ N₂) * (A * |t| ^ m₁) :=
            mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left hβ' hA.le)) (norm_nonneg _)
              (by positivity)
        _ = C₂ * A / |t| := by
            rw [hN₂, pow_succ]
            field_simp
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1 - a) (b := a) hpt
    refine this.trans (le_of_eq ?_)
    rw [abs_of_pos (by linarith : (0 : ℝ) < a - (1 - a))]
    ring
  have hH0 : ∀ s : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 1 ≤ |s k|) →
      (∀ k : ℕ, ∀ σ ∈ Icc (1 - a) a,
        ‖logDeriv L ((σ : ℂ) + (s k : ℂ) * Complex.I)‖ ≤ A * |s k| ^ β) →
      Tendsto (fun k : ℕ ↦ ∫ x in (1 - a)..a, H ((x : ℂ) + (s k : ℂ) * Complex.I)) atTop
        (𝓝 0) := by
    intro s hs hAn
    refine squeeze_zero_norm (a := fun k : ℕ ↦ (2 * a - 1) * (C₂ * A) / ((k : ℝ) + 1))
      (fun k : ℕ ↦ (hhoriz (s k) (by linarith [hs k, k.cast_nonneg (α := ℝ)]) (hAn k)).trans ?_)
      ?_
    · exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (by positivity)) (by positivity)
        (hs k)
    · have := (tendsto_const_div_atTop_nhds_zero_nat ((2 * a - 1) * (C₂ * A))).comp
        (tendsto_add_atTop_nat 1)
      refine this.congr fun k ↦ ?_
      simp [Function.comp]
  have hlo' := hH0 lo (fun k : ℕ ↦ by
      rw [abs_of_neg (by linarith [hloNeg k])]; linarith [(hloB k).2])
    (fun k σ hσ ↦ ((hloG k).2 σ hσ).2)
  have hup' := hH0 up (fun k : ℕ ↦ by
      rw [abs_of_pos (by linarith [hupPos k])]; linarith [(hupB k).1])
    (fun k σ hσ ↦ ((hupG k).2 σ hσ).2)
  -- The vertical edges converge to the line integrals.
  have hVa : Tendsto (fun k ↦ Complex.I * ∫ y in lo k..up k, H ((a : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (verticalLineIntegral H a)) :=
    (intervalIntegral_tendsto_integral hintR hloBot hupTop).const_mul Complex.I
  have hVb : Tendsto (fun k ↦ Complex.I *
      ∫ y in lo k..up k, H (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (verticalLineIntegral H (1 - a))) :=
    (intervalIntegral_tendsto_integral hintL hloBot hupTop).const_mul Complex.I
  have hlim : Tendsto (fun k ↦ ∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ)
      atTop (𝓝 ((verticalLineIntegral H a - verticalLineIntegral H (1 - a)) / twoPiI)) := by
    have := (((hlo'.sub hup').add hVa).sub hVb).div_const twoPiI
    simp only [sub_self, zero_add] at this
    exact this.congr fun k ↦ (hrectΦ k).symm
  -- Conclusion: the partial sums over the rectangles exhaust the support.
  set Sset : Set ℂ := {ρ | meromorphicOrderAt L ρ ≠ 0} with hSset
  have hsupp : support (fun ρ : ℂ ↦ ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ) ⊆
      Sset := by
    intro ρ hρ h0
    apply hρ
    show ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ = 0
    simp [h0]
  have hsub := (hasSum_subtype_iff_of_support_subset hsupp).mpr hsum.hasSum
  let W : ℕ → Finset Sset := fun k ↦ (Z k).subtype (· ∈ Sset)
  have hWmono : Monotone W := fun i j hij ↦ Finset.subtype_mono (hZmono hij)
  have hWex : ∀ x : Sset, ∃ k, x ∈ W k := by
    intro x
    have hx : meromorphicOrderAt L x.val ≠ 0 := x.property
    refine ⟨⌈|x.val.im|⌉₊ + 2, ?_⟩
    rw [Finset.mem_subtype]
    have hreρ := hre x.val hx
    refine (hZ _ _).mpr ⟨⟨by linarith [hreρ.1], by linarith [hreρ.2]⟩, ⟨?_, ?_⟩, hx⟩
    · have := (hloB (⌈|x.val.im|⌉₊ + 2)).2
      push_cast at this
      linarith [Nat.le_ceil |x.val.im|, neg_abs_le x.val.im]
    · have := (hupB (⌈|x.val.im|⌉₊ + 2)).1
      push_cast at this
      linarith [Nat.le_ceil |x.val.im|, le_abs_self x.val.im]
  have hWtop : Tendsto W atTop atTop := tendsto_atTop_finset_of_monotone hWmono hWex
  have hpartial : Tendsto
      (fun k ↦ ∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ) atTop
      (𝓝 (∑' ρ, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ)) := by
    refine (Filter.Tendsto.comp hsub hWtop).congr fun k ↦ ?_
    simp only [W, Function.comp_apply]
    exact Finset.sum_subtype_of_mem
      (fun ρ ↦ ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ)
      fun ρ hρ ↦ ((hZ k ρ).mp hρ).2.2
  have heq := tendsto_nhds_unique hpartial hlim
  rw [← heq]
  exact hsum.hasSum

-- TODO(paper-gap): (B.4.2.3) misses the chain-rule sign. The page specifies
-- Aχ, but the identification ε'/ε = log Aχ needs the conductor calculation.
-- The normalized integral of Φ in (B.4.2.4) gives the test value at one.

local notation "conductorExponents(" χ ", " v ")" =>
  ({n : ℕ | ∀ u : (HeightOneSpectrum.adicCompletion F v)ˣ, ‖u.val‖ = 1 →
    ‖u.val - 1‖ ≤ q(v) ^ (-(n : ℤ)) →
      χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1} : Set ℕ)

/-- Paper: Equation (B.4.2.3), p. 614. Each finite local character has
a least conductor exponent, and only finitely many exponents are nonzero.
Deviation: The exponent is given by the local unit filtration of §3.3.1. -/
theorem exists_heckeConductorExponents (χ : U[F]) :
    ∃ n : Primes(F) → ℕ, (Function.support n).Finite ∧
      ∀ v, IsLeast (conductorExponents(χ, v)) (n v) := by
  classical
  have hlocal (v : Primes(F)) : (conductorExponents(χ, v)).Nonempty := by
    let η : (v.adicCompletion F)ˣ →ₜ* Circle := χ.comp
      ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩
    have harc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
      simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
    have hpre : η ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : (v.adicCompletion F)ˣ) :=
      η.continuous.continuousAt.preimage_mem_nhds (by
        change Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (η 1)
        rwa [map_one])
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hpre
    obtain ⟨W, hW, hsub⟩ := mem_comap.mp hpre
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
    have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (inv_lt_one_of_one_lt₀ hq)
    refine ⟨n, fun u hu hclose ↦ ?_⟩
    -- Every power stays close to one, so its character lies in the same half circle.
    change η u = 1
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro k _
    rw [← map_pow]
    apply hsub
    apply hball
    change dist (u.val ^ k) 1 < r
    rw [dist_eq_norm]
    apply (local_unit_pow_bound u.val hu.le k).trans_lt
    exact hclose.trans_lt (by simpa only [zpow_neg, zpow_natCast, inv_pow] using hn)
  let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have hcover : c ∈ ⋃ T : Finset (Primes(F)), (unramifiedOutside F T : Set _) := by
    rw [iUnion_unramifiedOutside]
    exact mem_univ _
  obtain ⟨T, hT⟩ := mem_iUnion.mp hcover
  refine ⟨fun v ↦ sInf (conductorExponents(χ, v)), T.finite_toSet.subset ?_,
    fun v ↦ ⟨Nat.sInf_mem (hlocal v), fun _ hn ↦ Nat.sInf_le hn⟩⟩
  intro v hv
  by_contra hvT
  have hzero : 0 ∈ conductorExponents(χ, v) := by
    intro u hu _
    have hunit : u ∈ (v.adicCompletionIntegers F).units :=
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
        (Valued.toNormedField.norm_eq_one_iff.mp hu)
    let u' := (v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType ⟨u, hunit⟩
    have h := (mem_unramifiedOutside_iff F T c).mp hT v hvT u'
    exact Subtype.ext h
  exact hv (Nat.eq_zero_of_le_zero (Nat.sInf_le hzero))

/-- Paper: Equation (B.4.2.3), p. 614. The logarithm of the
discriminant–conductor product adds the finite conductor exponents weighted by log prime norm.
Deviation: The conductor exponent is given by the local unit filtration of §3.3.1. -/
def heckeLogDiscriminantConductor (χ : U[F]) : ℝ :=
  Real.log (Int.natAbs (NumberField.discr F)) +
    ∑ᶠ v : Primes(F), Real.log q(v) * (sInf (conductorExponents(χ, v)) : ℕ)

/-- Paper: Equation (B.4.2.3), p. 614. The trivial character has only the
discriminant contribution. -/
theorem heckeLogDiscriminantConductor_one :
    heckeLogDiscriminantConductor (1 : U[F]) =
      Real.log (Int.natAbs (NumberField.discr F)) := by
  simp [heckeLogDiscriminantConductor]

/-- Paper: Equation (B.4.2.3), p. 614, with Proposition 3.2.1.3(3), p. 123. The epsilon
factor of the functional equation of the completed continuations is a nonzero constant times
the exponential of the discriminant–conductor logarithm centred at `1/2`:
`Λ(1 - s, χ⁻¹) = C · exp(log A_χ · (s - 1/2)) · Λ(s, χ)` for every `s`.
Deviation: `completedHeckeL_continuation_functionalEquation` only gives an unspecified entire
nowhere-vanishing factor; this identifies its exponent. The global test of
`exists_globalHeckeTest_fourier` has Fourier-side scale `q = ∏ᵥ N(𝔭ᵥ)^(dᵥ + nᵥ)` over the
finitely many places where the different exponent `dᵥ` or the conductor exponent `nᵥ` is
nonzero: at an unramified place the Fourier transform of the integer indicator is the
indicator of the inverse different, and at a ramified place the Fourier transform of the
unit test is supported on the shell of norm `N(𝔭ᵥ)^(dᵥ + nᵥ)`. The norm of the different is
`|disc F|` (`NumberField.absNorm_differentIdeal`), so `log q = heckeLogDiscriminantConductor χ`,
and `a / (b q^(1-s)) = (a / (b √q)) · exp(log q · (s - 1/2))`. -/
theorem completedHeckeL_functionalEquation_conductorScale (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualAgree : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, Ldual (1 - s) =
      C * Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (s - 1 / 2)) * L s := by
  obtain ⟨n, _, hn⟩ := exists_heckeConductorExponents χ
  refine completedHeckeL_continuation_conductor_of_isLeast χ L Ldual hL hAgree hLdual hDualAgree
    (fun v ↦ sInf (conductorExponents(χ, v))) (fun v ↦ ?_)
  rw [(hn v).csInf_eq]
  exact hn v

/-- Paper: Equation (B.4.2.3), p. 614. The reflected logarithmic derivative
and the discriminant–conductor term give the logarithmic derivative of the continuation.
Deviation: Both terms acquire the minus signs dictated by the functional equation
in Proposition 3.2.1.3(3). The order hypothesis excludes zeros and poles. -/
theorem completedHeckeL_logDeriv_reflection (χ : U[F]) (L Ldual : ℂ → ℂ)
    (_hL : MeromorphicNFOn L univ) (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (_hLdual : MeromorphicNFOn Ldual univ)
    (_hDualAgree : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s)
    (s : ℂ) (_hs : meromorphicOrderAt L s = 0) :
    logDeriv L s = -logDeriv Ldual (1 - s) - (heckeLogDiscriminantConductor χ : ℂ) := by
  obtain ⟨C, hC, hFE⟩ := completedHeckeL_functionalEquation_conductorScale χ L Ldual _hL
    _hAgree _hLdual _hDualAgree
  have hNF : MeromorphicNFAt L s := _hL (mem_univ s)
  have hLs : L s ≠ 0 := hNF.meromorphicOrderAt_eq_zero_iff.mp _hs
  have hLan : AnalyticAt ℂ L s := hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp _hs.ge
  have hG : AnalyticAt ℂ (fun z ↦ Ldual (1 - z)) s := by
    rw [show (fun z ↦ Ldual (1 - z)) = fun z ↦
        C * Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (z - 1 / 2)) * L z from
      funext hFE]
    exact (analyticAt_const.mul
      ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp')).mul hLan
  have hGdual : AnalyticAt ℂ Ldual (1 - s) := by
    have hG' : AnalyticAt ℂ (fun z ↦ Ldual (1 - z)) (1 - (1 - s)) := by
      rwa [sub_sub_cancel]
    have hcomp := hG'.comp
      (analyticAt_const.sub analyticAt_id : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) (1 - s))
    refine hcomp.congr (Eventually.of_forall fun w ↦ ?_)
    simp [Function.comp]
  exact External.Grh.completed_logDeriv_reflection hC hLan.differentiableAt
    hGdual.differentiableAt hLs (Eventually.of_forall hFE)

-- TODO(paper-gap): In (B.4.2.15) a compactly supported logarithmic profile
-- with f(0) = 1 leaves Nᵥ/x at infinity. The gamma arguments also omit
-- the sign parity or angular weight. With the printed negative αᵥ on p. 616,
-- the constant in (B.4.2.12) should be +αᵥ. The digamma integral below includes
-- the parity or angular weight and the gamma prefactor.

/-- Paper: Proposition B.4.2.1, p. 616. The combined digamma integrand uses
the gamma arguments of the two local characters and the positive and negative
samples of the logarithmic test.
Deviation: The subtraction uses Euler's convergent digamma kernel. -/
def heckeArchimedeanDigammaKernel (k : ℝ) (zPlus zMinus : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (k : ℂ) * (2 * (Real.exp (-t) : ℂ) * f 0 / (t : ℂ) -
    (f (k * t) * Complex.exp (-zPlus * (t : ℂ)) +
      f (-(k * t)) * Complex.exp (-zMinus * (t : ℂ))) / (1 - (Real.exp (-t) : ℂ)))

section GaussDigamma

open Real

/-- The factor `1 / t - 1 / (1 - e^{-t})` lies in `[-1, 0]` for positive `t`. -/
private lemma digamma_remainder_bounds {t : ℝ} (ht : 0 < t) :
    -1 ≤ 1 / t - 1 / (1 - exp (-t)) ∧ 1 / t - 1 / (1 - exp (-t)) ≤ 0 := by
  have hq : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - exp (-t) := by linarith
  have h1 : 1 - exp (-t) ≤ t := by linarith [add_one_le_exp (-t)]
  have h2 : t * exp (-t) ≤ 1 - exp (-t) := by
    have h := add_one_le_exp t
    have he : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos (-t)]
  constructor
  · rw [div_sub_div _ _ ht.ne' hd.ne', le_div_iff₀ (mul_pos ht hd)]
    nlinarith
  · rw [sub_nonpos]
    exact one_div_le_one_div_of_le hd h1

/-- The real Gauss kernel `e^{-t}/t - e^{-t}/(1 - e^{-t})` of `ψ(1)`. -/
private noncomputable def gaussDigammaKernel (t : ℝ) : ℝ :=
  exp (-t) / t - exp (-t) / (1 - exp (-t))

private lemma exp_neg_natCast_mul (m : ℕ) (t : ℝ) : exp (-((m : ℝ) * t)) = exp (-t) ^ m := by
  rw [← exp_nat_mul]
  ring_nf

/-- Splitting off the first `n` terms of the geometric series. -/
private lemma gaussDigammaKernel_eq (n : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussDigammaKernel t =
      t⁻¹ * (exp (-(1 * t)) - exp (-(((n + 1 : ℕ) : ℝ) * t))) -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t))) := by
  have hq : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 1 - exp (-t) ≠ 0 := by linarith
  simp only [exp_neg_natCast_mul, one_mul, gaussDigammaKernel]
  set q := exp (-t)
  have hgeom : (∑ i ∈ Finset.range n, q ^ (i + 1)) * (1 - q) = q - q ^ (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have hsum : ∑ i ∈ Finset.range n, q ^ (i + 1) = (q - q ^ (n + 1)) / (1 - q) := by
    rw [← hgeom, mul_div_cancel_right₀ _ hd]
  rw [hsum]
  field_simp
  ring

private lemma integrableOn_exp_neg_natCast_mul (m : ℕ) (hm : 0 < m) :
    IntegrableOn (fun t : ℝ ↦ exp (-((m : ℝ) * t))) (Ioi 0) := by
  simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -(m : ℝ)) (by simp [hm]) 0

private lemma integral_exp_neg_natCast_mul (m : ℕ) (hm : 0 < m) :
    ∫ t in Ioi (0 : ℝ), exp (-((m : ℝ) * t)) = 1 / m := by
  have := integral_exp_mul_Ioi (a := -(m : ℝ)) (by simp [hm]) 0
  simp only [neg_mul, mul_zero, exp_zero] at this
  rw [this]
  field_simp

private lemma integrableOn_gaussDigammaKernel : IntegrableOn gaussDigammaKernel (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg_Ioi 0) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have hd : 1 - exp (-t) ≠ 0 := by
      have : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
      linarith
    have ht' : t ≠ 0 := ht.ne'
    unfold gaussDigammaKernel
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_)
    have ht : (0 : ℝ) < t := ht
    obtain ⟨h1, h2⟩ := digamma_remainder_bounds ht
    have : gaussDigammaKernel t = exp (-t) * (1 / t - 1 / (1 - exp (-t))) := by
      unfold gaussDigammaKernel; ring
    rw [this, norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
    have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
    nlinarith [exp_pos (-t)]

private lemma integral_gaussDigammaKernel :
    ∫ t in Ioi (0 : ℝ), gaussDigammaKernel t = -eulerMascheroniConstant := by
  set I := ∫ t in Ioi (0 : ℝ), gaussDigammaKernel t
  -- The remainder after `n` geometric terms.
  let R : ℕ → ℝ := fun n ↦
    ∫ t in Ioi (0 : ℝ), exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))
  have hRint : ∀ n : ℕ, IntegrableOn
      (fun t ↦ exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) (Ioi 0) := by
    intro n
    refine Integrable.mono' (integrableOn_exp_neg_natCast_mul (n + 1) n.succ_pos) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht : (0 : ℝ) < t := ht
      have hd : 1 - exp (-t) ≠ 0 := by
        have : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
        linarith
      have ht' : t ≠ 0 := ht.ne'
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_)
      obtain ⟨h1, h2⟩ := digamma_remainder_bounds (show (0 : ℝ) < t from ht)
      rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
      have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
      nlinarith [exp_pos (-(((n + 1 : ℕ) : ℝ) * t))]
  have hRle : ∀ n : ℕ, ‖R n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    calc ‖R n‖ ≤ ∫ t in Ioi (0 : ℝ), exp (-(((n + 1 : ℕ) : ℝ) * t)) := by
          refine norm_integral_le_of_norm_le (integrableOn_exp_neg_natCast_mul (n + 1) n.succ_pos)
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_))
          obtain ⟨h1, h2⟩ := digamma_remainder_bounds (show (0 : ℝ) < t from ht)
          rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
          have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
          nlinarith [exp_pos (-(((n + 1 : ℕ) : ℝ) * t))]
      _ = 1 / ((n : ℝ) + 1) := by
          rw [integral_exp_neg_natCast_mul (n + 1) n.succ_pos]; push_cast; rfl
  -- The finite expansion of the integral.
  have hexp : ∀ n : ℕ, I = -(harmonic n - log ((n : ℝ) + 1)) + R n := by
    intro n
    have hsumint : ∀ i ∈ Finset.range n,
        IntegrableOn (fun t : ℝ ↦ exp (-(((i + 1 : ℕ) : ℝ) * t))) (Ioi 0) :=
      fun i _ ↦ integrableOn_exp_neg_natCast_mul (i + 1) i.succ_pos
    have hsumint' : IntegrableOn
        (fun t : ℝ ↦ ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) (Ioi 0) :=
      integrable_finsetSum _ hsumint
    let Fr : ℝ → ℝ := fun t ↦ t⁻¹ * (exp (-(1 * t)) - exp (-(((n + 1 : ℕ) : ℝ) * t)))
    have hFr : EqOn Fr (fun t ↦ gaussDigammaKernel t +
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) -
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) (Ioi 0) := by
      intro t ht
      simp only [Fr, gaussDigammaKernel_eq n (show (0 : ℝ) < t from ht)]
      ring
    have hFrint : IntegrableOn Fr (Ioi 0) :=
      ((integrableOn_gaussDigammaKernel.add hsumint').sub (hRint n)).congr_fun hFr.symm
        measurableSet_Ioi
    have hFrval : ∫ t in Ioi (0 : ℝ), Fr t = log ((n : ℝ) + 1) := by
      have hc : Continuous fun x : ℝ ↦ exp (-x) := by fun_prop
      have hL : Tendsto (fun x : ℝ ↦ exp (-x)) (𝓝[>] 0) (𝓝 1) := by
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      have := Frullani.integral_Ioi_eq (f := fun x : ℝ ↦ exp (-x)) (a := 1)
        (b := ((n + 1 : ℕ) : ℝ)) (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
        one_pos (by positivity) hL tendsto_exp_neg_atTop_nhds_zero hFrint
      simpa [Fr] using this
    have hsumval : ∫ t in Ioi (0 : ℝ), ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)) =
        harmonic n := by
      rw [integral_finsetSum _ hsumint, harmonic, Rat.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_exp_neg_natCast_mul (i + 1) i.succ_pos]
      push_cast
      ring
    have hI : I = ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ gaussDigammaKernel_eq n ht
    have e1 : ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) =
        (∫ t in Ioi (0 : ℝ), (Fr t -
          (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))))) + R n :=
      integral_add (hFrint.sub hsumint') (hRint n)
    have e2 : ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)))) =
        (∫ t in Ioi (0 : ℝ), Fr t) -
          ∫ t in Ioi (0 : ℝ), ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)) :=
      integral_sub hFrint hsumint'
    rw [hI, e1, e2, hFrval, hsumval]
    ring
  -- Let `n → ∞`.
  have hR0 : Tendsto R atTop (𝓝 0) :=
    squeeze_zero_norm hRle tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ ↦ -(harmonic n - log ((n : ℝ) + 1)) + R n) atTop
      (𝓝 (-eulerMascheroniConstant + 0)) :=
    tendsto_harmonic_sub_log_add_one.neg.add hR0
  rw [add_zero] at hlim
  refine tendsto_nhds_unique ?_ hlim
  simp_rw [← hexp]
  exact tendsto_const_nhds

end GaussDigamma

/-- Paper: Proposition B.4.2.1, p. 616. At unit scale and unit gamma
arguments the integrable kernel for the constant test gives twice the digamma value at one.
Deviation: This is a sanity check for the corrected kernel. -/
theorem heckeArchimedeanDigammaKernel_one :
    let K := heckeArchimedeanDigammaKernel 1 1 1 (fun _ ↦ 1)
    IntegrableOn K (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), K t) = -2 * (Real.eulerMascheroniConstant : ℂ) := by
  intro K
  have hK : K = fun t ↦ ((2 * gaussDigammaKernel t : ℝ) : ℂ) := by
    funext t
    simp only [K, heckeArchimedeanDigammaKernel, gaussDigammaKernel]
    push_cast
    simp only [neg_mul, one_mul]
    ring
  rw [hK]
  simp only []
  refine ⟨(integrableOn_gaussDigammaKernel.const_mul 2).ofReal, ?_⟩
  rw [integral_complex_ofReal, integral_const_mul, integral_gaussDigammaKernel]
  push_cast
  ring

local notation "circleToComplex" =>
  (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)

local notation "localChart(" w ", " χ ")" =>
  quasiCharacterNormTwist
    ((Units.map nnNormHom.toMonoidHom) ^ (InfinitePlace.mult w) :
      (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) (continuous_infiniteLocalModule w) (ContinuousMonoidHom.comp circleToComplex χ)

/-- A real norm twist adds its coordinate to the radial exponent and preserves parity. -/
private theorem realHeckeArchimedean_mellinLogDeriv_twist (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (z : ℂ) (k : Fin 2)
    (hχ : ∀ x : ℝˣ,
      (χ (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) : ℂ) =
        (‖(x : ℝ)‖ : ℂ) ^ z * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ k.val) :
    infiniteLocalEulerFactor w ∘ localChart(w, χ) = fun s ↦ Complex.Gammaℝ (s + (z + k.val)) := by
  funext s
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have h := (realLocalEulerParameters w hw (localChart(w, χ) s)).unique
    (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (s + z, k)) (by
      intro x
      have hn : ‖e (x : ℝ)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero e) (x : ℝ)
      change (χ (Units.map e.toMonoidHom x) : ℂ) * ((‖e (x : ℝ)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
      rw [hχ, hn, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
      simp only [InfinitePlace.mult, hw, ite_true, pow_one]
      ac_rfl)
  simp only [Function.comp_apply, infiniteLocalEulerFactor, hw, ↓reduceDIte, h, add_assoc]

/-- Unitarity forces the exponent to be imaginary. Inverting the character negates that
exponent and leaves its sign character fixed. -/
private theorem realHeckeArchimedean_mellinLogDeriv_parameters (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) :
    let p := (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    p.1.re = 0 ∧
      (infiniteLocalEulerFactor w ∘ localChart(w, χ) = fun s ↦ Complex.Gammaℝ (s + (p.1 + p.2.val))) ∧
      (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹) = fun s ↦ Complex.Gammaℝ (s + (-p.1 + p.2.val))) := by
  intro p
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have hp := (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose_spec
  change ∀ x : ℝˣ, (χ (Units.map e.toMonoidHom x) : ℂ) =
    (‖(x : ℝ)‖ : ℂ) ^ p.1 * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val at hp
  refine ⟨?_, realHeckeArchimedean_mellinLogDeriv_twist w hw χ _ _ hp,
    realHeckeArchimedean_mellinLogDeriv_twist w hw χ⁻¹ _ _ ?_⟩
  · have h := congrArg norm (hp (Units.mk0 (2 : ℝ) (by norm_num)))
    have hpow : ‖((2 : ℝ) : ℂ) ^ p.1‖ = 1 := by simpa using h.symm
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hpow
    exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num)).mp
      (hpow.trans (Real.rpow_zero _).symm)
  · intro x
    change ((χ (Units.map e.toMonoidHom x) : ℂ))⁻¹ = _
    rw [hp, mul_inv, Complex.cpow_neg]
    split_ifs <;> simp [← inv_pow]

/-- The Gauss difference times a Schwartz trace is absolutely integrable in both variables.
Its bound uses the first absolute moment of the trace. -/
private theorem realHeckeArchimedean_mellinLogDeriv_domination (W : 𝓢(ℝ, ℂ))
    (a : ℝ) (b : ℂ) (hab : 0 < a + b.re) :
    Integrable (fun p : ℝ × ℝ ↦ W p.1 * gaussDigammaDifferenceKernel 1
      (((a : ℂ) + (p.1 : ℂ) * Complex.I + b) / 2) p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  let u := (a + b.re) / 2
  let m := min 1 u
  let C := |1 - u| + |b.im|
  have hm : 0 < m := lt_min one_pos (half_pos hab)
  have hExp := integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) 0
  have hxExp : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-m * x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) one_pos hm)
  have hEnv : IntegrableOn (fun x : ℝ ↦ (1 + x) * Real.exp (-m * x)) (Ioi 0) := by
    simpa only [Pi.add_def, add_mul, one_mul] using hExp.add hxExp
  have hMoment : Integrable (fun y : ℝ ↦ (C + |y|) * ‖W y‖) := by
    simpa only [Pi.add_def, add_mul, Real.norm_eq_abs, pow_one] using
      (W.integrable.norm.const_mul C).add (W.integrable_pow_mul volume 1)
  refine (hMoment.mul_prod hEnv).mono'
    (Measurable.aestronglyMeasurable (by unfold gaussDigammaDifferenceKernel; fun_prop)) ?_
  have hx : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume.restrict (Ioi 0))), p.2 ∈ Ioi 0 :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_snd measurableSet_Ioi)).mpr
      (Eventually.of_forall fun _ : ℝ ↦ ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi)
  filter_upwards [hx] with ⟨y, x⟩ hx
  have hxpos : 0 < x := hx
  have he : ((a : ℂ) + (y : ℂ) * Complex.I + b) / 2 =
      (u : ℂ) + ((y + b.im) / 2 : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [u, add_div, Complex.div_ofNat_re, Complex.div_ofNat_im]
  have hIm : |(y + b.im) / 2| ≤ |y| + |b.im| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le y b.im, abs_nonneg (y + b.im)]
  rw [norm_mul, he]
  have h := norm_gaussDigammaDifferenceKernel_le (d := 1) (u := u) (v := (y + b.im) / 2)
    one_pos hxpos
  simp only [div_one] at h
  change _ ≤ ((C + |y|) * ‖W y‖) * ((1 + x) * Real.exp (-m * x))
  rw [mul_assoc, mul_left_comm (C + |y|)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  dsimp [C]
  linarith

/-- A Mellin trace of an exponentially decaying test is Schwartz. Mellin inversion
evaluates its exponentially twisted integral at every log coordinate. -/
private theorem realHeckeArchimedean_mellinLogDeriv_trace (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I
    ∃ W : 𝓢(ℝ, ℂ), (∀ y, W y = logMellin f (s y)) ∧ ∀ x : ℝ,
      (∫ y : ℝ, W y * Complex.exp (-s y * (x : ℂ))) / (2 * (Real.pi : ℂ)) = f x := by
  intro s
  obtain ⟨W, hW⟩ := exists_schwartz_verticalTrace_mellin_of_weighted_schwartz f (a - 1) (a + 1)
    (by linarith) (fun c _ ↦ exponentialDecay_weighted_schwartz f hf c) a ⟨by linarith, by linarith⟩
  refine ⟨W, congrFun hW, fun x ↦ ?_⟩
  have hi : Complex.VerticalIntegrable (logMellin f) a :=
    W.integrable.congr (Eventually.of_forall (congrFun hW))
  have hx := Real.exp_pos x
  have he := mellinInv_mellin_eq a (fun t ↦ f (Real.log t)) hx
    (mellinConvergent_of_exponentialDecay f hf a) hi
    (f.continuous.continuousAt.comp (Real.continuousAt_log hx.ne'))
  rw [Real.log_exp] at he
  rw [← he, mellinInv, Complex.real_smul]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [div_eq_inv_mul, one_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, Real.log_exp, smul_eq_mul, mul_comm (x : ℂ)]
  rw [mul_comm, congrFun hW y]

/-- Reversing the ordinate in Mellin inversion gives the reflected trace.
The sample at log coordinate `x` acquires the factor `exp (-x)`. -/
private theorem realHeckeArchimedean_mellinLogDeriv_reflect (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I
    ∃ W : 𝓢(ℝ, ℂ), (∀ y, W y = logMellin f (1 - s y)) ∧ ∀ x : ℝ,
      (∫ y : ℝ, W y * Complex.exp (-s y * (x : ℂ))) / (2 * (Real.pi : ℂ)) =
        Complex.exp (-(x : ℂ)) * f (-x) := by
  intro s
  obtain ⟨T, hT, hinv⟩ := realHeckeArchimedean_mellinLogDeriv_trace f hf (1 - a)
  obtain ⟨R, hR, _⟩ := exists_schwartzLogReflection
  refine ⟨R T, fun y ↦ ?_, fun x ↦ ?_⟩
  · rw [hR, hT]
    congr 1
    dsimp [s]
    push_cast
    ring
  · rw [← hinv (-x), ← mul_div_assoc, ← integral_const_mul]
    congr 1
    rw [← integral_neg_eq_self (fun y : ℝ ↦ R T y * Complex.exp (-s y * (x : ℂ)))]
    apply integral_congr_ae
    filter_upwards with y
    rw [hR, neg_neg, mul_left_comm, ← Complex.exp_add]
    congr 2
    dsimp [s]
    push_cast
    ring

local notation "gaussSample(" b ", " g ", " t ")" =>
  (((g) 0 * (Real.exp (-(t)) : ℂ) - (g) ((t) / 2) * Complex.exp (-(b) * ((t) : ℂ) / 2)) /
    (1 - (Real.exp (-(t)) : ℂ)))

/-- Evaluate one shifted real gamma factor against a Schwartz trace. The Gauss
difference stays together under Fubini, including at the singular endpoint. -/
private theorem realHeckeArchimedean_mellinLogDeriv_leg (W : 𝓢(ℝ, ℂ)) (g : ℝ → ℂ)
    (a : ℝ) (b : ℂ) (hab : 0 < a + b.re)
    (hinv : ∀ x : ℝ, (∫ y : ℝ, W y * Complex.exp
      (-((a : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ))) / (2 * (Real.pi : ℂ)) = g x) :
    let s := fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I
    let L := fun y ↦ W y * logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) (s y)
    Integrable L ∧ IntegrableOn (fun t ↦ gaussSample(b, g, t)) (Ioi 0) ∧
      (∫ y, L y) / (2 * (Real.pi : ℂ)) =
        ((∫ t in Ioi (0 : ℝ), gaussSample(b, g, t)) -
          ((Real.eulerMascheroniConstant : ℂ) + (Real.log Real.pi : ℂ)) * g 0) / 2 := by
  intro s L
  let c : ℂ := 2 * Real.pi
  let A : ℂ := Real.eulerMascheroniConstant + (Real.log Real.pi : ℂ)
  let D (y t : ℝ) := gaussDigammaDifferenceKernel 1 ((s y + b) / 2) t
  have hW : Integrable (W : ℝ → ℂ) := W.integrable
  have hJ : Integrable (fun p : ℝ × ℝ ↦ W p.1 * D p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) :=
    realHeckeArchimedean_mellinLogDeriv_domination W a b hab
  have h0 : (∫ y, W y) / c = g 0 := by simpa [c] using hinv 0
  have hslice (t : ℝ) : (∫ y, W y * D y t) / c = gaussSample(b, g, t) := by
    let E : ℂ := Real.exp (-t)
    let B := Complex.exp (-b * (t : ℂ) / 2)
    let P (y : ℝ) := Complex.exp (-s y * ((t / 2 : ℝ) : ℂ))
    have hP : Integrable (fun y ↦ W y * P y) := by
      refine (hW.norm.mul_const (Real.exp (-a * (t / 2)))).mono'
        (Continuous.aestronglyMeasurable (by dsimp [P, s]; fun_prop)) ?_
      filter_upwards with y
      simp [P, s, Complex.norm_exp, Complex.mul_re]
    have hsample : (∫ y, W y * P y) / c = g (t / 2) := hinv _
    have hpoint (y : ℝ) : W y * D y t = (W y * E - (W y * P y) * B) / (1 - E) := by
      have hsplit : Complex.exp (-((s y + b) / 2) * (t : ℂ)) = P y * B := by
        change _ = Complex.exp _ * Complex.exp _
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [D, gaussDigammaDifferenceKernel, Complex.ofReal_one, neg_one_mul, hsplit, E,
        Complex.ofReal_exp, Complex.ofReal_neg]
      ring
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hW.mul_const E) (hP.mul_const B), integral_mul_const,
      integral_mul_const]
    change ((_ - _) / (1 - E)) / c = (g 0 * E - g (t / 2) * B) / (1 - E)
    rw [← h0, ← hsample]
    ring
  have hsampleInt : IntegrableOn (fun t ↦ gaussSample(b, g, t)) (Ioi 0) :=
    (hJ.integral_prod_right.div_const c).congr (Eventually.of_forall hslice)
  have hL (y : ℝ) : L y = ((∫ t in Ioi (0 : ℝ), W y * D y t) - W y * A) / 2 := by
    have hz : 0 < ((s y + b) / 2).re := by simpa [s, Complex.div_ofNat_re] using half_pos hab
    have hψ := (integral_gaussDigammaDifferenceKernel (d := 1) (w := (s y + b) / 2)
      one_pos (by simpa using hz)).2
    simp only [Complex.ofReal_one, div_one, Complex.digamma_one] at hψ
    dsimp only [L]
    rw [realHeckeArchimedean_mellinLogDeriv_gamma b (s y) hz, integral_const_mul]
    change _ = (W y * (∫ t in Ioi (0 : ℝ), gaussDigammaDifferenceKernel 1 ((s y + b) / 2) t) - _) / 2
    rw [hψ]
    dsimp [A]
    ring
  have hline := hJ.integral_prod_left
  refine ⟨(hline.sub (hW.mul_const A)).div_const 2 |>.congr (Eventually.of_forall fun y ↦ (hL y).symm),
    hsampleInt, ?_⟩
  change (∫ y, L y) / c = ((∫ t in Ioi (0 : ℝ), gaussSample(b, g, t)) - A * g 0) / 2
  simp_rw [hL]
  rw [integral_div, integral_sub hline (hW.mul_const A), integral_mul_const, integral_integral_swap hJ]
  have hsampleTotal : (∫ t in Ioi (0 : ℝ), ∫ y, W y * D y t) / c =
      ∫ t in Ioi (0 : ℝ), gaussSample(b, g, t) := by
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall hslice)
  rw [← hsampleTotal, ← h0]
  ring

/-- Paper: Proposition B.4.2.1, p. 616. The two real local contour terms equal
the integral of the digamma kernel and the real gamma prefactor contribution.
Deviation: The integral converges at both endpoints and includes sign parity. -/
theorem realHeckeArchimedean_mellinLogDeriv (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (a : ℝ) (_ha : 1 < a) :
    let p := (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    let K := heckeArchimedeanDigammaKernel (1 / 2)
      ((p.1 + p.2.val) / 2) ((1 - p.1 + p.2.val) / 2) f
    let H := fun s ↦ logMellin f s * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ)) s +
      logMellin f (1 - s) * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)) s
    Complex.VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      verticalLineIntegral H a / twoPiI =
        (∫ t in Ioi (0 : ℝ), K t) - (Real.log Real.pi : ℂ) * f 0 := by
  intro p K H
  let b : ℂ := p.1 + p.2.val
  let b' : ℂ := -p.1 + p.2.val
  let g (x : ℝ) := Complex.exp (-(x : ℂ)) * f (-x)
  have hg0 : g 0 = f 0 := by simp [g]
  obtain ⟨hre, hχ, hχinv⟩ := realHeckeArchimedean_mellinLogDeriv_parameters w hw χ
  change p.1.re = 0 at hre
  have hb : 0 < a + b.re := by simp [b, hre]; positivity
  have hb' : 0 < a + b'.re := by simp [b', hre]; positivity
  obtain ⟨W, hW, hWinv⟩ := realHeckeArchimedean_mellinLogDeriv_trace f _hf a
  obtain ⟨V, hV, hVinv⟩ := realHeckeArchimedean_mellinLogDeriv_reflect f _hf a
  obtain ⟨hD, hKD, hDval⟩ := realHeckeArchimedean_mellinLogDeriv_leg W f a b hb hWinv
  obtain ⟨hR, hKR, hRval⟩ := realHeckeArchimedean_mellinLogDeriv_leg V g a b' hb' hVinv
  let s (y : ℝ) := (a : ℂ) + (y : ℂ) * Complex.I
  have hline (y : ℝ) : H (s y) =
      W y * logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) (s y) +
        V y * logDeriv (fun z ↦ Complex.Gammaℝ (z + b')) (s y) := by
    rw [hW, hV]
    simp only [H, hχ, hχinv, b, b', p, s]
  have hK (t : ℝ) : K t = (gaussDigammaKernel t : ℂ) * f 0 +
      (gaussSample(b, f, t) + gaussSample(b', g, t)) / 2 := by
    have hsample : g (t / 2) * Complex.exp (-b' * (t : ℂ) / 2) =
        f (-(t / 2)) * Complex.exp (-((1 - p.1 + p.2.val) / 2) * (t : ℂ)) := by
      dsimp only [g]
      rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
      congr 2
      dsimp [b']
      push_cast
      ring
    simp only [K, heckeArchimedeanDigammaKernel, gaussDigammaKernel, hg0, hsample, b,
      one_div_mul_eq_div]
    push_cast
    ring_nf
  have hbase : IntegrableOn (fun t ↦ (gaussDigammaKernel t : ℂ) * f 0) (Ioi 0) :=
    integrableOn_gaussDigammaKernel.ofReal.mul_const _
  have hsum : IntegrableOn (fun t ↦ gaussSample(b, f, t) + gaussSample(b', g, t)) (Ioi 0) :=
    hKD.add hKR
  have hvi : Complex.VerticalIntegrable H a :=
    (hD.add hR).congr (Eventually.of_forall fun y ↦ (hline y).symm)
  refine ⟨hvi, (hbase.add (hsum.div_const 2)).congr
    (Eventually.of_forall fun t ↦ (hK t).symm), ?_⟩
  change (Complex.I * ∫ y, H (s y)) / twoPiI = _
  rw [mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_div_mul_left _ _ Complex.I_ne_zero]
  simp_rw [hline, hK]
  rw [integral_add hD hR, add_div, hDval, hRval,
    integral_add hbase (hsum.div_const 2), integral_div, integral_add hKD hKR,
    integral_mul_const, integral_complex_ofReal, integral_gaussDigammaKernel, hg0]
  push_cast
  ring

/-- Mellin inversion on the line of abscissa `a`, together with its first absolute moment. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_trace
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + y * Complex.I
    let W := fun y ↦ logMellin f (s y)
    Continuous W ∧ Integrable (fun y ↦ ‖W y‖ * (1 + |y|)) ∧
      ∀ x : ℝ, (∫ y, W y * Complex.exp (-s y * x)) / (2 * (Real.pi : ℂ)) = f x := by
  intro s W
  obtain ⟨g, hg⟩ := exists_schwartz_verticalTrace_mellin_of_weighted_schwartz f
    (a - 1) (a + 1) (by linarith) (fun σ _ ↦ exponentialDecay_weighted_schwartz f hf σ)
    a ⟨by linarith, by linarith⟩
  change (g : ℝ → ℂ) = W at hg
  refine ⟨hg ▸ g.continuous, ?_, fun x ↦ ?_⟩
  · rw [← hg]
    apply (g.integrable.norm.add (g.integrable_pow_mul volume 1)).congr
    filter_upwards with y
    simp [Real.norm_eq_abs, add_mul, mul_comm]
  · have hgInt : Complex.VerticalIntegrable (logMellin f) a := by
      change Integrable W volume
      rw [← hg]
      exact g.integrable
    have hi := mellinInv_mellin_eq a (fun t : ℝ ↦ f (Real.log t)) (Real.exp_pos x)
      (mellinConvergent_of_exponentialDecay f hf a) hgInt
      (f.continuous.continuousAt.comp (Real.continuousAt_log (Real.exp_pos x).ne'))
    have hpow (y : ℝ) : ((Real.exp x : ℝ) : ℂ) ^ (-s y) = Complex.exp (-s y * x) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]
    simp only [mellinInv, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Real.log_exp, smul_eq_mul] at hi
    change 1 / (2 * (Real.pi : ℂ)) * (∫ y, ((Real.exp x : ℝ) : ℂ) ^ (-s y) * W y) = f x at hi
    simpa only [hpow, mul_comm (Complex.exp _) _, div_eq_inv_mul, one_mul, mul_one] using hi

open Complex in
/-- The logarithmic derivative of the translated complex gamma factor, including its prefactor. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_gamma
    (β s : ℂ) (hs : 0 < (s + β).re) :
    logDeriv (fun z ↦ Gammaℂ (z + β) / 2) s =
      -((Real.log (2 * Real.pi) : ℂ) + Real.eulerMascheroniConstant) +
        ∫ x in Ioi (0 : ℝ), gaussDigammaDifference 1 (s + β) x := by
  let B : ℂ := (2 * Real.pi : ℝ)
  have hB : B ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hlog : log B = (Real.log (2 * Real.pi) : ℂ) :=
    (ofReal_log (by positivity : 0 ≤ 2 * Real.pi)).symm
  have heq : (fun z ↦ Gammaℂ (z + β) / 2) =
      (fun z ↦ B ^ (-(z + β)) * Gamma (z + β)) := by
    funext z
    simp only [Gammaℂ_def, B, ofReal_mul, ofReal_ofNat]
    ring
  have harg := (hasDerivAt_id' s).add_const β
  have hP := harg.neg.const_cpow (Or.inl hB)
  change HasDerivAt (fun z : ℂ ↦ B ^ (-(z + β))) (B ^ (-(s + β)) * log B * -1) s at hP
  have hP0 : B ^ (-(s + β)) ≠ 0 := by simp [cpow_eq_zero_iff, hB]
  have hreg (n : ℕ) : s + β ≠ -(n : ℂ) := by
    intro he
    simp [he] at hs
    exact (Nat.cast_nonneg n).not_gt hs
  have hG := (hasDerivAt_Gamma_of_re_pos hs).differentiableAt
  rw [heq, logDeriv_fun_mul (f := fun z ↦ B ^ (-(z + β))) (g := fun z ↦ Gamma (z + β))
    s hP0 (Gamma_ne_zero_of_re_pos hs) hP.differentiableAt (hG.comp s harg.differentiableAt),
    harg.logDeriv_Gamma hreg, one_mul, logDeriv_apply, hP.deriv]
  have hv := (integral_gaussDigammaDifference (w := s + β) (d := 1) one_pos (by simpa using hs)).2
  simp only [ofReal_one, div_one, digamma_one] at hv
  rw [hv, hlog]
  field_simp
  ring

open Complex in
/-- Evaluate one gamma contour using an ordinate weight whose inverse transform is `g`.
The joint first-moment bound permits Fubini before the two singular terms are separated. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_leg
    (a : ℝ) (ha : 0 < a) (β : ℂ) (hβ : 0 ≤ β.re) (W g : ℝ → ℂ)
    (hW : Continuous W) (hM : Integrable (fun y ↦ ‖W y‖ * (1 + |y|)))
    (hinv : ∀ x : ℝ, (∫ y : ℝ, W y * exp (-((a : ℂ) + y * I) * x)) /
      (2 * (Real.pi : ℂ)) = g x) :
    let s := fun y : ℝ ↦ (a : ℂ) + y * I
    let L := fun y ↦ W y * logDeriv (fun z ↦ Gammaℂ (z + β) / 2) (s y)
    let K := fun x : ℝ ↦ (g 0 * exp (-(x : ℂ)) - exp (-β * x) * g x) / (1 - exp (-(x : ℂ)))
    Integrable L ∧ IntegrableOn K (Ioi 0) ∧
      (∫ y, L y) / (2 * (Real.pi : ℂ)) =
        -((Real.log (2 * Real.pi) : ℂ) + Real.eulerMascheroniConstant) * g 0 + ∫ x in Ioi 0, K x := by
  intro s L K
  let c := 2 * (Real.pi : ℂ)
  let A := -((Real.log (2 * Real.pi) : ℂ) + Real.eulerMascheroniConstant)
  let H := fun y x ↦ gaussDigammaDifference 1 (s y + β) x
  have hJ : Integrable (fun p : ℝ × ℝ ↦ W p.1 * H p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    simpa only [H, s, Complex.re_add_im] using
      integrable_mul_gaussDigammaDifference (τ := β.im) ha one_pos hβ hW.measurable hM
  have hWi : Integrable W := hM.mono' hW.aestronglyMeasurable (Eventually.of_forall fun y ↦
    le_mul_of_one_le_right (norm_nonneg _) (by linarith [abs_nonneg y]))
  have hzero : (∫ y, W y) / c = g 0 := by simpa [c] using hinv 0
  have hslice (x : ℝ) : (∫ y, W y * H y x) / c = K x := by
    have hExp (y : ℝ) : exp (-(s y + β) * x) = exp (-β * x) * exp (-s y * x) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hXi : Integrable (fun y ↦ W y * exp (-s y * x)) := by
      refine (hWi.norm.mul_const (Real.exp (-a * x))).mono'
        ((hW.mul (by dsimp [s]; fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun y ↦ ?_)
      simp [Complex.norm_exp, s, mul_re]
    have hpoint (y : ℝ) : W y * H y x = (W y * exp (-(x : ℂ)) -
        exp (-β * x) * (W y * exp (-s y * x))) / (1 - exp (-(x : ℂ))) := by
      simp only [H, gaussDigammaDifference, ofReal_one, neg_one_mul, hExp, div_eq_mul_inv]
      ring
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hWi.mul_const _) (hXi.const_mul _), integral_mul_const,
      integral_const_mul]
    change _ = ((g 0) * _ - _ * g x) / _
    rw [← hzero, ← hinv x]
    dsimp only [c, s]
    ring
  have hK := (hJ.integral_prod_right.div_const c).congr (Eventually.of_forall hslice)
  have hline (y : ℝ) : L y = W y * A + ∫ x in Ioi (0 : ℝ), W y * H y x := by
    have hs : 0 < (s y + β).re := by simpa [s, mul_re] using add_pos_of_pos_of_nonneg ha hβ
    simp only [L, complexHeckeArchimedean_mellinLogDeriv_gamma β (s y) hs, mul_add,
      integral_const_mul, H, A]
  refine ⟨?_, hK, ?_⟩
  · simp_rw [show L = _ from funext hline]
    exact (hWi.mul_const A).add hJ.integral_prod_left
  · simp_rw [hline]
    rw [integral_add (hWi.mul_const A) hJ.integral_prod_left, integral_mul_const, add_div,
      mul_div_right_comm, hzero, mul_comm (g 0), integral_integral_swap hJ, ← integral_div]
    change _ + (∫ x in Ioi (0 : ℝ), (∫ y, W y * H y x) / c) = _
    simp_rw [hslice, A]

/-- A norm twist shifts the radial exponent and preserves the angular weight. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_factor
    (w : InfinitePlace F) (hw : w.IsComplex) (χ : PontryaginDual w.Completionˣ)
    (z : ℂ) (r : ℤ) (h : ∀ x : ℂˣ, (χ (Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom x) : ℂ) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ z * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ r) :
    infiniteLocalEulerFactor w ∘ localChart(w, χ) =
      fun s ↦ Complex.Gammaℂ (s + (z + (r.natAbs : ℂ) / 2)) / 2 := by
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
  have hn (x : ℂ) : ‖e x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
      (map_zero e) x
  have hnreal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
  funext s
  let hpar := complexLocalEulerParameters w hw (localChart(w, χ) s)
  have hp : hpar.exists.choose = (s + z, r) := by
    apply hpar.unique hpar.exists.choose_spec
    intro x
    change (χ (Units.map e.toMonoidHom x) : ℂ) * ((‖e (x : ℂ)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
    have hx : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
    rw [h x, hn, InfinitePlace.mult, ite_eq_right hnreal, Complex.cpow_add _ _ hx]
    ac_rfl
  simp only [Function.comp_apply, infiniteLocalEulerFactor, hnreal, ↓reduceDIte, hp, ← add_assoc]

/-- Inverting the reflected Mellin weight adds the factor `exp (-x)` to the negative sample. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_reflect
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + y * Complex.I
    let W := fun y ↦ logMellin f (1 - s y)
    Continuous W ∧ Integrable (fun y ↦ ‖W y‖ * (1 + |y|)) ∧
      ∀ x : ℝ, (∫ y, W y * Complex.exp (-s y * x)) / (2 * (Real.pi : ℂ)) =
        Complex.exp (-(x : ℂ)) * f (-x) := by
  intro s W
  let u := fun y : ℝ ↦ ((1 - a : ℝ) : ℂ) + y * Complex.I
  have hneg (y : ℝ) : 1 - s y = u (-y) := by dsimp [s, u]; push_cast; ring
  obtain ⟨hc, hm, hi⟩ := complexHeckeArchimedean_mellinLogDeriv_trace f hf (1 - a)
  change Continuous (fun y ↦ logMellin f (u y)) at hc
  have heq : W = fun y ↦ logMellin f (u (-y)) := funext fun y ↦ congrArg (logMellin f) (hneg y)
  rw [heq]
  refine ⟨hc.comp continuous_neg, ?_, fun x ↦ ?_⟩
  · simpa only [abs_neg] using hm.comp_neg
  · have hphase (y : ℝ) : Complex.exp (-s y * x) =
        Complex.exp (-(x : ℂ)) * Complex.exp (-u (-y) * ((-x : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← hneg]
      congr 1
      push_cast
      ring
    simp_rw [hphase, ← mul_left_comm (Complex.exp _) (logMellin f _)]
    rw [integral_const_mul, mul_div_assoc, ← hi (-x)]
    rw [integral_neg_eq_self (fun y : ℝ ↦ logMellin f (u y) *
      Complex.exp (-u y * ((-x : ℝ) : ℂ)))]

/-- Paper: Proposition B.4.2.1, p. 616. The two complex local contour terms
equal the digamma integral and the complex gamma prefactor contribution.
Deviation: The integral converges at both endpoints and includes absolute angular weight. -/
theorem complexHeckeArchimedean_mellinLogDeriv (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (a : ℝ) (_ha : 1 < a) :
    let p := (complexLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    let K := heckeArchimedeanDigammaKernel 1
      (p.1 + (p.2.natAbs : ℂ) / 2) (1 - p.1 + (p.2.natAbs : ℂ) / 2) f
    let H := fun s ↦ logMellin f s * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ)) s +
      logMellin f (1 - s) * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)) s
    Complex.VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      verticalLineIntegral H a / twoPiI =
        (∫ t in Ioi (0 : ℝ), K t) - 2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
  intro p K H
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
  let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  let c := ContinuousMonoidHom.comp circleToComplex χ
  have hp := (complexLocalEulerParameters w hw c).exists.choose_spec
  have hpRe : p.1.re = 0 := by
    obtain ⟨q, ⟨hRe, hq⟩, _⟩ := existsUnique_complexUnits_character_parameters (c.comp i)
      (fun x ↦ Circle.norm_coe (χ (i x)))
    have h : p = q := (complexLocalEulerParameters w hw c).unique hp hq
    simpa only [h] using hRe
  let b := (p.2.natAbs : ℂ) / 2
  let β := p.1 + b
  let β' := -p.1 + b
  have hb : 0 ≤ b.re := by
    simp [b, Complex.div_ofNat_re]
    positivity
  have hβ : 0 ≤ β.re := by simpa [β, hpRe] using hb
  have hβ' : 0 ≤ β'.re := by simpa [β', hpRe] using hb
  have hD := complexHeckeArchimedean_mellinLogDeriv_factor w hw χ p.1 p.2 hp
  have hR : infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹) =
      fun s ↦ Complex.Gammaℂ (s + β') / 2 := by
    have hinv (x : ℂˣ) : ((χ⁻¹) (i x) : ℂ) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-p.1) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (-p.2) := by
      change ((χ (i x) : ℂ)⁻¹) = _
      change ∀ x : ℂˣ, (χ (i x) : ℂ) = _ at hp
      rw [hp x, mul_inv, Complex.cpow_neg, zpow_neg]
    have hinvFactor := complexHeckeArchimedean_mellinLogDeriv_factor w hw χ⁻¹ (-p.1) (-p.2) hinv
    rw [Int.natAbs_neg] at hinvFactor
    exact hinvFactor
  let s := fun y : ℝ ↦ (a : ℂ) + y * Complex.I
  let directWeight := fun y ↦ logMellin f (s y)
  let reflectedWeight := fun y ↦ logMellin f (1 - s y)
  let reflectedTest := fun x : ℝ ↦ Complex.exp (-(x : ℂ)) * f (-x)
  let directLine := fun y ↦ directWeight y * logDeriv (fun z ↦ Complex.Gammaℂ (z + β) / 2) (s y)
  let reflectedLine := fun y ↦ reflectedWeight y * logDeriv (fun z ↦ Complex.Gammaℂ (z + β') / 2) (s y)
  let decay := fun x : ℝ ↦ Complex.exp (-(x : ℂ))
  let directKernel := fun x : ℝ ↦ (f 0 * decay x - Complex.exp (-β * x) * f x) / (1 - decay x)
  let reflectedKernel := fun x : ℝ ↦
    (reflectedTest 0 * decay x - Complex.exp (-β' * x) * reflectedTest x) / (1 - decay x)
  obtain ⟨hc, hm, hi⟩ := complexHeckeArchimedean_mellinLogDeriv_trace f _hf a
  obtain ⟨hc', hm', hi'⟩ := complexHeckeArchimedean_mellinLogDeriv_reflect f _hf a
  obtain ⟨hDirectLine, hDirectKernel, directEval⟩ :=
    complexHeckeArchimedean_mellinLogDeriv_leg a (by linarith) β hβ directWeight f hc hm hi
  obtain ⟨hReflectedLine, hReflectedKernel, reflectedEval⟩ :=
    complexHeckeArchimedean_mellinLogDeriv_leg a (by linarith) β' hβ' reflectedWeight reflectedTest hc' hm' hi'
  change Integrable directLine at hDirectLine
  change Integrable reflectedLine at hReflectedLine
  change IntegrableOn directKernel (Ioi 0) at hDirectKernel
  change IntegrableOn reflectedKernel (Ioi 0) at hReflectedKernel
  change (∫ y, directLine y) / _ = _ * f 0 + ∫ x in Ioi 0, directKernel x at directEval
  change (∫ y, reflectedLine y) / _ = _ * reflectedTest 0 + ∫ x in Ioi 0, reflectedKernel x at reflectedEval
  have line_eq (y : ℝ) : H (s y) = directLine y + reflectedLine y := by simp only [H, hD, hR]; rfl
  have hzero : reflectedTest 0 = f 0 := by simp [reflectedTest]
  -- The reference value of the subtracted Gauss integral is ψ(1) = -γ.
  let gaussTerm := fun x : ℝ ↦ (2 * f 0) * (gaussDigammaKernel x : ℂ)
  have kernel_eq (x : ℝ) : K x = gaussTerm x + (directKernel x + reflectedKernel x) := by
    have hphase : Complex.exp (-β' * (x : ℂ)) * Complex.exp (-(x : ℂ)) =
        Complex.exp (-(1 - p.1 + b) * (x : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; dsimp [β']; ring
    simp only [K, heckeArchimedeanDigammaKernel, Complex.ofReal_one, one_mul, gaussTerm,
      directKernel, reflectedKernel, hzero, reflectedTest, ← mul_assoc (Complex.exp (-β' * (x : ℂ))), hphase, gaussDigammaKernel, decay]
    push_cast
    simp only [β, b]
    ring
  have hGaussInt : IntegrableOn gaussTerm (Ioi 0) := integrableOn_gaussDigammaKernel.ofReal.const_mul _
  have hGauss : (∫ x in Ioi (0 : ℝ), gaussTerm x) =
      (2 * f 0) * (-(Real.eulerMascheroniConstant : ℂ)) := by
    simp [gaussTerm, integral_const_mul, integral_complex_ofReal, integral_gaussDigammaKernel]
  have hH : Complex.VerticalIntegrable H a := by
    change Integrable (fun y ↦ H (s y))
    simp_rw [line_eq]
    exact hDirectLine.add hReflectedLine
  refine ⟨hH, ?_, ?_⟩
  · rw [show K = _ from funext kernel_eq]
    exact hGaussInt.add (hDirectKernel.add hReflectedKernel)
  · change (Complex.I * ∫ y, H (s y)) / twoPiI = _
    simp_rw [line_eq, kernel_eq]
    rw [integral_add hDirectLine hReflectedLine,
      integral_add (f := gaussTerm) (g := fun x ↦ directKernel x + reflectedKernel x)
        hGaussInt (hDirectKernel.add hReflectedKernel),
      integral_add hDirectKernel hReflectedKernel, hGauss]
    have hnorm (v : ℂ) : (Complex.I * v) / twoPiI = v / (2 * (Real.pi : ℂ)) := by
      rw [mul_comm Complex.I, mul_div_mul_right _ _ Complex.I_ne_zero]
    rw [hnorm, add_div, directEval, reflectedEval, hzero]
    ring

-- TODO(paper-gap): (B.4.2.10) needs dt/(2π). With upward ds/(2πi),
-- (B.4.2.11) gives +log(q) χ̄(π)^m q^(-m) φ(q^(-m)).
-- Theorem B.4.2.2 also subtracts two pole terms for every χ and uses the
-- divergent archimedean integral from (B.4.2.15).

local notation "primeTerm(" χ ", " f ")" =>
  (fun j : Primes(F) × ℕ ↦
    if χ₀(χ).IsUnramifiedAt j.1 then
      let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
      (Real.log q(j.1) * Real.exp (-x / 2) : ℝ) *
        ((χ₀(χ).localValue j.1) ^ (j.2 + 1) * f x +
          (χ₀(χ⁻¹).localValue j.1) ^ (j.2 + 1) * f (-x))
    else (0 : ℂ))

/-- Paper: Theorem B.4.2.2, p. 616. The centered prime-power contributions
are absolutely summable over the finite places and positive exponents.
Deviation: Ramified Euler factors contribute zero. -/
theorem summable_heckeExplicitPrimeTerms (χ : U[F]) (f : 𝓢(ℝ, ℂ))
    (_hf : ExponentialDecay f) :
    Summable (fun j ↦ ‖primeTerm(χ, f) j‖) := by
  obtain ⟨g, hg⟩ := exponentialDecay_weighted_schwartz f _hf 3
  obtain ⟨h, hh⟩ := exponentialDecay_weighted_schwartz f _hf (-3)
  let C := SchwartzMap.seminorm ℂ 0 0 g + SchwartzMap.seminorm ℂ 0 0 h
  have hdecay (x : ℝ) : ‖f x‖ + ‖f (-x)‖ ≤ C * Real.exp (-(3 * x)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), add_mul]
    have hg' := g.norm_le_seminorm ℂ x
    have hh' := h.norm_le_seminorm ℂ (-x)
    rw [hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hg'
    simp only [hh, neg_mul_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)] at hh'
    simpa only [mul_comm] using add_le_add hg' hh'
  -- Index the majorant by the corresponding prime-power ideals.
  let I (j : Primes(F) × ℕ) := j.1.asIdeal ^ (j.2 + 1)
  have hI : Injective I := by
    rintro ⟨v, n⟩ ⟨w, k⟩ he
    change v.asIdeal ^ (n + 1) = w.asIdeal ^ (k + 1) at he
    have hd : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow
      (he ▸ dvd_pow_self _ (Nat.succ_ne_zero n))
    have hvw : v = w := HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hd)).symm
    subst w
    have hN := congrArg (Ideal.absNorm : Ideal (𝓞 F) → ℕ) he
    simp only [map_pow] at hN
    have hn := Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) hN
    exact Prod.ext rfl (Nat.succ.inj hn)
  have hsum := (summable_absNorm_rpow F (r := 2) (by norm_num)).comp_injective hI
  refine (hsum.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
  rintro ⟨v, k⟩
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlog := (Real.log_pos hq).le
  let x := ((k + 1 : ℕ) : ℝ) * Real.log q(v)
  have hx : Real.log q(v) ≤ x := by
    dsimp [x]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hlog]
  have hfactor : Real.log q(v) * Real.exp (-x / 2) ≤ Real.exp x :=
    (mul_le_of_le_one_right hlog (Real.exp_le_one_iff.mpr (by linarith))).trans
      (hx.trans (by linarith [Real.add_one_le_exp x]))
  change ‖(if _ then _ else (0 : ℂ))‖ ≤ C * ((I (v, k)).absNorm : ℝ) ^ (-(2 : ℝ))
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hlog (Real.exp_nonneg _))]
    calc
      _ ≤ (Real.log q(v) * Real.exp (-x / 2)) * (‖f x‖ + ‖f (-x)‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlog (Real.exp_nonneg _))
        simpa only [norm_mul, norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul]
          using norm_add_le ((χ₀(χ).localValue v) ^ (k + 1) * f x)
            ((χ₀(χ⁻¹).localValue v) ^ (k + 1) * f (-x))
      _ ≤ Real.exp x * (C * Real.exp (-(3 * x))) :=
        mul_le_mul hfactor (hdecay x) (by positivity) (Real.exp_nonneg _)
      _ = C * Real.exp (x + -(3 * x)) := by rw [Real.exp_add]; ring
      _ = _ := by
        change _ = C * (((v.asIdeal ^ (k + 1)).absNorm : ℕ) : ℝ) ^ (-(2 : ℝ))
        rw [map_pow, Nat.cast_pow, Real.rpow_def_of_pos (pow_pos (zero_lt_one.trans hq) _),
          Real.log_pow]
        dsimp [x]
        ring_nf
  · rw [norm_zero]
    exact mul_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Helper for `hasSum_heckeExplicitFormula`: the centred profile `x ↦ exp(-x/2) f x` of an
exponentially decaying Schwartz function is again an exponentially decaying Schwartz function. -/
private theorem hasSum_heckeExplicitFormula_centeredProfile (f : 𝓢(ℝ, ℂ))
    (hf : ExponentialDecay f) :
    ∃ g : 𝓢(ℝ, ℂ), ExponentialDecay g ∧ ∀ x : ℝ, g x = (Real.exp (-x / 2) : ℂ) * f x := by
  obtain ⟨R, hR, -⟩ := exists_schwartzLogReflection
  have hRf : ForwardSemiExponentialDecay (R f) :=
    (backwardSemiExponentialDecay_iff_forward_reflected (R f) f
      (fun x ↦ by rw [hR, neg_neg])).mp hf.2
  have hweight : ∀ c : ℝ, ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = (Real.exp (c * x) : ℂ) * f x := by
    intro c
    by_cases hc : 0 ≤ c
    · exact (forwardSemiExponentialDecay_iff_weighted_schwartz f).mp hf.1 c hc
    · obtain ⟨g, hg⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz (R f)).mp hRf (-c)
        (by linarith)
      exact ⟨R g, fun x ↦ by simp only [hR, hg, neg_neg, neg_mul_neg]⟩
  obtain ⟨g, hg⟩ := hweight (-1 / 2)
  refine ⟨g, ⟨?_, ?_⟩, fun x ↦ by rw [hg, show (-1 / 2 : ℝ) * x = -x / 2 by ring]⟩
  · refine (forwardSemiExponentialDecay_iff_weighted_schwartz g).mpr fun A hA ↦ ?_
    obtain ⟨h, hh⟩ := hweight (A - 1 / 2)
    refine ⟨h, fun x ↦ ?_⟩
    rw [hh, hg]
    beta_reduce
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  · refine (backwardSemiExponentialDecay_iff_forward_reflected (R g) g
      (fun x ↦ by rw [hR, neg_neg])).mpr ?_
    refine (forwardSemiExponentialDecay_iff_weighted_schwartz (R g)).mpr fun A hA ↦ ?_
    obtain ⟨h, hh⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz (R f)).mp hRf (A + 1 / 2)
      (by linarith)
    refine ⟨h, fun x ↦ ?_⟩
    rw [hh, hR f x, hR g x, hg (-x)]
    beta_reduce
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring

/-- Tilting the logarithmic test by the half weight shifts the Mellin argument. -/
private theorem heckeExplicitFormula_centeredLine_mellin
    (f g : 𝓢(ℝ, ℂ)) (hgf : ∀ x : ℝ, g x = (Real.exp (-x / 2) : ℂ) * f x)
    (s : ℂ) : logMellin g s = logMellin f (s - 1 / 2) := by
  have h : logMellin g s =
      mellin (fun t : ℝ ↦ (t : ℂ) ^ (-(1 / 2 : ℂ)) • f (Real.log t)) s := by
    show ∫ t in Ioi (0 : ℝ), _ = ∫ t in Ioi (0 : ℝ), _
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht' : (0 : ℝ) < t := ht
    simp only [hgf, smul_eq_mul]
    congr 2
    rw [show -Real.log t / 2 = Real.log t * (-(1 / 2 : ℝ)) by ring, ← Real.rpow_def_of_pos ht',
      Complex.ofReal_cpow ht'.le]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [h, mellin_cpow_smul, sub_eq_add_neg]

/-- A Schwartz Mellin trace remains integrable when multiplied by a continuous
function with at most linear growth. -/
private theorem heckeExplicitFormula_centeredLine_integrable
    (T : 𝓢(ℝ, ℂ)) (G : ℝ → ℂ) (hG : Continuous G) (C : ℝ)
    (hC : ∀ y, ‖G y‖ ≤ C * (1 + |y|)) :
    Integrable (fun y ↦ T y * G y) := by
  have hMoment : Integrable (fun y ↦ (1 + |y|) * ‖T y‖) := by
    simpa only [Pi.add_def, add_mul, one_mul, Real.norm_eq_abs, pow_one] using
      T.integrable.norm.add (T.integrable_pow_mul volume 1)
  refine (hMoment.const_mul C).mono' (T.continuous.mul hG).aestronglyMeasurable ?_
  filter_upwards with y
  rw [norm_mul]
  calc
    _ ≤ ‖T y‖ * (C * (1 + |y|)) := mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    _ = _ := by ring

/-- On the right of one the completed logarithmic derivative splits into its
finite and gamma terms, each integrable against a Schwartz Mellin trace. -/
private theorem heckeExplicitFormula_centeredLine_decompose
    (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) (a : ℝ) (ha : 1 < a)
    (W : ℂ → ℂ) (T : 𝓢(ℝ, ℂ)) (hT : ∀ y : ℝ, T y = W ((a : ℂ) + y * Complex.I)) :
    Complex.VerticalIntegrable (fun s ↦ W s * logDeriv L s) a ∧
      verticalLineIntegral (fun s ↦ W s * logDeriv L s) a =
        verticalLineIntegral (fun s ↦ W s * logDeriv (heckeGammaFactor χ) s) a +
        verticalLineIntegral (fun s ↦ W s * logDeriv (finiteSeries(χ)) s) a := by
  let s (y : ℝ) : ℂ := (a : ℂ) + y * Complex.I
  have hs (y : ℝ) : (s y).re = a := by simp [s]
  have hs' (y : ℝ) : 1 < (s y).re := hs y ▸ ha
  have hsplit (y : ℝ) := completedHeckeL_logDeriv_right_local χ L hL hAgree (hs' y)
  have hc : Continuous s := by dsimp [s]; fun_prop
  have hcL : Continuous (fun y ↦ logDeriv L (s y)) :=
    continuous_iff_continuousAt.mpr fun y ↦ (hsplit y).1.continuousAt.comp hc.continuousAt
  have hcF : Continuous (fun y ↦ logDeriv (finiteSeries(χ)) (s y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hA := LSeries_analyticOnNhd _ (s y) (completedHeckeL_logDeriv_abscissa χ (hs' y))
    have hne : finiteSeries(χ) (s y) ≠ 0 := norm_pos_iff.mp
      ((Real.exp_pos _).trans_le (completedHeckeL_logDeriv_finite_lower χ a ha (s y) (hs y)))
    exact (hA.deriv.div hA hne).continuousAt.comp hc.continuousAt
  have hcG : Continuous (fun y ↦ logDeriv (heckeGammaFactor χ) (s y)) := by
    have he : (fun y ↦ logDeriv (heckeGammaFactor χ) (s y)) =
        fun y ↦ logDeriv L (s y) - logDeriv (finiteSeries(χ)) (s y) :=
      funext fun y ↦ by rw [(hsplit y).2, add_sub_cancel_right]
    rw [he]
    exact hcL.sub hcF
  obtain ⟨C, -, hC⟩ := completedHeckeL_logDeriv_gammaFactor_bound χ a (zero_lt_one.trans ha)
  obtain ⟨D, hD, hD'⟩ := completedHeckeL_logDeriv_finite_bound χ a ha
  have hiG := (heckeExplicitFormula_centeredLine_integrable T _ hcG C hC).congr
    (Eventually.of_forall fun y ↦ congrArg (fun z ↦ z * logDeriv (heckeGammaFactor χ) (s y)) (hT y))
  have hiF := (heckeExplicitFormula_centeredLine_integrable T _ hcF D (fun y ↦
    (hD' _ (hs y)).trans (le_mul_of_one_le_right hD (le_add_of_nonneg_right (abs_nonneg y))))).congr
      (Eventually.of_forall fun y ↦ congrArg (fun z ↦ z * logDeriv (finiteSeries(χ)) (s y)) (hT y))
  have he (y : ℝ) : W (s y) * logDeriv L (s y) =
      W (s y) * logDeriv (heckeGammaFactor χ) (s y) +
        W (s y) * logDeriv (finiteSeries(χ)) (s y) := by
    rw [(hsplit y).2, mul_add]
  refine ⟨(hiG.add hiF).congr (Eventually.of_forall fun y ↦ (he y).symm), ?_⟩
  change Complex.I * (∫ y, W (s y) * logDeriv L (s y)) =
    Complex.I * (∫ y, W (s y) * logDeriv (heckeGammaFactor χ) (s y)) +
      Complex.I * (∫ y, W (s y) * logDeriv (finiteSeries(χ)) (s y))
  simp_rw [he]
  rw [integral_add hiG hiF, mul_add]

/-- Paper: Equation (B.4.2.7), p. 615.
The finite logarithmic derivative is the negative prime-power series. On a fixed
vertical line to the right of one, the moduli are bounded by the summable series
obtained by taking the trivial local character at every place. -/
private theorem heckeExplicitFormula_centeredLine_eulerSeries
    (χ : U[F]) (a : ℝ) (ha : 1 < a) :
    let x := fun j : Primes(F) × ℕ ↦ ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
    let c := fun j : Primes(F) × ℕ ↦ if χ₀(χ).IsUnramifiedAt j.1 then
      -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) else 0
    Summable (fun j ↦ Real.log q(j.1) * Real.exp (-a * x j)) ∧
      ∀ z : ℂ, z.re = a →
        HasSum (fun j ↦ c j * Complex.exp (-z * (x j : ℂ))) (logDeriv (finiteSeries(χ)) z) := by
  intro x c
  obtain ⟨r, hr, hra⟩ := exists_between ha
  let ε := a - r
  have hε : 0 < ε := sub_pos.mpr hra
  let J (j : Primes(F) × ℕ) := j.1.asIdeal ^ (j.2 + 1)
  have hJ : Injective J := by
    rintro ⟨v, n⟩ ⟨w, m⟩ h
    change v.asIdeal ^ (n + 1) = w.asIdeal ^ (m + 1) at h
    have hdvd : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow
      ((dvd_pow_self _ (Nat.succ_ne_zero n)).trans h.dvd)
    have hw : v = w := HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hdvd)).symm
    subst w
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot h))
  have hq (v : Primes(F)) : 1 < q(v) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ (v : Primes(F)) : 0 < q(v) := zero_lt_one.trans (hq v)
  let d (j : Primes(F) × ℕ) := Real.log q(j.1) * Real.exp (-a * x j)
  have hd (j : Primes(F) × ℕ) : 0 ≤ d j :=
    mul_nonneg (Real.log_nonneg (hq j.1).le) (Real.exp_nonneg _)
  have hdSum : Summable d := by
    refine (((summable_absNorm_rpow F hr).comp_injective hJ).div_const ε).of_nonneg_of_le hd ?_
    intro j
    let u : ℝ := (J j).absNorm
    have hu : u = q(j.1) ^ (j.2 + 1) := by simp [u, J, map_pow]
    have hu₀ : 0 < u := hu ▸ pow_pos (hq₀ j.1) _
    have hlog : Real.log u = x j := by rw [hu, Real.log_pow]
    have hlogq : Real.log q(j.1) ≤ Real.log u := by
      rw [hlog]
      apply le_mul_of_one_le_left (Real.log_nonneg (hq j.1).le)
      exact_mod_cast (Nat.succ_pos j.2)
    change d j ≤ u ^ (-r) / ε
    calc
      _ ≤ Real.log u * u ^ (-a) := by
        have hEq : Real.exp (-a * x j) = u ^ (-a) := by
          rw [Real.rpow_def_of_pos hu₀, hlog, mul_comm]
        dsimp only [d]
        rw [hEq]
        exact mul_le_mul_of_nonneg_right hlogq (Real.rpow_nonneg hu₀.le _)
      _ ≤ (u ^ ε / ε) * u ^ (-a) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hu₀.le hε) (Real.rpow_nonneg hu₀.le _)
      _ = _ := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hu₀, show ε + -a = -r by dsimp [ε]; ring]
  refine ⟨hdSum, fun z hz ↦ ?_⟩
  let b (v : Primes(F)) : ℂ := if χ₀(χ).IsUnramifiedAt v then (χ₀(χ)).localValue v else 0
  let U (v : Primes(F)) (w : ℂ) := b v * ((q(v) : ℝ) : ℂ) ^ (-w)
  have hb (v : Primes(F)) : ‖b v‖ ≤ 1 := by
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [b, h, norm_ideleClassNormTwist_zero_localValue]
  have hfactor (v : Primes(F)) :
      finiteHeckeEulerFactor χ v = fun w ↦ (1 - U v w)⁻¹ := by
    funext w
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [finiteHeckeEulerFactor, h, U, b]
  have hloc (v : Primes(F)) {w : ℂ} (hw : 1 < w.re) :
      DifferentiableAt ℂ (finiteHeckeEulerFactor χ v) w ∧ finiteHeckeEulerFactor χ v w ≠ 0 ∧
      logDeriv (finiteHeckeEulerFactor χ v) w = -((Real.log q(v) : ℝ) : ℂ) * U v w * (1 - U v w)⁻¹ ∧
      ‖U v w‖ < 1 := by
    have h₀ : ((q(v) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hq₀ v).ne'
    have hU : ‖U v w‖ < 1 := by
      unfold U
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hq₀ v), Complex.neg_re]
      exact (mul_le_of_le_one_left (Real.rpow_nonneg (hq₀ v).le _) (hb v)).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg (hq v) (by linarith))
    have hne : 1 - U v w ≠ 0 := fun h ↦ hU.ne (by rw [← sub_eq_zero.mp h, norm_one])
    have dU := ((hasDerivAt_id w).neg.const_cpow (Or.inl h₀)).const_mul (b v)
    change HasDerivAt (U v)
      (b v * (((q(v) : ℝ) : ℂ) ^ (-w) * Complex.log (q(v) : ℂ) * (-1))) w at dU
    have df := (dU.const_sub 1).inv hne
    change HasDerivAt (fun w ↦ (1 - U v w)⁻¹) _ w at df
    rw [hfactor]
    refine ⟨df.differentiableAt, inv_ne_zero hne, ?_, hU⟩
    rw [logDeriv_apply, df.deriv, ← Complex.ofReal_log (hq₀ v).le]
    change _ / (1 - U v w)⁻¹ = _
    field_simp [hne]
    dsimp [U]
    ring
  have hPow (v : Primes(F)) (n : ℕ) :
      Complex.exp (-z * (x (v, n) : ℂ)) = (((q(v) : ℝ) : ℂ) ^ (-z)) ^ (n + 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hq₀ v).ne'),
      ← Complex.exp_nat_mul, ← Complex.ofReal_log (hq₀ v).le]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hlocal (v : Primes(F)) :
      HasSum (fun n : ℕ ↦ c (v, n) * Complex.exp (-z * (x (v, n) : ℂ)))
        (logDeriv (finiteHeckeEulerFactor χ v) z) := by
    obtain ⟨-, -, hL, hU⟩ := hloc v (hz ▸ ha)
    rw [hL]
    apply ((hasSum_geometric_of_norm_lt_one hU).mul_left (-((Real.log q(v) : ℝ) : ℂ) * U v z)).congr_fun
    intro n
    rw [hPow, mul_assoc, ← pow_succ']
    simp only [U, mul_pow]
    dsimp only [c, b]
    split_ifs <;> simp [pow_succ] <;> ring
  obtain ⟨t, ht, htz⟩ := exists_between (show 1 < z.re from hz ▸ ha)
  let O := Complex.re ⁻¹' Ioi t
  have hO : IsOpen O := isOpen_Ioi.preimage Complex.continuous_re
  have hconv := (finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ ht).mono
    (show O ⊆ {w : ℂ | t ≤ w.re} from fun w (hw : t < w.re) ↦ hw.le)
  have hn : finiteSeries(χ) z ≠ 0 :=
    finiteHeckeL_ne_zero_of_one_lt_re χ ⟨z, show 1 < z.re from hz ▸ ha⟩
  have hplaces : HasSum (fun v ↦ logDeriv (finiteHeckeEulerFactor χ v) z) (logDeriv (finiteSeries(χ)) z) := by
    apply (Complex.logDeriv_tendsto hO (show z ∈ O from htz) hconv.tendstoLocallyUniformlyOn
      (.of_forall fun S ↦ DifferentiableOn.fun_finsetProd fun v _ w hw ↦
        (hloc v (ht.trans hw)).1.differentiableWithinAt) hn).congr
    intro S
    exact logDeriv_fun_prod (fun v _ ↦ (hloc v (hz ▸ ha)).2.1) (fun v _ ↦ (hloc v (hz ▸ ha)).1)
  have hsum : Summable (fun j ↦ c j * Complex.exp (-z * (x j : ℂ))) := by
    apply hdSum.of_norm_bounded
    intro j
    have hre : (-z * (x j : ℂ)).re = -a * x j := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re, hz]
    dsimp only [c, d]
    split_ifs
    · simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg (hq j.1).le),
        norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, mul_one, Complex.norm_exp, hre, le_refl]
    · simpa only [zero_mul, norm_zero] using hd j
  rw [← (hsum.hasSum.prod_fiberwise hlocal).unique hplaces]
  exact hsum.hasSum

/-- Mellin inversion integrates the Euler series term by term against a Schwartz
trace, with its samples supplied by the direct or reflected inversion formula. -/
private theorem heckeExplicitFormula_centeredLine_finiteLeg
    (χ : U[F]) (a : ℝ) (ha : 1 < a) (W : 𝓢(ℝ, ℂ)) (A : ℂ → ℂ) (P : ℝ → ℂ)
    (hW : ∀ y : ℝ, W y = A ((a : ℂ) + y * Complex.I))
    (hInv : ∀ x : ℝ, (∫ y : ℝ, W y * Complex.exp (-((a : ℂ) + y * Complex.I) * x)) /
      (2 * (Real.pi : ℂ)) = P x) :
    HasSum (fun j : Primes(F) × ℕ ↦ if χ₀(χ).IsUnramifiedAt j.1 then
      -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) *
        P (((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)) else 0)
      (verticalLineIntegral (fun s ↦ A s * logDeriv (finiteSeries(χ)) s) a / twoPiI) := by
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have hspan : Surjective (fun S : Finset (𝓞 F) ↦ Ideal.span (S : Set (𝓞 F))) :=
    fun I ↦ IsNoetherian.noetherian I
  let : Countable (Ideal (𝓞 F)) := hspan.countable
  let : Countable (Primes(F)) :=
    (show Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) from fun _ _ h ↦
      HeightOneSpectrum.ext h).countable
  let s (y : ℝ) : ℂ := (a : ℂ) + y * Complex.I
  let x (j : Primes(F) × ℕ) := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
  let c (j : Primes(F) × ℕ) : ℂ := if χ₀(χ).IsUnramifiedAt j.1 then
    -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) else 0
  let d (j : Primes(F) × ℕ) : ℝ := Real.log q(j.1) * Real.exp (-a * x j)
  let K (j : Primes(F) × ℕ) (y : ℝ) := W y * (c j * Complex.exp (-s y * (x j : ℂ)))
  obtain ⟨hs, hSeries⟩ := heckeExplicitFormula_centeredLine_eulerSeries χ a ha
  change Summable d at hs
  have hRe (y : ℝ) : (s y).re = a := by simp [s]
  have hlog (v : Primes(F)) : 0 ≤ Real.log q(v) := Real.log_nonneg
    (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le)
  have hbound (j : Primes(F) × ℕ) (y : ℝ) : ‖K j y‖ ≤ ‖W y‖ * d j := by
    change ‖W y * (c j * Complex.exp (-s y * (x j : ℂ)))‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hreal : (-s y * (x j : ℂ)).re = -a * x j := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.neg_re, hRe]
    dsimp only [c, d]
    split_ifs
    · simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (hlog _),
        norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, mul_one, Complex.norm_exp, hreal,
        le_refl]
    · rw [zero_mul, norm_zero]
      exact mul_nonneg (hlog _) (Real.exp_nonneg _)
  have hInt : HasSum (fun j ↦ ∫ y, K j y) (∫ y, W y * logDeriv (finiteSeries(χ)) (s y)) := by
    apply hasSum_integral_of_dominated_convergence (fun j y ↦ ‖W y‖ * d j)
    · intro j
      apply Continuous.aestronglyMeasurable
      unfold K s
      fun_prop
    · exact fun j ↦ Eventually.of_forall (hbound j)
    · exact Eventually.of_forall fun y ↦ hs.mul_left ‖W y‖
    · simp_rw [tsum_mul_left]
      exact W.integrable.norm.mul_const _
    · exact Eventually.of_forall fun y ↦ (hSeries (s y) (hRe y)).mul_left (W y)
  have hEval (j : Primes(F) × ℕ) :
      (∫ y, K j y) / (2 * (Real.pi : ℂ)) = c j * P (x j) := by
    have he (y : ℝ) : K j y = c j * (W y * Complex.exp (-s y * (x j : ℂ))) := by
      exact mul_left_comm _ _ _
    simp_rw [he]
    rw [integral_const_mul, mul_div_assoc, hInv]
  have h := hInt.div_const (2 * (Real.pi : ℂ))
  simp_rw [hEval, hW] at h
  have hTerm (j : Primes(F) × ℕ) : c j * P (x j) = if χ₀(χ).IsUnramifiedAt j.1 then
      -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) * P (x j) else 0 := by
    by_cases h : χ₀(χ).IsUnramifiedAt j.1 <;> simp [c, h]
  simp_rw [hTerm] at h
  change HasSum _ ((Complex.I * (∫ y, A (s y) * logDeriv (finiteSeries(χ)) (s y))) / twoPiI)
  rw [mul_comm Complex.I, mul_div_mul_right _ _ Complex.I_ne_zero]
  exact h

/-- Paper: Theorem B.4.2.2, p. 616, and (B.4.2.5)–(B.4.2.11), p. 615.
The two finite logarithmic derivatives on the right-hand line give the sum
over unramified prime powers. Both Mellin inversions have weight `q^(-m/2)`. -/
private theorem heckeExplicitFormula_centeredLine_finite
    (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) (ha : 1 < a) :
    (verticalLineIntegral (fun s ↦ logMellin f (s - 1 / 2) * logDeriv (finiteSeries(χ)) s) a +
      verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv (finiteSeries(χ⁻¹)) s) a) /
        twoPiI = -(∑' j, primeTerm(χ, f) j) := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f hf
  obtain ⟨W, hW, hInvW⟩ := realHeckeArchimedean_mellinLogDeriv_trace g hg a
  obtain ⟨V, hV, hInvV⟩ := realHeckeArchimedean_mellinLogDeriv_reflect g hg a
  have hshift := heckeExplicitFormula_centeredLine_mellin f g hgf
  have hshift' (z : ℂ) : logMellin g (1 - z) = logMellin f (1 / 2 - z) := by
    rw [hshift, show 1 - z - 1 / 2 = 1 / 2 - z by ring]
  have hD := heckeExplicitFormula_centeredLine_finiteLeg χ a ha W
    (fun s ↦ logMellin f (s - 1 / 2)) g (fun y ↦ (hW y).trans (hshift _)) hInvW
  have hR := heckeExplicitFormula_centeredLine_finiteLeg χ⁻¹ a ha V
    (fun s ↦ logMellin f (1 / 2 - s)) (fun x ↦ Complex.exp (-(x : ℂ)) * g (-x))
    (fun y ↦ (hV y).trans (hshift' _)) hInvV
  have hreflect (x : ℝ) : Complex.exp (-(x : ℂ)) * g (-x) = (Real.exp (-x / 2) : ℂ) * f (-x) := by
    rw [hgf, ← mul_assoc, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hterm (j : Primes(F) × ℕ) :
      let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
      ((if χ₀(χ).IsUnramifiedAt j.1 then
        -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) * g x else 0) +
        (if χ₀(χ⁻¹).IsUnramifiedAt j.1 then
          -(Real.log q(j.1) : ℂ) * (χ₀(χ⁻¹).localValue j.1) ^ (j.2 + 1) *
            (Complex.exp (-(x : ℂ)) * g (-x)) else 0)) = -primeTerm(χ, f) j := by
    intro x
    rw [show (χ₀(χ⁻¹)).IsUnramifiedAt j.1 ↔ (χ₀(χ)).IsUnramifiedAt j.1 from
      inverse_unramified j.1 χ]
    change _ = -(ite _ _ (0 : ℂ))
    split_ifs
    · rw [hreflect, hgf]
      simp only [Complex.ofReal_mul]
      ring
    · simp
  have h := (hD.add hR).congr_fun fun j ↦ (hterm j).symm
  rw [add_div, ← h.tsum_eq, tsum_neg]

/-- The same half weight shifts the gamma-kernel arguments in opposite directions. -/
private theorem heckeExplicitFormula_centeredLine_kernel
    (f g : 𝓢(ℝ, ℂ)) (hgf : ∀ x : ℝ, g x = (Real.exp (-x / 2) : ℂ) * f x)
    (k : ℝ) (z₁ z₂ : ℂ) (t : ℝ) :
    heckeArchimedeanDigammaKernel k z₁ z₂ g t =
      heckeArchimedeanDigammaKernel k (z₁ + (k : ℂ) / 2) (z₂ - (k : ℂ) / 2) f t := by
  have h₁ : g (k * t) * Complex.exp (-z₁ * (t : ℂ)) =
      f (k * t) * Complex.exp (-(z₁ + (k : ℂ) / 2) * t) := by
    rw [hgf, Complex.ofReal_exp, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h₂ : g (-(k * t)) * Complex.exp (-z₂ * (t : ℂ)) =
      f (-(k * t)) * Complex.exp (-(z₂ - (k : ℂ) / 2) * t) := by
    rw [hgf, Complex.ofReal_exp, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h₀ : g 0 = f 0 := by simp [hgf]
  simp only [heckeArchimedeanDigammaKernel, h₁, h₂, h₀]

/-- Paper: Proposition B.4.2.1 and Theorem B.4.2.2, p. 616.
The gamma factors give the sum of the real and complex local digamma terms.
Use the exponentially tilted test so that the two Mellin transforms are centred. -/
private theorem heckeExplicitFormula_centeredLine_gamma
    (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) (ha : 1 < a) :
    (verticalLineIntegral (fun s ↦ logMellin f (s - 1 / 2) * logDeriv (heckeGammaFactor χ) s) a +
      verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv (heckeGammaFactor χ⁻¹) s) a) /
        twoPiI =
        ∑ w : InfinitePlace F, if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f hf
  let G (ψ : U[F]) (w : InfinitePlace F) (s : ℂ) : ℂ :=
    if hw : w.IsReal then
      let p := (realHeckeCharacter_parameters ψ w hw).exists.choose
      Complex.Gammaℝ (s + p.1 + p.2.val)
    else
      let p := (complexHeckeCharacter_parameters ψ w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
      Complex.Gammaℂ (s + p.1 + (p.2.natAbs : ℂ) / 2) / 2
  let ρ (ψ : U[F]) (w : InfinitePlace F) : PontryaginDual w.Completionˣ :=
    ψ.comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩
  have hρ (ψ : U[F]) (w : InfinitePlace F) (u : w.Completionˣ) :
      (ρ ψ w u : ℂ) = infinitePlaceRestriction F w (χ₀(ψ)) u := by
    change (ψ _ : ℂ) = (ψ _ : ℂ) * _ ^ (0 : ℂ)
    rw [Complex.cpow_zero, mul_one]
  have hρinv (w : InfinitePlace F) : ρ χ⁻¹ w = (ρ χ w)⁻¹ := by
    ext1 u
    rfl
  have hReal (ψ : U[F]) (w : InfinitePlace F) (hw : w.IsReal) :
      (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex (ρ ψ w))).exists.choose =
        (realHeckeCharacter_parameters ψ w hw).exists.choose := by
    apply (realLocalEulerParameters w hw _).unique (realLocalEulerParameters w hw _).exists.choose_spec
    intro x
    change (ρ ψ w _ : ℂ) = _
    rw [hρ]
    exact (realHeckeCharacter_parameters ψ w hw).exists.choose_spec.2 x
  have hComplex (ψ : U[F]) (w : InfinitePlace F) (hw : w.IsComplex) :
      (complexLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex (ρ ψ w))).exists.choose =
        (complexHeckeCharacter_parameters ψ w hw).exists.choose := by
    apply (complexLocalEulerParameters w hw _).unique (complexLocalEulerParameters w hw _).exists.choose_spec
    intro x
    change (ρ ψ w _ : ℂ) = _
    rw [hρ]
    exact (complexHeckeCharacter_parameters ψ w hw).exists.choose_spec.2 x
  have hG (ψ : U[F]) (w : InfinitePlace F) :
      G ψ w = infiniteLocalEulerFactor w ∘ localChart(w, ρ ψ w) := by
    by_cases hw : w.IsReal
    · have h := (realHeckeArchimedean_mellinLogDeriv_parameters w hw (ρ ψ w)).2.1
      rw [hReal] at h
      simpa only [G, dite_eq_left hw, add_assoc] using h.symm
    · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hp := (complexLocalEulerParameters w hc
        (ContinuousMonoidHom.comp circleToComplex (ρ ψ w))).exists.choose_spec
      rw [hComplex] at hp
      have h := complexHeckeArchimedean_mellinLogDeriv_factor w hc (ρ ψ w) _ _ hp
      simpa only [G, dite_eq_right hw, hc, add_assoc] using h.symm
  let H (w : InfinitePlace F) (s : ℂ) :=
    logMellin g s * logDeriv (G χ w) s + logMellin g (1 - s) * logDeriv (G χ⁻¹ w) s
  have hg₀ : g 0 = f 0 := by simp [hgf]
  have hlocal (w : InfinitePlace F) : Complex.VerticalIntegrable (H w) a ∧
      verticalLineIntegral (H w) a / twoPiI =
        if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
    by_cases hw : w.IsReal
    · obtain ⟨hi, -, hv⟩ := realHeckeArchimedean_mellinLogDeriv w hw (ρ χ w) g hg a ha
      rw [hReal] at hv
      simp only [H, hG, hρinv, dite_eq_left hw]
      refine ⟨hi, hv.trans ?_⟩
      rw [hg₀]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [heckeExplicitFormula_centeredLine_kernel f g hgf]
      congr 2 <;> push_cast <;> ring
    · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      obtain ⟨hi, -, hv⟩ := complexHeckeArchimedean_mellinLogDeriv w hc (ρ χ w) g hg a ha
      rw [hComplex] at hv
      simp only [H, hG, hρinv, dite_eq_right hw]
      refine ⟨hi, hv.trans ?_⟩
      rw [hg₀]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [heckeExplicitFormula_centeredLine_kernel f g hgf]
      congr 1 <;> push_cast <;> ring
  let s (y : ℝ) : ℂ := (a : ℂ) + y * Complex.I
  have hregular (ψ : U[F]) (w : InfinitePlace F) (y : ℝ) :
      G ψ w (s y) ≠ 0 ∧ DifferentiableAt ℂ (G ψ w) (s y) := by
    by_cases hw : w.IsReal
    · let p := (realHeckeCharacter_parameters ψ w hw).exists.choose
      let b := p.1 + (p.2.val : ℂ)
      have hp : p.1.re = 0 := (realHeckeCharacter_parameters ψ w hw).exists.choose_spec.1
      have hb : 0 < (s y + b).re := by
        simp only [s, b, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
          neg_zero, add_zero, hp, Complex.natCast_re, zero_add]
        positivity
      simpa only [G, dite_eq_left hw, b, p, add_assoc] using
        completedHeckeL_logDeriv_GammaR_regular b (s y) hb
    · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let p := (complexHeckeCharacter_parameters ψ w hc).exists.choose
      let b := p.1 + (p.2.natAbs : ℂ) / 2
      have hp : p.1.re = 0 := (complexHeckeCharacter_parameters ψ w hc).exists.choose_spec.1
      have hb : 0 < (s y + b).re := by
        simp only [s, b, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
          neg_zero, add_zero, hp, Complex.div_ofNat_re, Complex.natCast_re, zero_add]
        positivity
      simpa only [G, dite_eq_right hw, hc, b, p, add_assoc] using
        (completedHeckeL_logDeriv_GammaC_split b (s y) hb).1
  have hprod (ψ : U[F]) (y : ℝ) :
      logDeriv (heckeGammaFactor ψ) (s y) = ∑ w, logDeriv (G ψ w) (s y) := by
    change logDeriv (fun z ↦ ∏ w, G ψ w z) (s y) = _
    exact logDeriv_fun_prod (fun w _ ↦ (hregular ψ w y).1) (fun w _ ↦ (hregular ψ w y).2)
  have hsum (y : ℝ) : (∑ w, H w (s y)) =
      logMellin g (s y) * logDeriv (heckeGammaFactor χ) (s y) +
        logMellin g (1 - s y) * logDeriv (heckeGammaFactor χ⁻¹) (s y) := by
    simp only [H, hprod, Finset.mul_sum, Finset.sum_add_distrib]
  have hi (ψ : U[F]) (W : 𝓢(ℝ, ℂ)) (A : ℂ → ℂ)
      (hW : ∀ y, W y = A (s y)) :
      Integrable (fun y ↦ A (s y) * logDeriv (heckeGammaFactor ψ) (s y)) := by
    have hcont : Continuous (fun y ↦ logDeriv (heckeGammaFactor ψ) (s y)) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      have hs : 0 < (s y).re := by simpa [s] using zero_lt_one.trans ha
      have hA : AnalyticAt ℂ (heckeGammaFactor ψ) (s y) :=
        DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
          (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos ψ hz).differentiableWithinAt)
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      exact (hA.deriv.div hA (heckeGammaFactor_ne_zero_of_re_pos ψ hs)).continuousAt.comp
        (by dsimp [s]; fun_prop)
    obtain ⟨C, -, hC⟩ := completedHeckeL_logDeriv_gammaFactor_bound ψ a (zero_lt_one.trans ha)
    exact (heckeExplicitFormula_centeredLine_integrable W _ hcont C hC).congr
      (Eventually.of_forall fun y ↦ congrArg (fun z ↦ z * logDeriv (heckeGammaFactor ψ) (s y)) (hW y))
  obtain ⟨W, hW, -⟩ := realHeckeArchimedean_mellinLogDeriv_trace g hg a
  obtain ⟨V, hV, -⟩ := realHeckeArchimedean_mellinLogDeriv_reflect g hg a
  have hSumInt :
      (∫ y : ℝ, ∑ w, H w (s y)) = ∑ w, ∫ y : ℝ, H w (s y) :=
    integral_finsetSum _ fun w _ ↦ (hlocal w).1
  have hshift := heckeExplicitFormula_centeredLine_mellin f g hgf
  have hshift' (z : ℂ) : logMellin g (1 - z) = logMellin f (1 / 2 - z) := by
    rw [hshift, show 1 - z - 1 / 2 = 1 / 2 - z by ring]
  simp_rw [← hshift, ← hshift']
  change (Complex.I * (∫ y, logMellin g (s y) * logDeriv (heckeGammaFactor χ) (s y)) +
    Complex.I * (∫ y, logMellin g (1 - s y) * logDeriv (heckeGammaFactor χ⁻¹) (s y))) / twoPiI = _
  rw [← mul_add, ← integral_add (hi χ W (logMellin g) hW)
    (hi χ⁻¹ V (fun z ↦ logMellin g (1 - z)) hV)]
  simp_rw [← hsum]
  rw [hSumInt, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun w _ ↦ (hlocal w).2

/-- Paper: Theorem B.4.2.2, p. 616, with (B.4.2.5)–(B.4.2.11) and Proposition B.4.2.1,
pp. 615–616. On a line `Re s = a` with `1 < a ≤ 2`, the centred Mellin transform `Φ(s - 1/2)`
paired with `L'/L`, plus the reflected centred transform `Φ(1/2 - s)` paired with the dual
`L'/L`, divided by `2πi`, equals minus the prime-power series plus the archimedean digamma
terms; the reflected product is integrable on the line.
Deviation: The finite part is the Euler product expansion (B.4.2.5)–(B.4.2.7) integrated
termwise by Mellin inversion, with the normalizations of F36 (both samples carry the centred
weight `q^(-m/2) log q`). The archimedean part is `realHeckeArchimedean_mellinLogDeriv` and
`complexHeckeArchimedean_mellinLogDeriv` applied to the centred profile `x ↦ exp(-x/2) f x`,
whose twist moves into the digamma kernel parameters, with `realHeckeCharacter_parameters`
and `complexHeckeCharacter_parameters` identified with the local Euler parameters of the
restriction of `χ` to the place. -/
theorem heckeExplicitFormula_centeredLine (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (L Ldual : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualAgree : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s)
    (a : ℝ) (ha : 1 < a) (haMax : a ≤ 2) :
    Complex.VerticalIntegrable (fun s ↦ logMellin f (1 / 2 - s) * logDeriv Ldual s) a ∧
      (verticalLineIntegral (fun s ↦ logMellin f (s - 1 / 2) * logDeriv L s) a +
        verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv Ldual s) a) / twoPiI =
      -(∑' j, primeTerm(χ, f) j) +
        ∑ w : InfinitePlace F, if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f hf
  have hshift := heckeExplicitFormula_centeredLine_mellin f g hgf
  obtain ⟨W, hW, -⟩ := realHeckeArchimedean_mellinLogDeriv_trace g hg a
  obtain ⟨V, hV, -⟩ := realHeckeArchimedean_mellinLogDeriv_reflect g hg a
  have hW' (y : ℝ) : W y = logMellin f (((a : ℂ) + y * Complex.I) - 1 / 2) :=
    (hW y).trans (hshift _)
  have hV' (y : ℝ) : V y = logMellin f (1 / 2 - ((a : ℂ) + y * Complex.I)) := by
    rw [hV y, hshift]
    congr 1
    ring
  obtain ⟨-, hd⟩ := heckeExplicitFormula_centeredLine_decompose χ L hL hAgree a ha
    (fun s ↦ logMellin f (s - 1 / 2)) W hW'
  obtain ⟨hi, hr⟩ := heckeExplicitFormula_centeredLine_decompose χ⁻¹ Ldual hLdual hDualAgree
    a ha (fun s ↦ logMellin f (1 / 2 - s)) V hV'
  refine ⟨hi, ?_⟩
  rw [hd, hr, add_add_add_comm, add_div, heckeExplicitFormula_centeredLine_gamma χ f hf a ha,
    heckeExplicitFormula_centeredLine_finite χ f hf a ha, add_comm]

/-- Paper: Theorem B.4.2.2, p. 616. The centered divisor sum equals the
discriminant–conductor term, minus the prime-power series, plus the gamma terms.
Deviation: Signed meromorphic orders count zeros and the actual poles of the
norm twist. The archimedean terms use the convergent digamma kernel with the
local sign parity or angular weight from §3.2. -/
theorem hasSum_heckeExplicitFormula (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    HasSum (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f (ρ - 1 / 2))
      ((heckeLogDiscriminantConductor χ : ℂ) * f 0 - (∑' j, primeTerm(χ, f) j) +
        ∑ w : InfinitePlace F, if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0) := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f _hf
  -- The Mellin transform of the centred profile is the shifted Mellin transform.
  have hshift (s : ℂ) : logMellin g s = logMellin f (s - 1 / 2) := by
    have h1 : logMellin g s =
        mellin (fun t : ℝ ↦ (t : ℂ) ^ (-(1 / 2 : ℂ)) • f (Real.log t)) s := by
      show ∫ t in Ioi (0 : ℝ), _ = ∫ t in Ioi (0 : ℝ), _
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht' : (0 : ℝ) < t := ht
      simp only [hgf, smul_eq_mul]
      congr 2
      rw [show -Real.log t / 2 = Real.log t * (-(1 / 2 : ℝ)) by ring, ← Real.rpow_def_of_pos ht',
        Complex.ofReal_cpow ht'.le]
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [h1, mellin_cpow_smul, sub_eq_add_neg]
  have hfun : (fun s ↦ logMellin g s * logDeriv L s) =
      fun s ↦ logMellin f (s - 1 / 2) * logDeriv L s := funext fun s ↦ by rw [hshift]
  obtain ⟨Ldual, hLdual, hDualAgree⟩ := completedHeckeL_exists_continuation χ⁻¹
  obtain ⟨-, -, hsum⟩ :=
    hasSum_heckeAsymptoticResidue χ g hg L _hL _hAgree (3 / 2) (by norm_num) (by norm_num)
  obtain ⟨hintDual, hline⟩ := heckeExplicitFormula_centeredLine χ f _hf L Ldual _hL _hAgree hLdual
    hDualAgree (3 / 2) (by norm_num) (by norm_num)
  set κ : ℂ := (heckeLogDiscriminantConductor χ : ℂ) with hκ
  have hΦgInt : Complex.VerticalIntegrable (logMellin g) (1 - 3 / 2) :=
    (uniformlySchwartzOnStrip_mellin_of_exponentialDecay g hg (-2) 2 (by norm_num)).verticalIntegrable
      _ ⟨by norm_num, by norm_num⟩
  -- On the left line the reflection formula turns the integrand around.
  have hleft (y : ℝ) :
      logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
          logDeriv L (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        -(logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) -
          κ * logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    set s : ℂ := ((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I with hs
    set s' : ℂ := ((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I with hs'
    have hsre : s.re < 0 := by
      simp [hs]
      norm_num
    have hord := hasSum_heckeAsymptoticResidue_order_left χ L _hL _hAgree s hsre
    have hrefl := completedHeckeL_logDeriv_reflection χ L Ldual _hL _hAgree hLdual hDualAgree s hord
    have h1s : 1 - s = s' := by
      simp only [hs, hs']
      push_cast
      ring
    have h1s' : 1 / 2 - s' = s - 1 / 2 := by
      rw [← h1s]
      ring
    rw [hrefl, h1s, h1s', ← hshift]
    ring
  have hVleft : verticalLineIntegral (fun s ↦ logMellin g s * logDeriv L s) (1 - 3 / 2) =
      -(verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv Ldual s) (3 / 2)) -
        κ * verticalLineIntegral (logMellin g) (1 - 3 / 2) := by
    have hintDual' : Integrable (fun y : ℝ ↦
        logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := hintDual
    have hF := hintDual'.comp_neg
    have hΦ : Integrable (fun y : ℝ ↦ logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) :=
      hΦgInt
    show Complex.I * (∫ y : ℝ, _) = -(Complex.I * (∫ y : ℝ, _)) - κ * (Complex.I * (∫ y : ℝ, _))
    beta_reduce
    rw [integral_congr_ae (Eventually.of_forall hleft),
      integral_sub (f := fun y : ℝ ↦ -((fun y : ℝ ↦
        logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (-y)))
        (g := fun y : ℝ ↦ κ * logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        hF.neg (hΦ.const_mul κ),
      integral_neg, integral_const_mul, integral_neg_eq_self (fun y : ℝ ↦
        logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))]
    ring
  have hκterm : verticalLineIntegral (logMellin g) (1 - 3 / 2) / twoPiI = f 0 := by
    rw [verticalLineIntegral_div_eq_mellinInv_one _ _ hΦgInt,
      mellinInv_mellin_eq (1 - 3 / 2 : ℝ) (fun t : ℝ ↦ g (Real.log t)) one_pos
        (mellinConvergent_of_exponentialDecay g hg _) hΦgInt
        (g.continuous.continuousAt.comp (Real.continuousAt_log one_ne_zero))]
    simp [hgf]
  rw [show (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f (ρ - 1 / 2)) =
      fun ρ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin g ρ from
    funext fun ρ ↦ by rw [hshift]]
  convert hsum using 1
  rw [hVleft, hfun]
  linear_combination -hline - κ * hκterm

end MellinExplicitFormula

local notation "𝒮ₐ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "𝒟(" G ")" => BruhatCompactSupport G
local notation "addTest(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "μ𝔭(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ν𝔭(" v ")" => finiteLocalAdditiveTamagawaMeasure F v
local notation "ν∞(" w ")" => infiniteLocalAdditiveTamagawaMeasure F w
local notation "ψ𝔭(" v ")" => finiteLocalStandardCharacter F v
local notation "ψ∞(" w ")" => (fun x ↦ adeleStandardCharacter F
  (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "V𝔭(" v ")" => ((μ𝔭(v) (O(v)).units).toReal)
local notation "finiteWeilScale(" v ")" => ((Real.log q(v) / V𝔭(v) : ℝ) : ℂ)

-- Use the local-field topology and Borel measures of Appendix A.
local instance instFiniteCompletionUnitsLocallyCompactSec4b (v : Primes(F)) :
    LocallyCompactSpace (v.adicCompletion F)ˣ :=
  letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  inferInstance

local instance instFiniteCompletionMeasurableSec4b (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance instFiniteCompletionUnitsMeasurableSec4b (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance instInfiniteCompletionMeasurableSec4b (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _
local instance instIdeleClassT2Sec4b : T2Space C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSec4b : LocallyCompactSpace C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassMeasurableSec4b : MeasurableSpace C[F] := borel _
local instance instNormOneIdeleClassMeasurableSec4b :
    MeasurableSpace (MonoidHom.ker (ideleClassNorm F)) := borel _

local notation "J𝔭(" v ")" =>
  (fun y : HeightOneSpectrum.adicCompletion F v ↦ (Real.log ‖y‖ / Real.log q(v) : ℝ))
local notation "J∞(" w ")" =>
  (fun y : InfinitePlace.Completion w ↦ Real.log (‖y‖ ^ InfinitePlace.mult w))
local notation "logFourierIntegrand(" ν ", " ψ ", " J ", " f ")" =>
  (fun y ↦ ((J y : ℝ) : ℂ) * tamagawaFourier ν ψ f y)

section LocalScaling

open scoped Pointwise

local instance instFiniteCompletionLocallyCompactSec4bScaling (v : Primes(F)) :
    LocallyCompactSpace (v.adicCompletion F) :=
  letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  inferInstance

/-- The Haar character of multiplication by a unit on a finite completion is the norm.
The multiplicative measure is invariant and has density the inverse norm, which compares
the additive masses of the unit sphere and of its dilate. -/
private theorem finiteLocalAdditive_distribHaarChar (v : Primes(F))
    (w : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) w = ‖w.val‖₊ := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  let ν : Measure K := ν𝔭(v)
  let : ν.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : ν.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  have he := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let C : ENNReal := (v.asIdeal.absNorm : ENNReal) / ((v.asIdeal.absNorm : ENNReal) - 1)
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hC0 : C ≠ 0 := ENNReal.div_ne_zero.mpr ⟨(zero_lt_one.trans hq).ne',
    ENNReal.sub_ne_top (ENNReal.natCast_ne_top _)⟩
  have hCtop : C ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt hq).ne'
  -- Away from zero the multiplicative mass is `C` times the inverse-norm integral.
  have hmass (A : Set K) (hA : MeasurableSet A) (h0 : (0 : K) ∉ A) :
      μ𝔭(v) (Units.val ⁻¹' A) = C * ∫⁻ x in A, (↑‖x‖₊ : ENNReal)⁻¹ ∂ν := by
    have hsub : A ⊆ range (Units.val : Kˣ → K) := fun x hx ↦
      ⟨Units.mk0 x (fun h ↦ h0 (h ▸ hx)), rfl⟩
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, smul_apply, smul_eq_mul,
      he.comap_apply, image_preimage_eq_of_subset hsub, withDensity_apply _ hA]
  let S : Set K := Metric.sphere 0 1
  have hSo : IsOpen S := IsUltrametricDist.isOpen_sphere (0 : K) one_ne_zero
  have hS0 : (0 : K) ∉ S := by simp [S]
  have hSν0 : ν S ≠ 0 := (hSo.measure_pos ν ⟨1, by simp [S]⟩).ne'
  have hSνtop : ν S ≠ ⊤ := (isCompact_sphere (0 : K) 1).measure_lt_top.ne
  have hwS : w • S = Metric.sphere 0 ‖w.val‖ := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem, Units.smul_def, mem_sphere_zero_iff_norm,
      mem_sphere_zero_iff_norm, smul_eq_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      inv_mul_eq_one₀ (norm_ne_zero_iff.mpr w.ne_zero), eq_comm]
  have hwSm : MeasurableSet (w • S) := hSo.measurableSet.const_smul w
  have hw0 : (0 : K) ∉ w • S := by
    rw [hwS, mem_sphere_zero_iff_norm, norm_zero]
    exact (norm_pos_iff.mpr w.ne_zero).ne
  have hwn : (↑‖w.val‖₊ : ENNReal) ≠ 0 := by simp [w.ne_zero]
  apply distribHaarChar_eq_of_measure_smul_eq_mul hSν0 hSνtop
  have hinv : μ𝔭(v) (Units.val ⁻¹' (w • S)) = μ𝔭(v) (Units.val ⁻¹' S) := by
    have hpre : Units.val ⁻¹' (w • S) = (fun u ↦ w⁻¹ * u) ⁻¹' (Units.val ⁻¹' S) := by
      ext u
      simp only [mem_preimage, Units.val_mul, Units.smul_def]
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ w.ne_zero, smul_eq_mul, Units.val_inv_eq_inv_val]
    rw [hpre, measure_preimage_mul]
  rw [hmass _ hwSm hw0, hmass _ hSo.measurableSet hS0,
    setLIntegral_congr_fun hwSm (g := fun _ ↦ (↑‖w.val‖₊ : ENNReal)⁻¹) (fun x hx ↦ by
      rw [hwS, mem_sphere_zero_iff_norm] at hx
      simp only [show ‖x‖₊ = ‖w.val‖₊ from NNReal.eq hx]),
    setLIntegral_congr_fun hSo.measurableSet (g := fun _ ↦ (1 : ENNReal)) (fun x hx ↦ by
      rw [mem_sphere_zero_iff_norm] at hx
      simp [show ‖x‖₊ = 1 from NNReal.eq hx]),
    setLIntegral_const, setLIntegral_const, one_mul] at hinv
  have h := (ENNReal.mul_right_inj hC0 hCtop).mp hinv
  calc ν (w • S) = ↑‖w.val‖₊ * ((↑‖w.val‖₊ : ENNReal)⁻¹ * ν (w • S)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hwn ENNReal.coe_ne_top, one_mul]
    _ = _ := by rw [h]

/-- Multiplication by a unit pushes additive Tamagawa measure forward to its multiple by
the inverse norm. -/
private theorem finiteLocalAdditive_map_mul (v : Primes(F)) (u : (v.adicCompletion F)ˣ) :
    (ν𝔭(v)).map (u.val * ·) = ENNReal.ofReal ‖u.val‖⁻¹ • ν𝔭(v) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := ν𝔭(v)
  let : ν.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : ν.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, smul_apply, smul_eq_mul]
  have hpre : (u.val * ·) ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [mem_preimage, Set.mem_inv_smul_set_iff]
    rfl
  rw [hpre, ← distribHaarChar_mul, finiteLocalAdditive_distribHaarChar, Units.val_inv_eq_inv_val,
    nnNorm_inv, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, coe_nnNorm]

/-- Integrals against additive Tamagawa measure change by the inverse norm under dilation. -/
private theorem finiteLocalAdditive_integral_comp_mul (v : Primes(F))
    (u : (v.adicCompletion F)ˣ) (h : v.adicCompletion F → ℂ) :
    (∫ y, h (u.val * y) ∂ν𝔭(v)) = (‖u.val‖⁻¹ : ℝ) • ∫ z, h z ∂ν𝔭(v) := by
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let e := (Homeomorph.mulLeft₀ u.val u.ne_zero).toMeasurableEquiv
  calc (∫ y, h (u.val * y) ∂ν𝔭(v)) = ∫ y, h (e y) ∂ν𝔭(v) := rfl
    _ = ∫ z, h z ∂((ν𝔭(v)).map e) := (integral_map_equiv e h).symm
    _ = _ := by
      rw [show ⇑e = (u.val * · : _ → _) from rfl, finiteLocalAdditive_map_mul,
        integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _))]

/-- Integrability against additive Tamagawa measure is invariant under dilation. -/
private theorem finiteLocalAdditive_integrable_comp_mul (v : Primes(F))
    (u : (v.adicCompletion F)ˣ) {h : v.adicCompletion F → ℂ} (hh : Integrable h ν𝔭(v)) :
    Integrable (fun y ↦ h (u.val * y)) ν𝔭(v) := by
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let e := (Homeomorph.mulLeft₀ u.val u.ne_zero).toMeasurableEquiv
  have h' : Integrable h ((ν𝔭(v)).map e) := by
    rw [show ⇑e = (u.val * · : _ → _) from rfl, finiteLocalAdditive_map_mul]
    exact hh.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_equiv e h).mp h'

/-- Fourier inversion at zero: the Fourier transform of an additive test is integrable,
with integral the value of the test at zero. -/
private theorem finiteLocal_integral_tamagawaFourier (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)) ν𝔭(v) ∧
      (∫ y, tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) = addTest(f) 0 := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨e, he, hP⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let μ : Measure G := ν𝔭(v)
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  have hinv := schwartzBruhat_inverse_integral μ _ hP f 1
  have hF (y : K) : lcaFourier μ f (e (Multiplicative.ofAdd y)) =
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y :=
    (tamagawaFourier_eq_lcaFourier _ _ _ y _ fun x ↦ (he y x).trans
      (congrArg _ (mul_comm y x))).symm
  let E := e.toHomeomorph.toMeasurableEquiv
  obtain ⟨hI, hval⟩ := hinv
  simp only [map_one, Circle.coe_one, mul_one] at hI hval
  change Integrable _ (Measure.map E μ) at hI
  change _ = ∫ χ, _ ∂(Measure.map E μ) at hval
  rw [integral_map_equiv] at hval
  have hI' := (integrable_map_equiv E _).mp hI
  refine ⟨hI'.congr (ae_of_all _ fun y ↦ hF y.toAdd), ?_⟩
  refine (integral_congr_ae (ae_of_all _ fun y ↦ (hF y).symm)).trans (hval.symm.trans ?_)
  rfl


/-- The normalized logarithm transforms additively under dilation, away from zero. -/
private theorem finiteLog_mul (v : Primes(F)) (a : (v.adicCompletion F)ˣ)
    {y : v.adicCompletion F} (hy : y ≠ 0) :
    (((J𝔭(v) (a.val * y)) : ℝ) : ℂ) =
      ((J𝔭(v) y : ℝ) : ℂ) + ((Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) := by
  simp only [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr a.ne_zero) (norm_ne_zero_iff.mpr hy),
    add_div]
  push_cast
  ring

/-- Dilating the argument of the Fourier transform against the normalized logarithm
shifts the pairing by the logarithm of the dilation times the value at zero. -/
private theorem finiteLogFourier_comp_mul (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (a : (v.adicCompletion F)ˣ)
    (hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v)) :
    Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)) ν𝔭(v) ∧
    (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) ∂ν𝔭(v)) =
      (‖a.val‖⁻¹ : ℝ) • ((∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) -
        ((Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * addTest(f) 0) := by
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  obtain ⟨hFI, hF0⟩ := finiteLocal_integral_tamagawaFourier v f
  let L : ℂ := ((Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ)
  let φ := tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)
  let h : v.adicCompletion F → ℂ := fun z ↦ (((J𝔭(v) z : ℝ) : ℂ) - L) * φ z
  have hh : Integrable h ν𝔭(v) := by
    refine (hint.sub (hFI.const_mul L)).congr (ae_of_all _ fun z ↦ ?_)
    simp only [Pi.sub_apply, h, sub_mul]
    rfl
  have hae : (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) * φ (a.val * y)) =ᵐ[ν𝔭(v)]
      fun y ↦ h (a.val * y) := by
    have h0 : ∀ᵐ y ∂ν𝔭(v), y ≠ 0 := by
      have : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
        let := Valued.toNontriviallyNormedField (v.adicCompletion F) _
        exact NormedField.nhdsNE_neBot 0
      rw [ae_iff]
      simp
    filter_upwards [h0] with y hy0
    simp only [h, finiteLog_mul v a hy0, L, add_sub_cancel_right]
  refine ⟨(finiteLocalAdditive_integrable_comp_mul v a hh).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, finiteLocalAdditive_integral_comp_mul v a h]
  congr 1
  simp only [h, sub_mul]
  rw [integral_sub hint (hFI.const_mul L), integral_const_mul]
  change _ - L * ∫ y, φ y ∂ν𝔭(v) = _
  rw [hF0]

/-- Multiplicative integrability on the units is additive integrability against the
inverse norm. -/
private theorem finiteLocal_units_integrable_iff (v : Primes(F)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : v.adicCompletion F → E) :
    Integrable (fun u : (v.adicCompletion F)ˣ ↦ g u.val) μ𝔭(v) ↔
      Integrable (fun y ↦ ‖y‖⁻¹ • g y) ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let c : ENNReal := (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ENNReal)
  let d : K → ENNReal := fun x ↦ (↑‖x‖₊ : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂(ν𝔭(v).restrict (range (Units.val : Kˣ → K))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  have hdy (y : K) : (d y).toReal = ‖y‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hc0 : c ≠ 0 :=
    (ENNReal.div_pos (zero_lt_one.trans hq).ne' (ENNReal.sub_ne_top (ENNReal.natCast_ne_top _))).ne'
  have hct : c ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (tsub_pos_of_lt hq).ne').ne
  have hsupp : support (fun y ↦ ‖y‖⁻¹ • g y) ⊆ range (Units.val : Kˣ → K) := by
    intro y hy
    have : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y this, rfl⟩
  rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity]
  rw [integrable_smul_measure hc0 hct, show (fun u : Kˣ ↦ g u.val) = g ∘ Units.val from rfl,
    ← hval.integrable_map_iff (g := g), hval.map_comap,
    restrict_withDensity hval.measurableSet_range,
    integrable_withDensity_iff_integrable_smul' hd hdlt,
    ← integrableOn_iff_integrable_of_support_subset hsupp]
  simp_rw [hdy]
  rfl

/-- The Fourier transform of an additive test is again an additive test. -/
private theorem finiteLocal_exists_fourier_test (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F)) :
    ∃ g : 𝒮ₐ(v.adicCompletion F), ∀ y,
      addTest(g) y = tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, he, -⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let μ : Measure G := ν𝔭(v)
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_comp_equivCLM e
  refine ⟨P (T f), fun y ↦ ?_⟩
  calc P (T f) (Multiplicative.ofAdd y) = T f (e (Multiplicative.ofAdd y)) := hP _ _
    _ = lcaFourier μ f (e (Multiplicative.ofAdd y)) := (hT f).2 _
    _ = _ := (tamagawaFourier_eq_lcaFourier _ _ _ y _ fun x ↦ (he y x).trans
      (congrArg _ (mul_comm y x))).symm

/-- The logarithm of the norm is dominated by the sum of two square-root weights. -/
private theorem abs_log_le_two_mul_rpow {t : ℝ} (ht : 0 < t) :
    |Real.log t| ≤ 2 * (t⁻¹ * t ^ (1 / 2 : ℝ) + t⁻¹ * t ^ (3 / 2 : ℝ)) := by
  have e1 : t⁻¹ * t ^ (1 / 2 : ℝ) = t⁻¹ ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg_one, ← Real.rpow_add ht, ← Real.rpow_neg ht.le]
    norm_num
  have e2 : t⁻¹ * t ^ (3 / 2 : ℝ) = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    norm_num
  rw [e1, e2]
  have h1 := Real.log_le_rpow_div ht.le (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := Real.log_le_rpow_div (inv_pos.mpr ht).le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Real.log_inv] at h2
  have p1 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have p2 : 0 ≤ t⁻¹ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (inv_pos.mpr ht).le _
  rw [abs_le]
  constructor <;> linarith

/-- The normalized logarithm is integrable against every additive test. -/
private theorem finiteLog_integrable_mul_test (v : Primes(F)) (g : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) * addTest(g) y) ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : ProperSpace K := properSpace_adicCompletion v
  let h : K → ℂ := addTest(g)
  have hh : Continuous h := (schwartzBruhat_continuous g).comp continuous_ofAdd
  have hw (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : K ↦ ‖y‖⁻¹ • (‖h y‖ * ‖y‖ ^ s)) ν𝔭(v) := by
    refine (finiteLocal_units_integrable_iff v (fun y : K ↦ ‖h y‖ * ‖y‖ ^ s)).mp ?_
    have hz := finiteLocalIdelicZetaIntegral_integrable v g 1 (s := (s : ℂ)) (by simpa using hs)
    refine hz.norm.congr (ae_of_all _ fun u ↦ ?_)
    change ‖h u.val * _‖ = ‖h u.val‖ * ‖u.val‖ ^ s
    rw [norm_mul]
    congr 1
    change ‖((1 : PontryaginDual Kˣ) u : ℂ) *
      ((((Units.map (nnNormHom : K →*₀ ℝ≥0).toMonoidHom u : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (s : ℂ)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)),
      Complex.ofReal_re]
    rfl
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlq : 0 < Real.log q(v) := Real.log_pos hq
  refine (((hw _ (by norm_num : (0 : ℝ) < 1 / 2)).add
    (hw _ (by norm_num : (0 : ℝ) < 3 / 2))).const_mul (2 / Real.log q(v))).mono' ?_
    (ae_of_all _ fun y ↦ ?_)
  · exact (Measurable.aestronglyMeasurable (by fun_prop)).mul hh.aestronglyMeasurable
  · simp only [Pi.add_apply, smul_eq_mul]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlq]
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have ht : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hl := abs_log_le_two_mul_rpow ht
    calc |Real.log ‖y‖| / Real.log q(v) * ‖h y‖
        ≤ 2 * (‖y‖⁻¹ * ‖y‖ ^ (1 / 2 : ℝ) + ‖y‖⁻¹ * ‖y‖ ^ (3 / 2 : ℝ)) / Real.log q(v) * ‖h y‖ := by
          gcongr
      _ = _ := by ring

end LocalScaling

section LocalFourier

/-- Paper: Proposition B.4.3.1(1), p. 617. Dilation of the additive test
changes the Fourier transform of the normalized logarithm by a multiple of evaluation at zero. -/
theorem finiteLogFourier_dilate (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (a : (v.adicCompletion F)ˣ) :
    let K : (v.adicCompletion F → ℂ) → v.adicCompletion F → ℂ :=
      fun g ↦ logFourierIntegrand(ν𝔭(v), ψ𝔭(v), J𝔭(v), g)
    Integrable (K (addTest(f) ∘ (fun x ↦ a.inv * x))) ν𝔭(v) ∧
      Integrable (K addTest(f)) ν𝔭(v) ∧
      (∫ y, K (addTest(f) ∘ (fun x ↦ a.inv * x)) y ∂ν𝔭(v)) =
        (∫ y, K addTest(f) y ∂ν𝔭(v)) -
          (Real.log ‖a.val‖ / Real.log q(v) : ℝ) * addTest(f) 0 := by
  intro K
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let φ := tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) * φ y) ν𝔭(v) :=
    (finiteLog_integrable_mul_test v g).congr (ae_of_all _ fun y ↦ by
      simp only [hg]; rfl)
  obtain ⟨hI, hEq⟩ := finiteLogFourier_comp_mul v f a hint
  -- Fourier transform of the dilated test.
  have hFT (y : v.adicCompletion F) :
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (addTest(f) ∘ (fun x ↦ a.inv * x)) y =
        ((‖a.val‖ : ℝ) : ℂ) * φ (a.val * y) := by
    have h := finiteLocalAdditive_integral_comp_mul v a⁻¹
      (fun z ↦ addTest(f) z * star (ψ𝔭(v) (z * (a.val * y)) : ℂ))
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_inv, Complex.real_smul] at h
    unfold tamagawaFourier
    refine Eq.trans ?_ h
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    have hx : (a.val)⁻¹ * x * (a.val * y) = x * y := by
      rw [mul_mul_mul_comm, inv_mul_cancel₀ a.ne_zero, one_mul]
    have ha : a.inv = (a.val)⁻¹ := Units.val_inv_eq_inv_val a
    simp only [Function.comp_apply]
    rw [hx, ha]
  have hK (y : v.adicCompletion F) : K (addTest(f) ∘ (fun x ↦ a.inv * x)) y =
      ((‖a.val‖ : ℝ) : ℂ) * (((J𝔭(v) y : ℝ) : ℂ) * φ (a.val * y)) := by
    change ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v)
      (addTest(f) ∘ (fun x ↦ a.inv * x)) y = _
    rw [hFT]
    ring
  have hne : ((‖a.val‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr a.ne_zero).ne'
  refine ⟨(hI.const_mul _).congr (ae_of_all _ fun y ↦ (hK y).symm), hint, ?_⟩
  rw [integral_congr_ae (ae_of_all _ hK), integral_const_mul, hEq, Complex.real_smul,
    ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ hne, one_mul]

/-- The norm on a finite completion is discrete: a norm in `(q⁻¹, 1]` equals `1`. -/
private theorem finiteLogFourier_eq_neg_haar_norm_eq_one (v : Primes(F))
    (x : v.adicCompletion F) (h1 : ‖x‖ ≤ 1) (h2 : q(v)⁻¹ < ‖x‖) : ‖x‖ = 1 := by
  have hx0 : Valued.v x ≠ 0 := by
    intro h
    have : x = 0 := (map_eq_zero _).mp h
    subst this
    simp at h2
    exact absurd h2 (not_lt.mpr (by positivity))
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hn : ‖x‖ = q(v) ^ WithZero.log (Valued.v x) := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hx0]
    simp
  rw [hn] at h1 h2 ⊢
  rw [← zpow_neg_one] at h2
  have a := (zpow_lt_zpow_iff_right₀ hq).mp h2
  have b := (zpow_le_zpow_iff_right₀ hq).mp (h1.trans_eq (zpow_zero _).symm)
  rw [show WithZero.log (Valued.v x) = 0 by omega, zpow_zero]

/-- Additive tests are locally constant with compact support. -/
private theorem finiteLogFourier_eq_neg_haar_testFacts (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) :
    IsLocallyConstant addTest(f) ∧ HasCompactSupport addTest(f) :=
  (mem_finitePlaceSchwartz_iff F v _).mp ⟨f, fun _ ↦ rfl⟩

/-- A continuous compactly supported function is bounded and supported in a ball. -/
private theorem finiteLogFourier_eq_neg_haar_bound (v : Primes(F))
    (φ : v.adicCompletion F → ℂ) (hc : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ C R : ℝ, 0 < R ∧ (∀ z, ‖φ z‖ ≤ C) ∧ ∀ z, φ z ≠ 0 → ‖z‖ ≤ R := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs.isCompact.isBounded
  refine ⟨C, max R 1, lt_max_of_lt_right one_pos, hC, fun z hz ↦ ?_⟩
  have := hR (subset_tsupport φ hz)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact this.trans (le_max_left _ _)

/-- A locally constant function vanishing at zero vanishes on a ball around zero. -/
private theorem finiteLogFourier_eq_neg_haar_vanish (v : Primes(F))
    (h : v.adicCompletion F → ℂ) (hl : IsLocallyConstant h) (h0 : h 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, h x ≠ 0 → r ≤ ‖x‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hl.isOpen_fiber 0) 0 h0
  refine ⟨r, hr, fun x hx ↦ not_lt.mp fun hlt ↦ hx ?_⟩
  exact hball (by rwa [Metric.mem_ball, dist_zero_right])

/-- The indicator of a compact clopen set is an additive test. -/
private theorem finiteLogFourier_eq_neg_haar_clopenTest (v : Primes(F))
    (s : Set (v.adicCompletion F)) (hs : IsClopen s) (hc : IsCompact s) :
    ∃ g : 𝒮ₐ(v.adicCompletion F), ∀ y,
      g (Multiplicative.ofAdd y) = s.indicator (fun _ ↦ (1 : ℂ)) y := by
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v (s.indicator (fun _ ↦ (1 : ℂ)))).mpr
    ⟨by
        have h : IsLocallyConstant (LocallyConstant.charFn ℂ hs : _ → ℂ) :=
          (LocallyConstant.charFn ℂ hs).isLocallyConstant
        rw [LocallyConstant.coe_charFn] at h
        exact h,
      HasCompactSupport.intro hc fun y hy ↦ indicator_of_notMem hy _⟩
  exact ⟨g, hg⟩

/-- The absolute value of the logarithm of the norm is integrable on every closed ball
about zero of a finite completion, for additive Tamagawa measure. -/
theorem finiteLog_abs_integrableOn_closedBall (v : Primes(F)) (R : ℝ) :
    IntegrableOn (fun b : v.adicCompletion F ↦ |Real.log ‖b‖|) {b | ‖b‖ ≤ R} ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : ProperSpace K := properSpace_adicCompletion v
  let r : ℝ := max R 1
  have hr : (0 : ℝ) < r := lt_max_of_lt_right one_pos
  let B : Set K := Metric.closedBall 0 r
  obtain ⟨g, hg⟩ := finiteLogFourier_eq_neg_haar_clopenTest v B
    (IsUltrametricDist.isClopen_closedBall 0 hr.ne') (isCompact_closedBall 0 r)
  have hint := finiteLog_integrable_mul_test v g
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlq : 0 < Real.log q(v) := Real.log_pos hq
  have hsub : {b : K | ‖b‖ ≤ R} ⊆ B := fun b (hb : ‖b‖ ≤ R) ↦ by
    simp only [B, Metric.mem_closedBall, dist_zero_right]; exact le_max_of_le_left hb
  refine IntegrableOn.mono_set ?_ hsub
  rw [← integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  refine (hint.norm.const_mul (Real.log q(v))).congr (ae_of_all _ fun y ↦ ?_)
  simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlq]
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy, indicator_of_mem hy, norm_one, mul_one, mul_div_cancel₀ _ hlq.ne']
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, norm_zero, mul_zero, mul_zero]

/-- The local standard character is continuous. -/
private theorem finiteLogFourier_eq_neg_haar_charContinuous (v : Primes(F)) :
    Continuous (finiteLocalStandardCharacter F v) := by
  have hψ0 := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  exact (hψ0.choose.continuous.comp continuous_ofAdd).congr hψ0.choose_spec.1

/-- The Fourier integrand of a continuous compactly supported function is integrable. -/
private theorem finiteLogFourier_eq_neg_haar_fourierIntegrable (v : Primes(F))
    (h : v.adicCompletion F → ℂ) (hc : Continuous h) (hs : HasCompactSupport h)
    (y : v.adicCompletion F) :
    Integrable (fun x ↦ h x * star (ψ𝔭(v) (x * y) : ℂ)) ν𝔭(v) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hψ := finiteLogFourier_eq_neg_haar_charContinuous v
  have hχ : Continuous fun x : v.adicCompletion F ↦ star (ψ𝔭(v) (x * y) : ℂ) :=
    continuous_star.comp (continuous_subtype_val.comp (hψ.comp (continuous_id.mul continuous_const)))
  exact (hc.mul hχ).integrable_of_hasCompactSupport hs.mul_right

/-- The logarithmic Fourier pairing of the indicator of the unit sphere is `-1`. -/
private theorem finiteLogFourier_eq_neg_haar_sphereTest (v : Primes(F)) :
    ∃ g : 𝒮ₐ(v.adicCompletion F),
      (∀ y, addTest(g) y =
        (Metric.sphere (0 : v.adicCompletion F) 1).indicator (fun _ ↦ (1 : ℂ)) y) ∧
      Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y) ν𝔭(v) ∧
      (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y ∂ν𝔭(v)) = -1 := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  obtain ⟨g, hg⟩ := finiteLogFourier_eq_neg_haar_clopenTest v (Metric.sphere (0 : K) 1)
    (IsUltrametricDist.isClopen_sphere 0 one_ne_zero) (isCompact_sphere 0 1)
  obtain ⟨g₁, hg₁⟩ := finiteLogFourier_eq_neg_haar_clopenTest v (Metric.closedBall (0 : K) 1)
    (IsUltrametricDist.isClopen_closedBall 0 one_ne_zero) (isCompact_closedBall 0 1)
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 π.val hπ.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨hI1, hI2, hEq⟩ := finiteLogFourier_dilate v g₁ p
  have hpinv : p.inv = (p.val)⁻¹ := Units.val_inv_eq_inv_val p
  have hpt (x : K) : addTest(g) x =
      addTest(g₁) x - (addTest(g₁) ∘ (fun x ↦ p.inv * x)) x := by
    simp only [Function.comp_apply, hg, hg₁, Set.indicator, Metric.mem_sphere,
      Metric.mem_closedBall, dist_zero_right, hpinv, norm_mul, norm_inv, hp, inv_inv]
    by_cases h1 : ‖x‖ ≤ 1
    · by_cases h2 : ‖x‖ ≤ q(v)⁻¹
      · have hne : ‖x‖ ≠ 1 := fun h ↦ by
          rw [h] at h2
          exact absurd h2 (not_le.mpr (inv_lt_one_of_one_lt₀ hq))
        have : q(v) * ‖x‖ ≤ 1 := by
          calc q(v) * ‖x‖ ≤ q(v) * q(v)⁻¹ := by gcongr
            _ = 1 := mul_inv_cancel₀ (by positivity)
        simp [hne, h1, this]
      · have he := finiteLogFourier_eq_neg_haar_norm_eq_one v x h1 (not_le.mp h2)
        simp [he, not_le.mpr (HeightOneSpectrum.one_lt_absNorm v)]
    · have hne : ‖x‖ ≠ 1 := fun h ↦ h1 h.le
      have : ¬ q(v) * ‖x‖ ≤ 1 := fun h ↦ h1 (by nlinarith [norm_nonneg x])
      simp [hne, h1, this]
  obtain ⟨hl₁, hc₁⟩ := finiteLogFourier_eq_neg_haar_testFacts v g₁
  have hc₁' : HasCompactSupport (addTest(g₁) ∘ (fun x ↦ p.inv * x)) := by
    rw [hpinv]
    exact hc₁.comp_isClosedEmbedding
      (Homeomorph.mulLeft₀ (p.val)⁻¹ (inv_ne_zero p.ne_zero)).isClosedEmbedding
  have hFT (y : K) : tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y =
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g₁) y -
        tamagawaFourier ν𝔭(v) ψ𝔭(v) (addTest(g₁) ∘ (fun x ↦ p.inv * x)) y := by
    unfold tamagawaFourier
    rw [← integral_sub
      (finiteLogFourier_eq_neg_haar_fourierIntegrable v _ hl₁.continuous hc₁ y)
      (finiteLogFourier_eq_neg_haar_fourierIntegrable v _
        (hl₁.continuous.comp (by fun_prop : Continuous fun x : K ↦ p.inv * x)) hc₁' y)]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [← sub_mul, ← hpt x]
  refine ⟨g, hg, ?_, ?_⟩
  · refine (hI2.sub hI1).congr (ae_of_all _ fun y ↦ ?_)
    simp only [Pi.sub_apply]
    rw [hFT y, mul_sub]
  · have hJ : ((Real.log ‖p.val‖ / Real.log q(v) : ℝ) : ℂ) = -1 := by
      rw [hp, Real.log_inv, neg_div, div_self (Real.log_pos hq).ne']
      push_cast; ring
    have h0 : addTest(g₁) 0 = 1 := (hg₁ 0).trans (by simp)
    calc (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y ∂ν𝔭(v))
        = (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g₁) y ∂ν𝔭(v)) -
          ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v)
            (addTest(g₁) ∘ (fun x ↦ p.inv * x)) y ∂ν𝔭(v) := by
          rw [← integral_sub hI2 hI1]
          refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
          dsimp only
          rw [hFT y, mul_sub]
      _ = -1 := by
          rw [hEq, hJ, h0]
          ring

/-- Pairing the normalized logarithm with a dilate of the Fourier transform of the unit
sphere indicator gives minus the inverse norm of the dilation. -/
private theorem finiteLogFourier_eq_neg_haar_kernel (v : Primes(F))
    (x : v.adicCompletion F) (hx : x ≠ 0) :
    (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v)
      ((Metric.sphere (0 : v.adicCompletion F) 1).indicator (fun _ ↦ (1 : ℂ))) (x * y) ∂ν𝔭(v)) =
      -((‖x‖⁻¹ : ℝ) : ℂ) := by
  obtain ⟨g, hg, hint, hL⟩ := finiteLogFourier_eq_neg_haar_sphereTest v
  have he : addTest(g) = (Metric.sphere (0 : v.adicCompletion F) 1).indicator
      (fun _ ↦ (1 : ℂ)) := funext hg
  have h0 : addTest(g) 0 = 0 := (hg 0).trans (by simp)
  have h := (finiteLogFourier_comp_mul v g (Units.mk0 x hx) hint).2
  rw [hL, h0, mul_zero, sub_zero, he, Units.val_mk0] at h
  rw [h, Complex.real_smul]
  ring

/-- Fubini for a product of integrable functions times a bounded continuous kernel. -/
private theorem finiteLogFourier_eq_neg_haar_swap (v : Primes(F))
    (A B : v.adicCompletion F → ℂ) (k : v.adicCompletion F → v.adicCompletion F → ℂ)
    (hA : Integrable A ν𝔭(v)) (hB : Integrable B ν𝔭(v)) (hk : Continuous (Function.uncurry k))
    (C : ℝ) (hC : ∀ a b, ‖k a b‖ ≤ C) :
    (∫ a, ∫ b, A a * B b * k a b ∂ν𝔭(v) ∂ν𝔭(v)) =
      ∫ b, ∫ a, A a * B b * k a b ∂ν𝔭(v) ∂ν𝔭(v) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  apply integral_integral_swap
  exact (hA.mul_prod hB).mul_bdd hk.aestronglyMeasurable (ae_of_all _ fun p ↦ hC p.1 p.2)

/-- Fubini for the normalized logarithm against a dilated bounded kernel, when the
dilations stay away from zero and the kernel has bounded support. -/
private theorem finiteLogFourier_eq_neg_haar_swapLog (v : Primes(F))
    (A Φ : v.adicCompletion F → ℂ) (hA : Integrable A ν𝔭(v)) (r : ℝ) (hr : 0 < r)
    (hAr : ∀ a, A a ≠ 0 → r ≤ ‖a‖) (hΦ : Continuous Φ) (C R : ℝ) (hR : 0 < R)
    (hC : ∀ z, ‖Φ z‖ ≤ C) (hΦR : ∀ z, Φ z ≠ 0 → ‖z‖ ≤ R) :
    (∫ a, A a * ∫ b, ((J𝔭(v) b : ℝ) : ℂ) * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v)) =
      ∫ b, ((J𝔭(v) b : ℝ) : ℂ) * ∫ a, A a * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  obtain ⟨gB, hgB⟩ := finiteLogFourier_eq_neg_haar_clopenTest v (Metric.closedBall (0 : K) (R / r))
    (IsUltrametricDist.isClopen_closedBall 0 (div_pos hR hr).ne') (isCompact_closedBall 0 _)
  let B : K → ℂ := fun b ↦ ((J𝔭(v) b : ℝ) : ℂ) *
    (Metric.closedBall (0 : K) (R / r)).indicator (fun _ ↦ (1 : ℂ)) b
  have hB : Integrable B ν𝔭(v) :=
    (finiteLog_integrable_mul_test v gB).congr (ae_of_all _ fun b ↦ by
      dsimp only [B]
      rw [← hgB b])
  have hpt (a b : K) : A a * (((J𝔭(v) b : ℝ) : ℂ) * Φ (a * b)) = A a * B b * Φ (a * b) := by
    by_cases ha : A a = 0
    · simp [ha]
    by_cases hb : Φ (a * b) = 0
    · simp [hb]
    have h1 := hAr a ha
    have h2 := hΦR _ hb
    rw [norm_mul] at h2
    have hb' : b ∈ Metric.closedBall (0 : K) (R / r) := by
      rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hr]
      nlinarith [norm_nonneg b]
    simp only [B, Set.indicator_of_mem hb', mul_one]
    ring
  have hsw := finiteLogFourier_eq_neg_haar_swap v A B (fun a b ↦ Φ (a * b)) hA hB
    (hΦ.comp (continuous_fst.mul continuous_snd)) C (fun a b ↦ hC _)
  calc (∫ a, A a * ∫ b, ((J𝔭(v) b : ℝ) : ℂ) * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v))
      = ∫ a, ∫ b, A a * B b * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v) := by
        refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun b ↦ hpt a b)
    _ = ∫ b, ∫ a, A a * B b * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v) := hsw
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
        exact (hpt a b).symm.trans (by ring)

/-- Averaging the dilates of a Fourier transform against a test is the Fourier transform of
the test paired with the function. -/
private theorem finiteLogFourier_eq_neg_haar_average (v : Primes(F))
    (s h : v.adicCompletion F → ℂ) (hs : Continuous s) (hs' : HasCompactSupport s)
    (hh : Continuous h) (hh' : HasCompactSupport h) (y : v.adicCompletion F) :
    (∫ u, s u * tamagawaFourier ν𝔭(v) ψ𝔭(v) h (u * y) ∂ν𝔭(v)) =
      ∫ x, h x * tamagawaFourier ν𝔭(v) ψ𝔭(v) s (x * y) ∂ν𝔭(v) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hψ := finiteLogFourier_eq_neg_haar_charContinuous v
  let k : v.adicCompletion F → v.adicCompletion F → ℂ :=
    fun u x ↦ star (ψ𝔭(v) (x * (u * y)) : ℂ)
  have hk : Continuous (Function.uncurry k) :=
    continuous_star.comp (continuous_subtype_val.comp (hψ.comp
      (continuous_snd.mul (continuous_fst.mul continuous_const))))
  have hsw := finiteLogFourier_eq_neg_haar_swap v s h k
    (hs.integrable_of_hasCompactSupport hs') (hh.integrable_of_hasCompactSupport hh') hk 1
    (fun a b ↦ by simp [k])
  unfold tamagawaFourier
  calc (∫ u, s u * ∫ x, h x * star (ψ𝔭(v) (x * (u * y)) : ℂ) ∂ν𝔭(v) ∂ν𝔭(v))
      = ∫ u, ∫ x, s u * h x * k u x ∂ν𝔭(v) ∂ν𝔭(v) := by
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        dsimp only [k]
        ring
    _ = ∫ x, ∫ u, s u * h x * k u x ∂ν𝔭(v) ∂ν𝔭(v) := hsw
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        dsimp only [k]
        rw [show u * (x * y) = x * (u * y) by ring]
        ring

/-- Integrals against multiplicative Tamagawa measure are additive integrals against the
inverse norm, up to the constant `q / (q - 1)`. -/
private theorem finiteLogFourier_eq_neg_haar_unitsIntegral (v : Primes(F))
    (g : v.adicCompletion F → ℂ) :
    (∫ u : (v.adicCompletion F)ˣ, g u.val ∂μ𝔭(v)) =
      ((v.asIdeal.absNorm : ENNReal) / ((v.asIdeal.absNorm : ENNReal) - 1)).toReal •
        ∫ y, ‖y‖⁻¹ • g y ∂ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let d : K → ENNReal := fun x ↦ (↑‖x‖₊ : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂(ν𝔭(v).restrict (range (Units.val : Kˣ → K))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  have hdy (y : K) : (d y).toReal = ‖y‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, integral_smul_measure]
  congr 1
  rw [← hval.integral_map g, hval.map_comap, restrict_withDensity hval.measurableSet_range,
    integral_withDensity_eq_integral_toReal_smul hd hdlt]
  simp_rw [hdy]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
  have : y = 0 := by
    by_contra h
    exact hy ⟨Units.mk0 y h, rfl⟩
  simp [this]

/-- Averaging over the unit sphere: the mass of the sphere times the logarithmic Fourier
pairing of a test vanishing at zero is minus its integral against the inverse norm. -/
private theorem finiteLogFourier_eq_neg_haar_identity (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) (hf : addTest(f) 0 = 0)
    (hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v)) :
    ((ν𝔭(v)).real (Metric.sphere (0 : v.adicCompletion F) 1) : ℂ) *
        (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) =
      -∫ x, ((‖x‖⁻¹ : ℝ) : ℂ) * addTest(f) x ∂ν𝔭(v) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let S := Metric.sphere (0 : K) 1
  let s1 : K → ℂ := S.indicator (fun _ ↦ (1 : ℂ))
  have hSc : IsClopen S := IsUltrametricDist.isClopen_sphere 0 one_ne_zero
  obtain ⟨g₀, hg₀⟩ := finiteLogFourier_eq_neg_haar_clopenTest v S hSc (isCompact_sphere 0 1)
  have hs1 : addTest(g₀) = s1 := funext hg₀
  obtain ⟨hl₀, hc₀⟩ := finiteLogFourier_eq_neg_haar_testFacts v g₀
  rw [hs1] at hl₀ hc₀
  obtain ⟨G, hG⟩ := finiteLocal_exists_fourier_test v g₀
  have hG' : addTest(G) = tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 := by
    rw [← hs1]
    exact funext hG
  obtain ⟨lG, cG⟩ := finiteLogFourier_eq_neg_haar_testFacts v G
  rw [hG'] at lG cG
  obtain ⟨CG, RG, hRG, hCG, hGR⟩ := finiteLogFourier_eq_neg_haar_bound v _ lG.continuous cG
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hφ : addTest(g) = tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) := funext hg
  obtain ⟨lφ, cφ⟩ := finiteLogFourier_eq_neg_haar_testFacts v g
  rw [hφ] at lφ cφ
  obtain ⟨Cφ, Rφ, hRφ, hCφ, hφR⟩ := finiteLogFourier_eq_neg_haar_bound v _ lφ.continuous cφ
  obtain ⟨hfl, hfc⟩ := finiteLogFourier_eq_neg_haar_testFacts v f
  obtain ⟨r, hr, hvan⟩ := finiteLogFourier_eq_neg_haar_vanish v _ hfl hf
  have hs1i : Integrable s1 ν𝔭(v) := hl₀.continuous.integrable_of_hasCompactSupport hc₀
  have hfi : Integrable addTest(f) ν𝔭(v) := hfl.continuous.integrable_of_hasCompactSupport hfc
  -- Every unit dilate has the same pairing.
  have ha (u : K) : s1 u * (∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (u * y) ∂ν𝔭(v)) =
      s1 u * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v) := by
    by_cases hu : u ∈ S
    · have hn : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
      have h := (finiteLogFourier_comp_mul v f (Units.mk0 u hu0) hint).2
      rw [hf, mul_zero, sub_zero, Units.val_mk0, hn, inv_one, one_smul] at h
      rw [h]
    · simp [s1, hu]
  -- Unit dilates of the test against the sphere indicator.
  have hb := finiteLogFourier_eq_neg_haar_swapLog v s1
    (tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)) hs1i 1 one_pos
    (fun u hu ↦ by
      have : u ∈ S := by
        by_contra h
        exact hu (by simp [s1, h])
      rw [mem_sphere_zero_iff_norm.mp this]) lφ.continuous Cφ Rφ hRφ hCφ hφR
  have hd := finiteLogFourier_eq_neg_haar_swapLog v addTest(f)
    (tamagawaFourier ν𝔭(v) ψ𝔭(v) s1) hfi r hr hvan lG.continuous CG RG hRG hCG hGR
  have he (x : K) : addTest(f) x * (∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 (x * y) ∂ν𝔭(v)) = -(((‖x‖⁻¹ : ℝ) : ℂ) * addTest(f) x) := by
    by_cases hx : x = 0
    · rw [hx, hf]
      ring
    · rw [finiteLogFourier_eq_neg_haar_kernel v x hx]
      ring
  calc ((ν𝔭(v)).real S : ℂ) *
        (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v))
      = ∫ u, s1 u * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v) ∂ν𝔭(v) := by
        rw [integral_mul_const, integral_indicator_const _ hSc.isOpen.measurableSet,
          Complex.real_smul, mul_one]
    _ = ∫ u, s1 u * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (u * y) ∂ν𝔭(v) ∂ν𝔭(v) :=
        integral_congr_ae (ae_of_all _ fun u ↦ (ha u).symm)
    _ = ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * ∫ u, s1 u *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (u * y) ∂ν𝔭(v) ∂ν𝔭(v) := hb
    _ = ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * ∫ x, addTest(f) x *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 (x * y) ∂ν𝔭(v) ∂ν𝔭(v) := by
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        dsimp only
        rw [finiteLogFourier_eq_neg_haar_average v s1 addTest(f) hl₀.continuous hc₀
          hfl.continuous hfc y]
    _ = ∫ x, addTest(f) x * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 (x * y) ∂ν𝔭(v) ∂ν𝔭(v) := hd.symm
    _ = _ := by
        rw [integral_congr_ae (ae_of_all _ he), integral_neg]

/-- Paper: Proposition B.4.3.1(2), p. 617. On additive tests vanishing at
zero, the Fourier transform is minus multiplicative Haar measure divided by
the mass of the integer units. -/
theorem finiteLogFourier_eq_neg_haar (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (_hf : addTest(f) 0 = 0) :
    let K : v.adicCompletion F → ℂ := logFourierIntegrand(ν𝔭(v), ψ𝔭(v), J𝔭(v), addTest(f))
    Integrable K ν𝔭(v) ∧ Integrable (fun u : (v.adicCompletion F)ˣ ↦ addTest(f) u.val) μ𝔭(v) ∧
      (∫ y, K y ∂ν𝔭(v)) =
        -(∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v)) / (V𝔭(v) : ℂ) := by
  intro K'
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hint : Integrable K' ν𝔭(v) :=
    (finiteLog_integrable_mul_test v g).congr (ae_of_all _ fun y ↦ by
      simp only [hg]; rfl)
  obtain ⟨hfl, hfc⟩ := finiteLogFourier_eq_neg_haar_testFacts v f
  obtain ⟨r, hr, hvan⟩ := finiteLogFourier_eq_neg_haar_vanish v _ hfl _hf
  have hfi : Integrable addTest(f) ν𝔭(v) := hfl.continuous.integrable_of_hasCompactSupport hfc
  have hInv : Integrable (fun y ↦ ‖y‖⁻¹ • addTest(f) y) ν𝔭(v) := by
    refine (hfi.norm.const_mul r⁻¹).mono'
      ((by fun_prop : Measurable fun y : v.adicCompletion F ↦ ‖y‖⁻¹).aestronglyMeasurable.smul
        hfi.aestronglyMeasurable) (ae_of_all _ fun y ↦ ?_)
    rw [norm_smul, norm_inv, norm_norm]
    by_cases hy : addTest(f) y = 0
    · rw [hy, norm_zero, mul_zero]; positivity
    · exact mul_le_mul_of_nonneg_right (inv_anti₀ hr (hvan y hy)) (norm_nonneg _)
  have hunits := (finiteLocal_units_integrable_iff v _).mpr hInv
  refine ⟨hint, hunits, ?_⟩
  have hId := finiteLogFourier_eq_neg_haar_identity v f _hf hint
  let S := Metric.sphere (0 : v.adicCompletion F) 1
  let s1 : v.adicCompletion F → ℂ := S.indicator (fun _ ↦ (1 : ℂ))
  let c := ((v.asIdeal.absNorm : ENNReal) / ((v.asIdeal.absNorm : ENNReal) - 1)).toReal
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hc : 0 < c := ENNReal.toReal_pos (ENNReal.div_pos (zero_lt_one.trans hq).ne'
    (ENNReal.sub_ne_top (ENNReal.natCast_ne_top _))).ne'
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (tsub_pos_of_lt hq).ne').ne
  have hSo : IsOpen S := IsUltrametricDist.isOpen_sphere (0 : v.adicCompletion F) one_ne_zero
  have hνS : 0 < (ν𝔭(v)).real S := ENNReal.toReal_pos
    (hSo.measure_pos _ ⟨1, by simp [S]⟩).ne' (isCompact_sphere _ _).measure_lt_top.ne
  have hpre : ((O(v)).units : Set (v.adicCompletion F)ˣ) = Units.val ⁻¹' S := by
    ext u
    simp only [SetLike.mem_coe, mem_preimage, S, mem_sphere_zero_iff_norm]
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      Valued.toNormedField.norm_eq_one_iff]
  have hV : V𝔭(v) = c * (ν𝔭(v)).real S := by
    have h1 := finiteLogFourier_eq_neg_haar_unitsIntegral v s1
    have h2 : (fun u : (v.adicCompletion F)ˣ ↦ s1 u.val) =
        (Units.val ⁻¹' S).indicator (fun _ ↦ (1 : ℂ)) := by
      funext u
      simp only [s1, Set.indicator, mem_preimage]
    have h3 : (fun y ↦ ‖y‖⁻¹ • s1 y) = s1 := by
      funext y
      by_cases hy : y ∈ S
      · simp [s1, hy, mem_sphere_zero_iff_norm.mp hy]
      · simp [s1, hy]
    rw [h2, integral_indicator_const _ (hSo.preimage Units.continuous_val).measurableSet, h3,
      integral_indicator_const _ hSo.measurableSet, ← hpre] at h1
    have := congrArg Complex.re h1
    simpa [Measure.real, c, ENNReal.toReal_div] using this
  have hU := finiteLogFourier_eq_neg_haar_unitsIntegral v addTest(f)
  have hsm : (fun y ↦ ‖y‖⁻¹ • addTest(f) y) =
      fun y ↦ ((‖y‖⁻¹ : ℝ) : ℂ) * addTest(f) y := funext fun y ↦ Complex.real_smul
  rw [hU, hV, hsm, Complex.real_smul]
  have hνS' : (((ν𝔭(v)).real S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hνS.ne'
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  change (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) = _
  rw [eq_div_iff (by push_cast; exact mul_ne_zero hc' hνS'), neg_mul_eq_mul_neg, ← hId]
  push_cast
  ring

-- TODO(paper-gap): Jᵥ is unbounded near zero and is not an additive
-- Schwartz–Bruhat test. The normalization at one is on its punctured-field representative.

/-- Every additive test of a finite completion is the Fourier transform of an additive test. -/
private theorem finiteLogFourier_unique_surjective (v : Primes(F))
    (g : 𝒮ₐ(v.adicCompletion F)) :
    ∃ f : 𝒮ₐ(v.adicCompletion F), ∀ y,
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x)) y =
        g (Multiplicative.ofAdd y) := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, he, -⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let μ : Measure G := ν𝔭(v)
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_comp_equivCLM e.symm
  have key (h : SchwartzBruhat G) (y : K) :
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ h (Multiplicative.ofAdd x)) y =
        T h (e (Multiplicative.ofAdd y)) := by
    have h1 : tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ h (Multiplicative.ofAdd x)) y =
        lcaFourier μ (fun x : G ↦ h (Multiplicative.ofAdd x.toAdd)) (e (Multiplicative.ofAdd y)) :=
      tamagawaFourier_eq_lcaFourier _ _ _ y _ fun x ↦ (he y x).trans
        (congrArg _ (mul_comm y x))
    exact h1.trans ((hT h).2 _).symm
  refine ⟨T.symm (P g), fun y ↦ ?_⟩
  rw [key, T.apply_symm_apply, hP, e.symm_apply_apply]

/-- The indicator of a closed ball of positive radius in a finite completion is an additive
test. -/
private theorem finiteLogFourier_unique_ballTest (v : Primes(F)) (x : v.adicCompletion F)
    {r : ℝ} (hr : 0 < r) :
    ∃ g : 𝒮ₐ(v.adicCompletion F), ∀ y,
      g (Multiplicative.ofAdd y) = (Metric.closedBall x r).indicator (fun _ ↦ (1 : ℂ)) y := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have hU : IsClopen (Metric.closedBall x r) := IsUltrametricDist.isClopen_closedBall x hr.ne'
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v
    ((Metric.closedBall x r).indicator (fun _ ↦ (1 : ℂ)))).mpr
    ⟨by
        have h : IsLocallyConstant (LocallyConstant.charFn ℂ hU : _ → ℂ) :=
          (LocallyConstant.charFn ℂ hU).isLocallyConstant
        rw [LocallyConstant.coe_charFn] at h
        exact h,
      HasCompactSupport.intro (isCompact_closedBall x r) fun y hy ↦ indicator_of_notMem hy _⟩
  exact ⟨g, hg⟩

/-- Paper: Proposition B.4.3.1, p. 618. The restriction away from zero of the
Fourier transform determines the normalized logarithm among continuous representatives off zero.
Deviation: The representative acts by integration on Fourier-transformed tests. -/
theorem finiteLogFourier_unique (v : Primes(F)) (J : v.adicCompletion F → ℂ)
    (_hcont : ContinuousOn J ({0}ᶜ)) (_hOne : J 1 = 0)
    (_hInt : ∀ f : 𝒮ₐ(v.adicCompletion F),
      Integrable (fun y ↦ J y * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v))
    (_hAway : ∀ f : 𝒮ₐ(v.adicCompletion F), addTest(f) 0 = 0 →
      (∫ y, J y * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) =
        -(∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v)) / (V𝔭(v) : ℂ)) :
    ∀ x ≠ 0, J x = (J𝔭(v) x : ℝ) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  -- The difference with the normalized logarithm.
  let L : v.adicCompletion F → ℂ := fun y ↦ ((J𝔭(v) y : ℝ) : ℂ)
  -- Integrability of `J` and of `L` against every test.
  have hJint (g : 𝒮ₐ(v.adicCompletion F)) :
      Integrable (fun y ↦ J y * g (Multiplicative.ofAdd y)) ν𝔭(v) := by
    obtain ⟨f, hf⟩ := finiteLogFourier_unique_surjective v g
    have h := _hInt f
    simp only [hf] at h
    exact h
  have hLint (g : 𝒮ₐ(v.adicCompletion F)) :
      Integrable (fun y ↦ L y * g (Multiplicative.ofAdd y)) ν𝔭(v) :=
    finiteLog_integrable_mul_test v g
  -- `J` and `L` agree on tests of integral zero.
  have hzero (g : 𝒮ₐ(v.adicCompletion F))
      (hg : ∫ y, g (Multiplicative.ofAdd y) ∂ν𝔭(v) = 0) :
      ∫ y, J y * g (Multiplicative.ofAdd y) ∂ν𝔭(v) =
        ∫ y, L y * g (Multiplicative.ofAdd y) ∂ν𝔭(v) := by
    obtain ⟨f, hf⟩ := finiteLogFourier_unique_surjective v g
    have hf0 : f (Multiplicative.ofAdd 0) = 0 := by
      have h := (finiteLocal_integral_tamagawaFourier v f).2
      simp only [hf] at h
      exact h.symm.trans hg
    have h1 := _hAway f hf0
    have h2 := (finiteLogFourier_eq_neg_haar v f hf0).2.2
    simp only [hf] at h1 h2
    exact h1.trans h2.symm
  -- Integrals against ball indicators are integrals over the balls.
  have hon (g : 𝒮ₐ(v.adicCompletion F)) (s : Set (v.adicCompletion F)) (hs : MeasurableSet s)
      (hg : ∀ y, g (Multiplicative.ofAdd y) = s.indicator (fun _ ↦ (1 : ℂ)) y)
      (Φ : v.adicCompletion F → ℂ) (hΦ : Integrable (fun y ↦ Φ y * g (Multiplicative.ofAdd y)) ν𝔭(v)) :
      IntegrableOn Φ s ν𝔭(v) ∧
        ∫ y, Φ y * g (Multiplicative.ofAdd y) ∂ν𝔭(v) = ∫ y in s, Φ y ∂ν𝔭(v) := by
    have e : (fun y ↦ Φ y * g (Multiplicative.ofAdd y)) = s.indicator Φ := funext fun y ↦ by
      rw [hg y]
      simp only [indicator_apply]
      split_ifs <;> simp
    rw [e] at hΦ ⊢
    exact ⟨(integrable_indicator_iff hs).mp hΦ, integral_indicator hs⟩
  let D : v.adicCompletion F → ℂ := fun y ↦ J y - L y
  have hball (x : v.adicCompletion F) {r : ℝ} (hr : 0 < r) :
      IntegrableOn D (Metric.closedBall x r) ν𝔭(v) ∧
        IntegrableOn D (Metric.closedBall 1 r) ν𝔭(v) ∧
        ∫ y in Metric.closedBall x r, D y ∂ν𝔭(v) =
          ∫ y in Metric.closedBall 1 r, D y ∂ν𝔭(v) := by
    have hm := (Metric.isClosed_closedBall (x := x) (ε := r)).measurableSet
    have hm1 := (Metric.isClosed_closedBall (x := (1 : v.adicCompletion F)) (ε := r)).measurableSet
    obtain ⟨gx, hgx⟩ := finiteLogFourier_unique_ballTest v x hr
    obtain ⟨g1, hg1⟩ := finiteLogFourier_unique_ballTest v 1 hr
    obtain ⟨hJx, eJx⟩ := hon gx _ hm hgx J (hJint gx)
    obtain ⟨hJ1, eJ1⟩ := hon g1 _ hm1 hg1 J (hJint g1)
    obtain ⟨hLx, eLx⟩ := hon gx _ hm hgx L (hLint gx)
    obtain ⟨hL1, eL1⟩ := hon g1 _ hm1 hg1 L (hLint g1)
    have hsub (y : v.adicCompletion F) : (gx - g1) (Multiplicative.ofAdd y) =
        gx (Multiplicative.ofAdd y) - g1 (Multiplicative.ofAdd y) := rfl
    have hfin (z : v.adicCompletion F) : ν𝔭(v) (Metric.closedBall z r) ≠ ⊤ :=
      (isCompact_closedBall z r).measure_lt_top.ne
    have hconst (g : 𝒮ₐ(v.adicCompletion F)) (z : v.adicCompletion F)
        (hg : ∀ y, g (Multiplicative.ofAdd y) =
          (Metric.closedBall z r).indicator (fun _ ↦ (1 : ℂ)) y) :
        Integrable (fun y ↦ g (Multiplicative.ofAdd y)) ν𝔭(v) ∧
          ∫ y, g (Multiplicative.ofAdd y) ∂ν𝔭(v) = ((ν𝔭(v)).real (Metric.closedBall z r) : ℂ) := by
      have hm' := (Metric.isClosed_closedBall (x := z) (ε := r)).measurableSet
      rw [funext hg]
      refine ⟨(integrable_indicator_iff hm').mpr (integrableOn_const (hfin z)), ?_⟩
      rw [integral_indicator hm', setIntegral_const, Complex.real_smul, mul_one]
    obtain ⟨igx, Igx⟩ := hconst gx x hgx
    obtain ⟨ig1, Ig1⟩ := hconst g1 1 hg1
    have hmeas : (ν𝔭(v)).real (Metric.closedBall x r) =
        (ν𝔭(v)).real (Metric.closedBall 1 r) := by
      rw [Measure.addHaar_real_closedBall_center,
        Measure.addHaar_real_closedBall_center (ν𝔭(v)) (1 : v.adicCompletion F)]
    have h0 : ∫ y, (gx - g1) (Multiplicative.ofAdd y) ∂ν𝔭(v) = 0 := by
      simp only [hsub]
      rw [integral_sub igx ig1, Igx, Ig1, hmeas, sub_self]
    have hz := hzero (gx - g1) h0
    simp only [hsub, mul_sub] at hz
    rw [integral_sub (hJint gx) (hJint g1), integral_sub (hLint gx) (hLint g1),
      eJx, eJ1, eLx, eL1] at hz
    refine ⟨hJx.sub hLx, hJ1.sub hL1, ?_⟩
    rw [integral_sub hJx hLx, integral_sub hJ1 hL1]
    linear_combination hz
  -- `D` is continuous away from zero and vanishes at one.
  have hDcont : ContinuousOn D ({0}ᶜ) := by
    refine _hcont.sub (Complex.continuous_ofReal.comp_continuousOn ?_)
    refine ContinuousOn.div_const ?_ _
    exact Real.continuousOn_log.comp continuous_norm.continuousOn fun y hy ↦ by
      simpa using hy
  have hD1 : D 1 = 0 := by simp [D, L, _hOne]
  intro x hx
  suffices hDx : D x = 0 by
    have := sub_eq_zero.mp hDx
    exact this
  rw [← hD1]
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hcx : ContinuousAt D x := hDcont.continuousAt (isOpen_compl_singleton.mem_nhds hx)
  have hc1 : ContinuousAt D 1 :=
    hDcont.continuousAt (isOpen_compl_singleton.mem_nhds one_ne_zero)
  obtain ⟨rx, hrx, hx'⟩ := Metric.continuousAt_iff.mp hcx (ε / 2) (half_pos hε)
  obtain ⟨r1, hr1, h1'⟩ := Metric.continuousAt_iff.mp hc1 (ε / 2) (half_pos hε)
  have hr : 0 < min rx r1 / 2 := half_pos (lt_min hrx hr1)
  have hrx' : min rx r1 / 2 < rx :=
    (half_lt_self (lt_min hrx hr1)).trans_le (min_le_left _ _)
  have hr1' : min rx r1 / 2 < r1 :=
    (half_lt_self (lt_min hrx hr1)).trans_le (min_le_right _ _)
  obtain ⟨hIx, hI1, hEq⟩ := hball x hr
  have hfin (z : v.adicCompletion F) : ν𝔭(v) (Metric.closedBall z (min rx r1 / 2)) < ⊤ :=
    (isCompact_closedBall z _).measure_lt_top
  have hpos : 0 < (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) :=
    ENNReal.toReal_pos ((Metric.isOpen_ball.measure_pos _ ⟨x, Metric.mem_ball_self hr⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)).ne' (hfin x).ne
  have hmeas : (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) =
      (ν𝔭(v)).real (Metric.closedBall 1 (min rx r1 / 2)) := by
    rw [Measure.addHaar_real_closedBall_center,
      Measure.addHaar_real_closedBall_center (ν𝔭(v)) (1 : v.adicCompletion F)]
  have bound (z : v.adicCompletion F) (hI : IntegrableOn D (Metric.closedBall z (min rx r1 / 2)) ν𝔭(v))
      (hz : ∀ y, dist y z < min rx r1 / 2 + (min rx r1 / 2) → dist (D y) (D z) < ε / 2) :
      ‖(∫ y in Metric.closedBall z (min rx r1 / 2), D y ∂ν𝔭(v)) -
          (ν𝔭(v)).real (Metric.closedBall z (min rx r1 / 2)) • D z‖ ≤
        ε / 2 * (ν𝔭(v)).real (Metric.closedBall z (min rx r1 / 2)) := by
    rw [← setIntegral_const, ← integral_sub hI (integrableOn_const (hfin z).ne)]
    refine norm_setIntegral_le_of_norm_le_const (hfin z) fun y hy ↦ ?_
    rw [← dist_eq_norm]
    exact (hz y ((Metric.mem_closedBall.mp hy).trans_lt (by linarith))).le
  have bx := bound x hIx fun y hy ↦ hx' (hy.trans_le (by linarith [min_le_left rx r1]))
  have b1 := bound 1 hI1 fun y hy ↦ h1' (hy.trans_le (by linarith [min_le_right rx r1]))
  rw [hEq] at bx
  rw [← hmeas] at b1
  have hdist : (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) * dist (D x) (D 1) ≤
      (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) * ε := by
    rw [dist_eq_norm, ← Real.norm_of_nonneg hpos.le, ← norm_smul, smul_sub]
    calc _ = ‖((∫ y in Metric.closedBall 1 (min rx r1 / 2), D y ∂ν𝔭(v)) -
            (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) • D 1) -
          ((∫ y in Metric.closedBall 1 (min rx r1 / 2), D y ∂ν𝔭(v)) -
            (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) • D x)‖ := by
          congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add b1 bx)
      _ = _ := by rw [Real.norm_of_nonneg hpos.le]; ring
  exact le_of_mul_le_mul_left hdist hpos

-- TODO(paper-gap): (B.4.3.13)–(B.4.3.14) multiply the Fourier distributions by
-- the local norm-one volumes 2 and 2π. Dilation gives the wrong delta term
-- with those factors (already visible on the real self-dual Gaussian).

local notation "eulerLogConstant" => (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant)

/-- Express an additive Schwartz–Bruhat test in the real coordinate of the completion. -/
private theorem realLogFourier_finitePart_realTest (w : InfinitePlace F) (hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) :
    ∃ u : 𝓢(ℝ, ℂ), ∀ x : w.Completion,
      addTest(f) x = u (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let c : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { toMulEquiv := e.toAddEquiv.toMultiplicative
      continuous_toFun := j.continuous
      continuous_invFun := j.symm.continuous }
  obtain ⟨E, hE⟩ := schwartzBruhat_realCoordinate_equiv c
  obtain ⟨u, rfl⟩ := E.surjective f
  exact ⟨u, fun x ↦ hE u (Multiplicative.ofAdd x)⟩

/-- Paper: Proposition B.4.3.2(1), p. 619. The real Fourier pairing equals
minus half the finite part and minus the logarithmic constant times evaluation at zero.
Deviation: Divides the printed distribution by two. -/
theorem realLogFourier_finitePart (w : InfinitePlace F) (_hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) :
    let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
    Integrable K ν∞(w) ∧
      (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ addTest(f) x / ((‖x‖ : ℝ) : ℂ))
        {x : w.Completion | ε ≤ ‖x‖} ν∞(w)) ∧
      Tendsto (fun ε : ℝ ↦ (∫ x in {x : w.Completion | ε ≤ ‖x‖},
        addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w)) + 2 * addTest(f) 0 * (Real.log ε : ℂ))
        (𝓝[>] 0) (𝓝 (-2 * ((∫ y, K y ∂ν∞(w)) + (eulerLogConstant : ℂ) * addTest(f) 0))) := by
  intro K
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal _hw
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  have hμ : ν∞(w) = (volume : Measure ℝ).map m := dite_eq_left _hw
  have hem (t : ℝ) : e (m t) = t := e.apply_symm_apply t
  have hnorm (t : ℝ) : ‖m t‖ = |t| := by
    change ‖j.symm t‖ = ‖t‖
    rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
      show j.symm 0 = 0 from map_zero e.symm]
  obtain ⟨u, hf⟩ := realLogFourier_finitePart_realTest w _hw f
  change ∀ x, addTest(f) x = u (e x) at hf
  have hK (t : ℝ) : K (m t) = (Real.log |t| : ℂ) * FourierTransform.fourier (u : ℝ → ℂ) t := by
    change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
    rw [_hw.mult_eq_one, pow_one, hnorm, funext hf, realModelFourier w _hw, hem]
  obtain ⟨hlog, hcut, hlim⟩ := real_log_fourier_cutoff u
  -- Transport the cutoff sets along the isometry, then double the real-line limit.
  simp only [hμ, integrable_map_equiv, integrableOn_map_equiv, setIntegral_map_equiv,
    integral_map_equiv, Function.comp_def, preimage_ofPred_eq, hK, hnorm, hf, hem, map_zero]
  refine ⟨hlog, hcut, ?_⟩
  have scale (x y z : ℂ) : 2 * (1 / 2 * x + y * z) = x + 2 * z * y := by ring
  have scale_limit (x y : ℂ) : 2 * (-x - y) = -2 * (x + y) := by ring
  simpa only [scale, scale_limit, Complex.ofReal_add] using hlim.const_mul (2 : ℂ)

open Real in
open scoped FourierTransform in
/-- Mean-value bound for the difference of two decaying exponentials. -/
private theorem complexLogFourier_finitePart_exp_sub_bound {α β y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hy : 0 ≤ y) :
    |exp (-α * y) - exp (-β * y)| ≤ |β - α| * y * exp (-(min α β) * y) := by
  wlog h : α ≤ β generalizing α β
  · have := this hβ hα (le_of_not_ge h)
    rwa [abs_sub_comm α β, min_comm, abs_sub_comm (exp (-β * y))] at this
  rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
  have h1 : exp (-β * y) ≤ exp (-α * y) := exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  -- exp(-αy) - exp(-βy) = exp(-αy) (1 - exp(-(β-α)y)) ≤ exp(-αy) (β-α) y
  have h2 : 1 - exp (-((β - α) * y)) ≤ (β - α) * y := by
    have := add_one_le_exp (-((β - α) * y)); linarith
  have h3 : exp (-β * y) = exp (-α * y) * exp (-((β - α) * y)) := by
    rw [← exp_add]; ring_nf
  rw [h3]
  have := exp_pos (-α * y)
  nlinarith

open Real in
open scoped FourierTransform in
/-- Frullani's integral for two decaying exponentials. -/
private theorem complexLogFourier_finitePart_frullani_exp {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntegrableOn (fun y ↦ y⁻¹ * (exp (-α * y) - exp (-β * y))) (Ioi 0) ∧
      ∫ y in Ioi 0, y⁻¹ * (exp (-α * y) - exp (-β * y)) = log (β / α) := by
  have hint : IntegrableOn (fun y ↦ y⁻¹ * (exp (-α * y) - exp (-β * y))) (Ioi 0) := by
    have hm : 0 < min α β := lt_min hα hβ
    have hdom : IntegrableOn (fun y ↦ |β - α| * exp (-(min α β) * y)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hm).const_mul _
    refine hdom.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 0 < y)
    rw [norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy]
    have := complexLogFourier_finitePart_exp_sub_bound hα hβ hy.le
    rw [inv_mul_le_iff₀ hy]
    nlinarith [this]
  refine ⟨hint, ?_⟩
  have h := Frullani.integral_Ioi_eq (f := fun x : ℝ ↦ exp (-x)) (L := 1) (R := 0)
    ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x)).locallyIntegrable.locallyIntegrableOn _) hα hβ
    (by simpa using ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x)).tendsto 0).mono_left nhdsWithin_le_nhds)
    (by simpa using tendsto_exp_neg_atTop_nhds_zero)
    (by simpa [smul_eq_mul, neg_mul] using hint)
  simpa [smul_eq_mul, neg_mul] using h

open Real in
open scoped FourierTransform in
/-- The Frullani integrand for exponentials has constant sign. -/
private theorem complexLogFourier_finitePart_frullani_abs {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ y in Ioi 0, |y⁻¹ * (exp (-α * y) - exp (-β * y))| = |log (β / α)| := by
  obtain ⟨hi, hv⟩ := complexLogFourier_finitePart_frullani_exp hα hβ
  rcases le_total α β with h | h
  · have hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ y⁻¹ * (exp (-α * y) - exp (-β * y)) := by
      intro y (hy : 0 < y)
      exact mul_nonneg (inv_nonneg.mpr hy.le)
        (sub_nonneg.mpr (exp_le_exp.mpr (by nlinarith)))
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ abs_of_nonneg (hnn y hy)), hv,
      abs_of_nonneg (log_nonneg ((one_le_div hα).mpr h))]
  · have hnp : ∀ y ∈ Ioi (0 : ℝ), y⁻¹ * (exp (-α * y) - exp (-β * y)) ≤ 0 := by
      intro y (hy : 0 < y)
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hy.le)
        (sub_nonpos.mpr (exp_le_exp.mpr (by nlinarith)))
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ abs_of_nonpos (hnp y hy)),
      integral_neg, hv, abs_of_nonpos (log_nonpos (div_nonneg hβ.le hα.le) ((div_le_one hα).mpr h))]

open Real in
open scoped FourierTransform in
/-- The substitution `x ↦ x⁻¹` preserves the measure `dx / x` on the positive reals. -/
private theorem complexLogFourier_finitePart_inv_sub (g : ℝ → ℝ) :
    (IntegrableOn (fun x ↦ x⁻¹ * g x⁻¹) (Ioi 0) ↔ IntegrableOn (fun x ↦ x⁻¹ * g x) (Ioi 0)) ∧
      ∫ x in Ioi 0, x⁻¹ * g x⁻¹ = ∫ x in Ioi 0, x⁻¹ * g x := by
  have hp : (-1 : ℝ) ≠ 0 := by norm_num
  have hc : EqOn (fun x : ℝ ↦ (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • ((x ^ (-1 : ℝ))⁻¹ * g (x ^ (-1 : ℝ))))
      (fun x ↦ x⁻¹ * g x⁻¹) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [rpow_neg_one, inv_inv, smul_eq_mul, abs_neg, abs_one, one_mul]
    rw [show (-1 : ℝ) - 1 = -2 by norm_num, rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      rpow_natCast]
    field_simp
  constructor
  · rw [← integrableOn_Ioi_comp_rpow_iff (fun y ↦ y⁻¹ * g y) hp,
      integrableOn_congr_fun hc measurableSet_Ioi]
  · rw [← integral_comp_rpow_Ioi (fun y ↦ y⁻¹ * g y) hp, setIntegral_congr_fun measurableSet_Ioi hc]

open Real in
open scoped FourierTransform in
/-- The substitution `x ↦ x⁻¹` for complex-valued integrands against `dx / x`. -/
private theorem complexLogFourier_finitePart_inv_subC (g : ℝ → ℂ) :
    ∫ x in Ioi 0, ((x⁻¹ : ℝ) : ℂ) * g x⁻¹ = ∫ x in Ioi 0, ((x⁻¹ : ℝ) : ℂ) * g x := by
  have hp : (-1 : ℝ) ≠ 0 := by norm_num
  have hc : EqOn (fun x : ℝ ↦ (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
      ((((x ^ (-1 : ℝ))⁻¹ : ℝ) : ℂ) * g (x ^ (-1 : ℝ))))
      (fun x ↦ ((x⁻¹ : ℝ) : ℂ) * g x⁻¹) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [rpow_neg_one, inv_inv, abs_neg, abs_one, one_mul, Complex.real_smul]
    rw [show (-1 : ℝ) - 1 = -2 by norm_num, rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      rpow_natCast]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
  rw [← integral_comp_rpow_Ioi (fun y ↦ ((y⁻¹ : ℝ) : ℂ) * g y) hp,
    setIntegral_congr_fun measurableSet_Ioi hc]

open Real in
open scoped FourierTransform in
/-- The logarithm is integrable against `e^{-t}` on the positive reals. -/
private theorem complexLogFourier_finitePart_log_exp_integrable :
    IntegrableOn (fun t ↦ log t * exp (-t)) (Ioi 0) := by
  have h1 := GammaIntegral_convergent (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := GammaIntegral_convergent (show (0 : ℝ) < 3 / 2 by norm_num)
  refine ((h1.add h2).const_mul 2).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (exp_pos _).le]
  have e1 : t ^ ((1 / 2 : ℝ) - 1) = t⁻¹ ^ (1 / 2 : ℝ) := by
    rw [inv_rpow ht.le, ← rpow_neg ht.le]; norm_num
  have e2 : t ^ ((3 / 2 : ℝ) - 1) = t ^ (1 / 2 : ℝ) := by norm_num
  show |log t| * exp (-t) ≤ 2 * (exp (-t) * t ^ ((1 / 2 : ℝ) - 1) + exp (-t) * t ^ ((3 / 2 : ℝ) - 1))
  rw [e1, e2]
  have h1 := log_le_rpow_div ht.le (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := log_le_rpow_div (inv_pos.mpr ht).le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [log_inv] at h2
  have p1 : 0 ≤ t ^ (1 / 2 : ℝ) := rpow_nonneg ht.le _
  have p2 : 0 ≤ t⁻¹ ^ (1 / 2 : ℝ) := rpow_nonneg (inv_pos.mpr ht).le _
  have hl : |log t| ≤ 2 * (t⁻¹ ^ (1 / 2 : ℝ) + t ^ (1 / 2 : ℝ)) := by
    rw [abs_le]; constructor <;> linarith
  have := exp_pos (-t)
  calc |log t| * exp (-t) ≤ 2 * (t⁻¹ ^ (1 / 2 : ℝ) + t ^ (1 / 2 : ℝ)) * exp (-t) := by gcongr
    _ = _ := by ring

open Real in
open scoped FourierTransform in
/-- Bounds for `e^{-t} - 1/(1+t)` on the positive reals. -/
private theorem complexLogFourier_finitePart_psi_bound {t : ℝ} (ht : 0 < t) :
    |exp (-t) - (1 + t)⁻¹| ≤ min t t⁻¹ ∧ t⁻¹ * |exp (-t) - (1 + t)⁻¹| ≤ 2 * ((1 + t) ^ 2)⁻¹ := by
  have h1 : exp (-t) ≤ (1 + t)⁻¹ := by
    rw [exp_neg]; exact inv_anti₀ (by linarith) (by linarith [add_one_le_exp t])
  have h2 : 1 - t ≤ exp (-t) := by linarith [add_one_le_exp (-t)]
  have hpos := exp_pos (-t)
  rw [abs_of_nonpos (by linarith), neg_sub]
  -- |ψ| = (1+t)⁻¹ - e^{-t} ≤ (1+t)⁻¹ - (1 - t) = t²/(1+t), and ≤ (1+t)⁻¹
  have hA : (1 + t)⁻¹ - exp (-t) ≤ t ^ 2 * (1 + t)⁻¹ := by
    have : (1 + t)⁻¹ - (1 - t) = t ^ 2 * (1 + t)⁻¹ := by field_simp; ring
    linarith
  have hB : (1 + t)⁻¹ - exp (-t) ≤ (1 + t)⁻¹ := by linarith
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  constructor
  · refine le_min ?_ ?_
    · refine hA.trans ?_
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; nlinarith
    · refine hB.trans ?_
      exact inv_anti₀ ht (by linarith)
  · rcases le_total t 1 with h | h
    · calc t⁻¹ * ((1 + t)⁻¹ - exp (-t)) ≤ t⁻¹ * (t ^ 2 * (1 + t)⁻¹) := by gcongr
        _ = t * (1 + t)⁻¹ := by field_simp
        _ ≤ 2 * ((1 + t) ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by positivity)]
          nlinarith
    · calc t⁻¹ * ((1 + t)⁻¹ - exp (-t)) ≤ t⁻¹ * (1 + t)⁻¹ := by gcongr
        _ ≤ 2 * ((1 + t) ^ 2)⁻¹ := by
          rw [← mul_inv, inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith

open Real in
open scoped FourierTransform in
/-- `(e^{-t} - 1/(1+t)) / t` is integrable on the positive reals. -/
private theorem complexLogFourier_finitePart_psi_integrable :
    IntegrableOn (fun t ↦ t⁻¹ * (exp (-t) - (1 + t)⁻¹)) (Ioi 0) := by
  have hd : IntegrableOn (fun t : ℝ ↦ 2 * ((1 + t) ^ 2)⁻¹) (Ioi 0) := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
      (by simp)).integrableOn (s := Ioi 0)
    refine IntegrableOn.congr_fun (h.const_mul 2) (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi
    simp only [Real.norm_eq_abs, abs_of_pos ht]
    rw [rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
  refine hd.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht]
  exact (complexLogFourier_finitePart_psi_bound ht).2

open Real in
open scoped FourierTransform in
/-- The symmetric splitting of `e^{-1/s} - 1 + e^{-s}`. -/
private theorem complexLogFourier_finitePart_phi_split {s : ℝ} (hs : 0 < s) :
    exp (-s⁻¹) - 1 + exp (-s) = (exp (-s) - (1 + s)⁻¹) + (exp (-s⁻¹) - (1 + s⁻¹)⁻¹) := by
  have : (1 + s)⁻¹ + (1 + s⁻¹)⁻¹ = 1 := by field_simp; ring
  linarith

open Real in
open scoped FourierTransform in
/-- `|e^{-1/s} - 1 + e^{-s}| ≤ 2 min(s, 1/s)` on the positive reals. -/
private theorem complexLogFourier_finitePart_phi_bound {s : ℝ} (hs : 0 < s) : |exp (-s⁻¹) - 1 + exp (-s)| ≤ 2 * min s s⁻¹ := by
  rw [complexLogFourier_finitePart_phi_split hs]
  have h1 := (complexLogFourier_finitePart_psi_bound hs).1
  have h2 := (complexLogFourier_finitePart_psi_bound (inv_pos.mpr hs)).1
  rw [inv_inv, min_comm] at h2
  linarith [abs_add_le (exp (-s) - (1 + s)⁻¹) (exp (-s⁻¹) - (1 + s⁻¹)⁻¹)]

open Real in
open scoped FourierTransform in
/-- `∫₀^∞ (e^{-1/s} - 1 + e^{-s}) ds / s = -2γ`, by integration by parts against the logarithm. -/
private theorem complexLogFourier_finitePart_k0 : IntegrableOn (fun s ↦ s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s))) (Ioi 0) ∧
    ∫ s in Ioi 0, s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s)) = -2 * eulerMascheroniConstant := by
  let ψ : ℝ → ℝ := fun t ↦ exp (-t) - (1 + t)⁻¹
  have hint : IntegrableOn (fun s ↦ s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s))) (Ioi 0) := by
    have h2 : IntegrableOn (fun s ↦ s⁻¹ * ψ s⁻¹) (Ioi 0) := (complexLogFourier_finitePart_inv_sub ψ).1.mpr complexLogFourier_finitePart_psi_integrable
    refine (complexLogFourier_finitePart_psi_integrable.add h2).congr_fun (fun s (hs : 0 < s) ↦ ?_) measurableSet_Ioi
    simp only [ψ, Pi.add_apply]
    rw [complexLogFourier_finitePart_phi_split hs, mul_add]
  refine ⟨hint, ?_⟩
  -- integration by parts against the logarithm
  let g : ℝ → ℝ := fun t ↦ -(t * log t * exp (-t))
  have hg1 : EqOn (fun x : ℝ ↦ x⁻¹ * g x⁻¹) (fun x ↦ log x * ((x ^ 2)⁻¹ * exp (-x⁻¹))) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [g, log_inv]
    field_simp
  have hg2 : EqOn (fun x : ℝ ↦ x⁻¹ * g x) (fun x ↦ -(log x * exp (-x))) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [g]
    field_simp
  have hLint := complexLogFourier_finitePart_log_exp_integrable
  have hA : IntegrableOn (fun x ↦ log x * ((x ^ 2)⁻¹ * exp (-x⁻¹))) (Ioi 0) := by
    rw [← integrableOn_congr_fun hg1 measurableSet_Ioi, (complexLogFourier_finitePart_inv_sub g).1,
      integrableOn_congr_fun hg2 measurableSet_Ioi]
    exact hLint.neg
  have hAval : ∫ x in Ioi 0, log x * ((x ^ 2)⁻¹ * exp (-x⁻¹)) = -∫ x in Ioi 0, log x * exp (-x) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hg1, (complexLogFourier_finitePart_inv_sub g).2,
      setIntegral_congr_fun measurableSet_Ioi hg2, integral_neg]
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt log x⁻¹ x := fun x hx ↦ hasDerivAt_log (ne_of_gt hx)
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s ↦ exp (-s⁻¹) - 1 + exp (-s))
      ((x ^ 2)⁻¹ * exp (-x⁻¹) - exp (-x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun s ↦ exp (-s⁻¹)) (exp (-x⁻¹) * (-(-(x ^ 2)⁻¹))) x :=
      ((hasDerivAt_inv (ne_of_gt hx)).neg).exp
    have h2 : HasDerivAt (fun s ↦ exp (-s)) (exp (-x) * (-1)) x := (hasDerivAt_neg x).exp
    convert (h1.sub_const 1).add h2 using 1
    ring
  have huv' : IntegrableOn (log * fun x ↦ (x ^ 2)⁻¹ * exp (-x⁻¹) - exp (-x)) (Ioi 0) := by
    refine (hA.sub hLint).congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, Pi.sub_apply]; ring
  have hu'v : IntegrableOn ((fun x : ℝ ↦ x⁻¹) * fun s ↦ exp (-s⁻¹) - 1 + exp (-s)) (Ioi 0) := hint
  have hlim_top : Tendsto (log * fun s ↦ exp (-s⁻¹) - 1 + exp (-s)) atTop (𝓝 0) := by
    have hl : Tendsto (fun s ↦ 2 * (log s / s)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 2
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_gt_atTop 1] with s hs
    have hs0 : 0 < s := by linarith
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (log_pos hs)]
    have hb := complexLogFourier_finitePart_phi_bound hs0
    have hm : min s s⁻¹ ≤ s⁻¹ := min_le_right _ _
    have := log_pos hs
    calc log s * |exp (-s⁻¹) - 1 + exp (-s)| ≤ log s * (2 * s⁻¹) := by gcongr; linarith
      _ = 2 * (log s / s) := by ring
  have hlim_zero : Tendsto (log * fun s ↦ exp (-s⁻¹) - 1 + exp (-s)) (𝓝[>] 0) (𝓝 0) := by
    have hl : Tendsto (fun s : ℝ ↦ 2 * (log s⁻¹ / s⁻¹)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun s ↦ 2 * (log s / s)) atTop (𝓝 0) := by
        simpa using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 2
      exact this.comp tendsto_inv_nhdsGT_zero
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_neg (log_neg hs0 hs1)]
    have hb := complexLogFourier_finitePart_phi_bound hs0
    have hm : min s s⁻¹ ≤ s := min_le_left _ _
    have := log_neg hs0 hs1
    calc -log s * |exp (-s⁻¹) - 1 + exp (-s)| ≤ -log s * (2 * s) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 2 * (log s⁻¹ / s⁻¹) := by rw [log_inv]; field_simp
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hlim_zero hlim_top
  simp only [sub_zero, zero_sub] at hibp
  have hsplit : ∫ x in Ioi 0, log x * ((x ^ 2)⁻¹ * exp (-x⁻¹) - exp (-x)) =
      (∫ x in Ioi 0, log x * ((x ^ 2)⁻¹ * exp (-x⁻¹))) - ∫ x in Ioi 0, log x * exp (-x) := by
    rw [← integral_sub hA hLint]; congr 1; funext x; ring
  rw [hsplit, hAval] at hibp
  rw [eulerMascheroniConstant_eq_neg_integral_log]
  linarith

open Real in
open scoped FourierTransform in
/-- `∫₀^∞ (e^{-a/s} - 1 + e^{-bs}) ds / s = -2γ - log(ab)`. -/
private theorem complexLogFourier_finitePart_cconst {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun s ↦ s⁻¹ * (exp (-(a * s⁻¹)) - 1 + exp (-(b * s)))) (Ioi 0) ∧
      ∫ s in Ioi 0, s⁻¹ * (exp (-(a * s⁻¹)) - 1 + exp (-(b * s))) =
        -2 * eulerMascheroniConstant - log (a * b) := by
  obtain ⟨hf1, vf1⟩ := complexLogFourier_finitePart_frullani_exp hb one_pos
  obtain ⟨hf2, vf2⟩ := complexLogFourier_finitePart_frullani_exp ha one_pos
  let g : ℝ → ℝ := fun t ↦ exp (-a * t) - exp (-1 * t)
  have h2 : IntegrableOn (fun s ↦ s⁻¹ * g s⁻¹) (Ioi 0) := (complexLogFourier_finitePart_inv_sub g).1.mpr hf2
  have v2 : ∫ s in Ioi 0, s⁻¹ * g s⁻¹ = log (1 / a) := (complexLogFourier_finitePart_inv_sub g).2.trans vf2
  obtain ⟨hk, vk⟩ := complexLogFourier_finitePart_k0
  have he : EqOn (fun s ↦ s⁻¹ * (exp (-(a * s⁻¹)) - 1 + exp (-(b * s))))
      ((fun y ↦ y⁻¹ * (exp (-b * y) - exp (-1 * y))) + (fun s ↦ s⁻¹ * g s⁻¹) +
        fun s ↦ s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s))) (Ioi 0) := by
    intro s _
    simp only [g, Pi.add_apply, neg_mul, one_mul]
    ring
  have hsum := (hf1.add h2).add hk
  refine ⟨hsum.congr_fun he.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add' (hf1.add h2) hk,
    integral_add' hf1 h2, vf1, v2, vk, log_mul ha.ne' hb.ne', one_div, one_div, log_inv, log_inv]
  ring

open Real in
open scoped FourierTransform in
/-- The Gaussian integral over a disc in the complex plane. -/
private theorem complexLogFourier_finitePart_ball_gauss {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, exp (-(s * ‖x‖ ^ 2)) = π / s * (1 - exp (-(s * ε))) := by
  have hmeas : MeasurableSet {x : ℂ | ‖x‖ ^ 2 < ε} := measurableSet_lt (by fun_prop) (by fun_prop)
  let f : ℝ → ℝ := fun r ↦ if r ^ 2 < ε then exp (-(s * r ^ 2)) else 0
  have h1 : ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, exp (-(s * ‖x‖ ^ 2)) = ∫ x : ℂ, f ‖x‖ := by
    rw [← integral_indicator hmeas]
    congr 1
  rw [h1, integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real]
  rw [hball]
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • f y = ∫ y in (0 : ℝ)..√ε, y * exp (-(s * y ^ 2)) := by
    rw [intervalIntegral.integral_of_le (sqrt_nonneg _), integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
    congr 1; funext y
    simp only [indicator, mem_Ioi, mem_Ioo, f, smul_eq_mul]
    by_cases hy : 0 < y
    · have : y ^ 2 < ε ↔ y < √ε := by
        rw [lt_sqrt hy.le]
      by_cases hy2 : y ^ 2 < ε
      · simp [hy, hy2, this.mp hy2]
      · simp [hy, hy2, mt this.mpr hy2]
    · simp [hy]
  have h3 : ∫ y in (0 : ℝ)..√ε, y * exp (-(s * y ^ 2)) = (1 - exp (-(s * ε))) / (2 * s) := by
    have hd : ∀ y ∈ uIcc (0 : ℝ) √ε, HasDerivAt (fun y ↦ -exp (-(s * y ^ 2)) / (2 * s))
        (y * exp (-(s * y ^ 2))) y := by
      intro y _
      have := (((hasDerivAt_pow 2 y).const_mul s).neg.exp).neg.div_const (2 * s)
      convert this using 1
      simp only [Pi.neg_apply]
      field_simp
      ring_nf
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun y : ℝ ↦ y * exp (-(s * y ^ 2))).intervalIntegrable _ _), sq_sqrt hε.le]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
      exp_zero]
    field_simp
    ring
  rw [h2, h3, smul_eq_mul, nsmul_eq_mul]
  push_cast
  field_simp

open Real in
open scoped FourierTransform in
/-- The Laplace transform of the constant one. -/
private theorem complexLogFourier_finitePart_exp_Ioi {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s ↦ exp (-(r * s))) (Ioi 0) ∧ ∫ s in Ioi (0 : ℝ), exp (-(r * s)) = r⁻¹ := by
  have h := exp_neg_integrableOn_Ioi 0 hr
  simp only [neg_mul] at h
  refine ⟨h, ?_⟩
  have := integral_exp_mul_Ioi (show -r < 0 by linarith) 0
  simp only [neg_mul, mul_zero, exp_zero] at this
  rw [this]; field_simp

open Real in
open scoped FourierTransform in
/-- Writing `1 / ‖x‖²` as a Laplace integral and exchanging the integrations. -/
private theorem complexLogFourier_finitePart_fubini_gen {w : ℂ → ℂ} (hw : Measurable w) {S : Set ℂ}
    (h0 : ∀ᵐ x ∂(volume.restrict S), x ≠ 0)
    (hi : IntegrableOn (fun x ↦ w x / ((‖x‖ ^ 2 : ℝ) : ℂ)) S) :
    IntegrableOn (fun s ↦ ∫ x in S, w x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), ∫ x in S, w x * (exp (-(s * ‖x‖ ^ 2)) : ℂ) =
        ∫ x in S, w x / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  let Fk : ℂ → ℝ → ℂ := fun x s ↦ w x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)
  have hF : Measurable (Function.uncurry Fk) := by
    unfold Fk Function.uncurry
    exact (hw.comp measurable_fst).mul (by fun_prop)
  have hx (x : ℂ) (hx : x ≠ 0) :
      Integrable (Fk x) (volume.restrict (Ioi 0)) ∧
        ∫ s in Ioi (0 : ℝ), ‖Fk x s‖ = ‖w x / ((‖x‖ ^ 2 : ℝ) : ℂ)‖ ∧
        ∫ s in Ioi (0 : ℝ), Fk x s = w x / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have hr : 0 < ‖x‖ ^ 2 := by positivity
    obtain ⟨hI, hV⟩ := complexLogFourier_finitePart_exp_Ioi hr
    have hI' : IntegrableOn (fun s ↦ exp (-(s * ‖x‖ ^ 2))) (Ioi 0) := by
      simpa only [mul_comm] using hI
    have hV' : ∫ s in Ioi (0 : ℝ), exp (-(s * ‖x‖ ^ 2)) = (‖x‖ ^ 2)⁻¹ := by
      simpa only [mul_comm] using hV
    refine ⟨hI'.ofReal.const_mul (w x), ?_, ?_⟩
    · simp only [Fk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
      rw [integral_const_mul, hV', norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
        div_eq_mul_inv]
    · simp only [Fk]
      have hc : ∫ s in Ioi (0 : ℝ), (exp (-(s * ‖x‖ ^ 2)) : ℂ) =
          ((∫ s in Ioi (0 : ℝ), exp (-(s * ‖x‖ ^ 2)) : ℝ) : ℂ) := integral_ofReal
      rw [integral_const_mul, hc, hV', Complex.ofReal_inv, div_eq_mul_inv]
  have hint : Integrable (Function.uncurry Fk) ((volume.restrict S).prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [h0] with x hx0 using (hx x hx0).1
    · refine hi.norm.congr ?_
      filter_upwards [h0] with x hx0 using ((hx x hx0).2.1).symm
  refine ⟨hint.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hint]
  refine integral_congr_ae ?_
  filter_upwards [h0] with x hx0 using (hx x hx0).2.2

open Real in
open scoped FourierTransform in
/-- `1 / ‖x‖` is integrable on discs in the plane. -/
private theorem complexLogFourier_finitePart_inv_norm_ball {r : ℝ} : IntegrableOn (fun x : ℂ ↦ ‖x‖⁻¹) (Metric.ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar (μ := volume) (f := fun y : ℝ ↦ y⁻¹), Complex.finrank_real_complex]
  refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y (hy : y ∈ Ioo 0 r) ↦ ?_)
    measurableSet_Ioo
  simp [smul_eq_mul, hy.1.ne']

open Real in
open scoped FourierTransform in
/-- The remainder of a Lipschitz-at-zero function over a shrinking disc tends to zero. -/
private theorem complexLogFourier_finitePart_disc_tendsto {g : ℂ → ℂ} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x - g 0‖ ≤ C * ‖x‖) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  have hm (ε : ℝ) : MeasurableSet {x : ℂ | ‖x‖ ^ 2 < ε} := measurableSet_lt (by fun_prop) (by fun_prop)
  simp_rw [← integral_indicator (hm _)]
  suffices key : Tendsto (fun ε : ℝ ↦ ∫ x : ℂ, {x : ℂ | ‖x‖ ^ 2 < ε}.indicator
      (fun x ↦ (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ)) x) (𝓝[>] 0) (𝓝 (∫ x : ℂ, (0 : ℂ))) by
    rwa [integral_zero] at key
  refine tendsto_integral_filter_of_dominated_convergence
    ((Metric.ball (0 : ℂ) 1).indicator fun x ↦ |C| * ‖x‖⁻¹) ?_ ?_ ?_ ?_
  · filter_upwards with ε
    refine (Measurable.indicator ?_ (hm ε)).aestronglyMeasurable
    exact ((hg.sub continuous_const).measurable).div (by fun_prop)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine ae_of_all _ fun x ↦ ?_
    by_cases hx : ‖x‖ ^ 2 < ε
    · have hx1 : x ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        nlinarith [norm_nonneg x, hε.2]
      rw [indicator_of_mem (show x ∈ {x : ℂ | ‖x‖ ^ 2 < ε} from hx), indicator_of_mem hx1]
      rcases eq_or_ne x 0 with rfl | h0
      · simp
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr h0
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖g x - g 0‖ / ‖x‖ ^ 2 ≤ C * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact hC x
        _ ≤ |C| * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact le_abs_self C
        _ = |C| * ‖x‖⁻¹ := by field_simp
    · rw [indicator_of_notMem (show x ∉ {x : ℂ | ‖x‖ ^ 2 < ε} from hx), norm_zero]
      exact indicator_nonneg (fun _ _ ↦ by positivity) _
  · exact (integrable_indicator_iff measurableSet_ball).mpr (complexLogFourier_finitePart_inv_norm_ball.const_mul _)
  · filter_upwards [Measure.ae_ne volume (0 : ℂ)] with x hx
    have hn : 0 < ‖x‖ ^ 2 := by positivity
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hn] with ε hε
    rw [indicator_of_notMem]
    simp only [mem_ofPred_eq, not_lt]; exact hε.2.le

open Real in
open scoped FourierTransform in
/-- The logarithmic Fourier pairing as an integral over Gaussian scales. -/
private theorem complexLogFourier_finitePart_fourier_side {g : ℂ → ℂ} (hg : Continuous g) (hgi : Integrable g) (hf : Integrable (𝓕 g))
    (hfc : Continuous (𝓕 g))
    (hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ)) :
    ∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * ((exp (-(π ^ 2) * y) : ℂ) * g 0 -
        ((π * y)⁻¹ : ℂ) * ∫ x, g x * Complex.exp (-(‖x‖ ^ 2 / y : ℝ))) := by
  have hπ : 0 < π ^ 2 := by positivity
  let Fk : ℂ → ℝ → ℂ := fun ξ y ↦ ((y⁻¹ * (exp (-(π ^ 2) * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) * 𝓕 g ξ
  have hF : Measurable (Function.uncurry Fk) := by
    unfold Fk Function.uncurry
    refine Measurable.mul (by fun_prop) ?_
    exact hfc.measurable.comp measurable_fst
  have hx (ξ : ℂ) (hξ : ξ ≠ 0) :
      Integrable (Fk ξ) (volume.restrict (Ioi 0)) ∧
        ∫ y in Ioi (0 : ℝ), ‖Fk ξ y‖ = ‖(log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ‖ ∧
        ∫ y in Ioi (0 : ℝ), Fk ξ y = (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ := by
    have hβ : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by positivity
    obtain ⟨hI, hV⟩ := complexLogFourier_finitePart_frullani_exp hπ hβ
    have hA := complexLogFourier_finitePart_frullani_abs hπ hβ
    have hq : π ^ 2 * ‖ξ‖ ^ 2 / π ^ 2 = ‖ξ‖ ^ 2 := by field_simp
    rw [hq] at hV hA
    refine ⟨hI.ofReal.mul_const _, ?_, ?_⟩
    · have e : ∀ y, ‖Fk ξ y‖ = |y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y))| * ‖𝓕 g ξ‖ :=
        fun y ↦ by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp_rw [e]
      rw [integral_mul_const, hA, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    · have hc : ∫ y in Ioi (0 : ℝ), ((y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) =
          ((∫ y in Ioi (0 : ℝ), y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) :=
        integral_ofReal
      simp only [Fk]
      rw [integral_mul_const, hc, hV]
  have hint : Integrable (Function.uncurry Fk) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ using (hx ξ hξ).1
    · refine hlog.norm.congr ?_
      filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ using ((hx ξ hξ).2.1).symm
  have hL : ∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ = ∫ ξ, ∫ y in Ioi (0 : ℝ), Fk ξ y := by
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ using ((hx ξ hξ).2.2).symm
  rw [hL, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
  -- the inner integral at a fixed scale
  have hmass : ∫ ξ, 𝓕 g ξ = g 0 := by
    have hinv := congrFun (hg.fourierInv_fourier_eq hgi hf) 0
    rw [Real.fourierInv_eq'] at hinv
    simpa using hinv
  have hb : 0 < ((π ^ 2 * y : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; exact mul_pos hπ hy
  set b : ℂ := ((π ^ 2 * y : ℝ) : ℂ) with hbdef
  have hGi : Integrable (fun v : ℂ ↦ Complex.exp (-b * ‖v‖ ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0
  have hFG (x : ℂ) : 𝓕 (fun v : ℂ ↦ Complex.exp (-b * ‖v‖ ^ 2)) x =
      ((π * y)⁻¹ : ℂ) * Complex.exp (-(‖x‖ ^ 2 / y : ℝ)) := by
    rw [fourier_gaussian_innerProductSpace hb, Complex.finrank_real_complex]
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hπ' : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one, hbdef]
    push_cast
    congr 1
    · field_simp
    · congr 1; field_simp
  have hgauss : ∫ ξ, Complex.exp (-b * ‖ξ‖ ^ 2) * 𝓕 g ξ =
      ((π * y)⁻¹ : ℂ) * ∫ x, g x * Complex.exp (-(‖x‖ ^ 2 / y : ℝ)) := by
    have he := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℂ)
      Real.continuous_fourierChar continuous_inner hgi hGi
    rw [flip_innerₗ] at he
    change (∫ ξ, 𝓕 g ξ • Complex.exp (-b * ‖ξ‖ ^ 2)) =
      ∫ x, g x • 𝓕 (fun v : ℂ ↦ Complex.exp (-b * ‖v‖ ^ 2)) x at he
    simp only [smul_eq_mul, hFG] at he
    rw [← integral_const_mul]
    simp only [mul_comm (Complex.exp _) (𝓕 g _)]
    rw [he]
    congr 1; funext x
    ring
  have hGi2 : Integrable (fun ξ : ℂ ↦ Complex.exp (-b * ‖ξ‖ ^ 2) * 𝓕 g ξ) := by
    refine hf.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun ξ ↦ ?_)
    have e : -b * (‖ξ‖ : ℂ) ^ 2 = ((-(π ^ 2 * y) * ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
      rw [hbdef]; push_cast; ring
    rw [e, Complex.norm_exp, Complex.ofReal_re, exp_le_one_iff]
    have := mul_pos hπ hy
    nlinarith [sq_nonneg ‖ξ‖]
  have hpt (ξ : ℂ) : ((y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) * 𝓕 g ξ =
      ((y⁻¹ : ℝ) : ℂ) * ((exp (-π ^ 2 * y) : ℂ) * 𝓕 g ξ - Complex.exp (-b * ‖ξ‖ ^ 2) * 𝓕 g ξ) := by
    have e : Complex.exp (-b * ‖ξ‖ ^ 2) = ((exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp, hbdef]; push_cast; ring_nf
    rw [e]; push_cast; ring
  simp only [Fk, hpt]
  rw [integral_const_mul, integral_sub (hf.const_mul _) hGi2, integral_const_mul, hmass, hgauss]

open Real in
open scoped FourierTransform in
/-- The planar finite-part identity for the logarithm, for Lebesgue measure and the standard
Fourier transform. -/
private theorem complexLogFourier_finitePart_core {g : ℂ → ℂ} (hg : Continuous g) (hgi : Integrable g) (hf : Integrable (𝓕 g))
    (hfc : Continuous (𝓕 g))
    (hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ))
    {C : ℝ} (hC : ∀ x, ‖g x - g 0‖ ≤ C * ‖x‖) :
    (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) {x | ε ≤ ‖x‖ ^ 2}) ∧
    Tendsto (fun ε : ℝ ↦ (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) +
        (π : ℂ) * g 0 * (log ε : ℂ)) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * ((∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ) +
        2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0))) := by
  have hπ0 : 0 < π := pi_pos
  have hπC : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hmA (ε : ℝ) : MeasurableSet {x : ℂ | ε ≤ ‖x‖ ^ 2} := measurableSet_le (by fun_prop) (by fun_prop)
  have hmB (ε : ℝ) : MeasurableSet {x : ℂ | ‖x‖ ^ 2 < ε} := measurableSet_lt (by fun_prop) (by fun_prop)
  -- integrability on the outer region
  have hA (ε : ℝ) (hε : 0 < ε) : IntegrableOn (fun x ↦ g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) {x | ε ≤ ‖x‖ ^ 2} := by
    refine (hgi.integrableOn.norm.const_mul ε⁻¹).mono' ?_ ?_
    · exact (hg.measurable.div (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (hmA ε)] with x (hx : ε ≤ ‖x‖ ^ 2)
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_mul_inv, mul_comm]
      gcongr
  refine ⟨hA, ?_⟩
  set I := ∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ with hIdef
  -- Gaussian averages of the test
  let G : ℝ → ℂ := fun s ↦ ∫ x, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)
  -- the Fourier side after the substitution s = 1/y
  have hIs : I = ∫ s in Ioi (0 : ℝ), (((s⁻¹ * exp (-(π ^ 2 * s⁻¹)) : ℝ) : ℂ) * g 0 -
      (π : ℂ)⁻¹ * G s) := by
    rw [hIdef, complexLogFourier_finitePart_fourier_side hg hgi hf hfc hlog]
    rw [← complexLogFourier_finitePart_inv_subC]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
    simp only [G]
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e : ∀ x : ℂ, Complex.exp (-(‖x‖ ^ 2 / s⁻¹ : ℝ)) = (exp (-(s * ‖x‖ ^ 2)) : ℂ) := by
      intro x; rw [Complex.ofReal_exp]; congr 1; push_cast; field_simp
    simp only [e]
    push_cast
    field_simp
  have key (ε : ℝ) (hε : 0 < ε) :
      (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) + (π : ℂ) * g 0 * (log ε : ℂ) =
        -(π : ℂ) * (I + 2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0) -
          ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    set A := {x : ℂ | ε ≤ ‖x‖ ^ 2}
    set B := {x : ℂ | ‖x‖ ^ 2 < ε}
    have hAB : Aᶜ = B := by ext x; simp [A, B, not_le]
    have h0A : ∀ᵐ x ∂(volume.restrict A), x ≠ 0 := by
      filter_upwards [ae_restrict_mem (hmA ε)] with x (hx : ε ≤ ‖x‖ ^ 2)
      rintro rfl; simp at hx; linarith
    have h0B : ∀ᵐ x ∂(volume.restrict B), x ≠ 0 := ae_restrict_of_ae (Measure.ae_ne volume 0)
    have hBball : B ⊆ Metric.ball (0 : ℂ) (√ε + 1) := by
      intro x (hx : ‖x‖ ^ 2 < ε)
      rw [mem_ball_zero_iff]
      have : ‖x‖ < √ε := by rw [lt_sqrt (norm_nonneg _)]; exact hx
      linarith
    have hiB : IntegrableOn (fun x ↦ (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ)) B := by
      refine ((complexLogFourier_finitePart_inv_norm_ball (r := √ε + 1)).mono_set hBball |>.const_mul |C|).mono' ?_ ?_
      · exact ((hg.measurable.sub_const _).div (by fun_prop)).aestronglyMeasurable
      · filter_upwards [h0B] with x hx
        have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        calc ‖g x - g 0‖ / ‖x‖ ^ 2 ≤ C * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact hC x
          _ ≤ |C| * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact le_abs_self C
          _ = |C| * ‖x‖⁻¹ := by field_simp
    obtain ⟨hQi, hQv⟩ := complexLogFourier_finitePart_fubini_gen (w := g) hg.measurable h0A (hA ε hε)
    obtain ⟨hEi, hEv⟩ := complexLogFourier_finitePart_fubini_gen (w := fun x ↦ g x - g 0) (hg.measurable.sub_const _) h0B hiB
    obtain ⟨hci, hcv⟩ := complexLogFourier_finitePart_cconst (a := π ^ 2) (b := ε) (by positivity) hε
    have hG (s : ℝ) (hs : 0 < s) : G s = (∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        (∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        g 0 * ((π / s * (1 - exp (-(s * ε))) : ℝ) : ℂ) := by
      have hint : Integrable (fun x ↦ g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) := by
        refine hgi.mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun x ↦ ?_)
        rw [Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
        have := sq_nonneg ‖x‖; nlinarith
      have hBe : IntegrableOn (fun x : ℂ ↦ (exp (-(s * ‖x‖ ^ 2)) : ℂ)) B := by
        refine Measure.integrableOn_of_bounded (M := 1) ?_ (by fun_prop) (ae_of_all _ fun x ↦ ?_)
        · exact ((measure_mono hBball).trans_lt measure_ball_lt_top).ne
        · rw [Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
          have := sq_nonneg ‖x‖; nlinarith
      have hsplit : (∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) =
          (∫ x in B, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) - g 0 * ∫ x in B, (exp (-(s * ‖x‖ ^ 2)) : ℂ) := by
        simp only [sub_mul]
        rw [integral_sub hint.integrableOn (hBe.const_mul _), integral_const_mul]
      have hball : ∫ x in B, (exp (-(s * ‖x‖ ^ 2)) : ℂ) = ((π / s * (1 - exp (-(s * ε))) : ℝ) : ℂ) := by
        have hc : ∫ x in B, (exp (-(s * ‖x‖ ^ 2)) : ℂ) = ((∫ x in B, exp (-(s * ‖x‖ ^ 2)) : ℝ) : ℂ) :=
          integral_ofReal
        rw [hc, complexLogFourier_finitePart_ball_gauss hs hε]
      rw [hsplit, hball]
      simp only [G]
      rw [← integral_add_compl (hmA ε) hint, hAB]
      ring
    have hpt : EqOn (fun s ↦ ((s⁻¹ * exp (-(π ^ 2 * s⁻¹)) : ℝ) : ℂ) * g 0 - (π : ℂ)⁻¹ * G s)
        (fun s ↦ g 0 * ((s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ) -
          (π : ℂ)⁻¹ * ((∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
            ∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ))) (Ioi 0) := by
      intro s (hs : 0 < s)
      simp only
      rw [hG s hs, mul_comm ε s]
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      push_cast
      field_simp
      ring
    have hc : ∫ s in Ioi (0 : ℝ), ((s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ) =
        ((∫ s in Ioi (0 : ℝ), s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ) :=
      integral_ofReal
    have h1 : IntegrableOn (fun s ↦ g 0 *
        ((s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ)) (Ioi 0) :=
      (hci.ofReal (𝕜 := ℂ)).const_mul (g 0)
    have h2 : IntegrableOn (fun s ↦ (π : ℂ)⁻¹ * ((∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        ∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ))) (Ioi 0) :=
      (hQi.add hEi).const_mul _
    have hsum : ∫ s in Ioi (0 : ℝ), ((∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        ∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) =
        (∫ x in A, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) + ∫ x in B, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [integral_add hQi hEi, hQv, hEv]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub h1 h2, integral_const_mul,
      integral_const_mul, hsum, hc, hcv] at hIs
    have hlog2 : log (π ^ 2 * ε) = 2 * log π + log ε := by
      rw [log_mul (by positivity) hε.ne', log_pow]; push_cast; ring
    rw [hlog2] at hIs
    have hπI : (π : ℂ) * I = (π : ℂ) * (g 0 * ((-2 * eulerMascheroniConstant - (2 * log π + log ε) : ℝ) : ℂ)) -
        ((∫ x in A, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) + ∫ x in B, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
      rw [hIs]; field_simp
    push_cast at hπI ⊢
    linear_combination hπI
  have hT := (tendsto_const_nhds (x := -(π : ℂ) * (I + 2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0))).sub
    (complexLogFourier_finitePart_disc_tendsto hg hC)
  rw [sub_zero] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (key ε hε).symm

open Real in
open scoped FourierTransform in
/-- Fourier inversion at the origin. -/
private theorem complexLogFourier_finitePart_mass (g : 𝓢(ℂ, ℂ)) : ∫ ξ, 𝓕 (g : ℂ → ℂ) ξ = g 0 := by
  have hf : Integrable (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).integrable
  have hinv := congrFun (g.continuous.fourierInv_fourier_eq g.integrable hf) 0
  rw [Real.fourierInv_eq'] at hinv
  simpa using hinv

open Real in
open scoped FourierTransform in
/-- The logarithm of the squared norm is integrable against Schwartz functions on the plane. -/
private theorem complexLogFourier_finitePart_logint (g : 𝓢(ℂ, ℂ)) : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * g ξ) := by
  have h := integrable_abs_log_norm_div_one_add_norm_pow (volume : Measure ℂ) (by simp)
  simp only [Complex.finrank_real_complex] at h
  obtain ⟨Λ, hΛ⟩ := RiemannMasullo.SchwartzMap.exists_strongDual_integral_mul (volume : Measure ℂ)
    (fun t ↦ (log (‖t‖ ^ 2) : ℂ))
    ((Complex.measurable_ofReal.comp (measurable_norm.pow_const 2).log).aestronglyMeasurable) 4
    ((h.const_mul 2).congr (ae_of_all _ fun t ↦ by
      simp only [Complex.norm_real, Real.norm_eq_abs, Real.log_pow]
      push_cast
      rw [abs_mul, abs_two]; ring))
  exact (hΛ g).1

open Real in
open scoped FourierTransform in
/-- The logarithmic pairing in the normalization of the complex completion, after the
change of variables `ξ = 2 conj t`. -/
private theorem complexLogFourier_finitePart_pairing (g : 𝓢(ℂ, ℂ)) :
    Integrable (fun t : ℂ ↦ (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t))) ∧
    ∫ t, (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t)) ∂(2 • volume) =
      (∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) - (log 4 : ℂ) * g 0 := by
  have hf : Integrable (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).integrable
  have hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using complexLogFourier_finitePart_logint (𝓕 g)
  let h : ℂ → ℂ := fun ξ ↦ (log (‖ξ‖ ^ 2 / 4) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ
  have hh (t : ℂ) : (log (‖t‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t) = h ((2 : ℝ) • star t) := by
    simp only [h, norm_smul, Real.norm_two, norm_star]
    congr 3; ring
  have hconj := (Complex.conjLIE.measurePreserving).integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding (fun u ↦ h ((2 : ℝ) • u))
  have hsc := Measure.integral_comp_smul (volume : Measure ℂ) h 2
  have hval : ∫ ξ, h ξ = (∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) - (log 4 : ℂ) * g 0 := by
    rw [← complexLogFourier_finitePart_mass g, ← integral_const_mul, ← integral_sub hlog (hf.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ
    simp only [h]
    rw [log_div (by positivity) (by norm_num)]
    push_cast; ring
  have hhi : Integrable h := by
    refine (hlog.sub (hf.const_mul (log 4 : ℂ))).congr ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ
    simp only [h, Pi.sub_apply]
    rw [log_div (by positivity) (by norm_num)]
    push_cast; ring
  have hcj (t : ℂ) : h ((2 : ℝ) • Complex.conjLIE t) = h ((2 : ℝ) • star t) := by
    rw [Complex.conjLIE_apply]; rfl
  have hi : Integrable (fun t : ℂ ↦ (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t))) := by
    have h1 : Integrable (fun u : ℂ ↦ h ((2 : ℝ) • u)) := hhi.comp_smul two_ne_zero
    have h2 : Integrable ((fun u : ℂ ↦ h ((2 : ℝ) • u)) ∘ Complex.conjLIE) :=
      ((Complex.conjLIE.measurePreserving).integrable_comp_emb (g := fun u : ℂ ↦ h ((2 : ℝ) • u))
        Complex.conjLIE.toHomeomorph.measurableEmbedding).mpr h1
    refine (h2.const_mul 2).congr (ae_of_all _ fun t ↦ ?_)
    change 2 * h ((2 : ℝ) • Complex.conjLIE t) = _
    rw [hcj, ← hh t]; ring
  refine ⟨hi, ?_⟩
  rw [show (2 • volume : Measure ℂ) = volume + volume from two_smul ℕ _,
    integral_add_measure hi hi]
  have hone : ∫ t, (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t)) =
      2 * ∫ t, h ((2 : ℝ) • Complex.conjLIE t) := by
    rw [← integral_const_mul]; congr 1; funext t
    rw [hcj, ← hh t]; ring
  rw [hone, hconj, hsc, ← hval, Complex.finrank_real_complex]
  norm_num
  ring

open Real in
open scoped FourierTransform in
/-- The planar finite-part identity in the normalization of the complex completion. -/
private theorem complexLogFourier_finitePart_final (g : 𝓢(ℂ, ℂ)) :
    Integrable (fun t : ℂ ↦ (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t)))
      (2 • volume) ∧
    (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) {x | ε ≤ ‖x‖ ^ 2}
      (2 • volume)) ∧
    Tendsto (fun ε : ℝ ↦ (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, g x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(2 • volume)) +
        ((2 * π : ℝ) : ℂ) * g 0 * (log ε : ℂ)) (𝓝[>] 0)
      (𝓝 (-((2 * π : ℝ) : ℂ) * ((∫ t, (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t))
        ∂(2 • volume)) + ((2 * (log (2 * π) + eulerMascheroniConstant) : ℝ) : ℂ) * g 0))) := by
  have hf : Integrable (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).integrable
  have hfc : Continuous (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).continuous
  have hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using complexLogFourier_finitePart_logint (𝓕 g)
  obtain ⟨C, -, hC⟩ := g.decay 0 1
  have hC' (x : ℂ) : ‖g x - g 0‖ ≤ C * ‖x‖ := by
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := (g : ℂ → ℂ))
      (fun y _ ↦ g.differentiableAt) (fun y _ ↦ by
        have := hC y
        simpa [norm_iteratedFDeriv_one] using this) (mem_univ 0) (mem_univ x)
    simpa using this
  obtain ⟨hA, hT⟩ := complexLogFourier_finitePart_core g.continuous g.integrable hf hfc hlog hC'
  -- the measure 2 • volume
  have h2 : (2 • (volume : Measure ℂ)) = volume + volume := two_smul ℕ _
  -- the change of variables in the logarithmic pairing
  obtain ⟨hi, hJ⟩ := complexLogFourier_finitePart_pairing g
  have h2v : (2 • volume : Measure ℂ) = volume + volume := two_smul ℕ _
  refine ⟨by rw [h2v]; exact hi.add_measure hi, fun ε hε ↦ ?_, ?_⟩
  · rw [h2v]; exact (hA ε hε).add_measure (hA ε hε)
  rw [hJ]
  have l4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring
  have l2π : log (2 * π) = log 2 + log π := log_mul two_ne_zero pi_ne_zero
  have hlim : -((2 * π : ℝ) : ℂ) * (((∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) - (log 4 : ℂ) * g 0) +
      ((2 * (log (2 * π) + eulerMascheroniConstant) : ℝ) : ℂ) * g 0) =
      2 * (-(π : ℂ) * ((∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) +
        2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0)) := by
    rw [l4, l2π]; push_cast; ring
  rw [hlim]
  refine (hT.const_mul (2 : ℂ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [h2v, Measure.restrict_add, integral_add_measure (hA ε hε) (hA ε hε)]
  push_cast; ring

/-- Paper: Proposition B.4.3.2(2), p. 619. The complex Fourier pairing
equals minus the finite part divided by 2π, with the squared module in the cutoff.
Deviation: Divides the printed distribution by 2π. -/
theorem complexLogFourier_finitePart (w : InfinitePlace F) (_hw : w.IsComplex)
    (f : 𝒮ₐ(w.Completion)) :
    let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
    Integrable K ν∞(w) ∧
      (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ))
        {x : w.Completion | ε ≤ ‖x‖ ^ 2} ν∞(w)) ∧
      Tendsto (fun ε : ℝ ↦ (∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2},
        addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂ν∞(w)) +
        (2 * Real.pi : ℝ) * addTest(f) 0 * (Real.log ε : ℂ))
        (𝓝[>] 0) (𝓝 (-(2 * Real.pi : ℝ) *
          ((∫ y, K y ∂ν∞(w)) + (2 * eulerLogConstant : ℝ) * addTest(f) 0))) := by
  intro K
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex _hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex _hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  have hμ : ν∞(w) = (2 • (volume : Measure ℂ)).map m :=
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr _hw)
  have hem (t : ℂ) : e (m t) = t := e.apply_symm_apply t
  have hnorm (t : ℂ) : ‖m t‖ = ‖t‖ := by
    change ‖j.symm t‖ = ‖t‖
    rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
      show j.symm 0 = 0 from map_zero e.symm]
  obtain ⟨g, hg⟩ := complexModelSchwartz w _hw f
  have hf : addTest(f) = fun x ↦ g (e x) := by
    funext x
    rw [hg]
    exact congrArg (fun y ↦ addTest(f) y) (e.symm_apply_apply x).symm
  have hK (t : ℂ) : K (m t) =
      (Real.log (‖t‖ ^ 2) : ℂ) * (2 * FourierTransform.fourier (g : ℂ → ℂ) ((2 : ℝ) • star t)) := by
    change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
    rw [_hw.mult_eq_two, hnorm, hf, complexModelFourier w _hw, hem]
  have hf' (x : w.Completion) : f (Multiplicative.ofAdd x) = g (e x) := congrFun hf x
  obtain ⟨hint, hcut, hlim⟩ := complexLogFourier_finitePart_final g
  simp only [hμ, integrable_map_equiv, integrableOn_map_equiv, setIntegral_map_equiv,
    integral_map_equiv, Function.comp_def, preimage_ofPred_eq, hK, hnorm, hf', hem, map_zero]
  exact ⟨hint, hcut, hlim⟩

end LocalFourier

section PrincipalValues

local notation "scaledMeasure(" v ", " a ")" =>
  (ENNReal.ofReal (Real.sqrt ‖(a : (HeightOneSpectrum.adicCompletion F v)ˣ).val‖) • ν𝔭(v))
local notation "scaledChar(" v ", " a ")" => (fun x ↦ ψ𝔭(v) (Units.val a * x))
local notation "zeroExtend(" f ")" => (Function.extend Units.val (f : _ → ℂ) (fun _ ↦ 0))
local notation "weightedTranslate(" abs ", " f ")" =>
  (fun x ↦ zeroExtend(f) (1 + x) / (Real.sqrt (abs (1 + x)) : ℂ))

/-- The finite Fourier transform is additive and homogeneous on continuous compactly
supported functions. -/
private theorem exists_finiteConnesPrincipalValue_fourier_linear (v : Primes(F)) (c : ℂ)
    (u w : v.adicCompletion F → ℂ) (hu : Continuous u) (hu' : HasCompactSupport u)
    (hw : Continuous w) (hw' : HasCompactSupport w) (y : v.adicCompletion F) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ u x + w x) y =
        tamagawaFourier ν𝔭(v) ψ𝔭(v) u y + tamagawaFourier ν𝔭(v) ψ𝔭(v) w y ∧
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ c * u x) y =
        c * tamagawaFourier ν𝔭(v) ψ𝔭(v) u y := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hψ0 := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  have hψ : Continuous (finiteLocalStandardCharacter F v) :=
    (hψ0.choose.continuous.comp continuous_ofAdd).congr hψ0.choose_spec.1
  have hχ : Continuous fun x : v.adicCompletion F ↦ star (ψ𝔭(v) (x * y) : ℂ) :=
    continuous_star.comp (continuous_subtype_val.comp (hψ.comp (continuous_id.mul continuous_const)))
  have hi (z : v.adicCompletion F → ℂ) (hz : Continuous z) (hz' : HasCompactSupport z) :
      Integrable (fun x ↦ z x * star (ψ𝔭(v) (x * y) : ℂ)) ν𝔭(v) :=
    (hz.mul hχ).integrable_of_hasCompactSupport hz'.mul_right
  unfold tamagawaFourier
  refine ⟨?_, ?_⟩
  · rw [← integral_add (hi u hu hu') (hi w hw hw')]
    exact integral_congr_ae (ae_of_all _ fun x ↦ add_mul _ _ _)
  · rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x ↦ mul_assoc _ _ _)

/-- Every additive and homogeneous functional on the additive tests of a finite completion is
continuous, since their topology is the finest locally convex one. -/
private theorem exists_finiteConnesPrincipalValue_ofLinear (v : Primes(F))
    (L : 𝒮ₐ(v.adicCompletion F) → ℂ) (hadd : ∀ f g, L (f + g) = L f + L g)
    (hsmul : ∀ (c : ℂ) f, L (c • f) = c * L f) (P : 𝒮ₐ(v.adicCompletion F) → ℂ → Prop)
    (hP : ∀ f, P f (L f)) :
    ∃ T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)), ∀ f, P f (T f) := by
  let ℓ : 𝒮ₐ(v.adicCompletion F) →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := hadd
      map_smul' := hsmul }
  have h := continuous_of_finestLocallyConvex (𝒮ₐ(v.adicCompletion F)) (M := ℂ) ℓ
  exact ⟨⟨ℓ, (congrArg (fun t ↦ @Continuous _ ℂ t _ ℓ)
    (finitePlaceSchwartz_finestTopology F v)).mpr h⟩, hP⟩

/-- The logarithm pairs integrably with the dilated Fourier transform of an additive test. -/
private theorem exists_finiteConnesPrincipalValue_integrable (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)) ν𝔭(v) := by
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v) :=
    (finiteLog_integrable_mul_test v g).congr (ae_of_all _ fun y ↦ by
      simp only [hg])
  exact (finiteLogFourier_comp_mul v f a hint).1

/-- The pairing of the logarithm with the dilated Fourier transform is additive. -/
private theorem exists_finiteConnesPrincipalValue_add (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f g : 𝒮ₐ(v.adicCompletion F)) :
    ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f + g) (a.val * y) ∂ν𝔭(v) =
      (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) ∂ν𝔭(v)) +
        ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) (a.val * y)
          ∂ν𝔭(v) := by
  have hreg (f : 𝒮ₐ(v.adicCompletion F)) :
      Continuous (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) ∧
        HasCompactSupport (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) :=
    ⟨(schwartzBruhat_continuous f).comp continuous_ofAdd,
      ((mem_finitePlaceSchwartz_iff F v _).1 ⟨f, fun _ ↦ rfl⟩).2⟩
  refine Eq.trans ?_ (integral_add (exists_finiteConnesPrincipalValue_integrable v a f)
    (exists_finiteConnesPrincipalValue_integrable v a g))
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have h : tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f + g) (a.val * y) =
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) +
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) (a.val * y) :=
    (exists_finiteConnesPrincipalValue_fourier_linear v 1 _ _ (hreg f).1 (hreg f).2
      (hreg g).1 (hreg g).2 (a.val * y)).1
  exact (congrArg (((J𝔭(v) y : ℝ) : ℂ) * ·) h).trans (mul_add _ _ _)

/-- The pairing of the logarithm with the dilated Fourier transform is homogeneous. -/
private theorem exists_finiteConnesPrincipalValue_smul (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (c : ℂ) (f : 𝒮ₐ(v.adicCompletion F)) :
    ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(c • f) (a.val * y) ∂ν𝔭(v) =
      c * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)
        ∂ν𝔭(v) := by
  have hreg : Continuous (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) ∧
      HasCompactSupport (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) :=
    ⟨(schwartzBruhat_continuous f).comp continuous_ofAdd,
      ((mem_finitePlaceSchwartz_iff F v _).1 ⟨f, fun _ ↦ rfl⟩).2⟩
  refine Eq.trans ?_ (integral_const_mul c _)
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have h : tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(c • f) (a.val * y) =
      c * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) :=
    (exists_finiteConnesPrincipalValue_fourier_linear v c _ _ hreg.1 hreg.2
      hreg.1 hreg.2 (a.val * y)).2
  exact (congrArg (((J𝔭(v) y : ℝ) : ℂ) * ·) h).trans (mul_left_comm _ _ _)

/-- The scaled pairing is `√‖a‖` times the dilated pairing, and integrable. -/
private theorem exists_finiteConnesPrincipalValue_scale (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v), addTest(f)))
        scaledMeasure(v, a) ∧
      -(V𝔭(v) : ℂ) * ((√‖a.val‖ * √‖a.val‖ : ℝ) : ℂ) *
          ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)
            ∂ν𝔭(v) =
        -(V𝔭(v) : ℂ) * ∫ y, logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v),
          addTest(f)) y ∂scaledMeasure(v, a) := by
  have hc : (ENNReal.ofReal √‖a.val‖).toReal = √‖a.val‖ :=
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  -- Changing the character and the measure dilates the transform and scales it by `√‖a‖`.
  have hF (y : v.adicCompletion F) :
      tamagawaFourier (ENNReal.ofReal √‖a.val‖ • ν𝔭(v)) (fun x ↦ ψ𝔭(v) (a.val * x))
        addTest(f) y = (√‖a.val‖ : ℝ) • tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) := by
    unfold tamagawaFourier
    rw [integral_smul_measure, hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [mul_left_comm a.val x y]
  have hK : logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v), addTest(f)) =
      fun y ↦ ((√‖a.val‖ : ℝ) : ℂ) * (((J𝔭(v) y : ℝ) : ℂ) *
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)) := by
    funext y
    rw [hF, Complex.real_smul]
    ring
  rw [hK]
  refine ⟨((exists_finiteConnesPrincipalValue_integrable v a f).const_mul _).smul_measure
    ENNReal.ofReal_ne_top, ?_⟩
  rw [integral_smul_measure, hc, integral_const_mul, Complex.real_smul]
  push_cast
  ring

/-- Paper: Definition B.4.4.1(1), p. 619. The scaled finite Fourier
pairing defines a continuous linear functional on additive tests.
Deviation: The additive character is allowed to be any translate of the standard character
by a nonzero field multiplier, with the corresponding self-dual measure. -/
theorem exists_finiteConnesPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    ∃ T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)),
      ∀ f : 𝒮ₐ(v.adicCompletion F),
        let ν := scaledMeasure(v, a)
        let K : v.adicCompletion F → ℂ := logFourierIntegrand(ν, scaledChar(v, a), J𝔭(v), addTest(f))
        Integrable K ν ∧ T f = -(V𝔭(v) : ℂ) * ∫ y, K y ∂ν :=
  exists_finiteConnesPrincipalValue_ofLinear v (fun f ↦
    -(V𝔭(v) : ℂ) * ((√‖a.val‖ * √‖a.val‖ : ℝ) : ℂ) *
      ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) ∂ν𝔭(v))
    (fun f g ↦ by rw [exists_finiteConnesPrincipalValue_add, mul_add])
    (fun c f ↦ by rw [exists_finiteConnesPrincipalValue_smul, mul_left_comm])
    (fun f z ↦ Integrable (logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v),
        addTest(f))) scaledMeasure(v, a) ∧
      z = -(V𝔭(v) : ℂ) * ∫ y, logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v),
        addTest(f)) y ∂scaledMeasure(v, a))
    (exists_finiteConnesPrincipalValue_scale v a)

/-- Paper: Definition B.4.4.1(1), p. 619. Connes's finite additive
principal value pairs the Fourier-transformed test with the normalized logarithm.
Deviation: The nonzero multiplier specifies the character as in (B.4.4.12). -/
def finiteConnesPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    StrongDual ℂ (𝒮ₐ(v.adicCompletion F)) := (exists_finiteConnesPrincipalValue v a).choose

/-- Paper: Definition B.4.4.1(1), p. 619. Outside the singularity, the finite
additive principal value for the standard character is ordinary multiplicative integration. -/
theorem finiteConnesPrincipalValue_one_of_apply_zero (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) (_hf : addTest(f) 0 = 0) :
    finiteConnesPrincipalValue v 1 f =
      ∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v) := by
  have hT := ((exists_finiteConnesPrincipalValue v 1).choose_spec f).2
  have hK := (finiteLogFourier_eq_neg_haar v f _hf).2.2
  have hV : V𝔭(v) ≠ 0 := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
  change finiteConnesPrincipalValue v 1 f = _ at hT
  simp only [Units.val_one, norm_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
    one_mul] at hT
  rw [hT, hK, mul_div, neg_mul_neg]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hV)

/-- The elementary Schwartz space of a real vector group is the usual Schwartz space. -/
private theorem exists_infiniteConnesPrincipalValue_elementaryEquiv (d : ℕ) :
    ∃ e : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) ≃L[ℂ] ElementarySchwartz d 0 0 PUnit,
      ∀ f x, e f x = f x.1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let X := 𝓢(E, ℂ)
  let Y := ElementarySchwartz d 0 0 PUnit
  let L : X →ₗ[ℂ] Y :=
    { toFun := fun f ↦ ⟨fun x ↦ f x.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL (f : X) (x : ElementaryLieGroup d 0 0 PUnit) : L f x = f x.1 := rfl
  have hbij : Bijective L := by
    constructor
    · intro f g h
      ext x
      exact congrArg (fun s : Y ↦ s (x, 0, 0, 0)) h
    · intro g
      let f (x : E) := g (x, 0, 0, 0)
      have heq : (fun x : ElementaryLieGroup d 0 0 PUnit ↦ f x.1) = g.val := by
        funext x
        exact congrArg g (Prod.ext rfl (Subsingleton.elim _ _))
      have hmem := (elementarySchwartzSubmodule_real_iff f).mp (heq ▸ g.property)
      obtain ⟨s, hs⟩ := hmem
      refine ⟨s, Subtype.ext ?_⟩
      change (fun x : ElementaryLieGroup d 0 0 PUnit ↦ s x.1) = g.val
      rw [← heq]
      exact congrArg (fun u : E → ℂ ↦ fun x : ElementaryLieGroup d 0 0 PUnit ↦ u x.1) hs
  have hX : IsFrechetTVS X := euclideanSchwartz_frechet d
  have : BarrelledSpace ℂ X := isFrechetTVS_barrelled hX
  have hc : Continuous L := by
    apply continuous_toElementarySchwartz_of_eval
    intro g
    exact ⟨(BoundedContinuousFunction.evalCLM ℂ g.1).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ), fun _ ↦ rfl⟩
  obtain ⟨hTX, -, hMX, hCX⟩ := hX
  obtain ⟨hTY, -, hMY, hCY⟩ := elementarySchwartz_isFrechet (m := d) (n := 0) (r := 0) (F := PUnit)
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hCX
  have : CompleteSpace Y := hCY
  have : (uniformity Y).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero Y]
    infer_instance
  have : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  let A : X →L[ℂ] Y := ⟨L, hc⟩
  have hopen : IsOpenMap A := by
    apply isOpenMap_of_not_isMeagre_range A
    change ¬ IsMeagre (range L)
    rw [hbij.surjective.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let e := LinearEquiv.ofBijective L hbij
  refine ⟨{ e with continuous_toFun := hc, continuous_invFun := ?_ }, hL⟩
  exact e.toEquiv.continuous_symm_iff.mpr hopen

/-- A real vector coordinate gives a largest structural pair, with whole open subgroup,
presented by the real vector group. -/
private theorem exists_infiniteConnesPrincipalValue_presentation {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {d : ℕ}
    (c : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d))) :
    ∃ a : BruhatStructuralPair G, (∀ b, b ≤ a) ∧ ∃ (hm : ∀ x : G, x ∈ a.val.1)
        (w : a.quotient ≃ₜ* Multiplicative (ElementaryLieGroup d 0 0 PUnit)),
        ∀ x : G, (w (QuotientGroup.mk ⟨x, hm x⟩)).toAdd.1 = (c x).toAdd := by
  have : ConnectedSpace (Multiplicative (EuclideanSpace ℝ (Fin d))) :=
    inferInstanceAs (ConnectedSpace (EuclideanSpace ℝ (Fin d)))
  have : ConnectedSpace G := c.symm.surjective.connectedSpace c.symm.continuous
  let chart : EuclideanSpace ℝ (Fin d) ≃ₜ G := c.symm.toHomeomorph
  have hgood : IsBruhatGoodSubgroup (⊥ : Subgroup G) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨d, ⟨chart.chartedSpace⟩⟩
  let H : Subgroup G := ⊤
  let i : G ≃ₜ* H :=
    ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩
  have htop : IsOpen (H : Set G) := isOpen_univ
  let : ConnectedSpace H := i.surjective.connectedSpace i.continuous
  let : LocallyCompactSpace H := htop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen : IsCompactlyGeneratedGroup H := by
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : H)
    have hOpen : IsOpen (Subgroup.closure U : Set H) :=
      Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
    exact ⟨U, hU, hUc, SetLike.coe_injective
      ((OpenSubgroup.isClopen ⟨Subgroup.closure U, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩
  let a : BruhatStructuralPair G := ⟨(H, OrderDual.toDual ⊥), htop, hgen, hgood, bot_le⟩
  have hmem (x : G) : x ∈ a.val.1 := Subgroup.mem_top x
  let p := (QuotientGroup.mk' _ : H →* a.quotient).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hinj : Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := (MulEquiv.ofBijective p ⟨hinj, hp.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hp.isQuotientMap.isOpen_preimage)
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) := uniqueOfSubsingleton 0
  let w : Multiplicative (ElementaryLieGroup d 0 0 PUnit) ≃ₜ*
      Multiplicative (EuclideanSpace ℝ (Fin d)) :=
    ContinuousMulEquiv.mk' (Homeomorph.prodUnique _ _) (fun _ _ ↦ rfl)
  have ha (b : BruhatStructuralPair G) : b ≤ a := by
    change b.val.1 ≤ ⊤ ∧ (⊥ : Subgroup G) ≤ OrderDual.ofDual b.val.2
    exact ⟨le_top, bot_le⟩
  refine ⟨a, ha, hmem, q.symm.trans (c.trans w.symm), fun x ↦ ?_⟩
  change (w (w.symm (c (q.symm (q x))))).toAdd = _
  rw [q.symm_apply_apply, w.apply_symm_apply]

/-- In real vector coordinates, the Schwartz–Bruhat space carries the usual Schwartz
topology. -/
private theorem exists_infiniteConnesPrincipalValue_coordinate {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {d : ℕ}
    (c : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d))) :
    ∃ e : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) ≃L[ℂ] SchwartzBruhat G,
      ∀ f x, e f x = f (c x).toAdd := by
  have : SecondCountableTopology (Multiplicative (EuclideanSpace ℝ (Fin d))) :=
    inferInstanceAs (SecondCountableTopology (EuclideanSpace ℝ (Fin d)))
  have : SecondCountableTopology G := c.toHomeomorph.isEmbedding.secondCountableTopology
  refine (exists_infiniteConnesPrincipalValue_presentation c).elim fun a hp ↦ ?_
  refine hp.2.elim fun hm hm' ↦ hm'.elim fun w hw ↦ ?_
  have ha := hp.1
  let e : ElementaryLCAPresentation a.quotient := ⟨d, 0, 0, PUnit, w⟩
  let J : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  have hJ : Topology.IsEmbedding J := schwartzBruhatStage_isEmbedding a e
  have hs : Surjective J := schwartzBruhat_maxStage_surjective a ha e
  let A := LinearEquiv.ofBijective J ⟨hJ.injective, hs⟩
  let B := ContinuousLinearEquiv.ofIsHomeomorph A
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hJ, hs⟩)
  refine (exists_infiniteConnesPrincipalValue_elementaryEquiv d).elim fun T hT ↦ ?_
  refine ⟨T.trans B, fun f x ↦ ?_⟩
  change (show SchwartzBruhat G from schwartzBruhatStageInclusion a e (T f)) x = _
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (hm x), hT]
  exact congrArg f (hw x)

/-- If, in a model of the completion, the logarithmic Fourier integrand is a weight of
polynomial growth times a Schwartz function depending continuously on the test, then
its integral is a continuous linear functional. -/
private theorem exists_infiniteConnesPrincipalValue_ofModel (w : InfinitePlace F)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] (m : V ≃ᵐ w.Completion) (μ : Measure V)
    (hμ : ν∞(w) = μ.map m) (Q : 𝒮ₐ(w.Completion) →L[ℂ] 𝓢(V, ℂ)) (L : V → ℂ)
    (hL : AEStronglyMeasurable L μ) (k : ℕ)
    (hk : Integrable (fun t ↦ ‖L t‖ / (1 + ‖t‖) ^ k) μ)
    (hK : ∀ (f : 𝒮ₐ(w.Completion)) (t : V),
      logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f)) (m t) = L t * Q f t) :
    ∃ T : StrongDual ℂ (𝒮ₐ(w.Completion)), ∀ f : 𝒮ₐ(w.Completion),
      let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
      Integrable K ν∞(w) ∧ T f = -(∫ y, K y ∂ν∞(w)) := by
  obtain ⟨Λ, hΛ⟩ := SchwartzMap.exists_strongDual_integral_mul μ L hL k hk
  refine ⟨-(Λ.comp Q), fun f ↦ ?_⟩
  intro K
  have hKm : K ∘ m = fun t ↦ L t * Q f t := funext (hK f)
  rw [hμ, integrable_map_equiv, integral_map_equiv]
  refine ⟨hKm ▸ (hΛ (Q f)).1, ?_⟩
  change -(Λ (Q f)) = -(∫ t, (K ∘ m) t ∂μ)
  rw [hKm, (hΛ (Q f)).2]

/-- Paper: Definition B.4.4.1(1), p. 619. The archimedean Fourier pairing
defines a continuous linear functional on additive tests. -/
theorem exists_infiniteConnesPrincipalValue (w : InfinitePlace F) :
    ∃ T : StrongDual ℂ (𝒮ₐ(w.Completion)), ∀ f : 𝒮ₐ(w.Completion),
      let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
      Integrable K ν∞(w) ∧ T f = -(∫ y, K y ∂ν∞(w)) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : ν∞(w) = (volume : Measure ℝ).map m := dite_eq_left hw
    have hem (t : ℝ) : e (m t) = t := e.apply_symm_apply t
    have hnorm (t : ℝ) : ‖m t‖ = ‖t‖ := by
      change ‖j.symm t‖ = ‖t‖
      rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
        show j.symm 0 = 0 from map_zero e.symm]
    let c : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
      { toMulEquiv := e.toAddEquiv.toMultiplicative
        continuous_toFun := j.continuous
        continuous_invFun := j.symm.continuous }
    obtain ⟨E, hE⟩ := schwartzBruhat_realCoordinate_equiv c
    have hP (f : 𝒮ₐ(w.Completion)) : addTest(f) = fun x ↦ E.symm f (e x) := by
      funext x
      conv_lhs => rw [← E.apply_symm_apply f]
      exact hE _ _
    refine exists_infiniteConnesPrincipalValue_ofModel w m volume hμ
      ((SchwartzMap.fourierTransformCLM ℂ).comp E.symm.toContinuousLinearMap)
      (fun t ↦ (Real.log ‖t‖ : ℂ))
      (Complex.measurable_ofReal.comp measurable_norm.log).aestronglyMeasurable 3 ?_
      fun f t ↦ ?_
    · have h := integrable_abs_log_norm_div_one_add_norm_pow (volume : Measure ℝ)
        (by simp)
      simp only [Module.finrank_self] at h
      simpa only [Complex.norm_real, Real.norm_eq_abs] using h
    · change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
      rw [hw.mult_eq_one, pow_one, hnorm, hP f, realModelFourier w hw, hem]
      rfl
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : ν∞(w) = (2 • (volume : Measure ℂ)).map m := dite_eq_right hw
    have hem (t : ℂ) : e (m t) = t := e.apply_symm_apply t
    have hnorm (t : ℂ) : ‖m t‖ = ‖t‖ := by
      change ‖j.symm t‖ = ‖t‖
      rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
        show j.symm 0 = 0 from map_zero e.symm]
    let LE : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (LinearEquiv.ofFinrankEq ℂ (EuclideanSpace ℝ (Fin 2)) (by simp)).toContinuousLinearEquiv
    let c₀ : w.Completion ≃ₜ EuclideanSpace ℝ (Fin 2) := j.toHomeomorph.trans LE.toHomeomorph
    let c : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin 2)) :=
      ContinuousMulEquiv.mk' c₀ (fun x y ↦ by
        change LE (e (x.toAdd + y.toAdd)) = LE (e x.toAdd) + LE (e y.toAdd)
        rw [map_add, map_add])
    obtain ⟨E, hE⟩ := exists_infiniteConnesPrincipalValue_coordinate c
    let P : 𝒮ₐ(w.Completion) →L[ℂ] 𝓢(ℂ, ℂ) :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ LE).comp E.symm.toContinuousLinearMap
    have hP (f : 𝒮ₐ(w.Completion)) : addTest(f) = fun x ↦ P f (e x) := by
      funext x
      conv_lhs => rw [← E.apply_symm_apply f]
      exact hE _ _
    let A : ℂ ≃L[ℝ] ℂ := Complex.conjCLE.trans
      (LinearEquiv.smulOfNeZero ℝ ℂ (2 : ℝ) two_ne_zero).toContinuousLinearEquiv
    have hA (z : ℂ) : A z = (2 : ℝ) • star z := rfl
    refine exists_infiniteConnesPrincipalValue_ofModel w m (2 • volume) hμ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A).comp
        ((SchwartzMap.fourierTransformCLM ℂ).comp P))
      (fun t ↦ (Real.log (‖t‖ ^ 2) : ℂ) * 2)
      ((Complex.measurable_ofReal.comp (measurable_norm.pow_const 2).log).mul_const
        _).aestronglyMeasurable 4 ?_ fun f t ↦ ?_
    · have h := integrable_abs_log_norm_div_one_add_norm_pow (volume : Measure ℂ)
        (by simp)
      simp only [Complex.finrank_real_complex] at h
      have h' : Integrable (fun t : ℂ ↦ ‖(Real.log (‖t‖ ^ 2) : ℂ) * 2‖ / (1 + ‖t‖) ^ 4)
          volume := by
        refine (h.const_mul 4).congr (ae_of_all _ fun t ↦ ?_)
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.log_pow]
        norm_num [abs_mul]
        ring
      rw [two_smul]
      exact h'.add_measure h'
    · change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
      rw [hc.mult_eq_two, hnorm, hP f, complexModelFourier w hc, hem]
      change _ = _ * FourierTransform.fourier (P f : ℂ → ℂ) (A t)
      rw [hA]
      ring

/-- Paper: Definition B.4.4.1(1), p. 619. Connes's archimedean additive
principal value is minus the Fourier transform of the logarithm distribution. -/
def infiniteConnesPrincipalValue (w : InfinitePlace F) :
    StrongDual ℂ (𝒮ₐ(w.Completion)) := (exists_infiniteConnesPrincipalValue w).choose

/-- Paper: Definition B.4.4.1(1), p. 619. On real tests vanishing at
zero, the additive principal value is integration against half of the weighted additive measure.
Deviation: The factor one half is the real case of the correction to Proposition B.4.3.2. -/
theorem realConnesPrincipalValue_of_apply_zero (w : InfinitePlace F) (_hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) (_hf : addTest(f) 0 = 0) :
    infiniteConnesPrincipalValue w f =
      (1 / 2 : ℂ) * ∫ x, addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w) := by
  have hT := ((exists_infiniteConnesPrincipalValue w).choose_spec f).2
  change infiniteConnesPrincipalValue w f = _ at hT
  have hL := (realLogFourier_finitePart w _hw f).2.2
  simp only [_hf, mul_zero, zero_mul, add_zero] at hL
  let : BorelSpace w.Completion := ⟨rfl⟩
  -- Real coordinates turn the test into a classical Schwartz function vanishing at zero.
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  let c : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { toMulEquiv := (InfinitePlace.Completion.ringEquivRealOfIsReal _hw).toAddEquiv.toMultiplicative
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have hc := schwartzBruhat_realCoordinate_equiv c
  have hE := hc.choose_spec
  let s := hc.choose.symm f
  have hs (t : ℝ) : s t = addTest(f) (e.symm t) := by
    have := hE s (Multiplicative.ofAdd (e.symm t))
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    refine Eq.trans ?_ this.symm
    exact congrArg s (e.apply_symm_apply t).symm
  have h0 : e.symm 0 = 0 := map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal _hw).symm
  have hnorm (t : ℝ) : ‖e.symm t‖ = ‖t‖ := by
    rw [← dist_zero_right, ← dist_zero_right t, ← e.symm.dist_eq t 0, h0]
  have hs0 : s 0 = 0 := by rw [hs, h0]; exact _hf
  -- The weighted test is integrable on the real line: Lipschitz near zero, decaying at infinity.
  let C := SchwartzMap.seminorm ℝ 0 1 s
  have hlip (t : ℝ) : ‖s t‖ ≤ C * ‖t‖ := by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := s) (s := univ) (C := C)
      (fun x _ ↦ s.differentiableAt) (fun x _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ t)
    · simpa [hs0] using this
    · rw [← norm_iteratedFDeriv_one]
      exact s.norm_iteratedFDeriv_le_seminorm ℝ 1 x
  have hR : Integrable (fun t : ℝ ↦ s t / ((‖t‖ : ℝ) : ℂ)) := by
    refine Integrable.mono' (g := fun t ↦ (Icc (-1 : ℝ) 1).indicator (fun _ ↦ C) t + ‖s t‖)
      ((continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).add
        s.integrable.norm)
      (s.continuous.measurable.div
        (Complex.measurable_ofReal.comp measurable_norm)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [norm_div, Complex.norm_real, norm_norm]
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem ht]
      rcases eq_or_ne t 0 with rfl | ht0
      · simp [hs0, C]
      · have : ‖s t‖ / ‖t‖ ≤ C := (div_le_iff₀ (norm_pos_iff.mpr ht0)).mpr (hlip t)
        linarith [norm_nonneg (s t)]
    · rw [indicator_of_notMem ht, zero_add]
      have h1 : 1 ≤ ‖t‖ := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rw [Real.norm_eq_abs]
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact div_le_self (norm_nonneg _) h1
  have hG : Integrable (fun x : w.Completion ↦ addTest(f) x / ((‖x‖ : ℝ) : ℂ)) ν∞(w) := by
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left _hw]
    let m := e.symm.toHomeomorph.toMeasurableEquiv
    rw [show ((InfinitePlace.Completion.ringEquivRealOfIsReal _hw).symm : ℝ → w.Completion) = m
      from rfl, integrable_map_equiv]
    refine hR.congr (Eventually.of_forall fun t ↦ ?_)
    change s t / ((‖t‖ : ℝ) : ℂ) = addTest(f) (e.symm t) / ((‖e.symm t‖ : ℝ) : ℂ)
    rw [hs, hnorm]
  -- Dominated convergence removes the cutoff.
  have hmeas (ε : ℝ) : MeasurableSet {x : w.Completion | ε ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x in {x : w.Completion | ε ≤ ‖x‖},
      addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w)) (𝓝[>] 0)
      (𝓝 (∫ x, addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w))) := by
    simp_rw [← integral_indicator (hmeas _)]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖addTest(f) x / ((‖x‖ : ℝ) : ℂ)‖)
      (Eventually.of_forall fun ε ↦ hG.aestronglyMeasurable.indicator (hmeas ε))
      (Eventually.of_forall fun ε ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)
      hG.norm (Eventually.of_forall fun x ↦ ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Set.indicator_apply]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (norm_pos_iff.mpr hx))] with ε hε
      rw [indicator_of_mem (show ε ≤ ‖x‖ from hε.le)]
  rw [hT, tendsto_nhds_unique hlim hL]
  ring

/-- Good subgroups of the units of a finite completion are open, because the dual
quotient is locally connected and totally disconnected. -/
private theorem finiteUnits_goodSubgroup_isOpen (v : Primes(F))
    (k : Subgroup (v.adicCompletion F)ˣ) (hk : IsBruhatGoodSubgroup k) :
    IsOpen (k : Set (v.adicCompletion F)ˣ) := by
  let G := (v.adicCompletion F)ˣ
  let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator k, hk.2⟩
  obtain ⟨γ, _, hγ, hker, _⟩ := lca_dualSubgroup_quotient A
  let Q := PontryaginDual A.val
  let : LocallyCompactSpace A.val := A.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨n, ⟨charts⟩⟩ := isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp A.property.2
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q := charts
  let : LocallyConnectedSpace Q := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) Q
  let B : OpenSubgroup G :=
    ⟨(v.adicCompletionIntegers F).units, Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)⟩
  let : CompactSpace B.toSubgroup := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let j : B.toSubgroup → v.adicCompletion F := Units.val ∘ Subtype.val
  have hj : Topology.IsEmbedding j :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).comp Topology.IsEmbedding.subtypeVal
  let η : B.toSubgroup →ₜ* Q := γ.comp ⟨B.toSubgroup.subtype, continuous_subtype_val⟩
  have hη : Continuous η := η.continuous
  have hηOpen : IsOpenMap η := hγ.isOpenMap.comp B.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hSmall (U : Set Q) (hU : U ∈ 𝓝 (1 : Q)) : ∃ V : OpenSubgroup Q, (V : Set Q) ⊆ U := by
    have hpre : η ⁻¹' U ∈ 𝓝 (1 : B.toSubgroup) :=
      hη.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
    rw [hj.isInducing.nhds_eq_comap] at hpre
    obtain ⟨S, hS, hSsub⟩ := mem_comap.mp hpre
    let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨r, hr⟩ := (Valued.mem_nhds (Γ₀ := WithZero (Multiplicative ℤ))).mp hS
    let W := (fun x : B.toSubgroup ↦ j x - j 1) ⁻¹' {y | ν.restrict y < r.val}
    have hW : IsClopen W :=
      (Valued.isClopen_ball (v.adicCompletion F) r.val).preimage
        (hj.continuous.sub continuous_const)
    have h1W : (1 : B.toSubgroup) ∈ W := by
      change ν.restrict (j 1 - j 1) < r.val
      rw [sub_self, map_zero]
      exact pos_iff_ne_zero.mpr r.ne_zero
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1W
    refine ⟨⟨V.toSubgroup.map η.toMonoidHom, hηOpen _ V.isOpen⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hSsub (hr (hV hx))
  have hComponent : connectedComponent (1 : Q) = {1} := by
    refine subset_antisymm ?_ (singleton_subset_iff.mpr mem_connectedComponent)
    intro y hy
    by_contra hne
    have h1y : (1 : Q) ∈ ({y} : Set Q)ᶜ :=
      fun h ↦ hne (mem_singleton_iff.mpr (mem_singleton_iff.mp h).symm)
    obtain ⟨V, hV⟩ := hSmall _ (isOpen_compl_singleton.mem_nhds h1y)
    have hyV := isPreconnected_connectedComponent.subset_isClopen V.isClopen
      ⟨1, mem_connectedComponent, V.one_mem⟩ hy
    exact (hV hyV) (mem_singleton y)
  have hOne : IsOpen ({1} : Set Q) := hComponent ▸ isOpen_connectedComponent
  rw [← lcaDualAnnihilator_annihilator k hk.1, ← hker]
  exact hOne.preimage γ.continuous

/-- A test function on the units of a finite completion is locally constant. -/
private theorem finiteUnits_test_isLocallyConstant (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) : IsLocallyConstant f.val := by
  have hf : IsBruhatSmooth f.val := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1
  obtain ⟨k, hk, hInv, _⟩ := hf 0
  have hkOpen := finiteUnits_goodSubgroup_isOpen v k hk
  refine (IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_
  refine ⟨(fun y ↦ y * x⁻¹) ⁻¹' (k : Set _),
    hkOpen.preimage (by fun_prop : Continuous fun y : (v.adicCompletion F)ˣ ↦ y * x⁻¹), by simp [k.one_mem], fun y hy ↦ ?_⟩
  simpa using hInv ⟨_, hy⟩ x

/-- The norm on the units of a finite completion is locally constant. -/
private theorem finiteUnits_norm_isLocallyConstant (v : Primes(F)) :
    IsLocallyConstant (fun u : (v.adicCompletion F)ˣ ↦ ‖u.val‖) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun u ↦ ?_
  refine ⟨(fun w : (v.adicCompletion F)ˣ ↦ w.val) ⁻¹' {y | ‖y - u.val‖ < ‖u.val‖},
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).preimage
      Units.continuous_val, ?_, fun w hw ↦ ?_⟩
  · change ‖u.val - u.val‖ < ‖u.val‖
    rw [sub_self, norm_zero]
    exact norm_pos_iff.mpr u.ne_zero
  have hw' : ‖w.val - u.val‖ < ‖u.val‖ := hw
  have hne : ‖w.val - u.val‖ ≠ ‖u.val‖ := hw'.ne
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [sub_add_cancel, max_eq_right hw'.le] at h
  exact h

/-- The zero extension of a locally constant compactly supported function on the units
of a finite completion is locally constant and compactly supported. -/
private theorem finiteUnits_extend_regular (v : Primes(F)) (h : (v.adicCompletion F)ˣ → ℂ)
    (hl : IsLocallyConstant h) (hc : HasCompactSupport h) :
    IsLocallyConstant (Function.extend Units.val h (fun _ ↦ (0 : ℂ))) ∧
      HasCompactSupport (Function.extend Units.val h (fun _ ↦ (0 : ℂ))) := by
  have he : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
    Units.isOpenEmbedding_val
  let E : v.adicCompletion F → ℂ := Function.extend Units.val h (fun _ ↦ (0 : ℂ))
  have hEu (u : (v.adicCompletion F)ˣ) : E u.val = h u := Units.val_injective.extend_apply h _ u
  let T := Units.val '' tsupport h
  have hT : IsCompact T := hc.image he.continuous
  have hE0 (y : v.adicCompletion F) (hy : y ∉ T) : E y = 0 := by
    by_cases hr : ∃ u : (v.adicCompletion F)ˣ, u.val = y
    · obtain ⟨u, rfl⟩ := hr
      rw [hEu]
      exact image_eq_zero_of_notMem_tsupport (fun hu ↦ hy ⟨u, hu, rfl⟩)
    · exact extend_apply' _ _ _ hr
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun y ↦ ?_,
    HasCompactSupport.of_support_subset_isCompact hT fun y hy ↦ by_contra fun h' ↦ hy (hE0 y h')⟩
  by_cases hy : y ∈ T
  · obtain ⟨u, -, rfl⟩ := hy
    obtain ⟨U, hU, huU, hconst⟩ := (IsLocallyConstant.iff_exists_open _).1 hl u
    refine ⟨Units.val '' U, he.isOpenMap _ hU, ⟨u, huU, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    change E w.val = E u.val
    rw [hEu, hEu]
    exact hconst w hw
  · refine ⟨Tᶜ, hT.isClosed.isOpen_compl, hy, fun z hz ↦ ?_⟩
    change E z = E y
    rw [hE0 z hz, hE0 y hy]

/-- A fixed-support stage is finite-dimensional when the good subgroup of its structural
pair is open: the compact support then meets finitely many of its cosets. -/
private theorem bruhatCompactSupportStage_finiteDimensional_of_isOpen {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts G) (hk : IsOpen ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G)) :
    FiniteDimensional ℂ (bruhatCompactSupportStage a e C) := by
  classical
  let k := OrderDual.ofDual a.val.2
  let R := schwartzBruhatStageRealization a e
  have hinv (s : SchwartzBruhatStage e) (h : G) (hh : h ∈ k) (x : G) : R s (h * x) = R s x :=
    stage_realization_mul_kernel a e s hh x
  have hRinj (s : SchwartzBruhatStage e) (hs : ∀ x, R s x = 0) : s = 0 := by
    let s' : elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor := s
    change s' = 0
    refine Subtype.ext (funext fun p ↦ ?_)
    let q : a.quotient := e.equiv.symm (Multiplicative.ofAdd p)
    let x : a.val.1 := q.out
    have hxq : (QuotientGroup.mk x : a.quotient) = q := QuotientGroup.out_eq' q
    have h0 : R s x.val = 0 := hs x.val
    rw [schwartzBruhatStageRealization_apply, dite_eq_left x.property] at h0
    change s (Multiplicative.toAdd (e.equiv (QuotientGroup.mk x))) = 0 at h0
    have h1 := congrArg (fun r : a.quotient ↦ s (Multiplicative.toAdd (e.equiv r))) hxq
    have h2 : e.equiv q = Multiplicative.ofAdd p := e.equiv.apply_symm_apply _
    simp only [h2] at h1
    rw [Submodule.coe_zero]
    exact h1.symm.trans h0
  have hcov : (C : Set G) ⊆ ⋃ y : G, (fun z ↦ z * y⁻¹) ⁻¹' (k : Set G) := fun z _ ↦
    mem_iUnion.mpr ⟨z, show z * z⁻¹ ∈ k by rw [mul_inv_cancel]; exact k.one_mem⟩
  have hfin := C.isCompact.elim_finite_subcover
    (fun y : G ↦ (fun z ↦ z * y⁻¹) ⁻¹' (k : Set G))
    (fun y ↦ hk.preimage (continuous_id.mul continuous_const)) hcov
  let t := hfin.choose
  have ht := hfin.choose_spec
  let X := bruhatCompactSupportStage a e C
  let Ψ : bruhatCompactSupportStage a e C →ₗ[ℂ] (t → ℂ) :=
    LinearMap.pi fun y ↦ (LinearMap.proj y.val).comp (R.comp (bruhatCompactSupportStage a e C).subtype)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    refine Subtype.ext ((hRinj s.val fun x ↦ ?_).trans (Submodule.coe_zero (p := X)).symm)
    by_cases hxC : x ∈ (C : Set G)
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hxC)
      have h0 : R s.val y = 0 := congrFun hs ⟨y, hy⟩
      have h1 := hinv s.val (x * y⁻¹) hxy y
      rw [inv_mul_cancel_right] at h1
      rw [h1, h0]
    · exact image_eq_zero_of_notMem_tsupport fun h ↦
        hxC ((mem_bruhatCompactSupportStage_iff a e C s.val).1 s.property h)
  exact Module.Finite.of_injective Ψ hΨ

/-- A fixed-support stage of test functions on the units of a finite completion is
finite-dimensional, since good subgroups of the units are open. -/
private theorem finiteUnits_stage_finiteDimensional (v : Primes(F))
    (a : BruhatStructuralPair (v.adicCompletion F)ˣ) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts (v.adicCompletion F)ˣ) :
    FiniteDimensional ℂ (bruhatCompactSupportStage a e C) :=
  bruhatCompactSupportStage_finiteDimensional_of_isOpen a e C
    (finiteUnits_goodSubgroup_isOpen v _ a.property.2.2.1)

/-- Paper: Definition B.4.4.1(2), p. 620. Translation of the zero-extended
test after inverse square-root weighting gives a continuous linear map to additive tests. -/
theorem exists_finiteWeilTestMap (v : Primes(F)) :
    ∃ A : 𝒟((v.adicCompletion F)ˣ) →L[ℂ] 𝒮ₐ(v.adicCompletion F),
      ∀ (f : 𝒟((v.adicCompletion F)ˣ)) (x : v.adicCompletion F),
        addTest(A f) x = weightedTranslate(norm, f.val) x := by
  let K := v.adicCompletion F
  let G := Kˣ
  let wt (f : 𝒟(G)) : G → ℂ := fun u ↦ f.val u / (Real.sqrt ‖u.val‖ : ℂ)
  let Φ (f : 𝒟(G)) : K → ℂ := fun x ↦ Function.extend Units.val (wt f) (fun _ ↦ (0 : ℂ)) (1 + x)
  have hΦ (f : 𝒟(G)) (x : K) : Φ f x = weightedTranslate(norm, f.val) x := by
    change Function.extend Units.val (wt f) (fun _ ↦ (0 : ℂ)) (1 + x) =
      Function.extend Units.val f.val (fun _ ↦ (0 : ℂ)) (1 + x) / (Real.sqrt ‖1 + x‖ : ℂ)
    by_cases hr : ∃ u : G, u.val = 1 + x
    · obtain ⟨u, hu⟩ := hr
      rw [← hu, Units.val_injective.extend_apply, Units.val_injective.extend_apply]
    · rw [extend_apply' _ _ _ hr, extend_apply' _ _ _ hr, zero_div]
  have hreg (f : 𝒟(G)) : IsLocallyConstant (Φ f) ∧ HasCompactSupport (Φ f) := by
    have hl : IsLocallyConstant (wt f) := (finiteUnits_test_isLocallyConstant v f).comp₂
      ((finiteUnits_norm_isLocallyConstant v).comp fun t ↦ ((Real.sqrt t : ℝ) : ℂ)) (· / ·)
    have hc : HasCompactSupport (wt f) := HasCompactSupport.mono f.property.2 fun u hu h0 ↦ hu (by
      change f.val u / _ = 0
      rw [h0, zero_div])
    obtain ⟨hEl, hEc⟩ := finiteUnits_extend_regular v (wt f) hl hc
    exact ⟨hEl.comp_continuous (continuous_const.add continuous_id),
      hEc.comp_homeomorph (Homeomorph.addLeft (1 : K))⟩
  have hmem (f : 𝒟(G)) : (fun y : Multiplicative K ↦ Φ f y.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative K) := by
    obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v (Φ f)).mpr (hreg f)
    have hgf : (fun y : Multiplicative K ↦ Φ f y.toAdd) = (g : Multiplicative K → ℂ) :=
      funext fun y ↦ (hg y.toAdd).symm
    rw [hgf]
    exact (show schwartzBruhatSubmodule (Multiplicative K) from g).property
  have hadd (f g : 𝒟(G)) (x : K) : Φ (f + g) x = Φ f x + Φ g x := by
    by_cases hr : ∃ u : G, u.val = 1 + x
    · obtain ⟨u, hu⟩ := hr
      simp only [Φ, ← hu, Units.val_injective.extend_apply]
      exact add_div _ _ _
    · simp only [Φ, extend_apply' _ _ _ hr, add_zero]
  have hsmul (c : ℂ) (f : 𝒟(G)) (x : K) : Φ (c • f) x = c • Φ f x := by
    by_cases hr : ∃ u : G, u.val = 1 + x
    · obtain ⟨u, hu⟩ := hr
      simp only [Φ, ← hu, Units.val_injective.extend_apply]
      exact mul_div_assoc _ _ _
    · simp only [Φ, extend_apply' _ _ _ hr, smul_zero]
  let Φlin : 𝒟(G) →ₗ[ℂ] (Multiplicative K → ℂ) :=
    { toFun := fun f y ↦ Φ f y.toAdd
      map_add' := fun f g ↦ funext fun y ↦ hadd f g y.toAdd
      map_smul' := fun c f ↦ funext fun y ↦ hsmul c f y.toAdd }
  let L : 𝒟(G) →ₗ[ℂ] 𝒮ₐ(K) := Φlin.codRestrict _ hmem
  have hcont : Continuous L := by
    let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
        (C : TopologicalSpace.Compacts G), Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
    refine (PolynormableSpace.withSeminorms ℂ (𝒮ₐ(K))).continuous_of_continuous_comp L fun p ↦
      (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
        (⟨p.val.comp L, ?_⟩ : P)
    intro a e C
    let X := bruhatCompactSupportStage a e C
    let : FiniteDimensional ℂ X := finiteUnits_stage_finiteDimensional v a e C
    let : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
    let : ContinuousSMul ℂ (SchwartzBruhatStage e) :=
      elementarySchwartz_withSeminorms.continuousSMul
    let : ContinuousSMul ℂ 𝒮ₐ(K) := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
    let M : X →ₗ[ℂ] 𝒮ₐ(K) :=
      L.comp (show X →ₗ[ℂ] 𝒟(G) from bruhatCompactSupportStageInclusion a e C)
    exact p.property.comp M.continuous_of_finiteDimensional
  exact ⟨⟨L, hcont⟩, fun f x ↦ hΦ f x⟩

/-- Closed graph theorem from a closed subspace of a Fréchet space to a Fréchet space. -/
private theorem weilTest_continuous_of_isClosed_graph {E Y : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y]
    (hE : IsFrechetTVS E) (hY : IsFrechetTVS Y) (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (T : S →ₗ[ℂ] Y) (hT : IsClosed (T.graph : Set (S × Y))) : Continuous T := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hE.2.2.2
  have : CompleteSpace Y := hY.2.2.2
  have : TopologicalSpace.MetrizableSpace E := hE.2.2.1
  have : TopologicalSpace.MetrizableSpace Y := hY.2.2.1
  have : CompleteSpace S := completeSpace_coe_iff_isComplete.mpr hS.isComplete
  have : IsUniformAddGroup S := S.toAddSubgroup.isUniformAddGroup
  let Γ := T.graph
  have : CompleteSpace Γ := completeSpace_coe_iff_isComplete.mpr hT.isComplete
  have : IsUniformAddGroup Γ := Γ.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace S :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (S : Set E))
  have : TopologicalSpace.MetrizableSpace (S × Y) := inferInstance
  have : TopologicalSpace.MetrizableSpace Γ :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Γ : Set (S × Y)))
  have : FirstCountableTopology Γ := inferInstance
  have : FirstCountableTopology S := inferInstance
  have : (uniformity S).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace S := BaireSpace.of_completelyPseudoMetrizable
  let P : Γ →L[ℂ] S := (ContinuousLinearMap.fst ℂ S Y).comp Γ.subtypeL
  have hmem (x : S) : (x, T x) ∈ Γ := (LinearMap.mem_graph_iff _ _).mpr rfl
  have hval (p : Γ) : p.val.2 = T p.val.1 := (LinearMap.mem_graph_iff _ _).mp p.property
  have hinj : Injective P := fun p q h ↦ by
    have h1 : p.val.1 = q.val.1 := h
    exact Subtype.ext (Prod.ext h1 (by rw [hval, hval, h1]))
  have hsurj : Surjective P := fun x ↦ ⟨⟨(x, T x), hmem x⟩, rfl⟩
  have ho : IsOpenMap P := by
    apply isOpenMap_of_not_isMeagre_range P
    rw [hsurj.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let h : Γ ≃ₜ S :=
    (Equiv.ofBijective P ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen P.continuous ho
  refine (continuous_snd.comp (continuous_subtype_val.comp h.symm.continuous)).congr fun x ↦ ?_
  have h1 : (h.symm x).val.1 = x := h.apply_symm_apply x
  change (h.symm x).val.2 = T x
  rw [hval, h1]

/-- A real vector coordinate gives a structural pair with trivial kernel and whole
open subgroup, presented by the real vector group. -/
private theorem weilTest_vectorPresentation {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {d : ℕ}
    (c : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d))) :
    ∃ a : BruhatStructuralPair G, ∃ (hm : ∀ x : G, x ∈ a.val.1)
        (w : a.quotient ≃ₜ* Multiplicative (ElementaryLieGroup d 0 0 PUnit)),
        ∀ x : G, (w (QuotientGroup.mk ⟨x, hm x⟩)).toAdd.1 = (c x).toAdd := by
  have : ConnectedSpace (Multiplicative (EuclideanSpace ℝ (Fin d))) :=
    inferInstanceAs (ConnectedSpace (EuclideanSpace ℝ (Fin d)))
  have : ConnectedSpace G := c.symm.surjective.connectedSpace c.symm.continuous
  let chart : EuclideanSpace ℝ (Fin d) ≃ₜ G := c.symm.toHomeomorph
  have hgood : IsBruhatGoodSubgroup (⊥ : Subgroup G) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨d, ⟨chart.chartedSpace⟩⟩
  let H : Subgroup G := ⊤
  let i : G ≃ₜ* H :=
    ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩
  have htop : IsOpen (H : Set G) := isOpen_univ
  let : ConnectedSpace H := i.surjective.connectedSpace i.continuous
  let : LocallyCompactSpace H := htop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen : IsCompactlyGeneratedGroup H := by
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : H)
    have hOpen : IsOpen (Subgroup.closure U : Set H) :=
      Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
    exact ⟨U, hU, hUc, SetLike.coe_injective
      ((OpenSubgroup.isClopen ⟨Subgroup.closure U, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩
  let a : BruhatStructuralPair G := ⟨(H, OrderDual.toDual ⊥), htop, hgen, hgood, bot_le⟩
  have hmem (x : G) : x ∈ a.val.1 := Subgroup.mem_top x
  let p := (QuotientGroup.mk' _ : H →* a.quotient).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hinj : Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := (MulEquiv.ofBijective p ⟨hinj, hp.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hp.isQuotientMap.isOpen_preimage)
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) := uniqueOfSubsingleton 0
  let w : Multiplicative (ElementaryLieGroup d 0 0 PUnit) ≃ₜ*
      Multiplicative (EuclideanSpace ℝ (Fin d)) :=
    ContinuousMulEquiv.mk' (Homeomorph.prodUnique _ _) (fun _ _ ↦ rfl)
  refine ⟨a, hmem, q.symm.trans (c.trans w.symm), fun x ↦ ?_⟩
  change (w (w.symm (c (q.symm (q x))))).toAdd = _
  rw [q.symm_apply_apply, w.apply_symm_apply]

/-- Extension by zero from the units evaluates the function off zero. -/
private theorem weilTest_zeroExtend_apply {K : Type*} [GroupWithZero K] (f : Kˣ → ℂ) (x : K) :
    Function.extend Units.val f (fun _ ↦ (0 : ℂ)) x =
      if hx : x = 0 then 0 else f (Units.mk0 x hx) := by
  split_ifs with hx
  · subst hx
    exact Function.extend_apply' _ _ _ fun ⟨u, hu⟩ ↦ u.ne_zero hu
  · exact Units.val_injective.extend_apply f (fun _ ↦ (0 : ℂ)) (Units.mk0 x hx)


/-- An exponential-type map with identity derivative has a smooth local inverse at one. -/
private theorem weilTest_localLog {𝕂 : Type*} [RCLike 𝕂] (E : 𝕂 → 𝕂) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0) :
    ∃ Λ : 𝕂 → 𝕂, ContDiffAt ℝ (⊤ : ℕ∞) Λ 1 ∧ ∀ᶠ y in 𝓝 1, E (Λ y) = y := by
  have hn0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hEc : ContDiffAt ℝ (⊤ : ℕ∞) E 0 := hEs.contDiffAt
  have hS := ContDiffAt.hasStrictFDerivAt hEc hEd hn0
  have h0 : (hS.toOpenPartialHomeomorph E).symm (E 0) = 0 := hS.localInverse_apply_image
  have hΛ : ContDiffAt ℝ (⊤ : ℕ∞) (hS.toOpenPartialHomeomorph E).symm (E 0) :=
    (hS.toOpenPartialHomeomorph E).contDiffAt_symm hS.image_mem_toOpenPartialHomeomorph_target
      (by rw [h0]; exact hEd) (by rw [h0]; exact hEc)
  have hright : ∀ᶠ y in 𝓝 (E 0), E ((hS.toOpenPartialHomeomorph E).symm y) = y :=
    hS.eventually_right_inverse
  rw [hE00] at hΛ hright
  exact ⟨_, hΛ, hright⟩


/-- On an elementary presentation, a function smooth on the covers stays smooth along a
continuous one-parameter family of translates given by an additive map from a real vector
space. -/
private theorem weilTest_elementary_curve {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    {𝕂 : Type*} [RCLike 𝕂] {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : ElementaryLCAPresentation Q) (f₀ : Q → ℂ) {N : ℕ∞}
    (hsm : ∀ (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor), ContDiff ℝ (N : WithTop ℕ∞)
      (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt z b)))))
    (θ : 𝕂 →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)
    (hθ : Continuous θ) (q₀ : Q) :
    ContDiff ℝ (N : WithTop ℕ∞)
      (fun v ↦ f₀ (e.equiv.symm (e.equiv q₀ * Multiplicative.ofAdd (θ v)))) := by
  obtain ⟨A, hA, hAv⟩ : ∃ A : ElementaryLieGroup d 0 0 PUnit.{1} →+
      ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor,
      Continuous A ∧ ∀ x, A x = θ (L.symm x.1) :=
    ⟨θ.comp ((L.symm.toLinearMap.toAddMonoidHom).comp (AddMonoidHom.fst _ _)),
      hθ.comp (L.symm.continuous.comp continuous_fst), fun _ ↦ rfl⟩
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor,
      Multiplicative.ofAdd θ₀ = e.equiv q₀ := ⟨_, rfl⟩
  obtain ⟨f', hf'v⟩ : ∃ f' : ElementaryLieGroup e.realDim e.torusDim e.latticeRank
      e.finiteFactor → ℂ, ∀ y, f' y = f₀ (e.equiv.symm (Multiplicative.ofAdd (θ₀ + y))) :=
    ⟨_, fun _ ↦ rfl⟩
  have hf' (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
      ContDiff ℝ (N : WithTop ℕ∞) (fun u ↦ f' (elementaryCover u z b)) := by
    obtain ⟨t, ht⟩ := elementaryCover_surjective θ₀.2.2.1 θ₀.2.2.2 θ₀.1 θ₀.2.1
    have hθ : θ₀ = elementaryCover (θ₀.1, t) θ₀.2.2.1 θ₀.2.2.2 := ht.symm
    have hshift (u : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
        θ₀ + elementaryCover u z b =
          elementaryCover ((θ₀.1, t) + u) (θ₀.2.2.1 + z) (θ₀.2.2.2 + b) := by
      calc θ₀ + elementaryCover u z b
          = elementaryCover (θ₀.1, t) θ₀.2.2.1 θ₀.2.2.2 + elementaryCover u z b :=
            congrArg (· + elementaryCover u z b) hθ
        _ = _ := by
          simp only [elementaryCover, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
            PiLp.add_apply, AddCircle.coe_add]
          rfl
    simp only [hf'v, hshift]
    exact (hsm _ _).comp (contDiff_const.add contDiff_id)
  have hG := (contDiff_comp_elementaryHom A hA hf' 0 0).comp
    (L.contDiff.prodMk (contDiff_const (c := (0 : EuclideanSpace ℝ (Fin 0)))))
  have heq : ∀ v : 𝕂, f₀ (e.equiv.symm (e.equiv q₀ * Multiplicative.ofAdd (θ v))) =
      f' (A (elementaryCover (m := d) (n := 0) (r := 0) (F := PUnit.{1})
        (L v, (0 : EuclideanSpace ℝ (Fin 0))) 0 0)) := by
    intro v
    rw [hAv]
    change _ = f' (θ (L.symm (L v)))
    rw [L.symm_apply_apply, hf'v, ofAdd_add, hθ₀]
  simp_rw [heq]
  exact hG

/-- A Bruhat smooth function on the units is smooth along every exponential curve. -/
private theorem weilTest_units_curve (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφs : Continuous φ.symm)
    {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEc : Continuous E) (f : w.Completionˣ → ℂ) (hf : IsBruhatSmooth f)
    (u₀ : w.Completionˣ) (n : ℕ) :
    ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun v : 𝕂 ↦
      Function.extend Units.val f (fun _ ↦ (0 : ℂ)) ((u₀ : w.Completion) * φ.symm (E v))) := by
  have hne (y : 𝕂) (hy : y ≠ 0) : φ.symm y ≠ 0 := (map_ne_zero φ.symm).mpr hy
  obtain ⟨k, hk, -, hdesc⟩ := hf n
  have hkC : IsCompact (k : Set w.Completionˣ) := (lcaDualAnnihilator_annihilator k hk.1) ▸
    isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains
    ((isCompact_singleton (x := u₀)).union hkC)
  obtain ⟨a, haH, hak⟩ : ∃ a : BruhatStructuralPair w.Completionˣ, a.val.1 = H.val ∧
      OrderDual.ofDual a.val.2 = k :=
    ⟨⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk, fun _ hx ↦ hH (Or.inr hx)⟩,
      rfl, rfl⟩
  obtain ⟨f₀, hf₀, hsm⟩ := hdesc a hak
  obtain ⟨e⟩ := a.elementary
  have hu₀ : u₀ ∈ a.val.1 := haH ▸ hH (Or.inl rfl)
  -- The exponential lands in the identity component, hence in the open subgroup.
  obtain ⟨Eu, hEuv⟩ : ∃ Eu : Multiplicative 𝕂 →* w.Completionˣ,
      ∀ v, (Eu v : w.Completion) = φ.symm (E v.toAdd) :=
    ⟨{ toFun := fun v ↦ Units.mk0 (φ.symm (E v.toAdd)) (hne _ (hE0 _))
       map_one' := Units.ext (by simp [hE00])
       map_mul' := fun a b ↦ Units.ext (by simp [hEadd]) }, fun _ ↦ rfl⟩
  have hEu : Continuous Eu := Units.isEmbedding_val₀.continuous_iff.mpr
    ((hφs.comp (hEc.comp continuous_toAdd)).congr fun v ↦ (hEuv v).symm)
  have hEH (v : Multiplicative 𝕂) : Eu v ∈ a.val.1 := by
    have hcl : IsClopen (a.val.1 : Set w.Completionˣ) :=
      ⟨a.val.1.isClosed_of_isOpen a.property.1, a.property.1⟩
    have : PreconnectedSpace (Multiplicative 𝕂) := inferInstanceAs (PreconnectedSpace 𝕂)
    exact (isPreconnected_range hEu).subset_isClopen hcl ⟨1, ⟨1, map_one Eu⟩, a.val.1.one_mem⟩
      ⟨v, rfl⟩
  obtain ⟨θ, hθc, hθv⟩ : ∃ θ : 𝕂 →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank
      e.finiteFactor, Continuous θ ∧ ∀ v, Multiplicative.ofAdd (θ v) =
        e.equiv (QuotientGroup.mk ⟨Eu (Multiplicative.ofAdd v), hEH _⟩) := by
    let θm : Multiplicative 𝕂 →* Multiplicative
        (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
      e.equiv.toMulEquiv.toMonoidHom.comp ((QuotientGroup.mk' _).comp (Eu.codRestrict _ hEH))
    have hθm : Continuous θm := e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
      (hEu.subtype_mk _))
    exact ⟨AddMonoidHom.toMultiplicative.symm θm, hθm, fun _ ↦ rfl⟩
  have hc := weilTest_elementary_curve L e f₀ (hsm e) θ hθc (QuotientGroup.mk ⟨u₀, hu₀⟩)
  have heq (v : 𝕂) : Function.extend Units.val f (fun _ ↦ (0 : ℂ))
      ((u₀ : w.Completion) * φ.symm (E v)) =
      f₀ (e.equiv.symm (e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) *
        Multiplicative.ofAdd (θ v))) := by
    have hmem : u₀ * Eu (Multiplicative.ofAdd v) ∈ a.val.1 := mul_mem hu₀ (hEH _)
    have hval : (u₀ : w.Completion) * φ.symm (E v) = ((u₀ * Eu (Multiplicative.ofAdd v) :
        w.Completionˣ) : w.Completion) := by
      rw [Units.val_mul, hEuv, toAdd_ofAdd]
    have hmul : e.equiv (QuotientGroup.mk ⟨u₀ * Eu (Multiplicative.ofAdd v), hmem⟩) =
        e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) * Multiplicative.ofAdd (θ v) :=
      calc e.equiv (QuotientGroup.mk ⟨u₀ * Eu (Multiplicative.ofAdd v), hmem⟩)
          = e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩ *
              QuotientGroup.mk ⟨Eu (Multiplicative.ofAdd v), hEH _⟩) := rfl
        _ = e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) *
              e.equiv (QuotientGroup.mk ⟨Eu (Multiplicative.ofAdd v), hEH _⟩) :=
            map_mul e.equiv _ _
        _ = _ := congrArg (e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) * ·) (hθv v).symm
    calc Function.extend Units.val f (fun _ ↦ (0 : ℂ)) ((u₀ : w.Completion) * φ.symm (E v))
        = Function.extend Units.val f (fun _ ↦ (0 : ℂ))
            ((u₀ * Eu (Multiplicative.ofAdd v) : w.Completionˣ) : w.Completion) :=
          congrArg _ hval
      _ = f (u₀ * Eu (Multiplicative.ofAdd v)) := Units.val_injective.extend_apply _ _ _
      _ = f₀ (QuotientGroup.mk ⟨_, hmem⟩) := (hf₀ ⟨_, hmem⟩).symm
      _ = _ := congrArg f₀ ((e.equiv.symm_apply_eq.mpr hmul.symm).symm)
  simp_rw [heq]
  exact hc

/-- A Bruhat smooth function on the units of an archimedean completion, extended by
zero, is smooth at every nonzero point in a real coordinate. -/
private theorem weilTest_source_contDiffAt (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφs : Continuous φ.symm)
    {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (f : w.Completionˣ → ℂ) (hf : IsBruhatSmooth f)
    (y₀ : 𝕂) (hy₀ : y₀ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ)) (φ.symm y)) y₀ := by
  rw [contDiffAt_infty]
  intro n
  obtain ⟨u₀, hu₀v⟩ : ∃ u : w.Completionˣ, (u : w.Completion) = φ.symm y₀ :=
    ⟨Units.mk0 _ ((map_ne_zero φ.symm).mpr hy₀), rfl⟩
  have hcurve := weilTest_units_curve w φ hφs L E hEadd hE0 hE00 hEs.continuous f hf u₀ n
  -- A local logarithm straightens the exponential curve near `y₀`.
  obtain ⟨Λ, hΛ, hright⟩ := weilTest_localLog E hE00 hEs hEd
  have hdiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : 𝕂 ↦ y * y₀⁻¹) := contDiff_id.mul contDiff_const
  have hlim : Tendsto (fun y : 𝕂 ↦ y * y₀⁻¹) (𝓝 y₀) (𝓝 1) := by
    have := hdiv.continuous.tendsto y₀
    rwa [mul_inv_cancel₀ hy₀] at this
  have hle : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hloc : ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun y ↦ Function.extend Units.val f
      (fun _ ↦ (0 : ℂ)) ((u₀ : w.Completion) * φ.symm (E (Λ (y * y₀⁻¹))))) y₀ := by
    have hΛ' : ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) Λ (y₀ * y₀⁻¹) := by
      rw [mul_inv_cancel₀ hy₀]
      exact hΛ.of_le hle
    exact hcurve.contDiffAt.comp y₀ (hΛ'.comp y₀ (hdiv.contDiffAt.of_le hle))
  refine hloc.congr_of_eventuallyEq ?_
  filter_upwards [hlim.eventually hright] with y hy
  rw [hu₀v, hy, ← map_mul, mul_left_comm, mul_inv_cancel₀ hy₀, mul_one]

/-- The weighted translate of a test on the units is smooth with compact support in a
real coordinate on the completion. -/
private theorem weilTest_target_contDiff (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφ : Continuous φ) (hφs : Continuous φ.symm)
    (hnorm : ∀ x, ‖φ x‖ = ‖x‖) {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (m : ℕ) (hW : ∀ z : 𝕂, z ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : 𝕂 ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z)
    (f : w.Completionˣ → ℂ) (hf : IsBruhatSmooth f) (hfc : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ))
        (1 + φ.symm y) / ((Real.sqrt (‖1 + φ.symm y‖ ^ m) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ))
        (1 + φ.symm y) / ((Real.sqrt (‖1 + φ.symm y‖ ^ m) : ℝ) : ℂ)) := by
  let h : 𝕂 → ℂ := fun y ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ)) (φ.symm y)
  let W : 𝕂 → ℂ := fun z ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)
  have hns (z : 𝕂) : ‖φ.symm z‖ = ‖z‖ := by rw [← hnorm, RingEquiv.apply_symm_apply]
  have hfun : (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ))
      (1 + φ.symm y) / ((Real.sqrt (‖1 + φ.symm y‖ ^ m) : ℝ) : ℂ)) =
      fun y ↦ h (1 + y) / W (1 + y) := by
    funext y
    have h1 : 1 + φ.symm y = φ.symm (1 + y) := by rw [map_add, map_one]
    simp only [h, W, h1, hns]
  rw [hfun]
  let Z : Set 𝕂 := φ '' (Units.val '' tsupport f)
  have hZ : IsCompact Z := (hfc.image Units.continuous_val).image hφ
  have hzero (z : 𝕂) (hz : z ∉ Z) : h z = 0 := by
    simp only [h]
    rw [weilTest_zeroExtend_apply]
    split_ifs with h0
    · rfl
    · refine image_eq_zero_of_notMem_tsupport fun hm ↦ hz ⟨_, ⟨_, hm, rfl⟩, ?_⟩
      simp
  have hWne (z : 𝕂) (hz : z ≠ 0) : W z ≠ 0 := by
    simp only [W, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (pow_pos (norm_pos_iff.mpr hz) m)).ne'
  have h0Z : (0 : 𝕂) ∉ Z := by
    rintro ⟨_, ⟨u, -, rfl⟩, hu⟩
    exact u.ne_zero ((map_eq_zero_iff φ φ.injective).mp hu)
  have htr : Continuous (fun y : 𝕂 ↦ 1 + y) := continuous_const.add continuous_id
  refine ⟨contDiff_iff_contDiffAt.mpr fun y ↦ ?_, ?_⟩
  · by_cases hy : 1 + y ∈ Z
    · have hy0 : 1 + y ≠ 0 := fun h ↦ h0Z (h ▸ hy)
      have hs := weilTest_source_contDiffAt w φ hφs L E hEadd hE0 hE00 hEs hEd f
        hf (1 + y) hy0
      have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : 𝕂 ↦ 1 + y) y := contDiffAt_const.add contDiffAt_id
      have hs' : ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ h (1 + y)) y := hs.comp y hc
      have hW' : ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ W (1 + y)) y := (hW (1 + y) hy0).comp y hc
      convert hs'.mul (hW'.inv (hWne _ hy0)) using 1
      funext y
      simp [div_eq_mul_inv]
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [(htr.tendsto y).eventually (hZ.isClosed.isOpen_compl.mem_nhds hy)]
        with y' hy'
      simp [hzero _ hy']
  · refine HasCompactSupport.intro (hZ.image (continuous_id.sub
      (continuous_const (y := (1 : 𝕂))))) fun y hy ↦ ?_
    have : 1 + y ∉ Z := fun h ↦ hy ⟨1 + y, h, by simp⟩
    simp [hzero _ this]


/-- The weighted translate is additive in the test. -/
private theorem weilTest_weighted_add (w : InfinitePlace F) (m : ℕ)
    (f f' : BruhatCompactSupport w.Completionˣ) (x : w.Completion) :
    Function.extend Units.val ((f + f').val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
        ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) =
      Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
          ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) +
        Function.extend Units.val (f'.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
          ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) := by
  simp only [weilTest_zeroExtend_apply]
  by_cases h0 : 1 + x = 0
  · simp only [h0, dite_true, zero_div, add_zero]
  · simp only [h0, dite_false]
    have hadd : (f + f').val (Units.mk0 (1 + x) h0) =
        f.val (Units.mk0 (1 + x) h0) + f'.val (Units.mk0 (1 + x) h0) := rfl
    exact (congrArg (· / ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ)) hadd).trans (add_div _ _ _)

/-- The weighted translate is homogeneous in the test. -/
private theorem weilTest_weighted_smul (w : InfinitePlace F) (m : ℕ) (c : ℂ)
    (f : BruhatCompactSupport w.Completionˣ) (x : w.Completion) :
    Function.extend Units.val ((c • f).val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
        ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) =
      c * (Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
          ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ)) := by
  simp only [weilTest_zeroExtend_apply]
  by_cases h0 : 1 + x = 0
  · simp only [h0, dite_true, zero_div, mul_zero]
  · simp only [h0, dite_false]
    have hsmul : (c • f).val (Units.mk0 (1 + x) h0) = c * f.val (Units.mk0 (1 + x) h0) := rfl
    exact (congrArg (· / ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ)) hsmul).trans (mul_div_assoc _ _ _)

/-- The weighted translate, read in real coordinates, defines a linear map into the
elementary Schwartz space of the real vector group. -/
private theorem weilTest_exists_linear (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφ : Continuous φ) (hφs : Continuous φ.symm)
    (hnorm : ∀ x, ‖φ x‖ = ‖x‖) {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (m : ℕ) (hW : ∀ z : 𝕂, z ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : 𝕂 ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z) :
    ∃ T : BruhatCompactSupport w.Completionˣ →ₗ[ℂ] ElementarySchwartz d 0 0 PUnit.{1},
      ∀ f g, T f g = Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ))
        (1 + φ.symm (L.symm g.1)) / ((Real.sqrt (‖1 + φ.symm (L.symm g.1)‖ ^ m) : ℝ) : ℂ) := by
  have hψ (f : BruhatCompactSupport w.Completionˣ) :=
    weilTest_target_contDiff w φ hφ hφs hnorm L E hEadd hE0 hE00 hEs hEd m hW
      f.val ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1) f.property.2
  have hψ' (f : BruhatCompactSupport w.Completionˣ) :=
    And.intro ((hψ f).1.comp L.symm.contDiff)
      ((hψ f).2.comp_isClosedEmbedding L.symm.toHomeomorph.isClosedEmbedding)
  let toY (f : BruhatCompactSupport w.Completionˣ) : ElementarySchwartz d 0 0 PUnit.{1} :=
    ⟨fun g ↦ (hψ' f).2.toSchwartzMap (hψ' f).1 g.1,
      (elementarySchwartzSubmodule_real_iff _).mpr ⟨(hψ' f).2.toSchwartzMap (hψ' f).1, rfl⟩⟩
  refine ⟨{ toFun := toY
            map_add' := fun f f' ↦ Subtype.ext (funext fun g ↦
              weilTest_weighted_add w m f f' (φ.symm (L.symm g.1)))
            map_smul' := fun c f ↦ Subtype.ext (funext fun g ↦
              weilTest_weighted_smul w m c f (φ.symm (L.symm g.1))) }, fun f g ↦ rfl⟩


/-- Elementary Schwartz functions with the same values are equal. -/
private theorem weilTest_elementarySchwartz_ext {d : ℕ}
    {s t : ElementarySchwartz d 0 0 PUnit.{1}} (h : ∀ g, s g = t g) : s = t :=
  Subtype.ext (funext h)

/-- Evaluation of elementary Schwartz functions on the real vector group is continuous. -/
private theorem weilTest_elementarySchwartz_eval {d : ℕ} (g : ElementaryLieGroup d 0 0 PUnit.{1}) :
    Continuous (fun t : ElementarySchwartz d 0 0 PUnit.{1} ↦ t g) := by
  obtain ⟨Lg, hLg⟩ := elementarySchwartz_eval_continuousLinear (d := d) (t := 0) (r := 0)
    (F := PUnit.{1}) g
  exact Lg.continuous.congr hLg

/-- On a fixed-support stage, the weighted translate is continuous by the closed graph
theorem. -/
private theorem weilTest_stage_continuous (w : InfinitePlace F) {d : ℕ} (m : ℕ)
    (ρ : ElementaryLieGroup d 0 0 PUnit.{1} → w.Completion)
    (T : BruhatCompactSupport w.Completionˣ →ₗ[ℂ] ElementarySchwartz d 0 0 PUnit.{1})
    (hT : ∀ f g, T f g = Function.extend Units.val (f.val : w.Completionˣ → ℂ)
      (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ))
    (a : BruhatStructuralPair w.Completionˣ) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts w.Completionˣ) :
    Continuous (T ∘ bruhatCompactSupportStageInclusion a e C) := by
  let G := w.Completionˣ
  let Y := ElementarySchwartz d 0 0 PUnit.{1}
  let X := bruhatCompactSupportStage a e C
  let i : X →ₗ[ℂ] bruhatCompactSupportSubmodule G := bruhatCompactSupportStageInclusion a e C
  let J : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  have hJ : Continuous J :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ (fun p ↦ p.2 a e)
  have hev (x : G) :
      Continuous (fun s : SchwartzBruhatStage e ↦ schwartzBruhatStageRealization a e s x) :=
    (continuous_schwartzBruhat_eval_forEndpoints x).comp hJ
  have hX : IsClosed (X : Set (SchwartzBruhatStage e)) := by
    simp only [X, bruhatCompactSupportStage, Submodule.coe_iInf]
    exact isClosed_iInter fun x ↦ isClosed_singleton.preimage (hev x.val)
  let T' : X →ₗ[ℂ] Y := T.comp i
  have hval (z : w.Completion) : Continuous (fun s : X ↦ Function.extend Units.val
      ((i s : BruhatCompactSupport G).val : G → ℂ) (fun _ ↦ (0 : ℂ)) z) := by
    simp only [weilTest_zeroExtend_apply]
    by_cases h0 : z = 0
    · simp only [h0, dite_true]
      exact continuous_const
    · simp only [h0, dite_false]
      exact (hev _).comp continuous_subtype_val
  have hgraph : IsClosed (T'.graph : Set (X × Y)) := by
    have heq : (T'.graph : Set (X × Y)) = ⋂ g : ElementaryLieGroup d 0 0 PUnit.{1},
        {p | p.2 g = Function.extend Units.val ((i p.1 : BruhatCompactSupport G).val : G → ℂ)
          (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ)} := by
      ext p
      refine ⟨fun h ↦ mem_iInter.mpr fun g ↦ ?_, fun h ↦ ?_⟩
      · have h' : p.2 = T' p.1 := (LinearMap.mem_graph_iff _ _).mp h
        exact (congrArg (fun t : Y ↦ t g) h').trans (hT _ g)
      · have hfun : ∀ g, p.2 g = T' p.1 g := fun g ↦ (mem_iInter.mp h g).trans (hT (i p.1) g).symm
        exact (LinearMap.mem_graph_iff _ _).mpr (weilTest_elementarySchwartz_ext hfun)
    have hc : IsClosed (⋂ g : ElementaryLieGroup d 0 0 PUnit.{1},
        {p : X × Y | p.2 g = Function.extend Units.val
          ((i p.1 : BruhatCompactSupport G).val : G → ℂ)
          (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ)}) := by
      refine isClosed_iInter fun g ↦ isClosed_eq ?_
        (((hval _).div_const _).comp continuous_fst)
      exact (weilTest_elementarySchwartz_eval g).comp continuous_snd
    exact (congrArg IsClosed heq).mpr hc
  have : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
  exact weilTest_continuous_of_isClosed_graph elementarySchwartz_isFrechet
    elementarySchwartz_isFrechet X hX T' hgraph

/-- A linear map from tests on the units to an elementary Schwartz space is continuous
when each value is the weighted translate at a point given by a fixed function. -/
private theorem weilTest_continuous_linear (w : InfinitePlace F) {d : ℕ} (m : ℕ)
    (ρ : ElementaryLieGroup d 0 0 PUnit.{1} → w.Completion)
    (T : BruhatCompactSupport w.Completionˣ →ₗ[ℂ] ElementarySchwartz d 0 0 PUnit.{1})
    (hT : ∀ f g, T f g = Function.extend Units.val (f.val : w.Completionˣ → ℂ)
      (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ)) :
    Continuous T := by
  let G := w.Completionˣ
  let Y := ElementarySchwartz d 0 0 PUnit.{1}
  have hstage := weilTest_stage_continuous w m ρ T hT
  refine (elementarySchwartz_withSeminorms (m := d) (n := 0) (r := 0)
    (F := PUnit.{1})).continuous_of_continuous_comp T fun j ↦ ?_
  let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : TopologicalSpace.Compacts G),
      Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
  exact (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
    (⟨(elementarySchwartzSeminorm j).comp T, fun a e C ↦
      (elementarySchwartz_withSeminorms.continuous_seminorm j).comp (hstage a e C)⟩ : P)


/-- In real coordinates on an archimedean completion, translation of the zero-extended
test after weighting is a continuous linear map to additive Schwartz–Bruhat tests. -/
private theorem weilTest_exists_map (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφ : Continuous φ) (hφs : Continuous φ.symm)
    (hnorm : ∀ x, ‖φ x‖ = ‖x‖) {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (m : ℕ) (hW : ∀ z : 𝕂, z ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : 𝕂 ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z) :
    ∃ A : BruhatCompactSupport w.Completionˣ →L[ℂ]
        SchwartzBruhat (Multiplicative w.Completion),
      ∀ (f : BruhatCompactSupport w.Completionˣ) (x : w.Completion),
        A f (Multiplicative.ofAdd x) = Function.extend Units.val (f.val : w.Completionˣ → ℂ)
          (fun _ ↦ (0 : ℂ)) (1 + x) / ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) := by
  have hex := weilTest_exists_linear w φ hφ hφs hnorm L E hEadd hE0 hE00 hEs hEd m hW
  refine hex.elim fun T hT ↦ ?_
  have hTc := weilTest_continuous_linear w m (fun g ↦ φ.symm (L.symm g.1)) T hT
  -- The completion is presented by its real coordinates.
  let c₀ : w.Completion ≃ₜ EuclideanSpace ℝ (Fin d) :=
    (Homeomorph.mk φ.toEquiv hφ hφs).trans L.toHomeomorph
  let c : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d)) :=
    ContinuousMulEquiv.mk' c₀ (fun x y ↦ by
      change L (φ (x.toAdd + y.toAdd)) = L (φ x.toAdd) + L (φ y.toAdd)
      rw [map_add, map_add])
  refine (weilTest_vectorPresentation c).elim fun a₁ h₁ ↦ h₁.elim fun hm₁ h₂ ↦
    h₂.elim fun w₁ hw₁ ↦ ?_
  let e₁ : ElementaryLCAPresentation a₁.quotient := ⟨d, 0, 0, PUnit, w₁⟩
  let J₁ : SchwartzBruhatStage e₁ →ₗ[ℂ] SchwartzBruhat (Multiplicative w.Completion) :=
    schwartzBruhatStageInclusion a₁ e₁
  have hJ₁ : Continuous J₁ :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ (fun p ↦ p.2 a₁ e₁)
  refine ⟨⟨J₁.comp T, hJ₁.comp hTc⟩, fun f x ↦ ?_⟩
  change (show SchwartzBruhat (Multiplicative w.Completion) from
    schwartzBruhatStageInclusion a₁ e₁ (T f)) (Multiplicative.ofAdd x) = _
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (hm₁ _)]
  refine (hT f _).trans ?_
  have hx : (w₁ (QuotientGroup.mk ⟨Multiplicative.ofAdd x, hm₁ _⟩)).toAdd.1 = L (φ x) :=
    hw₁ (Multiplicative.ofAdd x)
  change Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ))
      (1 + φ.symm (L.symm (w₁ (QuotientGroup.mk ⟨Multiplicative.ofAdd x, hm₁ _⟩)).toAdd.1)) /
        ((Real.sqrt (‖1 + φ.symm (L.symm
          (w₁ (QuotientGroup.mk ⟨Multiplicative.ofAdd x, hm₁ _⟩)).toAdd.1)‖ ^ m) : ℝ) : ℂ) = _
  rw [hx, L.symm_apply_apply, RingEquiv.symm_apply_apply]


/-- The inverse square-root weight is smooth away from zero. -/
private theorem weilTest_weight_contDiffAt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (m : ℕ) (z : V) (hz : z ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : V ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : V ↦ ‖z‖ ^ m) z := (contDiffAt_norm ℝ hz).pow m
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : V ↦ Real.sqrt (‖z‖ ^ m)) z :=
    (Real.contDiffAt_sqrt (pow_ne_zero m (norm_ne_zero_iff.mpr hz))).comp z h1
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z h2

/-- Paper: Definition B.4.4.1(2), p. 620. The weighted translate of a
multiplicative test at an infinite place is an additive test, continuously in the original test. -/
theorem exists_infiniteWeilTestMap (w : InfinitePlace F) :
    ∃ A : 𝒟(w.Completionˣ) →L[ℂ] 𝒮ₐ(w.Completion),
      ∀ (f : 𝒟(w.Completionˣ)) (x : w.Completion),
        addTest(A f) x = weightedTranslate((fun y : w.Completion ↦ ‖y‖ ^ w.mult), f.val) x := by
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      (LinearEquiv.ofFinrankEq ℝ (EuclideanSpace ℝ (Fin 1)) (by simp)).toContinuousLinearEquiv
    have hEd : HasFDerivAt Real.exp
        ((ContinuousLinearEquiv.refl ℝ ℝ : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) 0 :=
      (Real.hasDerivAt_exp 0).hasFDerivAt.congr_fderiv (by ext; simp)
    have hex := weilTest_exists_map w (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      e.continuous e.symm.continuous (fun x ↦ e.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)) x) L
      Real.exp Real.exp_add (fun a ↦ (Real.exp_pos a).ne') Real.exp_zero Real.contDiff_exp hEd
      w.mult (weilTest_weight_contDiffAt w.mult)
    exact hex.elim fun A hA ↦ ⟨A, fun f x ↦ hA f x⟩
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    let L : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (LinearEquiv.ofFinrankEq ℂ (EuclideanSpace ℝ (Fin 2)) (by simp)).toContinuousLinearEquiv
    have hEd : HasFDerivAt Complex.exp
        ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 0 :=
      (Complex.hasDerivAt_exp 0).complexToReal_fderiv.congr_fderiv (by ext; simp)
    have hex := weilTest_exists_map w (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)
      e.continuous e.symm.continuous (fun x ↦ e.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)) x) L
      Complex.exp Complex.exp_add Complex.exp_ne_zero Complex.exp_zero
      (Complex.contDiff_exp (𝕜 := ℝ)) hEd w.mult (weilTest_weight_contDiffAt w.mult)
    exact hex.elim fun A hA ↦ ⟨A, fun f x ↦ hA f x⟩

/-- Paper: Definition B.4.4.1(2), p. 620. The finite multiplicative
principal value applies Connes's functional to the weighted translated test.
Deviation: The multiplier parametrizes the additive character used by Lemma B.4.4.4. -/
def finiteConnesWeilPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    StrongDual ℂ (𝒟((v.adicCompletion F)ˣ)) :=
  (finiteConnesPrincipalValue v a).comp (exists_finiteWeilTestMap v).choose

/-- Paper: Definition B.4.4.1(2), p. 620. The infinite multiplicative
principal value applies Connes's functional to the weighted translated test. -/
def infiniteConnesWeilPrincipalValue (w : InfinitePlace F) :
    StrongDual ℂ (𝒟(w.Completionˣ)) :=
  (infiniteConnesPrincipalValue w).comp (exists_infiniteWeilTestMap w).choose

/-- Paper: Definition B.4.4.1(2), p. 620. At a real place a test vanishing
at one has its principal value given by the canonical ordinary integral. -/
theorem realConnesWeilPrincipalValue_of_apply_one_zero (w : InfinitePlace F)
    (_hw : w.IsReal) (f : 𝒟(w.Completionˣ)) (_hf : f.val 1 = 0) :
    let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
    (infiniteConnesWeilPrincipalValue w) f =
      (1 / 2 : ℂ) * ∫ u : w.Completionˣ,
        f.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ := by
  intro μ
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let r := InfinitePlace.Completion.ringEquivRealOfIsReal _hw
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hA := (exists_infiniteWeilTestMap w).choose_spec f
  have hmult : w.mult = 1 := by simp [InfinitePlace.mult, _hw]
  let Fz : w.Completion → ℂ := Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
  have hFu (u : w.Completionˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have hFz (y : w.Completion) (hy : y ∉ range (Units.val : w.Completionˣ → w.Completion)) :
      Fz y = 0 := by
    simp only [Fz, Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ hy ⟨u, hu⟩)]
  have h0 : addTest((exists_infiniteWeilTestMap w).choose f) 0 = 0 := by
    rw [hA]
    change Fz (1 + 0) / _ = 0
    rw [add_zero, ← Units.val_one, hFu, _hf, zero_div]
  change infiniteConnesPrincipalValue w ((exists_infiniteWeilTestMap w).choose f) = _
  rw [realConnesPrincipalValue_of_apply_zero w _hw _ h0]
  congr 1
  let G : w.Completion → ℂ := fun y ↦ Fz y / (Real.sqrt ‖y‖ : ℂ) / ((‖y - 1‖ : ℝ) : ℂ)
  -- Translation invariance moves the singularity from zero to one.
  have htr : ∫ x, addTest((exists_infiniteWeilTestMap w).choose f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w) =
      ∫ y, G y ∂ν∞(w) := by
    have hG : (fun x ↦ addTest((exists_infiniteWeilTestMap w).choose f) x / ((‖x‖ : ℝ) : ℂ)) =
        fun x ↦ G (1 + x) := by
      funext x
      rw [hA]
      change Fz (1 + x) / ((Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ)) / _ =
        Fz (1 + x) / (Real.sqrt ‖1 + x‖ : ℂ) / ((‖1 + x - 1‖ : ℝ) : ℂ)
      rw [hmult, pow_one, add_sub_cancel_left]
    rw [hG, infiniteLocalAdditiveTamagawaMeasure, dite_eq_left _hw]
    let m := e.symm.toHomeomorph.toMeasurableEquiv
    rw [show (r.symm : ℝ → w.Completion) = m from rfl, integral_map_equiv, integral_map_equiv]
    have hm (t : ℝ) : 1 + m t = m (1 + t) := by
      change 1 + r.symm t = r.symm (1 + t)
      rw [map_add, map_one]
    simp_rw [hm]
    exact integral_add_left_eq_self (fun t ↦ G (m t)) 1
  rw [htr]
  -- The multiplicative measure is the additive one with density `1 / ‖y‖` on units.
  let d : w.Completion → ENNReal := fun x ↦ (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  simp only [← hFu]
  change _ = ∫ u, _ ∂(ν∞(w).withDensity d).comap Units.val
  rw [← hval.integral_map (g := fun y ↦ Fz y * (Real.sqrt ‖y‖ : ℂ) / ((‖1 - y‖ : ℝ) : ℂ)),
    hval.map_comap, setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _
      hval.measurableSet_range,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
      (fun y hy ↦ by simp only [G, hFz y hy, zero_div])]
  · refine setIntegral_congr_fun hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr (hu ▸ u.ne_zero)
    simp only [G, d, hmult, pow_one]
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm, Complex.real_smul, norm_sub_rev]
    have hs : (Real.sqrt ‖y‖ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
    have hsq : (‖y‖ : ℂ) = (Real.sqrt ‖y‖ : ℂ) * (Real.sqrt ‖y‖ : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt hn.le).symm
    push_cast
    rw [hsq]
    field_simp
  · refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    simp only [d, hmult, pow_one]
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])

local notation "finiteWeilIntegrand(" v ", " f ")" =>
  (fun u : (HeightOneSpectrum.adicCompletion F v)ˣ ↦
    f u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ))

/-- Paper: Remark B.4.4.2, p. 620. For the finite local norm the canonical
multiplicative Haar measure gives an integer-unit shell mass equal to the log prime norm. -/
theorem finiteCanonicalHaar_eq_smul_tamagawa (v : Primes(F)) :
    letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    letI : SecondCountableTopology (v.adicCompletion F)ˣ :=
      (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).secondCountableTopology
    letI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
    let m : (v.adicCompletion F)ˣ →ₜ* ℝ≥0ˣ :=
      ⟨Units.map nnNormHom.toMonoidHom, continuous_finiteLocalModule v⟩
    ∃ hm : IsModulation m, canonicalModulatedHaar m hm =
      ENNReal.ofReal (Real.log q(v) / V𝔭(v)) • μ𝔭(v) := by
  classical
  intro m
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : SecondCountableTopology Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let : BorelSpace Kˣ := ⟨rfl⟩
  let q : ℝ≥0ˣ := Units.mk0 (v.asIdeal.absNorm : ℝ≥0)
    (by exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne')
  have hq : 1 < (q.val : ℝ) := by
    change 1 < (v.asIdeal.absNorm : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 (π : K) hπ.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  have hgen : m p⁻¹ = q := by
    apply Units.ext
    apply NNReal.eq
    change ‖(p⁻¹).val‖ = q(v)
    rw [Units.val_inv_eq_inv_val, norm_inv, hp, inv_inv]
  have hm : IsModulation m := by
    constructor
    · change IsProperMap (Units.map nnNormHom.toMonoidHom : Kˣ →* ℝ≥0ˣ)
      have h := isProperMap_units_nnNorm_pow (K := K) 1 one_ne_zero
      simpa only [MonoidHom.pow_apply, pow_one] using h
    · refine ⟨p⁻¹, fun he ↦ hq.ne' ?_⟩
      exact congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (hgen.symm.trans he)
  -- The inverse uniformizer generates the range of the normalized absolute value.
  have hrange : m.toMonoidHom.range = Subgroup.zpowers q := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨WithZero.log (Valued.v u.val), ?_⟩
      apply Units.ext
      apply NNReal.eq
      change (((q ^ _).val : ℝ≥0) : ℝ) = ‖u.val‖
      rw [Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, FinitePlace.norm_def,
        WithZeroMulInt.toNNReal_neg_apply _ (Valued.v.ne_zero_iff.mpr u.ne_zero)]
      simp [q]
    · exact Subgroup.zpowers_le.mpr ⟨p⁻¹, hgen⟩
  have hker : (m.toMonoidHom.ker : Set Kˣ) = (O(v)).units := by
    ext u
    change m u = 1 ↔ u ∈ (O(v)).units
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      ← Valued.toNormedField.norm_eq_one_iff, ← Units.val_inj, ← NNReal.coe_inj]
    rfl
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  refine ⟨hm, (existsUnique_canonicalModulatedHaar m hm).unique
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists) ?_⟩
  have hqval : (q.val : ℝ) = q(v) := by simp [q]
  simpa only [hker, hqval] using haar_logGrowth_of_cyclic_range m hm hq hrange μ𝔭(v)

/-- Paper: Remark B.4.4.2, p. 620. For the infinite local module, dividing
Tamagawa measure by two at a real place or by two pi at a complex place gives canonical Haar measure. -/
theorem infiniteCanonicalHaar_eq_smul_tamagawa (w : InfinitePlace F) :
    letI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    letI : SecondCountableTopology w.Completionˣ :=
      (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
    letI : BorelSpace w.Completion := ⟨rfl⟩
    letI : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let m : w.Completionˣ →ₜ* ℝ≥0ˣ :=
      ⟨(Units.map nnNormHom.toMonoidHom) ^ w.mult, continuous_infiniteLocalModule w⟩
    ∃ hm : IsModulation m, canonicalModulatedHaar m hm =
      ENNReal.ofReal ((if w.IsReal then 2 else 2 * Real.pi)⁻¹) •
        infiniteLocalMultiplicativeTamagawaMeasure F w := by
  intro m
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
  let : μ.IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion :=
    LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    rw [← hi.norm_map_of_map_zero (map_zero _) (2 : w.Completion), map_ofNat]
    norm_num
  have hmval (g : w.Completionˣ) : ((m g).val : ℝ) = ‖g.val‖ ^ w.mult := by
    change (((Units.map nnNormHom.toMonoidHom g) ^ w.mult : ℝ≥0ˣ).val : ℝ) = _
    rw [Units.val_pow_eq_pow_val, NNReal.coe_pow]
    rfl
  have hm : IsModulation m := by
    refine ⟨isProperMap_units_nnNorm_pow w.mult w.mult_ne_zero, ⟨Units.mk0 2 (by rw [← norm_ne_zero_iff, h2]; norm_num), ?_⟩⟩
    intro h
    have h2' := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    simp only [hmval, Units.val_one, NNReal.coe_one] at h2'
    rw [Units.val_mk0, h2] at h2'
    exact absurd ((pow_eq_one_iff_of_nonneg zero_le_two w.mult_ne_zero).mp h2') (by norm_num)
  let c : ℝ := if w.IsReal then 2 else 2 * Real.pi
  have hc : 0 < c := by unfold c; split_ifs <;> positivity
  refine ⟨hm, (existsUnique_canonicalModulatedHaar m hm).unique
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists)
    ⟨Measure.IsHaarMeasure.smul _ (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)).ne'
      ENNReal.ofReal_ne_top, ?_⟩⟩
  refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with Λ hΛ
  let S : Set w.Completionˣ := {g | ((m g).val : ℝ) ∈ Icc Λ⁻¹ Λ}
  have hS : MeasurableSet S := by
    have : Continuous fun g : w.Completionˣ ↦ ((m g).val : ℝ) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    exact this.measurable measurableSet_Icc
  let φ : ℝ → ℂ := fun r ↦ (((Icc Λ⁻¹ Λ).indicator 1 (r ^ w.mult) : ℝ) : ℂ)
  have h1 : ((μ.real S : ℝ) : ℂ) = ∫ u, φ ‖u.val‖ ∂μ := by
    rw [← integral_indicator_one hS, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
    simp only [φ, S, indicator, mem_ofPred_eq, hmval, Pi.one_apply]
  have hrad {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
      (hφ : ∀ r, 0 < r → φ r = (Icc a b).indicator (fun _ ↦ (1 : ℂ)) r) :
      ∫ r in Ioi (0 : ℝ), r⁻¹ • φ r = (Real.log (b / a) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := (Icc a b).indicator
      (fun r : ℝ ↦ ((r⁻¹ : ℝ) : ℂ))) (fun r hr ↦ by
        rw [hφ r hr]
        by_cases h : r ∈ Icc a b <;> simp [h, indicator, Complex.real_smul])]
    rw [setIntegral_indicator measurableSet_Icc,
      inter_eq_right.mpr (fun r (hr : r ∈ Icc a b) ↦ ha.trans_le hr.1),
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_ofReal,
      integral_inv_of_pos ha (ha.trans_le hab)]
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  have hval : μ.real S = 2 * c * Real.log Λ := by
    apply Complex.ofReal_injective
    rw [h1, localUnit_radial F w φ]
    by_cases hw : w.IsReal
    · rw [hrad (inv_pos.mpr hΛpos) (inv_le_one_of_one_le₀ hΛ |>.trans hΛ) (fun r _ ↦ by
        simp only [φ, hw.mult_eq_one, pow_one, indicator]
        split_ifs <;> simp)]
      simp only [c, hw, ↓reduceIte, div_inv_eq_mul, Real.log_mul hΛpos.ne' hΛpos.ne',
        Complex.real_smul]
      push_cast; ring
    · have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hs := Real.sqrt_pos.mpr hΛpos
      rw [hrad (inv_pos.mpr hs) ((inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hΛ)).trans
        (Real.one_le_sqrt.mpr hΛ)) (fun r hr ↦ by
          have : r ^ 2 ∈ Icc Λ⁻¹ Λ ↔ r ∈ Icc (√Λ)⁻¹ √Λ := by
            rw [mem_Icc, mem_Icc, ← Real.sqrt_inv, Real.sqrt_le_iff, Real.le_sqrt' hr]
            simp [hr.le]
          simp only [φ, hw'.mult_eq_two]
          by_cases h : r ∈ Icc (√Λ)⁻¹ √Λ <;>
            simp only [indicator, this, h, ↓reduceIte, Pi.one_apply, Complex.ofReal_one,
              Complex.ofReal_zero])]
      simp only [c, hw, ↓reduceIte, div_inv_eq_mul, Real.mul_self_sqrt hΛpos.le,
        Complex.real_smul]
      push_cast; ring
  rw [eq_comm]
  change ((ENNReal.ofReal c⁻¹ • μ) S).toReal - 2 * Real.log Λ = 0
  rw [smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_pos.mpr hc).le, ← measureReal_def, hval]
  field_simp
  ring

/-- Paper: Lemma B.4.4.3, p. 620. If the locally constant test vanishes
at one, the finite principal value is the ordinary integrable local term. -/
theorem finiteConnesWeilPrincipalValue_of_apply_one_zero (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) (_hf : f.val 1 = 0) :
    Integrable (finiteWeilIntegrand(v, f.val)) μ𝔭(v) ∧
      finiteConnesWeilPrincipalValue v 1 f =
        ∫ u, finiteWeilIntegrand(v, f.val) u ∂μ𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let c : ENNReal := (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ENNReal)
  let d : K → ENNReal := fun x ↦ (↑‖x‖₊ : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂(ν𝔭(v).restrict (range (Units.val : Kˣ → K))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  have hdy (y : K) : (d y).toReal = ‖y‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hc0 : c ≠ 0 :=
    (ENNReal.div_pos (zero_lt_one.trans hq).ne' (ENNReal.sub_ne_top (ENNReal.natCast_ne_top _))).ne'
  have hct : c ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (tsub_pos_of_lt hq).ne').ne
  have := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hsupp (g : K → ℂ) : support (fun y ↦ ‖y‖⁻¹ • g y) ⊆ range (Units.val : Kˣ → K) := by
    intro y hy
    have : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y this, rfl⟩
  -- Multiplicative integration is additive integration against `c / ‖y‖`.
  have key (g : K → ℂ) :
      (Integrable (fun u : Kˣ ↦ g u.val) μ𝔭(v) ↔ Integrable (fun y ↦ ‖y‖⁻¹ • g y) ν𝔭(v)) ∧
        ∫ u : Kˣ, g u.val ∂μ𝔭(v) = c.toReal • ∫ y, ‖y‖⁻¹ • g y ∂ν𝔭(v) := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity]
    refine ⟨?_, ?_⟩
    · rw [integrable_smul_measure hc0 hct, show (fun u : Kˣ ↦ g u.val) = g ∘ Units.val from rfl,
        ← hval.integrable_map_iff (g := g), hval.map_comap,
        restrict_withDensity hval.measurableSet_range,
        integrable_withDensity_iff_integrable_smul' hd hdlt,
        ← integrableOn_iff_integrable_of_support_subset (hsupp g)]
      simp_rw [hdy]
      rfl
    · rw [integral_smul_measure]
      congr 1
      rw [← hval.integral_map (g := g), hval.map_comap,
        setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _ hval.measurableSet_range,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
          (fun y hy ↦ Function.notMem_support.mp (fun h ↦ hy (hsupp g h)))]
      · simp_rw [hdy]
      · exact hdlt
  let A := (exists_finiteWeilTestMap v).choose
  have hA := (exists_finiteWeilTestMap v).choose_spec f
  let Fz : K → ℂ := Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
  have hFu (u : Kˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have h0 : addTest(A f) 0 = 0 := by
    rw [hA]
    change Fz (1 + 0) / _ = 0
    rw [add_zero, ← Units.val_one, hFu, _hf, zero_div]
  let Q : K → ℂ := fun y ↦ Fz y * (Real.sqrt ‖y‖ : ℂ) / ((‖1 - y‖ : ℝ) : ℂ)
  have hQ (u : Kˣ) : Q u.val = finiteWeilIntegrand(v, f.val) u := by
    change Fz u.val * _ / _ = _
    rw [hFu]
  let H : K → ℂ := fun y ↦ ‖y‖⁻¹ • Q y
  -- After the translation `y = 1 + x`, the two weighted integrands agree.
  have hPH (x : K) : ‖x‖⁻¹ • addTest(A f) x = H (1 + x) := by
    rw [hA]
    change ‖x‖⁻¹ • (Fz (1 + x) / (Real.sqrt ‖1 + x‖ : ℂ)) =
      ‖1 + x‖⁻¹ • (Fz (1 + x) * (Real.sqrt ‖1 + x‖ : ℂ) / ((‖1 - (1 + x)‖ : ℝ) : ℂ))
    rw [sub_add_cancel_left, norm_neg, Complex.real_smul, Complex.real_smul]
    rcases (norm_nonneg (1 + x)).eq_or_lt with hn | hn
    · simp [← hn]
    have hs : (Real.sqrt ‖1 + x‖ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
    have hsq : (‖1 + x‖ : ℂ) = (Real.sqrt ‖1 + x‖ : ℂ) * (Real.sqrt ‖1 + x‖ : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt hn.le).symm
    push_cast
    rw [hsq]
    field_simp
  have hPI := (finiteLogFourier_eq_neg_haar v (A f) h0).2.1
  have hPH' : (fun x ↦ ‖x‖⁻¹ • addTest(A f) x) = fun x ↦ H (1 + x) := funext hPH
  have hHI : Integrable H ν𝔭(v) := by
    have h1 := (key addTest(A f)).1.mp hPI
    rw [hPH'] at h1
    refine (h1.comp_add_left (-1)).congr (ae_of_all _ fun x ↦ ?_)
    exact congrArg H (add_neg_cancel_left 1 x)
  have e1 : finiteConnesWeilPrincipalValue v 1 f = ∫ u : Kˣ, addTest(A f) u.val ∂μ𝔭(v) :=
    finiteConnesPrincipalValue_one_of_apply_zero v (A f) h0
  have e2 : ∫ u : Kˣ, addTest(A f) u.val ∂μ𝔭(v) = ∫ u : Kˣ, Q u.val ∂μ𝔭(v) :=
    calc ∫ u : Kˣ, addTest(A f) u.val ∂μ𝔭(v)
        = c.toReal • ∫ y, ‖y‖⁻¹ • addTest(A f) y ∂ν𝔭(v) := (key addTest(A f)).2
      _ = c.toReal • ∫ y, H (1 + y) ∂ν𝔭(v) :=
        congrArg (c.toReal • ·) (congrArg (fun φ ↦ ∫ y, φ y ∂ν𝔭(v)) hPH')
      _ = c.toReal • ∫ y, H y ∂ν𝔭(v) := congrArg _ (integral_add_left_eq_self H 1)
      _ = ∫ u : Kˣ, Q u.val ∂μ𝔭(v) := ((key Q).2).symm
  have e3 : ∫ u : Kˣ, Q u.val ∂μ𝔭(v) = ∫ u, finiteWeilIntegrand(v, f.val) u ∂μ𝔭(v) :=
    integral_congr_ae (ae_of_all _ hQ)
  exact ⟨((key Q).1.mpr hHI).congr (ae_of_all _ hQ), e1.trans (e2.trans e3)⟩

-- TODO(paper-gap): Equation (B.4.4.6) gives the wrong sign and scale for
-- the restriction of T, and Fourier transformation requires an additive test space.

/-- Connes's principal value for the standard character is minus the unit mass times the
logarithmic Fourier pairing. -/
private theorem existsUnique_finiteWeilFourierDistribution_principalValue (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) :
    finiteConnesPrincipalValue v 1 f = -(V𝔭(v) : ℂ) *
      ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v) := by
  have hT := ((exists_finiteConnesPrincipalValue v 1).choose_spec f).2
  change finiteConnesPrincipalValue v 1 f = _ at hT
  simp only [Units.val_one, norm_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
    one_mul] at hT
  exact hT

/-- Translation by one of an additive test is an additive test. -/
private theorem existsUnique_finiteWeilFourierDistribution_translate (v : Primes(F))
    (g : 𝒮ₐ(v.adicCompletion F)) :
    ∃ g' : 𝒮ₐ(v.adicCompletion F), ∀ x, addTest(g') x = addTest(g) (1 + x) := by
  obtain ⟨hl, hc⟩ := finiteLogFourier_eq_neg_haar_testFacts v g
  obtain ⟨g', hg'⟩ := (mem_finitePlaceSchwartz_iff F v (fun x ↦ addTest(g) (1 + x))).mpr
    ⟨hl.comp_continuous (continuous_const.add continuous_id),
      hc.comp_homeomorph (Homeomorph.addLeft (1 : v.adicCompletion F))⟩
  exact ⟨g', hg'⟩

/-- Fourier inversion on a finite completion: the double transform is reflection. -/
private theorem existsUnique_finiteWeilFourierDistribution_fourier_fourier (v : Primes(F))
    (s : 𝒮ₐ(v.adicCompletion F)) (y : v.adicCompletion F) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v) (tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(s)) y =
      addTest(s) (-y) := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, he, hP⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let μ : Measure G := ν𝔭(v)
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hinv := schwartzBruhat_fourier_inversion μ _ hP s (Multiplicative.ofAdd (-y))
  let m := e.toHomeomorph.toMeasurableEquiv
  rw [show (⇑e : G → PontryaginDual G) = m from rfl, integral_map_equiv] at hinv
  obtain ⟨ψ', hψ', -⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  have hneg (a : K) : (ψ𝔭(v) (-a) : ℂ) = star (ψ𝔭(v) a : ℂ) := by
    rw [← hψ' a, ← hψ' (-a), ofAdd_neg, map_inv, Circle.coe_inv_eq_conj, Complex.star_def]
  change addTest(s) (-y) = _ at hinv
  refine Eq.trans ?_ hinv.symm
  change (∫ x, tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(s) x * star (ψ𝔭(v) (x * y) : ℂ) ∂ν𝔭(v)) = _
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have h1 : tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(s) x = lcaFourier μ s (m x) :=
    tamagawaFourier_eq_lcaFourier _ _ _ x _ fun z ↦ (he x z).trans (congrArg _ (mul_comm x z))
  have h2 : ((m x) (Multiplicative.ofAdd (-y)) : ℂ) = star (ψ𝔭(v) (x * y) : ℂ) := by
    change ((e (Multiplicative.ofAdd x)) (Multiplicative.ofAdd (-y)) : ℂ) = _
    rw [he, mul_neg, hneg]
  beta_reduce
  rw [h1, h2]

/-- The Fourier transform of the translate by one is the character times the transform. -/
private theorem existsUnique_finiteWeilFourierDistribution_fourier_translate (v : Primes(F))
    (g g' : 𝒮ₐ(v.adicCompletion F)) (hg' : ∀ x, addTest(g') x = addTest(g) (1 + x))
    (y : v.adicCompletion F) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g') y =
      (ψ𝔭(v) y : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  obtain ⟨ψ', hψ', -⟩ := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  have hadd (a b : K) : (ψ𝔭(v) (a + b) : ℂ) = ψ𝔭(v) a * ψ𝔭(v) b := by
    rw [← hψ' a, ← hψ' b, ← hψ' (a + b), ofAdd_add, map_mul, Circle.coe_mul]
  have hunit : (ψ𝔭(v) y : ℂ) * star (ψ𝔭(v) y : ℂ) = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel,
      Circle.coe_one]
  let H : K → ℂ := fun z ↦ (ψ𝔭(v) y : ℂ) * (addTest(g) z * star (ψ𝔭(v) (z * y) : ℂ))
  have hH : (fun x ↦ addTest(g') x * star (ψ𝔭(v) (x * y) : ℂ)) = fun x ↦ H (1 + x) := by
    funext x
    simp only [H, hg', add_mul, one_mul, hadd, star_mul']
    linear_combination (-(addTest(g) (1 + x) * star (ψ𝔭(v) (x * y) : ℂ))) * hunit
  unfold tamagawaFourier
  rw [hH, integral_add_left_eq_self H 1, ← integral_const_mul]

/-- Multiplicative integration is additive integration against `q/(q-1)` over the norm. -/
private theorem existsUnique_finiteWeilFourierDistribution_units_integral (v : Primes(F))
    (g : v.adicCompletion F → ℂ) :
    ∫ u : (v.adicCompletion F)ˣ, g u.val ∂μ𝔭(v) =
      ((q(v) / (q(v) - 1) : ℝ) : ℂ) * ∫ y, g y / ((‖y‖ : ℝ) : ℂ) ∂ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let c : ENNReal := (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ENNReal)
  let d : K → ENNReal := fun x ↦ (↑‖x‖₊ : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂(ν𝔭(v).restrict (range (Units.val : Kˣ → K))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  have hdy (y : K) : (d y).toReal = ‖y‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hsupp : support (fun y ↦ ‖y‖⁻¹ • g y) ⊆ range (Units.val : Kˣ → K) := by
    intro y hy
    have : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y this, rfl⟩
  have hc : (c.toReal : ℂ) = ((q(v) / (q(v) - 1) : ℝ) : ℂ) := by
    simp only [c]
    rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hq.le (ENNReal.natCast_ne_top _),
      ENNReal.toReal_natCast, ENNReal.toReal_one]
  rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, integral_smul_measure,
    ← hval.integral_map (g := g), hval.map_comap,
    setIntegral_withDensity_eq_setIntegral_toReal_smul hd hdlt _ hval.measurableSet_range]
  simp_rw [hdy]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy ↦ Function.notMem_support.mp (fun h ↦ hy (hsupp h))), ← hc, Complex.real_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show ‖y‖⁻¹ • g y = g y / ((‖y‖ : ℝ) : ℂ)
  rw [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

/-- The standard character is trivial on the integers. -/
private theorem existsUnique_finiteWeilFourierDistribution_char_eq_one (v : Primes(F))
    (x : v.adicCompletion F) (hx : ‖x‖ ≤ 1) : ψ𝔭(v) x = 1 := by
  have h := Set.ext_iff.mp (finiteLocalStandardCharacter_annihilator_integers F v) 1
  have hq : (1 : ℝ) ≤ (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have h1 := h.mpr (by simpa using one_le_pow₀ (M₀ := ℝ) hq)
  have hxO : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    exact hx
  simpa using h1 x hxO

/-- The Fourier transform of the unit-sphere indicator does not vanish at one. -/
private theorem existsUnique_finiteWeilFourierDistribution_sphere_fourier_one (v : Primes(F)) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v)
      (indicator {x : v.adicCompletion F | ‖x‖ = 1} (fun _ ↦ (1 : ℂ))) 1 ≠ 0 := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let S := {x : K | ‖x‖ = 1}
  have hS : S = Metric.sphere (0 : K) 1 := Set.ext fun x ↦ mem_sphere_zero_iff_norm.symm
  have hSo : IsOpen S := hS ▸ IsUltrametricDist.isOpen_sphere (0 : K) one_ne_zero
  have hSc : IsCompact S := hS ▸ isCompact_sphere (0 : K) 1
  have hind : (fun x ↦ S.indicator (fun _ ↦ (1 : ℂ)) x * star (ψ𝔭(v) (x * 1) : ℂ)) =
      S.indicator (fun _ ↦ (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, mul_one,
        existsUnique_finiteWeilFourierDistribution_char_eq_one v x (show ‖x‖ = 1 from hx).le,
        Circle.coe_one, star_one, one_mul]
    · rw [indicator_of_notMem hx, zero_mul]
  change (∫ x, S.indicator (fun _ ↦ (1 : ℂ)) x * star (ψ𝔭(v) (x * 1) : ℂ) ∂ν𝔭(v)) ≠ 0
  rw [hind, integral_indicator hSo.measurableSet, setIntegral_const, Complex.real_smul, mul_one,
    measureReal_def]
  exact_mod_cast (ENNReal.toReal_pos (hSo.measure_pos _ ⟨1, by simp [S]⟩).ne'
    hSc.measure_lt_top.ne).ne'

/-- Paper: Lemma B.4.4.3, pp. 620–621. The translated Fourier
distribution is normalized on the Fourier transform of the integer-unit indicator.
It evaluates the finite multiplicative principal value on inverse square-root weighted tests.
Deviation: The distribution is on the full additive test space. Its restriction away
from one is minus the specified density divided by the mass of the integer units.
The evaluation identity extends to all multiplicative tests by the weighted translation. -/
theorem existsUnique_finiteWeilFourierDistribution (v : Primes(F)) :
    let normalized := fun T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)) ↦
      (∀ f : 𝒮ₐ(v.adicCompletion F), addTest(f) 1 = 0 →
        T f = -((q(v) / (q(v) - 1) / V𝔭(v) : ℝ) : ℂ) *
          ∫ x, addTest(f) x / ((‖1 - x‖ : ℝ) : ℂ) ∂ν𝔭(v)) ∧
      (∃ g : 𝒮ₐ(v.adicCompletion F),
        addTest(g) = tamagawaFourier ν𝔭(v) ψ𝔭(v)
          (indicator {x : v.adicCompletion F | ‖x‖ = 1} (fun _ ↦ 1)) ∧ T g = 0)
    ∃ T, normalized T ∧ (∀ S, normalized S → S = T) ∧
      (∀ f : 𝒟((v.adicCompletion F)ˣ), ∃ g : 𝒮ₐ(v.adicCompletion F),
        (∀ x, addTest(g) x = zeroExtend(f.val) x / (Real.sqrt ‖x‖ : ℂ)) ∧
        finiteConnesWeilPrincipalValue v 1 f = -(V𝔭(v) : ℂ) * T g) := by
  intro normalized
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hV : V𝔭(v) ≠ 0 := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
  have hVc : (V𝔭(v) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  let C := finiteConnesPrincipalValue v 1
  -- Translation by one on the additive tests.
  let τ : 𝒮ₐ(K) → 𝒮ₐ(K) := fun g ↦
    (existsUnique_finiteWeilFourierDistribution_translate v g).choose
  have hτ (g : 𝒮ₐ(K)) (x : K) : addTest(τ g) x = addTest(g) (1 + x) :=
    (existsUnique_finiteWeilFourierDistribution_translate v g).choose_spec x
  have hτadd (g g' : 𝒮ₐ(K)) : τ (g + g') = τ g + τ g' := by
    refine SchwartzBruhat.ext fun x ↦ ?_
    change addTest(τ (g + g')) x.toAdd = addTest(τ g) x.toAdd + addTest(τ g') x.toAdd
    rw [hτ (g + g'), hτ g, hτ g']
    rfl
  have hτsmul (c : ℂ) (g : 𝒮ₐ(K)) : τ (c • g) = c • τ g := by
    refine SchwartzBruhat.ext fun x ↦ ?_
    change addTest(τ (c • g)) x.toAdd = c * addTest(τ g) x.toAdd
    rw [hτ (c • g), hτ g]
    rfl
  -- The distribution is minus the inverse unit mass times Connes's value on the translate.
  let L : 𝒮ₐ(K) → ℂ := fun g ↦ -(V𝔭(v) : ℂ)⁻¹ * C (τ g)
  have hLadd (g g' : 𝒮ₐ(K)) : L (g + g') = L g + L g' := by
    simp only [L, hτadd, map_add]
    ring
  have hLsmul (c : ℂ) (g : 𝒮ₐ(K)) : L (c • g) = c * L g := by
    simp only [L, hτsmul, map_smul, smul_eq_mul]
    ring
  obtain ⟨T, hT⟩ := exists_finiteConnesPrincipalValue_ofLinear v L hLadd hLsmul
    (fun g z ↦ z = L g) (fun _ ↦ rfl)
  -- (a) Away from one the distribution is the weighted integral.
  have hA (g : 𝒮ₐ(K)) (hg : addTest(g) 1 = 0) :
      T g = -((q(v) / (q(v) - 1) / V𝔭(v) : ℝ) : ℂ) *
        ∫ x, addTest(g) x / ((‖1 - x‖ : ℝ) : ℂ) ∂ν𝔭(v) := by
    have h0 : addTest(τ g) 0 = 0 := by rw [hτ, add_zero, hg]
    rw [hT, show L g = -(V𝔭(v) : ℂ)⁻¹ * C (τ g) from rfl,
      show C (τ g) = _ from finiteConnesPrincipalValue_one_of_apply_zero v (τ g) h0]
    simp_rw [hτ]
    rw [existsUnique_finiteWeilFourierDistribution_units_integral v (fun y ↦ addTest(g) (1 + y))]
    have htr : ∫ y, addTest(g) (1 + y) / ((‖y‖ : ℝ) : ℂ) ∂ν𝔭(v) =
        ∫ x, addTest(g) x / ((‖1 - x‖ : ℝ) : ℂ) ∂ν𝔭(v) := by
      rw [← integral_add_left_eq_self (μ := ν𝔭(v))
        (fun x ↦ addTest(g) x / ((‖1 - x‖ : ℝ) : ℂ)) 1]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      show addTest(g) (1 + y) / ((‖y‖ : ℝ) : ℂ) = addTest(g) (1 + y) / ((‖1 - (1 + y)‖ : ℝ) : ℂ)
      rw [sub_add_cancel_left, norm_neg]
    rw [htr]
    push_cast
    ring
  -- (b) The Fourier transform of the unit-sphere indicator is annihilated.
  have hS : {x : K | ‖x‖ = 1} = Metric.sphere (0 : K) 1 :=
    Set.ext fun x ↦ mem_sphere_zero_iff_norm.symm
  obtain ⟨s, hs⟩ := finiteLogFourier_eq_neg_haar_clopenTest v {x : K | ‖x‖ = 1}
    (hS ▸ IsUltrametricDist.isClopen_sphere (0 : K) one_ne_zero) (hS ▸ isCompact_sphere (0 : K) 1)
  obtain ⟨h, hh⟩ := finiteLocal_exists_fourier_test v s
  have hsf : addTest(s) = indicator {x : K | ‖x‖ = 1} (fun _ ↦ (1 : ℂ)) := funext hs
  have hhs : addTest(h) = tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(s) := funext hh
  have hhf : addTest(h) = tamagawaFourier ν𝔭(v) ψ𝔭(v)
      (indicator {x : K | ‖x‖ = 1} (fun _ ↦ (1 : ℂ))) := by rw [hhs, hsf]
  have hTh : T h = 0 := by
    rw [hT, show L h = -(V𝔭(v) : ℂ)⁻¹ * C (τ h) from rfl,
      show C (τ h) = _ from existsUnique_finiteWeilFourierDistribution_principalValue v (τ h)]
    have hzero (y : K) : ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(τ h) y = 0 := by
      rw [existsUnique_finiteWeilFourierDistribution_fourier_translate v h (τ h) (hτ h) y, hhs,
        existsUnique_finiteWeilFourierDistribution_fourier_fourier v s y]
      beta_reduce
      rw [hs]
      by_cases hy : ‖y‖ = 1
      · simp [hy]
      · rw [indicator_of_notMem (by show ¬ (‖-y‖ = 1); rwa [norm_neg]), mul_zero, mul_zero]
    simp only [hzero, integral_zero, mul_zero]
  -- (c) The weighted zero extension translates to Weil's test map.
  have hC (f : 𝒟(Kˣ)) : ∃ g : 𝒮ₐ(K),
      (∀ x, addTest(g) x = zeroExtend(f.val) x / (Real.sqrt ‖x‖ : ℂ)) ∧
        finiteConnesWeilPrincipalValue v 1 f = -(V𝔭(v) : ℂ) * T g := by
    let wt : Kˣ → ℂ := fun u ↦ f.val u / (Real.sqrt ‖u.val‖ : ℂ)
    have hl : IsLocallyConstant wt := (finiteUnits_test_isLocallyConstant v f).comp₂
      ((finiteUnits_norm_isLocallyConstant v).comp fun t ↦ ((Real.sqrt t : ℝ) : ℂ)) (· / ·)
    have hc : HasCompactSupport wt := HasCompactSupport.mono f.property.2 fun u hu h0 ↦ hu (by
      change f.val u / _ = 0
      rw [h0, zero_div])
    obtain ⟨hEl, hEc⟩ := finiteUnits_extend_regular v wt hl hc
    obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v _).mpr ⟨hEl, hEc⟩
    have hgx (x : K) : addTest(g) x = zeroExtend(f.val) x / (Real.sqrt ‖x‖ : ℂ) := by
      show g (Multiplicative.ofAdd x) = _
      rw [hg]
      by_cases hr : ∃ u : Kˣ, u.val = x
      · obtain ⟨u, rfl⟩ := hr
        rw [Units.val_injective.extend_apply, Units.val_injective.extend_apply]
      · rw [extend_apply' _ _ _ hr, extend_apply' _ _ _ hr, zero_div]
    refine ⟨g, hgx, ?_⟩
    have hτg : τ g = (exists_finiteWeilTestMap v).choose f := by
      refine SchwartzBruhat.ext fun x ↦ ?_
      change addTest(τ g) x.toAdd = addTest((exists_finiteWeilTestMap v).choose f) x.toAdd
      rw [hτ, hgx, (exists_finiteWeilTestMap v).choose_spec f]
    rw [hT, show L g = -(V𝔭(v) : ℂ)⁻¹ * C (τ g) from rfl, hτg, neg_mul, neg_mul, mul_neg,
      neg_neg, ← mul_assoc, mul_inv_cancel₀ hVc, one_mul]
    rfl
  refine ⟨T, ⟨hA, h, hhf, hTh⟩, ?_, hC⟩
  -- Uniqueness: both conditions determine the value on every test.
  rintro S ⟨hSa, h', hh', hSh'⟩
  have hh'h : h' = h := SchwartzBruhat.ext fun x ↦ by
    change addTest(h') x.toAdd = addTest(h) x.toAdd
    rw [hh', hhf]
  rw [hh'h] at hSh'
  have h1 : addTest(h) 1 ≠ 0 := by
    rw [hhf]
    exact existsUnique_finiteWeilFourierDistribution_sphere_fourier_one v
  refine ContinuousLinearMap.ext fun f ↦ ?_
  set a : ℂ := addTest(f) 1 / addTest(h) 1 with ha
  have hdec : addTest(f - a • h) 1 = 0 := by
    change f (Multiplicative.ofAdd 1) - a * h (Multiplicative.ofAdd 1) = 0
    rw [ha]
    field_simp
    ring
  calc S f = S (f - a • h) + a * S h := by rw [map_sub, map_smul, smul_eq_mul]; ring
    _ = T (f - a • h) + a * T h := by rw [hSa _ hdec, hA _ hdec, hSh', hTh]
    _ = T f := by rw [map_sub, map_smul, smul_eq_mul]; ring

/-- Paper: Lemma B.4.4.4(1), p. 622. Changing the finite additive
character by a multiplier adds a multiple of evaluation at zero to Connes's principal value. -/
theorem finiteConnesPrincipalValue_changeCharacter (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒮ₐ(v.adicCompletion F)) :
    finiteConnesPrincipalValue v a f = finiteConnesPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * addTest(f) 0 := by
  have ha := ((exists_finiteConnesPrincipalValue v a).choose_spec f).2
  change finiteConnesPrincipalValue v a f = _ at ha
  have h1 := (exists_finiteConnesPrincipalValue v 1).choose_spec f
  have h1E := h1.2
  change finiteConnesPrincipalValue v 1 f = _ at h1E
  have h1I := h1.1
  simp only [Units.val_one, norm_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
    one_mul] at h1I h1E
  have h1I' : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v) := h1I
  have hcE := (finiteLogFourier_comp_mul v f a h1I').2
  have hc : (ENNReal.ofReal √‖a.val‖).toReal = √‖a.val‖ :=
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  -- Changing the character and the measure dilates the transform and scales it by `√‖a‖`.
  have hF (y : v.adicCompletion F) :
      tamagawaFourier (ENNReal.ofReal √‖a.val‖ • ν𝔭(v)) (fun x ↦ ψ𝔭(v) (a.val * x))
        addTest(f) y = (√‖a.val‖ : ℝ) • tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) := by
    unfold tamagawaFourier
    rw [integral_smul_measure, hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [mul_left_comm a.val x y]
  beta_reduce at ha
  refine ha.trans (Eq.trans ?_ (congrArg (· + _) h1E.symm))
  rw [integral_smul_measure, hc]
  simp only [hF, mul_smul_comm]
  rw [integral_smul, hcE, smul_smul, mul_smul_comm, smul_smul, ← mul_assoc,
    Real.mul_self_sqrt (norm_nonneg _), mul_inv_cancel₀ (norm_ne_zero_iff.mpr a.ne_zero),
    one_smul]
  push_cast
  ring

/-- Paper: Lemma B.4.4.4(2), p. 622. The same change of character
adds a multiple of evaluation at one to the multiplicative principal value. -/
theorem finiteConnesWeilPrincipalValue_changeCharacter (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒟((v.adicCompletion F)ˣ)) :
    finiteConnesWeilPrincipalValue v a f = finiteConnesWeilPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * f.val 1 := by
  let A := (exists_finiteWeilTestMap v).choose
  have hunit := Units.val_injective.extend_apply f.val (fun _ ↦ 0)
    (1 : (v.adicCompletion F)ˣ)
  have hzero : addTest(A f) 0 = f.val 1 := by
    have h := (exists_finiteWeilTestMap v).choose_spec f 0
    simp only [add_zero, norm_one, Real.sqrt_one, Complex.ofReal_one, div_one] at h
    exact h.trans hunit
  exact (finiteConnesPrincipalValue_changeCharacter v a (A f)).trans
    (congrArg (fun z : ℂ ↦ finiteConnesWeilPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * z) hzero)

-- TODO(paper-gap): In the proof on p. 623 (footnote 24), the annihilator of
-- the maximal ideal is the inverse maximal ideal times the inverse different.
-- The second indicator in the printed display uses the different itself.

local notation "differentExp(" v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))


section ExplicitFormulaUnitsIndicator

/-- The indicator of a compact open subgroup is a test. -/
private theorem explicitFormula_subgroupIndicator_test
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) :
    ∃ f : 𝒟(G), f.val = (U : Set G).indicator (fun _ ↦ 1) := by
  classical
  let g : G → ℂ := (U : Set G).indicator (fun _ ↦ 1)
  let : CompactSpace (lcaAnnihilator U) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator U hU)
  have hClosed : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  have hSmooth : IsBruhatSmooth g := by
    intro p
    refine ⟨U, ⟨hClosed, isOpen_lcaAnnihilator U hUc, isCompactlyGeneratedGroup_of_compact⟩,
      ?_, ?_⟩
    · intro h x
      have hmem : h.val * x ∈ (U : Set G) ↔ x ∈ (U : Set G) := by
        refine ⟨fun hx ↦ ?_, U.mul_mem h.property⟩
        change x ∈ U
        simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem h.property) hx
      simp only [g, indicator_apply, hmem]
    · intro a ha
      let f₀ : a.quotient → ℂ := ({1} : Set a.quotient).indicator (fun _ ↦ 1)
      refine ⟨f₀, fun x ↦ ?_, ?_⟩
      · simp only [f₀, g, indicator_apply, mem_singleton_iff, a.quotient_mk_eq_one, ha]
        rfl
      · intro e z b
        let : DiscreteTopology a.quotient := QuotientGroup.discreteTopology (by
          rw [ha]
          exact hU.preimage continuous_subtype_val)
        let X := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
        let q : X → a.quotient := fun x ↦ e.equiv.symm (Multiplicative.ofAdd (elementaryCover x z b))
        have hq : Continuous q := e.equiv.symm.continuous.comp
          (continuous_fst.prodMk ((continuous_pi fun j ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
            ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).prodMk continuous_const))
        change ContDiff ℝ (p : ℕ∞) (fun x ↦ f₀ (q x))
        have heq : (fun x ↦ f₀ (q x)) = fun _ : X ↦ f₀ (q 0) :=
          funext fun x ↦ congrArg f₀ (TotallyDisconnectedSpace.eq_of_continuous q hq x 0)
        rw [heq]
        exact contDiff_const
  have hSub : Function.support g ⊆ (U : Set G) := support_indicator_subset
  have hSupport : HasCompactSupport g :=
    hUc.of_isClosed_subset isClosed_closure (closure_minimal hSub hClosed)
  exact ⟨⟨g, (mem_bruhatSmoothSubmodule_iff _).mpr hSmooth, hSupport⟩, rfl⟩

/-- Dilating a closed ball by a unit scales its mass by the norm of the unit. -/
private theorem explicitFormula_closedBall_mass_mul (v : Primes(F))
    (u : (v.adicCompletion F)ˣ) (R : ℝ) :
    (∫ y, (Metric.closedBall (0 : v.adicCompletion F) (‖u.val‖ * R)).indicator
        (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)) =
      ((‖u.val‖ : ℝ) : ℂ) * ∫ z, (Metric.closedBall (0 : v.adicCompletion F) R).indicator
        (fun _ ↦ (1 : ℂ)) z ∂ν𝔭(v) := by
  have hu : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have h := finiteLocalAdditive_integral_comp_mul v u
    ((Metric.closedBall (0 : v.adicCompletion F) (‖u.val‖ * R)).indicator (fun _ ↦ (1 : ℂ)))
  have hind (z : v.adicCompletion F) :
      (Metric.closedBall (0 : v.adicCompletion F) (‖u.val‖ * R)).indicator
        (fun _ ↦ (1 : ℂ)) (u.val * z) =
      (Metric.closedBall (0 : v.adicCompletion F) R).indicator (fun _ ↦ (1 : ℂ)) z := by
    simp only [indicator, Metric.mem_closedBall, dist_zero_right, norm_mul,
      mul_le_mul_iff_right₀ hu]
  simp only [hind] at h
  rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hu.ne',
    Complex.ofReal_one, one_mul]

/-- Dilating a closed ball by a unit: the logarithmic integral over the dilate. -/
private theorem explicitFormula_closedBall_log_mul (v : Primes(F))
    (u : (v.adicCompletion F)ˣ) (R : ℝ) :
    (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * (Metric.closedBall (0 : v.adicCompletion F) (‖u.val‖ * R)).indicator
        (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)) =
      ((‖u.val‖ : ℝ) : ℂ) * ((∫ z, ((J𝔭(v) z : ℝ) : ℂ) *
        (Metric.closedBall (0 : v.adicCompletion F) R).indicator (fun _ ↦ (1 : ℂ)) z ∂ν𝔭(v)) +
        ((Real.log ‖u.val‖ / Real.log q(v) : ℝ) : ℂ) *
          ∫ z, (Metric.closedBall (0 : v.adicCompletion F) R).indicator
            (fun _ ↦ (1 : ℂ)) z ∂ν𝔭(v)) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hu : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  let B : Set K := Metric.closedBall 0 R
  let ι : K → ℂ := B.indicator (fun _ ↦ (1 : ℂ))
  have h := finiteLocalAdditive_integral_comp_mul v u
    (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      (Metric.closedBall (0 : K) (‖u.val‖ * R)).indicator (fun _ ↦ (1 : ℂ)) y)
  have hind (z : K) :
      (Metric.closedBall (0 : K) (‖u.val‖ * R)).indicator (fun _ ↦ (1 : ℂ)) (u.val * z) = ι z := by
    simp only [ι, B, indicator, Metric.mem_closedBall, dist_zero_right, norm_mul,
      mul_le_mul_iff_right₀ hu]
  have h0 : ∀ᵐ y ∂ν𝔭(v), y ≠ 0 := by
    have : (𝓝[≠] (0 : K)).NeBot := by
      let := Valued.toNontriviallyNormedField K _
      exact NormedField.nhdsNE_neBot 0
    rw [ae_iff]
    simp
  have hae : (fun z ↦ ((J𝔭(v) (u.val * z) : ℝ) : ℂ) *
      (Metric.closedBall (0 : K) (‖u.val‖ * R)).indicator (fun _ ↦ (1 : ℂ)) (u.val * z)) =ᵐ[ν𝔭(v)]
      fun z ↦ ((J𝔭(v) z : ℝ) : ℂ) * ι z +
        ((Real.log ‖u.val‖ / Real.log q(v) : ℝ) : ℂ) * ι z := by
    filter_upwards [h0] with z hz
    rw [hind, finiteLog_mul v u hz, add_mul]
  -- Integrability on the ball.
  by_cases hR : 0 < R
  · obtain ⟨g, hg⟩ := finiteLogFourier_eq_neg_haar_clopenTest v B
      (IsUltrametricDist.isClopen_closedBall 0 hR.ne') (isCompact_closedBall 0 R)
    have hJI : Integrable (fun z ↦ ((J𝔭(v) z : ℝ) : ℂ) * ι z) ν𝔭(v) :=
      (finiteLog_integrable_mul_test v g).congr (ae_of_all _ fun z ↦ by simp only [hg]; rfl)
    have hιI : Integrable ι ν𝔭(v) :=
      ((continuousOn_const (c := (1 : ℂ))).integrableOn_compact
        (isCompact_closedBall (0 : K) R)).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
    rw [integral_congr_ae hae, integral_add hJI (hιI.const_mul _), integral_const_mul] at h
    rw [Complex.real_smul] at h
    have hne : ((‖u.val‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hu.ne', Complex.ofReal_one, one_mul]
  · have hB : ∀ z : K, ι z = 0 ∨ z = 0 := by
      intro z
      by_cases hz : z ∈ B
      · right
        have : ‖z‖ ≤ R := by simpa [B] using hz
        exact norm_le_zero_iff.mp (this.trans (not_lt.mp hR))
      · left
        exact indicator_of_notMem hz _
    have hι0 : ι =ᵐ[ν𝔭(v)] 0 := by
      filter_upwards [h0] with z hz
      rcases hB z with h1 | h1
      · exact h1
      · exact absurd h1 hz
    have hι0' : (Metric.closedBall (0 : K) (‖u.val‖ * R)).indicator (fun _ ↦ (1 : ℂ)) =ᵐ[ν𝔭(v)] 0 := by
      filter_upwards [h0] with z hz
      refine indicator_of_notMem (fun hm ↦ hz ?_) _
      have : ‖z‖ ≤ ‖u.val‖ * R := by simpa using hm
      exact norm_le_zero_iff.mp (this.trans (mul_nonpos_of_nonneg_of_nonpos hu.le (not_lt.mp hR)))
    have e1 : (∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
        (Metric.closedBall (0 : K) (‖u.val‖ * R)).indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)) = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [hι0'] with z hz
      simp [hz]
    have e2 : (∫ z, ((J𝔭(v) z : ℝ) : ℂ) * ι z ∂ν𝔭(v)) = 0 := by
      rw [integral_eq_zero_of_ae]
      filter_upwards [hι0] with z hz
      simp [hz]
    have e3 : (∫ z, ι z ∂ν𝔭(v)) = 0 := by
      rw [integral_eq_zero_of_ae hι0]
    change _ = _ * ((∫ z, ((J𝔭(v) z : ℝ) : ℂ) * ι z ∂ν𝔭(v)) + _ * ∫ z, ι z ∂ν𝔭(v))
    rw [e1, e2, e3]
    simp

end ExplicitFormulaUnitsIndicator

/-- Paper: Lemma B.4.4.5, p. 622, in the one remaining case `f = 1_{O_v^×}`.
The rescaled principal value of the integer-unit indicator is minus the local
different contribution. The two integrals of the unit-subtracted finite part
vanish on this test, so this is exactly the constant by which
`finiteConnesWeilPrincipalValue_eq_finitePart` fails for a general test.
It is the calculation of pp. 622--623: the Fourier transform of the indicator
of `-1 + O_v^×` against the normalized logarithm, whose printed form carries the
footnote "the right side should be double-checked"; see the `TODO(paper-gap)`
note directly above. -/
theorem finiteConnesWeilPrincipalValue_unitsIndicator (v : Primes(F)) :
    ∃ b : 𝒟((v.adicCompletion F)ˣ),
      b.val = indicator ((O(v)).units : Set (v.adicCompletion F)ˣ) (fun _ ↦ 1) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 b =
        -(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hU : IsOpen (((O(v)).units : Subgroup Kˣ) : Set Kˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact (((O(v)).units : Subgroup Kˣ) : Set Kˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  obtain ⟨b, hb⟩ := explicitFormula_subgroupIndicator_test _ hU hUc
  refine ⟨b, hb, ?_⟩
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < q(v) := zero_lt_one.trans hq
  have hlq : 0 < Real.log q(v) := Real.log_pos hq
  set d : ℕ := differentExp(v) with hd
  -- The mass of the integer ring, which is also the mass of the integer units.
  set M : ℝ := (ν𝔭(v) (O(v) : Set K)).toReal with hMdef
  have hMval : M = (Real.sqrt (q(v) ^ d))⁻¹ := by
    rw [hMdef, finiteLocalAdditiveTamagawaMeasure_integers, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hV : V𝔭(v) = M := by
    rw [hMdef, finiteLocalMultiplicativeTamagawaMeasure_integerUnits,
      finiteLocalAdditiveTamagawaMeasure_integers]
  have hqd : 0 < q(v) ^ d := pow_pos hq0 d
  have hM2 : M * M * q(v) ^ d = 1 := by
    rw [hMval, ← mul_inv, Real.mul_self_sqrt hqd.le, inv_mul_cancel₀ hqd.ne']
  have hMpos : 0 < M := by rw [hMval]; exact inv_pos.mpr (Real.sqrt_pos.mpr hqd)
  -- A uniformizer.
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 π.val hπ.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  let SO : Set K := Metric.closedBall 0 1
  let SP : Set K := Metric.closedBall 0 (q(v)⁻¹)
  have hSO : (O(v) : Set K) = SO := by
    ext y
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    simp [SO]
  have hqinv : (0 : ℝ) < q(v)⁻¹ := inv_pos.mpr hq0
  have hqinv1 : q(v)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  obtain ⟨gO, hgO⟩ := finiteLogFourier_eq_neg_haar_clopenTest v SO
    (IsUltrametricDist.isClopen_closedBall 0 one_ne_zero) (isCompact_closedBall 0 1)
  obtain ⟨gT, hgT₀⟩ := finiteLogFourier_eq_neg_haar_clopenTest v ((fun y ↦ 1 + y) ⁻¹' SP)
    ((IsUltrametricDist.isClopen_closedBall (0 : K) hqinv.ne').preimage
      (continuous_const.add continuous_id))
    ((Homeomorph.addLeft (1 : K)).isCompact_preimage.mpr (isCompact_closedBall 0 _))
  have hgT (x : K) : gT (Multiplicative.ofAdd x) = SP.indicator (fun _ ↦ (1 : ℂ)) (1 + x) := by
    rw [hgT₀]
    simp only [indicator, mem_preimage]
  -- Small norms are at most `q⁻¹`.
  have hsmall (x : K) (hx : ‖x‖ < 1) : ‖x‖ ≤ q(v)⁻¹ := by
    by_contra h
    exact hx.ne (finiteLogFourier_eq_neg_haar_norm_eq_one v x hx.le (not_le.mp h))
  have hn1 : ‖(-1 : K)‖ = 1 := by rw [norm_neg, norm_one]
  -- The weighted translate of the unit indicator is `1_O - 1_{-1+𝔭}`.
  let A := (exists_finiteWeilTestMap v).choose
  have hAb : A b = gO - gT := by
    refine SchwartzBruhat.ext fun x ↦ ?_
    change addTest(A b) x.toAdd = addTest(gO) x.toAdd - addTest(gT) x.toAdd
    rw [(exists_finiteWeilTestMap v).choose_spec b]
    beta_reduce
    rw [hgO, hgT x.toAdd]
    set y := x.toAdd
    have hy1 : ‖y‖ ≤ max ‖1 + y‖ 1 := by
      have := IsUltrametricDist.norm_add_le_max (1 + y) (-1 : K)
      rwa [add_neg_cancel_comm, hn1] at this
    have h1y : ‖1 + y‖ ≤ max ‖y‖ 1 := by
      have := IsUltrametricDist.norm_add_le_max (1 : K) y
      rwa [norm_one, max_comm] at this
    by_cases h0 : (1 : K) + y = 0
    · have hy : ‖y‖ = 1 := by
        rw [show y = -1 from by linear_combination h0, hn1]
      change Function.extend Units.val (b.val : _ → ℂ) (fun _ ↦ 0) (1 + y) / _ = _
      rw [Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ u.ne_zero (hu.trans h0)), h0]
      simp [SO, SP, hy, hqinv.le]
    · let u : Kˣ := Units.mk0 (1 + y) h0
      have hu : u.val = 1 + y := rfl
      change Function.extend Units.val (b.val : _ → ℂ) (fun _ ↦ 0) (1 + y) / _ = _
      rw [← hu, Units.val_injective.extend_apply, hb]
      have hmem : u ∈ (O(v)).units ↔ ‖u.val‖ = 1 := by
        rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
          Valued.toNormedField.norm_eq_one_iff]
      rw [hu] at hmem ⊢
      rcases lt_trichotomy ‖1 + y‖ 1 with hlt | heq | hgt
      · have hy : ‖y‖ ≤ 1 := hy1.trans (max_le hlt.le le_rfl)
        have hnm : u ∉ (O(v)).units := fun h ↦ hlt.ne (hmem.mp h)
        rw [indicator_of_notMem (show u ∈ _ → False from hnm)]
        simp [SO, SP, hy, hsmall _ hlt]
      · have hy : ‖y‖ ≤ 1 := hy1.trans (by rw [heq, max_self])
        have hm : u ∈ ((O(v)).units : Set Kˣ) := hmem.mpr heq
        rw [indicator_of_mem hm, heq]
        have : ¬ ‖1 + y‖ ≤ q(v)⁻¹ := by rw [heq]; exact not_le.mpr hqinv1
        simp [SO, SP, hy, this]
      · have hy : ¬ ‖y‖ ≤ 1 := fun h ↦ (h1y.trans (max_le h le_rfl)).not_gt hgt
        have hnm : u ∉ (O(v)).units := fun h ↦ hgt.ne' (hmem.mp h)
        rw [indicator_of_notMem (show u ∈ _ → False from hnm)]
        have : ¬ ‖1 + y‖ ≤ q(v)⁻¹ := fun h ↦ (h.trans hqinv1.le).not_gt hgt
        simp [SO, SP, hy, this]
  let C := finiteConnesPrincipalValue v 1
  have hPV : finiteConnesWeilPrincipalValue v 1 b = C gO - C gT := by
    change C (A b) = _
    rw [hAb, map_sub]
  have hnorm1 : ¬ ‖(1 : K)‖ ≤ q(v)⁻¹ := by rw [norm_one]; exact not_le.mpr hqinv1
  -- Masses of the two balls.
  have hIO : (∫ y, SO.indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)) = M := by
    rw [integral_indicator Metric.isClosed_closedBall.measurableSet, setIntegral_const,
      Complex.real_smul, mul_one, measureReal_def, hMdef, hSO]
  have hpR : ‖p.val‖ * 1 = q(v)⁻¹ := by rw [hp, mul_one]
  have hIP : (∫ y, SP.indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)) = (q(v)⁻¹ : ℝ) * M := by
    have h := explicitFormula_closedBall_mass_mul v p 1
    rw [hpR, hp] at h
    rw [h]
    exact congrArg _ hIO
  -- The value on the translated small ball is its multiplicative mass.
  have hgT0 : addTest(gT) 0 = 0 := by
    beta_reduce
    rw [hgT, add_zero]
    exact indicator_of_notMem (fun h ↦ hnorm1 (by simpa [SP] using h)) _
  have hCT : C gT = (M / (q(v) - 1) : ℝ) := by
    change finiteConnesPrincipalValue v 1 gT = _
    rw [finiteConnesPrincipalValue_one_of_apply_zero v gT hgT0,
      existsUnique_finiteWeilFourierDistribution_units_integral v
        (fun x ↦ gT (Multiplicative.ofAdd x))]
    have hpt : (fun y ↦ addTest(gT) y / ((‖y‖ : ℝ) : ℂ)) =
        fun y ↦ SP.indicator (fun _ ↦ (1 : ℂ)) (1 + y) := by
      funext y
      beta_reduce
      rw [hgT]
      by_cases hy : 1 + y ∈ SP
      · have h1 : ‖1 + y‖ ≤ q(v)⁻¹ := by simpa [SP] using hy
        have hy1 : ‖y‖ = 1 := by
          apply le_antisymm
          · have := IsUltrametricDist.norm_add_le_max (1 + y) (-1 : K)
            rw [add_neg_cancel_comm, hn1] at this
            exact this.trans (max_le (h1.trans hqinv1.le) le_rfl)
          · have := IsUltrametricDist.norm_add_le_max (1 + y) (-y)
            rw [add_neg_cancel_right, norm_one, norm_neg] at this
            rcases le_max_iff.mp this with h | h
            · exact (lt_irrefl (1 : ℝ) (h.trans_lt (h1.trans_lt hqinv1))).elim
            · exact h
        rw [hy1, Complex.ofReal_one, div_one]
      · rw [indicator_of_notMem hy, zero_div]
    rw [show (fun y ↦ (fun x ↦ gT (Multiplicative.ofAdd x)) y / ((‖y‖ : ℝ) : ℂ)) =
      fun y ↦ SP.indicator (fun _ ↦ (1 : ℂ)) (1 + y) from hpt,
      integral_add_left_eq_self (fun y ↦ SP.indicator (fun _ ↦ (1 : ℂ)) y) 1, hIP]
    have hqc : ((q(v) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    field_simp
    rw [mul_div_mul_left _ _ (by exact_mod_cast hq0.ne')]
  -- The logarithmic integral over the integer ring, by self-similarity.
  set Aint : ℂ := ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * SO.indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v) with hAint
  have hJP : (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * SP.indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)) = Aint := by
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    by_cases h1 : ‖y‖ ≤ q(v)⁻¹
    · have h2 : ‖y‖ ≤ 1 := h1.trans hqinv1.le
      simp [SO, SP, h1, h2]
    · by_cases h2 : ‖y‖ ≤ 1
      · have he := finiteLogFourier_eq_neg_haar_norm_eq_one v y h2 (not_le.mp h1)
        simp [SO, SP, he]
      · simp [SO, SP, h1, h2]
  have hlogp : Real.log ‖p.val‖ / Real.log q(v) = -1 := by
    rw [hp, Real.log_inv, neg_div, div_self hlq.ne']
  have hAeq : Aint = ((q(v)⁻¹ : ℝ) : ℂ) * (Aint + ((-1 : ℝ) : ℂ) * M) := by
    have h := explicitFormula_closedBall_log_mul v p 1
    rw [hpR, hlogp, hp] at h
    have h2 : (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * SP.indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)) =
        ((q(v)⁻¹ : ℝ) : ℂ) * (Aint + ((-1 : ℝ) : ℂ) * M) := by
      rw [hAint, ← hIO]
      exact h
    exact hJP.symm.trans h2
  have hqc : ((q(v) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hq1c : ((q(v) : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hq.ne'
  have hAval : Aint = -(M : ℂ) / (((q(v) : ℝ) : ℂ) - 1) := by
    rw [eq_div_iff hq1c]
    have hinv : ((q(v) : ℝ) : ℂ) * ((q(v)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hq0.ne', Complex.ofReal_one]
    have h := hAeq
    rw [Complex.ofReal_neg, Complex.ofReal_one] at h
    linear_combination ((q(v) : ℝ) : ℂ) * h + (Aint - M) * hinv
  -- The logarithmic integral over the inverse different.
  let u : Kˣ := p⁻¹ ^ d
  have hu : ‖u.val‖ = q(v) ^ d := by
    simp [u, Units.val_pow_eq_pow_val, norm_pow, norm_inv, hp]
  have hD : {x : K | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(v)} =
      Metric.closedBall (0 : K) (‖u.val‖ * 1) := by
    ext x
    simp [hu, d]
  have hlogu : Real.log ‖u.val‖ / Real.log q(v) = d := by
    rw [hu, Real.log_pow, mul_div_assoc, div_self hlq.ne', mul_one]
  have hB := explicitFormula_closedBall_log_mul v u 1
  rw [← hD, hlogu, hu] at hB
  change _ = ((q(v) ^ d : ℝ) : ℂ) * ((∫ z, ((J𝔭(v) z : ℝ) : ℂ) * SO.indicator (fun _ ↦ (1 : ℂ)) z
    ∂ν𝔭(v)) + ((d : ℝ) : ℂ) * ∫ z, SO.indicator (fun _ ↦ (1 : ℂ)) z ∂ν𝔭(v)) at hB
  rw [← hAint, hIO] at hB
  -- The value on the integer ring through its Fourier transform.
  have hgOf : addTest(gO) = (O(v) : Set K).indicator (fun _ ↦ (1 : ℂ)) := by
    funext y
    rw [hgO, hSO]
  have hCO : C gO = -(M : ℂ) * ((M : ℂ) * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
      {x : K | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(v)}.indicator (fun _ ↦ (1 : ℂ)) y
        ∂ν𝔭(v)) := by
    change finiteConnesPrincipalValue v 1 gO = _
    rw [existsUnique_finiteWeilFourierDistribution_principalValue, hgOf,
      finiteLocalTamagawaFourier_integers, ← finiteLocalAdditiveTamagawaMeasure_integers, hV]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hPV, hCO, hCT, hB, hAval, hV]
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hM2n : (M : ℂ) ^ 2 * ((v.asIdeal.absNorm : ℕ) : ℂ) ^ d = 1 := by
    rw [sq]; exact_mod_cast hM2
  push_cast
  field_simp
  rw [hM2n]
  ring

/-- Paper: Lemma B.4.4.5, p. 622. The rescaled finite principal value is
the unit-subtracted finite part with the different correction. -/
theorem finiteConnesWeilPrincipalValue_eq_finitePart (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) :
    let units : Set (v.adicCompletion F)ˣ := (O(v)).units
    let outside := finiteWeilIntegrand(v, f.val)
    let inside := finiteWeilIntegrand(v, (fun u ↦ f.val u - f.val 1))
    IntegrableOn outside unitsᶜ μ𝔭(v) ∧ IntegrableOn inside units μ𝔭(v) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
        finiteWeilScale(v) * ((∫ u in unitsᶜ, outside u ∂μ𝔭(v)) +
          (∫ u in units, inside u ∂μ𝔭(v))) -
        ((differentExp(v) : ℝ) * Real.log q(v) : ℝ) * f.val 1 := by
  obtain ⟨b, hbval, hbscale⟩ := finiteConnesWeilPrincipalValue_unitsIndicator v
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have hU : IsOpen ((O(v)).units : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUmeas : MeasurableSet ((O(v)).units : Set (v.adicCompletion F)ˣ) := hU.measurableSet
  have hb1 : b.val 1 = 1 := by
    rw [hbval]
    exact Set.indicator_of_mem (Subgroup.one_mem _) _
  set c : ℂ := f.val 1 with hc
  set g : 𝒟((v.adicCompletion F)ˣ) := f - c • b with hg
  have hgval (u : (v.adicCompletion F)ˣ) : g.val u = f.val u - c * b.val u := by
    rw [hg]
    rfl
  have hg1 : g.val 1 = 0 := by
    rw [hgval, hb1, hc]
    ring
  -- The test `g` vanishes at one, so the ordinary integral computes its principal value.
  obtain ⟨hintg, hPg0⟩ := finiteConnesWeilPrincipalValue_of_apply_one_zero v g hg1
  have hPg : finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 g =
      finiteWeilScale(v) * ∫ u, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) := by rw [hPg0]
  -- The principal value is linear, so the correction is the one of the indicator.
  have hfe : f = g + c • b := by
    rw [hg]
    abel
  have hP : finiteConnesWeilPrincipalValue v 1 f =
      finiteConnesWeilPrincipalValue v 1 g + c * finiteConnesWeilPrincipalValue v 1 b := by
    rw [hfe, map_add, map_smul, smul_eq_mul]
  -- Off the integer units the subtracted test agrees with the original one,
  -- and on them the unit-subtracted integrands agree.
  have hout (u : (v.adicCompletion F)ˣ) (hu : u ∉ (O(v)).units) :
      finiteWeilIntegrand(v, f.val) u = finiteWeilIntegrand(v, g.val) u := by
    have hbu : b.val u = 0 := by
      rw [hbval]
      exact Set.indicator_of_notMem hu _
    have hgu : g.val u = f.val u := by rw [hgval, hbu, mul_zero, sub_zero]
    exact (congrArg (fun t : ℂ ↦ t * (Real.sqrt ‖u.val‖ : ℂ) /
      ((‖1 - u.val‖ : ℝ) : ℂ)) hgu).symm
  have hin (u : (v.adicCompletion F)ˣ) (hu : u ∈ (O(v)).units) :
      finiteWeilIntegrand(v, (fun u ↦ f.val u - f.val 1)) u =
        finiteWeilIntegrand(v, g.val) u := by
    have hbu : b.val u = 1 := by
      rw [hbval]
      exact Set.indicator_of_mem hu _
    have hgu : g.val u = f.val u - f.val 1 := by rw [hgval, hbu, mul_one]
    exact (congrArg (fun t : ℂ ↦ t * (Real.sqrt ‖u.val‖ : ℂ) /
      ((‖1 - u.val‖ : ℝ) : ℂ)) hgu).symm
  have houtI : (∫ u in ((O(v)).units)ᶜ, finiteWeilIntegrand(v, f.val) u ∂μ𝔭(v)) =
      ∫ u in ((O(v)).units)ᶜ, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) :=
    setIntegral_congr_fun hUmeas.compl (fun u hu ↦ hout u hu)
  have hinI :
      (∫ u in ((O(v)).units), finiteWeilIntegrand(v, (fun u ↦ f.val u - f.val 1)) u ∂μ𝔭(v)) =
        ∫ u in ((O(v)).units), finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) :=
    setIntegral_congr_fun hUmeas (fun u hu ↦ hin u hu)
  have hsum : (∫ u in ((O(v)).units)ᶜ, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v)) +
      (∫ u in ((O(v)).units), finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v)) =
      ∫ u, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) := by
    rw [add_comm]
    exact integral_add_compl hUmeas hintg
  have hkey : finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
      finiteWeilScale(v) * (∫ u, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v)) +
        c * (-(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ)) := by
    have e1 : finiteWeilScale(v) * (c * finiteConnesWeilPrincipalValue v 1 b) =
        c * (finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 b) := by ring
    rw [hP, mul_add, hPg, e1, hbscale]
  refine ⟨hintg.integrableOn.congr_fun (fun u hu ↦ (hout u hu).symm) hUmeas.compl,
    hintg.integrableOn.congr_fun (fun u hu ↦ (hin u hu).symm) hUmeas, ?_⟩
  dsimp only
  rw [houtI, hinI, hsum, hkey]
  ring

/-- Evaluating the finite part on a compact open subgroup indicator gives the correction term. -/
private theorem finiteConnesWeilPrincipalValue_integerUnits_test
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G))
    (μ : Measure G) (num den : G → ℂ) (eval : 𝒟(G) → ℂ) (scale correction : ℂ)
    (heval : ∀ f : 𝒟(G), eval f =
      scale * ((∫ u in (U : Set G)ᶜ, f.val u * num u / den u ∂μ) +
        (∫ u in (U : Set G), (f.val u - f.val 1) * num u / den u ∂μ)) -
      correction * f.val 1) :
    ∃ f : 𝒟(G), f.val = (U : Set G).indicator (fun _ ↦ 1) ∧ eval f = -correction := by
  classical
  let g : G → ℂ := (U : Set G).indicator (fun _ ↦ 1)
  let : CompactSpace (lcaAnnihilator U) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator U hU)
  have hClosed : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  have hSmooth : IsBruhatSmooth g := by
    intro p
    refine ⟨U, ⟨hClosed, isOpen_lcaAnnihilator U hUc, isCompactlyGeneratedGroup_of_compact⟩,
      ?_, ?_⟩
    · intro h x
      have hmem : h.val * x ∈ (U : Set G) ↔ x ∈ (U : Set G) := by
        refine ⟨fun hx ↦ ?_, U.mul_mem h.property⟩
        change x ∈ U
        simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem h.property) hx
      simp only [g, indicator_apply, hmem]
    · intro a ha
      let f₀ : a.quotient → ℂ := ({1} : Set a.quotient).indicator (fun _ ↦ 1)
      refine ⟨f₀, fun x ↦ ?_, ?_⟩
      · simp only [f₀, g, indicator_apply, mem_singleton_iff, a.quotient_mk_eq_one, ha]
        rfl
      · intro e z b
        let : DiscreteTopology a.quotient := QuotientGroup.discreteTopology (by
          rw [ha]
          exact hU.preimage continuous_subtype_val)
        let X := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
        let q : X → a.quotient := fun x ↦ e.equiv.symm (Multiplicative.ofAdd (elementaryCover x z b))
        have hq : Continuous q := e.equiv.symm.continuous.comp
          (continuous_fst.prodMk ((continuous_pi fun j ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
            ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).prodMk continuous_const))
        change ContDiff ℝ (p : ℕ∞) (fun x ↦ f₀ (q x))
        have heq : (fun x ↦ f₀ (q x)) = fun _ : X ↦ f₀ (q 0) :=
          funext fun x ↦ congrArg f₀ (TotallyDisconnectedSpace.eq_of_continuous q hq x 0)
        rw [heq]
        exact contDiff_const
  have hSub : Function.support g ⊆ (U : Set G) := support_indicator_subset
  have hSupport : HasCompactSupport g :=
    hUc.of_isClosed_subset isClosed_closure (closure_minimal hSub hClosed)
  let f : 𝒟(G) := ⟨g, (mem_bruhatSmoothSubmodule_iff _).mpr hSmooth, hSupport⟩
  have hOne : g 1 = 1 := indicator_of_mem U.one_mem (fun _ : G ↦ (1 : ℂ))
  have hOut : (∫ u in (U : Set G)ᶜ, f.val u * num u / den u ∂μ) = 0 := by
    change (∫ u in (U : Set G)ᶜ, g u * num u / den u ∂μ) = 0
    calc
      _ = ∫ _u in (U : Set G)ᶜ, (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU.measurableSet.compl
        intro u hu
        have hgu : g u = 0 := indicator_of_notMem hu _
        simp only [hgu, zero_mul, zero_div]
      _ = 0 := by simp
  have hIn : (∫ u in (U : Set G), (f.val u - f.val 1) * num u / den u ∂μ) = 0 := by
    change (∫ u in (U : Set G), (g u - g 1) * num u / den u ∂μ) = 0
    calc
      _ = ∫ _u in (U : Set G), (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU.measurableSet
        intro u hu
        have hgu : g u = 1 := indicator_of_mem hu (fun _ : G ↦ (1 : ℂ))
        simp only [hgu, hOne, sub_self, zero_mul, zero_div]
      _ = 0 := by simp
  refine ⟨f, rfl, ?_⟩
  have hValue := heval f
  have hfOne : f.val 1 = 1 := hOne
  rw [hOut, hIn, hfOne, add_zero, mul_zero, zero_sub, mul_one] at hValue
  exact hValue

/-- Paper: Lemma B.4.4.5, p. 622. The integer-unit indicator detects
the different contribution to the Fourier-defined principal value. The
unit-subtracted finite part is zero on this test. -/
theorem finiteConnesWeilPrincipalValue_integerUnits (v : Primes(F)) :
    ∃ f : 𝒟((v.adicCompletion F)ˣ),
      f.val = indicator ((O(v)).units : Set (v.adicCompletion F)ˣ) (fun _ ↦ 1) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
        -(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ) := by
  let U : Subgroup (v.adicCompletion F)ˣ := (O(v)).units
  have hU : IsOpen (U : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact (U : Set (v.adicCompletion F)ˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  exact finiteConnesWeilPrincipalValue_integerUnits_test U hU hUc (μ𝔭(v))
    (fun u : (v.adicCompletion F)ˣ ↦ (Real.sqrt ‖u.val‖ : ℂ))
    (fun u : (v.adicCompletion F)ˣ ↦ ((‖1 - u.val‖ : ℝ) : ℂ))
    (fun f ↦ finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f)
    finiteWeilScale(v) (((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ)
    (fun f ↦ (finiteConnesWeilPrincipalValue_eq_finitePart v f).2.2)

/-- Paper: Remark B.4.4.6, p. 623. A finite local test agrees with its value at
one on a neighborhood of one, so the unit-subtracted integrand vanishes there. -/
theorem finiteWeilTest_eventually_eq_at_one (v : Primes(F)) (f : 𝒟((v.adicCompletion F)ˣ)) :
    ∀ᶠ u in 𝓝 (1 : (v.adicCompletion F)ˣ), f.val u = f.val 1 := by
  let G := (v.adicCompletion F)ˣ
  have hf : IsBruhatSmooth f.val := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1
  obtain ⟨k, hk, hInv, _⟩ := hf 0
  let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator k, hk.2⟩
  obtain ⟨γ, _, hγ, hker, _⟩ := lca_dualSubgroup_quotient A
  let Q := PontryaginDual A.val
  let : LocallyCompactSpace A.val := A.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨n, ⟨charts⟩⟩ := isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp A.property.2
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q := charts
  let : LocallyConnectedSpace Q := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) Q
  let B : OpenSubgroup G :=
    ⟨(v.adicCompletionIntegers F).units, Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)⟩
  let : CompactSpace B.toSubgroup := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let j : B.toSubgroup → v.adicCompletion F := Units.val ∘ Subtype.val
  have hj : Topology.IsEmbedding j :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).comp Topology.IsEmbedding.subtypeVal
  let η : B.toSubgroup →ₜ* Q := γ.comp ⟨B.toSubgroup.subtype, continuous_subtype_val⟩
  have hη : Continuous η := η.continuous
  have hηOpen : IsOpenMap η := hγ.isOpenMap.comp B.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hSmall (U : Set Q) (hU : U ∈ 𝓝 (1 : Q)) : ∃ V : OpenSubgroup Q, (V : Set Q) ⊆ U := by
    have hpre : η ⁻¹' U ∈ 𝓝 (1 : B.toSubgroup) :=
      hη.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
    rw [hj.isInducing.nhds_eq_comap] at hpre
    obtain ⟨S, hS, hSsub⟩ := mem_comap.mp hpre
    let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨r, hr⟩ := (Valued.mem_nhds (Γ₀ := WithZero (Multiplicative ℤ))).mp hS
    let W := (fun x : B.toSubgroup ↦ j x - j 1) ⁻¹' {y | ν.restrict y < r.val}
    have hW : IsClopen W :=
      (Valued.isClopen_ball (v.adicCompletion F) r.val).preimage
        (hj.continuous.sub continuous_const)
    have h1W : (1 : B.toSubgroup) ∈ W := by
      change ν.restrict (j 1 - j 1) < r.val
      rw [sub_self, map_zero]
      exact pos_iff_ne_zero.mpr r.ne_zero
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1W
    refine ⟨⟨V.toSubgroup.map η.toMonoidHom, hηOpen _ V.isOpen⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hSsub (hr (hV hx))
  have hComponent : connectedComponent (1 : Q) = {1} := by
    refine subset_antisymm ?_ (singleton_subset_iff.mpr mem_connectedComponent)
    intro y hy
    by_contra hne
    have h1y : (1 : Q) ∈ ({y} : Set Q)ᶜ :=
      fun h ↦ hne (mem_singleton_iff.mpr (mem_singleton_iff.mp h).symm)
    obtain ⟨V, hV⟩ := hSmall _ (isOpen_compl_singleton.mem_nhds h1y)
    have hyV := isPreconnected_connectedComponent.subset_isClopen V.isClopen
      ⟨1, mem_connectedComponent, V.one_mem⟩ hy
    exact (hV hyV) (mem_singleton y)
  have hOne : IsOpen ({1} : Set Q) := hComponent ▸ isOpen_connectedComponent
  have hkOpen : IsOpen (k : Set G) := by
    rw [← lcaDualAnnihilator_annihilator k hk.1, ← hker]
    exact hOne.preimage γ.continuous
  filter_upwards [hkOpen.mem_nhds k.one_mem] with u hu
  simpa only [mul_one] using hInv ⟨u, hu⟩ 1

end PrincipalValues

section IdelicExplicitFormula

/-- Paper: Theorem B.4.4.7, p. 623. Use the meromorphic continuation
from §3.2 to read off each zero's multiplicity in its norm-twist coordinate. -/
def explicitFormulaCompletedHeckeL (χ : U[F]) : ℂ → ℂ :=
  (completedHeckeL_exists_continuation χ).choose

/-- Paper: Theorem B.4.4.7, p. 623. The continued function is in
meromorphic normal form and agrees with the completed Euler product on the right half-plane. -/
theorem explicitFormulaCompletedHeckeL_spec (χ : U[F]) :
    MeromorphicNFOn (explicitFormulaCompletedHeckeL χ) univ ∧
      ∀ s : halfPlane, explicitFormulaCompletedHeckeL χ s = completedHeckeL χ s :=
  (completedHeckeL_exists_continuation χ).choose_spec

local notation "chartZeros(" τ ")" =>
  {z : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL z.1.val) univ z.2}
local notation "zeroMultiplicity(" z ")" =>
  (MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (z).val.1.val) univ (z).val.2 : ℂ)
local notation "zeroCharacter(" z ")" => ideleClassNormTwist (z).val.1.val (z).val.2
local notation "classVolume" => (normOneIdeleClassTamagawaMeasure F univ).toReal
local notation "classMeasure" => ideleClassTamagawaMeasure F
local notation "classWeight(" g ", " a ")" =>
  ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (a : ℂ))
local notation "classMellinIntegrand(" f ", " c ", " a ")" =>
  (fun g : C[F] ↦ (f).val g * c g * classWeight(g, a))
local notation "finiteClassMap(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "infiniteClassMap(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w

section ExplicitFormulaTestMaps

/-- A compactly supported test on the idele classes is a Schwartz–Bruhat function. -/
private theorem explicitTest_mem_schwartz (f : 𝒟(C[F])) :
    f.val ∈ schwartzBruhatSubmodule C[F] := by
  obtain ⟨m, _, hm, hms⟩ := exists_ideleClassModulation F
  have hf := bruhatCompactSupport_le_modulatedExponentialDecay m {0} hm hms f.property
  rwa [modulatedExponentialDecaySubmodule_singleton_zero] at hf

/-- A compactly supported test on the idele classes is continuous. -/
private theorem explicitTest_continuous (f : 𝒟(C[F])) : Continuous f.val := by
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff _).mp (explicitTest_mem_schwartz f)
  exact hs ▸ continuous_stage_realization a e s

/-- Integration against a continuous function is continuous on a fixed-support stage. -/
private theorem explicitStage_integral_continuous {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (c : G → ℂ) (hc : Continuous c) (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : TopologicalSpace.Compacts G) :
    Continuous (fun s : bruhatCompactSupportStage a e C ↦
      ∫ g, schwartzBruhatStageRealization a e s.val g * c g ∂μ) := by
  let E := SchwartzBruhatStage e
  let : TopologicalSpace.MetrizableSpace E := elementarySchwartz_isFrechet.choose_spec.2.1
  let : BarrelledSpace ℂ E := elementarySchwartz_barrelled
  let c' : G → ℂ := (C : Set G).indicator c
  have hc' : Integrable c' μ :=
    (integrable_indicator_iff C.isCompact.measurableSet).mpr
      (hc.continuousOn.integrableOn_compact C.isCompact)
  let A : E →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun s x ↦ schwartzBruhatStageRealization a e s x * c' x
      map_add' := fun s t ↦ funext fun x ↦ by simp only [map_add, Pi.add_apply, add_mul]
      map_smul' := fun z s ↦ funext fun x ↦ by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc] }
  obtain ⟨L, hL⟩ := exists_integralCLM_of_pointwise_continuous μ A
    (fun x ↦ (continuous_schwartzBruhatStage_eval a e x).mul_const _)
    (fun s ↦ hc'.bdd_mul (continuous_stage_realization a e s).aestronglyMeasurable
      (.of_forall fun x ↦ norm_stage_realization_le a e s x))
  refine (L.continuous.comp continuous_subtype_val).congr fun s ↦ ?_
  change L s.val = _
  rw [hL]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  change schwartzBruhatStageRealization a e s.val x * c' x =
    schwartzBruhatStageRealization a e s.val x * c x
  by_cases hx : x ∈ (C : Set G)
  · simp only [c', indicator_of_mem hx]
  · have hs : tsupport (schwartzBruhatStageRealization a e s.val) ⊆ (C : Set G) :=
      (mem_bruhatCompactSupportStage_iff a e C s.val).1 s.property
    have h0 : schwartzBruhatStageRealization a e s.val x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h)
    rw [h0, zero_mul, zero_mul]

/-- A cyclic subgroup small on a compact generating set of the annihilator
lies in the original closed subgroup. Copied from `Ch12_TraceGeometric/Sec4.lean`. -/
private theorem explicitFormula_smallPowers {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (K : Subgroup G) (hK : IsBruhatGoodSubgroup K) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ n : ℕ, x ^ n ∈ W) → x ∈ K := by
  let D := lcaAnnihilator K
  obtain ⟨C, _, hc, hgen⟩ := hK.2.2
  let arc := Circle.centeredArc (Real.pi / 2)
  have ha : arc ∈ 𝓝 (1 : Circle) := by
    simpa [arc] using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W := {x : G | ∀ χ ∈ C, (χ : D).val x ∈ arc}
  have hW : W ∈ 𝓝 (1 : G) := by
    apply hc.eventually_forall_of_forall_eventually
    intro χ _
    have hχ : Continuous (fun χ : D ↦ (χ.val : G →ₜ* Circle)) := continuous_subtype_val
    have he : Continuous (fun p : G × D ↦ p.2.val p.1) :=
      (continuous_eval (F := G →ₜ* Circle)).comp ((hχ.comp ((show Continuous (Prod.snd : G × D → D) from continuous_snd))).prodMk continuous_fst)
    exact he.continuousAt.preimage_mem_nhds (by simpa only [map_one] using ha)
  refine ⟨W, hW, fun x hx ↦ ?_⟩
  let ev : D →* Circle := ⟨⟨fun χ ↦ χ.val x, rfl⟩, fun _ _ ↦ rfl⟩
  have hg : C ⊆ ev.ker := by
    intro χ hχ
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    change χ.val x ^ n ∈ arc
    simpa only [map_pow] using hx n χ hχ
  have htop : ⊤ ≤ ev.ker := hgen ▸ (Subgroup.closure_le _).mpr hg
  rw [← lcaDualAnnihilator_annihilator K hK.1, mem_lcaDualAnnihilator_iff]
  exact fun χ ↦ htop (Subgroup.mem_top χ)

/-- A function invariant under a compact open subgroup and of compact support is a test
function. -/
private theorem explicitFormula_mem_of_openSubgroup_invariant {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) (g : G → ℂ)
    (hg : ∀ h ∈ U, ∀ x, g (h * x) = g x) (hgc : HasCompactSupport g) :
    g ∈ bruhatCompactSupportSubmodule G := by
  let : CompactSpace (lcaAnnihilator U) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator U hU)
  have hClosed : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  have hSmooth : IsBruhatSmooth g := by
    intro p
    refine ⟨U, ⟨hClosed, isOpen_lcaAnnihilator U hUc, isCompactlyGeneratedGroup_of_compact⟩,
      fun h x ↦ hg h.val h.property x, ?_⟩
    intro a ha
    let f₀ : a.quotient → ℂ := fun q ↦ g (Quotient.out q : a.val.1).val
    refine ⟨f₀, fun x ↦ ?_, ?_⟩
    · obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul
        ((OrderDual.ofDual a.val.2).comap a.val.1.subtype) x
      change g (Quotient.out (QuotientGroup.mk x : a.quotient) : a.val.1).val = g x.val
      have hmem : (h.val : G) ∈ U := ha ▸ Subgroup.mem_comap.mp h.property
      rw [hh, Subgroup.coe_mul, mul_comm]
      exact hg _ hmem _
    · intro e z b
      let : DiscreteTopology a.quotient := QuotientGroup.discreteTopology (by
        rw [ha]
        exact hU.preimage continuous_subtype_val)
      let X := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
      let q : X → a.quotient := fun x ↦ e.equiv.symm (Multiplicative.ofAdd (elementaryCover x z b))
      have hq : Continuous q := e.equiv.symm.continuous.comp
        (continuous_fst.prodMk ((continuous_pi fun j ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
          ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).prodMk continuous_const))
      change ContDiff ℝ (p : ℕ∞) (fun x ↦ f₀ (q x))
      have heq : (fun x ↦ f₀ (q x)) = fun _ : X ↦ f₀ (q 0) :=
        funext fun x ↦ congrArg f₀ (TotallyDisconnectedSpace.eq_of_continuous q hq x 0)
      rw [heq]
      exact contDiff_const
  exact ⟨(mem_bruhatSmoothSubmodule_iff _).mpr hSmooth, hgc⟩

/-- The units of a finite completion have arbitrarily small compact open subgroups. -/
private theorem explicitFormula_finiteUnits_openSubgroup (v : Primes(F))
    {W : Set (v.adicCompletion F)ˣ} (hW : W ∈ 𝓝 (1 : (v.adicCompletion F)ˣ)) :
    ∃ V : Subgroup (v.adicCompletion F)ˣ, IsOpen (V : Set (v.adicCompletion F)ˣ) ∧
      IsCompact (V : Set (v.adicCompletion F)ˣ) ∧ (V : Set (v.adicCompletion F)ˣ) ⊆ W := by
  let G := (v.adicCompletion F)ˣ
  let B : OpenSubgroup G :=
    ⟨(v.adicCompletionIntegers F).units, Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)⟩
  have hBc : IsCompact (B : Set G) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let : CompactSpace B.toSubgroup := isCompact_iff_compactSpace.mp hBc
  let j : B.toSubgroup → v.adicCompletion F := Units.val ∘ Subtype.val
  have hj : Topology.IsEmbedding j :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).comp Topology.IsEmbedding.subtypeVal
  have hpre : (Subtype.val : B.toSubgroup → G) ⁻¹' W ∈ 𝓝 (1 : B.toSubgroup) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  rw [hj.isInducing.nhds_eq_comap] at hpre
  obtain ⟨S, hS, hSsub⟩ := mem_comap.mp hpre
  let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨r, hr⟩ := (Valued.mem_nhds (Γ₀ := WithZero (Multiplicative ℤ))).mp hS
  let W' := (fun x : B.toSubgroup ↦ j x - j 1) ⁻¹' {y | ν.restrict y < r.val}
  have hW' : IsClopen W' :=
    (Valued.isClopen_ball (v.adicCompletion F) r.val).preimage (hj.continuous.sub continuous_const)
  have h1W : (1 : B.toSubgroup) ∈ W' := by
    change ν.restrict (j 1 - j 1) < r.val
    rw [sub_self, map_zero]
    exact pos_iff_ne_zero.mpr r.ne_zero
  obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW' h1W
  refine ⟨V.toSubgroup.map B.toSubgroup.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact B.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ V.isOpen
  · rw [Subgroup.coe_map]
    exact V.isClosed.isCompact.image continuous_subtype_val
  · rintro _ ⟨x, hx, rfl⟩
    exact hSsub (hr (hV hx))

/-- The preimage of a compact set of idele classes in the units of a finite completion is
compact, since the idele class norm restricts to the local norm. -/
private theorem explicitFormula_finiteClassMap_isCompact_preimage (v : Primes(F))
    {C : Set C[F]} (hC : IsCompact C) : IsCompact (finiteClassMap(v) ⁻¹' C) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let n : C[F] → ℝ := fun g ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hpos (g : C[F]) : 0 < n g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hnι (x : Kˣ) : n (finiteClassMap(v) x) = ‖x.val‖ := by
    simp only [n, ideleClassNorm_ofAdicCompletion]
    rfl
  obtain ⟨M₁, hM₁⟩ := hC.exists_bound_of_continuousOn hn.continuousOn
  obtain ⟨M₂, hM₂⟩ := hC.exists_bound_of_continuousOn
    (hn.inv₀ fun g ↦ (hpos g).ne').continuousOn
  let K₀ : Set K := {y | (max M₂ 1)⁻¹ ≤ ‖y‖ ∧ ‖y‖ ≤ M₁}
  have hK₀ : IsCompact K₀ := (isCompact_closedBall (0 : K) M₁).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    fun y hy ↦ mem_closedBall_zero_iff.mpr hy.2
  have hK₀r : K₀ ⊆ range (Units.val : Kˣ → K) := fun y hy ↦ by
    have hy0 : y ≠ 0 := fun h ↦ by
      have := hy.1
      rw [h, norm_zero] at this
      exact (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right M₂ 1))).not_ge this
    exact ⟨Units.mk0 y hy0, rfl⟩
  have hpre : IsCompact ((Units.val : Kˣ → K) ⁻¹' K₀) :=
    (Units.isEmbedding_val₀ (G₀ := K)).isInducing.isCompact_preimage' hK₀ hK₀r
  refine hpre.of_isClosed_subset (hC.isClosed.preimage (continuous_ideleClass_ofAdicCompletion F v))
    fun x hx ↦ ?_
  have h₁ := hM₁ _ hx
  have h₂ := hM₂ _ hx
  rw [Real.norm_eq_abs, abs_of_pos (hpos _), hnι] at h₁
  rw [Pi.inv_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos _)), hnι] at h₂
  have hx0 : 0 < ‖x.val‖ := norm_pos_iff.mpr x.ne_zero
  refine ⟨?_, h₁⟩
  rw [inv_le_comm₀ (lt_of_lt_of_le zero_lt_one (le_max_right M₂ 1)) hx0]
  exact h₂.trans (le_max_left M₂ 1)

/-- A good subgroup of a group receiving the units of a finite completion contains the image
of a compact open subgroup. -/
private theorem explicitFormula_finiteUnits_good (v : Primes(F)) {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (ι : (v.adicCompletion F)ˣ →* G) (hι : Continuous ι) (k : Subgroup G)
    (hk : IsBruhatGoodSubgroup k) :
    ∃ V : Subgroup (v.adicCompletion F)ˣ, IsOpen (V : Set (v.adicCompletion F)ˣ) ∧
      IsCompact (V : Set (v.adicCompletion F)ˣ) ∧ ∀ h ∈ V, ι h ∈ k := by
  obtain ⟨W, hW, hpow⟩ := explicitFormula_smallPowers k hk
  have hW' : ι ⁻¹' W ∈ 𝓝 1 := hι.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V, hVo, hVc, hVW⟩ := explicitFormula_finiteUnits_openSubgroup v hW'
  refine ⟨V, hVo, hVc, fun h hh ↦ hpow _ fun n ↦ ?_⟩
  rw [← map_pow]
  exact hVW (V.pow_mem hh n)

/-- On a fixed-support stage, restriction to the units of a finite completion factors
through finitely many point evaluations. -/
private theorem explicitFormula_finiteRestrict_stage (v : Primes(F)) {H : Type*} [CommGroup H]
    [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (ι : (v.adicCompletion F)ˣ →* H) (hι : Continuous ι)
    (hpre : ∀ C : Set H, IsCompact C → IsCompact (ι ⁻¹' C))
    (R : 𝒟(H) →ₗ[ℂ] 𝒟((v.adicCompletion F)ˣ)) (hR : ∀ f u, (R f).val u = f.val (ι u))
    (a : BruhatStructuralPair H) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts H) :
    Continuous (R ∘ bruhatCompactSupportStageInclusion a e C) := by
  let G := (v.adicCompletion F)ˣ
  have hk : IsBruhatGoodSubgroup (OrderDual.ofDual a.val.2) := a.property.2.2.1
  have hV := explicitFormula_finiteUnits_good v (ι)
    hι _ hk
  obtain ⟨V, hVo, hVc, hVk⟩ := hV
  let D := ι ⁻¹' (C : Set H)
  have hD : IsCompact D := hpre _ C.isCompact
  let : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hVo
  have hT : (QuotientGroup.mk '' D : Set (G ⧸ V)).Finite :=
    (hD.image QuotientGroup.continuous_mk).finite_of_discrete
  let T := hT.toFinset
  let Ψf (c : T → ℂ) (x : G) : ℂ := if h : (x : G ⧸ V) ∈ T then c ⟨_, h⟩ else 0
  have hΨ (c : T → ℂ) : Ψf c ∈ bruhatCompactSupportSubmodule G := by
    refine explicitFormula_mem_of_openSubgroup_invariant V hVo hVc _ (fun h hh x ↦ ?_) ?_
    · have hq : ((h * x : G) : G ⧸ V) = (x : G ⧸ V) :=
        QuotientGroup.eq.mpr (by simpa [mul_inv_rev] using V.inv_mem hh)
      simp only [Ψf, hq]
    · refine HasCompactSupport.intro (hD.mul hVc) fun x hx ↦ ?_
      refine dite_eq_right_iff.mpr fun hxT ↦ absurd ?_ hx
      obtain ⟨d, hd, hdx⟩ := hT.mem_toFinset.mp hxT
      exact Set.mem_mul.mpr ⟨d, hd, d⁻¹ * x, QuotientGroup.eq.mp hdx, mul_inv_cancel_left d x⟩
  let Ψ : (T → ℂ) →ₗ[ℂ] 𝒟(G) :=
    { toFun := fun c ↦ ⟨Ψf c, hΨ c⟩
      map_add' := fun c c' ↦ Subtype.ext (funext fun x ↦ by
        change Ψf (c + c') x = Ψf c x + Ψf c' x
        simp only [Ψf]
        split_ifs <;> simp)
      map_smul' := fun z c ↦ Subtype.ext (funext fun x ↦ by
        change Ψf (z • c) x = z * Ψf c x
        simp only [Ψf]
        split_ifs <;> simp) }
  let ev : bruhatCompactSupportStage a e C → (T → ℂ) := fun s t ↦
    schwartzBruhatStageRealization a e s.val (ι (Quotient.out t.val))
  have hev : Continuous ev := continuous_pi fun t ↦
    (continuous_schwartzBruhatStage_eval a e _).comp continuous_subtype_val
  let : ContinuousSMul ℂ 𝒟(G) := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
  have hΨc : Continuous Ψ := Ψ.continuous_of_finiteDimensional
  refine (hΨc.comp hev).congr fun s ↦ Subtype.ext (funext fun x ↦ ?_)
  refine Eq.trans ?_ (hR (bruhatCompactSupportStageInclusion a e C s) x).symm
  change Ψf (ev s) x = schwartzBruhatStageRealization a e s.val (ι x)
  simp only [Ψf]
  split_ifs with hx
  · let h := (QuotientGroup.mk_out_eq_mul V x).choose
    have hh : Quotient.out (x : G ⧸ V) = x * h := (QuotientGroup.mk_out_eq_mul V x).choose_spec
    have key : schwartzBruhatStageRealization a e s.val (ι (x * h)) =
        schwartzBruhatStageRealization a e s.val (ι x) := by
      rw [map_mul, mul_comm]
      exact stage_realization_mul_kernel a e s.val (hVk _ h.property) _
    exact (congrArg (fun y ↦ schwartzBruhatStageRealization a e s.val (ι y)) hh).trans key
  · have hxD : x ∉ D := fun h ↦ hx (hT.mem_toFinset.mpr ⟨x, h, rfl⟩)
    have hs : tsupport (schwartzBruhatStageRealization a e s.val) ⊆ (C : Set H) :=
      (mem_bruhatCompactSupportStage_iff a e C s.val).1 s.property
    exact (image_eq_zero_of_notMem_tsupport fun h ↦ hxD (hs h)).symm

/-- Neighbourhoods of one in the finite adeles contain the integers of all but finitely many
completions, inserted at their place. -/
private theorem explicitFormula_eventually_finiteAdele_mem (N : Set (FiniteAdeleRing (𝓞 F) F))
    (hN : N ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v : Primes(F) in cofinite, ∀ y ∈ v.adicCompletionIntegers F,
      FiniteAdeleRing.ofAdicCompletion F v y ∈ N := by
  classical
  let R := fun v : Primes(F) ↦ v.adicCompletion F
  let A := fun v : Primes(F) ↦ ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))
  have hAopen : ∀ v, IsOpen (A v) := fun v ↦ Valued.isOpen_valuationSubring _
  let s := RestrictedProduct.structureMap R A cofinite
  let x₁ : Π v, A v := fun v ↦ ⟨1, (v.adicCompletionIntegers F).one_mem⟩
  have hs1 : s x₁ = (1 : FiniteAdeleRing (𝓞 F) F) := rfl
  have hN' : s ⁻¹' N ∈ 𝓝 x₁ := by
    have h := RestrictedProduct.nhds_eq_map_structureMap hAopen x₁
    have hN₁ : N ∈ map (RestrictedProduct.structureMap (HeightOneSpectrum.adicCompletion F) A
        cofinite) (𝓝 x₁) := h ▸ hN
    exact hN₁
  rw [nhds_pi, Filter.mem_pi'] at hN'
  obtain ⟨I, t, ht, hsub⟩ := hN'
  filter_upwards [I.finite_toSet.compl_mem_cofinite] with v hv y hy
  have heq : FiniteAdeleRing.ofAdicCompletion F v y = s (Function.update x₁ v ⟨y, hy⟩) := by
    apply RestrictedProduct.ext
    intro w
    change RestrictedProduct.mulSingle _ v y w = (Function.update x₁ v ⟨y, hy⟩ w).val
    by_cases hw : w = v
    · subst hw
      rw [RestrictedProduct.mulSingle_eq_same, Function.update_self]
    · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hw, Function.update_of_ne hw]
  rw [heq]
  apply hsub
  intro w hw
  have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
  rw [Function.update_of_ne hwv]
  exact mem_of_mem_nhds (ht w)

/-- The images of the integer units of all but finitely many finite completions lie in a given
neighbourhood of one in the idele classes. -/
private theorem explicitFormula_eventually_units_mem (W : Set C[F]) (hW : W ∈ 𝓝 (1 : C[F])) :
    ∀ᶠ v : Primes(F) in cofinite, ∀ u ∈ (O(v)).units, finiteClassMap(v) u ∈ W := by
  let π : IdeleGroup (𝓞 F) F → C[F] := QuotientGroup.mk
  have h1 : π ⁻¹' W ∈ 𝓝 (1 : IdeleGroup (𝓞 F) F) :=
    QuotientGroup.continuous_mk.continuousAt.preimage_mem_nhds hW
  rw [Units.isInducing_embedProduct.nhds_eq_comap] at h1
  obtain ⟨N, hN, hNsub⟩ := mem_comap.mp h1
  let Ψ : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F →
      AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    fun p ↦ ((1, p.1), MulOpposite.op (1, p.2))
  have hΨ : Continuous Ψ := (continuous_const.prodMk continuous_fst).prodMk
    (MulOpposite.continuous_op.comp (continuous_const.prodMk continuous_snd))
  have h2 : Ψ ⁻¹' N ∈ 𝓝 ((1, 1) : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F) :=
    hΨ.continuousAt.preimage_mem_nhds hN
  obtain ⟨N₁, hN₁, N₂, hN₂, hprod⟩ := mem_nhds_prod_iff.mp h2
  filter_upwards [explicitFormula_eventually_finiteAdele_mem N₁ hN₁,
    explicitFormula_eventually_finiteAdele_mem N₂ hN₂] with v hv₁ hv₂ u hu
  apply hNsub
  exact hprod (Set.mk_mem_prod (hv₁ _ hu.1) (hv₂ _ hu.2))

/-- A unit of a finite completion outside the integer units has norm at least `q` or at
most `q⁻¹`. -/
private theorem explicitFormula_finiteUnits_norm_shell (v : Primes(F))
    (x : (v.adicCompletion F)ˣ) (hx : x ∉ (O(v)).units) : q(v) ≤ ‖x.val‖ ∨ ‖x.val‖ ≤ q(v)⁻¹ := by
  have hx0 : Valued.v x.val ≠ 0 := Valued.v.ne_zero_iff.mpr x.ne_zero
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hn : ‖x.val‖ = q(v) ^ WithZero.log (Valued.v x.val) := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hx0]
    simp
  have hne : WithZero.log (Valued.v x.val) ≠ 0 := by
    intro h
    apply hx
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      ← WithZero.exp_log hx0, h, WithZero.exp_zero]
  rw [hn]
  rcases lt_or_gt_of_ne hne with h | h
  · right
    calc q(v) ^ WithZero.log (Valued.v x.val) ≤ q(v) ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ hq.le (by omega)
      _ = q(v)⁻¹ := zpow_neg_one _
  · left
    calc q(v) = q(v) ^ (1 : ℤ) := (zpow_one _).symm
      _ ≤ q(v) ^ WithZero.log (Valued.v x.val) := zpow_le_zpow_right₀ hq.le (by omega)

/-- A linear map from a fixed-support stage to an elementary stage that is a pullback on
realizations is continuous, by the closed graph theorem. -/
private theorem explicitFormula_stage_continuous_of_realization {G H : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (a : BruhatStructuralPair H) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts H) (b : BruhatStructuralPair G)
    (d : ElementaryLCAPresentation b.quotient) (ι : G → H)
    (T : bruhatCompactSupportStage a e C →ₗ[ℂ] SchwartzBruhatStage d)
    (hkey : ∀ s x, schwartzBruhatStageRealization b d (T s) x =
      schwartzBruhatStageRealization a e s.val (ι x)) :
    Continuous T := by
  let X := bruhatCompactSupportStage a e C
  have hev (x : H) : Continuous (fun s : SchwartzBruhatStage e ↦ schwartzBruhatStageRealization a e s x) :=
    continuous_schwartzBruhatStage_eval a e x
  have hX : IsClosed (X : Set (SchwartzBruhatStage e)) := by
    simp only [X, bruhatCompactSupportStage, Submodule.coe_iInf]
    exact isClosed_iInter fun x ↦ isClosed_singleton.preimage (hev x.val)
  have hgraph : IsClosed (T.graph : Set (X × SchwartzBruhatStage d)) := by
    have heq : (T.graph : Set (X × SchwartzBruhatStage d)) = ⋂ x : G,
        {p | schwartzBruhatStageRealization b d p.2 x =
          schwartzBruhatStageRealization a e p.1.val (ι x)} := by
      ext p
      refine ⟨fun h ↦ mem_iInter.mpr fun x ↦ ?_, fun h ↦ ?_⟩
      · have h2 : p.2 = T p.1 := (LinearMap.mem_graph_iff _ _).mp h
        exact (congrArg (fun t ↦ schwartzBruhatStageRealization b d t x) h2).trans (hkey _ x)
      · exact (LinearMap.mem_graph_iff _ _).mpr (schwartzBruhatStageRealization_injective b d
          (funext fun x ↦ (mem_iInter.mp h x).trans (hkey _ x).symm))
    have hc : IsClosed (⋂ x : G, {p : X × SchwartzBruhatStage d |
        schwartzBruhatStageRealization b d p.2 x =
          schwartzBruhatStageRealization a e p.1.val (ι x)}) := by
      refine isClosed_iInter fun x ↦ isClosed_eq ?_ ?_
      · exact (continuous_schwartzBruhatStage_eval b d x).comp continuous_snd
      · exact (hev (ι x)).comp (continuous_subtype_val.comp continuous_fst)
    exact (congrArg IsClosed heq).mpr hc
  let : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
  have hFe : IsFrechetTVS (SchwartzBruhatStage e) := elementarySchwartz_isFrechet
  have hFd : IsFrechetTVS (SchwartzBruhatStage d) := elementarySchwartz_isFrechet
  exact weilTest_continuous_of_isClosed_graph (E := SchwartzBruhatStage e)
    (Y := SchwartzBruhatStage d) hFe hFd X hX T hgraph

/-- Restriction of test functions along a continuous homomorphism with compact preimages is
continuous on every fixed-support stage `(a, e, C)`. The restricted functions are invariant
under a good subgroup `k` with `ι k ≤ a.2`, vanish off the compact set `D = ι⁻¹ (C ∩ a.1)`, and
on the structural pair `(J, k)`, where `J` is generated by a compact neighbourhood of one inside
`ι⁻¹ a.1` together with `D` and `k`, they are the stage function composed with an elementary
homomorphism. -/
private theorem explicitFormula_restrict_stage {G H : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (ι : G →ₜ* H) (hpre : ∀ C : Set H, IsCompact C → IsCompact (ι ⁻¹' C))
    (R : 𝒟(H) →ₗ[ℂ] 𝒟(G)) (hR : ∀ f u, (R f).val u = f.val (ι u))
    (a : BruhatStructuralPair H) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts H) :
    Continuous (R ∘ bruhatCompactSupportStageInclusion a e C) := by
  obtain ⟨k, hk, hkι⟩ := exists_good_subgroup_image_in_kernel ι a
  let A : Subgroup G := a.val.1.comap ι.toMonoidHom
  have hAo : IsOpen (A : Set G) := a.property.1.preimage ι.continuous
  have hkA : k ≤ A := fun x hx ↦ a.property.2.2.2 (hkι ⟨x, hx, rfl⟩)
  let D : Set G := ι ⁻¹' ((C : Set H) ∩ a.val.1)
  have hD : IsCompact D :=
    hpre _ (C.isCompact.inter_right (a.val.1.isClosed_of_isOpen a.property.1))
  have hDA : D ⊆ A := fun x hx ↦ hx.2
  have hAmem : ∀ x, x ∈ A → ι x ∈ a.val.1 := fun _ h ↦ h
  clear_value A
  have h1A : (1 : G) ∈ (A : Set G) := A.one_mem
  have hAn := hAo.mem_nhds h1A
  have hUex := local_compact_nhds hAn
  obtain ⟨U, hU1, hUA, hU⟩ := hUex
  let Kg : Set G := U ∪ D ∪ (k : Set G)
  have hKg : IsCompact Kg := (hU.union hD).union hk.isCompact
  have hKg1 : Kg ∈ 𝓝 (1 : G) :=
    mem_of_superset hU1 (subset_union_left.trans subset_union_left)
  let J := Subgroup.closure Kg
  have hJo : IsOpen (J : Set G) := J.isOpen_of_mem_nhds (mem_of_superset hKg1 Subgroup.subset_closure)
  have hJA : J ≤ A := (Subgroup.closure_le _).mpr (union_subset (union_subset hUA hDA) hkA)
  have hJcg : IsCompactlyGeneratedGroup J :=
    ⟨Subtype.val ⁻¹' Kg, continuous_subtype_val.continuousAt.preimage_mem_nhds hKg1,
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKg
        (Subtype.range_coe.symm ▸ Subgroup.subset_closure),
      Subgroup.closure_preimage_eq_top _⟩
  let b : BruhatStructuralPair G :=
    ⟨(J, OrderDual.toDual k), hJo, hJcg, hk, fun x hx ↦ Subgroup.subset_closure (Or.inr hx)⟩
  let d := (BruhatStructuralPair.elementary b).some
  let i : b.val.1 →* a.val.1 :=
    (ι.toMonoidHom.comp b.val.1.subtype).codRestrict _ fun x ↦ hAmem _ (hJA x.property)
  have hi : Continuous i := (ι.continuous.comp continuous_subtype_val).subtype_mk _
  let j : b.quotient →* a.quotient := QuotientGroup.map _ _ i (fun x hx ↦ by
    change ι x.val ∈ OrderDual.ofDual a.val.2
    exact hkι ⟨x.val, hx, rfl⟩)
  have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hi)
  let L := AddMonoidHom.toMultiplicative.symm
    (e.equiv.toMulEquiv.toMonoidHom.comp (j.comp d.equiv.symm.toMulEquiv.toMonoidHom))
  have hL : Continuous L := e.equiv.continuous.comp (hj.comp d.equiv.symm.continuous)
  have hL' (q : b.quotient) :
      L (Multiplicative.toAdd (d.equiv q)) = Multiplicative.toAdd (e.equiv (j q)) := by
    exact congrArg (fun z ↦ Multiplicative.toAdd (e.equiv (j z))) (d.equiv.symm_apply_apply q)
  let X := bruhatCompactSupportStage a e C
  have hsupp (s : X) (x : G) (hx : schwartzBruhatStageRealization a e s.val (ι x) ≠ 0) :
      x ∈ D := by
    refine ⟨(mem_bruhatCompactSupportStage_iff a e C s.val).1 s.property (subset_tsupport _ hx),
      ?_⟩
    by_contra h
    have h' : ι x ∉ a.val.1 := h
    rw [schwartzBruhatStageRealization_apply] at hx
    split_ifs at hx
    exact hx rfl
  have hval (s : SchwartzBruhatStage e) (x : b.val.1) :
      s (L (Multiplicative.toAdd (d.equiv (QuotientGroup.mk x : b.quotient)))) =
        schwartzBruhatStageRealization a e s (ι x.val) := by
    have hx : ι x.val ∈ a.val.1 := hAmem _ (hJA x.property)
    refine (congrArg (fun y ↦ s y) (hL' _)).trans ?_
    rw [schwartzBruhatStageRealization_apply]
    split_ifs
    rfl
  have hJc : IsCompact (Subtype.val ⁻¹' D : Set b.val.1) :=
    (J.isClosed_of_isOpen hJo).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  let φ : b.val.1 → ElementaryLieGroup d.realDim d.torusDim d.latticeRank d.finiteFactor :=
    fun x ↦ Multiplicative.toAdd (d.equiv (QuotientGroup.mk x : b.quotient))
  have hφ : Continuous φ := d.equiv.continuous.comp QuotientGroup.continuous_mk
  have hmem (s : X) : (fun y ↦ s.val (L y)) ∈ elementarySchwartzSubmodule d.realDim d.torusDim
      d.latticeRank d.finiteFactor := by
    refine elementarySchwartz_of_compactSupport (fun z c ↦ ?_) ?_
    · exact contDiff_comp_elementaryHom L hL (f := s.val) s.val.property.1 z c
    · refine HasCompactSupport.intro (hJc.image hφ) fun y hy ↦ ?_
      have hq0 := d.equiv.surjective (Multiplicative.ofAdd y)
      obtain ⟨q, hq⟩ := hq0
      have hx0 := QuotientGroup.mk_surjective q
      obtain ⟨x, rfl⟩ := hx0
      have hy' : y = φ x := (congrArg Multiplicative.toAdd hq).symm
      subst hy'
      rw [hval]
      by_contra h
      exact hy ⟨x, hsupp s x.val h, rfl⟩
  let T : X →ₗ[ℂ] SchwartzBruhatStage d :=
    { toFun := fun s ↦ ⟨fun y ↦ s.val (L y), hmem s⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hkey (s : X) (x : G) :
      schwartzBruhatStageRealization b d (T s) x = schwartzBruhatStageRealization a e s.val (ι x) := by
    refine (schwartzBruhatStageRealization_apply b d (T s) x).trans ?_
    split_ifs with hx
    · exact hval s.val ⟨x, hx⟩
    · by_contra h
      exact hx (Subgroup.subset_closure (Or.inl (Or.inr (hsupp s x (Ne.symm h)))))
  let K : TopologicalSpace.Compacts G := ⟨D, hD⟩
  have hTK (s : X) : T s ∈ bruhatCompactSupportStage b d K := by
    refine (mem_bruhatCompactSupportStage_iff b d K _).2 (closure_minimal (fun x hx ↦ ?_)
      hD.isClosed)
    rw [Function.mem_support, hkey] at hx
    exact hsupp s x hx
  have hT : Continuous T := explicitFormula_stage_continuous_of_realization a e C b d ι T hkey
  let i' : bruhatCompactSupportStage b d K →ₗ[ℂ] 𝒟(G) := bruhatCompactSupportStageInclusion b d K
  have hi' : Continuous i' :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp i' fun p ↦ p.2 b d K
  refine (hi'.comp (hT.subtype_mk hTK)).congr fun s ↦ Subtype.ext (funext fun x ↦ ?_)
  refine Eq.trans ?_ (hR (bruhatCompactSupportStageInclusion a e C s) x).symm
  exact hkey s x

end ExplicitFormulaTestMaps

-- TODO(paper-gap): The printed sum omits zero multiplicity. In (B.4.4.16)
-- the corrected archimedean Fourier pairing is already canonically normalized.
-- The proof on p. 625 also needs the norm-one volume divisor in D(φ) and
-- a comparison of the Mellin local terms with the principal values (footnote 27).
-- For (B.4.4.22), compact norm support handles nonunit shells at large primes.
-- Invariance under the local units at almost every prime makes the unit-shell test constant.

/-- Paper: Theorem B.4.4.7, p. 626. Restriction along the closed embedding of the
units of a finite completion into the idele classes is a continuous linear map of
compactly supported test spaces. -/
theorem idelicExplicitFormula_finiteTestMap (v : Primes(F)) :
    ∃ R : 𝒟(C[F]) →L[ℂ] 𝒟((v.adicCompletion F)ˣ),
      ∀ (f : 𝒟(C[F])) (u : (v.adicCompletion F)ˣ), (R f).val u = f.val (finiteClassMap(v) u) := by
  let G := (v.adicCompletion F)ˣ
  let ι := finiteClassMap(v)
  have hgood := explicitFormula_finiteUnits_good v (G := C[F]) ι
    (continuous_ideleClass_ofAdicCompletion F v)
  have hmem (f : 𝒟(C[F])) : f.val ∘ ι ∈ bruhatCompactSupportSubmodule G := by
    obtain ⟨k, hk, hinv, _⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 0
    obtain ⟨V, hVo, hVc, hVk⟩ := hgood k hk
    refine explicitFormula_mem_of_openSubgroup_invariant V hVo hVc _ (fun h hh x ↦ ?_) ?_
    · change f.val (ι (h * x)) = f.val (ι x)
      rw [map_mul]
      exact hinv ⟨_, hVk h hh⟩ _
    · exact HasCompactSupport.intro (explicitFormula_finiteClassMap_isCompact_preimage v
        f.property.2) fun x hx ↦
        show f.val (ι x) = 0 from image_eq_zero_of_notMem_tsupport hx
  let R : 𝒟(C[F]) →ₗ[ℂ] 𝒟(G) :=
    { toFun := fun f ↦ ⟨f.val ∘ ι, hmem f⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hstage := explicitFormula_finiteRestrict_stage v (H := C[F]) ι
    (continuous_ideleClass_ofAdicCompletion F v)
    (fun _ hC ↦ explicitFormula_finiteClassMap_isCompact_preimage v hC) R fun _ _ ↦ rfl
  let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule C[F]) //
    ∀ (a : BruhatStructuralPair C[F]) (e : ElementaryLCAPresentation a.quotient)
      (C : TopologicalSpace.Compacts C[F]),
      Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
  have hR : Continuous R :=
    (PolynormableSpace.withSeminorms ℂ 𝒟(G)).continuous_of_continuous_comp R fun p ↦
      (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
        (⟨p.val.comp R, fun a e C ↦ p.property.comp (hstage a e C)⟩ : P)
  exact ⟨⟨R, hR⟩, fun _ _ ↦ rfl⟩

/-- The units of an archimedean completion embed properly into the idele classes: the class
norm restricts to a power of the local norm, which is proper on the units. -/
private theorem explicitFormula_infiniteClassMap_isCompact_preimage (w : InfinitePlace F)
    {C : Set C[F]} (hC : IsCompact C) : IsCompact (infiniteClassMap(w) ⁻¹' C) := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion :=
    LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  have hp := isProperMap_units_nnNorm_pow (K := w.Completion) w.mult w.mult_ne_zero
  have hN : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  refine (hp.isCompact_preimage (hC.image hN)).of_isClosed_subset
    (hC.isClosed.preimage (continuous_ideleClass_ofCompletion F w)) fun x hx ↦ ?_
  refine ⟨_, hx, ?_⟩
  rw [ideleClassNorm_ofCompletion]
  rfl

/-- Pullback of a Bruhat `Cᵖ` function along a continuous homomorphism is Bruhat `Cᵖ`: the
good subgroup is pulled back, and on each structural quotient the induced homomorphism of
elementary groups is affine on the covers (`contDiff_comp_elementaryHom`). -/
private theorem explicitFormula_isBruhatContDiff_comp {G H : Type*} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [T2Space G] [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H]
    (ι : G →ₜ* H) {p : ℕ} {f : H → ℂ} (hf : IsBruhatContDiff p f) :
    IsBruhatContDiff p (f ∘ ι) := by
  obtain ⟨k, hk, hinv, hdesc⟩ := hf
  have hkc : IsCompact (k : Set H) := hk.isCompact
  obtain ⟨J₀, hkJ₀⟩ := exists_openCompactlyGeneratedSubgroup_contains hkc
  let b₀ : BruhatStructuralPair H :=
    ⟨(J₀.val, OrderDual.toDual k), J₀.property.1, J₀.property.2, hk, hkJ₀⟩
  obtain ⟨k', hk', hk'k⟩ := exists_good_subgroup_image_in_kernel ι b₀
  have hιk (h : G) (hh : h ∈ k') : ι h ∈ k := hk'k ⟨h, hh, rfl⟩
  refine ⟨k', hk', fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · change f (ι (h.val * x)) = f (ι x)
    rw [map_mul]
    exact hinv ⟨_, hιk h.val h.property⟩ _
  obtain ⟨U, -, hUc, hUgen⟩ := a.property.2.1
  have hc : IsCompact ((fun u : a.val.1 ↦ ι u.val) '' U ∪ (k : Set H)) :=
    (hUc.image (ι.continuous.comp continuous_subtype_val)).union hkc
  obtain ⟨J, hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains hc
  let b : BruhatStructuralPair H :=
    ⟨(J.val, OrderDual.toDual k), J.property.1, J.property.2, hk,
      fun x hx ↦ hJ (Or.inr hx)⟩
  have haJ : a.val.1.map ι.toMonoidHom ≤ J.val := by
    have : (Subgroup.closure U).map (ι.toMonoidHom.comp a.val.1.subtype) ≤ J.val := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨u, hu, rfl⟩
      exact hJ (Or.inl ⟨u, hu, rfl⟩)
    rw [hUgen, Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype] at this
    exact this
  let i : a.val.1 →* b.val.1 :=
    (ι.toMonoidHom.comp a.val.1.subtype).codRestrict _ fun x ↦ haJ ⟨x.val, x.property, rfl⟩
  have hi : Continuous i := (ι.continuous.comp continuous_subtype_val).subtype_mk _
  let j : a.quotient →* b.quotient := QuotientGroup.map _ _ i (fun x hx ↦ by
    change ι x.val ∈ k
    exact hιk _ (ha ▸ hx))
  have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hi)
  obtain ⟨f₀, hf₀, hSmooth⟩ := hdesc b rfl
  refine ⟨f₀ ∘ j, fun x ↦ hf₀ (i x), fun e z d ↦ ?_⟩
  obtain ⟨e'⟩ := b.elementary
  let L := AddMonoidHom.toMultiplicative.symm
    (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
  have hL : Continuous L := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
  have hs := contDiff_comp_elementaryHom L hL
    (f := fun y ↦ f₀ (e'.equiv.symm (Multiplicative.ofAdd y))) (hSmooth e') z d
  convert hs using 1
  funext u
  change f₀ (j (e.equiv.symm _)) = f₀ (e'.equiv.symm (e'.equiv (j (e.equiv.symm _))))
  rw [e'.equiv.symm_apply_apply]

/-- Paper: Theorem B.4.4.7, p. 626. Restriction of test functions along a continuous
homomorphism with compact preimages out of the units of an archimedean completion is
continuous on every fixed-support stage `(a, e, C)` of `H`. The restricted functions are
invariant under one good subgroup `k'` with `ι k' ≤ a.2`, vanish off the compact set
`ι⁻¹ (C ∩ a.1)`, and descend to the elementary quotient of a structural pair `(J, k')` with
`J ≤ ι⁻¹ a.1`, where the descent is the stage function composed with an elementary
homomorphism. So the restriction factors through one stage of `𝒟(w.Completionˣ)`, and
continuity into that Fréchet stage follows from the closed graph theorem, since point
evaluations are continuous on both stages. -/
theorem bruhatCompactSupport_infiniteRestrict_stage (w : InfinitePlace F) {H : Type*}
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (ι : w.Completionˣ →* H) (_hι : Continuous ι)
    (_hpre : ∀ C : Set H, IsCompact C → IsCompact (ι ⁻¹' C))
    (R : 𝒟(H) →ₗ[ℂ] 𝒟(w.Completionˣ)) (_hR : ∀ f u, (R f).val u = f.val (ι u))
    (a : BruhatStructuralPair H) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts H) :
    Continuous (R ∘ bruhatCompactSupportStageInclusion a e C) :=
  explicitFormula_restrict_stage ⟨ι, _hι⟩ _hpre R _hR a e C

/-- Paper: Theorem B.4.4.7, p. 626. Restriction along the closed embedding of the
units of an archimedean completion into the idele classes is a continuous linear map of
compactly supported test spaces. -/
theorem idelicExplicitFormula_infiniteTestMap (w : InfinitePlace F) :
    ∃ R : 𝒟(C[F]) →L[ℂ] 𝒟(w.Completionˣ),
      ∀ (f : 𝒟(C[F])) (u : w.Completionˣ), (R f).val u = f.val (infiniteClassMap(w) u) := by
  let G := w.Completionˣ
  let ι := infiniteClassMap(w)
  have hmem (f : 𝒟(C[F])) : f.val ∘ ι ∈ bruhatCompactSupportSubmodule G :=
    ⟨(mem_bruhatSmoothSubmodule_iff _).2 fun p ↦ explicitFormula_isBruhatContDiff_comp
        ⟨ι, continuous_ideleClass_ofCompletion F w⟩
        ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1 p),
      HasCompactSupport.intro (explicitFormula_infiniteClassMap_isCompact_preimage w
        f.property.2) fun x hx ↦ show f.val (ι x) = 0 from image_eq_zero_of_notMem_tsupport hx⟩
  let R : 𝒟(C[F]) →ₗ[ℂ] 𝒟(G) :=
    { toFun := fun f ↦ ⟨f.val ∘ ι, hmem f⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hstage := bruhatCompactSupport_infiniteRestrict_stage w (H := C[F]) ι
    (continuous_ideleClass_ofCompletion F w)
    (fun _ hC ↦ explicitFormula_infiniteClassMap_isCompact_preimage w hC) R fun _ _ ↦ rfl
  let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule C[F]) //
    ∀ (a : BruhatStructuralPair C[F]) (e : ElementaryLCAPresentation a.quotient)
      (C : TopologicalSpace.Compacts C[F]),
      Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
  have hR : Continuous R :=
    (PolynormableSpace.withSeminorms ℂ 𝒟(G)).continuous_of_continuous_comp R fun p ↦
      (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
        (⟨p.val.comp R, fun a e C ↦ p.property.comp (hstage a e C)⟩ : P)
  exact ⟨⟨R, hR⟩, fun _ _ ↦ rfl⟩

/-- Paper: Theorem B.4.4.7, p. 626. Integration against a continuous function on the
idele classes is a continuous linear functional on the compactly supported test space. -/
theorem idelicExplicitFormula_integralDistribution (c : C[F] → ℂ) (_hc : Continuous c) :
    ∃ D : StrongDual ℂ (𝒟(C[F])), ∀ f : 𝒟(C[F]), D f = ∫ g, f.val g * c g ∂classMeasure := by
  let G := C[F]
  let : BorelSpace G := ⟨rfl⟩
  let : (classMeasure).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hint (f : 𝒟(G)) : Integrable (fun g ↦ f.val g * c g) classMeasure :=
    ((explicitTest_continuous f).mul _hc).integrable_of_hasCompactSupport f.property.2.mul_right
  let D : 𝒟(G) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ g, f.val g * c g ∂classMeasure
      map_add' := fun f f' ↦ by
        rw [← integral_add (hint f) (hint f')]
        exact integral_congr_ae (.of_forall fun g ↦ add_mul (f.val g) (f'.val g) (c g))
      map_smul' := fun z f ↦ by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (.of_forall fun g ↦ mul_assoc z (f.val g) (c g)) }
  let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : TopologicalSpace.Compacts G), Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
  have hD : Continuous D := (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp D fun _ ↦
    (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
      (⟨(normSeminorm ℂ ℂ).comp D, fun a e C ↦ continuous_norm.comp
        (explicitStage_integral_continuous classMeasure c _hc a e C)⟩ : P)
  exact ⟨⟨D, hD⟩, fun _ ↦ rfl⟩

/-- Paper: Lemma B.4.4.9, pp. 624–625. The zeros of the completed Hecke L-function of a
unitary character lie in the closed critical strip `0 ≤ Re s ≤ 1`: the Euler product does not
vanish for `Re s > 1`, and the functional equation reflects this to `Re s < 0`. -/
theorem explicitFormulaCompletedHeckeL_zero_re_mem (χ : U[F]) {s : ℂ}
    (_hs : 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ s) :
    s.re ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hL, hAgree⟩ := explicitFormulaCompletedHeckeL_spec χ
  refine hasSum_heckeAsymptoticResidue_re_mem χ _ hL hAgree s fun h0 ↦ ?_
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ s), h0] at _hs
  exact lt_irrefl _ _hs

section ExplicitFormulaZeroCount

/-! Copied from `RiemannMasullo/ForMathlib/Analysis/Meromorphic/VerticalStripZeros.lean`
(Jensen's inequality on discs counts zeros in a vertical strip), which this file does not
import. -/

open Metric
open scoped Asymptotics

local notation "ezAtAbsTop" => comap (abs : ℝ → ℝ) atTop
local notation "ezAtHeight" => comap (abs ∘ Complex.im) atTop
local notation "ezStripGrowth(" f ")" =>
  ∀ a b : ℝ, a < b → ∃ M : ℝ, 0 < M ∧
    (f : ℂ → ℂ) =O[ezAtHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z : ℂ ↦ |Complex.im z| ^ M
local notation "ezInverseGrowth(" f ", " σ ", " k ")" =>
  (fun t : ℝ ↦ ((f : ℂ → ℂ) ⟨σ, t⟩)⁻¹) =O[ezAtAbsTop] (fun t ↦ |t| ^ (k : ℕ))
local notation "ezWindowZeros(" f ", " b ", " a ")" =>
  {z : ℂ // 0 < MeromorphicOn.divisor (f : ℂ → ℂ) univ z ∧ |Complex.re z - (b : ℝ)| < (a : ℝ)}

/-- A square-root bound on the total weight in each unit height range gives a summable inverse-
square weight. -/
private theorem explicitZeroCount_summable_zeroWeights_of_bins {ι : Type*}
    (h m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (C : ℝ)
    (hcount : ∀ (n : ℕ) (S : Finset ι), (∀ i ∈ S, ⌊|h i|⌋₊ = n) →
      ∑ i ∈ S, m i ≤ C * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) :
    Summable (fun i ↦ m i / (1 + |h i|) ^ 2) := by
  classical
  let b (i : ι) := ⌊|h i|⌋₊
  let u (n : ℕ) := C / ((n : ℝ) + 1) ^ (3 / 2 : ℝ)
  have hu : Summable u := by
    have h := ((Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)).mul_left C
    simpa [u, abs_of_nonneg, add_nonneg, div_eq_mul_inv] using h
  have hC : 0 ≤ C := by simpa using hcount 0 ∅ (by simp)
  apply summable_of_sum_le (c := ∑' n, u n) (fun i ↦ div_nonneg (hm i) (sq_nonneg _))
  intro S
  have hf (n : ℕ) : ∑ i ∈ S with b i = n, m i / (1 + |h i|) ^ 2 ≤ u n := by
    let T := S.filter (fun i ↦ b i = n)
    have ht : ∀ i ∈ T, ⌊|h i|⌋₊ = n := fun i hi ↦ (Finset.mem_filter.mp hi).2
    have hn : 0 < (n : ℝ) + 1 := by positivity
    calc
      _ ≤ ∑ i ∈ T, m i / ((n : ℝ) + 1)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have he : b i = n := (Finset.mem_filter.mp hi).2
        have hle : (n : ℝ) ≤ |h i| := he ▸ Nat.floor_le (abs_nonneg _)
        exact div_le_div_of_nonneg_left (hm i) (sq_pos_of_pos hn)
          (pow_le_pow_left₀ hn.le (by linarith) 2)
      _ = (∑ i ∈ T, m i) / ((n : ℝ) + 1)^2 := by simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ C * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) / ((n : ℝ) + 1)^2 :=
        div_le_div_of_nonneg_right (hcount n T ht) (sq_nonneg _)
      _ = u n := by
        rw [show (((n : ℝ) + 1)^2) = ((n : ℝ) + 1)^(2 : ℝ) from (Real.rpow_two _).symm,
          mul_div_assoc, ← Real.rpow_sub hn, show (1 : ℝ)/2-2 = -(3/2) by norm_num, Real.rpow_neg hn.le]
        rfl
  calc
    _ = ∑ n ∈ S.image b, ∑ i ∈ S with b i = n, m i / (1 + |h i|) ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_image_of_mem b hi) _).symm
    _ ≤ ∑ n ∈ S.image b, u n := Finset.sum_le_sum (fun n _ ↦ hf n)
    _ ≤ ∑' n, u n := hu.sum_le_tsum _ fun _ _ ↦ div_nonneg hC (Real.rpow_nonneg (by positivity) _)

/-- Jensen’s inequality bounds the sum of orders on any finite subset of the smaller disc. -/
private theorem explicitZeroCount_disk_sum {f : ℂ → ℂ} {c : ℂ} {r R B : ℝ}
    (hr : 0 < r) (hrR : r < R) (ha : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hB : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c r) :
    ∑ z ∈ S, (analyticOrderNatAt f z : ℝ) ≤ Real.log B / Real.log (R / r) := by
  classical
  let W := {z : ℂ | z ∈ closedBall c r ∧ f z = 0}
  have hW : W.Finite := finite_zeros_closedBall hr.le (ha.mono (closedBall_subset_closedBall hrR.le)) hc
  let points := hW.toFinset ∪ S
  have heq : ∑ᶠ z ∈ closedBall c r, (analyticOrderNatAt f z : ℝ) = ∑ z ∈ points, (analyticOrderNatAt f z : ℝ) := by
    rw [← finsum_mem_coe_finset]
    apply finsum_mem_inter_support_eq'
    intro z hz
    have hzero : f z = 0 := by
      by_contra hne
      exact hz (by simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hne)])
    change z ∈ closedBall c r ↔ z ∈ points
    refine ⟨fun h ↦ Finset.mem_union_left _ (hW.mem_toFinset.mpr ⟨h, hzero⟩), ?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (hW.mem_toFinset.mp h).1
    · exact hS z h
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right (s₁ := hW.toFinset))
    (fun _ _ _ ↦ Nat.cast_nonneg _)) ?_
  rw [← heq]
  exact landau_sum_analyticOrderNatAt_le hr hrR ha hc hB

/-- An upper bound on meromorphic order gives the same bound on the completed divisor at each
point of the disc. -/
private theorem explicitZeroCount_local_order {L Λ : ℂ → ℂ} (hΛ : MeromorphicOn Λ univ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : AnalyticOnNhd ℂ L (closedBall c R)) (hc : L c ≠ 0)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z) {z : ℂ} (hz : z ∈ closedBall c R) :
    (MeromorphicOn.divisor Λ univ z : ℝ) ≤ analyticOrderNatAt L z := by
  have hbase : analyticOrderAt L c ≠ ⊤ := by
    rw [(ha c (mem_closedBall_self hR)).analyticOrderAt_eq_zero.mpr hc]
    simp
  have hf := ha.analyticOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected (mem_closedBall_self hR) hz hbase
  have ho : meromorphicOrderAt L z = ((analyticOrderNatAt L z : ℤ) : WithTop ℤ) := by
    rw [(ha z hz).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hf, ENat.map_natCast]
  rw [MeromorphicOn.divisor_apply hΛ (mem_univ _)]
  have h := hcmp z
  rw [ho] at h
  have : (meromorphicOrderAt Λ z).untop₀ ≤ (analyticOrderNatAt L z : ℤ) := by
    simpa using WithTop.untop₀_le_untop₀ (WithTop.coe_ne_top : ((analyticOrderNatAt L z : ℤ) : WithTop ℤ) ≠ ⊤) h
  exact_mod_cast this

private theorem explicitZeroCount_compact {f : ℂ → ℂ} (K : Set ℂ) (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ MeromorphicOn.divisor f univ z ≠ 0}.Finite := by
  let D := MeromorphicOn.divisor f univ
  have h := (D.restrict (subset_univ K)).finiteSupport hK
  apply h.subset
  intro z hz
  change (D.restrict (subset_univ K)) z ≠ 0
  simpa [locallyFinsuppWithin.restrict, hz.1, D] using hz.2

/-- Polynomial growth in a slightly wider strip rules out poles at sufficiently large absolute
height. -/
private theorem explicitZeroCount_polynomial_strip {L : ℂ → ℂ} (σ : ℝ) (hL : MeromorphicNFOn L univ)
    (hGrowth : ezStripGrowth(L)) (R : ℝ) (hR : 0 < R) :
    ∃ C M T : ℝ, 0 < C ∧ 0 < M ∧ ∀ z : ℂ, |z.re - σ| ≤ R → T < |z.im| →
      AnalyticAt ℂ L z ∧ ‖L z‖ ≤ C * |z.im| ^ M := by
  let a := σ - R - 1
  let b := σ + R + 1
  obtain ⟨M, hM, hg⟩ := hGrowth a b (by dsimp [a, b]; linarith)
  obtain ⟨C, hC, hg⟩ := Asymptotics.isBigO_iff'.mp hg
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hg
  obtain ⟨T, hT⟩ := hg
  have hB (z : ℂ) (hz : z.re ∈ Icc a b) (ht : T ≤ |z.im|) :
      ‖L z‖ ≤ C * |z.im| ^ M := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hT _ ht z rfl hz
  refine ⟨C, M, T, hC, hM, fun z hz ht ↦ ⟨?_, hB _ ⟨?_, ?_⟩ ht.le⟩⟩ <;>
    try first | (dsimp [a, b]; linarith [(abs_le.mp hz).1, (abs_le.mp hz).2])
  apply (hL (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  have hr : z.re ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
  have him : Continuous (fun u : ℂ ↦ |u.im|) := Complex.continuous_im.abs
  have hn₁ := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hr
  have hn₂ : ∀ᶠ u : ℂ in 𝓝 z, |u.im| ∈ Ioo T (|z.im| + 1) :=
    (isOpen_Ioo.preimage him).mem_nhds ⟨ht, by linarith⟩
  have hbnd : ∀ᶠ u : ℂ in 𝓝 z, ‖L u‖ ≤ C * (|z.im| + 1) ^ M := by
    filter_upwards [hn₁, hn₂] with u hu hv
    exact (hB u ⟨hu.1.le, hu.2.le⟩ hv.1.le).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hv.2.le hM.le) hC.le)
  have hinf := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop (C * (|z.im| + 1) ^ M)
  obtain ⟨u, hu, hv⟩ := ((hbnd.filter_mono nhdsWithin_le_nhds).and hinf).exists
  exact (not_lt_of_ge hu) hv

/-- The reciprocal estimate on the center line bounds the normalizing factor in Jensen’s
inequality. -/
private theorem explicitZeroCount_center_bound {L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hne : ∀ᶠ t : ℝ in ezAtAbsTop, L ⟨σ, t⟩ ≠ 0) (hinv : ezInverseGrowth(L, σ, k)) :
    ∃ D T : ℝ, ∃ k : ℕ, 0 < D ∧ ∀ t : ℝ, T ≤ |t| →
      L ⟨σ, t⟩ ≠ 0 ∧ ‖(L ⟨σ, t⟩)⁻¹‖ ≤ D * |t| ^ k := by
  obtain ⟨D, hD, hb⟩ := Asymptotics.isBigO_iff'.mp hinv
  have h := hne.and hb
  rw [eventually_comap, eventually_atTop] at h
  obtain ⟨T, hT⟩ := h
  refine ⟨D, T, k, hD, fun t ht ↦ ⟨(hT _ ht t rfl).1, ?_⟩⟩
  simpa using (hT _ ht t rfl).2

/-- A fixed-radius disc centered at `σ + it` has a polynomial bound relative to its center value,
uniformly at large absolute height. -/
private theorem explicitZeroCount_disk_growth {L : ℂ → ℂ} {σ : ℝ} {k : ℕ} (hL : MeromorphicNFOn L univ)
    (hGrowth : ezStripGrowth(L)) (hne : ∀ᶠ t : ℝ in ezAtAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : ezInverseGrowth(L, σ, k)) (R : ℝ) (hR : 0 < R) :
    ∃ B E T : ℝ, 0 < B ∧ 0 ≤ E ∧ ∀ t : ℝ, T ≤ |t| →
      let c : ℂ := ⟨σ, t⟩
      AnalyticOnNhd ℂ L (Metric.closedBall c R) ∧ L c ≠ 0 ∧
        ∀ z ∈ Metric.closedBall c R, ‖L z / L c‖ ≤ B * (1 + |t|) ^ E := by
  obtain ⟨C, M, T, hC, hM, hg⟩ := explicitZeroCount_polynomial_strip σ hL hGrowth R hR
  obtain ⟨D, T', k, hD, hd⟩ := explicitZeroCount_center_bound hne hinv
  let windowFactor := (1 + R) ^ M
  refine ⟨C * windowFactor * D, M + k, max (T + R + 1) T', mul_pos (mul_pos hC ?_) hD, by positivity, ?_⟩
  · exact Real.rpow_pos_of_pos (by linarith) _
  intro t ht c
  obtain ⟨hc, hci⟩ := hd t ((le_max_right _ _).trans ht)
  have hpoints {z : ℂ} (hz : z ∈ Metric.closedBall c R) :
      |z.re - σ| ≤ R ∧ T < |z.im| ∧ |z.im| ≤ (1 + R) * (1 + |t|) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre := (Complex.abs_re_le_norm (z - c)).trans hz
    have him := (Complex.abs_im_le_norm (z - c)).trans hz
    change |z.re - σ| ≤ R at hre
    change |z.im - t| ≤ R at him
    have hdiff := (abs_abs_sub_abs_le_abs_sub z.im t).trans him
    have ht' := (le_max_left _ T').trans ht
    refine ⟨hre, by linarith [(abs_le.mp hdiff).1], ?_⟩
    nlinarith [(abs_le.mp hdiff).2, mul_nonneg hR.le (abs_nonneg t)]
  refine ⟨fun z hz ↦ (hg z (hpoints hz).1 (hpoints hz).2.1).1, hc, fun z hz ↦ ?_⟩
  have h1 : 0 < 1 + |t| := by positivity
  have hV : 0 < windowFactor := Real.rpow_pos_of_pos (by linarith) _
  have hu := (hg z (hpoints hz).1 (hpoints hz).2.1).2
  have hv : |z.im| ^ M ≤ windowFactor * (1 + |t|) ^ M := by
    rw [← Real.mul_rpow (by linarith : 0 ≤ 1 + R) h1.le]
    exact Real.rpow_le_rpow (abs_nonneg _) (hpoints hz).2.2 hM.le
  have hi : ‖(L c)⁻¹‖ ≤ D * (1 + |t|) ^ k := hci.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (by linarith) k) hD.le)
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add h1, Real.rpow_natCast]
  calc
    _ ≤ (C * (windowFactor * (1 + |t|)^M)) * (D * (1 + |t|)^k) :=
      mul_le_mul (hu.trans (mul_le_mul_of_nonneg_left hv hC.le)) hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The logarithm in Jensen’s inequality is bounded by a constant times the square root of the
height. -/
private theorem explicitZeroCount_log_bound (B E r R : ℝ) (hB : 0 < B) (hE : 0 ≤ E)
    (hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 1 ≤ u →
      Real.log (B * u ^ E) / Real.log (R / r) ≤ K * u ^ (1 / 2 : ℝ) := by
  let D := Real.log (R / r)
  have hD : 0 < D := Real.log_pos ((one_lt_div hr).mpr hrR)
  refine ⟨(max (Real.log B) 0 + 2 * E)/D, div_nonneg (by positivity) hD.le, fun u hu ↦ ?_⟩
  have hpos : 0 < u := zero_lt_one.trans_le hu
  have hv : 1 ≤ u ^ (1 / 2 : ℝ) := Real.one_le_rpow hu (by norm_num)
  have hl : Real.log u ≤ 2 * u ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos (1 / 2 : ℝ))
    rw [Real.log_rpow hpos] at h
    linarith
  rw [Real.log_mul hB.ne' (Real.rpow_pos_of_pos hpos E).ne', Real.log_rpow hpos]
  change _ / D ≤ _ / D * _
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hD]
  nlinarith [mul_le_mul_of_nonneg_left hl hE,
    mul_le_mul_of_nonneg_left hv (le_max_right (Real.log B) 0), le_max_left (Real.log B) 0]

/-- Jensen's formula bounds the total multiplicity in a fixed-width rectangle of height two. -/
private theorem explicitZeroCount_window_at_height {Λ L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hΛ : MeromorphicOn Λ univ) (hL : MeromorphicNFOn L univ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    (hGrowth : ezStripGrowth(L)) (hne : ∀ᶠ t : ℝ in ezAtAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : ezInverseGrowth(L, σ, k)) (b a : ℝ) :
    ∃ K T : ℝ, 0 ≤ K ∧ ∀ t : ℝ, T ≤ |t| → ∀ S : Finset (ezWindowZeros(Λ, b, a)),
      (∀ z ∈ S, |z.val.im - t| ≤ 1) →
      ∑ z ∈ S, (MeromorphicOn.divisor Λ univ z.val : ℝ) ≤ K * (1 + |t|) ^ (1 / 2 : ℝ) := by
  classical
  let r := |a| + |b - σ| + 2
  let R := r + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := lt_add_one _
  obtain ⟨B, E, T, hB, hE, hdata⟩ := explicitZeroCount_disk_growth hL hGrowth hne hinv R (hr.trans hrR)
  obtain ⟨K, hK, hlog⟩ := explicitZeroCount_log_bound B E r R hB hE hr hrR
  refine ⟨K, T, hK, fun t ht S hS ↦ ?_⟩
  let c : ℂ := ⟨σ, t⟩
  obtain ⟨ha, hc, hbound⟩ := hdata t ht
  have hinside (z : ezWindowZeros(Λ, b, a)) (hz : |z.val.im - t| ≤ 1) : z.val ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    change |z.val.re - σ| + |z.val.im - t| ≤ |a| + |b - σ| + 2
    have hre : |z.val.re - σ| ≤ |a| + |b - σ| := calc
      _ = |(z.val.re - b) + (b - σ)| := by rw [sub_add_sub_cancel]
      _ ≤ _ := (abs_add_le ..).trans
        (add_le_add (z.property.2.le.trans (le_abs_self a)) le_rfl)
    linarith
  let emb : ezWindowZeros(Λ, b, a) ↪ ℂ := Function.Embedding.subtype _
  have hmem : ∀ z ∈ S.map emb, z ∈ closedBall c r := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
    exact hinside i (hS i hi)
  calc
    _ ≤ ∑ z ∈ S, (analyticOrderNatAt L z.val : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact explicitZeroCount_local_order hΛ (hr.trans hrR).le ha hc hcmp
        (closedBall_subset_closedBall hrR.le (hinside z (hS z hz)))
    _ = ∑ z ∈ S.map emb, (analyticOrderNatAt L z : ℝ) := (Finset.sum_map S emb (fun z ↦ (analyticOrderNatAt L z : ℝ))).symm
    _ ≤ _ := (explicitZeroCount_disk_sum hr hrR ha hc hbound _ hmem).trans (hlog _ (by linarith [abs_nonneg t]))

/-- In a fixed vertical strip, the positive orders of a meromorphic function are summable
with weight `(1 + |Im z|)⁻²` if they are bounded by the orders of a meromorphic function of
polynomial growth on fixed strips, with eventual nonvanishing and polynomial reciprocal
growth on a fixed vertical line `σ + it`. The strip has center `b` and half-width `a`. -/
private theorem explicitZeroCount_summable_divisor_div_one_add_abs_im_sq {Λ L : ℂ → ℂ} {σ : ℝ} {k : ℕ}
    (hΛ : MeromorphicOn Λ univ) (hL : MeromorphicNFOn L univ)
    (hcmp : ∀ z, meromorphicOrderAt Λ z ≤ meromorphicOrderAt L z)
    (hGrowth : ezStripGrowth(L)) (hne : ∀ᶠ t : ℝ in ezAtAbsTop, L ⟨σ, t⟩ ≠ 0)
    (hinv : ezInverseGrowth(L, σ, k)) (b a : ℝ) :
    Summable (fun z : ezWindowZeros(Λ, b, a) ↦
      (MeromorphicOn.divisor Λ univ z.val : ℝ) / (1 + |z.val.im|) ^ 2) := by
  classical
  obtain ⟨K, T, hK, hhi⟩ := explicitZeroCount_window_at_height hΛ hL hcmp hGrowth hne hinv b a
  let D := MeromorphicOn.divisor (Λ) univ
  let R := |a| + |b| + max T 0 + 2
  let Z := explicitZeroCount_compact (f := Λ) (closedBall 0 R) (isCompact_closedBall _ _)
  let B := ∑ z ∈ Z.toFinset, max (D z : ℝ) 0
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ le_max_right _ _)
  apply explicitZeroCount_summable_zeroWeights_of_bins (fun z : ezWindowZeros(Λ, b, a) ↦ z.val.im)
    (fun z ↦ (D z.val : ℝ)) (fun z ↦ by exact_mod_cast z.property.1.le) (max B (2 * K))
  intro n S hS
  have hbin (z : ezWindowZeros(Λ, b, a)) (hz : z ∈ S) :
      (n : ℝ) ≤ |z.val.im| ∧ |z.val.im| < (n : ℝ) + 1 := by
    rw [← hS z hz]
    exact ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  have hu : 1 ≤ ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num)
  by_cases ht : T ≤ (n : ℝ)
  · let C (z : ezWindowZeros(Λ, b, a)) := 0 ≤ z.val.im
    have hp := hhi n (by simpa using ht) (S.filter C) (by
      intro z hz
      obtain ⟨hzS, hpos⟩ := Finset.mem_filter.mp hz
      have he := hbin z hzS
      rw [abs_of_nonneg (show 0 ≤ z.val.im from hpos)] at he
      exact abs_le.mpr ⟨by linarith [he.1], by linarith [he.2]⟩)
    have hn := hhi (-(n : ℝ)) (by simpa using ht) (S.filter (fun z ↦ ¬ C z)) (by
      intro z hz
      obtain ⟨hzS, hneg⟩ := Finset.mem_filter.mp hz
      have he := hbin z hzS
      rw [abs_of_neg (lt_of_not_ge (show ¬ 0 ≤ z.val.im from hneg))] at he
      exact abs_le.mpr ⟨by linarith [he.2], by linarith [he.1]⟩)
    simp only [abs_neg, Nat.abs_cast, add_comm (1 : ℝ)] at hp hn
    have hsum := Finset.sum_filter_add_sum_filter_not S C (fun z ↦ (D z.val : ℝ))
    calc
      _ ≤ (2 * K) * (((n : ℝ) + 1) ^ (1 / 2 : ℝ)) := by
        rw [← hsum]
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hsub : ∀ z ∈ S, z ∈ (fun z : ezWindowZeros(Λ, b, a) ↦ z.val) ⁻¹' (Z.toFinset : Set ℂ) := by
      intro z hz
      change z.val ∈ Z.toFinset
      apply Z.mem_toFinset.mpr
      refine ⟨?_, z.property.1.ne'⟩
      rw [mem_closedBall_zero_iff]
      apply (Complex.norm_le_abs_re_add_abs_im _).trans
      have hre : |z.val.re| ≤ |a| + |b| := calc
        _ = |(z.val.re - b) + b| := by rw [sub_add_cancel]
        _ ≤ _ := (abs_add_le ..).trans
          (add_le_add (z.property.2.le.trans (le_abs_self a)) le_rfl)
      dsimp [R]
      linarith [(hbin z hz).2, le_max_left T 0, lt_of_not_ge ht]
    let emb : ezWindowZeros(Λ, b, a) ↪ ℂ := Function.Embedding.subtype _
    have hmap : S.map emb ⊆ Z.toFinset := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
      exact hsub i hi
    calc
      _ ≤ ∑ z ∈ S, max (D z.val : ℝ) 0 := Finset.sum_le_sum (fun _ _ ↦ le_max_left _ _)
      _ = ∑ z ∈ S.map emb, max (D z : ℝ) 0 := (Finset.sum_map S emb (fun z ↦ max (D z : ℝ) 0)).symm
      _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun _ _ _ ↦ le_max_right _ _)
      _ ≤ max B (2 * K) * (((n : ℝ) + 1) ^ (1 / 2 : ℝ)) :=
        (le_max_left _ _).trans (le_mul_of_one_le_right (hB.trans (le_max_left _ _)) hu)

/-- Removing the gamma factor from the continued completed function gives a continuation of the
finite L-function whose orders dominate those of the completed function (copied, adapted, from
`zeroCount_finite_companion` in `Ch01_Introduction/Sec4.lean`). -/
private theorem explicitZeroCount_companion (χ : U[F]) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ (∀ s : halfPlane, L s = finiteHeckeL χ s) ∧
      ∀ z, meromorphicOrderAt (explicitFormulaCompletedHeckeL χ) z ≤ meromorphicOrderAt L z := by
  let Λ := explicitFormulaCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let P := G * Λ
  obtain ⟨hΛ, hval⟩ := explicitFormulaCompletedHeckeL_spec χ
  have hG := differentiable_inv_heckeGammaFactor χ
  have hm : MeromorphicOn P univ := fun z hz ↦
    (hG.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  refine ⟨toMeromorphicNFOn P univ, meromorphicNFOn_toMeromorphicNFOn _ _, ?_, ?_⟩
  · intro z
    have hγ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans z.property)
    have hNF : MeromorphicNFAt P z :=
      (meromorphicNFAt_mul_iff_right (hG.analyticAt z) (inv_ne_zero hγ)).2 (hΛ (mem_univ _))
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _), toMeromorphicNFAt_eq_self.mpr hNF]
    simp [P, Λ, G, hval z, completedHeckeL, finiteHeckeL, hγ]
  · intro z
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
      show meromorphicOrderAt P z = _ from meromorphicOrderAt_mul
        (hG.analyticAt z).meromorphicAt (hΛ (mem_univ z)).meromorphicAt]
    exact le_add_of_nonneg_left (hG.analyticAt z).meromorphicOrderAt_nonneg

/-- On the line `Re s = 2` a continuation of the finite L-function is bounded away from zero
(Euler product). -/
private theorem explicitZeroCount_line_two (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ c > (0 : ℝ), ∀ t : ℝ, c ≤ ‖L ⟨2, t⟩‖ := by
  refine ⟨Real.exp (-(∑' v : Primes(F), q(v) ^ (-(2 : ℝ)))), Real.exp_pos _, fun t ↦ ?_⟩
  have h2 : (⟨2, t⟩ : ℂ) ∈ halfPlane := by
    change (1 : ℝ) < 2
    norm_num
  rw [hSeries ⟨_, h2⟩]
  exact completedHeckeL_logDeriv_finite_lower χ 2 (by norm_num) ⟨2, t⟩ rfl

end ExplicitFormulaZeroCount

/-- Paper: Lemma B.4.4.9, pp. 624–625. The zeros of the completed Hecke L-function of a
fixed unitary character, counted with multiplicity, satisfy `∑ ord(ρ) / (1 + |Im ρ|)² < ∞`.
This is the classical consequence of the zero count `N(T + 1) - N(T) = O(log T)`. -/
theorem explicitFormulaCompletedHeckeL_summable_divisor_div_sq (χ : U[F]) :
    Summable (fun s : {s : ℂ //
        0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ s} ↦
      (MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ s.val : ℝ) /
        (1 + |s.val.im|) ^ 2) := by
  obtain ⟨hΛ, -⟩ := explicitFormulaCompletedHeckeL_spec χ
  obtain ⟨L, hL, hSeries, hOrder⟩ := explicitZeroCount_companion χ
  obtain ⟨c, hc, hlow⟩ := explicitZeroCount_line_two χ L hSeries
  have hne : ∀ t : ℝ, L ⟨2, t⟩ ≠ 0 := fun t h ↦ by
    have := hlow t
    rw [h, norm_zero] at this
    linarith
  have hinv : (fun t : ℝ ↦ (L ⟨2, t⟩)⁻¹) =O[comap (abs : ℝ → ℝ) atTop]
      (fun t : ℝ ↦ |t| ^ (0 : ℕ)) := by
    refine Asymptotics.IsBigO.of_bound c⁻¹ (Eventually.of_forall fun t ↦ ?_)
    rw [pow_zero, norm_one, mul_one, norm_inv]
    exact inv_anti₀ hc (hlow t)
  have hW := explicitZeroCount_summable_divisor_div_one_add_abs_im_sq (k := 0) (σ := 2)
    hΛ.meromorphicOn hL hOrder
    (fun a b hab ↦ finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries a b hab)
    (Eventually.of_forall hne) hinv (1 / 2) 1
  let ι : {s : ℂ // 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ s} →
      {z : ℂ // 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ z ∧
        |Complex.re z - ((1 / 2 : ℝ))| < (1 : ℝ)} := fun s ↦
    ⟨s.val, s.property, by
      have h := explicitFormulaCompletedHeckeL_zero_re_mem χ s.property
      rw [abs_lt]
      constructor <;> linarith [h.1, h.2]⟩
  exact hW.comp_injective (f := _) (i := ι) fun x y h ↦ Subtype.ext (congrArg Subtype.val h :)

section ExplicitFormulaMellinDecay

open scoped Pointwise in
/-- The integral of the derivative of a compactly supported function along a one-parameter
subgroup vanishes: the integral of each right translate is the same, and the derivative may be
taken under the integral since the translates over `|t| < 1` stay in one compact set. -/
private theorem explicitFormula_integral_flowDeriv_eq_zero {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (b : Multiplicative ℝ →ₜ* G) {H H' : G → ℂ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (hH' : Continuous H') (hH'c : HasCompactSupport H')
    (hd : ∀ x, HasDerivAt (fun t : ℝ ↦ H (x * b (Multiplicative.ofAdd t))) (H' x) 0) :
    ∫ x, H' x ∂μ = 0 := by
  let β : ℝ → G := fun t ↦ b (Multiplicative.ofAdd t)
  have hβ : Continuous β := b.continuous.comp continuous_ofAdd
  have hβadd (t u : ℝ) : β (t + u) = β t * β u := by
    simp only [β, ofAdd_add, map_mul]
  have hdt (x : G) (t : ℝ) : HasDerivAt (fun u : ℝ ↦ H (x * β u)) (H' (x * β t)) t := by
    have h0 : HasDerivAt (fun u ↦ H (x * β t * β u)) (H' (x * β t)) (t - t) := by
      rw [sub_self]
      exact hd _
    have h := h0.comp_sub_const t t
    refine h.congr_of_eventuallyEq (.of_forall fun u ↦ ?_)
    change H (x * β u) = H (x * β t * β (u - t))
    rw [mul_assoc, ← hβadd, add_sub_cancel]
  obtain ⟨C, hC⟩ := hH'.bounded_above_of_compact_support hH'c
  let L : Set G := β '' Metric.closedBall 0 1
  have hL : IsCompact L := (isCompact_closedBall 0 1).image hβ
  let S : Set G := tsupport H' * L
  have hS : IsCompact S := hH'c.isCompact.mul hL
  let bound : G → ℝ := S.indicator fun _ ↦ C
  have hbound : Integrable bound μ :=
    (integrable_indicator_iff hS.measurableSet).mpr (integrableOn_const hS.measure_lt_top.ne)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t x ↦ H (x * β t)) (F' := fun t x ↦ H' (x * β t)) (x₀ := (0 : ℝ))
    (bound := bound) (Metric.ball_mem_nhds 0 one_pos)
    (.of_forall fun t ↦ (hH.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (by simpa [β] using hH.integrable_of_hasCompactSupport hHc)
    ((hH'.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
    (.of_forall fun x t ht ↦ ?_) hbound (.of_forall fun x t _ ↦ hdt x t)
  · have hconst : (fun t : ℝ ↦ ∫ x, H (x * β t) ∂μ) = fun _ ↦ ∫ x, H x ∂μ :=
      funext fun t ↦ integral_mul_right_eq_self H (β t)
    have h0 := hmain.2
    rw [hconst] at h0
    have h1 := h0.unique (hasDerivAt_const (0 : ℝ) (∫ x, H x ∂μ))
    simpa [β] using h1
  · by_cases hx : x * β t ∈ tsupport H'
    · have hxS : x ∈ S := ⟨x * β t, hx, β (-t), ⟨-t, by simpa using (Metric.mem_ball.mp ht).le, rfl⟩,
        show x * β t * β (-t) = x by rw [mul_assoc, ← hβadd, add_neg_cancel]; simp [β]⟩
      simp only [bound, indicator_of_mem hxS]
      exact hC _
    · simp only [image_eq_zero_of_notMem_tsupport hx, norm_zero, bound]
      exact indicator_nonneg (fun _ _ ↦ (norm_nonneg _).trans (hC 1)) x

/-- The derivative of a test along a one-parameter subgroup is a test: it is Bruhat smooth,
and it vanishes off the support of the test. -/
private theorem explicitFormula_flowDeriv_mem (b : Multiplicative ℝ →ₜ* C[F]) (f : 𝒟(C[F])) :
    bruhatDirectionalDeriv b f.val ∈ bruhatCompactSupportSubmodule C[F] := by
  refine ⟨bruhatDirectionalDeriv_mem_smooth b ⟨f.val, f.property.1⟩,
    HasCompactSupport.intro f.property.2 fun x hx ↦ ?_⟩
  have hev : (fun t : ℝ ↦ f.val (x * b (Multiplicative.ofAdd t))) =ᶠ[𝓝 0] fun _ ↦ 0 := by
    have ht : Tendsto (fun t : ℝ ↦ x * b (Multiplicative.ofAdd t)) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ ↦ x * b (Multiplicative.ofAdd t)) :=
        continuous_const.mul (b.continuous.comp continuous_ofAdd)
      simpa using hc.tendsto 0
    exact ht.eventually (notMem_tsupport_iff_eventuallyEq.mp hx)
  change deriv _ 0 = 0
  rw [hev.deriv_eq, deriv_const]

/-- Integration by parts along a one-parameter subgroup against a quasi-character: if the
quasi-character has derivative `σ` at the identity along the subgroup, then the derivative of a
test integrates against it to `-σ` times the test. -/
private theorem explicitFormula_integral_flowDeriv_mul (b : Multiplicative ℝ →ₜ* C[F])
    (c : C[F] →ₜ* ℂ) {σ : ℂ}
    (hσ : HasDerivAt (fun t : ℝ ↦ c (b (Multiplicative.ofAdd t))) σ 0) (f : 𝒟(C[F])) :
    ∫ x, bruhatDirectionalDeriv b f.val x * c x ∂classMeasure =
      -(σ * ∫ x, f.val x * c x ∂classMeasure) := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : (classMeasure).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hf1 : IsBruhatContDiff 1 f.val := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 1
  have hfc : Continuous f.val := explicitTest_continuous f
  have hDc : Continuous (bruhatDirectionalDeriv b f.val) := bruhatDirectionalDeriv_continuous b hf1
  have hDs : HasCompactSupport (bruhatDirectionalDeriv b f.val) :=
    (explicitFormula_flowDeriv_mem b f).2
  have hcc : Continuous c := c.continuous
  have h := explicitFormula_integral_flowDeriv_eq_zero classMeasure b
    (H := fun x ↦ f.val x * c x)
    (H' := fun x ↦ bruhatDirectionalDeriv b f.val x * c x + σ * (f.val x * c x))
    (hfc.mul hcc) f.property.2.mul_right
    ((hDc.mul hcc).add (continuous_const.mul (hfc.mul hcc)))
    ((hDs.mul_right).add (f.property.2.mul_right.mul_left)) fun x ↦ ?_
  · have hi1 : Integrable (fun x ↦ bruhatDirectionalDeriv b f.val x * c x) classMeasure :=
      (hDc.mul hcc).integrable_of_hasCompactSupport hDs.mul_right
    have hi2 : Integrable (fun x ↦ σ * (f.val x * c x)) classMeasure :=
      (continuous_const.mul (hfc.mul hcc)).integrable_of_hasCompactSupport
        f.property.2.mul_right.mul_left
    rw [integral_add hi1 hi2, integral_const_mul] at h
    exact eq_neg_of_add_eq_zero_left h
  · have hfd := hasDerivAt_bruhatDirectionalDeriv b hf1 x
    have hcd : HasDerivAt (fun t : ℝ ↦ c (x * b (Multiplicative.ofAdd t))) (c x * σ) 0 := by
      simp only [map_mul]
      exact hσ.const_mul (c x)
    have := hfd.mul hcd
    simp only [ofAdd_zero, map_one, mul_one] at this
    convert this using 1
    ring
/-- Differentiation along a one-parameter subgroup lifting the norm (`t ↦ τ(eᵗ)` for a section
`τ` of the class norm): for a unitary character `χ` there is a constant `κ` such that every test
has a test whose centered Mellin transform is that of the test times `s - 1/2 + κ`. -/
private theorem explicitFormula_mellin_flowDeriv (χ : U[F]) :
    ∃ κ : ℂ, ∀ f : 𝒟(C[F]), ∃ f' : 𝒟(C[F]), ∀ s : ℂ,
      ∫ g, classMellinIntegrand(f', ideleClassNormTwist χ s, -1 / 2) g ∂classMeasure =
        (s - 1 / 2 + κ) *
          ∫ g, classMellinIntegrand(f, ideleClassNormTwist χ s, -1 / 2) g ∂classMeasure := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨τ, hτc, hτ⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  let b : Multiplicative ℝ →ₜ* C[F] :=
    ⟨τ.comp positiveRealLogEquiv.symm.toMulEquiv.toMonoidHom,
      hτc.comp positiveRealLogEquiv.symm.continuous⟩
  have hN (t : ℝ) : ((ideleClassNorm F (b (Multiplicative.ofAdd t))).val : ℝ) = Real.exp t := by
    change ((ideleClassNorm F (τ (positiveRealLogEquiv.symm (Multiplicative.ofAdd t)))).val : ℝ) = _
    rw [hτ]
    have h := positiveRealLogEquiv_apply (positiveRealLogEquiv.symm (Multiplicative.ofAdd t))
    rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))).symm.trans
      (congrArg Real.exp h.symm)
  have hχ1 : IsBruhatContDiff 1 (fun x : C[F] ↦ (χ x : ℂ)) :=
    (mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth χ) 1
  let κ := bruhatDirectionalDeriv b (fun x : C[F] ↦ (χ x : ℂ)) 1
  have hκ : HasDerivAt (fun t : ℝ ↦ (χ (b (Multiplicative.ofAdd t)) : ℂ)) κ 0 := by
    simpa only [one_mul] using hasDerivAt_bruhatDirectionalDeriv b hχ1 1
  refine ⟨κ, fun f ↦ ⟨⟨fun x ↦ -bruhatDirectionalDeriv b f.val x,
    neg_mem (explicitFormula_flowDeriv_mem b f)⟩, fun s ↦ ?_⟩⟩
  let w : ℂ := s - 1 / 2
  let c : C[F] →ₜ* ℂ := ideleClassNormTwist χ w
  have hc (g : C[F]) : ideleClassNormTwist χ s g * classWeight(g, -1 / 2) = c g := by
    have hpos : (((ideleClassNorm F g).val : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change ((χ g : Circle) : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ s *
        (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-1 / 2 : ℂ) =
      ((χ g : Circle) : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w
    rw [mul_assoc, ← Complex.cpow_add _ _ hpos]
    congr 2
    simp only [w]
    ring
  have hσ : HasDerivAt (fun t : ℝ ↦ c (b (Multiplicative.ofAdd t))) (κ + w) 0 := by
    have he : HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * w)) w 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).cexp
      simpa using this
    have hprod := hκ.mul he
    simp only [ofAdd_zero, map_one, Circle.coe_one, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one, one_mul] at hprod
    refine hprod.congr_of_eventuallyEq (.of_forall fun t ↦ ?_)
    change ((χ (b (Multiplicative.ofAdd t)) : Circle) : ℂ) *
        (((ideleClassNorm F (b (Multiplicative.ofAdd t))).val : ℝ) : ℂ) ^ w = _
    rw [hN, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    rfl
  have hIBP := explicitFormula_integral_flowDeriv_mul b c hσ f
  have hM (h : C[F] → ℂ) : ∫ g, h g * ideleClassNormTwist χ s g * classWeight(g, -1 / 2)
      ∂classMeasure = ∫ g, h g * c g ∂classMeasure :=
    integral_congr_ae (.of_forall fun g ↦ by
      change h g * ideleClassNormTwist χ s g * classWeight(g, -1 / 2) = h g * c g
      rw [mul_assoc, hc])
  change ∫ g, (-bruhatDirectionalDeriv b f.val g) * ideleClassNormTwist χ s g *
      classWeight(g, -1 / 2) ∂classMeasure = _
  rw [hM, hM]
  simp only [neg_mul]
  rw [integral_neg, hIBP]
  simp only [w]
  ring

/-- On the closed critical strip, the centered idelic Mellin transform of a test is bounded:
the twisted weight `|g|^(Re s - 1/2)` is at most `|g|^(1/2) + |g|^(-1/2)`, which is integrable
against the compactly supported test. -/
private theorem explicitFormula_mellin_strip_bounded (f : 𝒟(C[F])) (χ : U[F]) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, s.re ∈ Icc (0 : ℝ) 1 →
      ‖∫ g, classMellinIntegrand(f, ideleClassNormTwist χ s, -1 / 2) g ∂classMeasure‖ ≤ B := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : (classMeasure).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let N : C[F] → ℝ := fun g ↦ ((ideleClassNorm F g).val : ℝ)
  have hNpos (g : C[F]) : 0 < N g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hNc : Continuous N := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  let w : C[F] → ℝ := fun g ↦ ‖f.val g‖ * (N g ^ (1 / 2 : ℝ) + N g ^ (-1 / 2 : ℝ))
  have hwc : Continuous w := (explicitTest_continuous f).norm.mul
    ((hNc.rpow_const fun g ↦ Or.inl (hNpos g).ne').add (hNc.rpow_const fun g ↦ Or.inl (hNpos g).ne'))
  have hwi : Integrable w classMeasure :=
    hwc.integrable_of_hasCompactSupport f.property.2.norm.mul_right
  refine ⟨∫ g, w g ∂classMeasure, integral_nonneg fun g ↦ ?_, fun s hs ↦ ?_⟩
  · exact mul_nonneg (norm_nonneg _) (add_nonneg (Real.rpow_nonneg (hNpos g).le _)
      (Real.rpow_nonneg (hNpos g).le _))
  refine norm_integral_le_of_norm_le hwi (.of_forall fun g ↦ ?_)
  have hχ : ‖ideleClassNormTwist χ s g‖ = N g ^ s.re := by
    change ‖((χ g : Circle) : ℂ) * ((N g : ℂ) ^ s)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hNpos g)]
  have hw : ‖((N g : ℂ) ^ (-1 / 2 : ℂ))‖ = N g ^ (-1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hNpos g)]
    norm_num
  rw [norm_mul, norm_mul, hχ]
  change ‖f.val g‖ * N g ^ s.re * ‖((N g : ℂ) ^ (-1 / 2 : ℂ))‖ ≤ w g
  rw [hw, mul_assoc, ← Real.rpow_add (hNpos g)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rcases le_total 1 (N g) with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hs.2])).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hNpos g).le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge (hNpos g) h1 (by linarith [hs.1])).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg (hNpos g).le _))

end ExplicitFormulaMellinDecay

/-- Paper: Lemma B.4.4.9, pp. 624–625. For a fixed test and a fixed unitary character, the
centered idelic Mellin transform of the test decays like the inverse square of the height in
the closed critical strip. The test is smooth and compactly supported along the norm, so this
is the standard integration by parts in the radial variable. -/
theorem idelicExplicitFormula_mellin_decay (f : 𝒟(C[F])) (χ : U[F]) :
    ∃ K : ℝ, ∀ s : ℂ, s.re ∈ Icc (0 : ℝ) 1 →
      ‖∫ g, classMellinIntegrand(f, ideleClassNormTwist χ s, -1 / 2) g ∂classMeasure‖ ≤
        K / (1 + |s.im|) ^ 2 := by
  obtain ⟨κ, hκ⟩ := explicitFormula_mellin_flowDeriv χ
  obtain ⟨f₁, h₁⟩ := hκ f
  obtain ⟨f₂, h₂⟩ := hκ f₁
  obtain ⟨B₀, hB₀, hb₀⟩ := explicitFormula_mellin_strip_bounded f χ
  obtain ⟨B₂, hB₂, hb₂⟩ := explicitFormula_mellin_strip_bounded f₂ χ
  refine ⟨B₀ * (2 * |κ.im| + 2) ^ 2 + 4 * B₂, fun s hs ↦ ?_⟩
  set M := ∫ g, classMellinIntegrand(f, ideleClassNormTwist χ s, -1 / 2) g ∂classMeasure
  set z : ℂ := s - 1 / 2 + κ
  have hM2 : ‖z‖ ^ 2 * ‖M‖ ≤ B₂ := by
    have h := hb₂ s hs
    rw [h₂, h₁, ← mul_assoc, norm_mul, norm_mul] at h
    change ‖z‖ * ‖z‖ * ‖M‖ ≤ B₂ at h
    rwa [sq]
  have hκ0 : 0 ≤ |κ.im| := abs_nonneg _
  have ht : 0 ≤ |s.im| := abs_nonneg _
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt |s.im| (2 * |κ.im| + 1) with h | h
  · have hp : (1 + |s.im|) ^ 2 ≤ (2 * |κ.im| + 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc ‖M‖ * (1 + |s.im|) ^ 2 ≤ B₀ * (2 * |κ.im| + 2) ^ 2 :=
          mul_le_mul (hb₀ s hs) hp (by positivity) hB₀
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hzim : z.im = s.im + κ.im := by simp [z]
    have hsub : |s.im| ≤ |s.im + κ.im| + |κ.im| := by
      have := abs_add_le (s.im + κ.im) (-κ.im)
      rwa [add_neg_cancel_right, abs_neg] at this
    have hz : (1 + |s.im|) / 2 ≤ ‖z‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm z)
      rw [hzim]
      linarith
    have hz2 : (1 + |s.im|) ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
      nlinarith [hz, norm_nonneg z]
    calc ‖M‖ * (1 + |s.im|) ^ 2 ≤ ‖M‖ * (4 * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hz2 (norm_nonneg _)
      _ = 4 * (‖z‖ ^ 2 * ‖M‖) := by ring
      _ ≤ 4 * B₂ := by linarith
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-- Paper: Lemma B.4.4.9, pp. 624–625, for one character. For a fixed unitary character `χ`,
the spectral terms of the idelic explicit formula at the zeros of the completed Hecke
L-function of `χ`, weighted by their multiplicities, are absolutely summable at every test. -/
theorem idelicExplicitFormula_summable_spectral_fiber (f : 𝒟(C[F])) (χ : U[F]) :
    Summable (fun s : {s : ℂ //
        0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ s} ↦
      ‖(MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ s.val : ℂ) *
        ∫ g, classMellinIntegrand(f, ideleClassNormTwist χ s.val, -1 / 2) g ∂classMeasure‖) := by
  obtain ⟨K, hK⟩ := idelicExplicitFormula_mellin_decay f χ
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun s ↦ ?_)
    ((explicitFormulaCompletedHeckeL_summable_divisor_div_sq χ).mul_left K)
  set d := MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ s.val
  have hd : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast s.property.le
  rw [norm_mul, show ((d : ℂ)) = ((d : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
    Real.norm_of_nonneg hd, mul_div_assoc', mul_comm K, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (hK s.val (explicitFormulaCompletedHeckeL_zero_re_mem χ s.property)) hd

/-- A nonzero Mellin coefficient of a test invariant under `k` has frequency trivial on
`k`. Translation by any element of `k` multiplies the coefficient by its character value. -/
private theorem idelicExplicitFormula_summable_spectral_characters_annihilator
    (k : Subgroup C[F]) (f : 𝒟(C[F])) (hinv : ∀ u : k, ∀ x, f.val (u.val * x) = f.val x)
    (c : QuasiCharacter C[F]) (h : (∫ x, f.val x * c x ∂classMeasure) ≠ 0) (u : k) :
    c u.val = 1 := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : (classMeasure).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  apply (mul_eq_left₀ h).mp
  rw [← integral_mul_const]
  calc ∫ x, f.val x * c x * c u.val ∂classMeasure
      = ∫ x, f.val (u.val * x) * c (u.val * x) ∂classMeasure := by
          simp only [hinv, map_mul]
          congr 1
          funext x
          ring
    _ = _ := integral_mul_left_eq_self (fun x ↦ f.val x * c x) u.val

/-- Uniform integration by parts in finitely many one-parameter subgroups. At each zero,
the direction attaining the largest frequency gains one power of its height. -/
private theorem idelicExplicitFormula_summable_spectral_characters_decay
    {Z : Type*} {n : ℕ} (X : Fin (n + 1) → LCATopologicalLie C[F])
    (c : Z → QuasiCharacter C[F]) (W : C[F] → ℝ) (hW : Continuous W)
    (hbound : ∀ z x, ‖c z x‖ ≤ W x) (level : Z → ℕ)
    (hlevel : ∀ z, ∃ i, (level z : ℝ) ≤ ‖bruhatDirectionalDeriv (X i) (c z) 1‖)
    (N : ℕ) (f : 𝒟(C[F])) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖∫ x, f.val x * c z x ∂classMeasure‖ ≤
      B / ((level z : ℝ) + 1) ^ N := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : (classMeasure).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let M (φ : 𝒟(C[F])) (z : Z) := ‖∫ x, φ.val x * c z x ∂classMeasure‖
  suffices ∀ φ : 𝒟(C[F]), ∃ B : ℝ, ∀ z, M φ z * ((level z : ℝ) + 1) ^ N ≤ B by
    obtain ⟨B, hB⟩ := this f
    exact ⟨max 0 B, le_max_left .., fun z ↦ (le_div_iff₀ (by positivity)).2
      ((hB z).trans (le_max_right ..))⟩
  induction N with
  | zero =>
    intro φ
    refine ⟨∫ x, ‖φ.val x‖ * W x ∂classMeasure, fun z ↦ ?_⟩
    simp only [pow_zero, mul_one, M]
    apply norm_integral_le_of_norm_le
      (((explicitTest_continuous φ).norm.mul hW).integrable_of_hasCompactSupport
        φ.property.2.norm.mul_right)
    exact .of_forall fun x ↦ (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left (hbound z x) (norm_nonneg _))
  | succ N ih =>
    intro φ
    let D (i : Fin (n + 1)) : 𝒟(C[F]) :=
      ⟨bruhatDirectionalDeriv (X i) φ.val, explicitFormula_flowDeriv_mem (X i) φ⟩
    choose B hB using fun i ↦ ih (D i)
    obtain ⟨A, hA⟩ := Finite.exists_le B
    obtain ⟨B₀, h₀⟩ := ih φ
    refine ⟨A + B₀, fun z ↦ ?_⟩
    obtain ⟨i, hi⟩ := hlevel z
    have hd := hasDerivAt_bruhatDirectionalDeriv (X i)
      ((mem_bruhatSmoothSubmodule_iff _).mp (quasiCharacter_mem_bruhatSmooth (c z)) 1) 1
    simp only [one_mul] at hd
    have hmul : ‖bruhatDirectionalDeriv (X i) (c z) 1‖ * M φ z = M (D i) z := by
      simp only [M, D, explicitFormula_integral_flowDeriv_mul (X i) (c z) hd φ, norm_neg, norm_mul]
    have hgain := (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans_eq hmul
    calc M φ z * ((level z : ℝ) + 1) ^ (N + 1)
        = (level z * M φ z) * ((level z : ℝ) + 1) ^ N + M φ z * ((level z : ℝ) + 1) ^ N := by ring
      _ ≤ A + B₀ := add_le_add ((mul_le_mul_of_nonneg_right hgain (by positivity)).trans
        ((hB i z).trans (hA i))) (h₀ z)

/-- The shell estimate of Lemma B.4.4.8 with weights. A shell of total multiplicity
at most `C (j+1)^d` and decay of order `d+2` contributes at most `C B / (j+1)^2`. -/
private theorem idelicExplicitFormula_summable_spectral_characters_shells
    {Z : Type*} (level : Z → ℕ) (w M : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hM : ∀ z, 0 ≤ M z)
    (C B : ℝ) (hB : 0 ≤ B) (d : ℕ)
    (hcount : ∀ j : ℕ, ∀ u : Finset Z, (∀ z ∈ u, M z ≠ 0 ∧ level z = j) →
      ∑ z ∈ u, w z ≤ C * ((j : ℝ) + 1) ^ d)
    (hdecay : ∀ z, M z ≤ B / ((level z : ℝ) + 1) ^ (d + 2)) :
    Summable (fun z ↦ w z * M z) := by
  classical
  have hseries : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hC : 0 ≤ C := by simpa using hcount 0 ∅ (by simp)
  refine summable_of_sum_le (fun z ↦ mul_nonneg (hw z) (hM z))
    (c := C * B * ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2) fun s ↦ ?_
  let u := s.filter (fun z ↦ M z ≠ 0)
  have hsu : ∑ z ∈ u, w z * M z = ∑ z ∈ s, w z * M z :=
    Finset.sum_subset (Finset.filter_subset ..) fun z hz hzu ↦ by
      simp_all [u]
  rw [← hsu, ← Finset.sum_fiberwise_of_maps_to (t := u.image level) (g := level)
    (fun z hz ↦ Finset.mem_image_of_mem _ hz)]
  calc ∑ j ∈ u.image level, ∑ z ∈ u with level z = j, w z * M z
      ≤ ∑ j ∈ u.image level, C * B * (1 / ((j : ℝ) + 1) ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        let v := u.filter (fun z ↦ level z = j)
        have hv (z) (hz : z ∈ v) : M z ≠ 0 ∧ level z = j :=
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2, (Finset.mem_filter.mp hz).2⟩
        calc ∑ z ∈ v, w z * M z ≤ ∑ z ∈ v, w z * (B / ((j : ℝ) + 1) ^ (d + 2)) := by
              refine Finset.sum_le_sum fun z hz ↦ mul_le_mul_of_nonneg_left ?_ (hw z)
              simpa only [(hv z hz).2] using hdecay z
          _ = (∑ z ∈ v, w z) * (B / ((j : ℝ) + 1) ^ (d + 2)) := (Finset.sum_mul ..).symm
          _ ≤ (C * ((j : ℝ) + 1) ^ d) * (B / ((j : ℝ) + 1) ^ (d + 2)) :=
            mul_le_mul_of_nonneg_right (hcount j v hv) (by positivity)
          _ = _ := by rw [pow_add]; field_simp
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hseries.sum_le_tsum _ fun j _ ↦ by positivity) (mul_nonneg hC hB)

/-- Along the given log-norm section, a centered zero character has multiplier
`ρ - 1/2`, since its unitary part is trivial on that section. -/
private theorem idelicExplicitFormula_summable_spectral_characters_radial
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (z : chartZeros(τ)) :
    bruhatDirectionalDeriv (τ.comp (positiveRealLogEquiv.symm : _ →ₜ* _))
      (ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2)) 1 = z.val.2 - 1 / 2 := by
  let w := z.val.2 - 1 / 2
  have he : HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * w)) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).cexp
  apply HasDerivAt.deriv (he.congr_of_eventuallyEq (.of_forall fun t ↦ ?_))
  let u := positiveRealLogEquiv.symm (Multiplicative.ofAdd t)
  have hu : (u.val : ℝ) = Real.exp t := by
    have h := positiveRealLogEquiv_apply u
    rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt u))).symm.trans (congrArg Real.exp h.symm)
  simp only [one_mul]
  change ((z.val.1.val (τ u) : Circle) : ℂ) * (((ideleClassNorm F (τ u)).val : ℝ) : ℂ) ^ w = _
  rw [z.val.1.property, Circle.coe_one, one_mul, hτ, hu, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]

/-- Classical input: the uniform local zero count for Hecke L-functions
(Lagarias–Odlyzko, 1977, Lemma 5.4 for finite-order characters, and
Iwaniec–Kowalski, *Analytic Number Theory*, Proposition 5.7 in general).
On a fixed Bruhat quotient the finite conductor is bounded. In torus coordinates the
derivatives of the unitary character along lifted angular directions have norms `|n_j|`.
Zeros with these frequencies and `|Im ρ|` below `T+1` have polynomially bounded total
multiplicity. Finite subsums express this before local finiteness has been proved.
This known theorem is an external arithmetic input whose formal proof is missing here. -/
private theorem idelicExplicitFormula_summable_spectral_characters_polynomialCount
    (τ : ℝ≥0ˣ →ₜ* C[F]) (_hτ : RightInverse τ (ideleClassNorm F))
    (k : Subgroup C[F]) (_hk : IsBruhatGoodSubgroup k) :
    ∃ (n : ℕ) (Y : Fin n → LCATopologicalLie (ideleClassNorm F).ker) (C : ℝ) (d : ℕ),
      ∀ T : ℕ, ∀ S : Finset (chartZeros(τ)),
        (∀ z ∈ S, (∀ u : k, z.val.1.val u.val = 1) ∧ |z.val.2.im| < (T : ℝ) + 1 ∧
          ∀ i, ‖bruhatDirectionalDeriv (Y i) (fun u ↦ (z.val.1.val u.val : ℂ)) 1‖ < (T : ℝ) + 1) →
        ∑ z ∈ S, ‖zeroMultiplicity(z)‖ ≤ C * ((T : ℝ) + 1) ^ d := by
  sorry

/-- Paper: Lemma B.4.4.9, pp. 624–625, summed over characters. Over the unitary characters
trivial on the image of the norm section `τ`, the per-character sums of the absolute spectral
terms of the idelic explicit formula at a fixed test are summable. This is the uniform half of
Lemma B.4.4.9: a test only sees the characters of a Lie quotient of the idele classes, and the
zero count of their completed Hecke L-functions must be polynomial jointly in the height and in
the archimedean frequency of the character (see the paper-gap note at
`summable_ideleClassMellin_completedHeckeZeros`). -/
theorem idelicExplicitFormula_summable_spectral_characters (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) :
    Summable (fun χ : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} ↦
      ∑' s : {s : ℂ // 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ s},
        ‖(MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ s.val : ℂ) *
          ∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s.val, -1 / 2) g
            ∂classMeasure‖) := by
  classical
  let Z := chartZeros(τ)
  let c (z : Z) := ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2)
  let M (z : Z) := ‖∫ x, f.val x * c z x ∂classMeasure‖
  obtain ⟨k, hk, hinv, _⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 0
  obtain ⟨n, Y, C, d, hcount⟩ :=
    idelicExplicitFormula_summable_spectral_characters_polynomialCount τ _hτ k hk
  let incl : (ideleClassNorm F).ker →ₜ* C[F] := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
  -- The radial flow and the norm-one flows measure all frequencies in the counting box.
  let X : Fin (n + 1) → LCATopologicalLie C[F] :=
    Fin.cons (τ.comp (positiveRealLogEquiv.symm : _ →ₜ* _)) (fun i ↦ incl.comp (Y i))
  let freq (i : Fin (n + 1)) (z : Z) := ‖bruhatDirectionalDeriv (X i) (c z) 1‖
  let level (z : Z) := Finset.univ.sup (fun i ↦ ⌊freq i z⌋₊)
  have hlevel (z : Z) : ∃ i, (level z : ℝ) ≤ freq i z := by
    obtain ⟨i, _, hi⟩ := Finset.univ.exists_mem_eq_sup Finset.univ_nonempty (fun i ↦ ⌊freq i z⌋₊)
    exact ⟨i, by simpa only [level, hi] using Nat.floor_le (norm_nonneg _)⟩
  let r (x : C[F]) : ℝ := ((ideleClassNorm F x).val : ℝ)
  have hr (x : C[F]) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hrc : Continuous r := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  let W (x : C[F]) := r x ^ (-(1 / 2) : ℝ) + r x ^ (1 / 2 : ℝ)
  have hW : Continuous W := (hrc.rpow_const fun x ↦ Or.inl (hr x).ne').add
    (hrc.rpow_const fun x ↦ Or.inl (hr x).ne')
  have hbound (z : Z) (x : C[F]) : ‖c z x‖ ≤ W x := by
    have hs := explicitFormulaCompletedHeckeL_zero_re_mem z.val.1.val z.property
    have hre : (z.val.2 - (1 / 2 : ℂ)).re = z.val.2.re - 1 / 2 := by simp
    change ‖((z.val.1.val x : Circle) : ℂ) * (r x : ℂ) ^ (z.val.2 - 1 / 2)‖ ≤ _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hr x), hre]
    rcases le_total (r x) 1 with h | h
    · exact (Real.rpow_le_rpow_of_exponent_ge (hr x) h (by linarith [hs.1])).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (hr x).le _))
    · exact (Real.rpow_le_rpow_of_exponent_le h (by linarith [hs.2])).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (hr x).le _))
  obtain ⟨B, hB, hdecay⟩ := idelicExplicitFormula_summable_spectral_characters_decay X c W hW
    hbound level hlevel (d + 2) f
  have hker : k ≤ (ideleClassNorm F).ker := by
    obtain ⟨m, hm, _, _⟩ := exists_ideleClassModulation F
    rw [← hm]
    exact compactSubgroup_le_modulation_ker m k hk.isCompact
  have hrestrict (z : Z) (g : C[F]) (hg : ideleClassNorm F g = 1) :
      c z g = (z.val.1.val g : ℂ) := by
    change ((z.val.1.val g : Circle) : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (z.val.2 - 1 / 2) = _
    simp [hg]
  have hsum : Summable (fun z : Z ↦ ‖zeroMultiplicity(z)‖ * M z) := by
    apply idelicExplicitFormula_summable_spectral_characters_shells level _ M (fun _ ↦ norm_nonneg _)
      (fun _ ↦ norm_nonneg _) C B hB d _ hdecay
    intro j S hS
    apply hcount j S
    intro z hz
    obtain ⟨hne, hj⟩ := hS z hz
    have hsmall (i : Fin (n + 1)) : freq i z < (j : ℝ) + 1 := by
      have hi : ⌊freq i z⌋₊ ≤ level z := Finset.le_sup (f := fun i ↦ ⌊freq i z⌋₊) (Finset.mem_univ i)
      exact (Nat.lt_floor_add_one (freq i z)).trans_le (by exact_mod_cast Nat.succ_le_succ (hj ▸ hi))
    refine ⟨fun u ↦ Circle.coe_injective ?_, ?_, fun i ↦ ?_⟩
    · rw [← hrestrict z u.val (hker u.property), Circle.coe_one]
      exact idelicExplicitFormula_summable_spectral_characters_annihilator k f hinv (c z)
        (norm_ne_zero_iff.mp hne) u
    · have h0 := hsmall 0
      simp only [freq, X, Fin.cons_zero, c,
        idelicExplicitFormula_summable_spectral_characters_radial τ _hτ] at h0
      simpa using (Complex.abs_im_le_norm (z.val.2 - 1 / 2)).trans_lt h0
    · have he : bruhatDirectionalDeriv (X i.succ) (c z) 1 =
          bruhatDirectionalDeriv (Y i) (fun u ↦ (z.val.1.val u.val : ℂ)) 1 := by
        simp only [bruhatDirectionalDeriv, one_mul, X, Fin.cons_succ]
        exact congrArg (fun g : ℝ → ℂ ↦ deriv g 0)
          (funext fun t ↦ hrestrict z _ (Y i (Multiplicative.ofAdd t)).property)
      simpa only [freq, he] using hsmall i.succ
  have hcenter (z : Z) (x : C[F]) : zeroCharacter(z) x * classWeight(x, -1 / 2) = c z x := by
    change ((z.val.1.val x : Circle) : ℂ) * (r x : ℂ) ^ z.val.2 * (r x : ℂ) ^ (-1 / 2 : ℂ) =
      ((z.val.1.val x : Circle) : ℂ) * (r x : ℂ) ^ (z.val.2 - 1 / 2)
    rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hr x).ne')]
    congr 2
    ring
  have hflat : Summable (fun z : Z ↦ ‖zeroMultiplicity(z) *
      ∫ x, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) x ∂classMeasure‖) := by
    simpa only [norm_mul, mul_assoc, hcenter, M] using hsum
  -- Regroup the weighted zero sum using the fixed-character convergence theorem.
  let P (χ : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}) (s : ℂ) :=
    0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ s
  let e := Equiv.subtypeProdEquivSigmaSubtype P
  exact ((e.symm.hasSum_iff.mpr hflat.hasSum).sigma fun χ ↦
    (idelicExplicitFormula_summable_spectral_fiber f χ.val).hasSum).summable

/-- Paper: Theorem B.4.4.7, pp. 623–626, and Lemma B.4.4.9, pp. 624–625. The spectral terms
of the idelic explicit formula are absolutely summable at every test. -/
theorem idelicExplicitFormula_summable_spectral (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) :
    Summable (fun z : chartZeros(τ) ↦ ‖zeroMultiplicity(z) *
      ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure‖) := by
  let P : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} → ℂ → Prop := fun χ s ↦
    0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ s
  let e := Equiv.subtypeProdEquivSigmaSubtype P
  rw [← e.symm.summable_iff]
  exact (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).2
    ⟨fun χ ↦ idelicExplicitFormula_summable_spectral_fiber f χ.val,
      idelicExplicitFormula_summable_spectral_characters τ _hτ f⟩

/-- Paper: Theorem B.4.4.7, p. 625, (B.4.4.22). For all but finitely many primes the
restricted test is a constant multiple of the integer-unit indicator at an unramified
prime, so its finite principal value vanishes. -/
theorem idelicExplicitFormula_finite_support (f : 𝒟(C[F]))
    (test : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_htest : ∀ v u, (test v).val u = f.val (finiteClassMap(v) u)) :
    {v : Primes(F) | finiteConnesWeilPrincipalValue v 1 (test v) ≠ 0}.Finite := by
  -- Invariance under the integer units at almost every prime.
  obtain ⟨k, hk, hinv, _⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 0
  obtain ⟨W, hW, hpow⟩ := explicitFormula_smallPowers (G := C[F]) k hk
  have hI : ∀ᶠ v : Primes(F) in cofinite,
      ∀ u ∈ (O(v)).units, f.val (finiteClassMap(v) u) = f.val 1 := by
    filter_upwards [explicitFormula_eventually_units_mem W hW] with v hv u hu
    have hk' : finiteClassMap(v) u ∈ k := hpow _ fun n ↦ by
      rw [← map_pow]
      exact hv _ ((O(v)).units.pow_mem hu n)
    exact (congrArg f.val (mul_one (finiteClassMap(v) u)).symm).trans (hinv ⟨_, hk'⟩ 1)
  -- Vanishing off the integer units at primes of large norm.
  let n : C[F] → ℝ := fun g ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hpos (g : C[F]) : 0 < n g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hnι (v : Primes(F)) (x : (v.adicCompletion F)ˣ) : n (finiteClassMap(v) x) = ‖x.val‖ := by
    simp only [n, ideleClassNorm_ofAdicCompletion]
    rfl
  obtain ⟨M₁, hM₁⟩ := f.property.2.exists_bound_of_continuousOn hn.continuousOn
  obtain ⟨M₂, hM₂⟩ := f.property.2.exists_bound_of_continuousOn
    (hn.inv₀ fun g ↦ (hpos g).ne').continuousOn
  let M := max M₁ M₂
  have hS : ∀ᶠ v : Primes(F) in cofinite, M < q(v) := by
    have hfin : {v : Primes(F) | q(v) ≤ M}.Finite := by
      refine ((Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊M⌋₊).preimage
        fun v _ w _ h ↦ HeightOneSpectrum.ext h).subset fun v hv ↦ ?_
      exact Nat.le_floor (show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≤ M from hv)
    filter_upwards [hfin.compl_mem_cofinite] with v hv
    exact lt_of_not_ge hv
  have hZ : ∀ᶠ v : Primes(F) in cofinite, ∀ x : (v.adicCompletion F)ˣ,
      x ∉ (O(v)).units → f.val (finiteClassMap(v) x) = 0 := by
    filter_upwards [hS] with v hv x hx
    by_contra h0
    have hmem : finiteClassMap(v) x ∈ tsupport f.val := subset_tsupport _ h0
    have h₁ := hM₁ _ hmem
    have h₂ := hM₂ _ hmem
    rw [Real.norm_eq_abs, abs_of_pos (hpos _), hnι] at h₁
    rw [Pi.inv_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos _)), hnι] at h₂
    have hx0 : 0 < ‖x.val‖ := norm_pos_iff.mpr x.ne_zero
    have hq : 0 < q(v) := by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
    rcases explicitFormula_finiteUnits_norm_shell v x hx with h | h
    · linarith [le_max_left M₁ M₂]
    · have : q(v) ≤ ‖x.val‖⁻¹ := by
        rw [le_inv_comm₀ hq hx0]
        exact h
      linarith [le_max_right M₁ M₂]
  -- Unramified primes.
  have hD : ∀ᶠ v : Primes(F) in cofinite,
      multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F)) = 0 := by
    filter_upwards [(Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).compl_mem_cofinite]
      with v hv
    exact multiplicity_eq_zero_of_not_dvd hv
  refine (Filter.eventually_cofinite.mp (hI.and (hZ.and hD))).subset fun v hv hP ↦ hv ?_
  obtain ⟨hIv, hZv, hDv⟩ := hP
  obtain ⟨g, hg, hgPV⟩ := finiteConnesWeilPrincipalValue_integerUnits v
  have htest : test v = f.val 1 • g := by
    refine Subtype.ext (funext fun u ↦ ?_)
    change (test v).val u = f.val 1 * g.val u
    rw [_htest, hg]
    by_cases hu : u ∈ (O(v)).units
    · rw [indicator_of_mem hu, hIv u hu, mul_one]
    · rw [indicator_of_notMem hu, hZv u hu, mul_zero]
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hV : V𝔭(v) ≠ 0 := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
  have hscale : finiteWeilScale(v) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero (Real.log_pos hq).ne' hV)
  have hPV : finiteConnesWeilPrincipalValue v 1 g = 0 := by
    rw [hDv] at hgPV
    simp only [Nat.cast_zero, zero_mul, Complex.ofReal_zero, neg_zero] at hgPV
    exact (mul_eq_zero.mp hgPV).resolve_left hscale
  rw [htest, map_smul, hPV, smul_zero]

local notation "chartChars(" τ ")" => {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "radialFlow(" τ ", " x ")" =>
  τ (positiveRealLogEquiv.symm (Multiplicative.ofAdd x))
local notation "explicitPrimeTerm(" χ ", " f ")" =>
  (fun j : Primes(F) × ℕ ↦
    if χ₀(χ).IsUnramifiedAt j.1 then
      let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
      (Real.log q(j.1) * Real.exp (-x / 2) : ℝ) *
        ((χ₀(χ).localValue j.1) ^ (j.2 + 1) * f x +
          (χ₀(χ⁻¹).localValue j.1) ^ (j.2 + 1) * f (-x))
    else (0 : ℂ))
local notation "explicitArchTerm(" χ ", " w ", " f ")" =>
  (if hw : (w : InfinitePlace F).IsReal then
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
      ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
        (Real.log Real.pi : ℂ) * f 0
  else
    let p := (complexHeckeCharacter_parameters χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
      (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
      (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
        2 * (Real.log (2 * Real.pi) : ℂ) * f 0)

section ExplicitFormulaRadialProfile

/-- Differentiation under the integral over the compact norm-one classes along a one-parameter
subgroup: the radial profile of a test has the radial profile of its flow derivative as
derivative. -/
private theorem explicitFormula_radial_hasDerivAt (b : Multiplicative ℝ →ₜ* C[F]) (χ : U[F])
    (f : 𝒟(C[F])) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ∫ u, f.val (b (Multiplicative.ofAdd y) * (u : C[F])) *
        (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F)
      (∫ u, bruhatDirectionalDeriv b f.val (b (Multiplicative.ofAdd x) * (u : C[F])) *
        (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) x := by
  -- The Tamagawa measure on `C¹` lives on the subtype σ-algebra.
  let : BorelSpace C[F] := ⟨rfl⟩
  let mK : MeasurableSpace (ideleClassNorm F).ker := Subtype.instMeasurableSpace
  have : OpensMeasurableSpace (ideleClassNorm F).ker := Subtype.opensMeasurableSpace (α := C[F]) _
  have : IsFiniteMeasure (normOneIdeleClassTamagawaMeasure F) :=
    ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let β : ℝ → C[F] := fun t ↦ b (Multiplicative.ofAdd t)
  have hβadd (t u : ℝ) : β (t + u) = β t * β u := by
    simp only [β, ofAdd_add, map_mul]
  have hf1 : IsBruhatContDiff 1 f.val := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 1
  have hfc : Continuous f.val := explicitTest_continuous f
  let D := bruhatDirectionalDeriv b f.val
  have hDc : Continuous D := bruhatDirectionalDeriv_continuous b hf1
  have hDs : HasCompactSupport D := (explicitFormula_flowDeriv_mem b f).2
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDs
  have hdt (g : C[F]) (t : ℝ) : HasDerivAt (fun y : ℝ ↦ f.val (β y * g)) (D (β t * g)) t := by
    have h0 : HasDerivAt (fun y ↦ f.val (g * β t * β y)) (D (g * β t)) (t - t) := by
      rw [sub_self]
      exact hasDerivAt_bruhatDirectionalDeriv b hf1 _
    have h := h0.comp_sub_const t t
    rw [mul_comm g] at h
    refine h.congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
    change f.val (β y * g) = f.val (β t * g * β (y - t))
    rw [mul_comm (β t) g, mul_assoc, ← hβadd, add_sub_cancel, mul_comm]
  have hχc : Continuous (fun u : (ideleClassNorm F).ker ↦ (χ (u : C[F]) : ℂ)) :=
    continuous_subtype_val.comp (χ.continuous.comp continuous_subtype_val)
  have hFc (y : ℝ) : Continuous (fun u : (ideleClassNorm F).ker ↦
      f.val (β y * (u : C[F])) * (χ (u : C[F]) : ℂ)) :=
    (hfc.comp (continuous_const.mul continuous_subtype_val)).mul hχc
  have hF'c (y : ℝ) : Continuous (fun u : (ideleClassNorm F).ker ↦
      D (β y * (u : C[F])) * (χ (u : C[F]) : ℂ)) :=
    (hDc.comp (continuous_const.mul continuous_subtype_val)).mul hχc
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := normOneIdeleClassTamagawaMeasure F)
    (F := fun y u ↦ f.val (β y * (u : C[F])) * (χ (u : C[F]) : ℂ))
    (F' := fun y u ↦ D (β y * (u : C[F])) * (χ (u : C[F]) : ℂ)) (x₀ := x)
    (bound := fun _ ↦ C) (Metric.ball_mem_nhds x one_pos)
    (.of_forall fun y ↦ (hFc y).aestronglyMeasurable)
    ((hFc x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hF'c x).aestronglyMeasurable
    (.of_forall fun u y _ ↦ by
      simp only [norm_mul, Circle.norm_coe, mul_one]
      exact hC _)
    (integrable_const C)
    (.of_forall fun u y _ ↦ (hdt u y).mul_const _)
  exact hmain.2

/-- The radial profile of a test along a one-parameter subgroup is smooth. -/
private theorem explicitFormula_radial_contDiff (b : Multiplicative ℝ →ₜ* C[F]) (χ : U[F])
    (n : ℕ) : ∀ f : 𝒟(C[F]), ContDiff ℝ n (fun y : ℝ ↦ ∫ u,
      f.val (b (Multiplicative.ofAdd y) * (u : C[F])) * (χ (u : C[F]) : ℂ)
        ∂normOneIdeleClassTamagawaMeasure F) := by
  induction n with
  | zero =>
    intro f
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x ↦
      (explicitFormula_radial_hasDerivAt b χ f x).continuousAt)
  | succ n ih =>
    intro f
    let f' : 𝒟(C[F]) := ⟨bruhatDirectionalDeriv b f.val, explicitFormula_flowDeriv_mem b f⟩
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (explicitFormula_radial_hasDerivAt b χ f x).differentiableAt,
      fun h ↦ absurd h (by simp), ?_⟩
    have hd : deriv (fun y : ℝ ↦ ∫ u, f.val (b (Multiplicative.ofAdd y) * (u : C[F])) *
        (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) = fun y : ℝ ↦ ∫ u,
          f'.val (b (Multiplicative.ofAdd y) * (u : C[F])) * (χ (u : C[F]) : ℂ)
            ∂normOneIdeleClassTamagawaMeasure F :=
      funext fun x ↦ (explicitFormula_radial_hasDerivAt b χ f x).deriv
    rw [hd]
    exact ih f'

end ExplicitFormulaRadialProfile

/-- Paper: Theorem B.4.4.7, pp. 623–624 (the decomposition `C[F] = C¹ × ℝ_{>0}` and the
character expansion of the test). For a test `f` on the idele classes, a continuous section `τ`
of the class norm and a unitary character `χ`, the radial profile
`x ↦ c · ∫_{C¹} f(τ(eˣ) u) χ(u) du` (any constant `c`) is an exponentially decaying Schwartz
function of the logarithmic variable `x`: it is smooth because `f` is smooth along the
one-parameter subgroup `x ↦ τ(eˣ)`, and compactly supported because the class norm is proper. -/
theorem idelicExplicitFormula_radialProfile (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (χ : U[F]) (c : ℂ) :
    ∃ Φ : 𝓢(ℝ, ℂ), ExponentialDecay Φ ∧ ∀ x : ℝ, Φ x = c *
      ∫ u, f.val (radialFlow(τ, x) * (u : C[F])) * (χ (u : C[F]) : ℂ)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let b : Multiplicative ℝ →ₜ* C[F] :=
    ⟨τ.toMonoidHom.comp positiveRealLogEquiv.symm.toMulEquiv.toMonoidHom,
      τ.continuous.comp positiveRealLogEquiv.symm.continuous⟩
  let I : ℝ → ℂ := fun y ↦ ∫ u, f.val (b (Multiplicative.ofAdd y) * (u : C[F])) *
    (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F
  have hI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) I :=
    contDiff_infty.mpr fun n ↦ explicitFormula_radial_contDiff b χ n f
  -- Compact support: the class norm of `b(eʸ) u` is `eʸ`, and `f` has compact support.
  let N : C[F] → ℝ := fun g ↦ ((ideleClassNorm F g).val : ℝ)
  have hNpos (g : C[F]) : 0 < N g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hNc : Continuous N := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hN (y : ℝ) (u : (ideleClassNorm F).ker) :
      Real.log (N (b (Multiplicative.ofAdd y) * (u : C[F]))) = y := by
    change Real.log (((ideleClassNorm F (τ (positiveRealLogEquiv.symm
      (Multiplicative.ofAdd y)) * (u : C[F]))).val : ℝ)) = y
    rw [map_mul, _hτ, MonoidHom.mem_ker.mp u.property, mul_one]
    have h := positiveRealLogEquiv_apply (positiveRealLogEquiv.symm (Multiplicative.ofAdd y))
    rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact h.symm
  have hIc : HasCompactSupport I := by
    refine HasCompactSupport.intro (f.property.2.isCompact.image
      (hNc.log fun g ↦ (hNpos g).ne')) fun y hy ↦ ?_
    refine integral_eq_zero_of_ae (.of_forall fun u ↦ ?_)
    have hu : b (Multiplicative.ofAdd y) * (u : C[F]) ∉ tsupport f.val := fun hmem ↦
      hy ⟨_, hmem, hN y u⟩
    simp only [image_eq_zero_of_notMem_tsupport hu, zero_mul, Pi.zero_apply]
  let Φ : 𝓢(ℝ, ℂ) := c • hIc.toSchwartzMap hI
  have hΦ (x : ℝ) : Φ x = c * I x := rfl
  have hΦc : HasCompactSupport (Φ : ℝ → ℂ) := by
    rw [show (Φ : ℝ → ℂ) = fun x ↦ c * I x from funext hΦ]
    exact hIc.mul_left
  have hz (j : ℕ) : iteratedDeriv j (Φ : ℝ → ℂ) =ᶠ[cocompact ℝ] 0 := by
    have hh := hΦc.iteratedFDeriv (𝕜 := ℝ) j
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hh
    filter_upwards [hh] with x hx
    rw [iteratedDeriv_eq_iteratedFDeriv, hx]
    rfl
  exact ⟨Φ, ⟨fun j _ _ ↦ ((hz j).filter_mono atTop_le_cocompact).trans_isBigO
    (Asymptotics.isBigO_zero _ _), fun j _ _ ↦ ((hz j).filter_mono atBot_le_cocompact).trans_isBigO
    (Asymptotics.isBigO_zero _ _)⟩, hΦ⟩


section ExplicitFormulaMellinMatching

/-- The log-Mellin transform is the two-sided Laplace transform. -/
private theorem explicitFormula_logMellin_eq (I : ℝ → ℂ) (w : ℂ) :
    mellin (fun t ↦ I (Real.log t)) w = ∫ x : ℝ, Complex.exp (w * x) * I x := by
  rw [mellin, ← integral_comp_exp]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- The exponential flow into the positive real units carries Lebesgue measure to `dt/t`. -/
private theorem explicitFormula_positiveRealHaar_integral (h : ℝ≥0ˣ → ℂ) :
    ∫ t, h t ∂positiveRealHaar =
      ∫ x : ℝ, h (positiveRealLogEquiv.symm (Multiplicative.ofAdd x)) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hE : positiveRealHaar = volume.map E := by
    apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
    funext y
    exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le))
  have hEx (x : ℝ) : E x = positiveRealLogEquiv.symm (Multiplicative.ofAdd x) := by
    apply positiveRealLogEquiv.injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    rw [positiveRealLogEquiv_apply, toAdd_ofAdd]
    change Real.log (Real.exp x) = x
    exact Real.log_exp x
  rw [hE, E.isClosedEmbedding.measurableEmbedding.integral_map]
  simp only [hEx]

/-- Fubini over `C[F] = ℝ_{>0} × C¹` along a norm section, in logarithmic coordinates. -/
private theorem explicitFormula_mellin_radial (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (χ : U[F])
    (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (s : ℂ) :
    ∫ g, classMellinIntegrand(f, ideleClassNormTwist χ s, -1 / 2) g ∂classMeasure =
      ∫ x : ℝ, Complex.exp ((s - 1 / 2) * x) *
        ∫ u, f.val (radialFlow(τ, x) * (u : C[F])) * (χ (u : C[F]) : ℂ)
          ∂normOneIdeleClassTamagawaMeasure F := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  have : IsFiniteMeasure (normOneIdeleClassTamagawaMeasure F) :=
    ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  let : (classMeasure).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let w : ℂ := s - 1 / 2
  let c : C[F] →ₜ* ℂ := ideleClassNormTwist χ w
  have hc (g : C[F]) : ideleClassNormTwist χ s g * classWeight(g, -1 / 2) = c g := by
    have hpos : (((ideleClassNorm F g).val : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change ((χ g : Circle) : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ s *
        (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-1 / 2 : ℂ) =
      ((χ g : Circle) : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w
    rw [mul_assoc, ← Complex.cpow_add _ _ hpos]
    congr 2
    simp only [w]
    ring
  let H : C[F] → ℂ := fun g ↦ f.val g * c g
  have hH : (fun g ↦ classMellinIntegrand(f, ideleClassNormTwist χ s, -1 / 2) g) = H := by
    funext g
    change f.val g * ideleClassNormTwist χ s g * classWeight(g, -1 / 2) = f.val g * c g
    rw [mul_assoc, hc]
  have hHc : Continuous H := (explicitTest_continuous f).mul c.continuous
  have hHi : Integrable H classMeasure :=
    hHc.integrable_of_hasCompactSupport f.property.2.mul_right
  let j : ℝ≥0ˣ × (ideleClassNorm F).ker → C[F] := fun p ↦ τ p.1 * p.2.val
  have hjc : Continuous j :=
    (τ.continuous.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  -- The Tamagawa measure on `C¹` lives on the subtype σ-algebra, not on the local Borel one.
  let mK : MeasurableSpace (ideleClassNorm F).ker := Subtype.instMeasurableSpace
  have hO : @OpensMeasurableSpace (ideleClassNorm F).ker _ mK :=
    Subtype.opensMeasurableSpace (α := C[F]) _
  have hPO : @OpensMeasurableSpace (ℝ≥0ˣ × (ideleClassNorm F).ker) _
      (@Prod.instMeasurableSpace _ _ _ mK) :=
    @Prod.opensMeasurableSpace ℝ≥0ˣ (ideleClassNorm F).ker _ _ _ _ mK hO _
  have hj : @Measurable _ _ (@Prod.instMeasurableSpace _ _ _ mK) _ j :=
    @Continuous.measurable _ _ _ (@Prod.instMeasurableSpace _ _ _ mK) hPO _ _ _ j hjc
  have hprod := classTamagawa_normProduct (fun t ↦ τ t) τ.continuous hτ
  rw [← hprod] at hHi
  rw [hH, ← hprod]
  rw [integral_map hj.aemeasurable hHc.aestronglyMeasurable]
  have hHi' : Integrable (H ∘ j)
      (positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)) :=
    (integrable_map_measure hHc.aestronglyMeasurable hj.aemeasurable).mp hHi
  refine (integral_prod (fun z ↦ H (j z)) hHi').trans ?_
  rw [explicitFormula_positiveRealHaar_integral]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  let t : ℝ≥0ˣ := positiveRealLogEquiv.symm (Multiplicative.ofAdd x)
  have ht : ((t : ℝ≥0) : ℝ) = Real.exp x := by
    have h := positiveRealLogEquiv_apply t
    rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))).symm.trans
      (congrArg Real.exp h.symm)
  have hpt (u : (ideleClassNorm F).ker) : H (j (t, u)) =
      Complex.exp (w * x) * (f.val (τ t * (u : C[F])) * (χ (u : C[F]) : ℂ)) := by
    have hn : ideleClassNorm F (τ t * u.val) = t := by
      rw [map_mul, hτ t, MonoidHom.mem_ker.mp u.property, mul_one]
    change f.val (τ t * u.val) * (((χ (τ t * u.val) : Circle) : ℂ) *
      (((ideleClassNorm F (τ t * u.val)).val : ℝ) : ℂ) ^ w) = _
    rw [hn, ht, map_mul, hχ, one_mul, Complex.ofReal_exp,
      Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    ring_nf
  exact (integral_congr_ae (.of_forall hpt)).trans (integral_const_mul _ _)

end ExplicitFormulaMellinMatching

/-- Paper: Theorem B.4.4.7, pp. 623–624 (Fubini for `C[F] = C¹ × ℝ_{>0}`). For a character
`χ` trivial on the image of the norm section `τ`, the idelic Mellin integral of a test `f`
against `χ |·|^(s - 1/2)`, divided by the volume of `C¹`, is the Mellin transform at
`s - 1/2` of the radial profile `x ↦ c · ∫_{C¹} f(τ(eˣ) u) χ(u) du`, for one constant `c`
(fixed by the normalization of the Tamagawa measures) and all `s`. -/
theorem idelicExplicitFormula_mellinMatching (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (χ : U[F])
    (_hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) :
    ∃ c : ℂ, ∀ s : ℂ,
      (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ s, -1 / 2) g ∂classMeasure) /
          (classVolume : ℂ) =
        logMellin (fun x ↦ c * ∫ u, f.val (radialFlow(τ, x) * (u : C[F])) *
          (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) (s - 1 / 2) := by
  refine ⟨1 / (classVolume : ℂ), fun s ↦ ?_⟩
  refine Eq.trans ?_ (explicitFormula_logMellin_eq (fun x ↦ 1 / (classVolume : ℂ) *
    ∫ u, f.val (radialFlow(τ, x) * (u : C[F])) * (χ (u : C[F]) : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F) (s - 1 / 2)).symm
  rw [explicitFormula_mellin_radial τ _hτ f χ _hχ s, div_eq_mul_one_div, mul_comm,
    ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  ring

section ExplicitFormulaPoles

/-- A twist `χ |·|^0 = |·|^(-it)` of a character trivial on the image of a section of the class
norm forces `t = 0`. -/
private theorem explicitFormula_twist_param_eq_zero (σ : ℝ≥0ˣ → C[F])
    (hσ : ∀ r, ideleClassNorm F (σ r) = r) (χ : U[F])
    (hχ : ∀ r, χ (σ r) = 1) (t : ℝ)
    (h : ideleClassNormTwist χ 0 = ideleClassNormTwist 1 (-Complex.I * (t : ℂ))) : t = 0 := by
  by_contra ht
  let x : ℝ := Real.pi / t
  let r : ℝ≥0ˣ := Units.mk0 ⟨Real.exp x, (Real.exp_pos x).le⟩
    (by intro h0; exact (Real.exp_pos x).ne' (congrArg Subtype.val h0))
  have hg := congrArg (fun φ ↦ φ (σ r)) h
  change ((χ (σ r) : Circle) : ℂ) * (((ideleClassNorm F (σ r) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
    (((1 : U[F]) (σ r) : Circle) : ℂ) *
      (((ideleClassNorm F (σ r) : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ)) at hg
  rw [hχ, hσ] at hg
  have hr : (((r : ℝ≥0) : ℝ) : ℂ) = ((Real.exp x : ℝ) : ℂ) := rfl
  have h1c : (((1 : U[F]) (σ r) : Circle) : ℂ) = 1 := rfl
  rw [hr, h1c, Complex.cpow_zero, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'), ← Complex.ofReal_log (Real.exp_pos x).le,
    Real.log_exp] at hg
  have h1 : (x : ℂ) * (-Complex.I * t) = -(Real.pi * Complex.I) := by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    simp only [x]; push_cast; field_simp
  simp only [Circle.coe_one, one_mul, mul_one, h1] at hg
  rw [Complex.exp_neg, Complex.exp_pi_mul_I] at hg
  norm_num at hg

/-- At a point of analyticity the divisor of a function in normal form is nonnegative. -/
private theorem explicitFormula_divisor_nonneg_of_analyticAt {L : ℂ → ℂ} (hL : MeromorphicNFOn L univ) (ρ : ℂ) (h : AnalyticAt ℂ L ρ) :
    0 ≤ MeromorphicOn.divisor L univ ρ := by
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ ρ)]
  have h0 := h.meromorphicOrderAt_nonneg
  generalize meromorphicOrderAt L ρ = o at h0 ⊢
  cases o with
  | top => simp
  | coe n => simpa using h0

end ExplicitFormulaPoles

/-- Paper: Theorem B.4.4.7, p. 624, with Proposition 3.2.1.3, p. 123. For a character trivial
on the image of the norm section `τ`, the continued completed Hecke L-function has a pole only
when the character is trivial, and then only at `0` and `1`. -/
theorem idelicExplicitFormula_chart_poles (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (χ : U[F]) (_hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1)
    (ρ : ℂ) (_hρ : MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ ρ < 0) :
    χ = 1 ∧ (ρ = 0 ∨ ρ = 1) := by
  obtain ⟨hL, hAgree⟩ := explicitFormulaCompletedHeckeL_spec χ
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨ht, -, -, han⟩, -⟩ := completedHeckeL_continuation_simplePoles χ _ hL hAgree hχ
    obtain rfl := explicitFormula_twist_param_eq_zero τ _hτ χ _hχ t ht
    refine ⟨ContinuousMonoidHom.ext fun g ↦ Circle.ext ?_, ?_⟩
    · have hg := congrArg (fun φ ↦ φ g) ht
      change (χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
        (((1 : U[F]) g : Circle) : ℂ) *
          (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I * ((0 : ℝ) : ℂ)) at hg
      simp only [Complex.cpow_zero, mul_one, Complex.ofReal_zero, mul_zero] at hg
      exact hg
    · by_contra hne
      have hA := han ρ (by simp only [Complex.ofReal_zero, mul_zero, add_zero]; simpa [not_or] using hne)
      exact (not_le.mpr _hρ) (explicitFormula_divisor_nonneg_of_analyticAt hL ρ hA)
  · exact absurd _hρ (not_lt.mpr (explicitFormula_divisor_nonneg_of_analyticAt hL ρ
      ((completedHeckeL_continuation_entire χ _ hL hAgree hχ).analyticAt ρ)))

/-- Paper: Theorem B.4.4.7, p. 624, with Proposition 3.2.1.3, p. 123. The continued completed
Dedekind zeta function has simple poles at `0` and `1`. -/
theorem idelicExplicitFormula_trivial_poles :
    MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (1 : U[F])) univ 0 = -1 ∧
      MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (1 : U[F])) univ 1 = -1 := by
  obtain ⟨hL, hAgree⟩ := explicitFormulaCompletedHeckeL_spec (1 : U[F])
  obtain ⟨t, ⟨ht, h0, h1, -⟩, -⟩ := completedHeckeL_continuation_simplePoles _ _ hL hAgree
    (MonoidHom.ext fun _ ↦ rfl)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, -, hσ⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  obtain rfl := explicitFormula_twist_param_eq_zero σ hσ 1 (fun _ ↦ rfl) t ht
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at h0 h1
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), h0, h1]
  exact ⟨rfl, rfl⟩

section ExplicitFormulaFiniteMatching

/-- The logarithm of the absolute discriminant is the sum over the finite places of the
different exponents weighted by the log prime norms; only finitely many terms are nonzero. -/
private theorem explicitFormula_log_discr_eq_tsum :
    Summable (fun v : Primes(F) ↦
      ((multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℝ) * Real.log q(v))) ∧
    ∑' v : Primes(F), (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℝ) * Real.log q(v) =
      Real.log (Int.natAbs (NumberField.discr F)) := by
  classical
  let J := differentIdeal ℤ (𝓞 F)
  have hJ : J ≠ ⊥ := differentIdeal_ne_bot
  let T := (Ideal.finite_factors hJ).toFinset
  let e : Primes(F) → ℕ := fun v ↦ multiplicity v.asIdeal J
  have hout (v : Primes(F)) (hv : v ∉ T) : e v = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    simpa [T, J] using hv
  have hfactor : ∏ v ∈ T, v.asIdeal ^ e v = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset
      (f := fun v : Primes(F) ↦ v.asIdeal ^ e v)]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ
    · intro v hv
      by_contra hn
      exact hv (by simp [hout v hn])
  have hnorm : (∏ v ∈ T, (↑(Ideal.absNorm v.asIdeal) : ℝ) ^ e v) =
      (↑(NumberField.discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) ↦ Ideal.absNorm I) hfactor :
      (∏ v ∈ T, Ideal.absNorm v.asIdeal ^ e v) = (NumberField.discr F).natAbs)
  have hzero (v : Primes(F)) (hv : v ∉ T) : (e v : ℝ) * Real.log q(v) = 0 := by
    rw [hout v hv, Nat.cast_zero, zero_mul]
  refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
  change ∑' v : Primes(F), (e v : ℝ) * Real.log q(v) = _
  rw [tsum_eq_sum hzero, ← hnorm, Real.log_prod (fun v _ ↦ pow_ne_zero _ (by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'))]
  exact Finset.sum_congr rfl fun v _ ↦ (Real.log_pow _ _).symm

end ExplicitFormulaFiniteMatching

section ExplicitFormulaInversion

open scoped FourierTransform in
/-- The radial profiles fixed by their Mellin transforms are the normalized `C¹`-integrals:
two Schwartz functions with the same two-sided Laplace transform on the imaginary axis have
the same Fourier transform, hence agree. -/
private theorem explicitFormula_profile_eq (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2))
    (χ : chartChars(τ)) (x : ℝ) :
    Φ χ x = (classVolume : ℂ)⁻¹ * ∫ u, f.val (radialFlow(τ, x) * (u : C[F])) *
      (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F := by
  obtain ⟨Ψ, -, hΨ⟩ := idelicExplicitFormula_radialProfile τ hτ f χ.val (classVolume : ℂ)⁻¹
  suffices h : Φ χ = Ψ by rw [h, hΨ]
  have hL (w : ℂ) : ∫ x : ℝ, Complex.exp (w * x) * Φ χ x =
      ∫ x : ℝ, Complex.exp (w * x) * Ψ x := by
    have h := hM χ (w + 1 / 2)
    rw [explicitFormula_mellin_radial τ hτ f χ.val χ.property, show w + 1 / 2 - 1 / 2 = w by ring] at h
    beta_reduce at h
    rw [explicitFormula_logMellin_eq] at h
    rw [← h, div_eq_inv_mul, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    simp only [hΨ]
    ring
  have hF : 𝓕 (Φ χ) = 𝓕 Ψ := by
    ext ξ
    change 𝓕 (Φ χ : ℝ → ℂ) ξ = 𝓕 (Ψ : ℝ → ℂ) ξ
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    have h := hL (-2 * Real.pi * ξ * Complex.I)
    simp only [smul_eq_mul]
    convert h using 3 with y y <;> push_cast <;> ring_nf
  rw [← FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) (Φ χ), hF,
    FourierTransform.fourierInv_fourier_eq]

end ExplicitFormulaInversion

section ExplicitFormulaNormOneFourier

open scoped ComplexConjugate Pointwise

/-- A nontrivial character of a group with a left invariant measure has integral `0`. -/
private theorem explicitFormula_integral_character_eq_zero {K : Type*} [CommGroup K]
    [TopologicalSpace K] {mK : MeasurableSpace K} [MeasurableMul K] (μ : Measure K)
    [μ.IsMulLeftInvariant] (ψ : PontryaginDual K) {x : K} (hx : ψ x ≠ 1) :
    ∫ y, (ψ y : ℂ) ∂μ = 0 := by
  have ht := integral_mul_left_eq_self (μ := μ) (fun y ↦ (ψ y : ℂ)) x
  simp_rw [map_mul, Circle.coe_mul, integral_const_mul] at ht
  by_contra hn
  exact hx (Circle.ext ((mul_eq_right₀ hn).mp ht))

/-- A continuous function on a compact abelian group whose integrals against every character
of a point-separating subgroup of characters vanish is zero (Stone–Weierstrass). -/
private theorem explicitFormula_eq_zero_of_integral_character {K : Type*} [CommGroup K]
    [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    {mK : MeasurableSpace K} [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (S : Subgroup (PontryaginDual K)) (hS : ∀ x : K, x ≠ 1 → ∃ ψ ∈ S, ψ x ≠ 1)
    (h : C(K, ℂ)) (hh : ∀ ψ ∈ S, ∫ x, h x * (ψ x : ℂ) ∂μ = 0) : h = 0 := by
  let r : PontryaginDual K →* C(K, ℂ) :=
    { toFun ψ := ⟨fun x ↦ (ψ x : ℂ), continuous_subtype_val.comp ψ.continuous⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let M := S.toSubmonoid.map r
  let A := StarAlgebra.adjoin ℂ (M : Set C(K, ℂ))
  have hstar : star (M : Set C(K, ℂ)) ⊆ M := by
    rw [Set.star_subset]
    rintro _ ⟨ψ, hψ, rfl⟩
    refine ⟨ψ⁻¹, S.inv_mem hψ, ContinuousMap.ext fun x ↦ ?_⟩
    change ((ψ⁻¹ x : Circle) : ℂ) = star ((ψ x : Circle) : ℂ)
    exact Circle.coe_inv_eq_conj (ψ x)
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨ψ, hψS, hψ⟩ := hS _ (div_ne_one.mpr hxy)
    refine ⟨_, ⟨r ψ, StarAlgebra.subset_adjoin ℂ (M : Set C(K, ℂ)) ⟨ψ, hψS, rfl⟩, rfl⟩, ?_⟩
    change ((ψ x : Circle) : ℂ) ≠ ψ y
    rw [Ne, Circle.coe_inj]
    exact fun he ↦ hψ ((map_div ψ _ _).trans (div_eq_one.mpr he))
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ (M : Set C(K, ℂ)) := by
    rw [StarAlgebra.adjoin_eq_span, Set.union_eq_left.mpr hstar, M.closure_eq]
  have hdense : (Submodule.span ℂ (M : Set C(K, ℂ))).topologicalClosure = ⊤ := by
    rw [← hspan]
    exact congrArg (fun S : StarSubalgebra ℂ C(K, ℂ) ↦ S.toSubalgebra.toSubmodule)
      (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep)
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let L := (innerSL ℂ (T (star h))).comp T
  have horth : Submodule.span ℂ (M : Set C(K, ℂ)) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ψ, hψ, rfl⟩
    change inner ℂ (T (star h)) (T (r ψ)) = 0
    rw [ContinuousMap.inner_toLp]
    refine (integral_congr_ae (.of_forall fun x ↦ ?_)).trans (hh ψ hψ)
    change ((ψ x : Circle) : ℂ) * conj (star (h x)) = h x * ψ x
    rw [Complex.star_def, Complex.conj_conj, mul_comm]
  have htop := (Submodule.span ℂ (M : Set C(K, ℂ))).topologicalClosure_minimal horth
    L.isClosed_ker
  rw [hdense] at htop
  have hc : inner ℂ (T (star h)) (T (star h)) = 0 := htop (Submodule.mem_top (x := star h))
  have hc0 := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ)
    ((inner_self_eq_zero.mp hc).trans (map_zero T).symm)
  rw [← star_star h, hc0, star_zero]


/-- Integration against a continuous function on a compact group, as a continuous linear map
on the continuous functions. -/
private theorem explicitFormula_exists_integralCLM {K : Type*} [TopologicalSpace K]
    [CompactSpace K] {mK : MeasurableSpace K} [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] (k : C(K, ℂ)) :
    ∃ L : C(K, ℂ) →L[ℂ] ℂ, ∀ p, L p = ∫ x, p x * k x ∂μ := by
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  refine ⟨(innerSL ℂ (T (star k))).comp T, fun p ↦ ?_⟩
  change inner ℂ (T (star k)) (T p) = _
  rw [ContinuousMap.inner_toLp]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  change p x * conj (star (k x)) = _
  rw [Complex.star_def, Complex.conj_conj]

/-- Two characters trivial on the image of the norm section agree once they agree on `C¹`. -/
private theorem explicitFormula_chartChar_ext (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (χ χ' : chartChars(τ))
    (h : ∀ u : (ideleClassNorm F).ker, χ.val (u : C[F]) = χ'.val (u : C[F])) : χ = χ' := by
  refine Subtype.ext (DFunLike.ext _ _ fun g ↦ ?_)
  have hg : (τ (ideleClassNorm F g))⁻¹ * g ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτ, inv_mul_cancel]
  have h1 := h ⟨_, hg⟩
  simp only [map_mul, map_inv, χ.2, χ'.2, inv_one, one_mul] at h1
  exact h1

/-- Every character of `C[F]` agrees on `C¹` with a character trivial on the image of the
norm section. -/
private theorem explicitFormula_exists_chartChar (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : U[F]) :
    ∃ χ : chartChars(τ), ∀ u : (ideleClassNorm F).ker, χ.val (u : C[F]) = ψ (u : C[F]) := by
  let N : C[F] →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let ψτ : U[F] := (ψ : C[F] →ₜ* Circle).comp (τ.comp N)
  refine ⟨⟨ψ * ψτ⁻¹, fun t ↦ ?_⟩, fun u ↦ ?_⟩
  · change ψ (τ t) * (ψ (τ (ideleClassNorm F (τ t))))⁻¹ = 1
    rw [hτ, mul_inv_cancel]
  · change ψ (u : C[F]) * (ψ (τ (ideleClassNorm F (u : C[F]))))⁻¹ = ψ (u : C[F])
    rw [MonoidHom.mem_ker.mp u.property, map_one, map_one, inv_one, mul_one]

/-- Orthogonality of the characters trivial on the image of the norm section, on `C¹`. -/
private theorem explicitFormula_integral_chartChar_inv_mul (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (χ χ' : chartChars(τ)) :
    ∫ u, ((χ.val⁻¹ (u : C[F]) : Circle) : ℂ) * (χ'.val (u : C[F]) : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F = if χ = χ' then (classVolume : ℂ) else 0 := by
  let K := (ideleClassNorm F).ker
  let μ := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let mK : MeasurableSpace K := Subtype.instMeasurableSpace
  have hB : @BorelSpace K _ mK := Subtype.borelSpace _
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have : @MeasurableMul K mK _ := @ContinuousMul.measurableMul _ _ mK hB _ _
  split_ifs with hχ
  · subst hχ
    have h1 (x : K) : ((χ.val⁻¹ (x : C[F]) : Circle) : ℂ) * (χ.val (x : C[F]) : ℂ) = 1 := by
      change ((((χ.val (x : C[F]))⁻¹ * χ.val (x : C[F]) : Circle)) : ℂ) = 1
      rw [inv_mul_cancel, Circle.coe_one]
    refine (integral_congr_ae (.of_forall h1)).trans ?_
    rw [integral_const, Complex.real_smul, mul_one]
    rfl
  · obtain ⟨u, hu⟩ : ∃ u : K, χ.val (u : C[F]) ≠ χ'.val (u : C[F]) := by
      by_contra! h
      exact hχ (explicitFormula_chartChar_ext τ hτ χ χ' h)
    let δ : PontryaginDual K :=
      PontryaginDual.map ⟨K.subtype, continuous_subtype_val⟩ (χ.val⁻¹ * χ'.val)
    have hδ : δ u ≠ 1 := by
      change (χ.val (u : C[F]))⁻¹ * χ'.val (u : C[F]) ≠ 1
      rw [Ne, inv_mul_eq_one]
      exact hu
    refine (integral_congr_ae (.of_forall fun x ↦ ?_)).trans
      (@explicitFormula_integral_character_eq_zero K _ _ mK _ μ _ δ u hδ)
    change ((χ.val⁻¹ (x : C[F]) : Circle) : ℂ) * (χ'.val (x : C[F]) : ℂ) =
      (((χ.val (x : C[F]))⁻¹ * χ'.val (x : C[F]) : Circle) : ℂ)
    rw [Circle.coe_mul]
    rfl

end ExplicitFormulaNormOneFourier

section BruhatMellinPolynomialCountCombinatorics

/-- The model series `1/1^2 + 1/2^2 + ...` has partial sums bounded by two. -/
private theorem summable_bruhatMellin_of_polynomialCount_sum_inv_sq_range (n : ℕ) :
    ∑ t ∈ Finset.range n, (((t : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have key : ∀ m : ℕ,
      ∑ t ∈ Finset.range m, (((t : ℝ) + 1) ^ 2)⁻¹ ≤ 2 - (m : ℝ)⁻¹ := by
    intro m
    induction m with
    | zero => norm_num
    | succ p ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos p with hp0 | hp
      · subst hp0
        norm_num
      · have hstep : (((p : ℝ) + 1) ^ 2)⁻¹ ≤ (p : ℝ)⁻¹ - ((p : ℝ) + 1)⁻¹ := by
          have h1 : (p : ℝ) ≠ 0 := by positivity
          have h2 : (p : ℝ) + 1 ≠ 0 := by positivity
          field_simp
          nlinarith
        have hcast : ((p + 1 : ℕ) : ℝ)⁻¹ = ((p : ℝ) + 1)⁻¹ := by
          push_cast
          ring
        rw [hcast]
        linarith
  exact (key n).trans (by
    have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    linarith)

/-- Absorbing polynomial growth into the quadratic decay. -/
private theorem summable_bruhatMellin_of_polynomialCount_pow_add_div_pow (x : ℝ) (hx : 1 ≤ x)
    (k : ℕ) : (x + 1) ^ k / x ^ (k + 2) ≤ (2 : ℝ) ^ k / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have habs : (x + 1) ^ k ≤ (2 : ℝ) ^ k * x ^ k := by
    have hle : x + 1 ≤ 2 * x := by linarith
    calc (x + 1) ^ k ≤ (2 * x) ^ k := pow_le_pow_left₀ (by linarith) hle k
      _ = (2 : ℝ) ^ k * x ^ k := mul_pow _ _ _
  have hxp : (0 : ℝ) < x ^ (k + 2) := pow_pos hx0 _
  have hx2 : (0 : ℝ) < x ^ 2 := pow_pos hx0 2
  rw [div_le_div_iff₀ hxp hx2]
  calc (x + 1) ^ k * x ^ 2 ≤ ((2 : ℝ) ^ k * x ^ k) * x ^ 2 :=
        mul_le_mul_of_nonneg_right habs (le_of_lt hx2)
    _ = (2 : ℝ) ^ k * x ^ (k + 2) := by rw [pow_add]; ring

/-- An inverse power decreases when the base increases. -/
private theorem summable_bruhatMellin_of_polynomialCount_mul_inv_pow_le {K x t : ℝ} (hK : 0 ≤ K)
    (ht : 0 < t) (htx : t ≤ x) (k : ℕ) : K / x ^ (k + 1) ≤ K / t ^ (k + 1) := by
  have hx : (0 : ℝ) < x := lt_of_lt_of_le ht htx
  have hmono : t ^ (k + 1) ≤ x ^ (k + 1) := pow_le_pow_left₀ (le_of_lt ht) htx _
  have htp : (0 : ℝ) < t ^ (k + 1) := pow_pos ht _
  have hxp : (0 : ℝ) < x ^ (k + 1) := pow_pos hx _
  rw [div_le_div_iff₀ hxp htp]
  calc K * t ^ (k + 1) ≤ K * x ^ (k + 1) := mul_le_mul_of_nonneg_left hmono hK
    _ = K * x ^ (k + 1) := rfl

/-- Paper: Lemma B.4.4.8, p. 624. Counting the level sets of the height
`max |Im s| (max_j |n_j|)` polynomially and having quadratic decay in that height
forces summability. This is the combinatorial half of Lemma B.4.4.8. -/
private theorem summable_bruhatMellin_of_polynomialCount_of_polyCount_decay
    {ι : Type*} (m : ι → ℝ) (hm : ∀ z, 0 ≤ m z) (C k : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (g : ι → ℝ)
    (hcount : ∀ T : ℕ, {z : ι | m z ≤ (T : ℝ)}.encard ≤ ((C * (T + 1) ^ k : ℕ) : ℕ∞))
    (hdecay : ∀ z, ‖g z‖ ≤ K / (1 + m z) ^ (k + 2)) :
    Summable g := by
  classical
  set S : ι → ℕ := fun z => Nat.ceil (m z) with hSdef
  have hSle (z : ι) : m z ≤ (S z : ℝ) := Nat.le_ceil (m z)
  have hmzle : ∀ {z : ι} {t : ℕ}, S z = t → m z ≤ (t : ℝ) := by
    intro z t hz
    calc m z ≤ (S z : ℝ) := hSle z
      _ = (t : ℝ) := by rw [hz]
  have hfin : ∀ T : ℕ, {z : ι | S z ≤ T}.Finite := by
    intro T
    exact Set.finite_of_encard_le_coe
      ((Set.encard_mono fun z hz => (hSle z).trans (by exact_mod_cast hz)).trans (hcount T))
  have hcard : ∀ t : ℕ, {z : ι | S z = t}.encard ≤ ((C * (t + 1) ^ k : ℕ) : ℕ∞) := by
    intro t
    have hsub : {z : ι | S z = t} ⊆ {z : ι | m z ≤ (t : ℝ)} := by
      intro z hz
      exact hmzle hz
    exact (Set.encard_mono hsub).trans (hcount t)
  have hfibercard : ∀ (t : ℕ) (u : Finset ι), (∀ z ∈ u, S z = t) →
      (u.card : ℝ) ≤ (C : ℝ) * (t + 1) ^ k := by
    intro t u hu
    have hcoe : ((u.card : ℕ) : ℕ∞) = (u : Set ι).encard :=
      (Set.encard_coe_eq_coe_finsetCard u).symm
    have hle : (u : Set ι).encard ≤ {z : ι | S z = t}.encard :=
      Set.encard_mono fun z hz => hu z hz
    have hnat : u.card ≤ C * (t + 1) ^ k := by
      have : ((u.card : ℕ) : ℕ∞) ≤ ((C * (t + 1) ^ k : ℕ) : ℕ∞) := by
        rw [hcoe]
        exact hle.trans (hcard t)
      exact_mod_cast this
    exact_mod_cast hnat
  -- decay of one term, with the level value in the base
  have hterm : ∀ (t : ℕ) (z : ι), S z = t → ‖g z‖ ≤ K / (max (t : ℝ) 1) ^ (k + 2) := by
    intro t z hz
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · have hmz : m z = 0 := le_antisymm (by simpa [ht0] using hmzle hz) (hm z)
      have hmax : max (t : ℝ) 1 = 1 := by simp [ht0]
      have hthis := hdecay z
      rw [hmax] at ⊢
      simp only [hmz, add_zero, one_pow, div_one] at hthis ⊢
      exact hthis
    · have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast htpos
      have hmax : max (t : ℝ) 1 = (t : ℝ) := max_eq_left ht1
      have hmet : ((t : ℝ) - 1) < m z := by
        by_contra hcon
        have hcon' : m z ≤ (t : ℝ) - 1 := not_lt.mp hcon
        have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
          push_cast [show 1 ≤ t from htpos]
          ring
        have hle : S z ≤ t - 1 := by
          rw [hSdef]
          exact Nat.ceil_le.mpr (by rw [hcast]; exact hcon')
        omega
      have htm : (t : ℝ) ≤ 1 + m z := by linarith
      have htpos' : (0 : ℝ) < (t : ℝ) := by linarith
      rw [hmax]
      exact (hdecay z).trans
        (summable_bruhatMellin_of_polynomialCount_mul_inv_pow_le hK htpos' htm (k + 1))
  -- the contribution of one level
  have hshell : ∀ (t : ℕ) (u : Finset ι), (∀ z ∈ u, S z = t) →
      ∑ z ∈ u, ‖g z‖ ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by
    intro t u hu
    have hcard' := hfibercard t u hu
    have hC : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
    have hCK : (0 : ℝ) ≤ (C : ℝ) * K := mul_nonneg hC hK
    have hnn : (0 : ℝ) ≤ K / (max (t : ℝ) 1) ^ (k + 2) :=
      div_nonneg hK (by positivity)
    have hsum : ∑ z ∈ u, ‖g z‖ ≤ (u.card : ℝ) * (K / (max (t : ℝ) 1) ^ (k + 2)) := by
      calc ∑ z ∈ u, ‖g z‖ ≤ ∑ _z ∈ u, (K / (max (t : ℝ) 1) ^ (k + 2)) :=
            Finset.sum_le_sum (fun z hz => hterm t z (hu z hz))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · have hmax : max (t : ℝ) 1 = 1 := by simp [ht0]
      have hcard0 : (u.card : ℝ) ≤ (C : ℝ) := by simpa [ht0] using hcard'
      have h1 : ∑ z ∈ u, ‖g z‖ ≤ (C : ℝ) * K := by
        calc ∑ z ∈ u, ‖g z‖ ≤ (u.card : ℝ) * (K / (max (t : ℝ) 1) ^ (k + 2)) := hsum
          _ = (u.card : ℝ) * K := by rw [hmax]; norm_num
          _ ≤ (C : ℝ) * K := mul_le_mul_of_nonneg_right hcard0 hK
      refine h1.trans ?_
      rw [show (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹
          = (C : ℝ) * K * ((2 : ℝ) ^ k * 4) by rw [ht0]; ring]
      have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ k * 4 := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith
      calc (C : ℝ) * K = (C : ℝ) * K * 1 := by ring
        _ ≤ (C : ℝ) * K * ((2 : ℝ) ^ k * 4) := mul_le_mul_of_nonneg_left h4 hCK
    · have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast htpos
      have hmax : max (t : ℝ) 1 = (t : ℝ) := max_eq_left ht1
      have hstep : ((t : ℝ) + 1) ^ k / (t : ℝ) ^ (k + 2) ≤ (2 : ℝ) ^ k / (t : ℝ) ^ 2 :=
        summable_bruhatMellin_of_polynomialCount_pow_add_div_pow (t : ℝ) ht1 k
      have h4 : ((t : ℝ) ^ 2)⁻¹ ≤ 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by
        have h1 : ((t : ℝ) + 1) ^ 2 * ((t : ℝ) ^ 2)⁻¹ ≤ 4 := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg ((t : ℝ) - 1)]
        have hq' : (0 : ℝ) ≤ (((t : ℝ) + 1) ^ 2)⁻¹ := by positivity
        calc ((t : ℝ) ^ 2)⁻¹
            = (((t : ℝ) + 1) ^ 2)⁻¹ * (((t : ℝ) + 1) ^ 2 * ((t : ℝ) ^ 2)⁻¹) := by
              field_simp
          _ ≤ (((t : ℝ) + 1) ^ 2)⁻¹ * 4 := mul_le_mul_of_nonneg_left h1 hq'
          _ = 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by ring
      have hnn' : (0 : ℝ) ≤ K / (t : ℝ) ^ (k + 2) :=
        div_nonneg hK (by positivity)
      calc ∑ z ∈ u, ‖g z‖ ≤ (u.card : ℝ) * (K / (max (t : ℝ) 1) ^ (k + 2)) := hsum
        _ = (u.card : ℝ) * (K / (t : ℝ) ^ (k + 2)) := by rw [hmax]
        _ ≤ ((C : ℝ) * ((t : ℝ) + 1) ^ k) * (K / (t : ℝ) ^ (k + 2)) :=
            mul_le_mul_of_nonneg_right hcard' hnn'
        _ = (C : ℝ) * K * (((t : ℝ) + 1) ^ k / (t : ℝ) ^ (k + 2)) := by ring
        _ ≤ (C : ℝ) * K * ((2 : ℝ) ^ k / (t : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep hCK
        _ = (C : ℝ) * K * (2 : ℝ) ^ k * ((t : ℝ) ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ (C : ℝ) * K * (2 : ℝ) ^ k * (4 * (((t : ℝ) + 1) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by ring
  -- assemble
  have hbound : ∀ u : Finset ι, ∑ z ∈ u, ‖g z‖ ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 8 := by
    intro u
    set T := u.sup S with hTdef
    have hTu : ∀ z ∈ u, S z ≤ T := fun z hz => Finset.le_sup (f := S) hz
    have hbox : u ⊆ (hfin T).toFinset := by
      intro z hz
      rw [Set.Finite.mem_toFinset]
      exact hTu z hz
    have hmaps : ∀ z ∈ (hfin T).toFinset, S z ∈ Finset.range (T + 1) := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le hz
    have step1 : ∑ z ∈ u, ‖g z‖ ≤ ∑ z ∈ (hfin T).toFinset, ‖g z‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _ => norm_nonneg _)
    have step2 : ∑ z ∈ (hfin T).toFinset, ‖g z‖
        = ∑ t ∈ Finset.range (T + 1),
            ∑ z ∈ (hfin T).toFinset.filter (fun z => S z = t), ‖g z‖ :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    have step3 : ∑ t ∈ Finset.range (T + 1),
          ∑ z ∈ (hfin T).toFinset.filter (fun z => S z = t), ‖g z‖
        ≤ ∑ t ∈ Finset.range (T + 1),
            (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by
      refine Finset.sum_le_sum (fun t _ => ?_)
      exact hshell t _ (fun z hz => (Finset.mem_filter.mp hz).2)
    refine (step1.trans (step2.le.trans step3)).trans ?_
    rw [← Finset.mul_sum]
    have h0 : (0 : ℝ) ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 4 := by positivity
    calc (C : ℝ) * K * (2 : ℝ) ^ k * 4 *
          ∑ t ∈ Finset.range (T + 1), (((t : ℝ) + 1) ^ 2)⁻¹
        ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 4 * 2 :=
          mul_le_mul_of_nonneg_left
            (summable_bruhatMellin_of_polynomialCount_sum_inv_sq_range (T + 1)) h0
      _ = (C : ℝ) * K * (2 : ℝ) ^ k * 8 := by ring
  exact Summable.of_norm (summable_of_sum_le (fun z => norm_nonneg _) hbound)

end BruhatMellinPolynomialCountCombinatorics

section ExplicitFormulaNormOneDecay

/-- The Fourier coefficient on `C¹` of a test invariant under a norm-one class `w` vanishes
at every character nontrivial at `w`. -/
private theorem explicitFormula_coeff_eq_zero_of_invariant (f : 𝒟(C[F])) (χ : U[F])
    (w : (ideleClassNorm F).ker) (hw : ∀ g : C[F], f.val (g * w) = f.val g)
    (hχ : χ (w : C[F]) ≠ 1) :
    ∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F = 0 := by
  let mK : MeasurableSpace (ideleClassNorm F).ker := Subtype.instMeasurableSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : BorelSpace C[F] := ⟨rfl⟩
  have hB : @BorelSpace (ideleClassNorm F).ker _ mK := Subtype.borelSpace _
  have : @MeasurableMul (ideleClassNorm F).ker mK _ := @ContinuousMul.measurableMul _ _ mK hB _ _
  set I := ∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F
    with hIdef
  have hI : I = (χ (w : C[F]) : ℂ) * I := by
    rw [← integral_const_mul]
    refine (integral_mul_left_eq_self (μ := normOneIdeleClassTamagawaMeasure F)
      (fun u : (ideleClassNorm F).ker ↦ f.val (u : C[F]) * (χ (u : C[F]) : ℂ)) w).symm.trans ?_
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    simp only [Subgroup.coe_mul, map_mul, Circle.coe_mul]
    rw [mul_comm (w : C[F]) (u : C[F]), hw]
    ring
  have hχw : (χ (w : C[F]) : ℂ) ≠ 1 := fun h ↦ hχ (Circle.ext h)
  have : (1 - (χ (w : C[F]) : ℂ)) * I = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχw.symm)

/-- Integration by parts on `C¹` along a one-parameter subgroup `b` with values in `C¹`: the
Fourier coefficient of the derivative of a test along `b` is `-κ` times that of the test, where
`κ` is the derivative of `t ↦ χ(b(t))` at `0`. -/
private theorem explicitFormula_normOne_coeff_flowDeriv (b : Multiplicative ℝ →ₜ* C[F])
    (hb : ∀ t, b t ∈ (ideleClassNorm F).ker) (χ : U[F]) (f : 𝒟(C[F])) :
    ∫ u, bruhatDirectionalDeriv b f.val (u : C[F]) * (χ (u : C[F]) : ℂ)
        ∂normOneIdeleClassTamagawaMeasure F =
      -(bruhatDirectionalDeriv b (fun x : C[F] ↦ (χ x : ℂ)) 1 *
        ∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) := by
  let mK : MeasurableSpace (ideleClassNorm F).ker := Subtype.instMeasurableSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : BorelSpace C[F] := ⟨rfl⟩
  have hB : @BorelSpace (ideleClassNorm F).ker _ mK := Subtype.borelSpace _
  have : @MeasurableMul (ideleClassNorm F).ker mK _ := @ContinuousMul.measurableMul _ _ mK hB _ _
  have hχ1 : IsBruhatContDiff 1 (fun x : C[F] ↦ (χ x : ℂ)) :=
    (mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth χ) 1
  have hκ : HasDerivAt (fun t : ℝ ↦ (χ (b (Multiplicative.ofAdd t)) : ℂ))
      (bruhatDirectionalDeriv b (fun x : C[F] ↦ (χ x : ℂ)) 1) 0 := by
    simpa only [one_mul] using hasDerivAt_bruhatDirectionalDeriv b hχ1 1
  have hP (y : ℝ) : ∫ u, f.val (b (Multiplicative.ofAdd y) * (u : C[F])) *
      (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F =
      (χ (b (Multiplicative.ofAdd y)) : ℂ)⁻¹ *
        ∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F := by
    let w : (ideleClassNorm F).ker := ⟨b (Multiplicative.ofAdd y), hb _⟩
    rw [eq_inv_mul_iff_mul_eq₀ (Circle.coe_ne_zero _), ← integral_const_mul]
    refine (integral_congr_ae (.of_forall fun u ↦ ?_)).trans
      (integral_mul_left_eq_self (μ := normOneIdeleClassTamagawaMeasure F)
        (fun u : (ideleClassNorm F).ker ↦ f.val (u : C[F]) * (χ (u : C[F]) : ℂ)) w)
    change (χ (w : C[F]) : ℂ) * (f.val ((w : C[F]) * (u : C[F])) * (χ (u : C[F]) : ℂ)) =
      f.val (((w * u : (ideleClassNorm F).ker)) : C[F]) *
        (χ (((w * u : (ideleClassNorm F).ker)) : C[F]) : ℂ)
    rw [Subgroup.coe_mul, map_mul, Circle.coe_mul]
    ring
  have hinv : HasDerivAt (fun y : ℝ ↦ (χ (b (Multiplicative.ofAdd y)) : ℂ)⁻¹ *
      ∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F)
      (-bruhatDirectionalDeriv b (fun x : C[F] ↦ (χ x : ℂ)) 1 *
        ∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) 0 := by
    have h1 : (χ (b (Multiplicative.ofAdd 0)) : ℂ) = 1 := by
      rw [ofAdd_zero, map_one, map_one, Circle.coe_one]
    refine ((hκ.fun_inv (by rw [h1]; exact one_ne_zero)).mul_const
      (∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F)).congr_deriv ?_
    rw [h1, one_pow, div_one]
  have hd := (explicitFormula_radial_hasDerivAt b χ f 0).unique
    (hinv.congr_of_eventuallyEq (.of_forall hP))
  rw [ofAdd_zero, map_one] at hd
  simp only [one_mul] at hd
  rw [hd, neg_mul]

/-- Iterating the integration by parts: for each `N` there is a test (the `N`-th derivative
along `b`) whose Fourier coefficients on `C¹` are those of `f` times `(-κ)^N`. -/
private theorem explicitFormula_normOne_coeff_flowDeriv_pow (b : Multiplicative ℝ →ₜ* C[F])
    (hb : ∀ t, b t ∈ (ideleClassNorm F).ker) (N : ℕ) (f : 𝒟(C[F])) :
    ∃ g : 𝒟(C[F]), ∀ χ : U[F],
      ∫ u, g.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F =
        (-bruhatDirectionalDeriv b (fun x : C[F] ↦ (χ x : ℂ)) 1) ^ N *
          ∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F := by
  induction N with
  | zero => exact ⟨f, fun χ ↦ by rw [pow_zero, one_mul]⟩
  | succ N ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨⟨bruhatDirectionalDeriv b g.val, explicitFormula_flowDeriv_mem b g⟩, fun χ ↦ ?_⟩
    change ∫ u, bruhatDirectionalDeriv b g.val (u : C[F]) * (χ (u : C[F]) : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F = _
    rw [explicitFormula_normOne_coeff_flowDeriv b hb χ g, hg, pow_succ]
    ring

/-- The Fourier coefficients on `C¹` of a test are bounded uniformly in the character. -/
private theorem explicitFormula_normOne_coeff_bound (f : 𝒟(C[F])) :
    ∃ B : ℝ, ∀ χ : U[F], ‖∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F‖ ≤ B := by
  have : IsFiniteMeasure (normOneIdeleClassTamagawaMeasure F) :=
    ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC⟩ := (explicitTest_continuous f).bounded_above_of_compact_support f.property.2
  refine ⟨C * (normOneIdeleClassTamagawaMeasure F).real univ, fun χ ↦
    norm_integral_le_of_norm_le_const (.of_forall fun u ↦ ?_)⟩
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact hC _

/-- Paper: Lemma B.4.4.8, p. 624 (the decay half, on `C¹`). Along a one-parameter subgroup `b`
of the idele classes with values in `C¹`, the Fourier coefficient of a test at `χ` decays faster
than any power of the frequency `κ_b(χ)`, the derivative of `t ↦ χ(b(t))` at `0`: for each `N`,
`|κ_b(χ)|^N |∫_{C¹} f χ|` is bounded independently of `χ`. -/
private theorem explicitFormula_normOne_coeff_decay (b : Multiplicative ℝ →ₜ* C[F])
    (hb : ∀ t, b t ∈ (ideleClassNorm F).ker) (N : ℕ) (f : 𝒟(C[F])) :
    ∃ B : ℝ, ∀ χ : U[F], ‖bruhatDirectionalDeriv b (fun x : C[F] ↦ (χ x : ℂ)) 1‖ ^ N *
      ‖∫ u, f.val (u : C[F]) * (χ (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F‖ ≤ B := by
  obtain ⟨g, hg⟩ := explicitFormula_normOne_coeff_flowDeriv_pow b hb N f
  obtain ⟨B, hB⟩ := explicitFormula_normOne_coeff_bound g
  refine ⟨B, fun χ ↦ ?_⟩
  rw [← norm_neg (bruhatDirectionalDeriv b _ 1), ← norm_pow, ← norm_mul, ← hg]
  exact hB χ

/-- Assembly of the absolute convergence on `C¹`: if `f` is invariant under `k`, and the
characters trivial on `k ∩ C¹` with frequencies at most `T` along finitely many one-parameter
subgroups `b j` of `C¹` number at most `C (T + 1)^d`, the Fourier coefficients of `f` are
absolutely summable. Off `k ∩ C¹` they vanish; on it they decay like `(1 + ∑ |κ_j|)^{-(d+2)}`. -/
private theorem explicitFormula_normOneFourier_summable_of_count (τ : ℝ≥0ˣ →ₜ* C[F])
    (f : 𝒟(C[F])) (k : Subgroup C[F]) (hinv : ∀ h : k, ∀ x, f.val (h.val * x) = f.val x)
    (r : ℕ) (b : Fin r → Multiplicative ℝ →ₜ* C[F])
    (hb : ∀ j t, b j t ∈ (ideleClassNorm F).ker) (C d : ℕ)
    (hcount : ∀ T : ℕ,
      {χ : chartChars(τ) | (∀ u : (ideleClassNorm F).ker, (u : C[F]) ∈ k → χ.val u = 1) ∧
        ∀ j, ‖bruhatDirectionalDeriv (b j) (fun x : C[F] ↦ (χ.val x : ℂ)) 1‖ ≤ T}.encard ≤
        ((C * (T + 1) ^ d : ℕ) : ℕ∞)) :
    Summable (fun χ : chartChars(τ) ↦
      ‖∫ u, f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F‖) := by
  classical
  let S : Set chartChars(τ) :=
    {χ | ∀ u : (ideleClassNorm F).ker, (u : C[F]) ∈ k → χ.val u = 1}
  let c : chartChars(τ) → ℝ := fun χ ↦
    ‖∫ u, f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F‖
  have hzero : ∀ χ ∉ Set.range ((↑) : S → chartChars(τ)), c χ = 0 := by
    intro χ hχ
    have hχS : χ ∉ S := fun h ↦ hχ ⟨⟨χ, h⟩, rfl⟩
    simp only [S, Set.mem_ofPred_eq, not_forall] at hχS
    obtain ⟨u, hu, hχu⟩ := hχS
    change ‖_‖ = 0
    rw [explicitFormula_coeff_eq_zero_of_invariant f χ.val u
      (fun g ↦ by rw [mul_comm]; exact hinv ⟨u, hu⟩ g) hχu, norm_zero]
  refine (Function.Injective.summable_iff Subtype.val_injective hzero).mp ?_
  let κ : Fin r → chartChars(τ) → ℂ := fun j χ ↦
    bruhatDirectionalDeriv (b j) (fun x : C[F] ↦ (χ.val x : ℂ)) 1
  let m : S → ℝ := fun χ ↦ ∑ j, ‖κ j χ.val‖
  have hm : ∀ χ, 0 ≤ m χ := fun χ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  obtain ⟨B0, hB0⟩ := explicitFormula_normOne_coeff_bound f
  choose B hB using fun j ↦ explicitFormula_normOne_coeff_decay (b j) (hb j) (d + 2) f
  have hB0nn : 0 ≤ B0 := (norm_nonneg _).trans (hB0 1)
  have hBnn (j : Fin r) : 0 ≤ B j := (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).trans (hB j 1)
  refine summable_bruhatMellin_of_polynomialCount_of_polyCount_decay (g := c ∘ Subtype.val)
    m hm C d (((r : ℝ) + 1) ^ (d + 1) * (B0 + ∑ j, B j))
    (mul_nonneg (by positivity) (add_nonneg hB0nn (Finset.sum_nonneg fun j _ ↦ hBnn j)))
    (fun T ↦ ?_) (fun χ ↦ ?_)
  · rw [← Subtype.val_injective.encard_image]
    refine (Set.encard_mono ?_).trans (hcount T)
    rintro _ ⟨χ, hχ, rfl⟩
    exact ⟨χ.2, fun j ↦ (Finset.single_le_sum (fun i _ ↦ norm_nonneg (κ i χ.val))
      (Finset.mem_univ j)).trans hχ⟩
  · have hc0 : 0 ≤ c χ.val := norm_nonneg _
    rw [Function.comp_apply, Real.norm_of_nonneg hc0, le_div_iff₀ (by positivity)]
    let g : Option (Fin r) → ℝ := fun o ↦ o.elim 1 fun j ↦ ‖κ j χ.val‖
    have hg : ∀ o ∈ (Finset.univ : Finset (Option (Fin r))), 0 ≤ g o := by
      rintro (_ | j) _
      · exact zero_le_one
      · exact norm_nonneg _
    have hJ := pow_sum_le_card_mul_sum_pow hg (d + 1)
    simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Fintype.sum_option,
      Option.elim, g, one_pow] at hJ
    push_cast at hJ
    have hsum : ∑ j, ‖κ j χ.val‖ ^ (d + 2) * c χ.val ≤ ∑ j, B j :=
      Finset.sum_le_sum fun j _ ↦ hB j χ.val.val
    calc c χ.val * (1 + m χ) ^ (d + 2)
        ≤ c χ.val * (((r : ℝ) + 1) ^ (d + 1) * (1 + ∑ j, ‖κ j χ.val‖ ^ (d + 2))) :=
          mul_le_mul_of_nonneg_left hJ hc0
      _ = ((r : ℝ) + 1) ^ (d + 1) * (c χ.val + ∑ j, ‖κ j χ.val‖ ^ (d + 2) * c χ.val) := by
          rw [← Finset.sum_mul]
          ring
      _ ≤ ((r : ℝ) + 1) ^ (d + 1) * (B0 + ∑ j, B j) := by
          gcongr
          exact hB0 χ.val.val

end ExplicitFormulaNormOneDecay

section ExplicitFormulaNormOneCover

variable {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]

/-- A real-valued homomorphism on an open subgroup extends to the whole group.
Copied from the private `openSubgroup_extend_real` (AppD Sec1d). -/
private theorem explicitFormula_count_extend_real (J : Subgroup X) (hJ : IsOpen (J : Set X))
    (g : J →ₜ* Multiplicative ℝ) : ∃ f : X →ₜ* Multiplicative ℝ, ∀ x : J, f x.val = g x := by
  let i : Additive J →+ Additive X := MonoidHom.toAdditive J.subtype
  let l : Additive J →+ ℝ := MonoidHom.toAdditive g.toMonoidHom
  obtain ⟨v, hv⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom i
    Subtype.val_injective l
  let f : X →* Multiplicative ℝ := AddMonoidHom.toMultiplicative v
  have he (x : J) : f x.val = g x := DFunLike.congr_fun hv (Additive.ofMul x)
  refine ⟨⟨f, continuous_of_continuousAt_one f ?_⟩, he⟩
  have hc : ContinuousAt (f ∘ Subtype.val : J → Multiplicative ℝ) 1 :=
    by rw [show (f ∘ Subtype.val : J → _) = g from funext he]; exact g.continuous.continuousAt
  exact hJ.isOpenEmbedding_subtypeVal.continuousAt_iff.mp hc

/-- The whole group as a subgroup is the group. Copied from the private `topSubgroupEquiv`
(AppD Sec1d). -/
private def explicitFormula_count_topEquiv : (⊤ : Subgroup X) ≃ₜ* X :=
  { Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := continuous_id.subtype_mk _ }

/-- Quotients along a topological isomorphism. Copied from the private `quotientCongr`
(AppD Sec1d). -/
private def explicitFormula_count_quotientCongr {G H : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K : Subgroup H) (N : Subgroup G) (e : H ≃ₜ* G) (he : K.map e.toMulEquiv = N) :
    H ⧸ K ≃ₜ* G ⧸ N :=
  let φ := QuotientGroup.congr K N e.toMulEquiv he
  { φ with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp e.continuous)
    continuous_invFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp e.symm.continuous) }

variable [T2Space X] [LocallyCompactSpace X]

/-- One-parameter subgroups lift through the quotient by a compact subgroup. Adapted from the
private `oneParameterMap_quotient_surjective` (AppD Sec1d). -/
private theorem explicitFormula_count_flow_lift (K : Subgroup X) (hk : IsCompact (K : Set X))
    (a : Multiplicative ℝ →ₜ* X ⧸ K) :
    ∃ b : Multiplicative ℝ →ₜ* X, ∀ t, (QuotientGroup.mk (b t) : X ⧸ K) = a t := by
  have : T2Space (X ⧸ K) := IsTopologicalGroup.t2Space_iff_one_closed.mpr <| by
    rw [← (QuotientGroup.isQuotientMap_mk K).isCoinducing.isClosed_preimage]
    convert hk.isClosed using 1
    simpa only [QuotientGroup.mk_one] using QuotientGroup.preimage_mk_one K
  let q : X →ₜ* X ⧸ K := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  obtain ⟨Z, hZ⟩ := lcaQuotientDual_equiv_annihilator K hk.isClosed
  obtain ⟨ea, hea⟩ := lcaTopologicalLie_dual (G := X)
  obtain ⟨eb, heb⟩ := lcaTopologicalLie_dual (G := X ⧸ K)
  let e := exists_realPontryaginDualEquiv.choose
  let g := (e.symm : PontryaginDual (Multiplicative ℝ) →ₜ* Multiplicative ℝ).comp
    ((eb a).comp (Z.symm : lcaAnnihilator K →ₜ* _))
  obtain ⟨f, hf⟩ := explicitFormula_count_extend_real (lcaAnnihilator K)
    (isOpen_lcaAnnihilator K hk) g
  let u := (e : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ)).comp f
  let b := ea.symm u
  have hb : PontryaginDual.map b = u := (hea _).symm.trans (ea.apply_symm_apply u)
  have hqb : q.comp b = a := by
    apply eb.injective
    rw [heb]
    apply ContinuousMonoidHom.ext
    intro χ
    apply PontryaginDual.ext
    intro t
    have he : PontryaginDual.map q χ = (Z χ).val :=
      PontryaginDual.ext fun x ↦ (hZ χ x).symm
    change χ (q (b t)) = eb a χ t
    calc χ (q (b t)) = PontryaginDual.map b (PontryaginDual.map q χ) t := rfl
      _ = e (f (Z χ).val) t := by rw [hb, he]; rfl
      _ = eb a χ t := by
        rw [hf]
        change e (e.symm (eb a (Z.symm (Z χ)))) t = _
        rw [e.apply_symm_apply, Z.symm_apply_apply]
  exact ⟨b, fun t ↦ congrArg (fun c : Multiplicative ℝ →ₜ* X ⧸ K ↦ c t) hqb⟩

/-- A group with a norm onto the positive reals that has a section and a compact kernel is
compactly generated. Copied from the private `compactlyGenerated_of_split` (AppD Sec1d). -/
private theorem explicitFormula_count_compactlyGenerated (n : X →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* X)
    (hτ : RightInverse τ n) (hk : IsCompact (n.ker : Set X)) : IsCompactlyGeneratedGroup X := by
  obtain ⟨U, hU, hne⟩ := exists_compact_mem_nhds (1 : X)
  let K := U ∪ (n.ker : Set X)
  let J := Subgroup.closure K
  have hK : K ∈ 𝓝 (1 : X) := Filter.mem_of_superset hne subset_union_left
  have hJ : IsOpen (J : Set X) :=
    J.isOpen_of_mem_nhds (Filter.mem_of_superset hK Subgroup.subset_closure)
  have hker : n.ker ≤ J := subset_union_right.trans Subgroup.subset_closure
  have : ConnectedSpace ℝ≥0ˣ := (Real.expOrderIso.toHomeomorph.trans
    (Nonneg.unitsHomeomorphPos ℝ).symm).surjective.connectedSpace (by fun_prop)
  have ht (t : ℝ≥0ˣ) : τ t ∈ J := by
    have hpre : IsClopen (τ ⁻¹' (J : Set X)) :=
      ⟨(J.isClosed_of_isOpen hJ).preimage τ.continuous, hJ.preimage τ.continuous⟩
    change t ∈ τ ⁻¹' (J : Set X)
    rw [hpre.eq_univ ⟨1, by change τ 1 ∈ J; rw [map_one]; exact J.one_mem⟩]
    exact mem_univ t
  refine ⟨K, hK, hU.union hk, top_unique (fun x _ ↦ ?_)⟩
  have hx : x / τ (n x) ∈ n.ker := by simp [MonoidHom.mem_ker, hτ (n x)]
  exact div_mul_cancel x (τ (n x)) ▸ J.mul_mem (hker hx) (ht _)

/-- A good subgroup is compact: it is the annihilator of its open annihilator. -/
private theorem explicitFormula_count_good_isCompact (k : Subgroup X)
    (hk : IsBruhatGoodSubgroup k) : IsCompact (k : Set X) := by
  rw [← lcaDualAnnihilator_annihilator k hk.1]
  exact isCompact_lcaDualAnnihilator _ hk.2.1

/-- A compact subgroup lies in the kernel of a continuous norm to the positive reals. -/
private theorem explicitFormula_count_le_ker (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (k : Subgroup X) (hkc : IsCompact (k : Set X)) : k ≤ n.ker := by
  have hc : Continuous fun g : X ↦ (((n g : ℝ≥0ˣ) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hn)
  obtain ⟨R, hR⟩ := (hkc.image hc).bddAbove
  have hle (x : X) (hx : x ∈ k) : ¬ 1 < (((n x : ℝ≥0ˣ) : ℝ≥0) : ℝ) := by
    intro h1
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R h1
    refine (hR ⟨x ^ m, k.pow_mem hx m, rfl⟩).not_gt ?_
    simpa only [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow] using hm
  intro x hx
  have h1 := hle x hx
  have h2 := hle x⁻¹ (k.inv_mem hx)
  have hpos : 0 < (((n x : ℝ≥0ˣ) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (n x).ne_zero)
  rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, one_lt_inv₀ hpos] at h2
  have he : (((n x : ℝ≥0ˣ) : ℝ≥0) : ℝ) = 1 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
  exact Units.ext (NNReal.coe_eq_one.mp he)

end ExplicitFormulaNormOneCover

section ExplicitFormulaNormOneCover2

variable {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
  [LocallyCompactSpace X]

/-- For a good subgroup `k` of a group with a split norm and compact norm-one part, there are
finitely many one-parameter subgroups `b j` of the norm-one part such that finitely many
translates of `{∏ b j (x j) · κ : |x j| ≤ 1, κ ∈ k}` cover the norm-one part. The flows are
lifts of the coordinate directions of an elementary presentation of the quotient by `k`, pushed
into the norm-one part with the section. -/
private theorem explicitFormula_count_cover (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n) (hker : IsCompact (n.ker : Set X))
    (k : Subgroup X) (hk : IsBruhatGoodSubgroup k) :
    ∃ (r : ℕ) (b : Fin r → Multiplicative ℝ →ₜ* X), (∀ j t, b j t ∈ n.ker) ∧
      ∃ s : Finset n.ker, ∀ y ∈ n.ker, ∃ g ∈ s, ∃ x : Fin r → ℝ,
        (∀ j, |x j| ≤ 1) ∧ ∃ κ ∈ k, y = (g : X) * (∏ j, b j (Multiplicative.ofAdd (x j))) * κ := by
  classical
  have hkc := explicitFormula_count_good_isCompact k hk
  have hkn := explicitFormula_count_le_ker n hn k hkc
  have hc := explicitFormula_count_compactlyGenerated n τ hτ hker
  let a : BruhatStructuralPair X := ⟨(⊤, OrderDual.toDual k), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv explicitFormula_count_topEquiv.symm hc,
    hk, le_top⟩
  let e := Classical.choice a.elementary
  let A : a.quotient ≃ₜ* X ⧸ k := explicitFormula_count_quotientCongr _ k
    explicitFormula_count_topEquiv (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩)
  let E := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let ψ := elementaryCoverZeroHom (m := e.realDim) (n := e.torusDim) (r := e.latticeRank)
    (F := e.finiteFactor)
  obtain ⟨hψc, hψo⟩ := elementaryCoverZeroHom_continuous_isOpenMap (m := e.realDim)
    (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  let r := Module.finrank ℝ E
  let β := Module.finBasis ℝ E
  let fZ (i : Fin r) : Multiplicative ℝ →ₜ* Multiplicative
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    { toFun := fun t ↦ Multiplicative.ofAdd (ψ (t.toAdd • β i))
      map_one' := by simp
      map_mul' := fun s t ↦ by
        simp only [toAdd_mul, add_smul, map_add, ofAdd_add]
      continuous_toFun := continuous_ofAdd.comp
        (hψc.comp ((continuous_toAdd).smul continuous_const)) }
  let B : X ⧸ k ≃ₜ* Multiplicative
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    A.symm.trans e.equiv
  choose u hu using fun i ↦ explicitFormula_count_flow_lift k hkc
    ((B.symm : Multiplicative _ →ₜ* X ⧸ k).comp (fZ i))
  let N : X →ₜ* ℝ≥0ˣ := ⟨n, hn⟩
  let b (i : Fin r) : Multiplicative ℝ →ₜ* X := u i * (τ.comp (N.comp (u i)))⁻¹
  have hbt (i : Fin r) (t) : b i t = u i t * (τ (n (u i t)))⁻¹ := rfl
  have hb (i : Fin r) (t) : b i t ∈ n.ker := by
    rw [hbt, MonoidHom.mem_ker, map_mul, map_inv, hτ, mul_inv_cancel]
  let P : X →* Multiplicative
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    (B : X ⧸ k →* _).comp (QuotientGroup.mk' k)
  have hPc : Continuous P := B.continuous.comp QuotientGroup.continuous_mk
  have hPu (i : Fin r) (t) : P (u i t) = fZ i t := by
    change B (QuotientGroup.mk (u i t)) = _
    rw [hu i t]
    exact B.apply_symm_apply _
  have hPk (x : X) (hx : P x = 1) : x ∈ k := by
    have h1 : (QuotientGroup.mk x : X ⧸ k) = 1 := B.injective (hx.trans (map_one B).symm)
    exact (QuotientGroup.eq_one_iff x).mp h1
  let O : Set E := {v | ∀ i, |β.repr v i| < 1}
  have hO : IsOpen O := by
    have : O = ⋂ i, (fun v ↦ β.repr v i) ⁻¹' Set.Ioo (-1) 1 := by
      ext v
      simp [O, abs_lt]
    rw [this]
    refine isOpen_iInter_of_finite fun i ↦ IsOpen.preimage ?_ isOpen_Ioo
    exact (β.coord i).continuous_of_finiteDimensional
  let W : Set X := P ⁻¹' (Multiplicative.toAdd ⁻¹' (ψ '' O))
  have hW : IsOpen W := ((hψo O hO).preimage continuous_toAdd).preimage hPc
  have h1W : (1 : X) ∈ W := ⟨0, fun i ↦ by simp, by simp⟩
  obtain ⟨s, hs⟩ := hker.elim_finite_subcover
    (fun g : n.ker ↦ (fun y ↦ (g : X)⁻¹ * y) ⁻¹' W)
    (fun g ↦ hW.preimage (continuous_const.mul continuous_id))
    (fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, by
      change (y : X)⁻¹ * y ∈ W
      rw [inv_mul_cancel]
      exact h1W⟩)
  refine ⟨r, b, hb, s, fun y hy ↦ ?_⟩
  obtain ⟨g, hgs, hgy⟩ := Set.mem_iUnion₂.mp (hs hy)
  obtain ⟨v, hvO, hv⟩ := hgy
  let x : Fin r → ℝ := fun i ↦ β.repr v i
  let U : X := ∏ i, u i (Multiplicative.ofAdd (x i))
  have hUdef : ∏ i, u i (Multiplicative.ofAdd (x i)) = U := rfl
  have hPU : P U = P ((g : X)⁻¹ * y) := by
    rw [map_prod]
    simp only [hPu]
    change ∏ i, Multiplicative.ofAdd (ψ (x i • β i)) = _
    rw [← ofAdd_sum, ← map_sum, β.sum_repr v]
    exact congrArg Multiplicative.ofAdd hv |>.trans (ofAdd_toAdd _)
  let κ : X := U⁻¹ * ((g : X)⁻¹ * y)
  have hκ : κ ∈ k := hPk κ (by rw [map_mul, map_inv, hPU, inv_mul_cancel])
  have hUκ : U * κ = (g : X)⁻¹ * y := mul_inv_cancel_left U _
  clear_value κ U
  have hnU : n U = 1 := by
    have h := congrArg n hUκ
    have h2 : n ((g : X)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp g.property, MonoidHom.mem_ker.mp hy, inv_one,
        one_mul]
    rw [map_mul, h2, MonoidHom.mem_ker.mp (hkn hκ), mul_one] at h
    exact h
  have hbU : ∏ j, b j (Multiplicative.ofAdd (x j)) = U := by
    let D : X →* X :=
      { toFun := fun z ↦ z * (τ (n z))⁻¹
        map_one' := by simp only [map_one, inv_one, mul_one]
        map_mul' := fun z w ↦ by
          simp only [map_mul, mul_inv]
          exact mul_mul_mul_comm _ _ _ _ }
    have hD : ∀ j, b j (Multiplicative.ofAdd (x j)) = D (u j (Multiplicative.ofAdd (x j))) :=
      fun j ↦ rfl
    simp only [hD]
    rw [← map_prod, hUdef]
    change U * (τ (n U))⁻¹ = U
    rw [hnU, map_one, inv_one, mul_one]
  refine ⟨g, hgs, x, fun j ↦ (hvO j).le, κ, hκ, ?_⟩
  rw [hbU, mul_assoc, hUκ, mul_inv_cancel_left]

end ExplicitFormulaNormOneCover2

section ExplicitFormulaNormOneChar

variable {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
  [LocallyCompactSpace X]

/-- A character along a one-parameter subgroup is `t ↦ exp(iθt)`, and its frequency
`bruhatDirectionalDeriv a χ 1` is `iθ`. -/
private theorem explicitFormula_count_char_flow (a : Multiplicative ℝ →ₜ* X)
    (χ : PontryaginDual X) : ∃ θ : ℝ,
      (∀ t : ℝ, (χ (a (Multiplicative.ofAdd t)) : ℂ) =
        Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I)) ∧
      bruhatDirectionalDeriv a (fun x : X ↦ (χ x : ℂ)) 1 = θ * Complex.I := by
  obtain ⟨e, he⟩ := exists_realPontryaginDualEquiv
  obtain ⟨x, hx⟩ := e.surjective ((χ : X →ₜ* Circle).comp a)
  let θ := 2 * Real.pi * x.toAdd
  have hval (t : ℝ) : (χ (a (Multiplicative.ofAdd t)) : ℂ) =
      Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) := by
    have h1 : e x (Multiplicative.ofAdd t) = χ (a (Multiplicative.ofAdd t)) := by rw [hx]; rfl
    have h : χ (a (Multiplicative.ofAdd t)) = Circle.exp (2 * Real.pi * (x.toAdd * t)) := by
      rw [← h1, ← he]
      rfl
    rw [h, Circle.coe_exp]
    congr 1
    push_cast
    simp only [θ]
    push_cast
    ring
  refine ⟨θ, hval, ?_⟩
  have hfun : (fun t : ℝ ↦ (χ (1 * a (Multiplicative.ofAdd t)) : ℂ)) =
      fun t : ℝ ↦ Complex.exp ((t : ℂ) * (θ * Complex.I)) := by
    funext t
    rw [one_mul, hval]
    congr 1
    push_cast
    ring
  have hd : HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * (θ * Complex.I))) (θ * Complex.I) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const ((θ : ℂ) * Complex.I)).cexp
    simpa using this
  rw [bruhatDirectionalDeriv, hfun, hd.deriv]

/-- `|exp(iα) - 1| ≤ |α|`, so a character close to `1` along all flows is close to `1`. -/
private theorem explicitFormula_count_exp_sub_one (α : ℝ) :
    ‖Complex.exp ((α : ℂ) * Complex.I) - 1‖ ≤ |α| := by
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := α)
  rw [mul_comm]
  simpa using this

end ExplicitFormulaNormOneChar

section ExplicitFormulaNormOneCount

/-- Bessel's inequality for the indicator of a set `E` of norm-one classes on which the
characters of a finite family all have real part at least `1/2`: with `h = ∑_χ χ`,
`∫ |h|² = (#t) vol(C¹)` by orthogonality, and `|h|² ≥ (#t/2)²` on `E`. -/
private theorem explicitFormula_count_bessel (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (t : Finset chartChars(τ))
    (E : Set (ideleClassNorm F).ker) (hEc : IsClosed E)
    (hχ : ∀ χ ∈ t, ∀ u ∈ E, (1 / 2 : ℝ) ≤ ((χ.val (u : C[F]) : Circle) : ℂ).re) :
    ((t.card : ℝ) / 2) ^ 2 * (normOneIdeleClassTamagawaMeasure F).real E ≤
      t.card * classVolume := by
  let K := (ideleClassNorm F).ker
  let μ := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let mK : MeasurableSpace K := Subtype.instMeasurableSpace
  have : OpensMeasurableSpace K := Subtype.opensMeasurableSpace (α := C[F]) _
  have hE : MeasurableSet E := hEc.measurableSet
  have : IsFiniteMeasure μ :=
    ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  have hcont (χ : U[F]) : Continuous fun u : K ↦ ((χ (u : C[F]) : Circle) : ℂ) :=
    continuous_subtype_val.comp (χ.continuous.comp continuous_subtype_val)
  have hint (χ ψ : U[F]) : Integrable (fun u : K ↦
      ((χ (u : C[F]) : Circle) : ℂ) * ((ψ (u : C[F]) : Circle) : ℂ)) μ := by
    refine Integrable.of_bound ((hcont χ).mul (hcont ψ)).aestronglyMeasurable 1
      (.of_forall fun u ↦ ?_)
    rw [norm_mul, Circle.norm_coe, Circle.norm_coe, mul_one]
  let h : K → ℂ := fun u ↦ ∑ χ ∈ t, ((χ.val (u : C[F]) : Circle) : ℂ)
  have hhc : Continuous h := continuous_finsetSum _ fun χ _ ↦ hcont χ.val
  let H : K → ℝ := fun u ↦ ‖h u‖ ^ 2
  have hHc : Continuous H := (continuous_norm.comp hhc).pow 2
  have hHint : Integrable H μ := by
    refine Integrable.of_bound hHc.aestronglyMeasurable ((t.card : ℝ) ^ 2)
      (.of_forall fun u ↦ ?_)
    have h1 : ‖h u‖ ≤ t.card := by
      refine (norm_sum_le _ _).trans ?_
      simp only [Circle.norm_coe, Finset.sum_const, nsmul_eq_mul, mul_one, le_refl]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hpt (u : K) : ((H u : ℝ) : ℂ) = ∑ χ ∈ t, ∑ ψ ∈ t,
      ((χ.val⁻¹ (u : C[F]) : Circle) : ℂ) * ((ψ.val (u : C[F]) : Circle) : ℂ) := by
    have hconj : (starRingEnd ℂ) (h u) = ∑ χ ∈ t, ((χ.val⁻¹ (u : C[F]) : Circle) : ℂ) := by
      simp only [h, map_sum]
      refine Finset.sum_congr rfl fun χ _ ↦ ?_
      change _ = (((χ.val (u : C[F]))⁻¹ : Circle) : ℂ)
      rw [Circle.coe_inv_eq_conj]
    rw [← Finset.sum_mul_sum, ← hconj, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hI : ∫ u, H u ∂μ = t.card * classVolume := by
    have hc : ∫ u, ((H u : ℝ) : ℂ) ∂μ = t.card * classVolume := by
      simp_rw [hpt]
      rw [integral_finsetSum (f := fun (χ : chartChars(τ)) (u : (ideleClassNorm F).ker) ↦ ∑ ψ ∈ t,
        ((χ.val⁻¹ (u : C[F]) : Circle) : ℂ) * ((ψ.val (u : C[F]) : Circle) : ℂ))
        _ fun χ _ ↦ integrable_finsetSum _ fun ψ _ ↦ hint _ _]
      have hin (χ : chartChars(τ)) : ∫ u, ∑ ψ ∈ t,
          ((χ.val⁻¹ (u : C[F]) : Circle) : ℂ) * ((ψ.val (u : C[F]) : Circle) : ℂ) ∂μ =
          ∑ ψ ∈ t, if χ = ψ then (classVolume : ℂ) else 0 := by
        rw [integral_finsetSum (f := fun (ψ : chartChars(τ)) (u : (ideleClassNorm F).ker) ↦
          ((χ.val⁻¹ (u : C[F]) : Circle) : ℂ) * ((ψ.val (u : C[F]) : Circle) : ℂ))
          _ fun ψ _ ↦ hint _ _]
        exact Finset.sum_congr rfl fun ψ _ ↦
          explicitFormula_integral_chartChar_inv_mul τ hτ χ ψ
      simp only [hin, Finset.sum_ite_eq, Finset.sum_ite_mem, Finset.inter_self]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [integral_complex_ofReal] at hc
    exact_mod_cast hc
  have hlow : μ.real E • (((t.card : ℝ) / 2) ^ 2) ≤ ∫ u in E, H u ∂μ := by
    refine setIntegral_ge_of_const_le hE (measure_ne_top _ _) (fun u hu ↦ ?_)
      hHint.integrableOn
    have hre : (t.card : ℝ) / 2 ≤ (h u).re := by
      simp only [h, Complex.re_sum]
      calc (t.card : ℝ) / 2 = ∑ χ ∈ t, (1 / 2 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum fun χ hχt ↦ hχ χ hχt u hu
    have h2 : (t.card : ℝ) / 2 ≤ ‖h u‖ := hre.trans (Complex.re_le_norm _)
    exact pow_le_pow_left₀ (by positivity) h2 2
  have hle : ∫ u in E, H u ∂μ ≤ ∫ u, H u ∂μ :=
    setIntegral_le_integral hHint (.of_forall fun u ↦ by positivity)
  rw [smul_eq_mul, mul_comm] at hlow
  rw [← hI]
  exact hlow.trans hle

/-- The count for one bound `T`, given a cover of `C¹` by finitely many translates of the flow
box `{∏ b j (x j) · κ : |x j| ≤ 1, κ ∈ k}`. With `L = 2r(T+1)+1`, the characters in question
have real part at least `1/2` on the small box `E` (`|x j| ≤ 1/L`), and `C¹` is covered by
`#s (2L+1)^r` translates of `E`, so Bessel's inequality gives at most `4 #s (2L+1)^r`. -/
private theorem explicitFormula_count_key (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (k : Subgroup C[F])
    (hkn : k ≤ (ideleClassNorm F).ker) (hkc : IsCompact (k : Set C[F])) {r : ℕ}
    (b : Fin r → Multiplicative ℝ →ₜ* C[F]) (hb : ∀ j t, b j t ∈ (ideleClassNorm F).ker)
    (s : Finset (ideleClassNorm F).ker)
    (hcov : ∀ y ∈ (ideleClassNorm F).ker, ∃ g ∈ s, ∃ x : Fin r → ℝ, (∀ j, |x j| ≤ 1) ∧
      ∃ κ ∈ k, y = (g : C[F]) * (∏ j, b j (Multiplicative.ofAdd (x j))) * κ)
    (T : ℕ) (t : Finset chartChars(τ))
    (ht : ∀ χ ∈ t, (∀ u : (ideleClassNorm F).ker, (u : C[F]) ∈ k → χ.val u = 1) ∧
      ∀ j, ‖bruhatDirectionalDeriv (b j) (fun x : C[F] ↦ (χ.val x : ℂ)) 1‖ ≤ T) :
    t.card ≤ 4 * s.card * (4 * r + 3) ^ r * (T + 1) ^ r := by
  classical
  let K := (ideleClassNorm F).ker
  let μ := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let mK : MeasurableSpace K := Subtype.instMeasurableSpace
  have hB : @BorelSpace K _ mK := Subtype.borelSpace _
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have : IsFiniteMeasure μ :=
    ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  have : @MeasurableMul K mK _ := @ContinuousMul.measurableMul _ _ mK hB _ _
  set L : ℕ := 2 * r * (T + 1) + 1 with hL
  have hLpos : (0 : ℝ) < L := by positivity
  set ρ : ℝ := 1 / L with hρ
  let Φ : (Fin r → ℝ) → C[F] := fun z ↦ ∏ j, b j (Multiplicative.ofAdd (z j))
  have hΦc : Continuous Φ := continuous_finsetProd _ fun j _ ↦
    (b j).continuous.comp (continuous_ofAdd.comp (continuous_apply j))
  have hΦadd (z w : Fin r → ℝ) : Φ (z + w) = Φ z * Φ w := by
    simp only [Φ, ← Finset.prod_mul_distrib, ← map_mul, Pi.add_apply, ofAdd_add]
  have hΦK (z : Fin r → ℝ) : Φ z ∈ K := Subgroup.prod_mem _ fun j _ ↦ hb j _
  let box : Set C[F] := (fun p : (Fin r → ℝ) × C[F] ↦ Φ p.1 * p.2) ''
    (Set.pi univ (fun _ ↦ Icc (-ρ) ρ) ×ˢ (k : Set C[F]))
  have hbox : IsCompact box := ((isCompact_univ_pi fun _ ↦ isCompact_Icc).prod hkc).image
    ((hΦc.comp continuous_fst).mul continuous_snd)
  let E : Set K := Subtype.val ⁻¹' box
  have hEc : IsClosed E := hbox.isClosed.preimage continuous_subtype_val
  have hEm : MeasurableSet E := hEc.measurableSet
  have hre : ∀ χ ∈ t, ∀ u ∈ E, (1 / 2 : ℝ) ≤ ((χ.val (u : C[F]) : Circle) : ℂ).re := by
    intro χ hχ u hu
    obtain ⟨⟨z, κ⟩, ⟨hz, hκ⟩, hzu⟩ := hu
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hz
    choose θ hθ hκθ using fun j ↦ explicitFormula_count_char_flow (b j) χ.val
    have hθT (j : Fin r) : |θ j| ≤ T := by
      have := (ht χ hχ).2 j
      rwa [hκθ j, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        at this
    have h1 : χ.val κ = 1 := (ht χ hχ).1 ⟨κ, hkn hκ⟩ hκ
    have hprod : ((∏ j, χ.val (b j (Multiplicative.ofAdd (z j))) : Circle) : ℂ) =
        ∏ j, ((χ.val (b j (Multiplicative.ofAdd (z j))) : Circle) : ℂ) :=
      map_prod Circle.coeHom _ _
    have hval : ((χ.val (u : C[F]) : Circle) : ℂ) =
        Complex.exp (((∑ j, θ j * z j : ℝ) : ℂ) * Complex.I) := by
      rw [← hzu]
      simp only [map_mul, h1, mul_one, Φ, map_prod]
      rw [hprod]
      simp only [hθ]
      rw [← Complex.exp_sum, ← Finset.sum_mul]
      push_cast
      rfl
    have hsum : |∑ j, θ j * z j| ≤ 1 / 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |θ j * z j| ≤ ∑ _j : Fin r, (T : ℝ) * ρ :=
            Finset.sum_le_sum fun j _ ↦ by
              rw [abs_mul]
              exact mul_le_mul (hθT j) (abs_le.mpr (hz j)) (abs_nonneg _) (Nat.cast_nonneg _)
        _ = r * T / L := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hρ]
            ring
        _ ≤ 1 / 2 := by
            rw [div_le_iff₀ hLpos, hL]
            push_cast
            nlinarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) T]
    have hd := explicitFormula_count_exp_sub_one (∑ j, θ j * z j)
    rw [← hval] at hd
    have hab := Complex.abs_re_le_norm (((χ.val (u : C[F]) : Circle) : ℂ) - 1)
    rw [Complex.sub_re, Complex.one_re] at hab
    linarith [neg_abs_le ((((χ.val (u : C[F]) : Circle) : ℂ)).re - 1)]
  let G : Finset (Fin r → ℤ) := Fintype.piFinset fun _ ↦ Finset.Icc (-(L : ℤ)) L
  have hGcard : G.card = (2 * L + 1) ^ r := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc]
    congr 1
    omega
  let w : (Fin r → ℤ) → (Fin r → ℝ) := fun m j ↦ (m j : ℝ) / L
  let hgt (p : K × (Fin r → ℤ)) : K := p.1 * ⟨Φ (w p.2), hΦK _⟩
  have hcover : μ univ ≤ ((s.card * (2 * L + 1) ^ r : ℕ) : ENNReal) * μ E := by
    have hsub : (univ : Set K) ⊆ ⋃ p ∈ s ×ˢ G, (fun u ↦ (hgt p)⁻¹ * u) ⁻¹' E := by
      intro y _
      obtain ⟨g, hg, x, hx, κ, hκ, hy⟩ := hcov y y.property
      let m : Fin r → ℤ := fun j ↦ ⌊x j * L + 1 / 2⌋
      have hxL (j : Fin r) : -(L : ℝ) ≤ x j * L ∧ x j * L ≤ L := by
        have := abs_le.mp (hx j)
        constructor <;> nlinarith
      have hmG : m ∈ G := Fintype.mem_piFinset.mpr fun j ↦ Finset.mem_Icc.mpr
        ⟨Int.le_floor.mpr (by push_cast; linarith [(hxL j).1]),
          Int.floor_le_iff.mpr (by push_cast; linarith [(hxL j).2])⟩
      refine Set.mem_biUnion (x := (g, m)) (Finset.mem_product.mpr ⟨hg, hmG⟩) ?_
      refine ⟨(x - w m, κ), ⟨fun j _ ↦ ?_, hκ⟩, ?_⟩
      · change (x - w m) j ∈ Icc (-ρ) ρ
        have h1 := Int.floor_le (x j * L + 1 / 2)
        have h2 := Int.lt_floor_add_one (x j * L + 1 / 2)
        have he : (x - w m) j = (x j * L - m j) / L := by
          simp only [Pi.sub_apply, w]
          field_simp
        rw [he, hρ, Set.mem_Icc]
        constructor
        · rw [← neg_div]
          exact div_le_div_of_nonneg_right (by linarith) hLpos.le
        · exact div_le_div_of_nonneg_right (by linarith) hLpos.le
      · change Φ (x - w m) * κ = ((g : C[F]) * Φ (w m))⁻¹ * (y : C[F])
        have hx' : Φ x = Φ (w m) * Φ (x - w m) := by rw [← hΦadd, add_sub_cancel]
        rw [hy]
        change Φ (x - w m) * κ = ((g : C[F]) * Φ (w m))⁻¹ * ((g : C[F]) * Φ x * κ)
        rw [hx']
        group
    calc μ univ ≤ μ (⋃ p ∈ s ×ˢ G, (fun u ↦ (hgt p)⁻¹ * u) ⁻¹' E) := measure_mono hsub
      _ ≤ ∑ p ∈ s ×ˢ G, μ ((fun u ↦ (hgt p)⁻¹ * u) ⁻¹' E) := measure_biUnion_finset_le _ _
      _ = ∑ p ∈ s ×ˢ G, μ E := Finset.sum_congr rfl fun p _ ↦ measure_preimage_mul μ _ E
      _ = _ := by
        rw [Finset.sum_const, Finset.card_product, hGcard, nsmul_eq_mul]
  have hV : 0 < classVolume :=
    ENNReal.toReal_pos (IsOpen.measure_pos μ isOpen_univ univ_nonempty).ne'
      (measure_ne_top _ _)
  have hcoverR : classVolume ≤ ((s.card * (2 * L + 1) ^ r : ℕ) : ℝ) * μ.real E := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (measure_ne_top _ _)) hcover
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
  have hbes := explicitFormula_count_bessel τ hτ t E hEc hre
  set P : ℝ := ((s.card * (2 * L + 1) ^ r : ℕ) : ℝ) with hP
  set c : ℝ := ((t.card : ℕ) : ℝ) with hc
  have hμE : 0 < μ.real E := by
    by_contra h
    have h0 : μ.real E = 0 := le_antisymm (not_lt.mp h) measureReal_nonneg
    rw [h0, mul_zero] at hcoverR
    linarith
  have hcP : c ≤ 4 * P := by
    rcases (Nat.cast_nonneg t.card : (0 : ℝ) ≤ c).eq_or_lt with h0 | hpos
    · have hP0 : 0 ≤ P := by positivity
      have hc0 : c = 0 := by rw [hc]; exact h0.symm
      linarith
    · have h3 : c * (c / 4) * μ.real E ≤ c * P * μ.real E := by
        have := hbes.trans (mul_le_mul_of_nonneg_left hcoverR hpos.le)
        nlinarith
      have h4 := le_of_mul_le_mul_right h3 hμE
      have h5 := le_of_mul_le_mul_left h4 hpos
      linarith
  have hnat : t.card ≤ 4 * (s.card * (2 * L + 1) ^ r) := by
    rw [hP, hc] at hcP
    exact_mod_cast hcP
  have hL3 : 2 * L + 1 ≤ (4 * r + 3) * (T + 1) := by
    rw [hL]
    nlinarith
  calc t.card ≤ 4 * (s.card * (2 * L + 1) ^ r) := hnat
    _ ≤ 4 * (s.card * ((4 * r + 3) * (T + 1)) ^ r) := by
        gcongr
    _ = 4 * s.card * (4 * r + 3) ^ r * (T + 1) ^ r := by
        rw [mul_pow]
        ring

end ExplicitFormulaNormOneCount

/-- Paper: Lemma B.4.4.9, pp. 624–625 (the counting step, through Lemma B.4.4.8, p. 624).
For a good subgroup `k` of the idele classes there are finitely many one-parameter subgroups
`b j` of the norm-one classes `C¹` such that the characters trivial on the image of the norm
section `τ` (equivalently, the characters of `C¹`) that are trivial on `k ∩ C¹` and have all
frequencies `κ_j(χ)` (the derivative of `t ↦ χ(b j t)` at `0`) of size at most `T` number at
most `C (T + 1)^d`.

Proof. `k` is compact (its annihilator is open), so it lies in `C¹`, and `C[F]/k` has an
elementary presentation `ℝ^m × 𝕋^n × ℤ^l × A`. The coordinate directions of `ℝ^m × 𝕋^n` lift to
one-parameter subgroups of `C[F]` (the quotient is by a compact subgroup), and dividing by the
norm section puts them in `C¹`; the images of the boxes `|x_j| ≤ 1` times `k` then form a
neighbourhood, so finitely many translates cover the compact `C¹`. A character `χ` with all
`|κ_j(χ)| ≤ T` and trivial on `k` has real part at least `1/2` on the box of side `1/L`,
`L = 2r(T+1)+1`, which takes up a proportion at least `1/(#translates · (2L+1)^r)` of `C¹`;
Bessel's inequality for `∑_χ χ` (orthogonality on `C¹`) bounds the number of such characters by
`4 · #translates · (2L+1)^r`. No arithmetic input (Dirichlet's unit theorem) is needed beyond
the compactness of `C¹`. -/
theorem idelicExplicitFormula_normOneFourier_count (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (k : Subgroup C[F])
    (_hk : IsBruhatGoodSubgroup k) :
    ∃ (r : ℕ) (b : Fin r → Multiplicative ℝ →ₜ* C[F]),
      (∀ j t, b j t ∈ (ideleClassNorm F).ker) ∧ ∃ C d : ℕ, ∀ T : ℕ,
        {χ : chartChars(τ) | (∀ u : (ideleClassNorm F).ker, (u : C[F]) ∈ k → χ.val u = 1) ∧
          ∀ j, ‖bruhatDirectionalDeriv (b j) (fun x : C[F] ↦ (χ.val x : ℂ)) 1‖ ≤ T}.encard ≤
          ((C * (T + 1) ^ d : ℕ) : ℕ∞) := by
  classical
  have hn : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hker : IsCompact ((ideleClassNorm F).ker : Set C[F]) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage (isCompact_singleton (x := (1 : ℝ≥0ˣ)))
  have hkc := explicitFormula_count_good_isCompact k _hk
  have hkn := explicitFormula_count_le_ker (ideleClassNorm F) hn k hkc
  obtain ⟨r, b, hb, s, hcov⟩ :=
    explicitFormula_count_cover (ideleClassNorm F) hn τ _hτ hker k _hk
  refine ⟨r, b, hb, 4 * s.card * (4 * r + 3) ^ r, r, fun T ↦ ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨t', ht'S, ht'⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
  have hfin : t'.Finite := Set.finite_of_encard_eq_coe ht'
  have hcard := explicitFormula_count_key τ _hτ k hkn hkc b hb s hcov T hfin.toFinset
    (fun χ hχ ↦ ht'S ((Set.Finite.mem_toFinset hfin).mp hχ))
  have h2 : ((hfin.toFinset.card : ℕ) : ℕ∞) =
      ((4 * s.card * (4 * r + 3) ^ r * (T + 1) ^ r : ℕ) : ℕ∞) + 1 := by
    rw [← Set.encard_coe_eq_coe_finsetCard, hfin.coe_toFinset, ht']
  have h3 : hfin.toFinset.card = 4 * s.card * (4 * r + 3) ^ r * (T + 1) ^ r + 1 := by
    exact_mod_cast h2
  omega

/-- Paper: Theorem B.4.4.7, pp. 625–626 (Fourier inversion on `C¹`, absolute convergence).
The Fourier coefficients `∫_{C¹} f(u) χ(u) du` of a test `f` on the idele classes, indexed by
the characters trivial on the image of the norm section `τ` (these restrict bijectively to the
characters of `C¹`), are absolutely summable.

Why it holds. `f` is invariant under an open subgroup `k` of the finite idele units, so its
coefficient vanishes unless `χ` is trivial on the image `k'` of `k` in `C¹`; `C¹/k'` is a
compact abelian Lie group (a torus times a finite group), and the characters trivial on `k'`
are those of `C¹/k'`. On `C¹/k'` the function `f` is smooth (it is smooth along the
archimedean flows), so its Fourier coefficients decay faster than any power of the frequency
and are absolutely summable. -/
theorem idelicExplicitFormula_normOneFourier_summable (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) :
    Summable (fun χ : chartChars(τ) ↦
      ‖∫ u, f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F‖) := by
  obtain ⟨k, hk, hinv, -⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 0
  obtain ⟨r, b, hb, C, d, hcount⟩ := idelicExplicitFormula_normOneFourier_count τ _hτ k hk
  exact explicitFormula_normOneFourier_summable_of_count τ f k hinv r b hb C d hcount

/-- Paper: Theorem B.4.4.7, pp. 625–626 (Fourier inversion on `C¹`). For a test `f` on the
idele classes and a norm-one class `c`, the Fourier series of `f` on the compact group `C¹`
converges absolutely to `f(c)`: summed over the characters trivial on the image of the norm
section `τ` (these restrict bijectively to the characters of `C¹`), the coefficients
`vol(C¹)⁻¹ ∫_{C¹} f(u) χ(u) du` times `χ(c)⁻¹` have sum `f(c)`.

Proof. The coefficients are absolutely summable
(`idelicExplicitFormula_normOneFourier_summable`), so the series converges uniformly on `C¹`
to a continuous function `g`. By orthogonality of characters, `g` has the same Fourier
coefficients as `f`. The characters of `C[F]` separate points, and each agrees on `C¹` with one
trivial on the image of `τ`; by Stone–Weierstrass a continuous function on `C¹` all of whose
Fourier coefficients vanish is zero, so `f = g` on `C¹`. -/
theorem idelicExplicitFormula_normOneFourierInversion (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (c : (ideleClassNorm F).ker) :
    HasSum (fun χ : chartChars(τ) ↦ ((classVolume : ℂ)⁻¹ *
      ∫ u, f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) *
        (((χ.val (c : C[F]))⁻¹ : Circle) : ℂ)) (f.val c) := by
  -- Measure-theoretic setup on `C¹` (the Tamagawa measure lives on the subtype σ-algebra).
  let K := (ideleClassNorm F).ker
  let μ := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let mK : MeasurableSpace K := Subtype.instMeasurableSpace
  have hB : @BorelSpace K _ mK := Subtype.borelSpace _
  let : CompactSpace K := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have : @MeasurableMul K mK _ := @ContinuousMul.measurableMul _ _ mK hB _ _
  have : IsFiniteMeasure μ :=
    ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  have hvol : (classVolume : ℂ) ≠ 0 := by
    have h0 : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨h0, measure_ne_top _ _⟩)
  -- The coefficients and the characters as continuous functions on `C¹`.
  let fK : C(K, ℂ) := ⟨fun u ↦ f.val (u : C[F]),
    (explicitTest_continuous f).comp continuous_subtype_val⟩
  let chr : U[F] → C(K, ℂ) := fun ψ ↦ ⟨fun u ↦ (ψ (u : C[F]) : ℂ),
    continuous_subtype_val.comp (ψ.continuous.comp continuous_subtype_val)⟩
  let a : chartChars(τ) → ℂ := fun χ ↦ (classVolume : ℂ)⁻¹ *
    ∫ u, f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ) ∂μ
  have ha : Summable (fun χ ↦ ‖a χ‖) := by
    refine ((idelicExplicitFormula_normOneFourier_summable τ _hτ f).mul_left
      ‖(classVolume : ℂ)⁻¹‖).congr fun χ ↦ ?_
    simp only [a, norm_mul]
    rfl
  let e : chartChars(τ) → C(K, ℂ) := fun χ ↦ a χ • chr χ.val⁻¹
  have he : Summable e := by
    refine ha.of_norm_bounded fun χ ↦ ?_
    rw [norm_smul]
    refine mul_le_of_le_one_right (norm_nonneg _) ((ContinuousMap.norm_le _ zero_le_one).mpr
      fun u ↦ ?_)
    change ‖((χ.val⁻¹ (u : C[F]) : Circle) : ℂ)‖ ≤ 1
    exact (Circle.norm_coe _).le
  obtain ⟨g, hg⟩ := he
  -- Orthogonality: the coefficients of `g` are those of `f`.
  have hcoef (χ' : chartChars(τ)) :
      ∫ u, (fK - g) u * (χ'.val (u : C[F]) : ℂ) ∂μ = 0 := by
    obtain ⟨L, hL⟩ := explicitFormula_exists_integralCLM μ (chr χ'.val)
    have hLe (χ : chartChars(τ)) : L (e χ) = if χ = χ' then a χ' * classVolume else 0 := by
      rw [hL]
      simp only [e, chr, ContinuousMap.smul_apply, ContinuousMap.coe_mk, smul_eq_mul, mul_assoc]
      rw [integral_const_mul]
      convert congrArg (a χ * ·) (explicitFormula_integral_chartChar_inv_mul τ _hτ χ χ') using 1
      split_ifs with hχ
      · subst hχ; rfl
      · rw [mul_zero]
    have h1 : HasSum (fun χ ↦ L (e χ)) (L g) := hg.mapL L
    simp_rw [hLe] at h1
    have h2 := h1.unique (hasSum_ite_eq χ' (a χ' * classVolume))
    have hf : L fK = a χ' * classVolume := by
      rw [hL]
      simp only [a, fK, chr, ContinuousMap.coe_mk]
      field_simp
    calc ∫ u, (fK - g) u * (χ'.val (u : C[F]) : ℂ) ∂μ = L (fK - g) := (hL _).symm
      _ = 0 := by rw [map_sub, hf, h2, sub_self]
  -- Completeness of the characters of `C¹`.
  let S : Subgroup (PontryaginDual K) :=
    (PontryaginDual.map ⟨K.subtype, continuous_subtype_val⟩).toMonoidHom.range
  have hS (x : K) (hx : x ≠ 1) : ∃ ψ ∈ S, ψ x ≠ 1 := by
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (G := C[F])
      (x := (x : C[F])) fun h ↦ hx (Subtype.ext h)
    exact ⟨_, ⟨ψ, rfl⟩, hψ⟩
  have hzero := @explicitFormula_eq_zero_of_integral_character K _ _ _ _ _ mK hB μ _ S hS
    (fK - g) (by
      rintro _ ⟨ψ, rfl⟩
      obtain ⟨χ, hχ⟩ := explicitFormula_exists_chartChar τ _hτ ψ
      refine (integral_congr_ae (.of_forall fun u ↦ ?_)).trans (hcoef χ)
      change (fK - g) u * (ψ (u : C[F]) : ℂ) = (fK - g) u * (χ.val (u : C[F]) : ℂ)
      rw [hχ])
  have hfg : f.val c = g c := by
    have h := congrArg (fun h : C(K, ℂ) ↦ h c) hzero
    rw [ContinuousMap.sub_apply, ContinuousMap.zero_apply, sub_eq_zero] at h
    exact h
  rw [hfg]
  have h := hg.mapL (ContinuousMap.evalCLM ℂ c)
  refine h.congr_fun fun χ ↦ ?_
  rfl

/-- Paper: Theorem B.4.4.7, pp. 625–626 (Fourier inversion on `C¹` at the identity). The
values at `0` of the radial profiles `Φ_χ` of a test `f` (fixed by their Mellin transforms
as in `idelicExplicitFormula_finiteMatching`) sum over the characters trivial on the image
of the norm section to `f(1)`.

Proof. `Φ_χ(0) = vol(C¹)⁻¹ ∫_{C¹} f(u) χ(u) du` (the Mellin transform on the imaginary axis is
the Fourier transform, which determines a Schwartz function), and
`idelicExplicitFormula_normOneFourierInversion` at the identity. -/
theorem idelicExplicitFormula_finiteMatching_inversion (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    HasSum (fun χ : chartChars(τ) ↦ Φ χ 0) (f.val 1) := by
  have h := idelicExplicitFormula_normOneFourierInversion τ _hτ f 1
  have h0 : radialFlow(τ, (0 : ℝ)) = 1 := by
    rw [ofAdd_zero, map_one, map_one]
  simp only [OneMemClass.coe_one, map_one, inv_one, Circle.coe_one, mul_one] at h
  convert h using 2 with χ
  rw [explicitFormula_profile_eq τ _hτ f Φ _hM χ 0, h0]
  simp only [one_mul]

local notation "conductorExponents(" χ ", " v ")" =>
  ({n : ℕ | ∀ u : (HeightOneSpectrum.adicCompletion F v)ˣ, ‖u.val‖ = 1 →
    ‖u.val - 1‖ ≤ q(v) ^ (-(n : ℤ)) →
      χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1} : Set ℕ)

section ExplicitFormulaFiniteLocal

/-- The class norm is bounded above and below on the support of a test. -/
private theorem explicitFormula_tsupport_norm_bound (f : 𝒟(C[F])) :
    ∃ M : ℝ, ∀ g ∈ tsupport f.val, ((ideleClassNorm F g : ℝ≥0) : ℝ) ≤ M ∧
      ((ideleClassNorm F g : ℝ≥0) : ℝ)⁻¹ ≤ M := by
  let n : C[F] → ℝ := fun g ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hpos (g : C[F]) : 0 < n g := NNReal.coe_pos.mpr (Units.zero_lt _)
  obtain ⟨M₁, hM₁⟩ := f.property.2.exists_bound_of_continuousOn hn.continuousOn
  obtain ⟨M₂, hM₂⟩ := f.property.2.exists_bound_of_continuousOn
    (hn.inv₀ fun g ↦ (hpos g).ne').continuousOn
  refine ⟨max M₁ M₂, fun g hg ↦ ⟨?_, ?_⟩⟩
  · have h := hM₁ g hg
    rw [Real.norm_eq_abs, abs_of_pos (hpos g)] at h
    exact h.trans (le_max_left _ _)
  · have h := hM₂ g hg
    rw [Pi.inv_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos g))] at h
    exact h.trans (le_max_right _ _)

/-- The radial profiles of a test vanish outside a fixed interval, uniformly in the
character. -/
private theorem explicitFormula_profile_support (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2))
    {M : ℝ} (hMb : ∀ g ∈ tsupport f.val, ((ideleClassNorm F g : ℝ≥0) : ℝ) ≤ M ∧
      ((ideleClassNorm F g : ℝ≥0) : ℝ)⁻¹ ≤ M)
    (χ : chartChars(τ)) (y : ℝ) (hy : Φ χ y ≠ 0) :
    Real.exp y ≤ M ∧ Real.exp (-y) ≤ M := by
  rw [explicitFormula_profile_eq τ hτ f Φ hM χ y] at hy
  have hI := right_ne_zero_of_mul hy
  obtain ⟨u, hu⟩ : ∃ u : (ideleClassNorm F).ker,
      f.val (radialFlow(τ, y) * (u : C[F])) ≠ 0 := by
    by_contra h
    push Not at h
    refine hI (integral_eq_zero_of_ae (.of_forall fun u ↦ ?_))
    simp only [h u, zero_mul, Pi.zero_apply]
  have hn : ((ideleClassNorm F (radialFlow(τ, y) * (u : C[F])) : ℝ≥0) : ℝ) = Real.exp y := by
    rw [map_mul, hτ, MonoidHom.mem_ker.mp u.property, mul_one]
    have h := positiveRealLogEquiv_apply (positiveRealLogEquiv.symm (Multiplicative.ofAdd y))
    rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))).symm.trans
      (congrArg Real.exp h.symm)
  obtain ⟨h1, h2⟩ := hMb _ (subset_tsupport _ hu)
  rw [hn] at h1 h2
  exact ⟨h1, by rwa [Real.exp_neg]⟩

/-- At a place where a test is invariant under the integer units, the radial profile of a
character ramified there vanishes at `0` (orthogonality of characters on `C¹`). -/
private theorem explicitFormula_profile_ramified (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2))
    (v : Primes(F))
    (hv : ∀ u ∈ (O(v)).units, ∀ g : C[F], f.val (g * finiteClassMap(v) u) = f.val g)
    (χ : chartChars(τ)) (hχ : sInf (conductorExponents(χ.val, v)) ≠ 0) : Φ χ 0 = 0 := by
  obtain ⟨u, hu1, hχu⟩ : ∃ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 ∧
      χ.val (finiteClassMap(v) u) ≠ 1 := by
    have h0 : (0 : ℕ) ∉ conductorExponents(χ.val, v) := fun h ↦
      hχ (Nat.sInf_eq_zero.mpr (Or.inl h))
    simp only [Set.mem_ofPred_eq, not_forall] at h0
    obtain ⟨u, h1, -, h⟩ := h0
    exact ⟨u, h1, h⟩
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have huO : u ∈ (O(v)).units := by
    by_contra h
    rcases explicitFormula_finiteUnits_norm_shell v u h with h' | h'
    · rw [hu1] at h'
      linarith
    · rw [hu1] at h'
      have := inv_lt_one_of_one_lt₀ hq
      linarith
  have hw : finiteClassMap(v) u ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
    ext
    change ‖u.val‖ = 1
    exact hu1
  let w : (ideleClassNorm F).ker := ⟨_, hw⟩
  have h0 : radialFlow(τ, (0 : ℝ)) = 1 := by
    rw [ofAdd_zero, map_one, map_one]
  rw [explicitFormula_profile_eq τ hτ f Φ hM χ 0, h0]
  simp only [one_mul]
  let mK : MeasurableSpace (ideleClassNorm F).ker := Subtype.instMeasurableSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : BorelSpace C[F] := ⟨rfl⟩
  have hB : @BorelSpace (ideleClassNorm F).ker _ mK := Subtype.borelSpace _
  have : @MeasurableMul (ideleClassNorm F).ker mK _ := @ContinuousMul.measurableMul _ _ mK hB _ _
  set I := ∫ u, f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F
    with hIdef
  have hI : I = (χ.val (w : C[F]) : ℂ) * I := by
    rw [← integral_const_mul]
    refine (integral_mul_left_eq_self (μ := normOneIdeleClassTamagawaMeasure F)
      (fun u : (ideleClassNorm F).ker ↦ f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ)) w).symm.trans ?_
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    simp only [Subgroup.coe_mul, map_mul, Circle.coe_mul]
    rw [mul_comm (w : C[F]) (u : C[F]), hv _ huO]
    ring
  have hχw : (χ.val (w : C[F]) : ℂ) ≠ 1 := fun h ↦ hχu (Circle.ext h)
  have : (1 - (χ.val (w : C[F]) : ℂ)) * I = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
  rw [show I = 0 from (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχw.symm), mul_zero]

end ExplicitFormulaFiniteLocal

section ExplicitFormulaConductorLocal

/-- A test is invariant under a congruence subgroup of the units at each finite place. -/
private theorem explicitFormula_test_congruence_invariant (f : 𝒟(C[F])) (v : Primes(F)) :
    ∃ n : ℕ, ∀ u : (v.adicCompletion F)ˣ, ‖u.val - 1‖ ≤ q(v) ^ (-(n : ℤ)) →
      ∀ g : C[F], f.val (g * finiteClassMap(v) u) = f.val g := by
  obtain ⟨k, hk, hinv, _⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 0
  obtain ⟨V, hVo, -, hVk⟩ := explicitFormula_finiteUnits_good v (G := C[F]) finiteClassMap(v)
    (continuous_ideleClass_ofAdicCompletion F v) k hk
  have hV : (V : Set (v.adicCompletion F)ˣ) ∈ 𝓝 1 := hVo.mem_nhds V.one_mem
  rw [(Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).isInducing.nhds_eq_comap,
    Units.val_one] at hV
  obtain ⟨S, hS, hSV⟩ := mem_comap.mp hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  refine ⟨n, fun u hu g ↦ ?_⟩
  have huV : u ∈ V := hSV (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    refine hu.trans_lt ?_
    rwa [zpow_neg, zpow_natCast, ← inv_pow]))
  rw [mul_comm]
  exact hinv ⟨_, hVk u huV⟩ g

/-- Termwise integration of an absolutely summable family of uniformly bounded functions
against a finite measure, without a countability assumption on the index type (the terms
with nonzero coefficient form a countable family). -/
private theorem explicitFormula_hasSum_integral {ι X : Type*} {mX : MeasurableSpace X}
    (ν : Measure X) [IsFiniteMeasure ν] (c : ι → ℂ) (hc : Summable (fun i ↦ ‖c i‖))
    (φ : ι → X → ℂ) (hφ : ∀ i, AEStronglyMeasurable (φ i) ν) (B : ℝ)
    (hB : ∀ i, c i ≠ 0 → ∀ᵐ x ∂ν, ‖φ i x‖ ≤ B) (g : X → ℂ)
    (hg : ∀ᵐ x ∂ν, HasSum (fun i ↦ c i * φ i x) (g x)) :
    HasSum (fun i ↦ ∫ x, c i * φ i x ∂ν) (∫ x, g x ∂ν) := by
  let s := Function.support c
  have hs : s.Countable := by
    have := hc.countable_support
    simpa [s, Function.support, norm_eq_zero] using this
  have : Countable s := hs.to_subtype
  have hsupp : Function.support (fun i ↦ ∫ x, c i * φ i x ∂ν) ⊆ s := by
    intro i hi
    by_contra h
    simp only [s, Function.mem_support, not_not] at h
    simp [h] at hi
  refine (hasSum_subtype_iff_of_support_subset hsupp).mp ?_
  refine hasSum_integral_of_dominated_convergence (fun i _ ↦ ‖c i‖ * B)
    (fun i ↦ (hφ i).const_mul _) (fun i ↦ ?_) (.of_forall fun _ ↦ ?_) (integrable_const _) ?_
  · filter_upwards [hB i i.property] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · exact (hc.comp_injective Subtype.val_injective).mul_right B
  · filter_upwards [hg] with x hx
    have hsx : Function.support (fun i ↦ c i * φ i x) ⊆ s := by
      intro i hi
      by_contra h
      simp only [s, Function.mem_support, not_not] at h
      simp [h] at hi
    exact (hasSum_subtype_iff_of_support_subset hsx).mpr hx

end ExplicitFormulaConductorLocal

section ExplicitFormulaConductorCharacter

/-- The unit filtration `U_j = {u : ‖u‖ = 1, ‖u - 1‖ ≤ q_v^{-j}}` of a finite completion
(`U_0` is the group of integer units). -/
private def explicitFormula_unitFiltration (v : Primes(F)) (j : ℕ) :
    Subgroup (v.adicCompletion F)ˣ where
  carrier := {u | ‖u.val‖ = 1 ∧ ‖u.val - 1‖ ≤ q(v) ^ (-(j : ℤ))}
  mul_mem' := by
    rintro a b ⟨ha1, ha⟩ ⟨hb1, hb⟩
    refine ⟨by rw [Units.val_mul, norm_mul, ha1, hb1, one_mul], ?_⟩
    have e : (a * b).val - 1 = a.val * (b.val - 1) + (a.val - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
    rw [norm_mul, ha1, one_mul]
    exact hb
  one_mem' := by
    refine ⟨by rw [Units.val_one, norm_one], ?_⟩
    rw [Units.val_one, sub_self, norm_zero]
    have hq : (0 : ℝ) < q(v) := by
      exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
    positivity
  inv_mem' := by
    rintro a ⟨ha1, ha⟩
    have hne : a.val ≠ 0 := a.ne_zero
    refine ⟨by rw [Units.val_inv_eq_inv_val, norm_inv, ha1, inv_one], ?_⟩
    have e : (a⁻¹).val - 1 = a.val⁻¹ * (1 - a.val) := by
      rw [Units.val_inv_eq_inv_val]; field_simp
    rw [e, norm_mul, norm_inv, ha1, inv_one, one_mul, norm_sub_rev]
    exact ha

private theorem explicitFormula_mem_unitFiltration (v : Primes(F)) (j : ℕ)
    (u : (v.adicCompletion F)ˣ) :
    u ∈ explicitFormula_unitFiltration v j ↔
      ‖u.val‖ = 1 ∧ ‖u.val - 1‖ ≤ q(v) ^ (-(j : ℤ)) := Iff.rfl

private theorem explicitFormula_unitFiltration_measurable (v : Primes(F)) (j : ℕ) :
    MeasurableSet (explicitFormula_unitFiltration v j : Set (v.adicCompletion F)ˣ) := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have hc : IsClosed {u : (v.adicCompletion F)ˣ |
      ‖u.val‖ = 1 ∧ ‖u.val - 1‖ ≤ q(v) ^ (-(j : ℤ))} :=
    (isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const).inter
      (isClosed_le (continuous_norm.comp (Units.continuous_val.sub continuous_const))
        continuous_const)
  exact hc.measurableSet

/-- Norms on a finite completion are integral powers of `q_v`, so a norm below `q_v^n` is at
most `q_v^(n-1)`. -/
private theorem explicitFormula_norm_le_zpow_pred (v : Primes(F)) (x : v.adicCompletion F)
    (n : ℤ) (h : ‖x‖ < q(v) ^ n) : ‖x‖ ≤ q(v) ^ (n - 1) := by
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    positivity
  rw [norm_adicCompletion_eq_zpow F v hx] at h ⊢
  have := (zpow_lt_zpow_iff_right₀ hq).mp h
  exact zpow_le_zpow_right₀ hq.le (by omega)

/-- The truncated weight `1 / max(‖x‖, q^{-N})` grows by `q^{N+1} - q^N` on the ball of
radius `q^{-(N+1)}` and is unchanged elsewhere. -/
private theorem explicitFormula_filtrationWeight_succ (v : Primes(F)) (x : v.adicCompletion F)
    (N : ℕ) :
    (max ‖x‖ (q(v) ^ (-((N + 1 : ℕ) : ℤ))))⁻¹ =
      (max ‖x‖ (q(v) ^ (-(N : ℤ))))⁻¹ +
        (if ‖x‖ ≤ q(v) ^ (-((N + 1 : ℕ) : ℤ)) then q(v) ^ (N + 1) - q(v) ^ N else 0) := by
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hle : q(v) ^ (-((N + 1 : ℕ) : ℤ)) ≤ q(v) ^ (-(N : ℤ)) :=
    zpow_le_zpow_right₀ hq.le (by omega)
  split_ifs with h
  · rw [max_eq_right h, max_eq_right (h.trans hle), zpow_neg, zpow_neg, inv_inv, inv_inv,
      zpow_natCast, zpow_natCast]
    ring
  · push Not at h
    have h2 : q(v) ^ (-(N : ℤ)) ≤ ‖x‖ := by
      by_contra h3
      push Not at h3
      have h4 := explicitFormula_norm_le_zpow_pred v x _ h3
      have e : -(N : ℤ) - 1 = -((N + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e] at h4
      linarith
    rw [max_eq_left h.le, max_eq_left h2, add_zero]

/-- A character nontrivial on a filtration subgroup integrates to zero over it. -/
private theorem explicitFormula_integral_filtration_char (v : Primes(F)) (χ : U[F]) (j : ℕ)
    (w : (v.adicCompletion F)ˣ) (hw : w ∈ explicitFormula_unitFiltration v j)
    (hχ : χ (finiteClassMap(v) w) ≠ 1) :
    ∫ u in (explicitFormula_unitFiltration v j : Set (v.adicCompletion F)ˣ),
      (((χ (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) ∂μ𝔭(v) = 0 := by
  let K := v.adicCompletion F
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  let H := explicitFormula_unitFiltration v j
  have hHm : MeasurableSet (H : Set Kˣ) := explicitFormula_unitFiltration_measurable v j
  let η : Kˣ → ℂ := fun u ↦ (((χ (finiteClassMap(v) u))⁻¹ : Circle) : ℂ)
  have hη (a b : Kˣ) : η (a * b) = η a * η b := by
    simp only [η, map_mul, mul_inv, Circle.coe_mul]
  have hI : (∫ u in (H : Set Kˣ), η u ∂μ𝔭(v)) = η w * ∫ u in (H : Set Kˣ), η u ∂μ𝔭(v) := by
    rw [← integral_indicator hHm, ← integral_const_mul]
    refine (integral_mul_left_eq_self (μ := μ𝔭(v)) ((H : Set Kˣ).indicator η) w).symm.trans
      (integral_congr_ae (.of_forall fun u ↦ ?_))
    dsimp only
    by_cases hu : u ∈ H
    · have hwu : w * u ∈ H := H.mul_mem hw hu
      rw [indicator_of_mem (SetLike.mem_coe.mpr hwu), indicator_of_mem (SetLike.mem_coe.mpr hu),
        hη]
    · have hwu : w * u ∉ H := fun h ↦ hu (by
        have := H.mul_mem (H.inv_mem hw) h
        rwa [inv_mul_cancel_left] at this)
      rw [indicator_of_notMem (fun h ↦ hwu (SetLike.mem_coe.mp h)),
        indicator_of_notMem (fun h ↦ hu (SetLike.mem_coe.mp h)), mul_zero]
  have hne : η w ≠ 1 := by
    intro h
    apply hχ
    have h' : (χ (finiteClassMap(v) w))⁻¹ = 1 := Circle.ext (by rw [Circle.coe_one]; exact h)
    exact inv_eq_one.mp h'
  have h0 : (1 - η w) * (∫ u in (H : Set Kˣ), η u ∂μ𝔭(v)) = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hne))

/-- `(q_v^{k+1} - q_v^k) vol U_{k+1} = vol O_v^×`, from the additive measure: `μ` is
`q_v/(q_v - 1)` times additive measure on the norm-one sphere, `U_{k+1}` is a translate of the
ball of radius `q_v^{-(k+1)}`, and the sphere is the unit ball minus the ball of radius
`q_v^{-1}`. -/
private theorem explicitFormula_filtration_volume (v : Primes(F)) (k : ℕ) :
    (q(v) ^ (k + 1) - q(v) ^ k) *
      (μ𝔭(v)).real (explicitFormula_unitFiltration v (k + 1) : Set (v.adicCompletion F)ˣ) =
      V𝔭(v) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < q(v) := zero_lt_one.trans hq
  let D : ℝ → ℂ := fun r ↦
    ∫ y, (Metric.closedBall (0 : K) r).indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)
  have hDint (r : ℝ) :
      Integrable ((Metric.closedBall (0 : K) r).indicator (fun _ ↦ (1 : ℂ))) ν𝔭(v) :=
    ((continuousOn_const (c := (1 : ℂ))).integrableOn_compact
      (isCompact_closedBall (0 : K) r)).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  obtain ⟨p, hp⟩ : ∃ p : Kˣ, ‖p.val‖ = (q(v))⁻¹ := by
    let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨a, ha⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    exact ⟨Units.mk0 a ha.ne_zero, norm_uniformizer_adicCompletion v _ ha⟩
  have hDpow (m : ℕ) : D (q(v) ^ (-(m : ℤ))) = ((q(v) ^ (-(m : ℤ)) : ℝ) : ℂ) * D 1 := by
    have h := explicitFormula_closedBall_mass_mul v (p ^ m) 1
    have hn : ‖(p ^ m).val‖ = q(v) ^ (-(m : ℤ)) := by
      rw [Units.val_pow_eq_pow_val, norm_pow, hp, zpow_neg, zpow_natCast, inv_pow]
    rw [hn, mul_one] at h
    exact h
  have hball1 (y : K) (r : ℝ) (hr : r < 1) (hy : ‖y - 1‖ ≤ r) : ‖y‖ = 1 := by
    have h1 : ‖y - 1‖ ≠ ‖(1 : K)‖ := by rw [norm_one]; exact (hy.trans_lt hr).ne
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
    rw [sub_add_cancel, norm_one, max_eq_right (hy.trans hr.le)] at this
    exact this
  -- The filtration subgroup.
  set r : ℝ := q(v) ^ (-((k + 1 : ℕ) : ℤ)) with hr
  have hr1 : r < 1 := zpow_lt_one_of_neg₀ hq (by omega)
  let g : K → ℂ := (Metric.closedBall (1 : K) r).indicator (fun _ ↦ (1 : ℂ))
  have hgU : (fun u : Kˣ ↦ g u.val) =
      (explicitFormula_unitFiltration v (k + 1) : Set Kˣ).indicator (fun _ ↦ (1 : ℂ)) := by
    funext u
    have : u.val ∈ Metric.closedBall (1 : K) r ↔
        u ∈ (explicitFormula_unitFiltration v (k + 1) : Set Kˣ) := by
      rw [SetLike.mem_coe, explicitFormula_mem_unitFiltration, Metric.mem_closedBall,
        dist_eq_norm]
      exact ⟨fun h ↦ ⟨hball1 _ r hr1 h, h⟩, fun h ↦ h.2⟩
    simp only [g, indicator, this]
  have hgdiv : (fun y ↦ g y / ((‖y‖ : ℝ) : ℂ)) = g := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (1 : K) r
    · rw [hball1 y r hr1 (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy)]
      simp
    · simp [g, indicator_of_notMem hy]
  have hgtrans : (∫ y, g y ∂ν𝔭(v)) = D r := by
    change _ = ∫ y, (Metric.closedBall (0 : K) r).indicator (fun _ ↦ (1 : ℂ)) y ∂ν𝔭(v)
    rw [← integral_sub_right_eq_self (μ := ν𝔭(v))
      ((Metric.closedBall (0 : K) r).indicator (fun _ ↦ (1 : ℂ))) (1 : K)]
    congr 1
    funext y
    simp only [g, indicator, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hU := existsUnique_finiteWeilFourierDistribution_units_integral v g
  rw [hgU, integral_indicator_const _ (explicitFormula_unitFiltration_measurable v (k + 1)),
    hgdiv, hgtrans, hr, hDpow, Complex.real_smul, mul_one] at hU
  -- The integer units.
  let s : K → ℂ := (Metric.sphere (0 : K) 1).indicator (fun _ ↦ (1 : ℂ))
  have hOm : MeasurableSet ((O(v)).units : Set Kˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hsU : (fun u : Kˣ ↦ s u.val) =
      ((O(v)).units : Set Kˣ).indicator (fun _ ↦ (1 : ℂ)) := by
    funext u
    have : u.val ∈ Metric.sphere (0 : K) 1 ↔ u ∈ ((O(v)).units : Set Kˣ) := by
      rw [mem_sphere_zero_iff_norm, SetLike.mem_coe,
        HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
        Valued.toNormedField.norm_eq_one_iff]
    simp only [s, indicator, this]
  have hsdiv : (fun y ↦ s y / ((‖y‖ : ℝ) : ℂ)) = s := by
    funext y
    by_cases hy : y ∈ Metric.sphere (0 : K) 1
    · rw [mem_sphere_zero_iff_norm.mp hy]
      simp
    · simp [s, indicator_of_notMem hy]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = q(v) ^ (-((1 : ℕ) : ℤ)) := ⟨_, rfl⟩
  have hq1 : c < 1 := hc ▸ zpow_lt_one_of_neg₀ hq (by norm_num)
  have hdisc (y : K) (h : ‖y‖ < 1) : ‖y‖ ≤ c := by
    have := explicitFormula_norm_le_zpow_pred v y 0 (by rwa [zpow_zero])
    rw [hc]
    simpa using this
  have hsdiff : s = fun y ↦ (Metric.closedBall (0 : K) 1).indicator (fun _ ↦ (1 : ℂ)) y -
      (Metric.closedBall (0 : K) c).indicator (fun _ ↦ (1 : ℂ)) y := by
    funext y
    simp only [s, indicator, mem_sphere_zero_iff_norm, Metric.mem_closedBall, dist_zero_right]
    by_cases h1 : ‖y‖ = 1
    · simp [h1, not_le.mpr hq1]
    · by_cases h2 : ‖y‖ ≤ 1
      · have h3 : ‖y‖ ≤ c := hdisc y (lt_of_le_of_ne h2 h1)
        simp [h1, h2, h3]
      · have h3 : ¬ ‖y‖ ≤ c := fun h ↦ h2 (h.trans hq1.le)
        simp [h1, h2, h3]
  have hO := existsUnique_finiteWeilFourierDistribution_units_integral v s
  rw [hsU, integral_indicator_const _ hOm, hsdiv, hsdiff, integral_sub (hDint 1) (hDint _),
    Complex.real_smul, mul_one] at hO
  change _ = _ * (D 1 - D c) at hO
  rw [hc, hDpow 1] at hO
  -- Combine.
  apply Complex.ofReal_injective
  change (((q(v) ^ (k + 1) - q(v) ^ k) * (μ𝔭(v)).real _ : ℝ) : ℂ) =
    (((μ𝔭(v)).real ((O(v)).units : Set Kˣ) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, hU, hO]
  have key : (q(v) ^ (k + 1) - q(v) ^ k) * q(v) ^ (-((k + 1 : ℕ) : ℤ)) =
      1 - q(v) ^ (-((1 : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_one]
    field_simp
    ring
  have keyc := congrArg (fun x : ℝ ↦ (x : ℂ)) key
  push_cast at keyc ⊢
  linear_combination ((q(v) : ℂ) / ((q(v) : ℂ) - 1) * D 1) * keyc


/-- The conductor integral truncated at level `N < a`: with the weight
`1 / max(|1 - u|, q^{-N})` it is `-(N + 1) vol O_v^×`. -/
private theorem explicitFormula_conductor_partial (v : Primes(F)) (χ : U[F]) (a : ℕ)
    (ha : ∀ n < a, n ∉ conductorExponents(χ, v)) (N : ℕ) (hN : N < a) :
    ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ),
      ((((χ (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) - 1) *
        (((max ‖1 - u.val‖ (q(v) ^ (-(N : ℤ))))⁻¹ : ℝ) : ℂ) ∂μ𝔭(v) =
      -(((N + 1 : ℕ) : ℂ) * (V𝔭(v) : ℂ)) := by
  let K := v.adicCompletion F
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  let O := ((O(v)).units : Set Kˣ)
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hOm : MeasurableSet O :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hOc : IsCompact O := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hO1 (u : Kˣ) : u ∈ O ↔ ‖u.val‖ = 1 := by
    change u ∈ (O(v)).units ↔ _
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      Valued.toNormedField.norm_eq_one_iff]
  have hsub1 (u : Kˣ) (hu : u ∈ O) : ‖1 - u.val‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_one, norm_neg, (hO1 u).mp hu, max_self]
  let η : Kˣ → ℂ := fun u ↦ (((χ (finiteClassMap(v) u))⁻¹ : Circle) : ℂ)
  have hηc : Continuous η := continuous_subtype_val.comp
    ((χ.continuous.comp (continuous_ideleClass_ofAdicCompletion F v)).inv)
  have hηI : IntegrableOn η O μ𝔭(v) := hηc.continuousOn.integrableOn_compact hOc
  have h1I : IntegrableOn (fun _ ↦ (1 : ℂ)) O μ𝔭(v) :=
    continuousOn_const.integrableOn_compact hOc
  have hwc (M : ℕ) : Continuous (fun u : Kˣ ↦
      (((max ‖1 - u.val‖ (q(v) ^ (-(M : ℤ))))⁻¹ : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp (Continuous.inv₀
      ((continuous_norm.comp (continuous_const.sub Units.continuous_val)).max continuous_const)
      fun u ↦ ?_)
    exact (lt_max_of_lt_right (zpow_pos (zero_lt_one.trans hq) _)).ne'
  have hVO : (∫ u in O, (1 : ℂ) ∂μ𝔭(v)) = (V𝔭(v) : ℂ) := by
    rw [setIntegral_const, Complex.real_smul, mul_one]
    rfl
  have hnon (n : ℕ) (hn : n < a) :
      ∃ w ∈ explicitFormula_unitFiltration v n, χ (finiteClassMap(v) w) ≠ 1 := by
    have h := ha n hn
    simp only [Set.mem_ofPred_eq, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, ⟨h1, h2⟩, h3⟩
  induction N with
  | zero =>
    have e : ∀ u ∈ O, (η u - 1) *
        (((max ‖1 - u.val‖ (q(v) ^ (-((0 : ℕ) : ℤ))))⁻¹ : ℝ) : ℂ) = η u - 1 := by
      intro u hu
      rw [Nat.cast_zero, neg_zero, zpow_zero, max_eq_right (hsub1 u hu), inv_one,
        Complex.ofReal_one, mul_one]
    change ∫ u in O, (η u - 1) * _ ∂μ𝔭(v) = _
    rw [setIntegral_congr_fun hOm e, integral_sub hηI h1I, hVO]
    obtain ⟨w, hw, hχw⟩ := hnon 0 hN
    have hset : (explicitFormula_unitFiltration v 0 : Set Kˣ) = O := by
      ext u
      rw [SetLike.mem_coe, explicitFormula_mem_unitFiltration, hO1]
      refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
      rw [Nat.cast_zero, neg_zero, zpow_zero, norm_sub_rev]
      exact hsub1 u ((hO1 u).mpr h)
    have h0 := explicitFormula_integral_filtration_char v χ 0 w hw hχw
    rw [hset] at h0
    change (∫ u in O, η u ∂μ𝔭(v)) - _ = _
    rw [h0]
    simp
  | succ N ih =>
    have ihN := ih (by omega)
    obtain ⟨w, hw, hχw⟩ := hnon (N + 1) hN
    let H := explicitFormula_unitFiltration v (N + 1)
    have hHm : MeasurableSet (H : Set Kˣ) := explicitFormula_unitFiltration_measurable v (N + 1)
    have hHO : (H : Set Kˣ) ⊆ O := fun u hu ↦ (hO1 u).mpr hu.1
    have e : ∀ u ∈ O, (η u - 1) *
        (((max ‖1 - u.val‖ (q(v) ^ (-((N + 1 : ℕ) : ℤ))))⁻¹ : ℝ) : ℂ) =
        (η u - 1) * (((max ‖1 - u.val‖ (q(v) ^ (-(N : ℤ))))⁻¹ : ℝ) : ℂ) +
          ((q(v) ^ (N + 1) - q(v) ^ N : ℝ) : ℂ) *
            (H : Set Kˣ).indicator (fun u ↦ η u - 1) u := by
      intro u hu
      rw [explicitFormula_filtrationWeight_succ v (1 - u.val) N]
      have hmem : u ∈ H ↔ ‖1 - u.val‖ ≤ q(v) ^ (-((N + 1 : ℕ) : ℤ)) := by
        rw [explicitFormula_mem_unitFiltration, norm_sub_rev]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨(hO1 u).mp hu, h⟩⟩
      by_cases h : ‖1 - u.val‖ ≤ q(v) ^ (-((N + 1 : ℕ) : ℤ))
      · rw [ite_eq_left h, indicator_of_mem (SetLike.mem_coe.mpr (hmem.mpr h))]
        push_cast
        ring
      · rw [ite_eq_right h, indicator_of_notMem (fun h' ↦ h (hmem.mp (SetLike.mem_coe.mp h')))]
        push_cast
        ring
    change ∫ u in O, (η u - 1) * _ ∂μ𝔭(v) = _
    have hI1 : IntegrableOn (fun u ↦ (η u - 1) *
        (((max ‖1 - u.val‖ (q(v) ^ (-(N : ℤ))))⁻¹ : ℝ) : ℂ)) O μ𝔭(v) :=
      ((hηc.sub continuous_const).mul (hwc N)).continuousOn.integrableOn_compact hOc
    have hI2 : Integrable ((H : Set Kˣ).indicator (fun u ↦ η u - 1)) (μ𝔭(v).restrict O) :=
      (hηI.sub h1I).integrable.indicator hHm
    rw [setIntegral_congr_fun hOm e, integral_add hI1 (hI2.const_mul _), integral_const_mul]
    change (∫ u in O, (η u - 1) * _ ∂μ𝔭(v)) + _ = _
    rw [ihN, integral_indicator hHm, Measure.restrict_restrict hHm, inter_eq_left.mpr hHO,
      integral_sub (hηI.mono_set hHO) (h1I.mono_set hHO),
      explicitFormula_integral_filtration_char v χ (N + 1) w hw hχw, setIntegral_const,
      Complex.real_smul, mul_one]
    have hvol := congrArg (fun x : ℝ ↦ (x : ℂ)) (explicitFormula_filtration_volume v N)
    simp only [Complex.ofReal_mul] at hvol
    rw [← hvol]
    push_cast
    ring

end ExplicitFormulaConductorCharacter

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (conductor integral of one character).
For a character `χ` of the idele classes and a finite place `v` where its conductor exponent is
`a` (the least `n` with `χ` trivial on the image of `1 + 𝔭_v^n` in the norm-one units),
`∫_{O_v^×} (χ(u)⁻¹ - 1) |u|^{1/2} / |1 - u| d^×u = -a · vol O_v^×`.

Computation. The integrand vanishes on `U_a = 1 + 𝔭_v^a` (all of `O_v^×` if `a = 0`). Write
`η` for `u ↦ χ(u)⁻¹` on `O_v^×` and `U_0 = O_v^×`. On `U_j \ U_{j+1}` the weight is `q_v^j`,
and `∫_{U_j} η` is `0` for `j < a` and `vol U_j` for `j ≥ a`. With `vol U_j =
vol O_v^× / ((q_v - 1) q_v^{j-1})` for `j ≥ 1`, the shells `j = 0`, `1 ≤ j ≤ a - 2` and
`j = a - 1` give `-(q_v - 2)/(q_v - 1)`, `-1` each, and `-q_v/(q_v - 1)` times `vol O_v^×`
(for `a = 1`, only `j = 0`, giving `-1`), in total `-a · vol O_v^×`. -/
theorem idelicExplicitFormula_conductorLocal_character (v : Primes(F)) (χ : U[F]) :
    ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ),
        ((((χ (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) - 1) *
          ((Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ)) ∂μ𝔭(v) =
      -(((sInf (conductorExponents(χ, v)) : ℕ) : ℂ) * (V𝔭(v) : ℂ)) := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  obtain ⟨n, -, hn⟩ := exists_heckeConductorExponents χ
  rw [(hn v).csInf_eq]
  have hmem := (hn v).1
  have hlow : ∀ m < n v, m ∉ conductorExponents(χ, v) :=
    fun m hm h ↦ absurd ((hn v).2 h) (not_le.mpr hm)
  have hOm : MeasurableSet ((O(v)).units : Set (v.adicCompletion F)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hO1 (u : (v.adicCompletion F)ˣ) (hu : u ∈ ((O(v)).units : Set (v.adicCompletion F)ˣ)) :
      ‖u.val‖ = 1 := by
    rw [SetLike.mem_coe, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hu
    exact Valued.toNormedField.norm_eq_one_iff.mpr hu
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  cases hnv : n v with
  | zero =>
    rw [hnv] at hmem
    have hmem' : ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
        ‖u.val - 1‖ ≤ q(v) ^ (-((0 : ℕ) : ℤ)) → χ (finiteClassMap(v) u) = 1 := hmem
    rw [Nat.cast_zero, zero_mul, neg_zero]
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ ?_
    have h1 := hO1 u hu
    have h2 : ‖u.val - 1‖ ≤ q(v) ^ (-((0 : ℕ) : ℤ)) := by
      rw [Nat.cast_zero, neg_zero, zpow_zero]
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_one, h1, max_self]
    rw [hmem' u h1 h2, inv_one, Circle.coe_one, sub_self, zero_mul]
  | succ N =>
    rw [hnv] at hmem hlow
    have hmem' : ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
        ‖u.val - 1‖ ≤ q(v) ^ (-((N + 1 : ℕ) : ℤ)) → χ (finiteClassMap(v) u) = 1 := hmem
    rw [← explicitFormula_conductor_partial v χ (N + 1) hlow N (Nat.lt_succ_self N)]
    refine setIntegral_congr_fun hOm fun u hu ↦ ?_
    have h1 := hO1 u hu
    by_cases h : ‖u.val - 1‖ ≤ q(v) ^ (-((N + 1 : ℕ) : ℤ))
    · rw [hmem' u h1 h, inv_one, Circle.coe_one, sub_self, zero_mul, zero_mul]
    · push Not at h
      have h2 : q(v) ^ (-(N : ℤ)) ≤ ‖1 - u.val‖ := by
        rw [norm_sub_rev]
        by_contra h3
        push Not at h3
        have h4 := explicitFormula_norm_le_zpow_pred v _ _ h3
        have e : -(N : ℤ) - 1 = -((N + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e] at h4
        linarith
      rw [max_eq_left h2, h1, Real.sqrt_one, Complex.ofReal_one, Complex.ofReal_inv, one_div]

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (conductor terms at one place). Summed
over the characters trivial on the image of the norm section, `log q_v` times the conductor
exponent at `v` times `Φ_χ(0)` gives minus
`(log q_v / vol O_v^×) ∫_{O_v^×} (f_v(u) - f_v(1)) |u|^{1/2} / |1 - u| d^×u`.

Proof. `Φ_χ(0)` is the Fourier coefficient `c_χ` of `f` on `C¹`, and Fourier inversion on `C¹`
at `u` and at `1` gives `f_v(u) - f_v(1) = ∑_χ c_χ (χ(u)⁻¹ - 1)` for `u ∈ O_v^×`. `f` is
invariant under some `1 + 𝔭_v^n`, so `c_χ = 0` unless `χ` is trivial there; the remaining terms
vanish on `1 + 𝔭_v^n` and are bounded by `2 q_v^n |c_χ|` elsewhere, and the coefficients are
absolutely summable, so the series may be integrated termwise. Each term is
`-a_v(χ) vol O_v^× · c_χ` (`idelicExplicitFormula_conductorLocal_character`). -/
theorem idelicExplicitFormula_finiteMatching_conductorLocal (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (testF : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_hF : ∀ v u, (testF v).val u = f.val (finiteClassMap(v) u))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) (v : Primes(F)) :
    HasSum (fun χ : chartChars(τ) ↦
        ((Real.log q(v) * (sInf (conductorExponents(χ.val, v)) : ℕ) : ℝ) : ℂ) * Φ χ 0)
      (-(finiteWeilScale(v) *
        ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ),
          ((testF v).val u - (testF v).val 1) * (Real.sqrt ‖u.val‖ : ℂ) /
            ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ𝔭(v))) := by
  let O := ((O(v)).units : Set (v.adicCompletion F)ˣ)
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hV : V𝔭(v) ≠ 0 := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
  have hfin : μ𝔭(v) O ≠ ⊤ := (ENNReal.toReal_ne_zero.mp hV).2
  have : IsFiniteMeasure (μ𝔭(v).restrict O) := isFiniteMeasure_restrict.mpr hfin
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have hOm : MeasurableSet O :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hker (u : (v.adicCompletion F)ˣ) (hu : ‖u.val‖ = 1) : finiteClassMap(v) u ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
    ext
    change ‖u.val‖ = 1
    exact hu
  have hO1 (u : (v.adicCompletion F)ˣ) (hu : u ∈ O) : ‖u.val‖ = 1 := by
    have hmem : u ∈ (O(v)).units ↔ ‖u.val‖ = 1 := by
      rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
        Valued.toNormedField.norm_eq_one_iff]
    exact hmem.mp hu
  -- The coefficients.
  let c : chartChars(τ) → ℂ := fun χ ↦ (classVolume : ℂ)⁻¹ *
    ∫ u, f.val (u : C[F]) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F
  have hΦc (χ : chartChars(τ)) : Φ χ 0 = c χ := by
    have h0 : radialFlow(τ, (0 : ℝ)) = 1 := by
      rw [ofAdd_zero, map_one, map_one]
    rw [explicitFormula_profile_eq τ _hτ f Φ _hM χ 0, h0]
    simp only [one_mul]
    rfl
  have hc : Summable (fun χ ↦ ‖c χ‖) := by
    refine ((idelicExplicitFormula_normOneFourier_summable τ _hτ f).mul_left
      ‖(classVolume : ℂ)⁻¹‖).congr fun χ ↦ ?_
    simp only [c, norm_mul]
  obtain ⟨n, hn⟩ := explicitFormula_test_congruence_invariant f v
  have hcz (χ : chartChars(τ)) (hχ : c χ ≠ 0) (u : (v.adicCompletion F)ˣ) (hu1 : ‖u.val‖ = 1)
      (hu : ‖u.val - 1‖ ≤ q(v) ^ (-(n : ℤ))) : χ.val (finiteClassMap(v) u) = 1 := by
    by_contra h
    refine hχ ?_
    simp only [c]
    rw [explicitFormula_coeff_eq_zero_of_invariant f χ.val ⟨finiteClassMap(v) u, hker u hu1⟩ (hn u hu) h,
      mul_zero]
  -- The weight and the expansion on the integer units.
  let w : (v.adicCompletion F)ˣ → ℂ :=
    fun u ↦ (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ)
  let φ : chartChars(τ) → (v.adicCompletion F)ˣ → ℂ :=
    fun χ u ↦ ((((χ.val (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) - 1) * w u
  have hexp (u : (v.adicCompletion F)ˣ) (hu : u ∈ O) :
      HasSum (fun χ ↦ c χ * φ χ u) ((f.val (finiteClassMap(v) u) - f.val 1) * w u) := by
    have h1 := idelicExplicitFormula_normOneFourierInversion τ _hτ f ⟨finiteClassMap(v) u, hker u (hO1 u hu)⟩
    have h2 := idelicExplicitFormula_normOneFourierInversion τ _hτ f 1
    refine ((h1.sub h2).mul_right (w u)).congr_fun fun χ ↦ ?_
    simp only [φ, c, OneMemClass.coe_one, map_one, inv_one, Circle.coe_one]
    ring
  have hφm (χ : chartChars(τ)) : AEStronglyMeasurable (φ χ) (μ𝔭(v).restrict O) := by
    have h1 : Continuous (fun u : (v.adicCompletion F)ˣ ↦
        ((((χ.val (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) - 1)) :=
      (continuous_subtype_val.comp ((χ.val.continuous.comp
        (continuous_ideleClass_ofAdicCompletion F v)).inv)).sub continuous_const
    have h2 : Continuous (fun u : (v.adicCompletion F)ˣ ↦ (Real.sqrt ‖u.val‖ : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (continuous_norm.comp Units.continuous_val))
    have h3 : Continuous (fun u : (v.adicCompletion F)ˣ ↦ ((‖1 - u.val‖ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_norm.comp
        (continuous_const.sub Units.continuous_val))
    exact (h1.measurable.mul (h2.measurable.div h3.measurable)).aestronglyMeasurable
  have hB (χ : chartChars(τ)) (hχ : c χ ≠ 0) :
      ∀ᵐ u ∂μ𝔭(v).restrict O, ‖φ χ u‖ ≤ 2 * q(v) ^ n := by
    filter_upwards [ae_restrict_mem hOm] with u hu
    have hu1 := hO1 u hu
    by_cases hs : ‖u.val - 1‖ ≤ q(v) ^ (-(n : ℤ))
    · simp only [φ, hcz χ hχ u hu1 hs, inv_one, Circle.coe_one, sub_self, zero_mul, norm_zero]
      positivity
    · push Not at hs
      have hpos : 0 < q(v) ^ (-(n : ℤ)) := zpow_pos (by linarith) _
      have ha : ‖((((χ.val (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) - 1)‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by rw [Circle.norm_coe, norm_one]; norm_num)
      have hb : ‖(Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ)‖ ≤ q(v) ^ n := by
        rw [norm_div, Complex.norm_real, Complex.norm_real, norm_norm, hu1, Real.sqrt_one,
          norm_one, norm_sub_rev, div_le_iff₀ (hpos.trans hs)]
        calc (1 : ℝ) = q(v) ^ n * q(v) ^ (-(n : ℤ)) := by
              rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_pos (by linarith) _).ne']
          _ ≤ q(v) ^ n * ‖u.val - 1‖ := mul_le_mul_of_nonneg_left hs.le (by positivity)
      simp only [φ, norm_mul]
      exact mul_le_mul ha hb (norm_nonneg _) (by norm_num)
  have hsum := explicitFormula_hasSum_integral (μ𝔭(v).restrict O) c hc φ hφm _ hB
    (fun u ↦ (f.val (finiteClassMap(v) u) - f.val 1) * w u)
    ((ae_restrict_iff' hOm).mpr (.of_forall hexp))
  have hVc : (V𝔭(v) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  convert hsum.mul_left (-finiteWeilScale(v)) using 1
  · funext χ
    rw [hΦc χ, integral_const_mul]
    simp only [φ, w]
    rw [idelicExplicitFormula_conductorLocal_character v χ.val]
    push_cast
    field_simp
  · rw [neg_mul]
    congr 2
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    simp only [_hF, w, map_one]
    ring

section ExplicitFormulaCopyDescent

/-! Copied from `AppD_SchwartzBruhat/Sec3b.lean`, where these lemmas are private: a smooth
compactly supported function is Schwartz–Bruhat. -/

variable {m n r m' n' r' : ℕ} {H H' : Type*}
  [AddCommGroup H] [TopologicalSpace H] [DiscreteTopology H]
  [AddCommGroup H'] [TopologicalSpace H'] [DiscreteTopology H']

/-- On a neighborhood of the origin the elementary cover is injective. -/
private theorem explicitFormula_copy_elementaryCoverZeroHom_injOn_nhds :
    ∃ W ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      InjOn (elementaryCoverZeroHom (r := r) (F := H)) W := by
  let W := ⋂ i : Fin n, (fun v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) ↦ v.2 i) ⁻¹'
    Ioo (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)
  have hW : IsOpen W := isOpen_iInter_of_finite fun i ↦ isOpen_Ioo.preimage
    ((PiLp.continuous_apply 2 _ i).comp continuous_snd)
  have hzero : 0 ∈ W := by simp [W]; norm_num
  refine ⟨W, hW.mem_nhds hzero, fun x hx y hy h ↦ Prod.ext (congrArg (fun v : ElementaryLieGroup m n r H ↦ v.1) h) ?_⟩
  apply PiLp.ext
  intro i
  apply AddCircle.injOn_coe_Ico (1 : ℝ) (-(1 / 2 : ℝ))
    (Ioo_subset_Ico_self (mem_iInter.mp hx i)) (Ioo_subset_Ico_self (mem_iInter.mp hy i))
  exact congrArg (fun v : ElementaryLieGroup m n r H ↦ v.2.1 i) h

/-- Openness of the homomorphism makes its linear lift between universal covers surjective. -/
private theorem explicitFormula_copy_elementaryHom_cover_rightInverse
    (a : ElementaryLieGroup m n r H →+ ElementaryLieGroup m' n' r' H')
    (ha : Continuous a) (hao : IsOpenMap a) :
    ∃ J : (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      ∀ v, a (elementaryCover (J v) 0 0) = elementaryCover v 0 0 := by
  let c := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := H)
  let d := elementaryCoverZeroHom (m := m') (n := n') (r := r') (F := H')
  let A := a.comp c
  have hA : Continuous A := ha.comp elementaryCoverZeroHom_continuous_isOpenMap.1
  let R := (AddMonoidHom.fst _ _).comp A
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp A)
  choose l hl using fun i : Fin n' ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hA.snd.fst)
  let L := (R.toRealLinearMap hA.fst).prod ((EuclideanSpace.equiv (Fin n') ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi l))
  have hL (v) : d (L v) = A v := by
    refine Prod.ext rfl (Prod.ext (funext fun i ↦ hl i v) ?_)
    have h := hA.snd.snd.isConst_of_preconnectedSpace v 0
    rw [map_zero A] at h
    exact h.symm
  obtain ⟨W, hW, hi⟩ := explicitFormula_copy_elementaryCoverZeroHom_injOn_nhds (m := m') (n := n') (r := r') (H := H')
  have hpre : L ⁻¹' W ∈ 𝓝 0 := L.continuous.continuousAt.preimage_mem_nhds (L.map_zero.symm ▸ hW)
  have hopen : IsOpenMap A := hao.comp elementaryCoverZeroHom_continuous_isOpenMap.2
  have him : A '' (L ⁻¹' W) ∈ 𝓝 0 := A.map_zero ▸ hopen.image_mem_nhds hpre
  have hd : Continuous d := elementaryCoverZeroHom_continuous_isOpenMap.1
  have hV : d ⁻¹' (A '' (L ⁻¹' W)) ∈ 𝓝 0 := hd.continuousAt.preimage_mem_nhds (d.map_zero.symm ▸ him)
  have hs : L.range = ⊤ := L.range.eq_top_of_nonempty_interior' ⟨0, mem_interior_iff_mem_nhds.mpr (by
    filter_upwards [hW, hV] with x hx hdx
    rcases hdx with ⟨u, hu, he⟩
    exact ⟨u, hi hu hx ((hL u).trans he)⟩)⟩
  obtain ⟨J, hJ⟩ := L.exists_rightInverse_of_surjective hs
  refine ⟨J, fun x ↦ (hL (J x)).symm.trans (congrArg d ?_)⟩
  exact DFunLike.congr_fun hJ x

/-- Smoothness on the cover descends through an open surjective elementary homomorphism. -/
private theorem explicitFormula_copy_contDiff_of_comp_elementaryHom [Finite H] {p : ℕ∞}
    (a : ElementaryLieGroup m n r H →+ ElementaryLieGroup m' n' r' H')
    (ha : Continuous a) (hao : IsOpenMap a) (hs : Surjective a)
    {f : ElementaryLieGroup m' n' r' H' → ℂ}
    (hf : ∀ z b, ContDiff ℝ p (fun u ↦ f (a (elementaryCover u z b))))
    (z : Fin r' → ℤ) (b : H') : ContDiff ℝ p (fun v ↦ f (elementaryCover v z b)) := by
  obtain ⟨J, hJ⟩ := explicitFormula_copy_elementaryHom_cover_rightInverse a ha hao
  obtain ⟨u, hu⟩ := hs (elementaryCover 0 z b)
  obtain ⟨t, ht⟩ := elementaryCover_surjective u.2.2.1 u.2.2.2 u.1 u.2.1
  have hshift (v) : elementaryCover (J v + (u.1,t)) u.2.2.1 u.2.2.2 = elementaryCover (J v) 0 0 + u := by
    rw [← show elementaryCover (u.1, t) u.2.2.1 u.2.2.2 = u from ht]
    simp [elementaryCover, Pi.add_def, Pi.zero_def]
  have he (v) : a (elementaryCover (J v + (u.1, t)) u.2.2.1 u.2.2.2) = elementaryCover v z b := by
    rw [hshift, map_add, hJ, hu]
    simp [elementaryCover, Pi.add_def, Pi.zero_def]
  simp_rw [← he]
  exact (hf u.2.2.1 u.2.2.2).comp (J.contDiff.add contDiff_const)

end ExplicitFormulaCopyDescent

section ExplicitFormulaCopyFixedQuotient
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- On any structural quotient to which a smooth function descends, its descent is smooth
at every order, even when the original finite-order witnesses use different kernels. -/
private theorem explicitFormula_copy_bruhatSmooth_fixed_quotient {f : G → ℂ} (hf : IsBruhatSmooth f)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    {f₀ : a.quotient → ℂ} (h₀ : ∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val)
    (z : Fin e.latticeRank → ℤ) (t : e.finiteFactor) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover v z t)))) := by
  apply contDiff_infty.mpr
  intro p
  obtain ⟨k, hk, _, hd⟩ := hf p
  let k₀ := OrderDual.ofDual a.val.2
  let b : BruhatStructuralPair G := ⟨(a.val.1, OrderDual.toDual (k₀ ⊓ k)), a.property.1, a.property.2.1,
    isBruhatGoodSubgroup_inf a.property.2.2.1 hk, inf_le_left.trans a.property.2.2.2⟩
  obtain ⟨g, hg, hgd⟩ := bruhatContDiff_descend_of_le hk hd b (show k₀ ⊓ k ≤ k from inf_le_right)
  let d := Classical.choice b.elementary
  let q : b.quotient →* a.quotient := QuotientGroup.map _ _ (MonoidHom.id a.val.1) (fun _ h ↦ h.1)
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk.of_comp_iff.mp
    (show IsOpenQuotientMap (QuotientGroup.mk : a.val.1 → a.quotient) from QuotientGroup.isOpenQuotientMap_mk)
  let A := AddMonoidHom.toMultiplicative.symm
    (e.equiv.toMonoidHom.comp (q.comp d.equiv.symm.toMonoidHom))
  have hc : Continuous A := e.equiv.continuous.comp (hq.continuous.comp d.equiv.symm.continuous)
  have ho : IsOpenMap A := e.equiv.toHomeomorph.isOpenMap.comp
    (hq.isOpenMap.comp d.equiv.symm.toHomeomorph.isOpenMap)
  have hsur : Surjective A := e.equiv.surjective.comp (hq.surjective.comp d.equiv.symm.surjective)
  let Fv := fun v ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd v))
  apply explicitFormula_copy_contDiff_of_comp_elementaryHom A hc ho hsur (f := Fv) _ z t
  intro z' t'
  have hdesc (v : b.quotient) : f₀ (q v) = g v := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    exact (h₀ x).trans (hg x).symm
  have heq (v) : Fv (A v) = g (d.equiv.symm (Multiplicative.ofAdd v)) := by
    change f₀ (e.equiv.symm (e.equiv _)) = _
    rw [e.equiv.symm_apply_apply]
    exact hdesc _
  simp_rw [heq]
  exact hgd d z' t'
/-- Every smooth compactly supported function is the realization of an elementary Schwartz stage. -/
private theorem explicitFormula_copy_bruhatCompactSupport_mem_schwartz {f : G → ℂ} (hf : f ∈ bruhatCompactSupportSubmodule G) :
    f ∈ schwartzBruhatSubmodule G := by
  classical
  have h := (mem_bruhatSmoothSubmodule_iff f).mp hf.1
  obtain ⟨k, hk, _, hd⟩ := h 0
  have hkC : IsCompact (k : Set G) := (lcaDualAnnihilator_annihilator k hk.1) ▸
    isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains (hf.2.union hkC)
  let a : BruhatStructuralPair G := ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk,
    fun _ hx ↦ hH (Or.inr hx)⟩
  let e := Classical.choice a.elementary
  obtain ⟨f₀, h₀, _⟩ := hd a rfl
  let φ := fun y ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd y))
  let q : a.val.1 → ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
    fun x ↦ (e.equiv (QuotientGroup.mk x)).toAdd
  have hq : Continuous q := continuous_toAdd.comp (e.equiv.continuous.comp QuotientGroup.continuous_mk)
  have hs : Surjective q := fun y ↦ (e.equiv.surjective.comp QuotientGroup.mk_surjective) (Multiplicative.ofAdd y)
  have he (x : a.val.1) : φ (q x) = f x.val := by
    change f₀ (e.equiv.symm (e.equiv _)) = _
    rw [e.equiv.symm_apply_apply, h₀]
  have hc : HasCompactSupport φ := by
    have hc' := (H.val.isClosed_of_isOpen H.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hf.2
    apply HasCompactSupport.intro (hc'.image hq)
    intro y hy
    obtain ⟨x, rfl⟩ := hs y
    exact (he x).trans (image_eq_zero_of_notMem_tsupport fun hx ↦ hy ⟨x, hx, rfl⟩)
  let s : SchwartzBruhatStage e := ⟨φ, elementarySchwartz_of_compactSupport (f := φ)
    (explicitFormula_copy_bruhatSmooth_fixed_quotient h a e h₀) hc⟩
  refine (mem_schwartzBruhatSubmodule_iff f).mpr ⟨a, e, s, funext fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs with hx
  · exact he ⟨x, hx⟩
  · exact (image_eq_zero_of_notMem_tsupport fun ht ↦ hx (hH (Or.inl ht))).symm


end ExplicitFormulaCopyFixedQuotient

section ExplicitFormulaShellInversion

/-- A left translate of a test on the idele classes is a test. -/
private theorem explicitFormula_test_translate (f : 𝒟(C[F])) (r : C[F]) :
    ∃ f' : 𝒟(C[F]), ∀ h, f'.val h = f.val (r * h) := by
  let v : SchwartzBruhat C[F] :=
    ⟨f.val, explicitFormula_copy_bruhatCompactSupport_mem_schwartz f.property⟩
  let u : SchwartzBruhat C[F] := ⟨_, schwartzBruhat_translate_mem r⁻¹ v⟩
  have hu (h : C[F]) : u.val h = f.val (r * h) := by
    change f.val (r⁻¹⁻¹ * h) = _
    rw [inv_inv]
  have hc : HasCompactSupport u.val := by
    have h := f.property.2.comp_homeomorph (Homeomorph.mulLeft r)
    convert h using 1
    funext h
    exact hu h
  exact ⟨⟨u.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth u), hc⟩,
    hu⟩

/-- Fourier inversion on the norm shell of a class `g`: the radial profiles at `log |g|`,
weighted by `χ(g)⁻¹`, sum to `f(g)`. -/
private theorem explicitFormula_shell_inversion (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) (g : C[F]) :
    HasSum (fun χ : chartChars(τ) ↦ Φ χ (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) *
      (((χ.val g)⁻¹ : Circle) : ℂ)) (f.val g) := by
  set x := Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) with hx
  set r := radialFlow(τ, x) with hr
  obtain ⟨f', hf'⟩ := explicitFormula_test_translate f r
  have hsec : positiveRealLogEquiv.symm (Multiplicative.ofAdd x) = ideleClassNorm F g := by
    rw [ContinuousMulEquiv.symm_apply_eq, ← ofAdd_toAdd (positiveRealLogEquiv _),
      positiveRealLogEquiv_apply]
  have hnr : ideleClassNorm F r = ideleClassNorm F g := by
    rw [hr, hτ, hsec]
  let c : (ideleClassNorm F).ker := ⟨r⁻¹ * g, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnr, inv_mul_cancel]⟩
  have h := idelicExplicitFormula_normOneFourierInversion τ hτ f' c
  have hfc : f'.val c = f.val g := by
    rw [hf']
    change f.val (r * (r⁻¹ * g)) = f.val g
    rw [mul_inv_cancel_left]
  rw [hfc] at h
  convert h using 1
  funext χ
  have hχr : χ.val r = 1 := χ.property _
  have hχc : χ.val (c : C[F]) = χ.val g := by
    change χ.val (r⁻¹ * g) = χ.val g
    rw [map_mul, map_inv, hχr, inv_one, one_mul]
  rw [hχc, explicitFormula_profile_eq τ hτ f Φ hM χ x]
  congr 2
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  change f.val (r * (u : C[F])) * _ = f'.val (u : C[F]) * _
  rw [hf']

end ExplicitFormulaShellInversion

section ExplicitFormulaPrimePowersLocal

/-- At a fixed point, the radial profiles of a test are absolutely summable over the
characters. -/
private theorem explicitFormula_profile_summable (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) (x : ℝ) :
    Summable (fun χ : chartChars(τ) ↦ ‖Φ χ x‖) := by
  obtain ⟨f', hf'⟩ := explicitFormula_test_translate f radialFlow(τ, x)
  refine ((idelicExplicitFormula_normOneFourier_summable τ hτ f').mul_left
    ‖(classVolume : ℂ)⁻¹‖).congr fun χ ↦ ?_
  rw [explicitFormula_profile_eq τ hτ f Φ hM χ x, norm_mul]
  congr 2
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  change f'.val (u : C[F]) * _ = f.val (radialFlow(τ, x) * (u : C[F])) * _
  rw [hf']

/-- The integer units are the zeroth filtration subgroup. -/
private theorem explicitFormula_unitFiltration_zero (v : Primes(F)) :
    (explicitFormula_unitFiltration v 0 : Set (v.adicCompletion F)ˣ) =
      ((O(v)).units : Set (v.adicCompletion F)ˣ) := by
  ext u
  rw [SetLike.mem_coe, explicitFormula_mem_unitFiltration, SetLike.mem_coe,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
    ← Valued.toNormedField.norm_eq_one_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rw [Nat.cast_zero, neg_zero, zpow_zero, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg, norm_one, h, max_self]

/-- `∫_{O_v^×} χ(u)⁻¹ d^×u` is `vol O_v^×` if `χ` is trivial on the norm-one units and `0`
otherwise. -/
private theorem explicitFormula_integral_units_char (v : Primes(F)) (χ : U[F]) :
    ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ),
      (((χ (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) ∂μ𝔭(v) =
      if ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 → χ (finiteClassMap(v) u) = 1 then
        (V𝔭(v) : ℂ) else 0 := by
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have hOm : MeasurableSet ((O(v)).units : Set (v.adicCompletion F)ˣ) :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hO1 (u : (v.adicCompletion F)ˣ) :
      u ∈ ((O(v)).units : Set (v.adicCompletion F)ˣ) ↔ ‖u.val‖ = 1 := by
    rw [← explicitFormula_unitFiltration_zero, SetLike.mem_coe,
      explicitFormula_mem_unitFiltration]
    refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
    rw [Nat.cast_zero, neg_zero, zpow_zero, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg, norm_one, h, max_self]
  split_ifs with h
  · rw [setIntegral_congr_fun hOm (g := fun _ ↦ (1 : ℂ)) fun u hu ↦ by
      rw [h u ((hO1 u).mp hu), inv_one, Circle.coe_one], setIntegral_const, Complex.real_smul,
      mul_one]
    rfl
  · push Not at h
    obtain ⟨w, hw1, hw⟩ := h
    have hw0 : w ∈ explicitFormula_unitFiltration v 0 := by
      rw [← SetLike.mem_coe, explicitFormula_unitFiltration_zero]
      exact (hO1 w).mpr hw1
    rw [← explicitFormula_unitFiltration_zero]
    exact explicitFormula_integral_filtration_char v χ 0 w hw0 hw

/-- Averaging the shell inversion over the integer units: weighted by `vol O_v^×` on the
characters trivial on the norm-one units at `v` and by `0` on the others, the profiles at
`log |g|` times `χ(g)⁻¹` sum to `∫_{O_v^×} f(g u) d^×u`. -/
private theorem explicitFormula_unramified_average (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2))
    (v : Primes(F)) (g : C[F]) :
    HasSum (fun χ : chartChars(τ) ↦
      (if ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 → χ.val (finiteClassMap(v) u) = 1 then
        (V𝔭(v) : ℂ) else 0) *
        (Φ χ (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) * (((χ.val g)⁻¹ : Circle) : ℂ)))
      (∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ),
        f.val (g * finiteClassMap(v) u) ∂μ𝔭(v)) := by
  let K := v.adicCompletion F
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  let O := ((O(v)).units : Set Kˣ)
  have hOm : MeasurableSet O :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hOc : IsCompact O := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have : IsFiniteMeasure (μ𝔭(v).restrict O) :=
    isFiniteMeasure_restrict.mpr hOc.measure_lt_top.ne
  have hO1 (u : Kˣ) (hu : u ∈ O) : ‖u.val‖ = 1 := by
    change u ∈ (O(v)).units at hu
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hu
    exact Valued.toNormedField.norm_eq_one_iff.mpr hu
  let x := Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)
  let a : chartChars(τ) → ℂ := fun χ ↦ Φ χ x * (((χ.val g)⁻¹ : Circle) : ℂ)
  let φ : chartChars(τ) → Kˣ → ℂ :=
    fun χ u ↦ (((χ.val (finiteClassMap(v) u))⁻¹ : Circle) : ℂ)
  have ha : Summable (fun χ ↦ ‖a χ‖) :=
    (explicitFormula_profile_summable τ hτ f Φ hM x).congr fun χ ↦ by
      simp only [a, norm_mul, Circle.norm_coe, mul_one]
  have hnorm (u : Kˣ) (hu : u ∈ O) :
      ideleClassNorm F (g * finiteClassMap(v) u) = ideleClassNorm F g := by
    rw [map_mul, ideleClassNorm_ofAdicCompletion]
    have h1 : Units.map nnNormHom.toMonoidHom u = 1 := by
      ext
      change ‖u.val‖ = 1
      exact hO1 u hu
    rw [h1, mul_one]
  have hexp : ∀ᵐ u ∂(μ𝔭(v).restrict O),
      HasSum (fun χ ↦ a χ * φ χ u) (f.val (g * finiteClassMap(v) u)) := by
    refine (ae_restrict_iff' hOm).mpr (.of_forall fun u hu ↦ ?_)
    have h := explicitFormula_shell_inversion τ hτ f Φ hM (g * finiteClassMap(v) u)
    rw [hnorm u hu] at h
    convert h using 1
    funext χ
    simp only [a, φ, map_mul, mul_inv, Circle.coe_mul, x]
    ring
  have hB (χ : chartChars(τ)) (_ : a χ ≠ 0) : ∀ᵐ u ∂(μ𝔭(v).restrict O), ‖φ χ u‖ ≤ 1 :=
    .of_forall fun u ↦ by simp only [φ, Circle.norm_coe, le_refl]
  have hφm (χ : chartChars(τ)) : AEStronglyMeasurable (φ χ) (μ𝔭(v).restrict O) :=
    (continuous_subtype_val.comp ((χ.val.continuous.comp
      (continuous_ideleClass_ofAdicCompletion F v)).inv)).aestronglyMeasurable
  have hsum := explicitFormula_hasSum_integral (μ𝔭(v).restrict O) a ha φ hφm 1 hB _ hexp
  convert hsum using 1
  funext χ
  rw [integral_const_mul]
  change _ = a χ * ∫ u in O, (((χ.val (finiteClassMap(v) u))⁻¹ : Circle) : ℂ) ∂μ𝔭(v)
  rw [explicitFormula_integral_units_char v χ.val]
  ring

end ExplicitFormulaPrimePowersLocal

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (prime-power terms at one place). Summed
over the characters trivial on the image of the norm section, the prime-power terms at a
finite place `v` of the explicit formula of Theorem B.4.2.2 for the radial profiles `Φ_χ` of
`f` give `(log q_v / vol O_v^×) ∫_{|u| ≠ 1} f_v(u) |u|^{1/2} / |1 - u| d^×u`.

Computation. Only the characters unramified at `v` contribute; for those,
`χ(π_v)^m Φ_χ(m log q_v)` is the Fourier coefficient of `f(π_v^{-m} ·)` on `C¹`, and Fourier
inversion over the characters unramified at `v` (the characters of `C¹` trivial on the image
of `O_v^×`) averages `f(π_v^{∓m} ·)` over `O_v^×`. On the shell `|u| = q_v^{∓m}` the weight
`|u|^{1/2} / |1 - u|` is `q_v^{-m/2} = e^{-x/2}` with `x = m log q_v`. -/
theorem idelicExplicitFormula_finiteMatching_primePowersLocal (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (testF : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_hF : ∀ v u, (testF v).val u = f.val (finiteClassMap(v) u))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) (v : Primes(F)) :
    HasSum (fun χ : chartChars(τ) ↦ ∑' m : ℕ, explicitPrimeTerm(χ.val, Φ χ) (v, m))
      (finiteWeilScale(v) *
        ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ)ᶜ,
          (testF v).val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ𝔭(v)) := by
  let K := v.adicCompletion F
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  let O := ((O(v)).units : Set Kˣ)
  have hOm : MeasurableSet O :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hOc : IsCompact O := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hO1 (u : Kˣ) : u ∈ O ↔ ‖u.val‖ = 1 := by
    change u ∈ (O(v)).units ↔ _
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      Valued.toNormedField.norm_eq_one_iff]
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < q(v) := zero_lt_one.trans hq
  have hV : V𝔭(v) ≠ 0 := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
  have hVc : (V𝔭(v) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV
  obtain ⟨M, hMb⟩ := explicitFormula_tsupport_norm_bound f
  let N : ℕ := ⌈M⌉₊
  have htc : Continuous (testF v).val := by
    have h : (testF v).val = fun u ↦ f.val (finiteClassMap(v) u) := funext (_hF v)
    rw [h]
    exact (explicitTest_continuous f).comp (continuous_ideleClass_ofAdicCompletion F v)
  -- A uniformizer.
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨a, ha⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 a ha.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ ha
  have hpk (k : ℕ) : ‖(p ^ k).val‖ = (q(v) ^ k)⁻¹ := by
    rw [Units.val_pow_eq_pow_val, norm_pow, hp, inv_pow]
  have hpk' (k : ℕ) : ‖((p ^ k)⁻¹).val‖ = q(v) ^ k := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hpk, inv_inv]
  have hnι (u : Kˣ) : ((ideleClassNorm F (finiteClassMap(v) u) : ℝ≥0) : ℝ) = ‖u.val‖ := by
    simp only [ideleClassNorm_ofAdicCompletion]
    rfl
  -- Unramified characters.
  let ur : U[F] → Prop := fun χ ↦ ∀ u : Kˣ, ‖u.val‖ = 1 → χ (finiteClassMap(v) u) = 1
  have hres (χ : U[F]) (x : Kˣ) :
      χ₀(χ).restrict v x.val = (χ (finiteClassMap(v) x) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (χ (finiteClassMap(v) x) : ℂ) *
      (((ideleClassNorm F (finiteClassMap(v) x) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hur (χ : U[F]) : χ₀(χ).IsUnramifiedAt v ↔ ur χ := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    constructor
    · intro h u hu
      have h1 : u.val ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
        (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr
          (Valued.toNormedField.norm_le_one_iff.mp hu.le)
      have h2 : (u⁻¹).val ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
        refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr
          (Valued.toNormedField.norm_le_one_iff.mp ?_)
        rw [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one]
      let y : (HeightOneSpectrum.adicCompletionIntegers F v)ˣ :=
        ⟨⟨u.val, h1⟩, ⟨(u⁻¹).val, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
      have hy := h y
      change χ₀(χ).restrict v u.val = 1 at hy
      rw [hres] at hy
      exact Circle.ext (hy.trans Circle.coe_one.symm)
    · intro h y
      let u := Units.map (HeightOneSpectrum.adicCompletionIntegers F v).subtype.toMonoidHom y
      have hn : ‖u.val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := u)).mp
          ⟨y.val.property, y.inv.property⟩)
      change χ₀(χ).restrict v u.val = 1
      rw [hres, h u hn, Circle.coe_one]
  have hloc (χ : U[F]) (h : χ₀(χ).IsUnramifiedAt v) :
      χ₀(χ).localValue v = (χ (finiteClassMap(v) p) : ℂ) := by
    rw [h.localValue_eq p.val ha, hres]
  have hloc' (χ : U[F]) (h : χ₀(χ).IsUnramifiedAt v) :
      χ₀(χ⁻¹).localValue v = (((χ (finiteClassMap(v) p))⁻¹ : Circle) : ℂ) :=
    hloc χ⁻¹ ((inverse_unramified v χ).mpr h)
  -- The averaged shell inversions at `π^{∓k}`.
  have hplus (k : ℕ) : HasSum (fun χ : chartChars(τ) ↦
      (if ur χ.val then (V𝔭(v) : ℂ) else 0) *
        (Φ χ ((k : ℝ) * Real.log q(v)) * ((χ.val (finiteClassMap(v) p) : ℂ) ^ k)))
      (∫ u in O, (testF v).val ((p ^ k)⁻¹ * u) ∂μ𝔭(v)) := by
    have h := explicitFormula_unramified_average τ _hτ f Φ _hM v (finiteClassMap(v) ((p ^ k)⁻¹))
    rw [hnι, hpk', Real.log_pow] at h
    convert h using 1
    · funext χ
      simp only [map_inv, map_pow, inv_inv, Circle.coe_pow]
      rfl
    · congr 1
      funext u
      rw [_hF, map_mul]
  have hminus (k : ℕ) : HasSum (fun χ : chartChars(τ) ↦
      (if ur χ.val then (V𝔭(v) : ℂ) else 0) *
        (Φ χ (-((k : ℝ) * Real.log q(v))) *
          ((((χ.val (finiteClassMap(v) p))⁻¹ : Circle) : ℂ) ^ k)))
      (∫ u in O, (testF v).val (p ^ k * u) ∂μ𝔭(v)) := by
    have h := explicitFormula_unramified_average τ _hτ f Φ _hM v (finiteClassMap(v) (p ^ k))
    rw [hnι, hpk, Real.log_inv, Real.log_pow] at h
    convert h using 1
    · funext χ
      simp only [map_pow, Circle.coe_pow, Circle.coe_inv, inv_pow]
      rfl
    · congr 1
      funext u
      rw [_hF, map_mul]
  -- The prime-power terms in these terms.
  have hterm (χ : chartChars(τ)) (m : ℕ) : explicitPrimeTerm(χ.val, Φ χ) (v, m) =
      ((Real.log q(v) * Real.exp (-(((m + 1 : ℕ) : ℝ) * Real.log q(v)) / 2) : ℝ) : ℂ) /
          (V𝔭(v) : ℂ) *
        ((if ur χ.val then (V𝔭(v) : ℂ) else 0) *
            (Φ χ (((m + 1 : ℕ) : ℝ) * Real.log q(v)) *
              ((χ.val (finiteClassMap(v) p) : ℂ) ^ (m + 1))) +
          (if ur χ.val then (V𝔭(v) : ℂ) else 0) *
            (Φ χ (-(((m + 1 : ℕ) : ℝ) * Real.log q(v))) *
              ((((χ.val (finiteClassMap(v) p))⁻¹ : Circle) : ℂ) ^ (m + 1)))) := by
    by_cases h : χ₀(χ.val).IsUnramifiedAt v
    · have h' := (hur χ.val).mp h
      show (if χ₀(χ.val).IsUnramifiedAt v then _ else (0 : ℂ)) = _
      rw [ite_eq_left h, ite_eq_left h']
      dsimp only
      rw [hloc χ.val h, hloc' χ.val h]
      field_simp
    · have h' : ¬ ur χ.val := fun h' ↦ h ((hur χ.val).mpr h')
      show (if χ₀(χ.val).IsUnramifiedAt v then _ else (0 : ℂ)) = _
      rw [ite_eq_right h, ite_eq_right h']
      simp
  have hzero (χ : chartChars(τ)) (m : ℕ) (hm : N ≤ m) :
      explicitPrimeTerm(χ.val, Φ χ) (v, m) = 0 := by
    have hx : Real.exp (((m + 1 : ℕ) : ℝ) * Real.log q(v)) = q(v) ^ (m + 1) := by
      rw [Real.exp_nat_mul, Real.exp_log hq0]
    have h2 : (2 : ℝ) ≤ q(v) := by
      have : 1 < Ideal.absNorm v.asIdeal := HeightOneSpectrum.one_lt_absNorm v
      exact_mod_cast this
    have h3 : ((m + 1 : ℕ) : ℝ) < 2 ^ (m + 1) := by exact_mod_cast Nat.lt_two_pow_self
    have h4 : (2 : ℝ) ^ (m + 1) ≤ q(v) ^ (m + 1) := pow_le_pow_left₀ (by norm_num) h2 _
    have h5 : M ≤ (N : ℝ) := Nat.le_ceil M
    have h6 : (N : ℝ) ≤ m := by exact_mod_cast hm
    have hlt : M < q(v) ^ (m + 1) := by push_cast at h3; linarith
    have h1 : Φ χ (((m + 1 : ℕ) : ℝ) * Real.log q(v)) = 0 := by
      by_contra h1
      have := (explicitFormula_profile_support τ _hτ f Φ _hM hMb χ _ h1).1
      rw [hx] at this
      linarith
    have h1' : Φ χ (-(((m + 1 : ℕ) : ℝ) * Real.log q(v))) = 0 := by
      by_contra h1'
      have := (explicitFormula_profile_support τ _hτ f Φ _hM hMb χ _ h1').2
      rw [neg_neg, hx] at this
      linarith
    rw [hterm, h1, h1']
    simp
  let c (m : ℕ) : ℂ :=
    ((Real.log q(v) * Real.exp (-(((m + 1 : ℕ) : ℝ) * Real.log q(v)) / 2) : ℝ) : ℂ) /
      (V𝔭(v) : ℂ)
  let P (m : ℕ) : ℂ := ∫ u in O, (testF v).val ((p ^ (m + 1))⁻¹ * u) ∂μ𝔭(v)
  let Q (m : ℕ) : ℂ := ∫ u in O, (testF v).val (p ^ (m + 1) * u) ∂μ𝔭(v)
  have hLHS : HasSum (fun χ : chartChars(τ) ↦ ∑' m : ℕ, explicitPrimeTerm(χ.val, Φ χ) (v, m))
      (∑ m ∈ Finset.range N, c m * (P m + Q m)) := by
    have h := hasSum_sum (s := Finset.range N) fun m _ ↦
      ((hplus (m + 1)).add (hminus (m + 1))).mul_left (c m)
    convert h using 1
    funext χ
    rw [tsum_eq_sum (s := Finset.range N) fun m hm ↦ hzero χ m (by simpa using hm)]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hterm]
  -- The integral over the complement of the units, shell by shell.
  let I : Kˣ → ℂ := fun u ↦
    (testF v).val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ)
  let s (k : ℕ) : ℝ := Real.exp (-((k : ℝ) * Real.log q(v)) / 2)
  have hsqrt (b : ℝ) : Real.sqrt (Real.exp b) = Real.exp (b / 2) :=
    (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr (by rw [← Real.exp_add, add_halves])
  have hexpk (k : ℕ) : Real.exp ((k : ℝ) * Real.log q(v)) = q(v) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hq0]
  have hs1 (k : ℕ) : Real.sqrt (q(v) ^ k) / q(v) ^ k = s k := by
    rw [← hexpk, hsqrt, ← Real.exp_sub]
    congr 1
    ring
  have hs2 (k : ℕ) : Real.sqrt ((q(v) ^ k)⁻¹) = s k := by
    rw [← hexpk, ← Real.exp_neg, hsqrt]
  let Fp (k : ℕ) (u : Kˣ) : ℂ := if ‖u.val‖ = q(v) ^ (k : ℤ) then I u else 0
  let Fm (k : ℕ) (u : Kˣ) : ℂ := if ‖u.val‖ = q(v) ^ (-(k : ℤ)) then I u else 0
  have hFp (k : ℕ) (hk : 1 ≤ k) : (fun u ↦ Fp k u) = fun u ↦
      O.indicator (fun u' ↦ (s k : ℂ) * (testF v).val ((p ^ k)⁻¹ * u')) (p ^ k * u) := by
    funext u
    have hnorm : ‖(p ^ k * u).val‖ = (q(v) ^ k)⁻¹ * ‖u.val‖ := by
      rw [Units.val_mul, norm_mul, hpk]
    have hiff : p ^ k * u ∈ O ↔ ‖u.val‖ = q(v) ^ (k : ℤ) := by
      rw [hO1, hnorm, zpow_natCast, inv_mul_eq_one₀ (pow_pos hq0 k).ne', eq_comm]
    by_cases h : ‖u.val‖ = q(v) ^ (k : ℤ)
    · rw [indicator_of_mem (hiff.mpr h)]
      show (if ‖u.val‖ = q(v) ^ (k : ℤ) then I u else 0) = _
      rw [ite_eq_left h, inv_mul_cancel_left]
      have hgt : 1 < ‖u.val‖ := by rw [h, zpow_natCast]; exact one_lt_pow₀ hq (by omega)
      have h1 : ‖1 - u.val‖ = ‖u.val‖ := by
        have hne : ‖(1 : K)‖ ≠ ‖-u.val‖ := by rw [norm_one, norm_neg]; exact hgt.ne
        rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one,
          norm_neg, max_eq_right hgt.le]
      change (testF v).val u * _ / _ = _
      rw [h1, h, zpow_natCast, ← hs1 k]
      push_cast
      ring
    · rw [indicator_of_notMem (fun h' ↦ h (hiff.mp h'))]
      show (if ‖u.val‖ = q(v) ^ (k : ℤ) then I u else 0) = _
      rw [ite_eq_right h]
  have hFm (k : ℕ) (hk : 1 ≤ k) : (fun u ↦ Fm k u) = fun u ↦
      O.indicator (fun u' ↦ (s k : ℂ) * (testF v).val (p ^ k * u')) ((p ^ k)⁻¹ * u) := by
    funext u
    have hnorm : ‖((p ^ k)⁻¹ * u).val‖ = q(v) ^ k * ‖u.val‖ := by
      rw [Units.val_mul, norm_mul, hpk']
    have hiff : (p ^ k)⁻¹ * u ∈ O ↔ ‖u.val‖ = q(v) ^ (-(k : ℤ)) := by
      rw [hO1, hnorm, zpow_neg, zpow_natCast, mul_comm,
        mul_eq_one_iff_eq_inv₀ (pow_pos hq0 k).ne']
    by_cases h : ‖u.val‖ = q(v) ^ (-(k : ℤ))
    · rw [indicator_of_mem (hiff.mpr h)]
      show (if ‖u.val‖ = q(v) ^ (-(k : ℤ)) then I u else 0) = _
      rw [ite_eq_left h, mul_inv_cancel_left]
      have hlt : ‖u.val‖ < 1 := by
        rw [h, zpow_neg, zpow_natCast]
        exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
      have h1 : ‖1 - u.val‖ = 1 := by
        have hne : ‖(1 : K)‖ ≠ ‖-u.val‖ := by rw [norm_one, norm_neg]; exact hlt.ne'
        rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one,
          norm_neg, max_eq_left hlt.le]
      change (testF v).val u * _ / _ = _
      rw [h1, h, zpow_neg, zpow_natCast, hs2 k]
      push_cast
      ring
    · rw [indicator_of_notMem (fun h' ↦ h (hiff.mp h'))]
      show (if ‖u.val‖ = q(v) ^ (-(k : ℤ)) then I u else 0) = _
      rw [ite_eq_right h]
  have hGint (k : ℕ) (g : Kˣ) : Integrable
      (O.indicator (fun u' ↦ (s k : ℂ) * (testF v).val (g * u'))) μ𝔭(v) :=
    ((continuous_const.mul (htc.comp (continuous_const.mul continuous_id))).continuousOn
      |>.integrableOn_compact hOc).integrable_indicator hOm
  have hFpi (k : ℕ) (hk : 1 ≤ k) : Integrable (fun u ↦ Fp k u) μ𝔭(v) := by
    rw [hFp k hk]
    exact (hGint k _).comp_mul_left (p ^ k)
  have hFmi (k : ℕ) (hk : 1 ≤ k) : Integrable (fun u ↦ Fm k u) μ𝔭(v) := by
    rw [hFm k hk]
    exact (hGint k _).comp_mul_left (p ^ k)⁻¹
  have hIp (k : ℕ) (hk : 1 ≤ k) : (∫ u, Fp k u ∂μ𝔭(v)) =
      (s k : ℂ) * ∫ u in O, (testF v).val ((p ^ k)⁻¹ * u) ∂μ𝔭(v) := by
    rw [show (∫ u, Fp k u ∂μ𝔭(v)) = ∫ u, (fun u ↦ Fp k u) u ∂μ𝔭(v) from rfl, hFp k hk,
      integral_mul_left_eq_self (μ := μ𝔭(v)) (O.indicator _) (p ^ k), integral_indicator hOm,
      integral_const_mul]
  have hIm (k : ℕ) (hk : 1 ≤ k) : (∫ u, Fm k u ∂μ𝔭(v)) =
      (s k : ℂ) * ∫ u in O, (testF v).val (p ^ k * u) ∂μ𝔭(v) := by
    rw [show (∫ u, Fm k u ∂μ𝔭(v)) = ∫ u, (fun u ↦ Fm k u) u ∂μ𝔭(v) from rfl, hFm k hk,
      integral_mul_left_eq_self (μ := μ𝔭(v)) (O.indicator _) (p ^ k)⁻¹, integral_indicator hOm,
      integral_const_mul]
  have hdec (u : Kˣ) :
      Oᶜ.indicator I u = ∑ m ∈ Finset.range N, (Fp (m + 1) u + Fm (m + 1) u) := by
    by_cases huO : u ∈ O
    · rw [indicator_of_notMem (Set.notMem_compl_iff.mpr huO)]
      have h1 := (hO1 u).mp huO
      refine (Finset.sum_eq_zero fun m _ ↦ ?_).symm
      have hne1 : ¬ (1 : ℝ) = q(v) ^ ((m + 1 : ℕ) : ℤ) := by
        rw [zpow_natCast]
        exact (one_lt_pow₀ hq (Nat.succ_ne_zero m)).ne
      have hne2 : ¬ (1 : ℝ) = q(v) ^ (-((m + 1 : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_natCast]
        exact (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (Nat.succ_ne_zero m))).ne'
      show (if ‖u.val‖ = _ then I u else 0) + (if ‖u.val‖ = _ then I u else 0) = 0
      rw [h1, ite_eq_right hne1, ite_eq_right hne2, add_zero]
    · rw [indicator_of_mem huO]
      by_cases hI : I u = 0
      · rw [hI]
        refine (Finset.sum_eq_zero fun m _ ↦ ?_).symm
        show (if ‖u.val‖ = _ then I u else 0) + (if ‖u.val‖ = _ then I u else 0) = 0
        rw [hI, ite_self, ite_self, add_zero]
      · obtain ⟨n, hn⟩ : ∃ n : ℤ, ‖u.val‖ = q(v) ^ n :=
          ⟨_, norm_adicCompletion_eq_zpow F v u.ne_zero⟩
        have hn0 : n ≠ 0 := by
          rintro rfl
          exact huO ((hO1 u).mpr (by rw [hn, zpow_zero]))
        have htf : f.val (finiteClassMap(v) u) ≠ 0 := by
          rw [← _hF]
          intro h
          exact hI (by simp only [I, h, zero_mul, zero_div])
        obtain ⟨hb1, hb2⟩ := hMb _ (subset_tsupport _ htf)
        rw [hnι, hn] at hb1 hb2
        obtain ⟨k, hk⟩ : ∃ k : ℕ, k = n.natAbs := ⟨_, rfl⟩
        have hkn : n = k ∨ n = -k := by rw [hk]; exact Int.natAbs_eq n
        have hk1 : 1 ≤ k := by rw [hk]; exact Int.natAbs_pos.mpr hn0
        have hbound : q(v) ^ k ≤ M := by
          rcases hkn with h | h
          · rwa [h, zpow_natCast] at hb1
          · rwa [h, zpow_neg, inv_inv, zpow_natCast] at hb2
        have hkN : k - 1 < N := by
          have h2 : (2 : ℝ) ≤ q(v) := by
            have : 1 < Ideal.absNorm v.asIdeal := HeightOneSpectrum.one_lt_absNorm v
            exact_mod_cast this
          have h3 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
          have h4 : (2 : ℝ) ^ k ≤ q(v) ^ k := pow_le_pow_left₀ (by norm_num) h2 _
          have h5 : M ≤ (N : ℝ) := Nat.le_ceil M
          have : (k : ℝ) < N := by linarith
          have : k < N := by exact_mod_cast this
          omega
        have hcond (m : ℕ) : Fp (m + 1) u + Fm (m + 1) u = if m = k - 1 then I u else 0 := by
          have e1 : ‖u.val‖ = q(v) ^ ((m + 1 : ℕ) : ℤ) ↔ n = (m : ℤ) + 1 := by
            rw [hn, zpow_right_inj₀ hq0 hq.ne']
            push_cast
            rfl
          have e2 : ‖u.val‖ = q(v) ^ (-((m + 1 : ℕ) : ℤ)) ↔ n = -((m : ℤ) + 1) := by
            rw [hn, zpow_right_inj₀ hq0 hq.ne']
            push_cast
            rfl
          show (if ‖u.val‖ = _ then I u else 0) + (if ‖u.val‖ = _ then I u else 0) = _
          simp only [e1, e2]
          split_ifs <;> first | (exfalso; omega) | simp
        rw [Finset.sum_congr rfl fun m _ ↦ hcond m, Finset.sum_ite_eq' (Finset.range N) (k - 1),
          ite_eq_left (Finset.mem_range.mpr hkN)]
  have hRHS : (∫ u in Oᶜ, I u ∂μ𝔭(v)) =
      ∑ m ∈ Finset.range N, (s (m + 1) : ℂ) * (P m + Q m) := by
    rw [← integral_indicator hOm.compl, integral_congr_ae (.of_forall hdec),
      integral_finsetSum (Finset.range N) (f := fun m u ↦ Fp (m + 1) u + Fm (m + 1) u) fun m _ ↦ (hFpi (m + 1) (by omega)).add (hFmi (m + 1) (by omega))]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [integral_add (hFpi (m + 1) (by omega)) (hFmi (m + 1) (by omega)),
      hIp (m + 1) (by omega), hIm (m + 1) (by omega), mul_add]
  change HasSum _ (finiteWeilScale(v) * ∫ u in Oᶜ, I u ∂μ𝔭(v))
  rw [hRHS, Finset.mul_sum]
  convert hLHS using 2 with m
  simp only [c, s]
  push_cast
  field_simp

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (prime-power terms). Summed over the
characters trivial on the image of the norm section, the prime-power terms of the explicit
formula of Theorem B.4.2.2 for the radial profiles `Φ_χ` of `f` give the sum over the finite
places of `(log q_v / vol O_v^×) ∫_{|u| ≠ 1} f_v(u) |u|^{1/2} / |1 - u| d^×u`, a sum with only
finitely many nonzero terms.

Proof. The profiles vanish outside a fixed interval (the class norm is bounded above and below
on the support of `f`), so only the finitely many prime powers of bounded norm contribute, for
every character at once, and `f_v` vanishes off the integer units at the other places. The sum
over the characters is then a finite sum of the local sums
`idelicExplicitFormula_finiteMatching_primePowersLocal`. -/
theorem idelicExplicitFormula_finiteMatching_primePowers (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (testF : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_hF : ∀ v u, (testF v).val u = f.val (finiteClassMap(v) u))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    let outside := fun v : Primes(F) ↦ finiteWeilScale(v) *
      ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ)ᶜ,
        (testF v).val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ𝔭(v)
    Summable outside ∧
      HasSum (fun χ : chartChars(τ) ↦ ∑' j, explicitPrimeTerm(χ.val, Φ χ) j) (∑' v, outside v) := by
  intro outside
  obtain ⟨M, hMb⟩ := explicitFormula_tsupport_norm_bound f
  have hq (v : Primes(F)) : (1 : ℝ) < q(v) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hfin : {v : Primes(F) | q(v) ≤ M}.Finite := by
    refine ((Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊M⌋₊).preimage
      fun v _ w _ h ↦ HeightOneSpectrum.ext h).subset fun v hv ↦ ?_
    exact Nat.le_floor (show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≤ M from hv)
  let T : Finset Primes(F) := hfin.toFinset
  let K : ℕ := ⌈M⌉₊
  -- A nonzero prime-power term has `q_v^(m+1) ≤ M`.
  have hbound (χ : chartChars(τ)) (v : Primes(F)) (m : ℕ)
      (h : explicitPrimeTerm(χ.val, Φ χ) (v, m) ≠ 0) : q(v) ^ (m + 1) ≤ M := by
    by_contra hlt
    push Not at hlt
    apply h
    have hx : Real.exp (((m + 1 : ℕ) : ℝ) * Real.log q(v)) = q(v) ^ (m + 1) := by
      rw [Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans (hq v))]
    have h1 : Φ χ (((m + 1 : ℕ) : ℝ) * Real.log q(v)) = 0 := by
      by_contra h1
      have := (explicitFormula_profile_support τ _hτ f Φ _hM hMb χ _ h1).1
      rw [hx] at this
      linarith
    have h2 : Φ χ (-(((m + 1 : ℕ) : ℝ) * Real.log q(v))) = 0 := by
      by_contra h2
      have := (explicitFormula_profile_support τ _hτ f Φ _hM hMb χ _ h2).2
      rw [neg_neg, hx] at this
      linarith
    simp only [h1, h2, mul_zero, add_zero, ite_self]
  have hmemT (χ : chartChars(τ)) (v : Primes(F)) (m : ℕ)
      (h : explicitPrimeTerm(χ.val, Φ χ) (v, m) ≠ 0) : v ∈ T ∧ m < K := by
    have hb := hbound χ v m h
    refine ⟨hfin.mem_toFinset.mpr ((le_self_pow₀ (hq v).le (by omega)).trans hb), ?_⟩
    have h2 : (2 : ℝ) ≤ q(v) := by
      have : 1 < Ideal.absNorm v.asIdeal := HeightOneSpectrum.one_lt_absNorm v
      exact_mod_cast this
    have hm : ((m + 1 : ℕ) : ℝ) ≤ q(v) ^ (m + 1) := by
      have h3 : ((m + 1 : ℕ) : ℝ) < 2 ^ (m + 1) := by exact_mod_cast Nat.lt_two_pow_self
      exact h3.le.trans (pow_le_pow_left₀ (by norm_num) h2 _)
    have : (m : ℝ) < M := by push_cast at hm; linarith
    exact Nat.lt_ceil.mpr this
  have hout (v : Primes(F)) (hv : v ∉ T) : outside v = 0 := by
    have hvM : M < q(v) := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr (not_lt.mp h))
    have hz : ∀ x : (v.adicCompletion F)ˣ, x ∉ (O(v)).units → (testF v).val x = 0 := by
      intro x hx
      rw [_hF]
      by_contra h0
      obtain ⟨h₁, h₂⟩ := hMb _ (subset_tsupport _ h0)
      have hnι : ((ideleClassNorm F (finiteClassMap(v) x) : ℝ≥0) : ℝ) = ‖x.val‖ := by
        simp only [ideleClassNorm_ofAdicCompletion]
        rfl
      rw [hnι] at h₁ h₂
      have hx0 : 0 < ‖x.val‖ := norm_pos_iff.mpr x.ne_zero
      have hq0 : 0 < q(v) := zero_lt_one.trans (hq v)
      rcases explicitFormula_finiteUnits_norm_shell v x hx with h | h
      · linarith
      · have : q(v) ≤ ‖x.val‖⁻¹ := by
          rw [le_inv_comm₀ hq0 hx0]
          exact h
        linarith
    change finiteWeilScale(v) * _ = 0
    rw [setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by
      rw [hz x hx, zero_mul, zero_div], mul_zero]
  have hχsum (χ : chartChars(τ)) : ∑' j, explicitPrimeTerm(χ.val, Φ χ) j =
      ∑ v ∈ T, ∑' m : ℕ, explicitPrimeTerm(χ.val, Φ χ) (v, m) := by
    rw [tsum_eq_sum (s := T ×ˢ Finset.range K) fun j hj ↦ by
      by_contra h
      obtain ⟨h1, h2⟩ := hmemT χ j.1 j.2 h
      exact hj (Finset.mem_product.mpr ⟨h1, Finset.mem_range.mpr h2⟩), Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ ↦ (tsum_eq_sum fun m hm ↦ ?_).symm
    by_contra h
    exact hm (Finset.mem_range.mpr (hmemT χ v m h).2)
  refine ⟨summable_of_ne_finset_zero hout, ?_⟩
  rw [tsum_eq_sum hout]
  convert hasSum_sum (fun v _ ↦
    idelicExplicitFormula_finiteMatching_primePowersLocal τ _hτ f testF _hF Φ _hΦ _hM v) using 1
  funext χ
  exact hχsum χ

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (conductor terms). Summed over the
characters trivial on the image of the norm section, the conductor part of the
discriminant–conductor term (Equation (B.4.2.3)) times `Φ_χ(0)` gives minus the sum over the
finite places of `(log q_v / vol O_v^×) ∫_{O_v^×} (f_v(u) - f_v(1)) |u|^{1/2} / |1 - u| d^×u`,
a sum with only finitely many nonzero terms.

Proof. `f` is invariant under the integer units at all but finitely many places. There both
sides vanish: the integrand is zero, and `Φ_χ(0)` is zero for every `χ` ramified at `v`
(orthogonality on `C¹`). The sum over the characters is then a finite sum of the local sums
`idelicExplicitFormula_finiteMatching_conductorLocal`. -/
theorem idelicExplicitFormula_finiteMatching_conductor (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (testF : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_hF : ∀ v u, (testF v).val u = f.val (finiteClassMap(v) u))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    let inside := fun v : Primes(F) ↦ finiteWeilScale(v) *
      ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ),
        ((testF v).val u - (testF v).val 1) * (Real.sqrt ‖u.val‖ : ℂ) /
          ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ𝔭(v)
    Summable inside ∧
      HasSum (fun χ : chartChars(τ) ↦
        ((heckeLogDiscriminantConductor χ.val - Real.log (Int.natAbs (NumberField.discr F)) :
          ℝ) : ℂ) * Φ χ 0) (-∑' v, inside v) := by
  intro inside
  obtain ⟨k, hk, hinv, _⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 0
  obtain ⟨W, hW, hpow⟩ := explicitFormula_smallPowers (G := C[F]) k hk
  have hI : ∀ᶠ v : Primes(F) in cofinite,
      ∀ u ∈ (O(v)).units, ∀ g : C[F], f.val (g * finiteClassMap(v) u) = f.val g := by
    filter_upwards [explicitFormula_eventually_units_mem W hW] with v hv u hu g
    have hk' : finiteClassMap(v) u ∈ k := hpow _ fun n ↦ by
      rw [← map_pow]
      exact hv _ ((O(v)).units.pow_mem hu n)
    rw [mul_comm]
    exact hinv ⟨_, hk'⟩ g
  let T : Finset Primes(F) := (Filter.eventually_cofinite.mp hI).toFinset
  have hP (v : Primes(F)) (hv : v ∉ T) :
      ∀ u ∈ (O(v)).units, ∀ g : C[F], f.val (g * finiteClassMap(v) u) = f.val g := by
    by_contra h
    exact hv ((Filter.eventually_cofinite.mp hI).mem_toFinset.mpr h)
  have hin (v : Primes(F)) (hv : v ∉ T) : inside v = 0 := by
    change finiteWeilScale(v) * _ = 0
    rw [setIntegral_eq_zero_of_forall_eq_zero fun u hu ↦ by
      have h := hP v hv u hu 1
      rw [one_mul] at h
      rw [_hF, _hF, h, map_one, sub_self, zero_mul, zero_div], mul_zero]
  have hχsum (χ : chartChars(τ)) :
      ((heckeLogDiscriminantConductor χ.val - Real.log (Int.natAbs (NumberField.discr F)) :
        ℝ) : ℂ) * Φ χ 0 = ∑ v ∈ T,
        ((Real.log q(v) * (sInf (conductorExponents(χ.val, v)) : ℕ) : ℝ) : ℂ) * Φ χ 0 := by
    rw [heckeLogDiscriminantConductor, add_sub_cancel_left]
    by_cases h0 : Φ χ 0 = 0
    · simp only [h0, mul_zero, Finset.sum_const_zero]
    rw [finsum_eq_sum_of_support_subset (s := T) _ fun v hv ↦ ?_, ← Finset.sum_mul]
    · push_cast
      rfl
    · by_contra hvT
      apply hv
      by_cases ha : sInf (conductorExponents(χ.val, v)) = 0
      · simp only [ha, Nat.cast_zero, mul_zero]
      · exact absurd (explicitFormula_profile_ramified τ _hτ f Φ _hM v (hP v hvT) χ ha) h0
  refine ⟨summable_of_ne_finset_zero hin, ?_⟩
  rw [tsum_eq_sum hin, ← Finset.sum_neg_distrib]
  convert hasSum_sum (fun v _ ↦
    idelicExplicitFormula_finiteMatching_conductorLocal τ _hτ f testF _hF Φ _hΦ _hM v) using 1
  funext χ
  exact hχsum χ

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (finite places). Let `Φ_χ` be the
radial profiles of a test `f` (Mellin transforms matching the idelic Mellin integrals, as in
`idelicExplicitFormula_mellinMatching`). Summed over the characters trivial on the image of
the norm section, the discriminant–conductor terms minus the prime-power terms of the
explicit formula of Theorem B.4.2.2 for `Φ_χ` give minus the sum over the finite places of
the scaled Connes–Weil principal values of the restrictions of `f`.

Computation. Because the class measure is `dt/t` times the measure on `C¹`
(`classTamagawa_normProduct`), `Φ_χ(x) = vol(C¹)⁻¹ ∫_{C¹} f(τ(eˣ) u) χ(u) du`, and Fourier
inversion on the compact group `C¹` gives `∑_χ χ(c)⁻¹ Φ_χ(log |c|) = f(c)`. Summing only over
the `χ` unramified at `v` averages over `O_v^×`, so the prime-power terms at `v` sum to
`(log q_v / vol O_v^×) ∫_{|u| ≠ 1} f_v(u) |u|^{1/2} / |1 - u| d^×u`. For a character of
`O_v^×` of conductor exponent `a`, `∫_{O_v^×} (χ(u) - 1) / |1 - u| du = -a · vol O_v^×`, so the
conductor terms at `v` sum to `-(log q_v / vol O_v^×) ∫_{O_v^×} (f_v(u) - f_v(1)) / |1 - u| d^×u`,
and `log |d_F| = ∑_v d_v log q_v`. By `finiteConnesWeilPrincipalValue_eq_finitePart` the total is
the claimed sum (`finiteConnesWeilPrincipalValue_unitsIndicator` holds: the Fourier transform of
`1_{-1 + O_v^×}` paired with `-log|y| / log q_v` gives `-d_v`). -/
theorem idelicExplicitFormula_finiteMatching (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (testF : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_hF : ∀ v u, (testF v).val u = f.val (finiteClassMap(v) u))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    HasSum (fun χ : chartChars(τ) ↦ (heckeLogDiscriminantConductor χ.val : ℂ) * Φ χ 0 -
        ∑' j, explicitPrimeTerm(χ.val, Φ χ) j)
      (-∑' v, finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 (testF v)) := by
  obtain ⟨hOutS, hB⟩ :=
    idelicExplicitFormula_finiteMatching_primePowers τ _hτ f testF _hF Φ _hΦ _hM
  obtain ⟨hInS, hC⟩ :=
    idelicExplicitFormula_finiteMatching_conductor τ _hτ f testF _hF Φ _hΦ _hM
  have hA := idelicExplicitFormula_finiteMatching_inversion τ _hτ f Φ _hΦ _hM
  obtain ⟨hDS, hD⟩ := explicitFormula_log_discr_eq_tsum (F := F)
  set Out := fun v : Primes(F) ↦ finiteWeilScale(v) *
      ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ)ᶜ,
        (testF v).val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ𝔭(v) with hOut
  set In := fun v : Primes(F) ↦ finiteWeilScale(v) *
      ∫ u in ((O(v)).units : Set (v.adicCompletion F)ˣ),
        ((testF v).val u - (testF v).val 1) * (Real.sqrt ‖u.val‖ : ℂ) /
          ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ𝔭(v) with hIn
  set Dv := fun v : Primes(F) ↦
    (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℝ) * Real.log q(v) with hDv
  have h1 (v : Primes(F)) : (testF v).val 1 = f.val 1 := by rw [_hF, map_one]
  -- Each principal value is the finite part minus the different contribution.
  have hPV (v : Primes(F)) : finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 (testF v) =
      Out v + In v - ((Dv v : ℝ) : ℂ) * f.val 1 := by
    rw [(finiteConnesWeilPrincipalValue_eq_finitePart v (testF v)).2.2, mul_add]
    simp only [Out, In, Dv, h1]
  have hDc : Summable (fun v ↦ ((Dv v : ℝ) : ℂ) * f.val 1) :=
    (Complex.ofRealCLM.summable hDS).mul_right _
  have htot := ((hA.mul_left ((Real.log (Int.natAbs (NumberField.discr F)) : ℝ) : ℂ)).add hC).sub hB
  convert htot using 1
  · funext χ
    push_cast
    ring
  · rw [tsum_congr hPV, Summable.tsum_sub (hOutS.add hInS) hDc, Summable.tsum_add hOutS hInS,
      tsum_mul_right, ← Complex.ofReal_tsum, hD]
    ring

section ExplicitFormulaRealPlace

/-- At a real place, the class of a real unit has class norm its absolute value. -/
private theorem explicitFormula_real_classNorm (w : InfinitePlace F) (hw : w.IsReal) (u : ℝˣ) :
    ((ideleClassNorm F (infiniteClassMap(w)
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom u)) :
        ℝ≥0) : ℝ) = |(u : ℝ)| := by
  rw [ideleClassNorm_ofCompletion, hw.mult_eq_one, pow_one]
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  change ‖j.symm (u : ℝ)‖ = |(u : ℝ)|
  rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right (u : ℝ), ← j.symm.dist_eq _ 0,
    show j.symm 0 = 0 from map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm]

/-- At a real place, a character on the class of a real unit is given by its radial exponent
and sign parity. -/
private theorem explicitFormula_real_character (w : InfinitePlace F) (hw : w.IsReal)
    (χ : U[F]) (u : ℝˣ) :
    ((χ (infiniteClassMap(w)
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom u)) :
        Circle) : ℂ) =
      (‖(u : ℝ)‖ : ℂ) ^ (realHeckeCharacter_parameters χ w hw).exists.choose.1 *
        (if 0 < (u : ℝ) then 1 else (-1 : ℂ)) ^
          (realHeckeCharacter_parameters χ w hw).exists.choose.2.val := by
  rw [← ((realHeckeCharacter_parameters χ w hw).exists.choose_spec.2 u)]
  change _ = (χ _ : ℂ) * (_ : ℂ) ^ (0 : ℂ)
  rw [Complex.cpow_zero, mul_one]

/-- `(e^x)^a = e^{a x}` for real `x`. -/
private theorem explicitFormula_exp_cpow (x : ℝ) (a : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ a = Complex.exp (a * x) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

/-- The parity weight of the real digamma kernel as a sign average:
`e^{-(1/2 + b + ε) t / 2} = e^{-t/4} ((c₊ + c₋)/2 + e^{-t/2} (c₊ - c₋)/2)` with
`c₊ = e^{-b t/2}` and `c₋ = (-1)^ε e^{-b t/2}`. -/
private theorem explicitFormula_real_kernel_alg (b : ℂ) (ε : Fin 2) (t : ℝ) :
    Complex.exp (-((1 / 2 + b + (ε.val : ℂ)) / 2) * (t : ℂ)) =
      ((Real.exp (-(t / 4)) : ℝ) : ℂ) *
        (((Complex.exp (b * ((t / 2 : ℝ) : ℂ)))⁻¹ +
            (Complex.exp (b * ((t / 2 : ℝ) : ℂ)) * (-1 : ℂ) ^ ε.val)⁻¹) / 2 +
          ((Real.exp (-(t / 2)) : ℝ) : ℂ) * ((Complex.exp (b * ((t / 2 : ℝ) : ℂ)))⁻¹ -
            (Complex.exp (b * ((t / 2 : ℝ) : ℂ)) * (-1 : ℂ) ^ ε.val)⁻¹) / 2) := by
  have h1 : ((Real.exp (-(t / 4)) : ℝ) : ℂ) = Complex.exp (-(t / 4 : ℂ)) := by
    push_cast; rfl
  have h2 : ((Real.exp (-(t / 2)) : ℝ) : ℂ) = Complex.exp (-(t / 2 : ℂ)) := by
    push_cast; rfl
  rw [h1, h2]
  push_cast
  fin_cases ε
  · simp only [pow_zero, mul_one, Nat.cast_zero, add_zero, sub_self,
      mul_zero, zero_div, ← Complex.exp_neg, add_self_div_two]
    rw [← Complex.exp_add]
    congr 1
    ring
  · simp only [pow_one, mul_neg, mul_one, Nat.cast_one, inv_neg,
      ← Complex.exp_neg, sub_neg_eq_add, add_neg_cancel, zero_div, zero_add]
    rw [mul_div_assoc, add_self_div_two, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring

/-- Fourier inversion on the norm shells through `±e^y` at a real place, with the character
values written through the radial exponent `a` and sign parity `ε` of each character. -/
private theorem explicitFormula_real_shell (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (w : InfinitePlace F)
    (hw : w.IsReal) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) (y : ℝ) :
    let e : ℝˣ →* w.Completionˣ :=
      Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
    HasSum (fun χ : chartChars(τ) ↦ Φ χ y *
        (Complex.exp ((realHeckeCharacter_parameters χ.val w hw).exists.choose.1 * y))⁻¹)
        (f.val (infiniteClassMap(w) (e (Units.mk0 (Real.exp y) (Real.exp_pos y).ne')))) ∧
      HasSum (fun χ : chartChars(τ) ↦ Φ χ y *
        (Complex.exp ((realHeckeCharacter_parameters χ.val w hw).exists.choose.1 * y) *
          (-1 : ℂ) ^ (realHeckeCharacter_parameters χ.val w hw).exists.choose.2.val)⁻¹)
        (f.val (infiniteClassMap(w) (e (-Units.mk0 (Real.exp y) (Real.exp_pos y).ne')))) := by
  intro e
  have hy := Real.exp_pos y
  constructor
  · have h := explicitFormula_shell_inversion τ hτ f Φ hM
      (infiniteClassMap(w) (e (Units.mk0 (Real.exp y) hy.ne')))
    rw [explicitFormula_real_classNorm w hw, Units.val_mk0, abs_of_pos hy, Real.log_exp] at h
    convert h using 2 with χ
    rw [Circle.coe_inv, explicitFormula_real_character w hw, Units.val_mk0, ite_eq_left hy, one_pow,
      mul_one, Real.norm_of_nonneg hy.le, explicitFormula_exp_cpow]
  · have h := explicitFormula_shell_inversion τ hτ f Φ hM
      (infiniteClassMap(w) (e (-Units.mk0 (Real.exp y) hy.ne')))
    rw [explicitFormula_real_classNorm w hw, Units.val_neg, Units.val_mk0, abs_neg,
      abs_of_pos hy, Real.log_exp] at h
    convert h using 2 with χ
    rw [Circle.coe_inv, explicitFormula_real_character w hw, Units.val_neg, Units.val_mk0,
      ite_eq_right (by linarith), norm_neg, Real.norm_of_nonneg hy.le, explicitFormula_exp_cpow]

end ExplicitFormulaRealPlace


/-- Fourier inversion followed by character orthogonality on a subgroup selects one
restriction fiber of the full dual. Its Fourier mass bounds every translate. -/
private theorem idelicExplicitFormula_infiniteMatching_realDomination_fiber
    {G K : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] (j : K →ₜ* G) (μ : Measure K) [μ.IsMulLeftInvariant]
    [IsFiniteMeasure μ] [NeZero μ] (ν : Measure (PontryaginDual G)) [SFinite ν]
    (H : PontryaginDual G → ℂ) (hi : Integrable H ν) (f : G → ℂ)
    (hinv : ∀ x, f x = ∫ ψ, H ψ * (ψ x : ℂ) ∂ν) (χ : PontryaginDual K) (g : G) :
    ‖((μ univ).toReal : ℂ)⁻¹ * ∫ u, f (g * j u) * (χ u : ℂ) ∂μ‖ ≤
      ∫ ψ in {ψ | PontryaginDual.map j ψ = χ⁻¹}, ‖H ψ‖ ∂ν := by
  let r := PontryaginDual.map j
  let S := {ψ | r ψ = χ⁻¹}
  have hm : MeasurableSet S := (isClosed_singleton.preimage r.continuous).measurableSet
  have hV : ((μ univ).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ENNReal.toReal_ne_zero.mpr ⟨Measure.measure_univ_ne_zero.mpr (NeZero.ne μ), measure_ne_top μ _⟩)
  have horth (ψ : PontryaginDual G) :
      ∫ u : K, (ψ (j u) : ℂ) * (χ u : ℂ) ∂μ =
        if ψ ∈ S then ((μ univ).toReal : ℂ) else 0 := by
    let δ := r ψ * χ
    have he (u : K) : (δ u : ℂ) = (ψ (j u) : ℂ) * (χ u : ℂ) := rfl
    simp_rw [← he]
    split_ifs with h
    · have hz : δ = 1 := eq_inv_iff_mul_eq_one.mp h
      rw [hz]
      change (∫ _ : K, (1 : ℂ) ∂μ) = _
      rw [integral_const, Complex.real_smul, mul_one]
      rfl
    · obtain ⟨u, hu⟩ : ∃ u, δ u ≠ 1 := by
        by_contra! hh
        exact h ((eq_inv_iff_mul_eq_one).mpr (DFunLike.ext _ _ hh : δ = 1))
      exact explicitFormula_integral_character_eq_zero μ δ hu
  let L (u : K) (ψ : PontryaginDual G) := H ψ * (ψ (g * j u) : ℂ) * (χ u : ℂ)
  have hEval : Continuous (fun p : K × PontryaginDual G ↦ (p.2 (g * j p.1) : ℂ)) :=
    continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous.comp continuous_snd).prodMk
        (continuous_const.mul (j.continuous.comp continuous_fst))))
  have hL : Integrable (uncurry L) (μ.prod ν) := by
    refine (hi.norm.comp_snd μ).mono' ?_ (.of_forall fun ⟨u, ψ⟩ ↦ ?_)
    · exact ((hi.comp_snd μ).aestronglyMeasurable.mul hEval.aestronglyMeasurable).mul
        (continuous_subtype_val.comp (χ.continuous.comp continuous_fst)).aestronglyMeasurable
    · simp only [L, uncurry_apply_pair, norm_mul, Circle.norm_coe, mul_one]
      rfl
  have hswap : (∫ u, f (g * j u) * (χ u : ℂ) ∂μ) =
      ∫ ψ, ∫ u, L u ψ ∂μ ∂ν := by
    refine Eq.trans (integral_congr_ae (.of_forall fun u ↦ ?_)) (integral_integral_swap hL)
    exact (congrArg (· * (χ u : ℂ)) (hinv (g * j u))).trans (integral_mul_const ..).symm
  have hinner (ψ : PontryaginDual G) : (∫ u, L u ψ ∂μ) =
      ((μ univ).toReal : ℂ) * S.indicator (fun ψ ↦ H ψ * (ψ g : ℂ)) ψ := by
    have he (u : K) : L u ψ = (H ψ * (ψ g : ℂ)) * ((ψ (j u) : ℂ) * (χ u : ℂ)) := by
      simp only [L, map_mul, Circle.coe_mul]; ring
    simp_rw [he]
    rw [integral_const_mul, horth]
    by_cases h : ψ ∈ S <;> simp [h, mul_comm]
  rw [hswap]
  simp_rw [hinner]
  rw [integral_const_mul, inv_mul_cancel_left₀ hV, integral_indicator hm]
  exact norm_integral_le_of_norm_le hi.norm.integrableOn (.of_forall fun ψ ↦ by
    simp only [norm_mul, Circle.norm_coe, mul_one, le_refl])

/-- The Fourier coefficients of all translates of a test on the norm-one subgroup have a
common summable majorant. By Fourier inversion each coefficient uses only the part of the
dual whose restriction is the inverse character. These parts are pairwise disjoint. -/
private theorem idelicExplicitFormula_infiniteMatching_realDomination_translates
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) :
    ∃ A : chartChars(τ) → ℝ, Summable A ∧ ∀ χ (g : C[F]),
      ‖(classVolume : ℂ)⁻¹ * ∫ u, f.val (g * (u : C[F])) * (χ.val (u : C[F]) : ℂ)
        ∂normOneIdeleClassTamagawaMeasure F‖ ≤ A χ := by
  let K := (ideleClassNorm F).ker
  let μ := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let mK : MeasurableSpace K := Subtype.instMeasurableSpace
  have hB : @BorelSpace K _ mK := Subtype.borelSpace _
  let : CompactSpace K := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : SecondCountableTopology (AdeleRing (𝓞 F) F) := adeleGroupSecondCountable F
  let : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (IdeleGroup (𝓞 F) F) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  let : SecondCountableTopology C[F] :=
    Topology.IsOpenQuotientMap.secondCountableTopology (ideleGroup_quotient.{_, 0} F).2.2.2.2.1
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  let : SecondCountableTopology U[F] :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C[F] Circle).secondCountableTopology
  let : MeasurableSpace U[F] := borel _
  let : BorelSpace U[F] := ⟨rfl⟩
  let : (classMeasure).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  obtain ⟨ν, hν⟩ := (lcaPlancherelMeasure_existsUnique classMeasure).exists
  let : ν.IsHaarMeasure := hν.1
  let v : SchwartzBruhat C[F] := ⟨f.val, explicitTest_mem_schwartz f⟩
  let H := lcaFourier classMeasure v
  -- Fourier inversion as in AppD §1c, schwartzBruhat_fourier_inversion, using the compact
  -- support of the test for its L² bound.
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_continuousLinear classMeasure
  have hi : Integrable H ν := (SchwartzBruhat.integrable ν (T v)).congr (.of_forall (hT v))
  have hfc := explicitTest_continuous f
  have hf₂ : MemLp f.val 2 classMeasure := hfc.memLp_of_hasCompactSupport f.property.2
  obtain ⟨v', hv', hval⟩ := lcaInverseFourier_zeroAtInfty classMeasure ν hν _ H hi
    ((lcaFourier_unitary classMeasure ν hν).exists.choose_spec f.val
      (hfc.integrable_of_hasCompactSupport f.property.2) hf₂)
  have hinv : (v' : C[F] → ℂ) = f.val :=
    Measure.eq_of_ae_eq (hv'.trans hf₂.coeFn_toLp) v'.continuous hfc
  let r : U[F] →ₜ* PontryaginDual K := PontryaginDual.map ⟨K.subtype, continuous_subtype_val⟩
  let S (χ : chartChars(τ)) := {ψ : U[F] | r ψ = (r χ.val)⁻¹}
  have hm (χ : chartChars(τ)) : MeasurableSet (S χ) :=
    (isClosed_singleton.preimage r.continuous).measurableSet
  have hd : Pairwise (Disjoint on S) := by
    intro χ η hne
    refine Set.disjoint_left.mpr fun ψ hχ hη ↦ hne ?_
    have he := inv_injective (hχ.symm.trans hη : (r χ.val)⁻¹ = (r η.val)⁻¹)
    exact explicitFormula_chartChar_ext τ hτ χ η (DFunLike.congr_fun he)
  refine ⟨fun χ ↦ ∫ ψ in S χ, ‖H ψ‖ ∂ν, ?_, ?_⟩
  · apply summable_of_sum_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) (c := ∫ ψ, ‖H ψ‖ ∂ν)
    intro s
    rw [← integral_biUnion_finset s (fun i _ ↦ hm i) (fun _ _ _ _ h ↦ hd h)
      (fun _ _ ↦ hi.norm.integrableOn)]
    exact setIntegral_le_integral hi.norm (.of_forall fun _ ↦ norm_nonneg _)
  intro χ g
  exact idelicExplicitFormula_infiniteMatching_realDomination_fiber
    (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* C[F]) μ ν H hi f.val
    (fun x ↦ (congrFun hinv x).symm.trans (hval x)) (r χ.val) g

/-- On the local positive real flow the phase of the character is exactly the difference
between translating along this flow and translating along the chosen norm section. -/
private theorem idelicExplicitFormula_infiniteMatching_realDomination_flow
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (w : InfinitePlace F) (hw : w.IsReal) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    ∃ b : Multiplicative ℝ →ₜ* C[F], ∀ χ (x : ℝ),
      (classVolume : ℂ)⁻¹ * (∫ u, f.val (b (Multiplicative.ofAdd x) * (u : C[F])) *
        (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) =
      Φ χ x * Complex.exp (-(realHeckeCharacter_parameters χ.val w hw).exists.choose.1 * x) := by
  let e : ℝˣ →ₜ* w.Completionˣ :=
    ⟨Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
  let expU : Multiplicative ℝ →ₜ* ℝˣ :=
    { toFun := fun t ↦ Units.mk0 (Real.exp t.toAdd) (Real.exp_pos _).ne'
      map_one' := Units.ext Real.exp_zero
      map_mul' := fun x y ↦ Units.ext (Real.exp_add _ _)
      continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
        (Real.continuous_exp.comp continuous_toAdd) }
  let b := (⟨infiniteClassMap(w), continuous_ideleClass_ofCompletion F w⟩ :
    w.Completionˣ →ₜ* C[F]).comp (e.comp expU)
  refine ⟨b, fun χ x ↦ ?_⟩
  let r := radialFlow(τ, x)
  let g := b (Multiplicative.ofAdd x)
  have hn : ideleClassNorm F g = positiveRealLogEquiv.symm (Multiplicative.ofAdd x) := by
    apply positiveRealLogEquiv.injective
    apply Multiplicative.toAdd.injective
    rw [ContinuousMulEquiv.apply_symm_apply, positiveRealLogEquiv_apply]
    rw [show ((ideleClassNorm F g : ℝ≥0) : ℝ) = |Real.exp x| from
      explicitFormula_real_classNorm w hw (expU (Multiplicative.ofAdd x)),
      abs_of_pos (Real.exp_pos _), Real.log_exp, toAdd_ofAdd]
  let k : (ideleClassNorm F).ker := ⟨r⁻¹ * g, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, show ideleClassNorm F r = _ from hτ _, hn,
      inv_mul_cancel]⟩
  let mK : MeasurableSpace (ideleClassNorm F).ker := Subtype.instMeasurableSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : BorelSpace C[F] := ⟨rfl⟩
  have hB : @BorelSpace (ideleClassNorm F).ker _ mK := Subtype.borelSpace _
  have : @MeasurableMul (ideleClassNorm F).ker mK _ := @ContinuousMul.measurableMul _ _ mK hB _ _
  have hχ : (χ.val (k : C[F]) : ℂ) =
      Complex.exp ((realHeckeCharacter_parameters χ.val w hw).exists.choose.1 * x) := by
    simp only [k, map_mul, map_inv, show χ.val r = 1 from χ.property _, inv_one, one_mul]
    rw [show (χ.val g : ℂ) = _ from
      explicitFormula_real_character w hw χ.val (expU (Multiplicative.ofAdd x))]
    change (‖Real.exp x‖ : ℂ) ^ _ * (if 0 < Real.exp x then 1 else (-1 : ℂ)) ^ _ = _
    rw [ite_eq_left (Real.exp_pos x), one_pow, mul_one, Real.norm_of_nonneg (Real.exp_pos x).le,
      explicitFormula_exp_cpow]
  rw [neg_mul, Complex.exp_neg, ← hχ, ← div_eq_mul_inv, eq_div_iff (Circle.coe_ne_zero _),
    explicitFormula_profile_eq τ hτ f Φ hM χ x, mul_assoc, ← integral_mul_const]
  congr 1
  refine Eq.trans (integral_congr_ae (.of_forall fun u ↦ ?_))
    (integral_mul_left_eq_self (μ := normOneIdeleClassTamagawaMeasure F)
      (fun u : (ideleClassNorm F).ker ↦ f.val (r * (u : C[F])) * (χ.val (u : C[F]) : ℂ)) k)
  change f.val (g * (u : C[F])) * _ * _ = f.val (r * ((r⁻¹ * g) * (u : C[F]))) * _
  rw [← mul_assoc r, mul_inv_cancel_left]
  simp only [Subgroup.coe_mul, map_mul, Circle.coe_mul]
  ring

/-- After the local character has been absorbed into the profile, subtract its value at zero
before estimating the two samples. A Lipschitz bound then cancels the singular denominator. -/
private theorem idelicExplicitFormula_infiniteMatching_realDomination_bound
    (g : ℝ → ℂ) (c B t : ℝ) (hc : 1 / 4 ≤ c) (hc' : c ≤ 1) (hB : 0 ≤ B)
    (hg : ∀ x : ℝ, ‖g x - g 0‖ ≤ B * |x|) (ht : 0 < t) :
    ‖(1 / 2 : ℂ) * (2 * (Real.exp (-t) : ℂ) * g 0 / t -
      (Real.exp (-c * t) : ℂ) * (g (t / 2) + g (-(t / 2))) / (1 - (Real.exp (-t) : ℂ)))‖ ≤
      (2 * ‖g 0‖ + B) * ((1 + t) * Real.exp (-(1 / 4) * t)) := by
  let E := Real.exp (-t)
  let Z := Real.exp (-c * t)
  let d := 1 - E
  have hE : 0 < E := Real.exp_pos _
  have hZ : 0 < Z := Real.exp_pos _
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))
  have hEZ : E ≤ Z := Real.exp_le_exp.mpr (by nlinarith)
  have hZ1 : Z ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hZt : Z ≤ Real.exp (-(1 / 4) * t) := Real.exp_le_exp.mpr (by nlinarith)
  have hr := digamma_remainder_bounds ht
  change -1 ≤ 1 / t - 1 / d ∧ 1 / t - 1 / d ≤ 0 at hr
  have htd : t / d ≤ 1 + t := by
    have h := mul_le_mul_of_nonneg_right hr.1 ht.le
    field_simp [ht.ne', hd.ne'] at h ⊢
    linarith
  have hconst : |E / t - Z / d| ≤ 2 * Z := by
    have hrem : |E * (1 / t - 1 / d)| ≤ E := by
      rw [abs_mul, abs_of_pos hE]
      exact mul_le_of_le_one_right hE.le (abs_le.mpr ⟨hr.1, hr.2.trans zero_le_one⟩)
    have hdiff : |(E - Z) / d| ≤ Z := by
      rw [abs_div, abs_of_pos hd, abs_of_nonpos (sub_nonpos.mpr hEZ), div_le_iff₀ hd]
      dsimp [d]
      nlinarith [mul_le_mul_of_nonneg_right hZ1 hE.le]
    rw [show E / t - Z / d = E * (1 / t - 1 / d) + (E - Z) / d by ring]
    linarith [abs_add_le (E * (1 / t - 1 / d)) ((E - Z) / d)]
  let Δ := (g (t / 2) - g 0) + (g (-(t / 2)) - g 0)
  have hΔ : ‖Δ‖ ≤ B * t := by
    have hp := hg (t / 2)
    have hm := hg (-(t / 2))
    rw [abs_neg] at hm
    rw [abs_of_pos (half_pos ht)] at hp hm
    exact (norm_add_le _ _).trans (by linarith)
  have heq : (1 / 2 : ℂ) * (2 * (E : ℂ) * g 0 / t -
      (Z : ℂ) * (g (t / 2) + g (-(t / 2))) / (1 - (E : ℂ))) =
      ((E / t - Z / d : ℝ) : ℂ) * g 0 - ((Z / (2 * d) : ℝ) : ℂ) * Δ := by
    dsimp only [Δ, d]
    push_cast
    rw [div_mul_eq_div_div]
    ring
  rw [heq]
  calc
    _ ≤ |E / t - Z / d| * ‖g 0‖ + (Z / (2 * d)) * ‖Δ‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ Z / (2 * d) by positivity)] using
        norm_sub_le (((E / t - Z / d : ℝ) : ℂ) * g 0) (((Z / (2 * d) : ℝ) : ℂ) * Δ)
    _ ≤ (2 * Z) * ‖g 0‖ + Z / (2 * d) * (B * t) :=
      add_le_add (mul_le_mul_of_nonneg_right hconst (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hΔ (by positivity))
    _ ≤ (2 * ‖g 0‖ + B) * ((1 + t) * Z) := by
      rw [show Z / (2 * d) * (B * t) = (B * Z / 2) * (t / d) by rw [div_mul_eq_div_div]; ring]
      have hm := mul_le_mul_of_nonneg_left htd (show 0 ≤ B * Z / 2 by positivity)
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (g 0)) ht.le) hZ.le,
        mul_nonneg (mul_nonneg hB (show 0 ≤ 1 + t by linarith)) hZ.le]
    _ ≤ _ := by gcongr

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (domination at a real place `w`). For
the radial profiles `Φ_χ` of a test `f` (as in `idelicExplicitFormula_finiteMatching`), each
real digamma kernel `t ↦ K_χ(t)` at `w` (with the radial exponent and sign parity of `χ` at
`w`) is integrable on `(0, ∞)`, and `∑_χ ∫_0^∞ |K_χ(t)| dt < ∞`.

Why it holds. `Φ_χ(x)` is the Fourier coefficient on `C¹` of the translate of `f` by the norm
section at `eˣ`, supported in a fixed interval `|x| ≤ log M` (`f` has compact support). Near
`t = 0` the kernel is bounded by `C (1 + |a_χ|)² (sup |Φ_χ| + sup |Φ_χ'| + sup |Φ_χ''|)`
(`a_χ` the radial exponent at `w`, `Φ_χ'` the profile of the flow derivative of `f`), and for
`t ≥ 1` by `C e^{-t/4} sup |Φ_χ|`. These suprema times any power of `1 + |a_χ|` are summable
over `χ`: the coefficients of the smooth function `f` on `C¹` decay faster than any power of
the archimedean frequency, uniformly on the compact set of translates
(`idelicExplicitFormula_normOneFourier_summable`). -/
theorem idelicExplicitFormula_infiniteMatching_realDomination (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (w : InfinitePlace F)
    (hw : w.IsReal) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    let K : chartChars(τ) → ℝ → ℂ := fun χ t ↦
      let p := (realHeckeCharacter_parameters χ.val w hw).exists.choose
      heckeArchimedeanDigammaKernel (1 / 2) ((1 / 2 + p.1 + p.2.val) / 2)
        ((1 / 2 - p.1 + p.2.val) / 2) (Φ χ) t
    (∀ χ, IntegrableOn (K χ) (Ioi 0)) ∧
      Summable (fun χ ↦ ∫ t in Ioi (0 : ℝ), ‖K χ t‖) := by
  intro K
  obtain ⟨b, hb⟩ := idelicExplicitFormula_infiniteMatching_realDomination_flow τ _hτ f w hw Φ _hM
  let D : 𝒟(C[F]) := ⟨_, explicitFormula_flowDeriv_mem b f⟩
  obtain ⟨A, hAs, hA⟩ := idelicExplicitFormula_infiniteMatching_realDomination_translates τ _hτ f
  obtain ⟨B, hBs, hB⟩ := idelicExplicitFormula_infiniteMatching_realDomination_translates τ _hτ D
  let G (φ : 𝒟(C[F])) (χ : chartChars(τ)) (y : ℝ) := (classVolume : ℂ)⁻¹ *
    ∫ u, φ.val (b (Multiplicative.ofAdd y) * (u : C[F])) * (χ.val (u : C[F]) : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F
  have hder (χ : chartChars(τ)) (x : ℝ) : HasDerivAt (G f χ) (G D χ x) x :=
    (explicitFormula_radial_hasDerivAt b χ.val f x).const_mul _
  have hLip (χ : chartChars(τ)) (x : ℝ) : ‖G f χ x - G f χ 0‖ ≤ B χ * |x| := by
    simpa only [sub_zero, Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ ↦ (hder χ y).hasDerivWithinAt) (fun y _ ↦ hB χ (b (Multiplicative.ofAdd y)))
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
  let E (t : ℝ) := (1 + t) * Real.exp (-(1 / 4) * t)
  have hi : IntegrableOn E (Ioi 0) := by
    have h₁ := integrableOn_exp_mul_Ioi (a := -(1 / 4)) (by norm_num) 0
    have h₂ : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(1 / 4) * t)) (Ioi 0) := by
      simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num)
        one_pos (by norm_num : 0 < (1 / 4 : ℝ)))
    simpa only [E, Pi.add_def, add_mul, one_mul] using h₁.add h₂
  have hbound (χ : chartChars(τ)) (t : ℝ) (ht : 0 < t) :
      ‖K χ t‖ ≤ (2 * A χ + B χ) * E t := by
    let p := (realHeckeCharacter_parameters χ.val w hw).exists.choose
    let c : ℝ := (1 / 2 + p.2.val) / 2
    have hc : 1 / 4 ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) p.2.val]
    have hc' : c ≤ 1 := by
      have hn : p.2.val ≤ 1 := Nat.le_of_lt_succ p.2.isLt
      have hr : (p.2.val : ℝ) ≤ 1 := by exact_mod_cast hn
      dsimp [c]; linarith
    have he (z : ℂ) :
        Complex.exp (-((1 / 2 + z + p.2.val) / 2) * t) =
          (Real.exp (-c * t) : ℂ) * Complex.exp (-z * ((t / 2 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [c]; push_cast; ring
    have heq : K χ t = (1 / 2 : ℂ) * (2 * (Real.exp (-t) : ℂ) * G f χ 0 / t -
        (Real.exp (-c * t) : ℂ) * (G f χ (t / 2) + G f χ (-(t / 2))) /
          (1 - (Real.exp (-t) : ℂ))) := by
      change heckeArchimedeanDigammaKernel _ ((1 / 2 + p.1 + p.2.val) / 2)
        ((1 / 2 - p.1 + p.2.val) / 2) (Φ χ) t = _
      simp only [heckeArchimedeanDigammaKernel, one_div_mul_eq_div, sub_eq_add_neg (1 / 2 : ℂ) p.1,
        he, show ∀ y, G f χ y = Φ χ y * Complex.exp (-p.1 * y) from hb χ,
        Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, neg_neg, Complex.ofReal_neg,
        neg_mul_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring
    rw [heq]
    refine (idelicExplicitFormula_infiniteMatching_realDomination_bound (G f χ) c (B χ) t hc hc'
      ((norm_nonneg _).trans (hB χ 1)) (hLip χ) ht).trans ?_
    have h₀ : ‖G f χ 0‖ ≤ A χ := hA χ (b (Multiplicative.ofAdd 0))
    exact mul_le_mul_of_nonneg_right (by linarith : 2 * ‖G f χ 0‖ + B χ ≤ 2 * A χ + B χ)
      (show 0 ≤ E t from mul_nonneg (by linarith : 0 ≤ 1 + t) (Real.exp_pos _).le)
  have hae (χ : chartChars(τ)) : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖K χ t‖ ≤ (2 * A χ + B χ) * E t :=
    (ae_restrict_mem measurableSet_Ioi).mono (fun t ht ↦ hbound χ t ht)
  have hKi (χ : chartChars(τ)) : IntegrableOn (K χ) (Ioi 0) := by
    refine (hi.const_mul _).mono' ?_ (hae χ)
    apply Measurable.aestronglyMeasurable
    dsimp only [K, heckeArchimedeanDigammaKernel]
    fun_prop
  refine ⟨hKi, Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_
    (((hAs.mul_left 2).add hBs).mul_right (∫ t in Ioi (0 : ℝ), E t))⟩
  intro χ
  rw [← integral_const_mul]
  exact integral_mono_ae (hKi χ).norm (hi.const_mul _) (hae χ)


/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (character sum at a real place `w`).
Let `Φ_χ` be the radial profiles of a test `f`, as in `idelicExplicitFormula_finiteMatching`,
and write `g₊(y) = f(e^y)`, `g₋(y) = f(-e^y)` for the test along the positive and negative
half-lines of `F_w = ℝ`. Summed over the characters trivial on the image of the norm section,
the archimedean digamma terms at `w` are
`∫_0^∞ ½ (2 e^{-t} f(1) / t - e^{-t/4} (Q(t/2) + Q(-t/2)) / (1 - e^{-t})) dt - log π · f(1)`
with `Q(y) = (g₊(y) + g₋(y)) / 2 + e^{-t/2} (g₊(y) - g₋(y)) / 2`.

Computation. Write `χ_w(x) = |x|^a sgn(x)^ε`. Fourier inversion on `C¹` (translated to the
norm shell `log |g| = y`) gives `∑_χ Φ_χ(y) χ(g)⁻¹ = f(g)`; here `Φ_χ(±t/2) e^{∓a t/2} =
Φ_χ(±t/2) χ_w(e^{±t/2})⁻¹`, and `e^{-εt/2} = (1 + χ_w(-1)) / 2 + e^{-t/2} (1 - χ_w(-1)) / 2`
turns the parity weight of the kernel into the sign average. The sums commute with the
integral over `t` because the coefficients of `f` and of its derivatives along the
archimedean flows are absolutely summable (`idelicExplicitFormula_normOneFourier_summable`). -/
theorem idelicExplicitFormula_infiniteMatching_realCharacterSum (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (w : InfinitePlace F)
    (hw : w.IsReal) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    let e : ℝˣ →* w.Completionˣ :=
      Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
    let gp : ℝ → ℂ := fun y ↦
      f.val (infiniteClassMap(w) (e (Units.mk0 (Real.exp y) (Real.exp_pos y).ne')))
    let gm : ℝ → ℂ := fun y ↦
      f.val (infiniteClassMap(w) (e (-Units.mk0 (Real.exp y) (Real.exp_pos y).ne')))
    let Q : ℝ → ℝ → ℂ := fun t y ↦
      (gp y + gm y) / 2 + (Real.exp (-(t / 2)) : ℂ) * (gp y - gm y) / 2
    HasSum (fun χ : chartChars(τ) ↦ explicitArchTerm(χ.val, w, Φ χ))
      ((∫ t in Ioi (0 : ℝ), (1 / 2 : ℂ) * (2 * (Real.exp (-t) : ℂ) * f.val 1 / (t : ℂ) -
          (Real.exp (-(t / 4)) : ℂ) * (Q t (t / 2) + Q t (-(t / 2))) /
            (1 - (Real.exp (-t) : ℂ)))) -
        (Real.log Real.pi : ℂ) * f.val 1) := by
  intro e gp gm Q
  have hdom := idelicExplicitFormula_infiniteMatching_realDomination τ _hτ f w hw Φ _hΦ _hM
  let P : chartChars(τ) → ℂ × Fin 2 := fun χ ↦
    (realHeckeCharacter_parameters χ.val w hw).exists.choose
  let K : chartChars(τ) → ℝ → ℂ := fun χ t ↦
    heckeArchimedeanDigammaKernel (1 / 2) ((1 / 2 + (P χ).1 + (P χ).2.val) / 2)
      ((1 / 2 - (P χ).1 + (P χ).2.val) / 2) (Φ χ) t
  have hKi : ∀ χ, IntegrableOn (K χ) (Ioi 0) := hdom.1
  have hKs : Summable (fun χ ↦ ∫ t in Ioi (0 : ℝ), ‖K χ t‖) := hdom.2
  let S : ℝ → ℂ := fun t ↦ (1 / 2 : ℂ) * (2 * (Real.exp (-t) : ℂ) * f.val 1 / (t : ℂ) -
    (Real.exp (-(t / 4)) : ℂ) * (Q t (t / 2) + Q t (-(t / 2))) / (1 - (Real.exp (-t) : ℂ)))
  have h0 := idelicExplicitFormula_finiteMatching_inversion τ _hτ f Φ _hΦ _hM
  -- The kernels sum pointwise to the sign-averaged kernel.
  have hpt (t : ℝ) : HasSum (fun χ ↦ K χ t) (S t) := by
    obtain ⟨HpA, HpB⟩ := explicitFormula_real_shell τ _hτ f w hw Φ _hM (t / 2)
    obtain ⟨HmA, HmB⟩ := explicitFormula_real_shell τ _hτ f w hw Φ _hM (-(t / 2))
    have hP := (((HpA.add HpB).div_const 2).add
      (((HpA.sub HpB).mul_left ((Real.exp (-(t / 2)) : ℝ) : ℂ)).div_const 2)).mul_left
        ((Real.exp (-(t / 4)) : ℝ) : ℂ)
    have hN := (((HmA.add HmB).div_const 2).add
      (((HmA.sub HmB).mul_left ((Real.exp (-(t / 2)) : ℝ) : ℂ)).div_const 2)).mul_left
        ((Real.exp (-(t / 4)) : ℝ) : ℂ)
    have htot := (((h0.mul_left (2 * ((Real.exp (-t) : ℝ) : ℂ))).div_const (t : ℂ)).sub
      ((hP.add hN).div_const (1 - ((Real.exp (-t) : ℝ) : ℂ)))).mul_left (1 / 2 : ℂ)
    convert htot using 1
    swap
    · simp only [S, Q, gp, gm]
      ring
    funext χ
    have hp := explicitFormula_real_kernel_alg (P χ).1 (P χ).2 t
    have hm := explicitFormula_real_kernel_alg (-(P χ).1) (P χ).2 t
    have hcast : ((-(t / 2) : ℝ) : ℂ) = -((t / 2 : ℝ) : ℂ) := by push_cast; ring
    simp only [K, heckeArchimedeanDigammaKernel]
    rw [show (1 / 2 : ℝ) * t = t / 2 by ring,
      show (1 / 2 - (P χ).1 + ((P χ).2.val : ℂ)) / 2 = (1 / 2 + -(P χ).1 + ((P χ).2.val : ℂ)) / 2
        by ring, hp]
    simp only [hcast, mul_neg, neg_mul] at hm ⊢
    rw [hm]
    push_cast
    ring
  -- Termwise integration over the countably many characters with nonzero profile.
  have hzero (χ : chartChars(τ)) (hχ : ∀ q : ℚ, Φ χ q = 0) (t : ℝ) : K χ t = 0 := by
    have hΦ0 : (Φ χ : ℝ → ℂ) = 0 :=
      Continuous.ext_on Rat.denseRange_cast (Φ χ).continuous continuous_const
        (by rintro _ ⟨q, rfl⟩; exact hχ q)
    simp only [K, heckeArchimedeanDigammaKernel, hΦ0, Pi.zero_apply]
    ring
  let T : Set chartChars(τ) := ⋃ q : ℚ, Function.support (fun χ ↦ Φ χ q)
  have hT : T.Countable := by
    refine Set.countable_iUnion fun q ↦ ?_
    obtain ⟨H, -⟩ := explicitFormula_real_shell τ _hτ f w hw Φ _hM (q : ℝ)
    refine H.summable.countable_support.mono fun χ hχ ↦ ?_
    simp only [Function.mem_support] at hχ ⊢
    exact mul_ne_zero hχ (inv_ne_zero (Complex.exp_ne_zero _))
  have hoff (χ : chartChars(τ)) (hχ : χ ∉ T) (t : ℝ) : K χ t = 0 := by
    refine hzero χ (fun q ↦ ?_) t
    by_contra h
    exact hχ (Set.mem_iUnion.mpr ⟨q, h⟩)
  have hsuppI : Function.support (fun χ ↦ ∫ t in Ioi (0 : ℝ), K χ t) ⊆ T := by
    intro χ hχ
    by_contra h
    apply hχ
    simp only [hoff χ h, integral_zero]
  have : Countable T := hT.to_subtype
  have hI := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun χ : T ↦ K χ.val) (fun χ ↦ hKi χ.val)
    (hKs.comp_injective Subtype.val_injective)
  have hI' : HasSum (fun χ ↦ ∫ t in Ioi (0 : ℝ), K χ t) (∫ t in Ioi (0 : ℝ), S t) := by
    refine (hasSum_subtype_iff_of_support_subset hsuppI).mp ?_
    have hS : (∫ t in Ioi (0 : ℝ), S t) = ∫ t in Ioi (0 : ℝ), ∑' χ : T, K χ.val t := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ ?_)
      have hsupp : Function.support (fun χ ↦ K χ t) ⊆ T := by
        intro χ hχ
        by_contra h
        exact hχ (hoff χ h t)
      exact ((hasSum_subtype_iff_of_support_subset hsupp).mpr (hpt t)).tsum_eq.symm
    rw [hS]
    exact hI
  have htot := hI'.sub (h0.mul_left (Real.log Real.pi : ℂ))
  convert htot using 1
  funext χ
  exact dite_eq_left hw

/-- Cut off the comparison function at additive distance `ε` from zero. The negative
half contributes `-log ε` and the positive half contributes `log (1+ε) - log ε`. -/
private theorem idelicExplicitFormula_infiniteMatching_realLocal_cutoff {ε : ℝ}
    (hε : 0 < ε) (h₁ : ε ≤ 1) :
    let R (x : ℝ) := if 0 < x then (1 + x)⁻¹ else if -1 ≤ x then 1 else 0
    let A := {x : ℝ | ε ≤ |x|}
    IntegrableOn (fun x ↦ R x / |x|) A ∧
      (∫ x in A, R x / |x|) = Real.log (1 + ε) - 2 * Real.log ε := by
  intro R A
  let p (x : ℝ) := (1 + x)⁻¹ / x
  let n (x : ℝ) := x⁻¹
  have hd (x : ℝ) (hx : ε ≤ x) :
      HasDerivAt (fun y : ℝ ↦ -Real.log (1 + y⁻¹)) (p x) x := by
    have hx' : 0 < x := hε.trans_le hx
    convert (((hasDerivAt_inv hx'.ne').const_add 1).log (by positivity)).neg using 1
    dsimp [p]
    field_simp
    ring
  have hlim : Tendsto (fun y : ℝ ↦ -Real.log (1 + y⁻¹)) atTop (𝓝 0) := by
    simpa using (((Real.continuousAt_log one_ne_zero).tendsto.comp
      (show Tendsto (fun y : ℝ ↦ 1 + y⁻¹) atTop (𝓝 1) by
        simpa using tendsto_inv_atTop_zero.const_add (1 : ℝ))).neg)
  have hp := integrableOn_Ioi_deriv_of_nonneg' hd (fun x (hx : ε < x) ↦ by
    dsimp [p]
    have := hε.trans hx
    positivity) hlim
  have hpv := integral_Ioi_of_hasDerivAt_of_tendsto' hd hp hlim
  have hn : IntegrableOn n (Icc ε 1) :=
    (continuousOn_inv₀.mono (fun x (hx : x ∈ Icc ε (1 : ℝ)) ↦
      (hε.trans_le hx.1).ne')).integrableOn_compact isCompact_Icc
  let P := (Ici ε).indicator p
  let N := (Icc ε 1).indicator n
  have hP : Integrable P := (integrable_indicator_iff measurableSet_Ici).mpr
    ((integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr hp)
  have hN : Integrable N := (integrable_indicator_iff measurableSet_Icc).mpr hn
  have hA : MeasurableSet A := measurableSet_le measurable_const continuous_abs.measurable
  have he (x : ℝ) : A.indicator (fun y ↦ R y / |y|) x = P x + N (-x) := by
    rcases lt_or_ge 0 x with hx | hx
    · have hh : ¬ ε ≤ -x := by linarith
      simp [A, R, P, N, p, indicator, abs_of_pos hx, hx, hh]
    · have hh : ¬ ε ≤ x := by linarith
      have hiff : -x ≤ 1 ↔ -1 ≤ x := by constructor <;> intro h <;> linarith
      simp only [A, R, P, N, n, indicator, mem_ofPred_eq, abs_of_nonpos hx, mem_Ici, hh,
        ite_false, zero_add, mem_Icc, not_lt.mpr hx]
      by_cases h : ε ≤ -x <;> by_cases h' : -1 ≤ x <;>
        simp [h, hiff, h', one_div]
  rw [← integrable_indicator_iff hA, ← integral_indicator hA, funext he]
  refine ⟨hP.add hN.comp_neg, ?_⟩
  rw [integral_add hP hN.comp_neg, integral_neg_eq_self, show P = _ from rfl,
    show N = _ from rfl, integral_indicator measurableSet_Ici, integral_indicator measurableSet_Icc,
    integral_Ici_eq_integral_Ioi, hpv, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le h₁, show n = _ from rfl, integral_inv_of_pos hε one_pos]
  rw [show 1 + ε⁻¹ = (1 + ε) / ε by field_simp; ring,
    Real.log_div (by positivity) hε.ne', one_div, Real.log_inv]
  ring

/-- Folding both signs of the multiplicative group and both signs of its logarithmic
coordinate gives four evaluations of an absolutely integrable additive density. -/
private theorem idelicExplicitFormula_infiniteMatching_realLocal_fold (D : ℝ → ℂ)
    (hD : Integrable D) :
    let T (y : ℝ) := Real.exp y • (D (Real.exp y - 1) + D (-Real.exp y - 1))
    IntegrableOn (fun y ↦ T y + T (-y)) (Ioi 0) ∧
      (∫ y in Ioi 0, T y + T (-y)) = ∫ x, D x := by
  intro T
  let g (u : ℝ) := D (u - 1)
  have hg : Integrable g := hD.comp_sub_right 1
  have hT : Integrable T := (integrable_comp_exp (fun u ↦ g u + g (-u))).mpr
    (hg.add hg.comp_neg).integrableOn
  have fold (f : ℝ → ℂ) (hf : Integrable f) :
      (∫ y in Ioi 0, f y + f (-y)) = ∫ y, f y := by
    rw [integral_add hf.integrableOn hf.comp_neg.integrableOn, integral_comp_neg_Ioi, neg_zero,
      add_comm, intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn]
  refine ⟨hT.integrableOn.add hT.comp_neg.integrableOn, ?_⟩
  rw [fold T hT, show T = (fun y ↦ Real.exp y • (g (Real.exp y) + g (-Real.exp y))) from rfl,
    integral_comp_exp (fun u ↦ g u + g (-u)), fold g hg]
  exact integral_sub_right_eq_self D 1

/-- In the half-logarithmic coordinate the comparison function contributes the Gauss
kernel at one plus the Frullani difference for exponential scales two and one. -/
private theorem idelicExplicitFormula_infiniteMatching_realLocal_constant :
    let C (y : ℝ) := Real.exp (-2 * y) / y - Real.exp (-y) / (1 - Real.exp (-y))
    IntegrableOn C (Ioi 0) ∧ (∫ y in Ioi 0, C y) =
      -Real.eulerMascheroniConstant - Real.log 2 := by
  intro C
  obtain ⟨hF, hV⟩ := complexLogFourier_finitePart_frullani_exp (α := 2) (β := 1)
    (by norm_num) one_pos
  have he : C = fun y ↦ gaussDigammaKernel y + y⁻¹ * (Real.exp (-2 * y) - Real.exp (-1 * y)) := by
    funext y
    simp only [C, gaussDigammaKernel, neg_one_mul]
    ring
  rw [he, integral_add integrableOn_gaussDigammaKernel hF, integral_gaussDigammaKernel, hV,
    one_div, Real.log_inv]
  exact ⟨integrableOn_gaussDigammaKernel.add hF, by ring⟩

/-- Subtract the comparison function before removing the additive cutoff. The remainder
is bounded near zero by a first derivative of the Schwartz test. -/
private theorem idelicExplicitFormula_infiniteMatching_realLocal_remainder (s : 𝓢(ℝ, ℂ)) :
    let R (x : ℝ) := if 0 < x then (1 + x)⁻¹ else if -1 ≤ x then 1 else 0
    let D (x : ℝ) := (s x - s 0 * (R x : ℂ)) / ((|x| : ℝ) : ℂ)
    Integrable D ∧ Tendsto (fun ε : ℝ ↦
      (∫ x in {z : ℝ | ε ≤ |z|}, s x / ((|x| : ℝ) : ℂ)) + 2 * s 0 * (Real.log ε : ℂ))
      (𝓝[>] 0) (𝓝 (∫ x, D x)) := by
  intro R D
  let A (ε : ℝ) := {x : ℝ | ε ≤ |x|}
  have hA (ε : ℝ) : MeasurableSet (A ε) :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hR : Measurable R :=
    ((measurable_const.add measurable_id).inv.ite (measurableSet_lt measurable_const measurable_id)
      (measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const))
  have hDmeas : Measurable D :=
    (s.continuous.measurable.sub ((Complex.measurable_ofReal.comp hR).const_mul _)).div
      (Complex.measurable_ofReal.comp continuous_abs.measurable)
  have htail {ε : ℝ} (hε : 0 < ε) (h₁ : ε ≤ 1) :
      IntegrableOn D (A ε) := by
    have hi := (real_log_fourier_cutoff s).2.1 ε hε
    have hr := (idelicExplicitFormula_infiniteMatching_realLocal_cutoff hε h₁).1.ofReal.const_mul (s 0)
    refine (hi.sub hr).congr_fun (fun x _ ↦ ?_) (hA ε)
    change s x / _ - s 0 * ((R x / |x| : ℝ) : ℂ) = _
    simp only [D, Complex.ofReal_div, sub_div, mul_div_assoc]
  let C := SchwartzMap.seminorm ℝ 0 1 s
  have hlip (x : ℝ) : ‖s x - s 0‖ ≤ C * |x| := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := s) (s := univ) (C := C)
      (fun z _ ↦ s.differentiableAt) (fun z _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ x)
    · simpa [Real.norm_eq_abs] using h
    · rw [← norm_iteratedFDeriv_one]
      exact s.norm_iteratedFDeriv_le_seminorm ℝ 1 z
  have hbound (x : ℝ) (hx : |x| < 1 / 2) : |1 - R x| ≤ |x| := by
    by_cases hp : 0 < x
    · rw [show R x = (1 + x)⁻¹ from ite_eq_left hp, abs_of_pos hp,
        show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring, abs_of_nonneg (by positivity)]
      exact div_le_self hp.le (by linarith)
    · have hx' : -1 ≤ x := by linarith [(abs_lt.mp hx).1]
      simp [R, hp, hx']
  have hnear : IntegrableOn D (Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    refine (integrableOn_const (C := C + ‖s 0‖) measure_Ioo_lt_top.ne).mono'
      hDmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [D, C, add_nonneg (apply_nonneg _ _) (norm_nonneg _)]
    rw [show D x = (s x - s 0 + s 0 * ((1 - R x : ℝ) : ℂ)) / ((|x| : ℝ) : ℂ) by
        dsimp [D]; push_cast; ring, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs,
      div_le_iff₀ (abs_pos.mpr hx0), add_mul]
    refine (norm_add_le _ _).trans (add_le_add (hlip x) ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbound x (abs_lt.mpr hx)) (norm_nonneg _)
  have hu : A (1 / 2) ∪ Ioo (-(1 / 2 : ℝ)) (1 / 2) = univ := by
    ext x
    simp [A, ← abs_lt, le_or_gt]
  have hD : Integrable D := integrableOn_univ.mp
    (hu ▸ ((htail (ε := 1 / 2) (by norm_num) (by norm_num)).union hnear))
  refine ⟨hD, ?_⟩
  have hlim : Tendsto (fun ε ↦ ∫ x in A ε, D x) (𝓝[>] 0) (𝓝 (∫ x, D x)) := by
    simp_rw [← integral_indicator (hA _)]
    apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖D x‖)
      (.of_forall fun ε ↦ hD.aestronglyMeasurable.indicator (hA ε))
      (.of_forall fun _ ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _) hD.norm
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [hne] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (abs_pos.mpr hx))] with ε hε
    exact (indicator_of_mem (s := A ε) hε.le D).symm
  have hlog : Tendsto (fun ε : ℝ ↦ (Real.log (1 + ε) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ (Real.log (1 + ε) : ℂ)) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  apply (show Tendsto (fun ε ↦ (∫ x in A ε, D x) + s 0 * (Real.log (1 + ε) : ℂ)) _ _ by
    simpa using hlim.add (hlog.const_mul (s 0))).congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
    nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)] with ε (hε : 0 < ε) h₁
  obtain ⟨hr, hv⟩ := idelicExplicitFormula_infiniteMatching_realLocal_cutoff hε h₁.le
  have he (x : ℝ) : D x = s x / ((|x| : ℝ) : ℂ) - s 0 * ((R x / |x| : ℝ) : ℂ) := by
    simp only [D, Complex.ofReal_div, sub_div, mul_div_assoc]
  have hi := (real_log_fourier_cutoff s).2.1 ε hε
  have hr' : IntegrableOn (fun x ↦ s 0 * ((R x / |x| : ℝ) : ℂ)) (A ε) := hr.ofReal.const_mul _
  change (∫ x in A ε, D x) + _ = _
  simp_rw [he]
  rw [integral_sub hi hr', integral_const_mul, integral_complex_ofReal, hv]
  push_cast
  ring

/-- Express the weighted translate in a real coordinate, together with its additive
finite part. Multiplication by `exp (y / 2)` recovers either signed multiplicative test. -/
private theorem idelicExplicitFormula_infiniteMatching_realLocal_coordinate
    (w : InfinitePlace F) (hw : w.IsReal) (f : 𝒟(w.Completionˣ)) :
    let e := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
    ∃ s : 𝓢(ℝ, ℂ), s 0 = f.val 1 ∧
      (∀ u : ℝˣ, f.val (e u) = (Real.sqrt |(u : ℝ)| : ℂ) * s ((u : ℝ) - 1)) ∧
      Tendsto (fun ε : ℝ ↦ (∫ x in {z : ℝ | ε ≤ |z|}, s x / ((|x| : ℝ) : ℂ)) +
        2 * s 0 * (Real.log ε : ℂ)) (𝓝[>] 0)
        (𝓝 (2 * (infiniteConnesWeilPrincipalValue w f -
          ((Real.log (2 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * s 0))) := by
  intro e
  let : BorelSpace w.Completion := ⟨rfl⟩
  let A := (exists_infiniteWeilTestMap w).choose f
  let r := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  have hμ : ν∞(w) = (volume : Measure ℝ).map m := dite_eq_left hw
  have hm (x : ℝ) : r (m x) = x := r.apply_symm_apply x
  have hn (x : ℝ) : ‖m x‖ = |x| :=
    j.symm.isometry.norm_map_of_map_zero (map_zero r.symm) x
  obtain ⟨s, hs⟩ := realLogFourier_finitePart_realTest w hw A
  change ∀ x, addTest(A) x = s (r x) at hs
  have hval (u : ℝˣ) : f.val (e u) = (Real.sqrt |(u : ℝ)| : ℂ) * s ((u : ℝ) - 1) := by
    have hu : 1 + m ((u : ℝ) - 1) = (e u).val := by
      change 1 + r.symm ((u : ℝ) - 1) = r.symm (u : ℝ)
      rw [map_sub, map_one]; ring
    rw [← hm ((u : ℝ) - 1), ← hs, (exists_infiniteWeilTestMap w).choose_spec]
    change _ = _ * (Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
      (1 + m ((u : ℝ) - 1)) / _)
    rw [hu, Units.val_injective.extend_apply, hw.mult_eq_one]
    dsimp only
    rw [pow_one, show ‖(e u).val‖ = |(u : ℝ)| from hn _]
    field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (abs_pos.mpr u.ne_zero)).ne']
  have h0 : s 0 = f.val 1 := by simpa using (hval 1).symm
  refine ⟨s, h0, hval, ?_⟩
  have hlim := (realLogFourier_finitePart w hw A).2.2
  have hv := ((exists_infiniteConnesPrincipalValue w).choose_spec A).2
  change infiniteConnesWeilPrincipalValue w f = _ at hv
  simp only [hμ, hs] at hv
  rw [hv]
  simp only [hμ, setIntegral_map_equiv, preimage_ofPred_eq, hn, hs,
    hm, map_zero] at hlim
  push_cast
  convert hlim using 2
  ring

/-- At positive log-radius `y`, identify the two sign averages with the four
Jacobian-weighted evaluations of the additive remainder. -/
private theorem idelicExplicitFormula_infiniteMatching_realLocal_kernel (s : ℝ → ℂ)
    (gp gm : ℝ → ℂ)
    (hp : ∀ y, gp y = (Real.exp (y / 2) : ℂ) * s (Real.exp y - 1))
    (hm : ∀ y, gm y = (Real.exp (y / 2) : ℂ) * s (-Real.exp y - 1))
    {y : ℝ} (hy : 0 < y) :
    let R (x : ℝ) := if 0 < x then (1 + x)⁻¹ else if -1 ≤ x then 1 else 0
    let D (x : ℝ) := (s x - s 0 * (R x : ℂ)) / ((|x| : ℝ) : ℂ)
    let T (z : ℝ) := Real.exp z • (D (Real.exp z - 1) + D (-Real.exp z - 1))
    let Q (t z : ℝ) := (gp z + gm z) / 2 + (Real.exp (-(t / 2)) : ℂ) * (gp z - gm z) / 2
    let t := 2 * y
    2 * ((1 / 2 : ℂ) * (2 * (Real.exp (-t) : ℂ) * s 0 / (t : ℂ) -
        (Real.exp (-(t / 4)) : ℂ) * (Q t (t / 2) + Q t (-(t / 2))) / (1 - (Real.exp (-t) : ℂ)))) =
      ((Real.exp (-2 * y) / y - Real.exp (-y) / (1 - Real.exp (-y)) : ℝ) : ℂ) * s 0 -
        (T y + T (-y)) / 2 := by
  intro R D T Q t
  let b := Real.exp (y / 2)
  let u := Real.exp y
  let v := Real.exp (-y)
  have hu : 1 < u := Real.one_lt_exp_iff.mpr hy
  have hv : v < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hy)
  have hv₀ : 0 < v := Real.exp_pos _
  have hP : D (u - 1) = (s (u - 1) - s 0 * ((u⁻¹ : ℝ) : ℂ)) / ((u - 1 : ℝ) : ℂ) := by
    simp [D, R, sub_pos.mpr hu, abs_of_pos (sub_pos.mpr hu)]
  have hN (a : ℝ) (ha : 0 < a) : D (-a - 1) = s (-a - 1) / ((a + 1 : ℝ) : ℂ) := by
    have h₁ : -a - 1 < 0 := by linarith
    have h₂ : -a - 1 < -1 := by linarith
    simp [D, R, not_lt.mpr h₁.le, not_le.mpr h₂, abs_of_neg h₁, add_comm]
  have hV : D (v - 1) = (s (v - 1) - s 0) / ((1 - v : ℝ) : ℂ) := by
    have hv₁ : -1 ≤ v - 1 := by linarith
    simp [D, R, not_lt.mpr (sub_nonpos.mpr hv.le), hv₁, abs_of_neg (sub_neg.mpr hv)]
  have hub : u = b ^ 2 := by dsimp [u, b]; rw [← Real.exp_nat_mul]; congr 1; ring
  have hvu : v = u⁻¹ := Real.exp_neg _
  have hq : Real.exp (-t) = v ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; dsimp [t]; ring
  have hhalf : t / 2 = y := by dsimp [t]; ring
  have hquarter : Real.exp (-(t / 4)) = b⁻¹ := by
    rw [show t / 4 = y / 2 by dsimp [t]; ring, Real.exp_neg]
  have hbneg : Real.exp (-y / 2) = b⁻¹ := by rw [neg_div, Real.exp_neg]
  have hu₀ : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hb₀ : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have h₁ : (u : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hu.ne')
  have h₂ : (u : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : u + 1 ≠ 0)
  have h₃ : (u : ℂ) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by nlinarith : u ^ 2 ≠ 1))
  have h₂' : 1 + (u : ℂ) ≠ 0 := by rwa [add_comm]
  have hscale : -(2 : ℝ) * y = -t := by dsimp [t]; ring
  simp only [Q, T, hhalf, hquarter, hscale, hq, hp, hm, hbneg,
    show Real.exp (y / 2) = b from rfl, show Real.exp y = u from rfl,
    show Real.exp (-y) = v from rfl]
  change _ = _ - ((u • (D (u - 1) + D (-u - 1))) + v • (D (v - 1) + D (-v - 1))) / 2
  rw [hP, hV, hN u (Real.exp_pos _), hN v hv₀]
  -- Use `v = 1/u` and `b² = u` only in the scalar coefficients.
  generalize s (u - 1) = P
  generalize s (-u - 1) = N
  generalize s (v - 1) = p
  generalize s (-v - 1) = n
  simp only [hvu, t, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp [hu₀, hb₀, h₁, h₂, h₂', h₃, Complex.ofReal_ne_zero.mpr hy.ne']
  rw [hub]
  push_cast
  ring

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (local identity at a real place `w`).
For a test `f` on `F_w^× = ℝ^×`, with `g₊(y) = f(e^y)`, `g₋(y) = f(-e^y)` and `Q` as in
`idelicExplicitFormula_infiniteMatching_realCharacterSum`,
`∫_0^∞ ½ (2 e^{-t} f(1) / t - e^{-t/4} (Q(t/2) + Q(-t/2)) / (1 - e^{-t})) dt - log π · f(1)`
is minus the Connes–Weil principal value of `f` at `w`.

Computation. With `u = ±e^{∓t/2}` the second part of the integrand is
`½ f(u) |u|^{1/2} / |1 - u|` against `d^×u`, so the left side is
`-½ ∫ f(u) |u|^{1/2} / |1 - u| d^×u`, regularized at `u = 1` by `e^{-t}/t`, minus `log π f(1)`.
The principal value is `-∫ log|y| F̂(y) dy` with `F(x) = f(1 + x) / |1 + x|^{1/2}`, and
`realLogFourier_finitePart` (`𝓕 log|x| = -½ Pf(1/|x|) - (γ + log 2π) δ`) turns it into
`½ Pf∫ F(x) / |x| dx + (γ + log 2π) F(0)`, the same integral regularized by `2 F(0) log ε`.
The difference of the two regularizations cancels the constants exactly, so the sum is
zero (checked numerically to 30 digits on four tests with `f(1) ≠ 0`). -/
theorem idelicExplicitFormula_infiniteMatching_realLocal (w : InfinitePlace F) (hw : w.IsReal)
    (testI : 𝒟(w.Completionˣ)) :
    let e : ℝˣ →* w.Completionˣ :=
      Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
    let gp : ℝ → ℂ := fun y ↦ testI.val (e (Units.mk0 (Real.exp y) (Real.exp_pos y).ne'))
    let gm : ℝ → ℂ := fun y ↦ testI.val (e (-Units.mk0 (Real.exp y) (Real.exp_pos y).ne'))
    let Q : ℝ → ℝ → ℂ := fun t y ↦
      (gp y + gm y) / 2 + (Real.exp (-(t / 2)) : ℂ) * (gp y - gm y) / 2
    (∫ t in Ioi (0 : ℝ), (1 / 2 : ℂ) * (2 * (Real.exp (-t) : ℂ) * testI.val 1 / (t : ℂ) -
          (Real.exp (-(t / 4)) : ℂ) * (Q t (t / 2) + Q t (-(t / 2))) /
            (1 - (Real.exp (-t) : ℂ)))) -
        (Real.log Real.pi : ℂ) * testI.val 1 =
      -infiniteConnesWeilPrincipalValue w testI := by
  intro e gp gm Q
  obtain ⟨s, h0, hu, hPV⟩ := idelicExplicitFormula_infiniteMatching_realLocal_coordinate w hw testI
  let R (x : ℝ) := if 0 < x then (1 + x)⁻¹ else if -1 ≤ x then 1 else 0
  let D (x : ℝ) := (s x - s 0 * (R x : ℂ)) / ((|x| : ℝ) : ℂ)
  let T (y : ℝ) := Real.exp y • (D (Real.exp y - 1) + D (-Real.exp y - 1))
  let C (y : ℝ) := Real.exp (-2 * y) / y - Real.exp (-y) / (1 - Real.exp (-y))
  obtain ⟨hD, hlim⟩ := idelicExplicitFormula_infiniteMatching_realLocal_remainder s
  have hvalue := tendsto_nhds_unique hlim hPV
  change (∫ x, D x) = _ at hvalue
  obtain ⟨hT, hfold⟩ := idelicExplicitFormula_infiniteMatching_realLocal_fold D hD
  change IntegrableOn (fun y ↦ T y + T (-y)) (Ioi 0) at hT
  change (∫ y in Ioi 0, T y + T (-y)) = _ at hfold
  obtain ⟨hC, hconst⟩ := idelicExplicitFormula_infiniteMatching_realLocal_constant
  change (∫ y in Ioi 0, C y) = _ at hconst
  have hsqrt (y : ℝ) : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
    rw [show Real.exp y = Real.exp (y / 2) ^ 2 by rw [← Real.exp_nat_mul]; congr 1; ring,
      Real.sqrt_sq (Real.exp_pos _).le]
  have hp (y : ℝ) : gp y = (Real.exp (y / 2) : ℂ) * s (Real.exp y - 1) := by
    simpa only [gp, Units.val_mk0, abs_of_pos (Real.exp_pos _), hsqrt] using
      hu (Units.mk0 (Real.exp y) (Real.exp_pos y).ne')
  have hm (y : ℝ) : gm y = (Real.exp (y / 2) : ℂ) * s (-Real.exp y - 1) := by
    simpa only [gm, Units.val_neg, Units.val_mk0, abs_neg, abs_of_pos (Real.exp_pos _), hsqrt] using
      hu (-Units.mk0 (Real.exp y) (Real.exp_pos y).ne')
  let S (t : ℝ) := (1 / 2 : ℂ) * (2 * (Real.exp (-t) : ℂ) * s 0 / (t : ℂ) -
    (Real.exp (-(t / 4)) : ℂ) * (Q t (t / 2) + Q t (-(t / 2))) / (1 - (Real.exp (-t) : ℂ)))
  rw [← h0]
  change (∫ t in Ioi 0, S t) - _ = _
  have hscale : (∫ t in Ioi 0, S t) = ∫ y in Ioi 0, (2 : ℂ) * S (2 * y) := by
    rw [integral_const_mul (2 : ℂ) (fun y ↦ S (2 * y)),
      integral_comp_mul_left_Ioi S 0 (by norm_num : (0 : ℝ) < 2), mul_zero, Complex.real_smul]
    push_cast
    ring
  rw [hscale, setIntegral_congr_fun measurableSet_Ioi
      (fun y hy ↦ idelicExplicitFormula_infiniteMatching_realLocal_kernel s gp gm hp hm hy)]
  change (∫ y in Ioi 0, (C y : ℂ) * s 0 - (T y + T (-y)) / 2) - _ = _
  have hi : IntegrableOn (fun y ↦ (C y : ℂ) * s 0) (Ioi 0) := hC.ofReal.mul_const _
  rw [integral_sub hi (hT.div_const (2 : ℂ)), integral_mul_const,
    integral_complex_ofReal, integral_div, hconst, hfold, hvalue,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne']
  push_cast
  ring

/-- The idele classes are second countable as an open quotient of the ideles. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_secondCountable
    (F : Type*) [Field F] [NumberField F] : SecondCountableTopology C[F] := by
  let : SecondCountableTopology (AdeleRing (𝓞 F) F) := adeleGroupSecondCountable F
  let : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (IdeleGroup (𝓞 F) F) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact Topology.IsOpenQuotientMap.secondCountableTopology (ideleGroup_quotient.{_, 0} F).2.2.2.2.1

/-- Restriction embeds the chart characters in the countable dual of the compact metrizable
group of norm-one idele classes. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_countable
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) : Countable chartChars(τ) := by
  let J := (ideleClassNorm F).ker
  let := idelicExplicitFormula_infiniteMatching_complexCharacterSum_secondCountable F
  let : SecondCountableTopology J := TopologicalSpace.Subtype.secondCountableTopology _
  let : CompactSpace J := (ideleClassGroup_finiteness F).2.1
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual J) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap J Circle).secondCountableTopology
  let : Countable (PontryaginDual J) := countable_of_Lindelof_of_discrete
  let res (χ : chartChars(τ)) : PontryaginDual J :=
    PontryaginDual.map ⟨J.subtype, continuous_subtype_val⟩ χ.val
  apply Function.Injective.countable (f := res)
  exact fun χ ψ he ↦
    explicitFormula_chartChar_ext τ hτ χ ψ (fun u ↦ DFunLike.congr_fun he u)

/-- The norm and the inverse character of a complex local unit in log-polar coordinates. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_polar
    (w : InfinitePlace F) (hw : w.IsComplex) (y φ : ℝ) :
    let e := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
    let z : ℂ := y / 2 + φ * Complex.I
    let c := infiniteClassMap(w) (e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)))
    Real.log ((ideleClassNorm F c : ℝ≥0) : ℝ) = y ∧ ∀ χ : U[F],
      let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
      (χ c : ℂ)⁻¹ = Complex.exp (-p.1 * y) * Complex.exp (φ * Complex.I) ^ (-p.2) := by
  intro e z
  let u := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)
  let c := infiniteClassMap(w) (e u)
  have hz : ‖(u : ℂ)‖ = Real.exp (y / 2) := by
    change ‖Complex.exp _‖ = _
    simp [Complex.norm_exp, z, Complex.div_ofNat_re]
  have hr : ‖(u : ℂ)‖ ^ 2 = Real.exp y := by
    rw [hz, sq, ← Real.exp_add]
    congr 1
    ring
  have harg : (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = Complex.exp (φ * Complex.I) := by
    rw [hz, div_eq_iff (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
    change Complex.exp (_ + _) = _
    rw [Complex.exp_add, mul_comm, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hn : Real.log ((ideleClassNorm F c : ℝ≥0) : ℝ) = y := by
    rw [show ((ideleClassNorm F c : ℝ≥0) : ℝ) = ‖(u : ℂ)‖ ^ 2 by
      rw [ideleClassNorm_ofCompletion, hw.mult_eq_two]
      change ‖((e u : w.Completionˣ) : w.Completion)‖ ^ 2 = _
      congr 1
      let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
      change ‖j.symm (u : ℂ)‖ = ‖(u : ℂ)‖
      rw [← dist_zero_right, ← dist_zero_right (u : ℂ), ← j.symm.dist_eq _ 0,
        show j.symm 0 = 0 from map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm],
      hr, Real.log_exp]
  refine ⟨hn, fun χ ↦ ?_⟩
  let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
  have hp := (complexHeckeCharacter_parameters χ w hw).exists.choose_spec.2 u
  change (χ c : ℂ) * _ ^ (0 : ℂ) = _ at hp
  rw [Complex.cpow_zero, mul_one, hr, harg, explicitFormula_exp_cpow] at hp
  rw [hp, mul_inv, ← Complex.exp_neg, ← zpow_neg]
  simp only [neg_mul]

/-- The Fourier coefficients on all translates of the compact norm-one group have one
summable majorant. In the inverse Fourier integral for the full idele class group, a
coefficient selects a single fiber of restriction to the norm-one group. Translation only
changes the phase there. Summing these fibers gives Fourier inversion on the translate. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_translatedFourier
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) :
    (∃ B : chartChars(τ) → ℝ, Summable B ∧ ∀ χ (g : C[F]),
      ‖∫ u, f.val (g * (u : C[F])) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F‖
        ≤ B χ) ∧ ∀ g : C[F], HasSum (fun χ : chartChars(τ) ↦ (classVolume : ℂ)⁻¹ *
          ∫ u, f.val (g * (u : C[F])) * (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F)
          (f.val g) := by
  let := idelicExplicitFormula_infiniteMatching_complexCharacterSum_countable τ hτ
  let J := (ideleClassNorm F).ker
  let η := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let mJ : MeasurableSpace J := Subtype.instMeasurableSpace
  have : BorelSpace J := Subtype.borelSpace _
  let : η.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : IsFiniteMeasure η := ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  let := idelicExplicitFormula_infiniteMatching_complexCharacterSum_secondCountable F
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology U[F] :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C[F] Circle).secondCountableTopology
  let μ : Measure C[F] := Measure.haar
  let : MeasurableSpace U[F] := borel _
  let : BorelSpace U[F] := ⟨rfl⟩
  obtain ⟨ν, hν, -⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  let fS : SchwartzBruhat C[F] := ⟨_, explicitTest_mem_schwartz f⟩
  let W := lcaFourier μ fS
  have hinv (x : C[F]) := schwartzBruhat_inverse_integral μ ν hν fS x
  have hW : Integrable W ν := by simpa [W] using (hinv 1).1
  let res : U[F] → PontryaginDual J := PontryaginDual.map ⟨J.subtype, continuous_subtype_val⟩
  let S := fun (χ : chartChars(τ)) ↦ {ψ : U[F] | res ψ = (res χ.val)⁻¹}
  have hS (χ) : MeasurableSet (S χ) :=
    (isClosed_eq (PontryaginDual.map ⟨J.subtype, continuous_subtype_val⟩).continuous continuous_const).measurableSet
  have hdis : Pairwise (Disjoint on S) := by
    intro χ χ' h
    refine Set.disjoint_left.mpr fun _ h₁ h₂ ↦ h (explicitFormula_chartChar_ext τ hτ χ χ' ?_)
    exact fun u ↦ DFunLike.congr_fun (inv_injective (h₁.symm.trans h₂)) u
  let ev : U[F] × C[F] → Circle := fun x ↦ x.1 x.2
  have hev : Continuous ev := (continuous_eval (F := C(C[F], Circle))).comp
    (((ContinuousMonoidHom.isInducing_toContinuousMap C[F] Circle).continuous.comp
      continuous_fst).prodMk continuous_snd)
  have hEq (χ : chartChars(τ)) (g : C[F]) : (∫ u, f.val (g * (u : C[F])) * (χ.val (u : C[F]) : ℂ) ∂η) =
      (η.real univ : ℂ) * ∫ ψ in S χ, W ψ * (ψ g : ℂ) ∂ν := by
    let H := fun (u : J) (ψ : U[F]) ↦ W ψ * (ψ (g * (u : C[F])) : ℂ) * (χ.val (u : C[F]) : ℂ)
    have hH : Integrable (uncurry H) (η.prod ν) := by
      have hc : Continuous (fun z : J × U[F] ↦ (z.2 (g * (z.1 : C[F])) : ℂ)) :=
        continuous_subtype_val.comp (hev.comp (continuous_snd.prodMk
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))
      have hc' : Continuous (fun z : J × U[F] ↦ (χ.val (z.1 : C[F]) : ℂ)) :=
        continuous_subtype_val.comp (χ.val.continuous.comp (continuous_subtype_val.comp continuous_fst))
      apply (hW.norm.comp_snd η).mono' ((hW.1.comp_snd.mul hc.aestronglyMeasurable).mul hc'.aestronglyMeasurable)
      exact .of_forall fun z ↦ by simp
    have hinner (ψ : U[F]) : (∫ u, H u ψ ∂η) =
        (S χ).indicator (fun ψ : U[F] ↦ (η.real univ : ℂ) * (W ψ * (ψ g : ℂ))) ψ := by
      let δ := res ψ * res χ.val
      have hfun (u : J) : H u ψ = (W ψ * (ψ g : ℂ)) * (δ u : ℂ) := by
        simp only [H, map_mul, Circle.coe_mul]
        change _ = (W ψ * (ψ g : ℂ)) * ((ψ (u : C[F]) * χ.val (u : C[F]) : Circle) : ℂ)
        rw [Circle.coe_mul]
        ring
      simp_rw [hfun, integral_const_mul]
      by_cases hs : ψ ∈ S χ
      · have he : δ = 1 := by
          change res ψ * res χ.val = 1
          rw [show res ψ = _ from hs, inv_mul_cancel]
        rw [indicator_of_mem hs, he]
        simp [mul_comm]
      · have hn : δ ≠ 1 := fun h ↦ hs (eq_inv_of_mul_eq_one_left h)
        obtain ⟨u, hu⟩ : ∃ u : J, δ u ≠ 1 := by
          by_contra! h
          exact hn (DFunLike.ext _ _ h)
        rw [indicator_of_notMem hs, explicitFormula_integral_character_eq_zero η δ hu, mul_zero]
    calc
      _ = ∫ u, ∫ ψ, H u ψ ∂ν ∂η := by
        refine integral_congr_ae (.of_forall fun u ↦ ?_)
        change f.val (g * (u : C[F])) * _ = _
        rw [show f.val (g * (u : C[F])) = _ from (hinv _).2, ← integral_mul_const]
      _ = ∫ ψ, ∫ u, H u ψ ∂η ∂ν := integral_integral_swap hH
      _ = _ := by simp_rw [hinner]; rw [integral_indicator (hS _), integral_const_mul]
  constructor
  · refine ⟨fun χ ↦ η.real univ * ∫ ψ in S χ, ‖W ψ‖ ∂ν,
      (hasSum_integral_iUnion hS hdis hW.norm.integrableOn).summable.mul_left _, fun χ g ↦ ?_⟩
    rw [hEq, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
    apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
    apply (norm_integral_le_integral_norm _).trans_eq
    simp only [norm_mul, Circle.norm_coe, mul_one]
  · intro g
    have hcover : ⋃ χ, S χ = univ := by
      apply eq_univ_of_forall
      intro ψ
      obtain ⟨χ, he⟩ := explicitFormula_exists_chartChar τ hτ ψ⁻¹
      refine mem_iUnion.mpr ⟨χ, ?_⟩
      apply DFunLike.ext
      intro u
      change ψ (u : C[F]) = (χ.val (u : C[F]))⁻¹
      rw [he]
      exact (inv_inv _).symm
    have hsum := hasSum_integral_iUnion hS hdis (hinv g).1.integrableOn
    rw [hcover, setIntegral_univ, ← (hinv g).2] at hsum
    refine hsum.congr_fun fun χ ↦ ?_
    have hv : (η.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr <|
      ENNReal.toReal_ne_zero.mpr ⟨Measure.measure_univ_ne_zero.mpr (NeZero.ne η), measure_ne_top _ _⟩
    rw [hEq]
    exact inv_mul_cancel_left₀ hv _

/-- Translating the norm-one Fourier integral to the shell through `g` introduces the
inverse character at `g`. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_translate
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2))
    (χ : chartChars(τ)) (g : C[F]) (y : ℝ) (hy : Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) = y) :
    (classVolume : ℂ)⁻¹ * (∫ u, f.val (g * (u : C[F])) * (χ.val (u : C[F]) : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F) = Φ χ y * (χ.val g : ℂ)⁻¹ := by
  let J := (ideleClassNorm F).ker
  let η := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace C[F] := ⟨rfl⟩
  let mJ : MeasurableSpace J := Subtype.instMeasurableSpace
  have : BorelSpace J := Subtype.borelSpace _
  let : η.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let r := radialFlow(τ, y)
  have hn : ideleClassNorm F r = ideleClassNorm F g := by
    rw [show ideleClassNorm F r = _ from hτ _, ContinuousMulEquiv.symm_apply_eq]
    exact congrArg Multiplicative.ofAdd (hy.symm.trans (positiveRealLogEquiv_apply _).symm)
  let k : J := ⟨r⁻¹ * g, by rw [MonoidHom.mem_ker, map_mul, map_inv, hn, inv_mul_cancel]⟩
  let h := fun u : J ↦ f.val (r * (u : C[F])) * (χ.val (u : C[F]) : ℂ)
  have hk : χ.val (k : C[F]) = χ.val g := by
    change χ.val (r⁻¹ * g) = _
    rw [map_mul, map_inv, show χ.val r = 1 from χ.property _, inv_one, one_mul]
  rw [explicitFormula_profile_eq τ hτ f Φ hM, mul_assoc, ← integral_mul_const]
  congr 1
  calc
    _ = ∫ u : J, h (k * u) * (χ.val g : ℂ)⁻¹ ∂η := by
      refine integral_congr_ae (.of_forall fun u ↦ ?_)
      change f.val _ * _ = f.val (r * ((k : C[F]) * (u : C[F]))) *
        (χ.val ((k : C[F]) * (u : C[F])) : ℂ) * _
      rw [show r * ((k : C[F]) * (u : C[F])) = g * (u : C[F]) by
        change r * (r⁻¹ * g * (u : C[F])) = _
        group, map_mul, hk, Circle.coe_mul]
      field_simp
    _ = _ := integral_mul_left_eq_self (μ := η) (fun u ↦ h u * (χ.val g : ℂ)⁻¹) k

/-- A summable bound on the derivatives of norm-one coefficients translated along a flow. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_flow
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (b : Multiplicative ℝ →ₜ* C[F]) :
    let Q := fun (χ : chartChars(τ)) (y : ℝ) ↦ (classVolume : ℂ)⁻¹ *
      ∫ u, f.val (b (Multiplicative.ofAdd y) * (u : C[F])) * (χ.val (u : C[F]) : ℂ)
        ∂normOneIdeleClassTamagawaMeasure F
    ∃ B : chartChars(τ) → ℝ, Summable B ∧ ∀ χ y,
      HasDerivAt (Q χ) (deriv (Q χ) y) y ∧ ‖deriv (Q χ) y‖ ≤ B χ := by
  intro Q
  let df : 𝒟(C[F]) := ⟨_, explicitFormula_flowDeriv_mem b f⟩
  obtain ⟨M, hM, h⟩ := (idelicExplicitFormula_infiniteMatching_complexCharacterSum_translatedFourier τ hτ df).1
  refine ⟨_, hM.mul_left ‖(classVolume : ℂ)⁻¹‖, fun χ y ↦ ?_⟩
  have hd := (explicitFormula_radial_hasDerivAt b χ.val f y).const_mul (classVolume : ℂ)⁻¹
  refine ⟨hd.differentiableAt.hasDerivAt, ?_⟩
  rw [show deriv (Q χ) y = _ from hd.deriv, norm_mul]
  exact mul_le_mul_of_nonneg_left (h χ _) (norm_nonneg _)

/-- Fourier inversion on the complex circle of log norm `y`, in angular coordinates. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_shell
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (w : InfinitePlace F) (hw : w.IsComplex) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) (y φ : ℝ) :
    let e := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
    let z : ℂ := y / 2 + φ * Complex.I
    HasSum (fun χ : chartChars(τ) ↦
      let p := (complexHeckeCharacter_parameters χ.val w hw).exists.choose
      (Φ χ y * Complex.exp (-p.1 * y)) * Complex.exp (φ * Complex.I) ^ (-p.2))
      (f.val (infiniteClassMap(w) (e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z))))) := by
  intro e z
  let c := infiniteClassMap(w) (e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)))
  obtain ⟨hn, hχ⟩ := idelicExplicitFormula_infiniteMatching_complexCharacterSum_polar w hw y φ
  have H := (idelicExplicitFormula_infiniteMatching_complexCharacterSum_translatedFourier τ hτ f).2 c
  refine H.congr_fun fun χ ↦ ?_
  rw [idelicExplicitFormula_infiniteMatching_complexCharacterSum_translate τ hτ f Φ hM χ c y hn,
    hχ χ.val, mul_assoc]

/-- The Fourier moments of the complex-place angular denominator, by Cauchy's formula
at `r` applied to `z^k / (1 - r*z)`, and conjugation for negative indices. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_moment
    (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (n : ℤ) :
    (2 * Real.pi : ℂ)⁻¹ * (∫ φ in (0 : ℝ)..2 * Real.pi,
      Complex.exp (φ * Complex.I) ^ n / (‖1 - (r : ℂ) * Complex.exp (φ * Complex.I)‖ ^ 2 : ℝ)) =
        (r : ℂ) ^ n.natAbs / (1 - (r : ℂ) ^ 2) := by
  let E := fun φ : ℝ ↦ Complex.exp (φ * Complex.I)
  have hE (φ) : ‖E φ‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hden (z : ℂ) (hz : ‖z‖ ≤ 1) : 1 - (r : ℂ) * z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have H := congrArg norm h
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at H
    nlinarith
  let D := fun φ : ℝ ↦ (‖1 - (r : ℂ) * E φ‖ ^ 2 : ℝ)
  have hd (φ) : D φ ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hden _ (hE φ).le))
  have hd' (φ) : (D φ : ℂ) * E φ = (1 - (r : ℂ) * E φ) * (E φ - r) := by
    dsimp only [D]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp only [map_sub, map_one, map_mul, Complex.conj_ofReal, ← Complex.inv_eq_conj (hE φ)]
    field_simp [show E φ ≠ 0 from Complex.exp_ne_zero _]
  have hpos (k : ℕ) : (2 * Real.pi : ℂ)⁻¹ * (∫ φ in (0 : ℝ)..2 * Real.pi,
      E φ ^ k / (D φ : ℂ)) = (r : ℂ) ^ k / (1 - (r : ℂ) ^ 2) := by
    have hf : DifferentiableOn ℂ (fun z : ℂ ↦ z ^ k / (1 - (r : ℂ) * z))
        (Metric.closedBall 0 1) := by
      refine (differentiableOn_id.pow _).div (by fun_prop) fun z hz ↦ hden z ?_
      simpa using hz
    have hmem : (r : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr₁
    have H := hf.circleIntegral_sub_inv_smul hmem
    rw [circleIntegral] at H
    simp only [deriv_circleMap, circleMap, Complex.ofReal_one, one_mul, zero_add, smul_eq_mul] at H
    have ht (φ : ℝ) : E φ * Complex.I * ((E φ - r)⁻¹ * (E φ ^ k / (1 - (r : ℂ) * E φ))) =
        Complex.I * (E φ ^ k / (D φ : ℂ)) := by
      calc
        _ = Complex.I * E φ ^ k * (E φ / ((1 - (r : ℂ) * E φ) * (E φ - r))) := by
          simp only [div_eq_mul_inv, mul_inv]
          ring
        _ = _ := by
          rw [← hd']
          field_simp [Complex.ofReal_ne_zero.mpr (hd φ), show E φ ≠ 0 from Complex.exp_ne_zero _]
    change (∫ φ in (0 : ℝ)..2 * Real.pi, E φ * Complex.I *
      ((E φ - r)⁻¹ * (E φ ^ k / (1 - (r : ℂ) * E φ)))) = _ at H
    simp_rw [ht] at H
    rw [intervalIntegral.integral_const_mul] at H
    rw [← sq] at H
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero] at H ⊢
    linear_combination H
  rcases n with k | k
  · simpa [E, D] using hpos k
  · have hc : Continuous (fun φ ↦ E φ ^ (k + 1) / (D φ : ℂ)) := by
      apply Continuous.div (by dsimp [E]; fun_prop) (by dsimp [D, E]; fun_prop)
      exact fun φ ↦ Complex.ofReal_ne_zero.mpr (hd φ)
    have H := congrArg (starRingEnd ℂ) (hpos (k + 1))
    have hconj := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := volume) 0 (2 * Real.pi))
    change (∫ φ in (0 : ℝ)..2 * Real.pi, (starRingEnd ℂ) (E φ ^ (k + 1) / (D φ : ℂ))) =
      (starRingEnd ℂ) _ at hconj
    rw [map_mul, ← hconj] at H
    simp only [map_inv₀, map_mul, map_ofNat, Complex.conj_ofReal, map_div₀, map_pow, map_sub,
      map_one, ← Complex.inv_eq_conj (hE _), inv_pow] at H
    exact H

/-- Integrating an absolutely convergent angular Fourier series against the local kernel
multiplies its `n`-th coefficient by `r^|n| / (1-r²)`. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_average
    {ι : Type*} [Countable ι] (a : ι → ℂ) (n : ι → ℤ) (g : ℝ → ℂ) (r : ℝ) (hr : 0 < r) (hr₁ : r < 1)
    (hs : ∀ φ : ℝ, HasSum (fun i ↦ a i * Complex.exp (φ * Complex.I) ^ n i) (g φ)) :
    HasSum (fun i ↦ a i * ((r : ℂ) ^ (n i).natAbs / (1 - (r : ℂ) ^ 2)))
      ((2 * Real.pi : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi,
        g φ / (‖1 - (r : ℂ) * Complex.exp (φ * Complex.I)‖ ^ 2 : ℝ)) := by
  let E := fun φ : ℝ ↦ Complex.exp (φ * Complex.I)
  let D := fun φ : ℝ ↦ ‖1 - (r : ℂ) * E φ‖ ^ 2
  have ha : Summable a := by simpa using (hs 0).summable
  have hnorm (φ) : ‖(r : ℂ) * E φ‖ = r := by
    simp [E, abs_of_pos hr]
  have hD (φ) : (1 - r) ^ 2 ≤ D φ := by
    apply pow_le_pow_left₀ (by linarith)
    simpa only [norm_one, hnorm] using norm_sub_norm_le (1 : ℂ) ((r : ℂ) * E φ)
  have hd (φ) : 0 < D φ := (sq_pos_of_pos (sub_pos.mpr hr₁)).trans_le (hD φ)
  let v := fun (i : ι) φ ↦ a i * E φ ^ n i / (D φ : ℂ)
  have hcs : Summable (fun i : ι ↦ ‖a i‖ / (1 - r) ^ 2) :=
    ha.norm.div_const _
  have H := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := volume) (F := v)
    (fun i _ ↦ ‖a i‖ / (1 - r) ^ 2)
    (fun i ↦ ((continuous_const.mul ((by dsimp [E]; fun_prop : Continuous E).zpow₀ _
          (fun _ ↦ Or.inl (Complex.exp_ne_zero _)))).div
        (by dsimp [D, E]; fun_prop) (fun φ ↦ Complex.ofReal_ne_zero.mpr (hd φ).ne')).aestronglyMeasurable)
    (fun i ↦ .of_forall fun φ _ ↦ by
      dsimp only [v]
      rw [norm_div, norm_mul, norm_zpow, Complex.norm_exp_ofReal_mul_I, one_zpow, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd φ)]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos (sub_pos.mpr hr₁)) (hD φ))
    (.of_forall fun _ _ ↦ hcs) (intervalIntegrable_const)
    (.of_forall fun φ _ ↦ (hs φ).div_const (D φ : ℂ))
  refine (H.mul_left (2 * Real.pi : ℂ)⁻¹).congr_fun fun i ↦ ?_
  rw [← idelicExplicitFormula_infiniteMatching_complexCharacterSum_moment r hr hr₁ (n i)]
  dsimp only [v, E, D]
  rw [show (fun φ : ℝ ↦ a i * Complex.exp (φ * Complex.I) ^ n i /
      ((‖1 - (r : ℂ) * Complex.exp (φ * Complex.I)‖ ^ 2 : ℝ) : ℂ)) =
      (fun φ : ℝ ↦ a i * (Complex.exp (φ * Complex.I) ^ n i /
      ((‖1 - (r : ℂ) * Complex.exp (φ * Complex.I)‖ ^ 2 : ℝ) : ℂ))) from
        funext fun _ ↦ mul_div_assoc .., intervalIntegral.integral_const_mul]
  ring

/-- The exponential multipliers in the digamma kernel are the radial character and the
Poisson multiplier for its angular frequency. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_multiplier
    (a : ℂ) (k : ℕ) (t : ℝ) :
    Complex.exp (-(1 / 2 + a + (k : ℂ) / 2) * (t : ℂ)) =
      Complex.exp (-a * t) * (Real.exp (-(t / 2)) : ℂ) ^ k * (Real.exp (-(t / 2)) : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- Along the radial flow, the phase-corrected profiles have summably bounded slopes.
Differentiation along rotations bounds the angular frequency times the value at zero. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_profiles
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (w : InfinitePlace F) (hw : w.IsComplex) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    let p := fun (χ : chartChars(τ)) ↦ (complexHeckeCharacter_parameters χ.val w hw).exists.choose
    let Q := fun χ (y : ℝ) ↦ Φ χ y * Complex.exp (-(p χ).1 * y)
    ∃ B N : chartChars(τ) → ℝ, Summable B ∧ Summable N ∧ ∀ χ,
      0 ≤ B χ ∧ (∀ y, ‖Q χ y - Φ χ 0‖ ≤ B χ * |y|) ∧
        (p χ).2.natAbs * ‖Φ χ 0‖ ≤ N χ := by
  intro p Q
  let e := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
  let j : ℂˣ →ₜ* w.Completionˣ := ⟨e,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  let i : w.Completionˣ →ₜ* C[F] := ⟨infiniteClassMap(w), continuous_ideleClass_ofCompletion F w⟩
  let b (d : ℂ) : Multiplicative ℝ →ₜ* ℂˣ :=
    { toFun := fun x ↦ Units.mk0 (Complex.exp ((x.toAdd : ℂ) * d)) (Complex.exp_ne_zero _)
      map_one' := Units.ext (by simp)
      map_mul' := fun x y ↦ Units.ext (by simp [add_mul, Complex.exp_add])
      continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
        ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_toAdd).mul continuous_const))) }
  let path (d : ℂ) := i.comp (j.comp (b d))
  let V := fun d (χ : chartChars(τ)) (y : ℝ) ↦ (classVolume : ℂ)⁻¹ *
    ∫ u, f.val (path d (Multiplicative.ofAdd y) * (u : C[F])) * (χ.val (u : C[F]) : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F
  let avg (χ : chartChars(τ)) (z : ℂ) := (classVolume : ℂ)⁻¹ * ∫ u,
    f.val (infiniteClassMap(w) (e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z))) * (u : C[F])) *
      (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F
  have hV (y φ : ℝ) (χ : chartChars(τ)) : avg χ (y / 2 + φ * Complex.I) =
      Q χ y * Complex.exp (φ * Complex.I) ^ (-(p χ).2) := by
    obtain ⟨hn, hc⟩ := idelicExplicitFormula_infiniteMatching_complexCharacterSum_polar w hw y φ
    dsimp only [avg]
    rw [idelicExplicitFormula_infiniteMatching_complexCharacterSum_translate τ hτ f Φ hM χ _ y hn,
      hc χ.val, ← mul_assoc]
  have hR (χ) : V (1 / 2) χ = Q χ := by
    funext y
    change avg χ ((y : ℂ) * (1 / 2)) = Q χ y
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, Complex.exp_zero, one_zpow, mul_one,
      div_eq_mul_inv, one_mul] using hV y 0 χ
  have hI (χ) : V Complex.I χ = fun y : ℝ ↦ Φ χ 0 *
      Complex.exp (((( -(p χ).2 : ℤ) : ℂ) * Complex.I) * y) := by
    funext y
    change avg χ ((y : ℂ) * Complex.I) = _
    have h := hV 0 y χ
    simp only [Complex.ofReal_zero, zero_div, zero_add, Q, mul_zero, Complex.exp_zero, mul_one,
      ← Complex.exp_int_mul] at h
    rw [h]
    congr 2
    ring
  obtain ⟨B, hB, hR'⟩ := idelicExplicitFormula_infiniteMatching_complexCharacterSum_flow τ hτ f (path (1 / 2))
  obtain ⟨N, hN, hI'⟩ := idelicExplicitFormula_infiniteMatching_complexCharacterSum_flow τ hτ f (path Complex.I)
  change ∀ χ y, HasDerivAt (V _ χ) _ y ∧ ‖deriv (V _ χ) y‖ ≤ B χ at hR'
  change ∀ χ y, HasDerivAt (V _ χ) _ y ∧ ‖deriv (V _ χ) y‖ ≤ N χ at hI'
  refine ⟨B, N, hB, hN, fun χ ↦ ⟨(norm_nonneg _).trans (hR' χ 0).2, fun y ↦ ?_, ?_⟩⟩
  · have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun x _ ↦ (hR' χ x).1.differentiableAt) (fun x _ ↦ (hR' χ x).2)
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ y)
    simpa only [hR, Q, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      sub_zero, Real.norm_eq_abs] using h
  · let c : ℂ := ((-(p χ).2 : ℤ) : ℂ) * Complex.I
    have hder : HasDerivAt (V Complex.I χ) (Φ χ 0 * c) 0 := by
      rw [hI]
      simpa only [c, id_eq, Complex.ofReal_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, one_mul] using
        (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).cexp.const_mul (Φ χ 0))
    have h := (hI' χ 0).2
    rw [hder.deriv, norm_mul] at h
    simpa [c, norm_mul, Complex.norm_intCast, mul_comm] using h

/-- An integrable envelope for the two samples of a complex digamma kernel. Subtracting
the central value before estimating removes the singularity of `1 / (1 - exp (-t))`. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_estimate
    (t : ℝ) (ht : 0 < t) (k : ℕ) (b x y : ℂ) (B N : ℝ)
    (hx : ‖x - b‖ ≤ B * t) (hy : ‖y - b‖ ≤ B * t) (hk : k * ‖b‖ ≤ N) :
    let r := Real.exp (-(t / 2))
    ‖2 * (Real.exp (-t) : ℂ) * b / t -
      ((r : ℂ) * (r : ℂ) ^ k * (x + y)) / (1 - (Real.exp (-t) : ℂ))‖ ≤
      (3 * ‖b‖ + N + 2 * B) * ((1 + t) * r) := by
  intro r
  let d := 1 - Real.exp (-t)
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hr2 : Real.exp (-t) = r * r := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₁ : 1 - r ≤ t / 2 := by linarith [Real.add_one_le_exp (-(t / 2))]
  have h₂ : 1 - r ^ k ≤ k * t / 2 := by
    rw [show r ^ k = Real.exp ((k : ℝ) * (-(t / 2))) from (Real.exp_nat_mul _ _).symm]
    linarith [Real.add_one_le_exp ((k : ℝ) * (-(t / 2)))]
  have hrem := digamma_remainder_bounds ht
  change -1 ≤ 1 / t - 1 / d ∧ 1 / t - 1 / d ≤ 0 at hrem
  have htd : t / d ≤ 1 + t := by
    calc
      _ = t * (1 / d) := by ring
      _ ≤ t * (1 / t + 1) := mul_le_mul_of_nonneg_left (by linarith [hrem.1]) ht.le
      _ = _ := by field_simp
  have hbase : |Real.exp (-t) / t - r / d| ≤ r * (3 / 2) := by
    rw [hr2, show r * r / t - r / d = r * ((r - 1) / t + (1 / t - 1 / d)) by ring,
      abs_mul, abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left _ hr.le
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos ht, abs_of_nonpos (sub_nonpos.mpr hr₁), abs_of_nonpos hrem.2]
    have := (div_le_iff₀ ht).mpr (show -(r - 1) ≤ 1 / 2 * t by linarith)
    linarith [hrem.1]
  have hk₁ := pow_le_one₀ hr.le hr₁ (n := k)
  have herr (v : ℂ) (hv : ‖v - b‖ ≤ B * t) :
      ‖b - (r : ℂ) ^ k * v‖ ≤ (N / 2 + B) * t := by
    rw [show b - (r : ℂ) ^ k * v = ((1 - r ^ k : ℝ) : ℂ) * b + (r : ℂ) ^ k * (b - v) by
      push_cast; ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hk₁),
      norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, norm_sub_rev b]
    have hpow := mul_le_mul_of_nonneg_right hk₁ (norm_nonneg (v - b))
    have hcoef := mul_le_mul_of_nonneg_right h₂ (norm_nonneg b)
    nlinarith [mul_le_mul_of_nonneg_right hk ht.le]
  have hxy : ‖(b - (r : ℂ) ^ k * x) + (b - (r : ℂ) ^ k * y)‖ ≤ (N + 2 * B) * t :=
    (norm_add_le _ _).trans (by linarith [herr x hx, herr y hy])
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hx) ht
  have hN : 0 ≤ N := (mul_nonneg (Nat.cast_nonneg k) (norm_nonneg b)).trans hk
  have hdecomp : 2 * (Real.exp (-t) : ℂ) * b / t -
      (r : ℂ) * (r : ℂ) ^ k * (x + y) / (1 - (Real.exp (-t) : ℂ)) =
      ((Real.exp (-t) / t - r / d : ℝ) : ℂ) * (2 * b) +
        ((r / d : ℝ) : ℂ) * ((b - (r : ℂ) ^ k * x) + (b - (r : ℂ) ^ k * y)) := by
    dsimp only [d]
    push_cast
    ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
    abs_of_nonneg (div_nonneg hr.le hd.le)]
  calc
    _ ≤ (r * (3 / 2)) * (2 * ‖b‖) + r / d * ((N + 2 * B) * t) := by gcongr
    _ = 3 * ‖b‖ * r + (N + 2 * B) * r * (t / d) := by ring
    _ ≤ 3 * ‖b‖ * r + (N + 2 * B) * r * (1 + t) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg b) hr.le) ht.le]

/-- Absolute integrability of the complex digamma kernels, summed over the chart
characters. Their common radial envelope is `(1+t) exp(-t/2)`. -/
private theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum_domination (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (w : InfinitePlace F)
    (hw : w.IsComplex) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2))
    (h0 : Summable (fun χ ↦ ‖Φ χ 0‖)) :
    let K := fun (χ : chartChars(τ)) t ↦
      let p := (complexHeckeCharacter_parameters χ.val w hw).exists.choose
      heckeArchimedeanDigammaKernel 1 (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
        (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) (Φ χ) t
    (∀ χ, IntegrableOn (K χ) (Ioi 0)) ∧ Summable (fun χ ↦ ∫ t in Ioi (0 : ℝ), ‖K χ t‖) := by
  intro K
  let p := fun (χ : chartChars(τ)) ↦ (complexHeckeCharacter_parameters χ.val w hw).exists.choose
  let Q := fun (χ : chartChars(τ)) (y : ℝ) ↦ Φ χ y * Complex.exp (-(p χ).1 * y)
  obtain ⟨B, N, hB, hN, h⟩ := idelicExplicitFormula_infiniteMatching_complexCharacterSum_profiles
    τ _hτ f w hw Φ _hM
  let C := fun χ ↦ 3 * ‖Φ χ 0‖ + N χ + 2 * B χ
  have hC : Summable C := ((h0.mul_left 3).add hN).add (hB.mul_left 2)
  let E := fun t : ℝ ↦ (1 + t) * Real.exp (-(t / 2))
  have hE : IntegrableOn E (Ioi 0) := by
    have h₁ := integrableOn_exp_mul_Ioi (a := -(1/2 : ℝ)) (by norm_num) 0
    have h₂ := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1/2)
      (by norm_num) one_pos (by norm_num)
    convert h₁.add h₂ using 1
    funext t
    simp only [E, Pi.add_apply, Real.rpow_one, add_mul, one_mul, neg_mul]
    ring_nf
  have hbound (χ) (t : ℝ) (ht : 0 < t) : ‖K χ t‖ ≤ C χ * E t := by
    obtain ⟨_, hQ, hk⟩ := h χ
    have hxy := idelicExplicitFormula_infiniteMatching_complexCharacterSum_estimate t ht
      (p χ).2.natAbs (Φ χ 0) (Q χ t) (Q χ (-t)) (B χ) (N χ)
      (by simpa only [abs_of_pos ht] using hQ t)
      (by simpa only [abs_neg, abs_of_pos ht] using hQ (-t)) hk
    convert hxy using 2
    simp only [K, heckeArchimedeanDigammaKernel, Complex.ofReal_one, one_mul, Q,
      idelicExplicitFormula_infiniteMatching_complexCharacterSum_multiplier,
      show 1 / 2 - (p χ).1 = 1 / 2 + -(p χ).1 by ring, p, Complex.ofReal_neg, neg_neg,
      neg_mul_neg]
    ring
  have hi (χ) : IntegrableOn (K χ) (Ioi 0) := by
    apply (hE.const_mul (C χ)).mono' ?_
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht ↦ hbound χ t ht))
    apply Measurable.aestronglyMeasurable
    dsimp only [K, heckeArchimedeanDigammaKernel]
    fun_prop
  refine ⟨hi, (hC.mul_right (∫ t in Ioi (0 : ℝ), E t)).of_norm_bounded fun χ ↦ ?_⟩
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), ← integral_const_mul]
  exact integral_mono_ae (hi χ).norm (hE.const_mul _) <|
    (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht ↦ hbound χ t ht)

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (character sum at a complex place `w`).
Let `Φ_χ` be the radial profiles of a test `f`, as in `idelicExplicitFormula_finiteMatching`,
and write `g(z) = f(e^z)` for the test in logarithmic coordinates on `F_w^× = ℂ^×` (so
`|e^z|_w = e^{2 Re z}`). Summed over the characters trivial on the image of the norm section,
the archimedean digamma terms at `w` are
`∫_0^∞ (2 e^{-t} f(1) / t - A(t)) dt - 2 log 2π · f(1)` with the Poisson average
`A(t) = (2π)⁻¹ ∫_0^{2π} e^{-t/2} (g(t/2 + iφ) + g(-t/2 + iφ)) / |1 - e^{-t/2 + iφ}|² dφ`.

Computation. Write `χ_w(x) = (|x|²)^a (x/|x|)^n`. Fourier inversion on `C¹` (translated to the
norm shell) gives `∑_χ Φ_χ(t) χ(g)⁻¹ = f(g)` for `|g| = e^t`; `Φ_χ(±t) e^{∓at} =
Φ_χ(±t) χ_w(e^{±t/2})⁻¹`, and `r^{|n|}` with `r = e^{-t/2}` is the `n`-th Fourier coefficient
of the Poisson kernel `P_r(φ) = (1 - r²) / |1 - r e^{iφ}|²`, whose numerator cancels the
denominator `1 - e^{-t}` of the digamma kernel. The sums commute with the integrals because the
coefficients of `f` and of its derivatives along the archimedean flows are absolutely
summable (`idelicExplicitFormula_normOneFourier_summable`). -/
theorem idelicExplicitFormula_infiniteMatching_complexCharacterSum (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (w : InfinitePlace F)
    (hw : w.IsComplex) (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    let e : ℂˣ →* w.Completionˣ :=
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
    let g : ℂ → ℂ := fun z ↦
      f.val (infiniteClassMap(w) (e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z))))
    let A : ℝ → ℂ := fun t ↦ (2 * Real.pi : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi,
      (Real.exp (-(t / 2)) : ℂ) * (g (t / 2 + φ * Complex.I) + g (-(t / 2) + φ * Complex.I)) /
        ((‖1 - Complex.exp (-(t / 2) + φ * Complex.I)‖ ^ 2 : ℝ) : ℂ)
    HasSum (fun χ : chartChars(τ) ↦ explicitArchTerm(χ.val, w, Φ χ))
      ((∫ t in Ioi (0 : ℝ), (2 * (Real.exp (-t) : ℂ) * f.val 1 / (t : ℂ) - A t)) -
        2 * (Real.log (2 * Real.pi) : ℂ) * f.val 1) := by
  intro e g A
  let := idelicExplicitFormula_infiniteMatching_complexCharacterSum_countable τ _hτ
  let p := fun (χ : chartChars(τ)) ↦ (complexHeckeCharacter_parameters χ.val w hw).exists.choose
  let K := fun (χ : chartChars(τ)) ↦ heckeArchimedeanDigammaKernel 1
    (1 / 2 + (p χ).1 + ((p χ).2.natAbs : ℂ) / 2)
    (1 / 2 - (p χ).1 + ((p χ).2.natAbs : ℂ) / 2) (Φ χ)
  have h0 : HasSum (fun χ ↦ Φ χ 0) (f.val 1) := by
    simpa using idelicExplicitFormula_infiniteMatching_complexCharacterSum_shell τ _hτ f w hw Φ _hM 0 0
  have hpt (t : ℝ) (ht : 0 < t) :
      HasSum (fun χ ↦ K χ t) (2 * (Real.exp (-t) : ℂ) * f.val 1 / (t : ℂ) - A t) := by
    let r := Real.exp (-(t / 2))
    have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    let n := fun (χ : chartChars(τ)) ↦ -(p χ).2
    let a := fun (χ : chartChars(τ)) ↦ Φ χ t * Complex.exp (-(p χ).1 * t) +
      Φ χ (-t) * Complex.exp ((p χ).1 * t)
    let b := fun (φ : ℝ) ↦ g (t / 2 + φ * Complex.I) + g (-(t / 2) + φ * Complex.I)
    let D := fun (φ : ℝ) ↦ (‖1 - (r : ℂ) * Complex.exp (φ * Complex.I)‖ ^ 2 : ℝ)
    have h (φ : ℝ) := (idelicExplicitFormula_infiniteMatching_complexCharacterSum_shell
      τ _hτ f w hw Φ _hM t φ).add (idelicExplicitFormula_infiniteMatching_complexCharacterSum_shell
      τ _hτ f w hw Φ _hM (-t) φ)
    have hsum (φ : ℝ) : HasSum (fun χ ↦ a χ * Complex.exp (φ * Complex.I) ^ n χ) (b φ) := by
      simpa only [b, a, p, n, g, e, add_mul, Complex.ofReal_neg, neg_div, neg_mul_neg] using h φ
    have hA := (idelicExplicitFormula_infiniteMatching_complexCharacterSum_average
      a n b r (Real.exp_pos _) hr₁ hsum).mul_left (r : ℂ)
    have hr (φ : ℝ) : Complex.exp (-(t / 2 : ℂ) + φ * Complex.I) =
        (r : ℂ) * Complex.exp (φ * Complex.I) := by
      simp [r, Complex.exp_add, Complex.ofReal_exp]
    have hav : A t = (r : ℂ) * ((2 * Real.pi : ℂ)⁻¹ *
        ∫ φ in (0 : ℝ)..2 * Real.pi, b φ / (D φ : ℂ)) := by
      dsimp only [A]
      simp_rw [hr, mul_div_assoc]
      rw [intervalIntegral.integral_const_mul]
      change _ * ((r : ℂ) * _) = (r : ℂ) * (_ * _)
      ring
    rw [hav]
    have H := ((h0.mul_left (2 * (Real.exp (-t) : ℂ))).div_const (t : ℂ)).sub hA
    refine H.congr_fun fun χ ↦ ?_
    have hr2 : (r : ℂ) ^ 2 = (Real.exp (-t) : ℂ) := by
      rw [← Complex.ofReal_pow, sq, ← Real.exp_add]
      congr 2
      ring
    simp only [K, heckeArchimedeanDigammaKernel, Complex.ofReal_one, one_mul,
      idelicExplicitFormula_infiniteMatching_complexCharacterSum_multiplier (p χ).1,
      show 1 / 2 - (p χ).1 = 1 / 2 + -(p χ).1 by ring,
      idelicExplicitFormula_infiniteMatching_complexCharacterSum_multiplier (-(p χ).1),
      neg_neg, hr2, a, n, Int.natAbs_neg]
    dsimp only [r]
    ring
  have hdom := idelicExplicitFormula_infiniteMatching_complexCharacterSum_domination
    τ _hτ f w hw Φ _hM h0.summable.norm
  have hKi : ∀ χ, IntegrableOn (K χ) (Ioi 0) := hdom.1
  have hKs : Summable (fun χ ↦ ∫ t in Ioi (0 : ℝ), ‖K χ t‖) := hdom.2
  have hI := hasSum_integral_of_summable_integral_norm hKi hKs
  have hsum := hI.sub (h0.mul_left (2 * (Real.log (2 * Real.pi) : ℂ)))
  convert hsum using 1
  · funext χ
    exact dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  · congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ (hpt t ht).tsum_eq.symm)

/-- Fubini in polar coordinates, with the angle integrated over a full period. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_radii
    (H : ℂ → ℂ) (hm : Measurable H) (hi : Integrable H) :
    let J := fun r : ℝ ↦ r • ∫ φ in (0 : ℝ)..2 * Real.pi, H (circleMap 0 r φ)
    IntegrableOn J (Ioi 0) ∧ (∫ r in Ioi (0 : ℝ), J r) = ∫ u, H u := by
  let U := Ioo (-Real.pi) Real.pi
  let P (p : ℝ × ℝ) := p.1 • H (Complex.polarCoord.symm p)
  have hP : IntegrableOn P Complex.polarCoord.target := by
    refine ⟨measurable_fst.smul (hm.comp ?_) |>.aestronglyMeasurable, ?_⟩
    · change Measurable (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p)
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    · rw [hasFiniteIntegral_iff_eNorm]
      have hfin := hasFiniteIntegral_iff_eNorm.mp hi.hasFiniteIntegral
      rw [← Complex.lintegral_comp_polarCoord_symm] at hfin
      refine lt_of_le_of_lt (le_of_eq ?_) hfin
      apply setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
      intro p hp
      rw [Complex.polarCoord_target] at hp
      simp only [P, eNorm_smul, Real.eNorm_eq_ofReal (show 0 ≤ p.1 from hp.1.le), smul_eq_mul]
  have hP' : Integrable P ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict U)) := by
    rwa [Complex.polarCoord_target, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hP
  have hJ (r : ℝ) : (∫ φ in U, P (r, φ)) =
      r • ∫ φ in (0 : ℝ)..2 * Real.pi, H (circleMap 0 r φ) := by
    have hperiod : Periodic (fun φ ↦ H (circleMap 0 r φ)) (2 * Real.pi) :=
      fun φ ↦ congrArg H (periodic_circleMap 0 r φ)
    have hshift := hperiod.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      integral_Ioc_eq_integral_Ioo] at hshift
    simp only [P, Complex.polarCoord_symm_apply, integral_smul]
    congr 1
    rw [← hshift]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro φ _
    simp [circleMap, Complex.exp_mul_I]
  simp only [← hJ]
  refine ⟨hP'.integral_prod_left, ?_⟩
  rw [← integral_prod P hP', Measure.prod_restrict, ← Measure.volume_eq_prod,
    ← Complex.polarCoord_target]
  exact Complex.integral_comp_polarCoord_symm H

/-- Cauchy's integral formula evaluates the angular integral of one simple pole.
Parametrizing the contour supplies the numerator `z = (z - p) + p`. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_resolvent
    (r : ℝ) (hr : 0 < r) (p : ℂ) (hp : p ≠ 0) (hpr : ‖p‖ ≠ r) :
    (∫ φ in (0 : ℝ)..2 * Real.pi, (circleMap 0 r φ - p)⁻¹) =
      if ‖p‖ < r then 0 else -(2 * Real.pi : ℂ) / p := by
  have hne (φ : ℝ) : circleMap 0 r φ - p ≠ 0 := by
    intro h
    exact hpr (by rw [← sub_eq_zero.mp h, norm_circleMap_zero, abs_of_pos hr])
  let J := fun φ ↦ (circleMap 0 r φ - p)⁻¹
  have hi : IntervalIntegrable J volume 0 (2 * Real.pi) :=
    ((continuous_circleMap _ _ |>.sub continuous_const).inv₀ hne).intervalIntegrable ..
  have hcontour : (∮ z in C(0, r), (z - p)⁻¹) =
      Complex.I * ((2 * Real.pi : ℂ) + p * ∫ φ in (0 : ℝ)..2 * Real.pi, J φ) := by
    unfold circleIntegral
    simp only [deriv_circleMap, smul_eq_mul]
    calc
      _ = ∫ φ in (0 : ℝ)..2 * Real.pi, Complex.I * (1 + p * J φ) := by
        apply intervalIntegral.integral_congr
        intro φ _
        dsimp only [J]
        field_simp [hne φ]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          intervalIntegrable_const (hi.const_mul p), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp [Complex.real_smul]
  change (∫ φ in (0 : ℝ)..2 * Real.pi, J φ) = _
  split_ifs with h
  · rw [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.mpr h)] at hcontour
    apply mul_left_cancel₀ hp
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination -hcontour
  · have hdiff : DifferentiableOn ℂ (fun z : ℂ ↦ (z - p)⁻¹) (Metric.closedBall 0 r) := by
      refine (differentiableOn_id.sub_const p).inv ?_
      intro z hz hpz
      exact hpr (le_antisymm (sub_eq_zero.mp hpz ▸ mem_closedBall_zero_iff.mp hz) (le_of_not_gt h))
    rw [(hdiff.mono Metric.closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr.le] at hcontour
    apply (eq_div_iff hp).mpr
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination -hcontour

/-- The pole at `-1` is locally integrable, and the Cauchy reference divided by
the squared radius decays cubically at infinity. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_reference_integrable
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun x : ℂ ↦ (1 + x)⁻¹ / ((‖x‖ ^ 2 : ℝ) : ℂ)) {x | ε ≤ ‖x‖ ^ 2} := by
  let b := (Metric.ball (0 : ℂ) 4).indicator (fun x : ℂ ↦ ‖x‖⁻¹)
  have hib : Integrable b := (integrable_indicator_iff measurableSet_ball).mpr
    complexLogFourier_finitePart_inv_norm_ball
  have hit : Integrable (fun x : ℂ ↦ ((1 + ‖x‖) ^ 3)⁻¹) := by
    have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3) (by norm_num)
    refine h.congr (.of_forall fun x ↦ ?_)
    change (1 + ‖x‖) ^ (-(3 : ℝ)) = _
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
  refine (((hib.comp_add_left 1).const_mul ε⁻¹).add (hit.const_mul 16)).integrableOn.mono'
    (((measurable_const.add measurable_id).inv.div (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_const (measurable_norm.pow_const _))]
    with x (hx : ε ≤ ‖x‖ ^ 2)
  simp only [Pi.add_apply, norm_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have htail : 0 ≤ 16 * ((1 + ‖x‖) ^ 3)⁻¹ := by positivity
  by_cases h : ‖x‖ ≤ 2
  · have hh : 1 + x ∈ Metric.ball (0 : ℂ) 4 := by
      rw [mem_ball_zero_iff]
      linarith [norm_add_le (1 : ℂ) x, norm_one (α := ℂ)]
    rw [show b (1 + x) = ‖1 + x‖⁻¹ from indicator_of_mem hh _]
    refine (le_add_of_nonneg_right htail).trans' ?_
    rw [div_eq_mul_inv, mul_comm]
    gcongr
  · have h2 : 2 < ‖x‖ := lt_of_not_ge h
    have hb : 0 ≤ ε⁻¹ * b (1 + x) := mul_nonneg (inv_nonneg.mpr hε.le)
      (indicator_nonneg (fun z _ ↦ inv_nonneg.mpr (norm_nonneg z)) _)
    refine (le_add_of_nonneg_left hb).trans' ?_
    have ha : ‖x‖ ≤ 1 + ‖1 + x‖ := by
      simpa [add_comm] using norm_sub_le (1 + x) (1 : ℂ)
    have hn : 0 < ‖1 + x‖ := by linarith
    rw [← one_div, div_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    calc
      (1 + ‖x‖) ^ 3 ≤ (2 * ‖x‖) ^ 3 := by gcongr; linarith
      _ = 8 * ‖x‖ * ‖x‖ ^ 2 := by ring
      _ ≤ 16 * (‖1 + x‖ * ‖x‖ ^ 2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The angular mean of `1/(1+x)` vanishes outside the unit circle. Its
integral against the cut-off reciprocal squared radius is exactly `-π log ε`. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_reference_cut
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, (1 + x)⁻¹ / ((‖x‖ ^ 2 : ℝ) : ℂ)) =
      -(Real.pi : ℂ) * (Real.log ε : ℂ) := by
  let U := {x : ℂ | ε ≤ ‖x‖ ^ 2}
  have hU : MeasurableSet U := measurableSet_le measurable_const (measurable_norm.pow_const _)
  let H := U.indicator fun x : ℂ ↦ (1 + x)⁻¹ / ((‖x‖ ^ 2 : ℝ) : ℂ)
  have hm : Measurable H := Measurable.indicator (by fun_prop) hU
  have hi : Integrable H := (integrable_indicator_iff hU).mpr
    (idelicExplicitFormula_infiniteMatching_complexLocal_reference_integrable ε hε)
  obtain ⟨_, hrad⟩ := idelicExplicitFormula_infiniteMatching_complexLocal_radii H hm hi
  let s := Real.sqrt ε
  have hs : 0 < s := Real.sqrt_pos.mpr hε
  have hs1 : s < 1 := by simpa using (Real.sqrt_lt_sqrt hε.le hε1)
  let q := fun r : ℝ ↦ (2 * Real.pi : ℂ) * ((r⁻¹ : ℝ) : ℂ)
  rw [← integral_indicator hU]
  change (∫ x, H x) = _
  rw [← hrad]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Ico s 1).indicator q r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))]
        with r (hr : 0 < r) hr1
      have hn (φ : ℝ) : ‖circleMap 0 r φ‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr]
      have hmem (φ : ℝ) : circleMap 0 r φ ∈ U ↔ s ≤ r := by
        change ε ≤ ‖circleMap 0 r φ‖ ^ 2 ↔ s ≤ r
        rw [hn, Real.sqrt_le_iff]; simp [hr.le]
      by_cases hsr : s ≤ r
      · have hH (φ : ℝ) : H (circleMap 0 r φ) = (circleMap 0 r φ - (-1))⁻¹ / ((r ^ 2 : ℝ) : ℂ) := by
          simp [H, (hmem φ).mpr hsr, hn, add_comm]
        simp only [hH, intervalIntegral.integral_div, Complex.real_smul]
        have hres := idelicExplicitFormula_infiniteMatching_complexLocal_resolvent r hr (-1)
          (by norm_num) (by simpa using hr1.symm)
        rw [hres]; simp only [norm_neg, norm_one]
        rcases lt_or_gt_of_ne hr1 with h | h
        · rw [ite_eq_right h.not_gt, indicator_of_mem (show r ∈ Ico s 1 from ⟨hsr, h⟩)]
          dsimp [q]; push_cast; field_simp
        · rw [ite_eq_left h, indicator_of_notMem (show r ∉ Ico s 1 from fun h' ↦ h.asymm h'.2)]
          simp
      · have hH (φ : ℝ) : H (circleMap 0 r φ) = 0 := indicator_of_notMem (fun h ↦ hsr ((hmem φ).mp h)) _
        simp [hH, indicator_of_notMem (show r ∉ Ico s 1 from fun h ↦ hsr h.1)]
    _ = ∫ r in Ico s 1, q r := by
      rw [integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
        inter_eq_left.mpr (show Ico s 1 ⊆ Ioi 0 from fun _ h ↦ hs.trans_le h.1)]
    _ = _ := by
      rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs1.le]
      simp only [q, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
        integral_inv_of_pos hs zero_lt_one, one_div, Real.log_inv, s, Real.log_sqrt hε.le]
      push_cast
      ring

/-- Subtracting `S(0)/(1+x)` from the additive test gives an integrable remainder.
Its integral with respect to `2 dA` is the circular finite part. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_disc (S : 𝓢(ℂ, ℂ)) :
    let K := fun x : ℂ ↦ (S x - S 0 / (1 + x)) / ((‖x‖ ^ 2 : ℝ) : ℂ)
    Integrable K ∧ Tendsto (fun ε : ℝ ↦
      (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, S x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(2 • volume)) +
      ((2 * Real.pi : ℝ) : ℂ) * S 0 * (Real.log ε : ℂ))
      (𝓝[>] 0) (𝓝 (2 * ∫ x, K x)) := by
  intro K
  let N := fun x : ℂ ↦ S x - S 0 / (1 + x)
  let T := fun x : ℂ ↦ (1 + x)⁻¹ / ((‖x‖ ^ 2 : ℝ) : ℂ)
  let U := fun ε : ℝ ↦ {x : ℂ | ε ≤ ‖x‖ ^ 2}
  have hU (ε : ℝ) : MeasurableSet (U ε) := measurableSet_le measurable_const (measurable_norm.pow_const _)
  have hN : DifferentiableAt ℝ N 0 := by
    apply S.differentiableAt.sub
    fun_prop (disch := norm_num)
  obtain ⟨C, hC⟩ := hN.isBigO_sub.exists_pos
  have hnear : ∀ᶠ x in 𝓝 (0 : ℂ), ‖N x‖ ≤ C * ‖x‖ := by simpa [N] using hC.2.bound
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hm : Measurable K := (S.continuous.measurable.sub
    (measurable_const.div (measurable_const.add measurable_id))).div (by fun_prop)
  have hsmall : IntegrableOn K (Metric.ball 0 δ) := by
    refine (complexLogFourier_finitePart_inv_norm_ball.const_mul C).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae (Measure.ae_ne volume (0 : ℂ))]
      with x hx hx0
    change ‖N x / ((‖x‖ ^ 2 : ℝ) : ℂ)‖ ≤ _
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖N x‖ / ‖x‖ ^ 2 ≤ C * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact hball hx
      _ = _ := by field_simp [norm_ne_zero_iff.mpr hx0]
  have hK (x : ℂ) : K x = S x / ((‖x‖ ^ 2 : ℝ) : ℂ) - S 0 * T x := by
    dsimp only [K, T]
    ring
  have hi : Integrable K := by
    have hlarge : IntegrableOn K (U (δ ^ 2)) := by
      have hS : IntegrableOn (fun x : ℂ ↦ S x / ((‖x‖ ^ 2 : ℝ) : ℂ)) (U (δ ^ 2)) := by
        refine (S.integrable.norm.integrableOn.const_mul (δ ^ 2)⁻¹).mono'
          ((S.continuous.measurable.div (by fun_prop)).aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem (hU _)] with x (hx : δ ^ 2 ≤ ‖x‖ ^ 2)
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), div_eq_mul_inv, mul_comm]
        gcongr
      rw [show K = _ from funext hK]
      have hT := idelicExplicitFormula_infiniteMatching_complexLocal_reference_integrable _ (sq_pos_of_pos hδ)
      exact hS.sub (hT.const_mul _)
    apply integrableOn_univ.mp
    refine (integrableOn_union.mpr ⟨hsmall, hlarge⟩).mono_set fun x _ ↦ ?_
    by_cases h : ‖x‖ < δ
    · exact Or.inl (mem_ball_zero_iff.mpr h)
    · exact Or.inr (pow_le_pow_left₀ hδ.le (le_of_not_gt h) 2)
  refine ⟨hi, ?_⟩
  have hlim : Tendsto (fun ε ↦ ∫ x in U ε, K x) (𝓝[>] 0) (𝓝 (∫ x, K x)) := by
    simp_rw [← integral_indicator (hU _)]
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun ε ↦ hi.aestronglyMeasurable.indicator (hU ε))
      (.of_forall fun ε ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _) hi.norm ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (sq_pos_of_pos (norm_pos_iff.mpr hx))] with ε hε
    exact (indicator_of_mem (show x ∈ U ε from hε.2.le) _).symm
  refine (hlim.const_mul 2).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  have hT := idelicExplicitFormula_infiniteMatching_complexLocal_reference_integrable ε hε.1
  have hfull (x : ℂ) : S x / ((‖x‖ ^ 2 : ℝ) : ℂ) = K x + S 0 * T x := by rw [hK]; abel
  have hsc := idelicExplicitFormula_infiniteMatching_complexLocal_reference_cut ε hε.1 hε.2
  change (∫ x in U ε, T x) = _ at hsc
  simp only [hfull, ← show U ε = {x : ℂ | ε ≤ ‖x‖ ^ 2} from rfl]
  have hT' : IntegrableOn (fun x ↦ S 0 * T x) (U ε) := hT.const_mul _
  have htotal : IntegrableOn (fun x ↦ K x + S 0 * T x) (U ε) := hi.integrableOn.add hT'
  rw [show (2 • (volume : Measure ℂ)) = volume + volume from two_smul ℕ _,
    Measure.restrict_add, integral_add_measure htotal htotal,
    integral_add hi.integrableOn hT', integral_const_mul, hsc]
  push_cast
  ring

/-- Polar integration about `1 + x = 0`, pairing the two radii `exp (±t/2)`.
The factor of two comes from the change from log radius to log squared radius. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_polar
    (K : ℂ → ℂ) (hm : Measurable K) (hi : Integrable K) :
    let B := fun y : ℝ ↦ (Real.exp y : ℂ) ^ 2 * ∫ φ in (0 : ℝ)..2 * Real.pi,
      K (Complex.exp ((y : ℂ) + φ * Complex.I) - 1)
    IntegrableOn (fun t : ℝ ↦ B (t / 2) + B (-(t / 2))) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), B (t / 2) + B (-(t / 2))) = 2 * ∫ x, K x := by
  intro B
  let H := fun z : ℂ ↦ K (z - 1)
  obtain ⟨hiJ, hvJ⟩ := idelicExplicitFormula_infiniteMatching_complexLocal_radii H
    (hm.comp (measurable_id.sub_const _)) (hi.comp_sub_right 1)
  let J := fun r : ℝ ↦ r • ∫ φ in (0 : ℝ)..2 * Real.pi, H (circleMap 0 r φ)
  have hB : B = fun y ↦ Real.exp y • J (Real.exp y) := by
    funext y
    simp only [B, J, H, circleMap, zero_add, Complex.exp_add, Complex.ofReal_exp,
      Complex.real_smul, sq, mul_assoc]
  have hiB : Integrable B := hB ▸ (integrable_comp_exp J).mpr hiJ
  have hvB : (∫ y, B y) = ∫ x, K x := by
    rw [hB, integral_comp_exp J, hvJ, integral_sub_right_eq_self]
  let T := fun t : ℝ ↦ B (t / 2)
  have hiT : Integrable T := by
    simpa only [T, div_eq_inv_mul] using hiB.comp_mul_left' (inv_ne_zero two_ne_zero)
  refine ⟨hiT.integrableOn.add hiT.comp_neg.integrableOn |>.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi, ?_⟩
  · simp only [T, Pi.add_apply, neg_div]
  · change (∫ t in Ioi (0 : ℝ), T t + B (-(t / 2))) = _
    simp_rw [← neg_div]
    change (∫ t in Ioi (0 : ℝ), T t + T (-t)) = _
    rw [integral_add hiT.integrableOn hiT.comp_neg.integrableOn, integral_comp_neg_Ioi,
      neg_zero, add_comm, intervalIntegral.integral_Iic_add_Ioi hiT.integrableOn hiT.integrableOn]
    simp only [T, div_eq_inv_mul, Measure.integral_comp_mul_left, inv_inv, abs_of_pos (zero_lt_two : (0 : ℝ) < 2),
      Complex.real_smul, Complex.ofReal_ofNat, hvB]

/-- The first Fourier coefficient of the Poisson kernel from its two simple poles. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_poisson
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    let v := circleMap 0 1
    (∫ φ in (0 : ℝ)..2 * Real.pi, (v φ)⁻¹ / ((‖1 - (r : ℂ) * v φ‖ ^ 2 : ℝ) : ℂ)) =
      (2 * Real.pi : ℂ) * r / (1 - (r : ℂ) ^ 2) := by
  intro v
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hout : 1 < ‖(r : ℂ)⁻¹‖ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact one_lt_inv_iff₀.mpr ⟨hr, hr1⟩
  have hin : ‖(r : ℂ)‖ < 1 := by simpa [Real.norm_of_nonneg hr.le] using hr1
  have hv (φ : ℝ) : ‖v φ‖ = 1 := by simp [v]
  have hn (p : ℂ) (hp : ‖p‖ ≠ 1) (φ : ℝ) : v φ - p ≠ 0 :=
    fun h ↦ hp (sub_eq_zero.mp h ▸ hv φ)
  have hi (p : ℂ) (hp : ‖p‖ ≠ 1) :
      IntervalIntegrable (fun φ ↦ (v φ - p)⁻¹) volume 0 (2 * Real.pi) :=
    (((continuous_circleMap _ _).sub continuous_const).inv₀ (hn p hp)).intervalIntegrable ..
  have hsq : 1 - (r : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show 1 - r ^ 2 ≠ 0 by nlinarith [mul_pos (sub_pos.mpr hr1) (show 0 < 1 + r by positivity)])
  have he (φ : ℝ) : (v φ)⁻¹ / ((‖1 - (r : ℂ) * v φ‖ ^ 2 : ℝ) : ℂ) =
      ((v φ - r)⁻¹ - (v φ - (r : ℂ)⁻¹)⁻¹) / (1 - (r : ℂ) ^ 2) := by
    have hv0 : v φ ≠ 0 := norm_ne_zero_iff.mp ((hv φ).trans_ne one_ne_zero)
    have hconj : (starRingEnd ℂ) (v φ) = (v φ)⁻¹ := by
      apply mul_right_cancel₀ hv0
      rw [inv_mul_cancel₀ hv0]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hv φ]
      norm_num
    have h1 : 1 - (r : ℂ) * v φ ≠ 0 := by
      intro h
      apply hn _ hout.ne' φ
      apply sub_eq_zero.mpr
      apply mul_left_cancel₀ hr'
      rw [mul_inv_cancel₀ hr']
      exact (sub_eq_zero.mp h).symm
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sub, map_one, map_mul,
      Complex.conj_ofReal, hconj]
    rw [show 1 - (r : ℂ) * (v φ)⁻¹ = (v φ - r) / v φ by field_simp,
      show v φ - (r : ℂ)⁻¹ = -(1 - (r : ℂ) * v φ) / r by field_simp; ring]
    field_simp [hv0, hr', hsq, hn _ hin.ne φ, h1]
    ring_nf
    field_simp [h1]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hi _ hin.ne) (hi _ hout.ne'),
    idelicExplicitFormula_infiniteMatching_complexLocal_resolvent 1 one_pos _ hr' hin.ne,
    idelicExplicitFormula_infiniteMatching_complexLocal_resolvent 1 one_pos _ (inv_ne_zero hr') hout.ne']
  rw [ite_eq_left hin, ite_eq_right hout.not_gt, div_inv_eq_mul]
  ring

/-- The degree minus one circle character is the multiplicative test corresponding
to the additive Cauchy kernel. Its Poisson average at radius `r` is `r`. -/
private theorem idelicExplicitFormula_infiniteMatching_complexLocal_angular
    (S : 𝓢(ℂ, ℂ)) (g : ℂ → ℂ)
    (hg : ∀ z, g z = (‖Complex.exp z‖ : ℂ) * S (Complex.exp z - 1)) (t : ℝ) (ht : 0 < t) :
    let K := fun x : ℂ ↦ (S x - S 0 / (1 + x)) / ((‖x‖ ^ 2 : ℝ) : ℂ)
    let B := fun y : ℝ ↦ (Real.exp y : ℂ) ^ 2 * ∫ φ in (0 : ℝ)..2 * Real.pi,
      K (Complex.exp ((y : ℂ) + φ * Complex.I) - 1)
    let A := (2 * Real.pi : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi,
      (Real.exp (-(t / 2)) : ℂ) * (g (t / 2 + φ * Complex.I) + g (-(t / 2) + φ * Complex.I)) /
        ((‖1 - Complex.exp (-(t / 2) + φ * Complex.I)‖ ^ 2 : ℝ) : ℂ)
    A = (2 * Real.pi : ℂ)⁻¹ * (B (t / 2) + B (-(t / 2))) +
      2 * S 0 * (Real.exp (-t) : ℂ) / (1 - (Real.exp (-t) : ℂ)) := by
  intro K B A
  let y := t / 2
  let r := Real.exp (-y)
  let R := Real.exp y
  let v := circleMap 0 1
  let u := fun (a : ℝ) (φ : ℝ) ↦ (a : ℂ) * v φ
  let d := fun φ ↦ ((‖1 - u r φ‖ ^ 2 : ℝ) : ℂ)
  have hy : 0 < y := half_pos ht
  have hr : 0 < r := Real.exp_pos _
  have hR : 0 < R := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hy)
  have hR1 : 1 < R := Real.one_lt_exp_iff.mpr hy
  have hrR : (r : ℂ) * R = 1 := by
    exact_mod_cast (show r * R = 1 by simp [r, R, Real.exp_neg])
  have hv (φ : ℝ) : ‖v φ‖ = 1 := by simp [v]
  have hu (a : ℝ) (ha : 0 < a) (φ : ℝ) : ‖u a φ‖ = a := by
    simp [u, hv, Real.norm_of_nonneg ha.le]
  have hExp (s φ : ℝ) : Complex.exp ((s : ℂ) + φ * Complex.I) = u (Real.exp s) φ := by
    simp [u, v, circleMap, Complex.exp_add, Complex.ofReal_exp]
  have hne (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) (φ : ℝ) : u a φ - 1 ≠ 0 := by
    intro h
    exact ha1 ((hu a ha φ).symm.trans (by rw [sub_eq_zero.mp h, norm_one]))
  have hd (φ : ℝ) : d φ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (sub_ne_zero.mp (hne r hr hr1.ne φ)).symm))
  have hscale (φ : ℝ) : ((‖u R φ - 1‖ ^ 2 : ℝ) : ℂ) = (R : ℂ) ^ 2 * d φ := by
    have hc : v φ * (starRingEnd ℂ) (v φ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]; norm_num
    have he : u R φ - 1 = (R : ℂ) * v φ * (starRingEnd ℂ) (1 - u r φ) := by
      simp only [u, map_sub, map_one, map_mul, Complex.conj_ofReal]
      linear_combination (R : ℂ) * r * hc + hrR
    rw [he, norm_mul, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_of_nonneg hR.le,
      Complex.norm_conj, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
  have hki (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
      IntervalIntegrable (fun φ ↦ K (u a φ - 1)) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    have huc : Continuous (u a) := continuous_const.mul (continuous_circleMap _ _)
    have huv (φ : ℝ) : u a φ ≠ 0 := norm_ne_zero_iff.mp ((hu a ha φ).trans_ne ha.ne')
    simp only [K, add_sub_cancel]
    exact ((S.continuous.comp (huc.sub continuous_const)).sub (continuous_const.div huc huv)).div
      (by fun_prop) (fun φ ↦ Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hne a ha ha1 φ))))
  have hdcont : Continuous d := by
    dsimp [d, u, v]; fun_prop
  have hvi : IntervalIntegrable (fun φ ↦ (v φ)⁻¹ / d φ) volume 0 (2 * Real.pi) := by
    exact (((continuous_circleMap _ _).inv₀ (fun φ ↦ norm_ne_zero_iff.mp ((hv φ).trans_ne one_ne_zero))).div
      hdcont hd).intervalIntegrable ..
  let L := fun (a φ : ℝ) ↦ (a : ℂ) ^ 2 * K (u a φ - 1)
  have hiL (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
      IntervalIntegrable (L a) volume 0 (2 * Real.pi) := (hki a ha ha1).const_mul _
  have hpt (φ : ℝ) : (r : ℂ) * ((R : ℂ) * S (u R φ - 1) + (r : ℂ) * S (u r φ - 1)) / d φ =
      L R φ + L r φ + (2 * S 0 * r) * ((v φ)⁻¹ / d φ) := by
    dsimp only [L, K]
    rw [add_sub_cancel, add_sub_cancel, hscale, norm_sub_rev (u r φ) 1]
    change _ = _ * ((_ - S 0 / u R φ) / (_ * d φ)) +
      _ * ((_ - S 0 / u r φ) / d φ) + _
    have hv0 : v φ ≠ 0 := norm_ne_zero_iff.mp ((hv φ).trans_ne one_ne_zero)
    have hr' := Complex.ofReal_ne_zero.mpr hr.ne'
    dsimp only [u]
    rw [show (R : ℂ) = (r : ℂ)⁻¹ from by apply mul_left_cancel₀ hr'; rwa [mul_inv_cancel₀ hr']]
    field_simp [hd φ, hv0, hr']
    ring
  have haverage := idelicExplicitFormula_infiniteMatching_complexLocal_poisson r hr hr1
  change (∫ φ in (0 : ℝ)..2 * Real.pi, (v φ)⁻¹ / d φ) = _ at haverage
  have hb (s : ℝ) : B s = ∫ φ in (0 : ℝ)..2 * Real.pi, L (Real.exp s) φ := by
    simp only [B, L, hExp, intervalIntegral.integral_const_mul]
  have ht' : (Real.exp (-t) : ℂ) = (r : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    dsimp [y]
    ring
  have hform (s φ : ℝ) : g ((s : ℂ) + φ * Complex.I) =
      (Real.exp s : ℂ) * S (u (Real.exp s) φ - 1) := by rw [hg, hExp, hu _ (Real.exp_pos _) φ]
  change (2 * Real.pi : ℂ)⁻¹ * (∫ φ in (0 : ℝ)..2 * Real.pi, _) = _
  simp only [← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_div, ← Complex.ofReal_neg]
  simp only [hform, hExp]
  change (2 * Real.pi : ℂ)⁻¹ * (∫ φ in (0 : ℝ)..2 * Real.pi,
    (r : ℂ) * ((R : ℂ) * S (u R φ - 1) + (r : ℂ) * S (u r φ - 1)) / d φ) = _
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hiL R hR hR1.ne').add (hiL r hr hr1.ne)) (hvi.const_mul _),
    intervalIntegral.integral_add (hiL R hR hR1.ne') (hiL r hr hr1.ne),
    intervalIntegral.integral_const_mul (2 * S 0 * ↑r), haverage, hb, hb, ht']
  have hc : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp only [Complex.ofReal_ofNat]
  change _ = (2 * Real.pi : ℂ)⁻¹ * ((∫ φ in (0 : ℝ)..2 * Real.pi, L R φ) + (∫ φ in (0 : ℝ)..2 * Real.pi, L r φ)) + _
  field_simp [hc]

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (local identity at a complex place `w`).
For a test `f` on `F_w^× = ℂ^×`, with `g(z) = f(e^z)` and the Poisson average `A` as in
`idelicExplicitFormula_infiniteMatching_complexCharacterSum`,
`∫_0^∞ (2 e^{-t} f(1) / t - A(t)) dt - 2 log 2π · f(1)` is minus the Connes–Weil principal
value of `f` at `w`.

Computation. With `u = e^{∓t/2 + iφ}`, `A(t) dt` is `(2π)⁻¹ f(u) |u|_w^{1/2} / |1 - u|_w`
against `d^×u = 2 dA / |u|²` (`|u|_w = |u|²`), so the left side is
`-(2π)⁻¹ ∫ f(u) |u|_w^{1/2} / |1 - u|_w d^×u`, regularized at `u = 1` by `2 e^{-t}/t`, minus
`2 log 2π f(1)`. The principal value is `-∫ log|y|_w F̂(y) dν(y)` with
`F(x) = f(1 + x) / |1 + x|_w^{1/2}`, and `complexLogFourier_finitePart`
(`𝓕 log|x|² = -(1/π) Pf(1/|x|²) - 2(γ + log π) δ` for the self-dual measure `2 dA`) turns it
into `(2π)⁻¹ Pf∫ F(x) / |x|_w dν(x) + 2 (γ + log 2π) F(0)`. The two regularizations differ
exactly by the constants (the strip-minus-disc integral `∫ dA / r² = 2π log(δ/ε)` near
`u = 1`); checked numerically to 20 digits. -/
theorem idelicExplicitFormula_infiniteMatching_complexLocal (w : InfinitePlace F)
    (hw : w.IsComplex) (testI : 𝒟(w.Completionˣ)) :
    let e : ℂˣ →* w.Completionˣ :=
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
    let g : ℂ → ℂ := fun z ↦
      testI.val (e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)))
    let A : ℝ → ℂ := fun t ↦ (2 * Real.pi : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi,
      (Real.exp (-(t / 2)) : ℂ) * (g (t / 2 + φ * Complex.I) + g (-(t / 2) + φ * Complex.I)) /
        ((‖1 - Complex.exp (-(t / 2) + φ * Complex.I)‖ ^ 2 : ℝ) : ℂ)
    (∫ t in Ioi (0 : ℝ), (2 * (Real.exp (-t) : ℂ) * testI.val 1 / (t : ℂ) - A t)) -
        2 * (Real.log (2 * Real.pi) : ℂ) * testI.val 1 =
      -infiniteConnesWeilPrincipalValue w testI := by
  intro e g A
  let R := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let W := (exists_infiniteWeilTestMap w).choose testI
  obtain ⟨S, hS⟩ := complexModelSchwartz w hw W
  have hW (z : ℂ) :
      S z = Function.extend Units.val (testI.val : _ → ℂ) (fun _ ↦ 0) (R.symm (1 + z)) /
        (‖1 + z‖ : ℂ) := by
    rw [congrFun hS z, (exists_infiniteWeilTestMap w).choose_spec testI]
    dsimp only
    rw [map_add, map_one, hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _)]
    rw [show ‖1 + R.symm z‖ = ‖1 + z‖ by
      rw [← map_one R.symm, ← map_add]
      exact j.symm.isometry.norm_map_of_map_zero (map_zero R.symm) _]
  have h0 : S 0 = testI.val 1 := by
    rw [hW, add_zero, map_one, norm_one, Complex.ofReal_one, div_one, ← Units.val_one]
    exact Units.val_injective.extend_apply _ _ _
  have hg (z : ℂ) : g z = (‖Complex.exp z‖ : ℂ) * S (Complex.exp z - 1) := by
    let u := e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z))
    rw [hW, add_sub_cancel]
    change testI.val u = _ * (Function.extend Units.val _ _ u.val / _)
    rw [Units.val_injective.extend_apply]
    field_simp [norm_ne_zero_iff.mpr (Complex.exp_ne_zero z)]
  -- Both regularizations integrate the same remainder after the Cauchy kernel is removed.
  let K := fun x : ℂ ↦ (S x - S 0 / (1 + x)) / ((‖x‖ ^ 2 : ℝ) : ℂ)
  let B := fun y : ℝ ↦ (Real.exp y : ℂ) ^ 2 * ∫ φ in (0 : ℝ)..2 * Real.pi,
    K (Complex.exp ((y : ℂ) + φ * Complex.I) - 1)
  obtain ⟨hKi, hdisc⟩ := idelicExplicitFormula_infiniteMatching_complexLocal_disc S
  have hm : Measurable K := (S.continuous.measurable.sub
    (measurable_const.div (measurable_const.add measurable_id))).div (by fun_prop)
  obtain ⟨hBi, hpolar⟩ := idelicExplicitFormula_infiniteMatching_complexLocal_polar K hm hKi
  let c := (2 * Real.pi : ℂ)
  have hc : c ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let m : ℂ ≃ᵐ w.Completion := j.symm.toHomeomorph.toMeasurableEquiv
  have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (2 • (volume : Measure ℂ)).map m :=
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hn (z : ℂ) : ‖m z‖ = ‖z‖ := j.symm.isometry.norm_map_of_map_zero (map_zero R.symm) z
  have hval (z : ℂ) : W (Multiplicative.ofAdd (m z)) = S z := (congrFun hS z).symm
  have hval0 : W (Multiplicative.ofAdd 0) = S 0 := by
    rw [← hval, show m 0 = 0 from map_zero R.symm]
  have hF := (complexLogFourier_finitePart w hw W).2.2
  have hPV := ((exists_infiniteConnesPrincipalValue w).choose_spec W).2
  change infiniteConnesWeilPrincipalValue w testI = _ at hPV
  rw [← neg_eq_iff_eq_neg.mpr hPV] at hF
  dsimp only at hF
  rw [hval0, hμ] at hF
  simp only [setIntegral_map_equiv, preimage_ofPred_eq, hn, hval] at hF
  have hfinite := tendsto_nhds_unique hdisc hF
  -- The reference contribution is the unit-argument digamma integral.
  have hD := heckeArchimedeanDigammaKernel_one
  let D := heckeArchimedeanDigammaKernel 1 1 1 (fun _ ↦ 1)
  have hInt : (∫ t in Ioi (0 : ℝ), 2 * (Real.exp (-t) : ℂ) * testI.val 1 / (t : ℂ) - A t) =
      (∫ t in Ioi (0 : ℝ), D t * S 0 - c⁻¹ * (B (t / 2) + B (-(t / 2)))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hA := idelicExplicitFormula_infiniteMatching_complexLocal_angular S g hg t ht
    change A t = c⁻¹ * (B (t / 2) + B (-(t / 2))) + _ at hA
    dsimp only
    rw [hA, ← h0]
    simp only [D, heckeArchimedeanDigammaKernel, one_mul, neg_mul, ← Complex.ofReal_neg,
      ← Complex.ofReal_exp, Complex.ofReal_one]
    ring
  rw [hInt, integral_sub (hD.1.mul_const _) (hBi.const_mul _), integral_mul_const,
    integral_const_mul, hD.2, hpolar, ← h0]
  change 2 * (∫ x, K x) = -((2 * Real.pi : ℝ) : ℂ) * _ at hfinite
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat] at hfinite
  change 2 * (∫ x, K x) = -c * _ at hfinite
  rw [hfinite]
  push_cast
  field_simp [hc]
  ring

/-- Paper: Theorem B.4.4.7, pp. 625–626, footnote 27 (one infinite place `w`). Let `Φ_χ` be
the radial profiles of a test `f`, as in `idelicExplicitFormula_finiteMatching`. Summed over
the characters trivial on the image of the norm section, the archimedean digamma terms at `w`
of the explicit formula of Theorem B.4.2.2 for `Φ_χ` give minus the Connes–Weil principal
value at `w` of the restriction of `f`.

Computation. Write the radial characters as `χ_w(x) = |x|^{iθ} sgn(x)^ε` (real) or
`(|x|²)^{iθ} (x/|x|)^n` (complex). Fourier inversion on `C¹` (as for the finite places) turns
`e^{-εy}` into the sign average and `e^{-|n|t/2}` into the Poisson kernel, so the sum of the
digamma integrals is `-c_w ∫ f_w(u) |u|_w^{1/2} / |1 - u|_w d^×u` with `c_w = 1/2` (real) or
`1/(2π)` (complex), regularized at `u = 1` by the `e^{-t}/t` term. On the other side `infiniteConnesPrincipalValue`
is `-∫ log|y|_w · f̂`, and `𝓕(log|y|) = -½ Pf(1/|x|) - (γ + log 2π) δ` on `ℝ`,
`-(1/2π) Pf(1/|x|²) - (γ + log π) δ` on `ℝ²`. The constants `- log π` and `- 2 log 2π` cancel
the difference of the two regularizations exactly; checked numerically to 20–30 digits on
several tests with `f_w(1) ≠ 0` at a real and at a complex place. -/
theorem idelicExplicitFormula_infiniteMatching (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) (w : InfinitePlace F)
    (testI : 𝒟(w.Completionˣ)) (_hI : ∀ u, testI.val u = f.val (infiniteClassMap(w) u))
    (Φ : chartChars(τ) → 𝓢(ℝ, ℂ)) (_hΦ : ∀ χ, ExponentialDecay (Φ χ))
    (_hM : ∀ χ s, (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g
      ∂classMeasure) / (classVolume : ℂ) = logMellin (Φ χ) (s - 1 / 2)) :
    HasSum (fun χ : chartChars(τ) ↦ explicitArchTerm(χ.val, w, Φ χ))
      (-infiniteConnesWeilPrincipalValue w testI) := by
  by_cases hw : w.IsReal
  · have h1 := idelicExplicitFormula_infiniteMatching_realCharacterSum τ _hτ f w hw Φ _hΦ _hM
    have h2 := idelicExplicitFormula_infiniteMatching_realLocal w hw testI
    have h1' : testI.val 1 = f.val 1 := by rw [_hI, map_one]
    simp only [← _hI, ← h1'] at h1
    simp only at h2
    rwa [h2] at h1
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h1 := idelicExplicitFormula_infiniteMatching_complexCharacterSum τ _hτ f w hc Φ _hΦ _hM
    have h2 := idelicExplicitFormula_infiniteMatching_complexLocal w hc testI
    have h1' : testI.val 1 = f.val 1 := by rw [_hI, map_one]
    simp only [← _hI, ← h1'] at h1
    simp only at h2
    rwa [h2] at h1

/-- Paper: Theorem B.4.4.7, pp. 623–626. Assuming absolute convergence of the
zero sum at this test, the characterwise contour formulas and the finite and
archimedean matching identities give the normalized idelic formula. -/
theorem idelicExplicitFormula_pointwise_of_summable (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (hZ : Summable (fun z : chartZeros(τ) ↦ ‖zeroMultiplicity(z) *
      ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure‖))
    (testI : ∀ w : InfinitePlace F, 𝒟(w.Completionˣ))
    (_hI : ∀ w u, (testI w).val u = f.val (infiniteClassMap(w) u))
    (testF : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_hF : ∀ v u, (testF v).val u = f.val (finiteClassMap(v) u)) :
    HasSum (fun z : chartZeros(τ) ↦ zeroMultiplicity(z) / (classVolume : ℂ) *
        ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure)
      (((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ) -
        (∑ w, infiniteConnesWeilPrincipalValue w (testI w)) -
        ∑' v, finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 (testF v)) := by
  classical
  set V : ℂ := (classVolume : ℂ) with hV
  -- (a), (b): radial profiles whose Mellin transforms are the idelic Mellin integrals.
  have hprof : ∀ χ : chartChars(τ), ∃ Φ : 𝓢(ℝ, ℂ), ExponentialDecay Φ ∧ ∀ s : ℂ,
      (∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s, -1 / 2) g ∂classMeasure) / V =
        logMellin Φ (s - 1 / 2) := by
    intro χ
    obtain ⟨c, hc⟩ := idelicExplicitFormula_mellinMatching τ _hτ f χ.val χ.property
    obtain ⟨Φ, hΦ, hΦx⟩ := idelicExplicitFormula_radialProfile τ _hτ f χ.val c
    have hfun : (fun x ↦ c * ∫ u, f.val (radialFlow(τ, x) * (u : C[F])) *
        (χ.val (u : C[F]) : ℂ) ∂normOneIdeleClassTamagawaMeasure F) = (Φ : ℝ → ℂ) :=
      funext fun x ↦ (hΦx x).symm
    refine ⟨Φ, hΦ, fun s ↦ (hc s).trans ?_⟩
    rw [hfun]
  choose Φ hΦ hM using hprof
  -- (c), (d): the explicit formula of each character, restricted to its zeros.
  have hfiber : ∀ χ : chartChars(τ), HasSum
      (fun s : {s : ℂ // 0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ s} ↦
        (MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ s.val : ℂ) / V *
          ∫ g, classMellinIntegrand(f, ideleClassNormTwist χ.val s.val, -1 / 2) g ∂classMeasure)
      ((((heckeLogDiscriminantConductor χ.val : ℂ) * Φ χ 0 -
          ∑' j, explicitPrimeTerm(χ.val, Φ χ) j) + ∑ w, explicitArchTerm(χ.val, w, Φ χ)) +
        if χ.val = 1 then logMellin (Φ χ) (0 - 1 / 2) + logMellin (Φ χ) (1 - 1 / 2) else 0) := by
    intro χ
    obtain ⟨hL, hAgree⟩ := explicitFormulaCompletedHeckeL_spec χ.val
    have hE := hasSum_heckeExplicitFormula χ.val (Φ χ) (hΦ χ) _ hL hAgree
    set d := MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ with hd
    set g : ℂ → ℂ := fun ρ ↦ (d ρ : ℂ) * logMellin (Φ χ) (ρ - 1 / 2) with hg
    set P : ℂ := if χ.val = 1 then logMellin (Φ χ) (0 - 1 / 2) + logMellin (Φ χ) (1 - 1 / 2)
      else 0 with hP
    have hzero (ρ : ℂ) (h0 : ¬ 0 < d ρ) (hne : ¬ (χ.val = 1 ∧ (ρ = 0 ∨ ρ = 1))) : g ρ = 0 := by
      have : d ρ = 0 := by
        rcases lt_or_eq_of_le (not_lt.mp h0) with h | h
        · exact absurd (idelicExplicitFormula_chart_poles τ _hτ χ.val χ.property ρ h) hne
        · exact h
      simp [hg, this]
    have hcomp : HasSum ({ρ | 0 < d ρ}ᶜ.indicator g) (-P) := by
      by_cases h1 : χ.val = 1
      · obtain ⟨h0, h1'⟩ := idelicExplicitFormula_trivial_poles (F := F)
        rw [← h1] at h0 h1'
        have e0 : d 0 = -1 := h0
        have e1 : d 1 = -1 := h1'
        have heq : {ρ | 0 < d ρ}ᶜ.indicator g = fun ρ ↦
            (if ρ = 0 then -logMellin (Φ χ) (0 - 1 / 2) else 0) +
              (if ρ = 1 then -logMellin (Φ χ) (1 - 1 / 2) else 0) := by
          funext ρ
          by_cases hρ0 : ρ = 0
          · subst hρ0
            rw [Set.indicator_of_mem (by simp [e0])]
            simp [hg, e0]
          by_cases hρ1 : ρ = 1
          · subst hρ1
            rw [Set.indicator_of_mem (by simp [e1])]
            simp [hg, e1]
          simp only [hρ0, hρ1, if_false, add_zero]
          by_cases hpos : 0 < d ρ
          · exact Set.indicator_of_notMem (by simpa using hpos) _
          · rw [Set.indicator_of_mem (by simpa using hpos)]
            exact hzero ρ hpos (by tauto)
        rw [heq, hP, if_pos h1, neg_add]
        exact (hasSum_ite_eq 0 _).add (hasSum_ite_eq 1 _)
      · have heq : {ρ | 0 < d ρ}ᶜ.indicator g = fun _ ↦ 0 := by
          funext ρ
          by_cases hpos : 0 < d ρ
          · exact Set.indicator_of_notMem (by simpa using hpos) _
          · rw [Set.indicator_of_mem (by simpa using hpos)]
            exact hzero ρ hpos (by tauto)
        rw [heq, hP, if_neg h1, neg_zero]
        exact hasSum_zero
    have key : {ρ | 0 < d ρ}.indicator g = fun ρ ↦ g ρ - {ρ | 0 < d ρ}ᶜ.indicator g ρ := by
      funext ρ
      rw [eq_sub_iff_add_eq]
      exact congrFun (Set.indicator_self_add_compl {ρ | 0 < d ρ} g) ρ
    have hZ := hE.sub hcomp
    rw [← key, sub_neg_eq_add] at hZ
    have hsub := (hasSum_subtype_iff_indicator (s := {ρ | 0 < d ρ})).mpr hZ
    refine hsub.congr_fun fun s ↦ ?_
    change (d s.val : ℂ) / V * _ = (d s.val : ℂ) * logMellin (Φ χ) (s.val - 1 / 2)
    rw [← hM χ s.val]
    ring
  -- (e): sum over the characters.
  have hS : Summable (fun z : chartZeros(τ) ↦ zeroMultiplicity(z) / V *
      ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure) :=
    (hZ.of_norm.div_const V).congr fun z ↦ by ring
  let Pr : chartChars(τ) → ℂ → Prop := fun χ s ↦
    0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ.val) univ s
  let e := Equiv.subtypeProdEquivSigmaSubtype Pr
  have hsig := ((e.symm.hasSum_iff).mpr hS.hasSum).sigma hfiber
  -- (f) and the pole term.
  let χ₁ : chartChars(τ) := ⟨1, fun _ ↦ rfl⟩
  have hpole : HasSum (fun χ : chartChars(τ) ↦
      if χ.val = 1 then logMellin (Φ χ) (0 - 1 / 2) + logMellin (Φ χ) (1 - 1 / 2) else 0)
      (((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / V) := by
    have heq : (fun χ : chartChars(τ) ↦
        if χ.val = 1 then logMellin (Φ χ) (0 - 1 / 2) + logMellin (Φ χ) (1 - 1 / 2) else 0) =
        fun χ ↦ if χ = χ₁ then logMellin (Φ χ₁) (0 - 1 / 2) + logMellin (Φ χ₁) (1 - 1 / 2)
          else 0 := by
      funext χ
      by_cases h : χ = χ₁
      · subst h; simp [χ₁]
      · have h' : ¬ χ.val = 1 := fun h' ↦ h (Subtype.ext h')
        simp [h, h']
    rw [heq]
    convert hasSum_ite_eq χ₁ _ using 1
    rw [← hM χ₁ 0, ← hM χ₁ 1, add_div]
    have hw0 (g : C[F]) : classMellinIntegrand(f, ideleClassNormTwist (1 : U[F]) 0, -1 / 2) g =
        f.val g * classWeight(g, -1 / 2) := by
      change f.val g * ((1 : ℂ) * _ ^ (0 : ℂ)) * _ = _
      rw [Complex.cpow_zero, one_mul, mul_one]
    have hw1 (g : C[F]) : classMellinIntegrand(f, ideleClassNormTwist (1 : U[F]) 1, -1 / 2) g =
        f.val g * classWeight(g, 1 / 2) := by
      change f.val g * ideleClassNormTwist (1 : U[F]) 1 g * _ = _
      rw [ideleClassNormTwist_one_one, mul_assoc]
      congr 1
      have hpos : (((ideleClassNorm F g).val : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
      conv_lhs => arg 1; rw [← Complex.cpow_one (((ideleClassNorm F g).val : ℝ) : ℂ)]
      rw [← Complex.cpow_add _ _ hpos]
      norm_num
    simp only [χ₁, hw0, hw1]
  have hfin := idelicExplicitFormula_finiteMatching τ _hτ f testF _hF Φ hΦ hM
  have harch := hasSum_sum (s := Finset.univ) fun w _ ↦
    idelicExplicitFormula_infiniteMatching τ _hτ f w (testI w) (_hI w) Φ hΦ hM
  have htot := (hfin.add harch).add hpole
  have hval := hsig.unique htot
  rw [hS.hasSum_iff, hval, Finset.sum_neg_distrib]
  ring

/-- Paper: Theorem B.4.4.7, pp. 623–626. The pointwise idelic explicit formula: at every
test, the multiplicity-weighted Mellin values at the completed Hecke zeros sum to the pole
terms minus the archimedean and finite Connes–Weil principal values of the restricted tests. -/
theorem idelicExplicitFormula_pointwise (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F]))
    (testI : ∀ w : InfinitePlace F, 𝒟(w.Completionˣ))
    (_hI : ∀ w u, (testI w).val u = f.val (infiniteClassMap(w) u))
    (testF : ∀ v : Primes(F), 𝒟((v.adicCompletion F)ˣ))
    (_hF : ∀ v u, (testF v).val u = f.val (finiteClassMap(v) u)) :
    HasSum (fun z : chartZeros(τ) ↦ zeroMultiplicity(z) / (classVolume : ℂ) *
        ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure)
      (((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ) -
        (∑ w, infiniteConnesWeilPrincipalValue w (testI w)) -
        ∑' v, finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 (testF v)) :=
  idelicExplicitFormula_pointwise_of_summable τ _hτ f (idelicExplicitFormula_summable_spectral τ _hτ f)
    testI _hI testF _hF

/-- A bounded family of compactly supported tests has common compact support. If the
supports escape an exhaustion, weighted evaluations are pointwise bounded but unbounded on the family. -/
private theorem idelicExplicitFormula_hasSum_strongDual_commonSupport
    {E X : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] [TopologicalSpace X] (K : CompactExhaustion X)
    (ev : X → StrongDual ℂ E) (hs : ∀ f, ∃ n, ∀ x ∉ K n, ev x f = 0)
    (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) : ∃ n, ∀ f ∈ B, ∀ x ∉ K n, ev x f = 0 := by
  by_contra! h
  choose f hf x hx hne using h
  let D (n : ℕ) : StrongDual ℂ E := ((n : ℂ) / ev (x n) (f n)) • ev (x n)
  have hpt (g : E) : Tendsto (fun n ↦ D n g) atTop (𝓝 0) := by
    obtain ⟨k, hk⟩ := hs g
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    change 0 = _ * ev (x n) g
    rw [hk _ (fun hm ↦ hx n (K.subset hn hm)), mul_zero]
  have heq := (PolynormableSpace.banach_steinhaus (𝓕 := D)
    (fun g ↦ (hpt g).isVonNBounded_range ℂ)).equicontinuous (0 : E)
  have hU : {g : E | ∀ n, dist (D n 0) (D n g) < 1} ∈ 𝓝 0 :=
    Metric.equicontinuousAt_iff_right.mp heq 1 zero_lt_one
  obtain ⟨r, _, hr⟩ := (hB hU).exists_pos
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℂ r
  obtain ⟨n, hn⟩ := exists_nat_gt ‖c‖
  obtain ⟨g, hg, he⟩ := hr c hc.le (hf n)
  have hnorm : ‖D n g‖ ≤ 1 := by simpa only [map_zero, dist_zero_left] using (hg n).le
  have hDn : D n (f n) = (n : ℂ) := div_mul_cancel₀ _ (hne n)
  rw [← he, map_smul, smul_eq_mul] at hDn
  exact hn.not_ge (calc
    (n : ℝ) = ‖c * D n g‖ := by rw [hDn, Complex.norm_natCast]
    _ ≤ ‖c‖ := by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hnorm)

/-- The inclusion of idele class tests into the Schwartz–Bruhat space is continuous,
by the final topology of the fixed-support stages (AppD_SchwartzBruhat/Sec3b). -/
private theorem idelicExplicitFormula_hasSum_strongDual_inclusion [SecondCountableTopology C[F]] :
    ∃ J : 𝒟(C[F]) →L[ℂ] SchwartzBruhat C[F], ∀ f, (J f).val = f.val := by
  let G := C[F]
  let E := 𝒟(G)
  let J : E →ₗ[ℂ] SchwartzBruhat G := Submodule.inclusion
    (p := bruhatCompactSupportSubmodule G) (p' := schwartzBruhatSubmodule G)
    (fun f hf ↦ explicitTest_mem_schwartz (F := F) ⟨f, hf⟩)
  have hJ : Continuous J := by
    let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
        (C : TopologicalSpace.Compacts G), Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
    refine (PolynormableSpace.withSeminorms ℂ (SchwartzBruhat G)).continuous_of_continuous_comp J
      fun p ↦ (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
        (⟨p.val.comp J, ?_⟩ : P)
    intro a e C
    exact p.property.comp
      ((schwartzBruhatStage_isEmbedding a e).continuous.comp continuous_subtype_val)
  exact ⟨⟨J, hJ⟩, fun _ ↦ rfl⟩

/-- A bounded set of idele class tests lies in a compact subset of one fixed-support
elementary Schwartz stage, mapped continuously into the test space. -/
private theorem idelicExplicitFormula_hasSum_strongDual_compact
    [SecondCountableTopology C[F]] [BarrelledSpace ℂ (𝒟(C[F]))]
    (B : Set (𝒟(C[F]))) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ A : Set (𝒟(C[F])), IsCompact A ∧ B ⊆ A := by
  let G := C[F]
  let E := 𝒟(G)
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  obtain ⟨J, hJ⟩ := idelicExplicitFormula_hasSum_strongDual_inclusion (F := F)
  let ev (x : G) : StrongDual ℂ E :=
    ⟨(LinearMap.proj x).comp (bruhatCompactSupportSubmodule G).subtype,
      ((continuous_schwartzBruhat_eval_forEndpoints x).comp J.continuous).congr
        (fun f ↦ congrFun (hJ f) x)⟩
  let K := CompactExhaustion.choice G
  obtain ⟨n, hn⟩ := idelicExplicitFormula_hasSum_strongDual_commonSupport K ev (fun f ↦ by
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact f.property.2
    exact ⟨n, fun x hx ↦ show f.val x = 0 from
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hn h)⟩) B hB
  let C : TopologicalSpace.Compacts G := ⟨K n, K.isCompact n⟩
  obtain ⟨a, e, S, hS, hImage⟩ := schwartzBruhat_bounded_image_stage (G := G) (hB.image J)
  let X := bruhatCompactSupportStage a e C
  let i : X →ₗ[ℂ] E := bruhatCompactSupportStageInclusion a e C
  have hi : Continuous i := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp i
    fun p ↦ p.property a e C
  have hX : IsClosed (X : Set (SchwartzBruhatStage e)) := by
    simp only [X, bruhatCompactSupportStage, Submodule.coe_iInf]
    exact isClosed_iInter fun x ↦
      isClosed_singleton.preimage (continuous_schwartzBruhatStage_eval a e x.val)
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  let : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
  have hcomp : IsCompact (closure S) :=
    elementarySchwartz_isCompact_of_isClosed_isVonNBounded isClosed_closure hS.closure
  refine ⟨i '' (Subtype.val ⁻¹' closure S),
    (hX.isClosedEmbedding_subtypeVal.isCompact_preimage hcomp).image hi, ?_⟩
  intro f hf
  let j : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  have hfJ : J f ∈ j '' S := hImage.symm.subset (mem_image_of_mem J hf)
  obtain ⟨s, hs, he⟩ := hfJ
  have hval : schwartzBruhatStageRealization a e s = f.val :=
    (congrArg (fun g : SchwartzBruhat G ↦ g.val) he).trans (hJ f)
  have hmem : s ∈ X := (mem_bruhatCompactSupportStage_iff a e C s).mpr (by
    rw [hval]
    exact closure_minimal (fun x hx ↦ by_contra fun h ↦ hx (hn f hf x h)) C.isCompact.isClosed)
  exact ⟨⟨s, hmem⟩, subset_closure hs, Subtype.ext hval⟩

/-- Pointwise absolute summability bounds all finite partial sums. Banach–Steinhaus
gives equicontinuity, so these sums converge uniformly on every compact set. -/
private theorem idelicExplicitFormula_hasSum_strongDual_of_compact
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (hc : ∀ B : Set E, Bornology.IsVonNBounded ℂ B → ∃ K : Set E, IsCompact K ∧ B ⊆ K)
    (T : ι → StrongDual ℂ E) (hT : ∀ f, Summable (fun i ↦ ‖T i f‖)) :
    ∃ L : StrongDual ℂ E, (∀ f, HasSum (fun i ↦ T i f) (L f)) ∧ HasSum T L := by
  let P (s : Finset ι) : StrongDual ℂ E := ∑ i ∈ s, T i
  let v (f : E) := ∑' i, T i f
  have hlim : Tendsto (fun s f ↦ P s f) atTop (𝓝 v) := by
    apply tendsto_pi_nhds.mpr
    intro f
    simpa only [P, sum_apply, HasSum, SummationFilter.unconditional_filter] using
      (show HasSum (fun i ↦ T i f) (v f) from (hT f).of_norm.hasSum)
  have hb (f : E) : Bornology.IsVonNBounded ℂ (range fun s ↦ P s f) := by
    refine (NormedSpace.isVonNBounded_iff' ℂ).mpr ⟨∑' i, ‖T i f‖, ?_⟩
    rintro _ ⟨s, rfl⟩
    simpa only [P, sum_apply] using (norm_sum_le s (fun i ↦ T i f)).trans
      ((hT f).sum_le_tsum s (fun i _ ↦ norm_nonneg _))
  have he := (PolynormableSpace.banach_steinhaus hb).equicontinuous
  let L : StrongDual ℂ E := ⟨linearMapOfTendsto v (fun s ↦ (P s).toLinearMap) hlim,
    hlim.continuous_of_equicontinuous he⟩
  refine ⟨L, fun f ↦ (hT f).of_norm.hasSum, ?_⟩
  have hu := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi (𝔖 := {K : Set E | IsCompact K})
    (fun _ h ↦ h) sUnion_isCompact_eq_univ (fun K _ ↦ he.equicontinuousOn K) atTop v).mpr hlim
  apply (UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn (RingHom.id ℂ) ℂ
    {B : Set E | Bornology.IsVonNBounded ℂ B}).mpr
  intro B hB
  obtain ⟨K, hK, hBK⟩ := hc B hB
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hu K hK).mono hBK

/-- Paper: Theorem B.4.4.7, pp. 625–626, with Remark B.4.1.6. A family of distributions on
the idele class test space whose values are absolutely summable at every test has a
continuous pointwise sum, and converges to it in the strong dual: the test space is
barrelled and its bounded sets are precompact. -/
theorem idelicExplicitFormula_hasSum_strongDual {ι : Type*}
    (T : ι → StrongDual ℂ (𝒟(C[F]))) (_hT : ∀ f, Summable (fun i ↦ ‖T i f‖)) :
    ∃ T₀ : StrongDual ℂ (𝒟(C[F])), (∀ f, HasSum (fun i ↦ T i f) (T₀ f)) ∧ HasSum T T₀ := by
  let : SecondCountableTopology C[F] := by
    let : SecondCountableTopology (IdeleGroup (𝓞 F) F) := idele_secondCountable F
    exact inferInstanceAs
      (SecondCountableTopology (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  let E := 𝒟(C[F])
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  -- Restrict a lower semicontinuous seminorm to the Fréchet stages, as in
  -- IsLFSpace.barrelled in AppC_LCTVS/Sec1.
  let : BarrelledSpace ℂ E := by
    obtain ⟨_, S, _, hS, _, htop⟩ := bruhatCompactSupport_strictLF (G := C[F])
    refine ⟨fun p hp ↦ ?_⟩
    have hP : WithSeminorms
        (Subtype.val : {q : Seminorm ℂ E // ∀ k, Continuous (q ∘ (S k).subtype)} → _) := ⟨htop⟩
    apply hP.continuous_seminorm (i := ⟨p, ?_⟩)
    intro k
    let : BarrelledSpace ℂ (S k) := isFrechetTVS_barrelled (hS k)
    exact (p.comp (S k).subtype).continuous_of_lowerSemicontinuous (hp.comp continuous_subtype_val)
  exact idelicExplicitFormula_hasSum_strongDual_of_compact
    (idelicExplicitFormula_hasSum_strongDual_compact (F := F)) T _hT

/-- Paper: Theorem B.4.4.7, pp. 623–626. Absolute spectral convergence at every
test gives the distributional explicit formula and strong-dual convergence
of the spectral and finite-place series. -/
theorem idelicExplicitFormula_of_summable (τ : ℝ≥0ˣ →ₜ* C[F]) (_hτ : RightInverse τ (ideleClassNorm F))
    (hZ : ∀ f : 𝒟(C[F]), Summable (fun z : chartZeros(τ) ↦ ‖zeroMultiplicity(z) *
      ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure‖)) :
    ∃ (spectral : chartZeros(τ) → StrongDual ℂ (𝒟(C[F])))
      (poles : StrongDual ℂ (𝒟(C[F])))
      (arch : InfinitePlace F → StrongDual ℂ (𝒟(C[F])))
      (finite : Primes(F) → StrongDual ℂ (𝒟(C[F]))),
      (∀ z f, spectral z f = zeroMultiplicity(z) / (classVolume : ℂ) *
        ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure) ∧
      (∀ f, poles f =
        ((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ)) ∧
      (∀ w f, ∃ test : 𝒟(w.Completionˣ),
        (∀ u, test.val u = f.val (infiniteClassMap(w) u)) ∧
        arch w f = infiniteConnesWeilPrincipalValue w test) ∧
      (∀ v f, ∃ test : 𝒟((v.adicCompletion F)ˣ),
        (∀ u, test.val u = f.val (finiteClassMap(v) u)) ∧
        finite v f = finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 test) ∧
      (∀ f, Summable (fun z ↦ ‖spectral z f‖)) ∧
      (∀ f, (Function.support (fun v ↦ finite v f)).Finite) ∧
      Summable finite ∧
      HasSum spectral (poles - (∑ w, arch w) - (∑' v, finite v)) := by
  choose RF hRF using fun v : Primes(F) ↦ idelicExplicitFormula_finiteTestMap (F := F) v
  choose RI hRI using fun w : InfinitePlace F ↦ idelicExplicitFormula_infiniteTestMap (F := F) w
  have hwc (a : ℂ) : Continuous fun g : C[F] ↦ classWeight(g, a) :=
    (ideleClassNorm_cpow_properties (F := F) a).2.2
  choose Dz hDz using fun z : chartZeros(τ) ↦ idelicExplicitFormula_integralDistribution
    (fun g ↦ zeroCharacter(z) g * classWeight(g, -1 / 2))
    ((zeroCharacter(z)).continuous.mul (hwc _))
  obtain ⟨D₁, hD₁⟩ := idelicExplicitFormula_integralDistribution
    (fun g : C[F] ↦ classWeight(g, -1 / 2)) (hwc _)
  obtain ⟨D₂, hD₂⟩ := idelicExplicitFormula_integralDistribution
    (fun g : C[F] ↦ classWeight(g, 1 / 2)) (hwc _)
  let spectral : chartZeros(τ) → StrongDual ℂ (𝒟(C[F])) :=
    fun z ↦ (zeroMultiplicity(z) / (classVolume : ℂ)) • Dz z
  let poles : StrongDual ℂ (𝒟(C[F])) := (classVolume : ℂ)⁻¹ • (D₁ + D₂)
  let arch : InfinitePlace F → StrongDual ℂ (𝒟(C[F])) :=
    fun w ↦ (infiniteConnesWeilPrincipalValue w).comp (RI w)
  let finite : Primes(F) → StrongDual ℂ (𝒟(C[F])) :=
    fun v ↦ finiteWeilScale(v) • (finiteConnesWeilPrincipalValue v 1).comp (RF v)
  have hspec (z : chartZeros(τ)) (f : 𝒟(C[F])) : spectral z f = zeroMultiplicity(z) /
      (classVolume : ℂ) * ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure := by
    change (zeroMultiplicity(z) / (classVolume : ℂ)) * Dz z f = _
    rw [hDz]
    exact congrArg (zeroMultiplicity(z) / (classVolume : ℂ) * ·)
      (integral_congr_ae (ae_of_all _ fun g ↦ (mul_assoc _ _ _).symm))
  have hpoles (f : 𝒟(C[F])) : poles f =
      ((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
        (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ) := by
    change (classVolume : ℂ)⁻¹ * (D₁ f + D₂ f) = _
    rw [hD₁, hD₂]
    exact (div_eq_inv_mul _ _).symm
  have hfin (v : Primes(F)) (f : 𝒟(C[F])) :
      finite v f = finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 (RF v f) := rfl
  have hsupp (f : 𝒟(C[F])) : (Function.support (fun v ↦ finite v f)).Finite := by
    refine (idelicExplicitFormula_finite_support f (fun v ↦ RF v f) (fun v u ↦ hRF v f u)).subset
      fun v hv ↦ ?_
    intro h0
    apply hv
    show finite v f = 0
    rw [hfin, h0, mul_zero]
  have hsummable (f : 𝒟(C[F])) : Summable (fun z ↦ ‖spectral z f‖) := by
    refine ((hZ f).mul_left
      ‖(classVolume : ℂ)⁻¹‖).congr fun z ↦ ?_
    rw [hspec, ← norm_mul]
    congr 1
    ring
  obtain ⟨Tf, hTf, hTfsum⟩ := idelicExplicitFormula_hasSum_strongDual finite fun f ↦
    summable_of_ne_finset_zero (s := (hsupp f).toFinset) fun v hv ↦ by
      rw [Finite.mem_toFinset] at hv
      rw [Function.notMem_support.mp hv, norm_zero]
  obtain ⟨Ts, hTs, hTssum⟩ := idelicExplicitFormula_hasSum_strongDual spectral hsummable
  have hTfeq : (∑' v, finite v) = Tf := hTfsum.tsum_eq
  have hTseq : Ts = poles - (∑ w, arch w) - (∑' v, finite v) := by
    refine ContinuousLinearMap.ext fun f ↦ ?_
    have h := idelicExplicitFormula_pointwise_of_summable τ _hτ f (hZ f) (fun w ↦ RI w f) (fun w u ↦ hRI w f u)
      (fun v ↦ RF v f) (fun v u ↦ hRF v f u)
    have h' : HasSum (fun z ↦ spectral z f) (((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ) -
        (∑ w, infiniteConnesWeilPrincipalValue w (RI w f)) -
        ∑' v, finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 (RF v f)) := by
      refine h.congr_fun fun z ↦ ?_
      rw [hspec]
    rw [(hTs f).unique h', sub_apply, sub_apply, hpoles, sum_apply, hTfeq, ← (hTf f).tsum_eq]
    rfl
  refine ⟨spectral, poles, arch, finite, hspec, hpoles, fun w f ↦ ⟨RI w f, hRI w f, rfl⟩,
    fun v f ↦ ⟨RF v f, hRF v f, rfl⟩, hsummable, hsupp, hTfsum.summable, hTseq ▸ hTssum⟩

/-- Paper: Theorem B.4.4.7, pp. 623–626. The sum over completed Hecke zeros
equals the pole distributions minus the local principal value distributions.
The zero and finite-place series converge in the strong dual of the test space.
Deviation: A norm section indexes each quasi-character once, the signed formula
counts zero multiplicity, and the archimedean pairing already uses canonical
Haar normalization. -/
theorem idelicExplicitFormula (τ : ℝ≥0ˣ →ₜ* C[F]) (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ (spectral : chartZeros(τ) → StrongDual ℂ (𝒟(C[F])))
      (poles : StrongDual ℂ (𝒟(C[F])))
      (arch : InfinitePlace F → StrongDual ℂ (𝒟(C[F])))
      (finite : Primes(F) → StrongDual ℂ (𝒟(C[F]))),
      (∀ z f, spectral z f = zeroMultiplicity(z) / (classVolume : ℂ) *
        ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure) ∧
      (∀ f, poles f =
        ((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ)) ∧
      (∀ w f, ∃ test : 𝒟(w.Completionˣ),
        (∀ u, test.val u = f.val (infiniteClassMap(w) u)) ∧
        arch w f = infiniteConnesWeilPrincipalValue w test) ∧
      (∀ v f, ∃ test : 𝒟((v.adicCompletion F)ˣ),
        (∀ u, test.val u = f.val (finiteClassMap(v) u)) ∧
        finite v f = finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 test) ∧
      (∀ f, Summable (fun z ↦ ‖spectral z f‖)) ∧
      (∀ f, (Function.support (fun v ↦ finite v f)).Finite) ∧
      Summable finite ∧
      HasSum spectral (poles - (∑ w, arch w) - (∑' v, finite v)) :=
  idelicExplicitFormula_of_summable τ _hτ (idelicExplicitFormula_summable_spectral τ _hτ)

-- TODO(paper-gap): Discreteness in each component imposes no bound on
-- the number of points in consecutive height intervals, even for G = ℝ₊ˣ.
-- In (B.4.4.18), c(τ(t)) already equals t^s. Use this radial character once.

section BruhatMellinPolynomialCount

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Integrate a derivative along a one-parameter subgroup by first integrating its
translates over a unit time interval. Haar invariance cancels the two endpoints.
This is the σ-finite case of the argument in AppD §1c, `integral_orbit_derivative_zero`. -/
private theorem bruhatMellin_integral_orbitDeriv (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    (X : LCATopologicalLie G) {w v : G → ℂ} (hw : Integrable w μ) (hv : Integrable v μ)
    (hc : Continuous v)
    (hd : ∀ x, HasDerivAt (fun t : ℝ ↦ w (x * X (Multiplicative.ofAdd t))) (v x) 0) :
    ∫ x, v x ∂μ = 0 := by
  let γ (t : ℝ) := X (Multiplicative.ofAdd t)
  have hγ : Continuous γ := X.continuous.comp continuous_ofAdd
  let V (t : ℝ) (x : G) := v (x * γ t)
  have htime (x : G) (t : ℝ) : HasDerivAt (fun s ↦ w (x * γ s)) (V t x) t := by
    have h : HasDerivAt (fun s ↦ w ((x * γ t) * γ s)) (V t x) (t - t) := sub_self t ▸ hd _
    convert h.comp_sub_const t t using 1
    funext s
    simp only [γ, mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  have hFTC (x : G) : (∫ t in (0 : ℝ)..1, V t x) = w (x * γ 1) - w x := by
    simpa only [γ, ofAdd_zero, map_one, mul_one] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ htime x t)
        ((hc.comp (continuous_const.mul hγ)).intervalIntegrable (μ := volume) 0 1)
  have hV : Continuous (uncurry V) := hc.comp (continuous_snd.mul (hγ.comp continuous_fst))
  have hi : Integrable (uncurry V) ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) := by
    let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr (by simp)
    refine (integrable_prod_iff hV.aestronglyMeasurable).mpr ⟨.of_forall fun t ↦
      (measurePreserving_mul_right μ (γ t)).integrable_comp_of_integrable hv, ?_⟩
    have hnorm (t : ℝ) : (∫ x, ‖V t x‖ ∂μ) = ∫ x, ‖v x‖ ∂μ :=
      integral_mul_right_eq_self (fun x ↦ ‖v x‖) (γ t)
    simpa only [uncurry_apply_pair, hnorm] using
      (integrable_const (μ := volume.restrict (uIoc (0 : ℝ) 1)) (∫ x, ‖v x‖ ∂μ))
  have he := intervalIntegral_integral_swap hi
  simp_rw [hFTC] at he
  have hw' : Integrable (fun x ↦ w (x * γ 1)) μ :=
    (measurePreserving_mul_right μ (γ 1)).integrable_comp_of_integrable hw
  rw [integral_sub hw' hw, integral_mul_right_eq_self, sub_self] at he
  simpa [V, integral_mul_right_eq_self] using he

/-- A directional derivative is again a compactly supported test. Integration by parts
expresses its Mellin coefficient as the original coefficient times the negative character derivative. -/
private theorem bruhatMellin_directionalTest (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    (X : LCATopologicalLie G) (f : 𝒟(G)) (hf : Continuous f.val) :
    ∃ F : 𝒟(G), ∀ (c : QuasiCharacter G) (v : ℂ),
      HasDerivAt (fun t : ℝ ↦ c (X (Multiplicative.ofAdd t))) v 0 →
      (∫ x, F.val x * c x ∂μ) = -(v * ∫ x, f.val x * c x ∂μ) := by
  let D := bruhatDirectionalDeriv X f.val
  have h₁ := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1 1
  have hD : Continuous D := bruhatDirectionalDeriv_continuous X h₁
  have hK : HasCompactSupport D := by
    apply HasCompactSupport.of_support_subset_isCompact f.property.2
    intro x
    contrapose
    intro hx
    have hγ : Tendsto (fun t : ℝ ↦ x * X (Multiplicative.ofAdd t)) (𝓝 0) (𝓝 x) := by
      have h : Continuous (fun t : ℝ ↦ x * X (Multiplicative.ofAdd t)) :=
        continuous_const.mul (X.continuous.comp continuous_ofAdd)
      simpa using h.tendsto 0
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto hγ
    rw [notMem_support]
    simpa [D, bruhatDirectionalDeriv, comp_def] using hz.deriv_eq
  refine ⟨⟨D, bruhatDirectionalDeriv_mem_smooth X ⟨_, f.property.1⟩, hK⟩, ?_⟩
  intro c v hc
  have hi : Integrable (fun x ↦ f.val x * c x) μ :=
    (hf.mul c.continuous).integrable_of_hasCompactSupport f.property.2.mul_right
  have hi' : Integrable (fun x ↦ D x * c x) μ :=
    (hD.mul c.continuous).integrable_of_hasCompactSupport hK.mul_right
  have he := bruhatMellin_integral_orbitDeriv μ X
    (v := fun x ↦ D x * c x + v * (f.val x * c x)) hi (hi'.add (hi.const_mul v))
    ((hD.mul c.continuous).add (continuous_const.mul (hf.mul c.continuous))) (fun x ↦ by
      have h := (hasDerivAt_bruhatDirectionalDeriv X h₁ x).fun_mul (hc.const_mul (c x))
      simp only [ofAdd_zero, map_one, mul_one] at h
      simpa only [map_mul, D, mul_left_comm, mul_comm, mul_assoc] using h)
  rw [integral_add hi' (hi.const_mul v), integral_const_mul] at he
  exact eq_neg_of_add_eq_zero_left he

/-- If one of finitely many directional multipliers dominates the height, one more
integration by parts gains one power of the height, uniformly over all the characters. -/
private theorem bruhatMellin_decay_of_directions {Z ι : Type*} [Finite ι]
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] (c : Z → QuasiCharacter G)
    (W : G → ℝ) (hW : Continuous W) (hbound : ∀ z x, ‖c z x‖ ≤ W x)
    (hcont : ∀ f : 𝒟(G), Continuous f.val)
    (X : ι → LCATopologicalLie G) (v : ι → Z → ℂ)
    (hd : ∀ i z, HasDerivAt (fun t : ℝ ↦ c z (X i (Multiplicative.ofAdd t))) (v i z) 0)
    (H : Z → ℝ) (hH : ∀ z, 0 ≤ H z) (hcoord : ∀ z, ∃ i, H z ≤ ‖v i z‖)
    (N : ℕ) (f : 𝒟(G)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z, ‖∫ x, f.val x * c z x ∂μ‖ ≤ K / (1 + H z) ^ N := by
  let M (φ : 𝒟(G)) (z : Z) := ‖∫ x, φ.val x * c z x ∂μ‖
  suffices ∀ φ : 𝒟(G), ∃ B : ℝ, ∀ z, M φ z * (1 + H z) ^ N ≤ B by
    obtain ⟨B, hB⟩ := this f
    exact ⟨max 1 B, zero_lt_one.trans_le (le_max_left ..), fun z ↦
      (le_div_iff₀ (pow_pos (by linarith [hH z]) N)).mpr ((hB z).trans (le_max_right ..))⟩
  induction N with
  | zero =>
    intro φ
    refine ⟨∫ x, ‖φ.val x‖ * W x ∂μ, fun z ↦ ?_⟩
    simp only [pow_zero, mul_one, M]
    apply norm_integral_le_of_norm_le (((hcont φ).norm.mul hW).integrable_of_hasCompactSupport
      φ.property.2.norm.mul_right)
    exact .of_forall fun x ↦ (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left (hbound z x) (norm_nonneg _))
  | succ n ih =>
    intro φ
    choose D hD using fun i ↦ bruhatMellin_directionalTest μ (X i) φ (hcont φ)
    choose B hB using fun i ↦ ih (D i)
    obtain ⟨C, hC⟩ := Finite.exists_le B
    obtain ⟨B₀, h₀⟩ := ih φ
    refine ⟨B₀ + C, fun z ↦ ?_⟩
    obtain ⟨i, hi⟩ := hcoord z
    have hmul : ‖v i z‖ * M φ z = M (D i) z := by
      simp only [M, hD i (c z) _ (hd i z), norm_neg, norm_mul]
    have hgain : H z * M φ z ≤ M (D i) z :=
      (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans_eq hmul
    calc M φ z * (1 + H z) ^ (n + 1)
        = M φ z * (1 + H z) ^ n + (H z * M φ z) * (1 + H z) ^ n := by ring
      _ ≤ B₀ + C := add_le_add (h₀ z)
        ((mul_le_mul_of_nonneg_right hgain (pow_nonneg (by linarith [hH z]) n)).trans
          ((hB i z).trans (hC i)))

end

section

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] {d : ℕ}
local notation "P" => ℝ≥0ˣ × (Fin d → Circle) × A
local notation "Z" => ℂ × (Fin d → ℤ) × PontryaginDual A
local notation "weight(" z ", " p ")" =>
  ((((p).1.val : ℝ) : ℂ) ^ (z).1 * (∏ j : Fin d, (((p).2.1 j : Circle) : ℂ) ^ (z).2.1 j) *
    ((z).2.2 (p).2.2 : ℂ))

/-- The product of the torus and finite characters, twisted by the radial complex power. -/
private theorem bruhatMellin_coordinateCharacter (z : Z) :
    ∃ c : QuasiCharacter P, ∀ p, c p = weight(z, p) := by
  let m := ContinuousMonoidHom.fst ℝ≥0ˣ ((Fin d → Circle) × A)
  let χ : P →ₜ* Circle :=
    { toFun := fun p ↦ (∏ j, p.2.1 j ^ z.2.1 j) * z.2.2 p.2.2
      map_one' := by simp
      map_mul' := fun x y ↦ by
        simp only [Prod.snd_mul, Prod.fst_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib,
          map_mul]
        ac_rfl
      continuous_toFun := (continuous_finsetProd _ fun j _ ↦
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd)).zpow _).mul
        (z.2.2.continuous.comp (continuous_snd.comp continuous_snd)) }
  let coeχ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  refine ⟨quasiCharacterNormTwist m.toMonoidHom m.continuous coeχ z.1, fun p ↦ ?_⟩
  change Circle.coeHom ((∏ j, p.2.1 j ^ z.2.1 j) * z.2.2 p.2.2) *
    (((p.1.val : ℝ) : ℂ) ^ z.1) = _
  rw [map_mul, map_prod]
  change ((∏ j, ((p.2.1 j : Circle) : ℂ) ^ z.2.1 j) * (z.2.2 p.2.2 : ℂ)) * _ = _
  ac_rfl

/-- The logarithmic radial flow and the individual rotations have eigenvalues
`s` and `nⱼ i` respectively. -/
private theorem bruhatMellin_coordinateDirections :
    ∃ X : Option (Fin d) → LCATopologicalLie P, ∀ i (z : Z),
      HasDerivAt (fun t : ℝ ↦ weight(z, X i (Multiplicative.ofAdd t)))
        (i.elim z.1 (fun j ↦ (z.2.1 j : ℂ) * Complex.I)) 0 := by
  let radial : LCATopologicalLie P := (ContinuousMonoidHom.inl _ _).comp positiveRealLogEquiv.symm
  let rot : Multiplicative ℝ →ₜ* Circle :=
    { toFun := fun t ↦ Circle.exp t.toAdd
      map_one' := Circle.exp_zero
      map_mul' := fun s t ↦ Circle.exp_add _ _
      continuous_toFun := by fun_prop }
  let axis (j : Fin d) : Circle →ₜ* (Fin d → Circle) :=
    ⟨MonoidHom.mulSingle (fun _ : Fin d ↦ Circle) j,
      continuous_mulSingle (A := fun _ : Fin d ↦ Circle) j⟩
  let angular (j : Fin d) : LCATopologicalLie P :=
    (ContinuousMonoidHom.inr _ _).comp ((ContinuousMonoidHom.inl _ _).comp ((axis j).comp rot))
  refine ⟨fun i ↦ i.elim radial angular, fun i z ↦ ?_⟩
  have hd (v : ℂ) : HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * v)) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v).cexp)
  cases i with
  | none =>
    apply (hd z.1).congr_of_eventuallyEq
    filter_upwards with t
    change ((Real.exp t : ℝ) : ℂ) ^ z.1 * (∏ j : Fin d, ((1 : Circle) : ℂ) ^ z.2.1 j) *
      (z.2.2 1 : ℂ) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
    simp
  | some j =>
    apply (hd ((z.2.1 j : ℂ) * Complex.I)).congr_of_eventuallyEq
    filter_upwards with t
    change ((1 : ℝ) : ℂ) ^ z.1 *
      (∏ k, ((Pi.mulSingle (M := fun _ : Fin d ↦ Circle) j (Circle.exp t) k : Circle) : ℂ) ^ z.2.1 k) *
        (z.2.2 1 : ℂ) = _
    rw [Finset.prod_eq_single_of_mem j (Finset.mem_univ _) (fun k _ h ↦ by
      simp [Pi.mulSingle_eq_of_ne h]), Pi.mulSingle_eq_same]
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, map_one, Circle.coe_one, mul_one,
      Circle.coe_exp, ← Complex.exp_int_mul]
    congr 1
    ring

end

/-- Paper: Lemma B.4.4.8, p. 624. On a bounded vertical strip, the Mellin evaluation of
compactly supported Bruhat test is dominated by any inverse power of the joint height
`max |Im s| (max_j |n_j|)`, with a constant that depends on the test and on the strip.
This is the analytic half of Lemma B.4.4.8: it is the standard smoothing estimate for the
Mellin transform of a compactly supported test, applied in the `t` coordinate and in each
torus coordinate of the product presentation `e`, and it carries no counting hypothesis. -/
private theorem summable_bruhatMellin_of_polynomialCount_decay
    {G A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {d : ℕ} (e : G ≃ₜ* (ℝ≥0ˣ × (Fin d → Circle) × A))
    (μ : Measure G) [μ.IsHaarMeasure]
    (a b : ℝ) (N : ℕ) (f : 𝒟(G)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ × (Fin d → ℤ) × PontryaginDual A, z.1.re ∈ Icc a b →
      ‖∫ g, f.val g *
        (((e g).1.val : ℝ) : ℂ) ^ z.1 *
        (∏ j : Fin d, (((e g).2.1 j : Circle) : ℂ) ^ z.2.1 j) *
        (z.2.2 (e g).2.2 : ℂ) ∂μ‖ ≤
      K / (1 + max |z.1.im|
        ((Finset.univ.sup (fun j : Fin d => (z.2.1 j).natAbs) : ℕ) : ℝ)) ^ N := by
  classical
  let Z := {z : ℂ × (Fin d → ℤ) × PontryaginDual A // z.1.re ∈ Icc a b}
  let m := (ContinuousMonoidHom.fst ℝ≥0ˣ ((Fin d → Circle) × A)).comp (e : G →ₜ* _)
  let r (g : G) : ℝ := ((e g).1.val : ℝ)
  have hr (g : G) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hrc : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  -- The two endpoint weights bound every character in the strip on either side of r = 1.
  let W (g : G) := r g ^ a + r g ^ b
  have hW : Continuous W := (hrc.rpow_const (fun g ↦ .inl (hr g).ne')).add
    (hrc.rpow_const (fun g ↦ .inl (hr g).ne'))
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology G := e.toHomeomorph.isEmbedding.secondCountableTopology
  have hms : Surjective m := Prod.fst_surjective.comp e.surjective
  have hm : IsModulation m := ⟨isProperMap_fst_of_compactSpace.comp e.toHomeomorph.isProperMap, by
    obtain ⟨u, hu⟩ := exists_ne (1 : ℝ≥0ˣ)
    obtain ⟨g, hg⟩ := hms u
    exact ⟨g, hg ▸ hu⟩⟩
  -- The decay space at exponent zero supplies continuity of the underlying tests.
  have hcont (φ : 𝒟(G)) : Continuous φ.val := by
    have h := bruhatCompactSupport_le_modulatedExponentialDecay m {0} hm hms φ.property
    rw [modulatedExponentialDecaySubmodule_singleton_zero] at h
    exact schwartzBruhat_continuous (⟨_, h⟩ : SchwartzBruhat G)
  choose c hc using fun z : Z ↦ bruhatMellin_coordinateCharacter z.val
  let χ (z : Z) := (c z).comp (e : G →ₜ* _)
  have hbound (z : Z) (g : G) : ‖χ z g‖ ≤ W g := by
    change ‖c z (e g)‖ ≤ _
    rw [hc]
    simp only [norm_mul, Complex.norm_prod, norm_zpow, Circle.norm_coe, one_zpow,
      Finset.prod_const_one, mul_one]
    change ‖(r g : ℂ) ^ z.val.1‖ ≤ W g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hr g)]
    rcases le_total (r g) 1 with h | h
    · exact (Real.rpow_le_rpow_of_exponent_ge (hr g) h z.property.1).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (hr g).le b))
    · exact (Real.rpow_le_rpow_of_exponent_le h z.property.2).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (hr g).le a))
  obtain ⟨X, hX⟩ := bruhatMellin_coordinateDirections (A := A) (d := d)
  let Y (i : Option (Fin d)) : LCATopologicalLie G := (e.symm : _ →ₜ* G).comp (X i)
  let v (i : Option (Fin d)) (z : Z) := i.elim z.val.1 (fun j ↦ (z.val.2.1 j : ℂ) * Complex.I)
  have hd (i) (z : Z) :
      HasDerivAt (fun t : ℝ ↦ χ z (Y i (Multiplicative.ofAdd t))) (v i z) 0 := by
    change HasDerivAt (fun t : ℝ ↦ c z (e (e.symm (X i (Multiplicative.ofAdd t))))) _ _
    simp only [ContinuousMulEquiv.apply_symm_apply, hc]
    exact hX i z.val
  let H (z : Z) := max |z.val.1.im| ((Finset.univ.sup (fun j ↦ (z.val.2.1 j).natAbs) : ℕ) : ℝ)
  have hcoord (z : Z) : ∃ i, H z ≤ ‖v i z‖ := by
    by_cases h : ((Finset.univ.sup (fun j ↦ (z.val.2.1 j).natAbs) : ℕ) : ℝ) ≤ |z.val.1.im|
    · exact ⟨none, (max_eq_left h).le.trans (Complex.abs_im_le_norm _)⟩
    · have hn : (Finset.univ : Finset (Fin d)).Nonempty := by
        by_contra! hempty
        simp [hempty] at h
      obtain ⟨j, _, hj⟩ := Finset.univ.exists_mem_eq_sup hn (fun j ↦ (z.val.2.1 j).natAbs)
      refine ⟨some j, ?_⟩
      simp [H, max_eq_right (le_of_not_ge h), hj, v, Complex.norm_intCast]
  obtain ⟨K, hK, hdec⟩ := bruhatMellin_decay_of_directions μ χ W hW hbound hcont Y v hd H
    (fun z ↦ (abs_nonneg _).trans (le_max_left ..)) hcoord N f
  refine ⟨K, hK, fun z hz ↦ ?_⟩
  have heval (g : G) : χ ⟨z, hz⟩ g = _ := hc ⟨z, hz⟩ (e g)
  simpa only [heval, H, mul_assoc] using hdec ⟨z, hz⟩

end BruhatMellinPolynomialCount

/-- Paper: Lemma B.4.4.8, p. 624. Compactly supported Bruhat tests have
absolutely summable Mellin evaluations on polynomially counted samples in
a bounded strip of the quasi-character space of a real-modulated abelian Lie group.
Deviation: The joint counting bound includes both vertical height and torus
frequency, and uses a common strip. A product coordinate displays the compact
kernel as a torus times a finite abelian group. -/
theorem summable_bruhatMellin_of_polynomialCount
    {G A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {d : ℕ} (e : G ≃ₜ* (ℝ≥0ˣ × (Fin d → Circle) × A))
    (μ : Measure G) [μ.IsHaarMeasure]
    (Z : Set (ℂ × (Fin d → ℤ) × PontryaginDual A))
    (a b : ℝ) (_hStrip : ∀ z ∈ Z, z.1.re ∈ Icc a b)
    (_hCount : ∃ C k : ℕ, ∀ T : ℕ,
      {z ∈ Z | |z.1.im| ≤ T ∧ ∀ j, (z.2.1 j).natAbs ≤ T}.encard ≤
        ((C * (T + 1) ^ k : ℕ) : ℕ∞))
    (f : 𝒟(G)) :
    Summable (fun z : Z ↦ ‖∫ g, f.val g *
      (((e g).1.val : ℝ) : ℂ) ^ z.val.1 *
      (∏ j : Fin d, (((e g).2.1 j : Circle) : ℂ) ^ z.val.2.1 j) *
      (z.val.2.2 (e g).2.2 : ℂ) ∂μ‖) := by
  obtain ⟨C, k, hCount⟩ := _hCount
  obtain ⟨K, hK, hDecay⟩ :=
    summable_bruhatMellin_of_polynomialCount_decay e μ a b (k + 2) f
  set m : Z → ℝ := fun z => max |z.val.1.im|
    ((Finset.univ.sup (fun j : Fin d => (z.val.2.1 j).natAbs) : ℕ) : ℝ) with hmdef
  have hm : ∀ z : Z, 0 ≤ m z := by
    intro z
    rw [hmdef]
    exact (abs_nonneg _).trans (le_max_left _ _)
  refine summable_bruhatMellin_of_polynomialCount_of_polyCount_decay
    (g := fun z : Z => ‖∫ g, f.val g *
      (((e g).1.val : ℝ) : ℂ) ^ z.val.1 *
      (∏ j : Fin d, (((e g).2.1 j : Circle) : ℂ) ^ z.val.2.1 j) *
      (z.val.2.2 (e g).2.2 : ℂ) ∂μ‖)
    m hm C k K hK.le ?_ (hdecay := fun z => by
      rw [hmdef]
      simpa using hDecay z.val (_hStrip z.val z.2))
  intro T
  have hset : Subtype.val '' {z : Z | m z ≤ (T : ℝ)} =
      {p : ℂ × (Fin d → ℤ) × PontryaginDual A |
        p ∈ Z ∧ |p.1.im| ≤ (T : ℝ) ∧ ∀ j, (p.2.1 j).natAbs ≤ T} := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, (le_max_left _ _).trans hz, fun j => ?_⟩
      have h2 : ((Finset.univ.sup (fun j : Fin d => (z.val.2.1 j).natAbs) : ℕ) : ℝ) ≤ (T : ℝ) :=
        (le_max_right _ _).trans hz
      have h3 : (Finset.univ.sup (fun j : Fin d => (z.val.2.1 j).natAbs) : ℕ) ≤ T :=
        by exact_mod_cast h2
      exact (Finset.le_sup (f := fun j : Fin d => (z.val.2.1 j).natAbs)
        (Finset.mem_univ j)).trans h3
    · rintro ⟨hpZ, him, hn⟩
      refine ⟨⟨p, hpZ⟩, ?_, rfl⟩
      change max |p.1.im| ((Finset.univ.sup (fun j : Fin d => (p.2.1 j).natAbs) : ℕ) : ℝ)
        ≤ (T : ℝ)
      rw [max_le_iff]
      refine ⟨him, ?_⟩
      have h3 : (Finset.univ.sup (fun j : Fin d => (p.2.1 j).natAbs) : ℕ) ≤ T :=
        Finset.sup_le fun j _ => hn j
      exact_mod_cast h3
  calc {z : Z | m z ≤ (T : ℝ)}.encard
      = (Subtype.val '' {z : Z | m z ≤ (T : ℝ)}).encard :=
        (Subtype.val_injective.injOn.encard_image).symm
    _ = {p : ℂ × (Fin d → ℤ) × PontryaginDual A |
          p ∈ Z ∧ |p.1.im| ≤ (T : ℝ) ∧ ∀ j, (p.2.1 j).natAbs ≤ T}.encard := by rw [hset]
    _ = {z ∈ Z | |z.1.im| ≤ T ∧ ∀ j, (z.2.1 j).natAbs ≤ T}.encard := by congr 1
    _ ≤ _ := hCount T

private theorem summable_ideleClassMellin_completedHeckeZeros_weight
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (f : 𝒟(G)) (b : ℝ) :
    ∃ f' : 𝒟(G), ∀ g, f'.val g = (((m g).val : ℝ) : ℂ) ^ (b : ℂ) * f.val g := by
  have hS : modulationWeight m b f.val ∈ schwartzBruhatSubmodule G :=
    modulationWeight_mem_schwartzBruhat m univ ⟨b, mem_univ _⟩
      ⟨f.val, bruhatCompactSupport_le_modulatedExponentialDecay m univ hm hms f.property⟩
  refine ⟨⟨modulationWeight m b f.val, (mem_bruhatSmoothSubmodule_iff _).2
    (schwartzBruhat_isBruhatSmooth (G := G) ⟨_, hS⟩), f.property.2.mul_left⟩, ?_⟩
  intro g
  change ((((m g).val : ℝ) ^ b : ℝ) : ℂ) * f.val g = _
  rw [Complex.ofReal_cpow (m g).val.coe_nonneg]

-- TODO(paper-gap): On p. 625, passing to a Lie quotient eliminates other kernel
-- characters. A uniform zero count with multiplicity for the remaining characters
-- is still needed to apply the corrected Lemma B.4.4.8.

/-- Paper: Lemma B.4.4.9, pp. 624–625. Mellin evaluations on any subset
of the completed Hecke zeros are absolutely summable after a real norm twist.
Deviation: Norm-section coordinates list the zeros once, and the weight also
counts their multiplicities as needed in the explicit formula. -/
theorem summable_ideleClassMellin_completedHeckeZeros (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (Z : Set (chartZeros(τ)))
    (f : 𝒟(C[F])) (a : ℝ) :
    Summable (fun z : Z ↦ ‖zeroMultiplicity(z.val) *
      ∫ g, classMellinIntegrand(f, zeroCharacter(z.val), (a : ℂ)) g ∂classMeasure‖) := by
  -- Absorb the shift from the centered exponent of the idelic explicit formula into the test.
  obtain ⟨m, hmNorm, hm, hms⟩ := exists_ideleClassModulation F
  obtain ⟨f', h'⟩ := summable_ideleClassMellin_completedHeckeZeros_weight
    (G := C[F]) m hm hms f (a + 1 / 2)
  have hw (g : C[F]) : f'.val g * classWeight(g, -1 / 2) = f.val g * classWeight(g, (a : ℂ)) := by
    have hx : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [h', show m g = ideleClassNorm F g from DFunLike.congr_fun hmNorm g, mul_comm _ (f.val g),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    push_cast
    ring_nf
  have hvol : 0 < classVolume := by
    rw [normOneIdeleClassTamagawaMeasure_volume]
    have := NumberField.classNumber_pos F
    have := NumberField.Units.regulator_pos F
    have := NumberField.Units.torsionOrder_pos F
    have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
    rw [ENNReal.toReal_ofReal (by positivity)]
    positivity
  -- Restrict the absolutely summable spectral family and undo its volume normalization.
  obtain ⟨S, _, _, _, hSval, _, _, _, hsum, _⟩ := idelicExplicitFormula τ _hτ
  refine (((hsum f').subtype (fun z ↦ z ∈ Z)).mul_left ‖(classVolume : ℂ)‖).congr fun z ↦ ?_
  change ‖(classVolume : ℂ)‖ * ‖S z.val f'‖ = _
  rw [← norm_mul, hSval]
  congr 1
  rw [← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hvol.ne')]
  congr 1
  apply integral_congr_ae
  filter_upwards with g
  calc _ = (f'.val g * classWeight(g, -1 / 2)) * zeroCharacter(z.val) g := by ring
       _ = _ := by rw [hw]; ring

end IdelicExplicitFormula

end RiemannMasullo
