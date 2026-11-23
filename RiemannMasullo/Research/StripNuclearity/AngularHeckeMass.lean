module

public import RiemannMasullo.Research.StripNuclearity.AngularHeckeParameters
public import RiemannMasullo.Research.StripNuclearity.AngularConductor
public import RiemannMasullo.Research.StripNuclearity.HeckeComponent
import RiemannMasullo.Research.StripNuclearity.HeckePairedDivisor

/-! # An angular weight for the positive Hecke divisor

The ordinary finite conductor is bounded on the nonzero angular profiles
of a single compact Bruhat test. The archimedean parameters are real
frequencies on the compact dual. Together they control the quadratic weight
of the completed divisor, including the single polar channel.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U" => PontryaginDual C𝔽
local notation "X" => PontryaginDual C₁
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) ψ) univ

/-- The sum of positive multiplicities of the completed Hecke divisor,
weighted by `(1+|Im z|)⁻²`, over the entire plane. -/
def heckePositiveDivisorMass (ψ : U) : ℝ :=
  ∑' z : ℂ, ((D(ψ) z).toNat : ℝ) / (1 + |z.im|) ^ 2

/-- The fixed-character inverse-square count also covers the trivial
character, with its two poles contributing zero positive multiplicity. -/
theorem summable_heckePositiveDivisor_mass (ψ : U) :
    Summable (fun z : ℂ ↦ ((D(ψ) z).toNat : ℝ) / (1 + |z.im|) ^ 2) := by
  classical
  let f (z : ℂ) := ((D(ψ) z).toNat : ℝ) / (1 + |z.im|) ^ 2
  let S := {z : ℂ | 0 < D(ψ) z ∧ |z.re - 1 / 2| < 1}
  have hsum : Summable (f ∘ (↑) : S → ℝ) := by
    apply (summable_heckePositiveDivisor_in_window ψ 1).congr
    intro z
    have hn : (((D(ψ) z.val).toNat : ℕ) : ℝ) = (D(ψ) z.val : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg z.property.1.le)
    simp [Function.comp_apply, f, hn]
  have hsupp : support f ⊆ S := by
    intro z hz
    have hd : 0 < D(ψ) z := by
      by_contra h
      exact hz (by simp [f, Int.toNat_of_nonpos (le_of_not_gt h)])
    obtain ⟨hl, hr⟩ := heckePositiveDivisor_open_strip ψ hd
    exact ⟨hd, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  exact ((hasSum_subtype_iff_of_support_subset hsupp).mp hsum.hasSum).summable

theorem heckePositiveDivisorMass_nonneg (ψ : U) : 0 ≤ heckePositiveDivisorMass ψ :=
  tsum_nonneg (fun _ ↦ by positivity)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

/-- For every fixed Bruhat test, the square of one plus the full Hecke zero
mass on its active angular channels is dominated by one of the frequency
weights in the angular Fourier estimates. A multiplicative section ensures
that its only polar channel is the trivial character. -/
theorem exists_angular_weight_heckePositiveDivisorMass_of_bound
    (φ : BruhatCompactSupport C𝔽) (μ : Measure C₁) [μ.IsHaarMeasure]
    (χ : X →* U) (hχ : IsSpectralBasepointChoice χ)
    (K : ℝ) (hK : 0 ≤ K) (hκ : ∀ ψ : U, 0 ≤ heckeLogDiscriminantConductor ψ)
    (hbound : ∀ ψ : U, ψ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 →
      heckePositiveDivisorMass ψ ≤ K * (1 + |heckeLogDiscriminantConductor ψ| +
        Real.log (6 + ∑ v : InfinitePlace F, ‖heckeArchimedeanShift ψ v‖))) :
    ∃ (C : ℝ) (fs : List (X →ₜ* Multiplicative ℝ)), 0 ≤ C ∧ ∀ ξ : X,
      (∃ g : C𝔽, (∫ k : C₁, φ.val (k.val * g) * (ξ k : ℂ) ∂μ) ≠ 0) →
      (1 + heckePositiveDivisorMass (χ ξ)) ^ 2 ≤
        C * (fs.map (fun f ↦ 1 + ((f ξ).toAdd)^2)).prod := by
  classical
  obtain ⟨C₀, hC₀⟩ := bruhatCompactSupport_bounded_angular_logConductor φ μ
  obtain ⟨fs, hfs⟩ := exists_angular_weight_heckeArchimedeanShifts χ
  let n : ℝ := Fintype.card (InfinitePlace F)
  let B := 1 + heckePositiveDivisorMass (1 : U) + K * (7 + |C₀| + 3*n)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hp := heckePositiveDivisorMass_nonneg (1 : U)
  have hB : 1 ≤ B := by dsimp [B]; linarith [mul_nonneg hK (by positivity : 0 ≤ 7 + |C₀| + 3*n)]
  refine ⟨B ^ 2, fs ++ fs, sq_nonneg _, fun ξ ⟨g, hg⟩ ↦ ?_⟩
  let W := (fs.map (fun f ↦ 1 + ((f ξ).toAdd)^2)).prod
  obtain ⟨hw, hj⟩ := hfs ξ
  change 1 ≤ W at hw
  change (∑ v : InfinitePlace F, ‖heckeArchimedeanShift (χ ξ) v‖) ≤ 3*n*W at hj
  have heval (k : C₁) : χ ξ k.val = ξ k := DFunLike.congr_fun (hχ ξ) k
  have hineq : 1 + heckePositiveDivisorMass (χ ξ) ≤ B * W := by
    by_cases htriv : ξ = 1
    · rw [htriv, map_one]
      apply le_trans _ (le_mul_of_one_le_right (zero_le_one.trans hB) hw)
      dsimp [B]
      linarith [mul_nonneg hK (by positivity : 0 ≤ 7 + |C₀| + 3*n)]
    have hnon : (χ ξ).toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := by
      intro h
      apply htriv
      apply PontryaginDual.ext
      intro k
      exact (heval k).symm.trans (DFunLike.congr_fun h k)
    have hprof : (∫ k : C₁, φ.val (k.val * g) * (χ ξ (k.val * g) : ℂ) ∂μ) ≠ 0 := by
      have he : (∫ k : C₁, φ.val (k.val * g) * (χ ξ (k.val * g) : ℂ) ∂μ) =
          (χ ξ g : ℂ) * ∫ k : C₁, φ.val (k.val * g) * (ξ k : ℂ) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae (.of_forall fun k ↦ ?_)
        rw [map_mul, heval]
        simp only [Circle.coe_mul]
        ring
      rw [he]
      exact mul_ne_zero (Circle.coe_ne_zero _) hg
    have hc : |heckeLogDiscriminantConductor (χ ξ)| ≤ |C₀| := by
      rw [abs_of_nonneg (hκ _)]
      exact (hC₀ (χ ξ) g hprof).trans (le_abs_self _)
    let J := ∑ v : InfinitePlace F, ‖heckeArchimedeanShift (χ ξ) v‖
    have hJ : 0 ≤ J := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hlog : Real.log (6 + J) ≤ 6 + J := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have hs : 1 + |heckeLogDiscriminantConductor (χ ξ)| + Real.log (6 + J) ≤
        (7 + |C₀| + 3*n)*W := by
      change J ≤ 3*n*W at hj
      nlinarith [mul_le_mul_of_nonneg_left hw (abs_nonneg C₀)]
    have hM := hbound (χ ξ) hnon
    change heckePositiveDivisorMass (χ ξ) ≤ K * (1 + |heckeLogDiscriminantConductor (χ ξ)| + Real.log (6 + J)) at hM
    dsimp [B]
    nlinarith [hM.trans (mul_le_mul_of_nonneg_left hs hK), mul_nonneg hp (zero_le_one.trans hw)]
  have hpow := pow_le_pow_left₀ (by linarith [heckePositiveDivisorMass_nonneg (χ ξ)]) hineq 2
  simpa only [List.map_append, List.prod_append, ← sq, mul_pow] using hpow

end RiemannMasullo.StripNuclearity
