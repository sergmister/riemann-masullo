module

public import RiemannMasullo.Research.StripNuclearity.HeckeArchimedean
public import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Positive Hecke zero mass from a signed partial-fraction identity

The signed identity in the last theorem is an explicit hypothesis. The bound for
the poles applies also to nontrivial norm twists with nonreal poles.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "D(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ

/-- The difference between the Cauchy kernels at two and minus one. -/
def pairedHeckeKernel (z : ℂ) : ℂ := (2 - z)⁻¹ + (1 + z)⁻¹

private theorem norm_pairedHeckeKernel_le {z : ℂ} (h₀ : 0 ≤ z.re) (h₁ : z.re ≤ 1) :
    ‖pairedHeckeKernel z‖ ≤ 2 := by
  have hl : 1 ≤ ‖(2 : ℂ) - z‖ := calc
    (1 : ℝ) ≤ ((2 : ℂ) - z).re := by simp; linarith
    _ ≤ _ := Complex.re_le_norm _
  have hr : 1 ≤ ‖(1 : ℂ) + z‖ := calc
    (1 : ℝ) ≤ ((1 : ℂ) + z).re := by simpa
    _ ≤ _ := Complex.re_le_norm _
  refine (norm_add_le _ _).trans ?_
  rw [norm_inv, norm_inv]
  linarith [inv_le_one_of_one_le₀ hl, inv_le_one_of_one_le₀ hr]

private theorem zero_re_lt_one (χ : U) {z : ℂ}
    (hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z) : z.re < 1 := by
  rcases le_or_gt z.re 0 with h | h
  · exact h.trans_lt zero_lt_one
  · have hΛ := continuedCompletedHeckeL_spec χ
    exact completedHeckeL_continuation_zeros χ _ hΛ.1 hΛ.2 h hp

/-- Paper: Proposition 3.2.1.3(3)–(4), p. 123. The positive divisor of the
completed continuation lies in the open critical strip, including for norm twists. -/
theorem heckePositiveDivisor_open_strip (χ : U) {z : ℂ} (hz : 0 < D(χ) z) :
    0 < z.re ∧ z.re < 1 := by
  obtain ⟨hL, hl⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hd⟩ := continuedCompletedHeckeL_spec χ⁻¹
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
    rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hz
    cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => simp
    | coe k =>
      rw [he, WithTop.untop₀_coe] at hz
      exact_mod_cast hz
  obtain ⟨ε, hε, hne, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation χ _ _ hL hl hD hd
  have he : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹)
        (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
        (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) = ε * continuedCompletedHeckeL χ
    from funext hfe, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at he
  have h := zero_re_lt_one χ⁻¹ (he ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at h
  exact ⟨by linarith, zero_re_lt_one χ hp⟩

private theorem heckePolarCorrection (χ : U) :
    ∃ P : ℂ, ‖P‖ ≤ 4 ∧ HasSum
      (fun z : ℂ ↦ (((-(D(χ) z)).toNat : ℕ) : ℂ) * pairedHeckeKernel z) P := by
  classical
  obtain ⟨hL, hl⟩ := continuedCompletedHeckeL_spec χ
  have hn {z : ℂ} (ha : AnalyticAt ℂ (continuedCompletedHeckeL χ) z) :
      (-(D(χ) z)).toNat = 0 := by
    rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)]
    have h := ha.meromorphicOrderAt_nonneg
    cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) z with
    | top => simp
    | coe k =>
      rw [he] at h
      simp only [WithTop.untop₀_coe]
      have hk : 0 ≤ k := by exact_mod_cast h
      omega
  by_cases hc : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨_, hp, hq, ha⟩, _⟩ := completedHeckeL_continuation_simplePoles χ _ hL hl hc
    let p := Complex.I * (t : ℂ)
    let q := 1 + p
    have hpr : p.re = 0 := by simp [p]
    have hqr : q.re = 1 := by simp [q, hpr]
    have hpq : p ≠ q := fun h ↦ by have := congrArg Complex.re h; linarith
    have hp' : D(χ) p = -1 := by rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)]; simp [p, hp]
    have hq' : D(χ) q = -1 := by rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)]; simp [q, p, hq]
    have hb₁ := norm_pairedHeckeKernel_le hpr.ge (by linarith : p.re ≤ 1)
    have hb₂ := norm_pairedHeckeKernel_le (by linarith : 0 ≤ q.re) hqr.le
    refine ⟨pairedHeckeKernel p + pairedHeckeKernel q, (norm_add_le _ _).trans ?_, ?_⟩
    · linarith
    convert (hasSum_ite_eq p (pairedHeckeKernel p)).add (hasSum_ite_eq q (pairedHeckeKernel q)) using 1
    funext z
    by_cases hz : z = p
    · subst z; simp [hp', hpq]
    by_cases hz' : z = q
    · subst z; simp [hq', hpq.symm]
    · have hm := hn (ha z (by simpa [p, q] using And.intro hz hz'))
      simp [hz, hz', hm]
  · have he := completedHeckeL_continuation_entire χ _ hL hl hc
    refine ⟨0, by norm_num, ?_⟩
    simpa only [fun z ↦ hn (he.analyticAt z), Nat.cast_zero, zero_mul] using
      (hasSum_zero (β := ℂ) (α := ℂ))

/-- An arithmetic reduction for all number fields. The signed sum uses the corrected
conductor sign of (B.4.2.3), p. 614, and both actual logarithmic derivatives at two.
The real bound is uniform in the character and counts only positive multiplicities.
The paired partial-fraction identity remains a hypothesis. -/
theorem exists_uniform_heckeZeroMass_of_paired_divisor (F : Type*) [Field F] [NumberField F] :
    ∃ C ≥ (0 : ℝ), ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      HasSum (fun z : ℂ ↦ (D(χ) z : ℂ) * pairedHeckeKernel z)
        (logDeriv (continuedCompletedHeckeL χ) 2 + logDeriv (continuedCompletedHeckeL χ⁻¹) 2 +
          (heckeLogDiscriminantConductor χ : ℂ)) →
      let W := fun ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F) ↦
        ∑ v : InfinitePlace F, (1 + (heckeArchimedeanShift ψ v).re + |(heckeArchimedeanShift ψ v).im|)
      let mass := fun z : ℂ ↦ ((D(χ) z).toNat : ℝ) / (1 + |z.im|) ^ 2
      Summable mass ∧ ∑' z, mass z ≤ C * (1 + W χ + W χ⁻¹ + |heckeLogDiscriminantConductor χ|) := by
  obtain ⟨A, hA, hder⟩ := exists_continuedCompletedHeckeL_uniform_logDeriv_two F
  refine ⟨2 * A + 5, by positivity, fun χ h ↦ ?_⟩
  let W (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :=
    ∑ v : InfinitePlace F, (1 + (heckeArchimedeanShift ψ v).re + |(heckeArchimedeanShift ψ v).im|)
  have hW (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) : 0 ≤ W ψ :=
    Finset.sum_nonneg fun v _ ↦ add_nonneg (add_nonneg zero_le_one (heckeArchimedeanShift_re_nonneg ψ v))
      (abs_nonneg _)
  obtain ⟨P, hP, hp⟩ := heckePolarCorrection χ
  have hadd := h.add hp
  have split (k : ℤ) : (k : ℂ) + ((-k).toNat : ℂ) = (k.toNat : ℂ) := by
    exact_mod_cast (show k + ((-k).toNat : ℤ) = (k.toNat : ℤ) by omega)
  simp only [← add_mul, split] at hadd
  have hz := heckeZeroMass_le_of_hasSum_reciprocalPair (fun z : ℂ ↦ z)
    (fun z ↦ (D(χ) z).toNat) (fun z hz ↦ by
      have hs := heckePositiveDivisor_open_strip χ (z := z) (by omega)
      exact ⟨hs.1.le, hs.2.le⟩) hadd
  refine ⟨hz.1, hz.2.trans ?_⟩
  change _ ≤ (2 * A + 5) * (1 + W χ + W χ⁻¹ + |heckeLogDiscriminantConductor χ|)
  have hl (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
      (logDeriv (continuedCompletedHeckeL ψ) 2).re ≤ A * (1 + W ψ) :=
    (Complex.re_le_norm _).trans (hder ψ)
  simp only [Complex.add_re, Complex.ofReal_re]
  have hC := abs_nonneg (heckeLogDiscriminantConductor χ)
  nlinarith [hl χ, hl χ⁻¹, (Complex.re_le_norm P).trans hP, le_abs_self (heckeLogDiscriminantConductor χ),
    hW χ, hW χ⁻¹, mul_nonneg hA (hW χ), mul_nonneg hA (hW χ⁻¹), mul_nonneg hA hC]

end RiemannMasullo.StripNuclearity
