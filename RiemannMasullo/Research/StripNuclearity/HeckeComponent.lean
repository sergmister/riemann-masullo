module

public import RiemannMasullo.Research.StripNuclearity.ScalarProjection
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros

/-!
# The projected radial resolvent for a single Hecke character

The fixed-character divisor count from #6438 supplies the rank summability.
The scalar projector is defined intrinsically by the admitted Mellin jets of
the completed Hecke function, including the strict Sobolev boundary cutoff.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "right(" a ")" => Complex.re ⁻¹' Ioi (a : ℝ)
local notation "zeroOrder(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
set_option quotPrecheck false in
local notation "windowZeros(" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder(χ, s) ∧ |s.re - 1 / 2| < (a : ℝ)}

/-- Removing the gamma factor gives a continuation of the finite L-function. The entire
reciprocal gamma factor can only increase the order at a zero. -/
private theorem zeroCount_finite_companion (χ : U𝔽) :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧ (∀ z : right(1), L z = finiteHeckeL χ z) ∧
      ∀ z, meromorphicOrderAt (continuedCompletedHeckeL χ) z ≤ meromorphicOrderAt L z := by
  let Λ := continuedCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let P := G * Λ
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec χ
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

/-- Paper: §1.4.3, p. 29, for the proof that the zero sum is entire. Weighted zero count:
for every unitary character `χ` and every half-width `a`, the zeros of the completed Hecke
L-function in the open window `|Re s - 1/2| < a`, counted with their orders, satisfy
`∑ ord(ρ) / (1 + |Im ρ|)² < ∞`. This is the classical consequence of the zero count
`N(T + 1) - N(T) = O(log T)` for Hecke L-functions. -/
private theorem hecke_zeroCount (χ : U𝔽) (a : ℝ) :
    Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℝ) / (1 + |r.val.im|) ^ 2) := by
  obtain ⟨L, hL, hSeries, hOrder⟩ := zeroCount_finite_companion χ
  obtain ⟨hLine, k, _, hInv⟩ := finiteHeckeL_inv_isBigO_oneLine χ L hL hSeries
  exact summable_divisor_div_one_add_abs_im_sq (k := k) (σ := 1)
    (continuedCompletedHeckeL_spec χ).1.meromorphicOn hL hOrder
    (finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries) (hLine.mono fun _ ht ↦ ht.2)
    hInv (1 / 2) a

/-- The inverse-square moment of the positive divisor of a fixed Hecke character
in any open critical window. This includes the polar character. -/
theorem summable_heckePositiveDivisor_in_window (χ : U𝔽) (a : ℝ) :
    Summable (fun r : windowZeros(χ, a) ↦ (zeroOrder(χ, r.val) : ℝ) / (1 + |r.val.im|) ^ 2) :=
  hecke_zeroCount χ a

/-- For fixed strip parameters, the projected resolvent for every unitary
Hecke character uses the same operator and constant. Its trace norm is bounded
by that constant times the square of one plus the weighted admitted divisor
mass. Each boundary jet obeys the strict Sobolev cutoff. -/
theorem exists_projected_hecke_resolvent_uniform {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) :
    let d := α+s+2
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    let r := fun z : ℂ ↦ (((d+1 : ℝ) : ℂ)^2-z^2)⁻¹
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E) (C : ℝ), 0 ≤ C ∧
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          r z * mellin (fun t ↦ p.val (Real.log t)) z) ∧
      ∀ χ : U𝔽,
        let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
        let Z := {z : ℂ // 0 < D z ∧ |z.re - 1/2| ≤ α}
        let w := fun z : Z ↦ (⟨z.val.re - 1/2, z.val.im⟩ : ℂ)
        let m := fun z : Z ↦ spectralStripMultiplicity α s (w z).re (D z.val).toNat
        let J := Σ z, Fin (m z)
        let W := ∑' z : Z, (m z : ℝ)/(1+|(w z).im|)^2
        ∃ Λ : J → StrongDual ℂ E,
          (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
            (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) ∧
          let P := (⨅ l, (Λ l).ker).orthogonal.starProjection
          ∃ hn : IsNuclearOperator (R.adjoint.comp P),
            traceNorm ⟨R.adjoint.comp P,hn⟩ ≤ C*(1+W)^(2:ℕ) := by
  intro d E I r
  obtain ⟨j,R,C,hC,hdense,hjrep,hr,hu⟩ :=
    exists_scalar_resolvent_on_admitted_jets_uniform.{0} ha (by linarith : 0 ≤ s)
  refine ⟨j,R,C,hC,hdense,hjrep,hr,?_⟩
  intro χ D Z w m J W
  let wide (z : Z) : windowZeros(χ, α+1) :=
    ⟨z.val, z.property.1, z.property.2.trans_lt (lt_add_one _)⟩
  have hemb : Injective wide := fun x y h ↦ Subtype.ext (congrArg (fun z : windowZeros(χ, α+1) ↦ z.val) h)
  have hcnt := (hecke_zeroCount χ (α+1)).comp_injective hemb
  have hw (z : Z) : (w z).re ∈ Icc (-α) α := abs_le.mp z.property.2
  have hedge (z : Z) (hi : (w z).re ∉ Ioo (-α) α) :
      (w z).re = -α ∨ (w z).re = α := by
    have hx := hw z
    rcases eq_or_lt_of_le hx.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (eq_of_le_of_not_lt hx.2 (fun hy ↦ hi ⟨h,hy⟩))
  have hm (z : Z) : 0 < m z := by
    have hz : 0 < (D z.val).toNat := by omega
    by_cases hi : (w z).re ∈ Ioo (-α) α
    · simpa only [m, spectralStripMultiplicity_interior hi] using hz
    · dsimp only [m]
      rw [spectralStripMultiplicity_boundary ha (hedge z hi), lt_spectralBoundaryMultiplicity]
      exact ⟨hz, by simpa using hs⟩
  have hj (z : Z) (l : Fin (m z)) :
      (w z).re ∈ Ioo (-α) α ∨ (w z).re ∈ Icc (-α) α ∧ 2 * (l.val : ℝ) + 1 < s := by
    by_cases hi : (w z).re ∈ Ioo (-α) α
    · exact Or.inl hi
    · have hl : l.val < spectralBoundaryMultiplicity s (D z.val).toNat :=
        lt_of_lt_of_eq l.isLt (spectralStripMultiplicity_boundary ha (hedge z hi) s _)
      exact Or.inr ⟨hw z, by linarith [((lt_spectralBoundaryMultiplicity s _ _).mp hl).2]⟩
  have hsum : Summable fun z : Z ↦ (m z : ℝ) / (1+|(w z).im|)^2 := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ hcnt
    intro z
    have hn : m z ≤ (D z.val).toNat := by
      unfold m spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    have hreal : (m z : ℝ) ≤ (D z.val : ℝ) := by
      have hn' : (m z : ℤ) ≤ D z.val := by
        have hpos := z.property.1
        omega
      exact_mod_cast hn'
    exact div_le_div_of_nonneg_right hreal (sq_nonneg _)
  exact hu w m hm hsum hj

/-- The actual closed-strip divisor of a fixed unitary Hecke character gives
a nuclear projected resolvent on the weighted radial Sobolev space. The
resolvent is identified on dense tests by its Mellin symbol. -/
theorem exists_projected_hecke_resolvent (χ : U𝔽) {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) :
    let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    let Z := {z : ℂ // 0 < D z ∧ |z.re - 1/2| ≤ α}
    let w := fun z : Z ↦ (⟨z.val.re - 1/2, z.val.im⟩ : ℂ)
    let m := fun z : Z ↦ spectralStripMultiplicity α s (w z).re (D z.val).toNat
    let d := α+s+2
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    let J := Σ z, Fin (m z)
    let r := fun z : ℂ ↦ (((d+1 : ℝ) : ℂ)^2-z^2)⁻¹
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E) (Λ : J → StrongDual ℂ E),
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
        ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
          r z * mellin (fun t ↦ p.val (Real.log t)) z) ∧
      (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
        (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) ∧
      IsNuclearOperator (R.adjoint.comp ((⨅ l, (Λ l).ker).orthogonal.starProjection)) := by
  intro D Z w m d E I J r
  obtain ⟨j,R,C,-,hdense,hj,hr,hu⟩ := exists_projected_hecke_resolvent_uniform (F := F) ha hs
  obtain ⟨Λ,hΛ,hn,-⟩ := hu χ
  exact ⟨j,R,Λ,hdense,hj,hr,hΛ,hn⟩

end RiemannMasullo.StripNuclearity
