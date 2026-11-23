module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-! # Printed trace formula of §12.5

The proposition records Theorem 12.5.1.1 as printed. The repaired statement is
`traceFormula` in `Sec5.lean`. Nothing imports this file.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
local notation "M[" F "](" φ ", " c ")" =>
  modulatedFourierMellin m[F] univ
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m[F])
    (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport C[F]).val c
local notation "ord(" χ ", " s ")" => MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ s

open Classical in
/-- Paper: Theorem 12.5.1.1, pp. 519–520. As printed, for every number field F,
every test φ vanishing on C_F¹ and every interval I = [−α, α] with α > 0
as in §1.8.4, p. 53, the sum of the local principal
values equals M(φ)(|·|^{1/2}) + M(φ)(|·|^{−1/2}) minus the sum of N(c)·M(φ)(c|·|^{−1/2})
over the zeros c in the interior of Ω(C_F)_I, with convergent series. The interior
is |σ(c) − 1/2| < α, and a norm section lists each quasi-character once.
The complex denominator is the ordinary modulus printed in (12.5.1.1).
The local tests vanish at one, so this term is an ordinary integral. -/
def Printed.traceFormula : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    ∀ φ : BruhatCompactSupport C[F], (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
    ∀ α : ℝ, 0 < α →
      let zeros := {z : {χ : PontryaginDual C[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
        0 < ord(z.1.val, z.2) ∧ |z.2.re - 1 / 2| < α}
      let finiteTerm := fun (v : HeightOneSpectrum (𝓞 F))
          (b : BruhatCompactSupport (v.adicCompletion F)ˣ) ↦
        let μ := finiteLocalMultiplicativeTamagawaMeasure F v
        let mass := (μ (v.adicCompletionIntegers F).units).toReal
        ((Real.log (v.asIdeal.absNorm : ℝ) / mass : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b
      let archTerm := fun (w : InfinitePlace F) (a : BruhatCompactSupport w.Completionˣ) ↦
        if w.IsReal then infiniteConnesWeilPrincipalValue w a
        else (1 / (2 * (Real.pi : ℂ))) * ∫ u : w.Completionˣ,
          a.val u * (‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ)
            ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)
      ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
        (b : (v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ),
        (∀ w u, (a w).val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (b v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        Summable (fun v ↦ finiteTerm v (b v)) ∧
        HasSum (fun z : zeros ↦ ((ord(z.val.1.val, z.val.2) : ℤ) : ℂ) *
            M[F](φ, ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2)))
          (M[F](φ, ideleClassNormTwist 1 (1 / 2)) + M[F](φ, ideleClassNormTwist 1 (-1 / 2)) -
            ((∑ w : InfinitePlace F, archTerm w (a w)) +
              ∑' v, finiteTerm v (b v)))


private theorem traceFormula_false_hasSum_zero {X : Type*} (f : X → ℂ) (e : X ≃ X)
    (he : ∀ x, f (e x) = -f x) {S : ℂ} (h : HasSum f S) : S = 0 := by
  have h2 : HasSum (fun x ↦ f (e x)) S := e.hasSum_iff.mpr h
  simp only [he] at h2
  have h3 : -S = S := h.neg.unique h2
  linear_combination -h3 / 2

private theorem traceFormula_false_natPow (n : ℕ) (k : ℤ) (hn : 0 < n)
    (h1 : Real.log (9 / 4) < |Real.log ((n : ℝ) ^ k)|)
    (h2 : |Real.log ((n : ℝ) ^ k)| < Real.log (11 / 4)) : False := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : |Real.log ((n : ℝ) ^ k)| = Real.log (((n ^ k.natAbs : ℕ) : ℝ)) := by
    rw [Real.log_zpow, abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn)),
      Nat.cast_pow, Real.log_pow, Nat.cast_natAbs, Int.cast_abs]
  rw [hl] at h1 h2
  have hm : (0 : ℝ) < ((n ^ k.natAbs : ℕ) : ℝ) := by exact_mod_cast pow_pos hn _
  rw [Real.log_lt_log_iff (by norm_num) hm] at h1
  rw [Real.log_lt_log_iff hm (by norm_num)] at h2
  have b1 : (2 : ℝ) < ((n ^ k.natAbs : ℕ) : ℝ) := by linarith
  have b2 : ((n ^ k.natAbs : ℕ) : ℝ) < 3 := by linarith
  have a1 : 2 < n ^ k.natAbs := by exact_mod_cast b1
  have a2 : n ^ k.natAbs < 3 := by exact_mod_cast b2
  omega

private theorem traceFormula_false_bump :
    ∃ h : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ HasCompactSupport h ∧
      (∀ t, h (-t) = -h t) ∧
      (∀ t, h t ≠ 0 → Real.log (9 / 4) < |t| ∧ |t| < Real.log (11 / 4)) ∧
      (∀ t, 0 ≤ h t * t) ∧ ∃ t, h t ≠ 0 := by
  set A := Real.log (9 / 4)
  set B := Real.log (11 / 4)
  have hA : 0 < A := Real.log_pos (by norm_num)
  have hAB : A < B := Real.log_lt_log (by norm_num) (by norm_num)
  let b : ContDiffBump ((A + B) / 2) := ⟨(B - A) / 4, (B - A) / 2, by linarith, by linarith⟩
  have hsupp (t : ℝ) (ht : b t ≠ 0) : A < t ∧ t < B := by
    have : t ∈ Metric.ball ((A + B) / 2) ((B - A) / 2) := by
      rw [← b.support_eq]; exact ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  refine ⟨fun t ↦ b t - b (-t), ?_, ?_, ?_, ?_, ?_, ⟨(A + B) / 2, ?_⟩⟩
  · exact b.contDiff.sub (b.contDiff.comp contDiff_neg)
  · exact b.hasCompactSupport.sub (b.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ))
  · intro t; simp only [neg_neg]; ring
  · intro t ht
    dsimp only at ht
    by_cases h1 : b t = 0
    · have h2 : b (-t) ≠ 0 := by intro h2; exact ht (by rw [h1, h2, sub_zero])
      obtain ⟨c1, c2⟩ := hsupp _ h2
      rw [abs_of_neg (by linarith)]
      exact ⟨c1, c2⟩
    · obtain ⟨c1, c2⟩ := hsupp _ h1
      rw [abs_of_pos (by linarith)]
      exact ⟨c1, c2⟩
  · intro t
    dsimp only
    by_cases h1 : b t = 0
    · by_cases h2 : b (-t) = 0
      · simp [h1, h2]
      · obtain ⟨c1, _⟩ := hsupp _ h2
        rw [h1, zero_sub]
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr b.nonneg) (by linarith)
    · obtain ⟨c1, _⟩ := hsupp _ h1
      have h2 : b (-t) = 0 := by
        by_contra h2; obtain ⟨c3, _⟩ := hsupp _ h2; linarith
      rw [h2, sub_zero]
      exact mul_nonneg b.nonneg (by linarith)
  · have h1 : b ((A + B) / 2) = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self
      b.rIn_pos.le)
    have h2 : b (-((A + B) / 2)) = 0 := by
      by_contra h2; obtain ⟨c3, _⟩ := hsupp _ h2; linarith
    simp [h1, h2]

private theorem traceFormula_false_localPos {K : Type*} [NormedField K]
    {_ : MeasurableSpace Kˣ} [BorelSpace Kˣ] (μ : Measure Kˣ) [μ.IsInvInvariant]
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (f : Kˣ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hodd : ∀ u, f u⁻¹ = -f u)
    (hsign : ∀ u, 0 ≤ f u * (‖(u : K)‖ - 1)) (ρ : ℝ) (hρ : 1 < ρ)
    (hz : ∀ u : Kˣ, ρ⁻¹ < ‖(u : K)‖ → ‖(u : K)‖ < ρ → f u = 0) (u₀ : Kˣ) (hu₀ : f u₀ ≠ 0) :
    0 < (∫ u, (f u : ℂ) * (‖(u : K)‖ : ℂ) / (‖1 - (u : K)‖ : ℂ) ∂μ).re := by
  have hnc : Continuous (fun u : Kˣ ↦ ‖(u : K)‖) := continuous_norm.comp Units.continuous_val
  let F1 : Kˣ → ℝ := fun u ↦ f u * (‖(u : K)‖ / ‖1 - (u : K)‖)
  let F2 : Kˣ → ℝ := fun u ↦ f u / ‖1 - (u : K)‖
  have hF1 : Continuous F1 := by
    refine continuous_iff_continuousAt.mpr fun u ↦ ?_
    by_cases hu : (u : K) = 1
    · have hopen : IsOpen {x : Kˣ | ρ⁻¹ < ‖(x : K)‖ ∧ ‖(x : K)‖ < ρ} :=
        (isOpen_lt continuous_const hnc).inter (isOpen_lt hnc continuous_const)
      have hev : F1 =ᶠ[nhds u] fun _ ↦ 0 := by
        filter_upwards [hopen.mem_nhds (show u ∈ {x : Kˣ | ρ⁻¹ < ‖(x : K)‖ ∧ ‖(x : K)‖ < ρ} by
          simp only [mem_ofPred_eq, hu, norm_one]; exact ⟨inv_lt_one_of_one_lt₀ hρ, hρ⟩)]
          with x hx
        simp [F1, hz x hx.1 hx.2]
      exact (continuousAt_congr hev).mpr continuousAt_const
    · have hne : ‖1 - (u : K)‖ ≠ 0 := by
        rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h ↦ hu h.symm
      exact hf.continuousAt.mul (hnc.continuousAt.div
        (continuous_norm.comp (continuous_const.sub Units.continuous_val)).continuousAt hne)
  have hF1c : HasCompactSupport F1 := hfc.mul_right
  have hF1i : Integrable F1 μ := hF1.integrable_of_hasCompactSupport hF1c
  have hinv (u : Kˣ) : F1 u⁻¹ = -F2 u := by
    simp only [F1, F2, hodd, Units.val_inv_eq_inv_val, norm_inv]
    have hu0 : ‖(u : K)‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
    have h1 : 1 - (u : K)⁻¹ = -((1 - (u : K)) / (u : K)) := by
      field_simp; ring
    rw [h1, norm_neg, norm_div]
    by_cases h0 : ‖1 - (u : K)‖ = 0
    · simp [h0]
    · field_simp
  have hF2 : F2 = fun u ↦ -F1 u⁻¹ := by funext u; rw [hinv, neg_neg]
  have hF2i : Integrable F2 μ := by rw [hF2]; exact hF1i.comp_inv.neg
  have hI2 : ∫ u, F2 u ∂μ = -∫ u, F1 u ∂μ := by
    rw [hF2, integral_neg, integral_inv_eq_self (fun u ↦ F1 u) μ]
  let G : Kˣ → ℝ := fun u ↦ F1 u - F2 u
  have hGc : Continuous G := by
    refine hF1.sub ?_
    rw [hF2]; exact (hF1.comp continuous_inv).neg
  have hGe (u : Kˣ) : G u = f u * (‖(u : K)‖ - 1) / ‖1 - (u : K)‖ := by
    simp only [G, F1, F2]; ring
  have hGs : HasCompactSupport G := by
    refine hfc.mono fun u hu h0 ↦ hu ?_
    rw [hGe, h0, zero_mul, zero_div]
  have hGn : 0 ≤ G := fun u ↦ by rw [hGe]; exact div_nonneg (hsign u) (norm_nonneg _)
  have hG0 : G u₀ ≠ 0 := by
    have hn1 : ‖(u₀ : K)‖ ≠ 1 := by
      intro h1
      exact hu₀ (hz u₀ (by rw [h1]; exact inv_lt_one_of_one_lt₀ hρ) (by rw [h1]; exact hρ))
    have hne : ‖1 - (u₀ : K)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h; apply hn1; rw [← h, norm_one]
    rw [hGe]
    exact div_ne_zero (mul_ne_zero hu₀ (sub_ne_zero.mpr hn1)) hne
  have hpos := hGc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μ) hGs hGn hG0
  have hGI : ∫ u, G u ∂μ = 2 * ∫ u, F1 u ∂μ := by
    simp only [G]
    rw [integral_sub hF1i hF2i, hI2]; ring
  have hC : (fun u ↦ (f u : ℂ) * (‖(u : K)‖ : ℂ) / (‖1 - (u : K)‖ : ℂ)) =
      fun u ↦ ((F1 u : ℝ) : ℂ) := by
    funext u; simp only [F1]; push_cast; ring
  rw [hC, integral_complex_ofReal, Complex.ofReal_re]
  linarith


/-- A continuous homomorphism into the reals kills every compact subgroup. -/
private theorem traceFormula_false_compact_le_ker {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (L : G →* Multiplicative ℝ) (hL : Continuous L)
    {k : Subgroup G} (hk : IsCompact (k : Set G)) : k ≤ L.ker := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((hk.image
    ((show Continuous (Multiplicative.toAdd : Multiplicative ℝ → ℝ) from continuous_id).comp
      hL)).isBounded)
  intro x hx
  rw [MonoidHom.mem_ker]
  by_contra h
  have hne : (L x).toAdd ≠ 0 := h
  have hxpos : 0 < |(L x).toAdd| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |(L x).toAdd|)
  have hbound := hC (L (x ^ n)).toAdd ⟨x ^ n, k.pow_mem hx n, rfl⟩
  rw [map_pow, toAdd_pow, nsmul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hxpos).mp hn)

/-- On each fiber of an elementary group, a smooth function of a real-valued
continuous homomorphism is smooth in the cover coordinates. -/
private theorem traceFormula_false_contDiff_elementary {m n r : ℕ} {E : Type} [AddCommGroup E]
    [TopologicalSpace E] [DiscreteTopology E]
    (ψ : Multiplicative (ElementaryLieGroup m n r E) →* Multiplicative ℝ) (hψ : Continuous ψ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) (z : Fin r → ℤ) (b : E) {p : ℕ∞} :
    ContDiff ℝ p (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) := by
  let c : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ElementaryLieGroup m n r E :=
    { toFun := fun xt ↦ elementaryCover xt 0 0
      map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
      map_add' := fun x y ↦ Prod.ext rfl
        (Prod.ext (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm) }
  have hc : Continuous c :=
    continuous_fst.prodMk
      ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
        ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const)
  let ℓ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ℝ :=
    (MonoidHom.toAdditive ψ).comp c
  have hℓ : Continuous ℓ := hψ.comp hc
  have hshift u : c u + elementaryCover 0 z b = elementaryCover u z b := by
    change elementaryCover u 0 0 + elementaryCover 0 z b = elementaryCover u z b
    refine Prod.ext (add_zero _) (Prod.ext (funext fun i ↦ ?_) (Prod.ext (zero_add _) (zero_add _)))
    change ((u.2 i : ℝ) : AddCircle (1 : ℝ)) + (((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) :
      AddCircle (1 : ℝ)) = ((u.2 i : ℝ) : AddCircle (1 : ℝ))
    rw [show ((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) = 0 from rfl, AddCircle.coe_zero, add_zero]
  have heq u : (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd =
      ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd := by
    rw [← hshift u, ofAdd_add, map_mul, toAdd_mul]
    rfl
  rw [show (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) =
      fun u ↦ H (ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd) from
    funext fun u ↦ by rw [heq u]]
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    Prod.continuousSMul
  have hlin : ContDiff ℝ p (fun u ↦ ℓ u) := (ℓ.toRealLinearMap hℓ).contDiff
  exact (hH.of_le (by exact_mod_cast le_top)).comp (hlin.add contDiff_const)

/-- A smooth function of a continuous real-valued homomorphism is Bruhat smooth. -/
private theorem traceFormula_false_bruhatSmooth {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (L : G →* Multiplicative ℝ) (hL : Continuous L)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H) :
    IsBruhatSmooth (fun g ↦ H (L g).toAdd) := by
  obtain ⟨k, hk, _, _⟩ := isBruhatContDiff_zero (G := G) 0
  have hker : k ≤ L.ker := traceFormula_false_compact_le_ker L hL hk.isCompact
  intro p
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · show H (L (h.val * x)).toAdd = H (L x).toAdd
    rw [map_mul, MonoidHom.mem_ker.mp (hker h.property), one_mul]
  · let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let q : a.quotient →* Multiplicative ℝ :=
      QuotientGroup.lift N (L.comp a.val.1.subtype) (fun x hx ↦ hker (ha ▸ hx))
    have hq : Continuous q := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (hL.comp continuous_subtype_val)
    refine ⟨fun x ↦ H (q x).toAdd, fun x ↦ rfl, fun e z b ↦ ?_⟩
    exact traceFormula_false_contDiff_elementary (q.comp e.equiv.symm.toMulEquiv.toMonoidHom)
      (hq.comp e.equiv.symm.continuous) hH z b

private theorem traceFormula_false_unitsPos (u : ℝ≥0ˣ) : (0 : ℝ) < ((u : ℝ≥0) : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr u.ne_zero)

/-- A smooth compactly supported function of the logarithm of the norm is a test function. -/
private theorem traceFormula_false_normTest (F : Type) [Field F] [NumberField F]
    (g : ℝ → ℂ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) :
    ∃ φ : BruhatCompactSupport C[F],
      ∀ x, φ.val x = g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)) := by
  let L : C[F] →* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
          (traceFormula_false_unitsPos _).ne' (traceFormula_false_unitsPos _).ne', ofAdd_add] }
  have hL : Continuous L := by
    have hc : Continuous (fun x : C[F] ↦ ((ideleClassNorm F x : ℝ≥0) : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp
        (isProperMap_ideleClassNorm F).continuous)
    exact continuous_ofAdd.comp (hc.log fun x ↦ (traceFormula_false_unitsPos _).ne')
  have hs := traceFormula_false_bruhatSmooth L hL hg
  have hcs : HasCompactSupport (fun x : C[F] ↦ g (L x).toAdd) := by
    let E : ℝ → ℝ≥0ˣ := fun t ↦
      Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
    have hE : Continuous E := Units.continuous_iff.mpr
      ⟨continuous_real_toNNReal.comp Real.continuous_exp,
        (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun t ↦
          (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'⟩
    have hK : IsCompact (E '' tsupport g) := hgc.isCompact.image hE
    refine HasCompactSupport.intro ((isProperMap_ideleClassNorm F).isCompact_preimage hK)
      fun x hx ↦ image_eq_zero_of_notMem_tsupport fun hmem ↦ hx ⟨_, hmem, ?_⟩
    apply Units.ext
    change (Real.exp (Real.log _)).toNNReal = _
    rw [Real.exp_log (traceFormula_false_unitsPos _), Real.toNNReal_coe]
  exact ⟨(⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hs, hcs⟩ :
    bruhatCompactSupportSubmodule C[F]), fun _ ↦ rfl⟩

private theorem traceFormula_false_field :
    ∀ w : InfinitePlace (CyclotomicField 4 ℚ), w.IsComplex := by
  have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) := by
    convert! CyclotomicField.isCyclotomicExtension 4 ℚ using 1
  exact (IsCyclotomicExtension.Rat.isTotallyComplex (CyclotomicField 4 ℚ) (n := 4)
    (by decide)).isComplex

/-- For a test odd under inversion, inverting the quasi-character negates the Mellin value. -/
private theorem traceFormula_false_mellin_inv (F : Type) [Field F] [NumberField F]
    (φ : BruhatCompactSupport C[F]) (hφ : ∀ g, φ.val g⁻¹ = -φ.val g)
    (c c' : QuasiCharacter C[F]) (hc : ∀ g, c' g = c g⁻¹) : M[F](φ, c') = -M[F](φ, c) := by
  have hM (c : QuasiCharacter C[F]) :
      M[F](φ, c) = ∫ g, φ.val g * c g ∂ideleClassTamagawaMeasure F := by
    unfold modulatedFourierMellin
    rw [Set.indicator_of_mem (by simp [relativeVerticalStrip])]
  rw [hM, hM, ← integral_inv_eq_self _ (ideleClassTamagawaMeasure F), ← integral_neg]
  congr 1
  funext g
  rw [hφ, hc, inv_inv]
  ring

private theorem traceFormula_false_twist_inv (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (r : ℂ) (g : C[F]) :
    ideleClassNormTwist χ⁻¹ (-r) g = ideleClassNormTwist χ r g⁻¹ := by
  change (((χ⁻¹ g : Circle)) : ℂ) * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-r) =
    ((χ g⁻¹ : Circle) : ℂ) * ((((ideleClassNorm F g⁻¹ : ℝ≥0) : ℝ)) : ℂ) ^ r
  have hx := traceFormula_false_unitsPos (ideleClassNorm F g)
  have harg : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [map_inv χ g, map_inv (ideleClassNorm F) g, Units.val_inv_eq_inv_val, NNReal.coe_inv,
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  congr 1

private theorem traceFormula_false_ord (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (s : ℂ) : ord(χ⁻¹, 1 - s) = ord(χ, s) := by
  obtain ⟨hL, hLh⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hDh⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hεne, hfun⟩ :=
    completedHeckeL_continuation_functionalEquation χ _ _ hL hLh hD hDh
  have hcomp : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) s =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - s) := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) s := by fun_prop
    have hd : deriv (fun s : ℂ ↦ 1 - s) s ≠ 0 := by simp
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹) ha hd
  have hεord : meromorphicOrderAt ε s = 0 :=
    ((hε.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr (hεne s)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) = ε * continuedCompletedHeckeL χ from
      funext hfun, meromorphicOrderAt_mul (hε.analyticAt s).meromorphicAt
      (hL (mem_univ _)).meromorphicAt, hεord, zero_add] at hcomp
  rw [MeromorphicOn.divisor_apply hD.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← hcomp]

private theorem traceFormula_false_zeroSum {X : Type*} (ι : X → X) (hι : ∀ x, ι (ι x) = x)
    (Z : Set X) (hZ : ∀ x ∈ Z, ι x ∈ Z) (G : X → ℂ) (hG : ∀ x ∈ Z, G (ι x) = -G x) {S : ℂ}
    (h : HasSum (fun z : Z ↦ G z) S) : S = 0 := by
  let e : Z ≃ Z :=
    { toFun := fun z ↦ ⟨ι z, hZ z z.2⟩
      invFun := fun z ↦ ⟨ι z, hZ z z.2⟩
      left_inv := fun z ↦ Subtype.ext (hι z)
      right_inv := fun z ↦ Subtype.ext (hι z) }
  exact traceFormula_false_hasSum_zero _ e (fun z ↦ hG z z.2) h

private theorem traceFormula_false_final {Mp Mm A Fs : ℂ} (h : Mp + Mm - (A + Fs) = 0)
    (h1 : Mm = -Mp) (h2 : Fs = 0) : A = 0 := by
  subst h2; rw [h1] at h; linear_combination -h

private theorem traceFormula_false_sign (h : ℝ → ℝ) (hsign : ∀ t, 0 ≤ h t * t) {x : ℝ}
    (hx : 0 < x) : 0 ≤ h (Real.log (x ^ 2)) * (x - 1) := by
  have hs := hsign (Real.log (x ^ 2))
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · have hl : Real.log (x ^ 2) < 0 := Real.log_neg (by positivity) (by nlinarith)
    have : h (Real.log (x ^ 2)) ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    nlinarith
  · rw [h1, sub_self, mul_zero]
  · have hl : 0 < Real.log (x ^ 2) := Real.log_pos (by nlinarith)
    have : 0 ≤ h (Real.log (x ^ 2)) := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    nlinarith

private theorem traceFormula_false_nearOne (h : ℝ → ℝ)
    (hsupp : ∀ t, h t ≠ 0 → Real.log (9 / 4) < |t| ∧ |t| < Real.log (11 / 4)) {x : ℝ}
    (h1 : (3 / 2 : ℝ)⁻¹ < x) (h2 : x < 3 / 2) : h (Real.log (x ^ 2)) = 0 := by
  by_contra hne
  have hA := (hsupp _ hne).1
  have hx : 0 < x := lt_trans (by norm_num) h1
  have hlt : Real.log (x ^ 2) < Real.log (9 / 4) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  have hgt : -Real.log (9 / 4) < Real.log (x ^ 2) := by
    rw [← Real.log_inv]
    exact Real.log_lt_log (by norm_num) (by norm_num at h1 ⊢; nlinarith)
  have := abs_lt.mpr ⟨hgt, hlt⟩
  linarith

private theorem traceFormula_false_adicNorm (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ∃ k : ℤ, ‖(u : v.adicCompletion F)‖ = ((v.asIdeal.absNorm : ℕ) : ℝ) ^ k := by
  refine ⟨WithZero.log (Valued.v (u : v.adicCompletion F)), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
    (Valued.v.ne_zero_iff.mpr u.ne_zero)]
  simp

private theorem traceFormula_false_sum_ne {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hs : s.Nonempty) (hpos : ∀ i ∈ s, 0 < (f i).re) : ∑ i ∈ s, f i ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  exact (Finset.sum_pos hpos hs).ne' hre

private theorem traceFormula_false_dual_zero {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (L : StrongDual ℂ (BruhatCompactSupport G)) (x : BruhatCompactSupport G)
    (hx : ∀ u, x.val u = 0) : L x = 0 := by
  have : x = 0 := Subtype.ext (funext hx)
  rw [this, map_zero]

private theorem traceFormula_false_of_complex (F : Type) [Field F] [NumberField F]
    (hcx : ∀ w : InfinitePlace F, w.IsComplex) (hP : Printed.traceFormula) : False := by
  obtain ⟨h, hh, hhc, hodd, hsupp, hsign, t₁, ht₁⟩ := traceFormula_false_bump
  have h0 : h 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
  obtain ⟨φ, hφ⟩ := traceFormula_false_normTest F (fun t ↦ (h t : ℂ))
    (Complex.ofRealCLM.contDiff.comp hh) (hhc.comp_left Complex.ofReal_zero)
  have hφinv (g : C[F]) : φ.val g⁻¹ = -φ.val g := by
    rw [hφ, hφ, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, hodd,
      Complex.ofReal_neg]
  have hφ1 : ∀ g : (ideleClassNorm F).ker, φ.val g = 0 := fun g ↦ by
    rw [hφ, MonoidHom.mem_ker.mp g.2]; simp [h0]
  let τ : ℝ≥0ˣ →ₜ* C[F] :=
    ⟨(QuotientGroup.mk' _).comp (canonicalIdeleNormSection F),
      continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous _)⟩
  obtain ⟨a, b, ha, hb, _, hS⟩ :=
    hP F τ (canonicalIdeleNormSection_rightInverse _) φ hφ1 1 one_pos
  have hpos (v : HeightOneSpectrum (𝓞 F)) : 0 < v.asIdeal.absNorm :=
    zero_lt_one.trans (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  refine absurd (traceFormula_false_final (traceFormula_false_zeroSum
    (X := {χ : PontryaginDual C[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ)
    (fun p ↦ (⟨p.1.val⁻¹, fun t ↦ by
      change (p.1.val (τ t))⁻¹ = 1
      rw [p.1.2 t, inv_one]⟩, 1 - p.2))
    (fun p ↦ Prod.ext (Subtype.ext (inv_inv _)) (sub_sub_cancel 1 p.2))
    {p | 0 < ord(p.1.val, p.2) ∧ |p.2.re - 1 / 2| < 1} ?_
    (fun p ↦ ((ord(p.1.val, p.2) : ℤ) : ℂ) *
      M[F](φ, ideleClassNormTwist p.1.val (p.2 - 1 / 2))) ?_ hS) ?_ ?_) ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := hp
    refine ⟨?_, ?_⟩
    · change 0 < ord(p.1.val⁻¹, 1 - p.2)
      rw [traceFormula_false_ord]
      exact h1
    · change |(1 - p.2).re - 1 / 2| < 1
      rw [Complex.sub_re, Complex.one_re, show 1 - p.2.re - 1 / 2 = -(p.2.re - 1 / 2) by ring,
        abs_neg]
      exact h2
  · intro p _
    dsimp only
    rw [traceFormula_false_ord, traceFormula_false_mellin_inv _ φ hφinv
      (ideleClassNormTwist p.1.val (p.2 - 1 / 2)) _ (fun g ↦ by
        rw [show (1 - p.2 - 1 / 2 : ℂ) = -(p.2 - 1 / 2) by ring]
        exact traceFormula_false_twist_inv _ _ _ g)]
    ring
  · exact traceFormula_false_mellin_inv _ φ hφinv _ _ (fun g ↦ by
      have := traceFormula_false_twist_inv _ (1 : PontryaginDual C[F])
        (1 / 2) g
      rw [inv_one] at this
      rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
      exact this)
  · refine (tsum_congr fun v ↦ ?_).trans tsum_zero
    refine mul_eq_zero_of_right _ (traceFormula_false_dual_zero _ (b v) fun u ↦ ?_)
    rw [hb v u, hφ, ideleClassNorm_ofAdicCompletion]
    obtain ⟨k, hk⟩ := traceFormula_false_adicNorm _ v u
    change ((h (Real.log ‖(u : v.adicCompletion F)‖) : ℝ) : ℂ) = 0
    rw [hk, Complex.ofReal_eq_zero]
    by_contra hne
    exact traceFormula_false_natPow _ k (hpos v) (hsupp _ hne).1 (hsupp _ hne).2
  · refine traceFormula_false_sum_ne _ _ Finset.univ_nonempty (fun w _ ↦ ?_)
    beta_reduce
    have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr (hcx w)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnr), show (1 / (2 * (Real.pi : ℂ))) =
      (((1 / (2 * Real.pi)) : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    refine mul_pos (by positivity) ?_
    let : MeasurableSpace w.Completion := borel _
    let : BorelSpace w.Completion := ⟨rfl⟩
    let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
      infiniteLocalMultiplicativeTamagawaMeasure_haar _ w
    let : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let : SecondCountableTopology w.Completionˣ :=
      (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
    have : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsInvInvariant := inferInstance
    have hN (u : w.Completionˣ) : ((ideleClassNorm _
        (IdeleClassGroup.ofCompletion (𝓞 F) _ w u) : ℝ≥0) : ℝ) =
        ‖(u : w.Completion)‖ ^ 2 := by
      rw [ideleClassNorm_ofCompletion, (hcx w).mult_eq_two]
      simp
    have hval (u : w.Completionˣ) :
        (a w).val u = ((h (Real.log (‖(u : w.Completion)‖ ^ 2)) : ℝ) : ℂ) := by
      rw [ha, hφ, hN]
    simp_rw [hval]
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex (hcx w)
    have hen (x : w.Completion) : ‖e x‖ = ‖x‖ := e.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hcx w))) x
    have hx0 : ‖e.symm (Real.exp (t₁ / 2) : ℂ)‖ = Real.exp (t₁ / 2) := by
      rw [← hen, e.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hx0' : e.symm (Real.exp (t₁ / 2) : ℂ) ≠ 0 := by
      rw [← norm_ne_zero_iff, hx0]; exact (Real.exp_pos _).ne'
    refine traceFormula_false_localPos _
      (fun u : w.Completionˣ ↦ h (Real.log (‖(u : w.Completion)‖ ^ 2)))
      (hh.continuous.comp (((continuous_norm.comp Units.continuous_val).pow 2).log
        fun u ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr u.ne_zero))) ?_ (fun u ↦ ?_)
      (fun u ↦ traceFormula_false_sign h hsign (norm_pos_iff.mpr u.ne_zero)) (3 / 2)
      (by norm_num) (fun u h1 h2 ↦ traceFormula_false_nearOne h hsupp h1 h2)
      (Units.mk0 _ hx0') ?_
    · refine (a w).2.2.mono fun u hu h0 ↦ hu ?_
      have := hval u
      rw [h0, eq_comm, Complex.ofReal_eq_zero] at this
      exact this
    · simp only [Units.val_inv_eq_inv_val, norm_inv, inv_pow, Real.log_inv, hodd]
    · rw [Units.val_mk0, hx0, ← Real.exp_nat_mul, Real.log_exp]
      convert ht₁ using 2
      push_cast; ring

private theorem traceFormula_false_aux : ¬ Printed.traceFormula :=
  traceFormula_false_of_complex (CyclotomicField 4 ℚ) traceFormula_false_field

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Take F = ℚ(i), α = 1, and
φ(g) = h(|g|) − h(|g|⁻¹) for a nonzero nonnegative smooth bump h supported
in (9/4, 11/4). All finite local terms vanish because the two norm intervals
avoid every prime power and its reciprocal. Inversion interchanges the two
pole terms with a minus sign. Only the trivial norm-one character contributes,
and the completed Dedekind zeta functional equation pairs s with 1 − s,
with equal multiplicity and opposite Mellin values in the centered strip.
At the complex place set r = ‖u‖, so |u|ᵥ = r². Inverting the inner annulus
makes the local integral a positive constant times the integral of
h(r²) (r − 1) / ‖1 − u‖ on the outer annulus, which is strictly positive. -/
theorem Printed.traceFormula_false : ¬ Printed.traceFormula := traceFormula_false_aux

end RiemannMasullo
