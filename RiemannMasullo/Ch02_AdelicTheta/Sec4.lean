module

public import RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.AppA_AlgebraicNT.Sec5a
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import RiemannMasullo.ForMathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Small-norm estimates for S-local adelic theta

Masullo, §2.4, pp. 106–116. As in §2.3, the Lean place set records the
finite places only. All archimedean places are included in `SAdeleRing`.
-/

@[expose] public noncomputable section

open Asymptotics Bornology Filter IsDedekindDomain MeasureTheory NumberField Topology
open scoped NNReal

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "classOf" => (QuotientGroup.mk : Iₛ → SIdeleQuotient F S)
local notation "normℝ[" K "," V "]" =>
  fun (g : (SAdeleRing K V)ˣ) ↦ ((Units.val (sIdeleNorm K V g) : ℝ≥0) : ℝ)
local notation "smallNorm[" K "," V "]" => comap normℝ[K, V] (𝓝[>] (0 : ℝ))

-- As in §2.3, the homogeneous operator takes its Haar measure as a parameter.
local instance : MeasurableSpace J₁ := borel _

-- TODO(paper-gap): Lemma 2.4.1.2 prints C in (2.4.1.3) after quantifying Cφ.
-- A coefficient depending only on T, M, N and the bases fails for
-- M = 1, N = 2, a₁ = 2, T = 1 and φ(t) = K on (0, 1), zero for t ≥ 1.
-- At t = 2⁻ⁿ the sum is K n, so the coefficient must be at least K / log 2.

/-- A bounded function with power decay has a single majorant for all decay exponents
between zero and one. -/
private theorem geometric_grid_decay_majorant {N : ℕ} (hN : 1 ≤ N) {φ : ℝ → ℂ}
    {C A T : ℝ} (hC : 0 < C) (hb : ∀ y, 0 < y → ‖φ y‖ ≤ C)
    (hd : ∀ y, T ≤ y → ‖φ y‖ ≤ A * (y ^ N)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ y, 0 < y → ∀ L : ℝ, 1 ≤ L →
      ‖φ y‖ ≤ D * Real.exp (-Real.log y / L) := by
  let D := max (C * max 1 T) A
  have hCD : C ≤ D :=
    (le_mul_of_one_le_right hC.le (le_max_left 1 T)).trans (le_max_left _ _)
  refine ⟨D, hC.trans_le hCD, ?_⟩
  intro y hy L hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rcases le_total y 1 with hy₁ | hy₁
  · have hlog := Real.log_nonpos hy.le hy₁
    exact ((hb y hy).trans hCD).trans (le_mul_of_one_le_right (hC.le.trans hCD)
      (Real.one_le_exp (div_nonneg (neg_nonneg.mpr hlog) hL0.le)))
  · have hlinear : ‖φ y‖ * y ≤ D := by
      by_cases hT : T ≤ y
      · have hpow : y ≤ y ^ N := by simpa using pow_le_pow_right₀ hy₁ hN
        have hdec : ‖φ y‖ ≤ A / y ^ N := by simpa only [div_eq_mul_inv] using hd y hT
        exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans
          (((le_div_iff₀ (pow_pos hy N)).mp hdec).trans (le_max_right _ _))
      · exact (mul_le_mul (hb y hy) ((le_of_not_ge hT).trans (le_max_right _ _)) hy.le hC.le).trans
          (le_max_left _ _)
    calc
      ‖φ y‖ ≤ D * Real.exp (-Real.log y) := by
        rw [Real.exp_neg, Real.exp_log hy, ← div_eq_mul_inv]
        exact (le_div_iff₀ hy).mpr hlinear
      _ ≤ D * Real.exp (-Real.log y / L) := by
        gcongr
        apply (le_div_iff₀ hL0).mpr
        nlinarith [mul_nonneg (Real.log_nonneg hy₁) (sub_nonneg.mpr hL)]

/-- The mass of a geometric series with ratio exp(-b/L) is at most linear in L. -/
private theorem geometric_grid_factor_bound {b L : ℝ} (hb : 0 < b) (hL : 1 ≤ L) :
    (1 - Real.exp (-b / L))⁻¹ ≤ (1 + b⁻¹) * L := by
  have hL0 := zero_lt_one.trans_le hL
  let x := b / L
  have hx : 0 < x := div_pos hb hL0
  have hex : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  calc
    (1 - Real.exp (-b / L))⁻¹ = 1 + (Real.exp x - 1)⁻¹ := by
      rw [neg_div, Real.exp_neg]
      change (1 - (Real.exp x)⁻¹)⁻¹ = _
      field_simp [hex.ne', (Real.exp_pos x).ne']
      ring
    _ ≤ 1 + x⁻¹ := by
      gcongr
      linarith [Real.add_one_le_exp x]
    _ ≤ (1 + b⁻¹) * L := by
      dsimp [x]
      rw [inv_div, one_add_mul, div_eq_inv_mul]
      linarith

/-- The geometric grid estimate, including the zero-dimensional grid. -/
private theorem geometric_grid_log_bound (M N : ℕ) (hN : 1 < N)
    (a : Fin M → ℝ) (ha : ∀ i, 1 < a i) (φ : ℝ → ℂ)
    (hbounded : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ C)
    (hdecay : ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖φ t‖ ≤ A * (t ^ N)⁻¹) :
    ∃ T₀ Cφ : ℝ, 0 < T₀ ∧ 0 < Cφ ∧ ∀ t : ℝ, 0 < t → t < T₀ →
      let term : (Fin M → ℕ) → ℝ := fun k ↦ ‖φ ((∏ i, a i ^ k i) * t)‖
      Summable term ∧ (∑' k, term k) ≤ Cφ * |Real.log t| ^ M := by
  obtain ⟨C, hC, hb⟩ := hbounded
  obtain ⟨A, T, -, -, hd⟩ := hdecay
  obtain ⟨D, hD, hmajor⟩ := geometric_grid_decay_majorant hN.le hC hb hd
  let b (i : Fin M) := Real.log (a i)
  have hbpos (i : Fin M) : 0 < b i := Real.log_pos (ha i)
  have hapos (i : Fin M) : 0 < a i := zero_lt_one.trans (ha i)
  let P := ∏ i, (1 + (b i)⁻¹)
  have hP : 0 < P := Finset.prod_pos fun i _ ↦ by have := hbpos i; positivity
  refine ⟨Real.exp (-1), D * Real.exp 1 * P, Real.exp_pos _, by positivity, ?_⟩
  intro t ht ht₀
  -- Choose the decay exponent 1/L so that the factor from t is exactly exp(1).
  let L := -Real.log t
  have hL : 1 ≤ L := by
    have h := (Real.log_lt_iff_lt_exp ht).mpr ht₀
    dsimp [L]
    linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let q (i : Fin M) := Real.exp (-b i / L)
  let w (k : Fin M → ℕ) := ∏ i, (q i) ^ k i
  have hq (i : Fin M) : q i < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr (hbpos i)) hL0)
  have hw : HasSum w (∏ i, (1 - q i)⁻¹) :=
    hasSum_prod_fin_of_nonneg (fun i n ↦ q i ^ n) _
      (fun i n ↦ pow_nonneg (Real.exp_nonneg _) _)
      (fun i ↦ hasSum_geometric_of_lt_one (Real.exp_nonneg _) (hq i))
  have hpoint (k : Fin M → ℕ) :
      ‖φ ((∏ i, a i ^ k i) * t)‖ ≤ D * Real.exp 1 * w k := by
    have hp : 0 < ∏ i, a i ^ k i := Finset.prod_pos fun i _ ↦ pow_pos (hapos i) _
    refine (hmajor _ (mul_pos hp ht) L hL).trans_eq ?_
    have hlog : -Real.log ((∏ i, a i ^ k i) * t) / L = 1 + ∑ i, (k i : ℝ) * (-b i / L) := by
      rw [Real.log_mul hp.ne' ht.ne', Real.log_prod (fun i _ ↦ (pow_pos (hapos i) _).ne')]
      simp only [Real.log_pow]
      have hterm (i : Fin M) : (k i : ℝ) * (-b i / L) = -((k i : ℝ) * b i) / L := by ring
      simp_rw [hterm]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]
      change -((∑ i, (k i : ℝ) * b i) + Real.log t) / L = _
      have htL : Real.log t = -L := (neg_neg _).symm
      rw [htL]
      field_simp [hL0.ne']
      ring
    rw [hlog, Real.exp_add, Real.exp_sum, mul_assoc]
    simp only [Real.exp_nat_mul, w, q]
  have hsum := hw.mul_left (D * Real.exp 1)
  have hs := hsum.summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hpoint
  refine ⟨hs, (hs.tsum_le_tsum hpoint hsum.summable).trans ?_⟩
  rw [hsum.tsum_eq, abs_of_nonpos (by change Real.log t ≤ 0; dsimp [L] at hL; linarith)]
  change D * Real.exp 1 * (∏ i, (1 - q i)⁻¹) ≤ D * Real.exp 1 * P * L ^ M
  rw [mul_assoc (D * Real.exp 1)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD.le (Real.exp_nonneg _))
  calc
    (∏ i, (1 - q i)⁻¹) ≤ ∏ i, ((1 + (b i)⁻¹) * L) :=
      Finset.prod_le_prod₀ (fun i _ ↦ inv_nonneg.mpr (sub_nonneg.mpr (hq i).le))
        (fun i _ ↦ geometric_grid_factor_bound (hbpos i) hL)
    _ = P * L ^ M := by simp [P, Finset.prod_mul_distrib]

/-- Paper: Lemma 2.4.1.2, p. 107. For a bounded function with power decay
at infinity, the sum of the norms over the multiplicative grid with M bases
greater than one converges and is bounded by a constant times the Mth power
of the absolute log near zero.
Deviation: Equation (2.4.1.3) uses the existentially quantified constant
`Cφ`. The real-domain function is used only at positive arguments, and
summability is explicit. -/
theorem summable_geometric_grid_log_bound (M N : ℕ) (hM : 1 ≤ M) (hN : 1 < N)
    (a : Fin M → ℝ) (ha : ∀ i, 1 < a i) (φ : ℝ → ℂ)
    (hbounded : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ C)
    (hdecay : ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖φ t‖ ≤ A * (t ^ N)⁻¹) :
    ∃ T₀ Cφ : ℝ, 0 < T₀ ∧ 0 < Cφ ∧ ∀ t : ℝ, 0 < t → t < T₀ →
      let term : (Fin M → ℕ) → ℝ := fun k ↦ ‖φ ((∏ i, a i ^ k i) * t)‖
      Summable term ∧ (∑' k, term k) ≤ Cφ * |Real.log t| ^ M := by
  clear hM
  exact geometric_grid_log_bound M N hN a ha φ hbounded hdecay

/-! ## The rational number field -/

section Rat

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

local notation "A" => SAdeleRing ℚ S
local notation "U" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ
local notation "unitAtS" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ S)
    (Subring.subtype (integralAdelesOutside ℚ S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ S)))
local notation "ratNorm" => fun (g : Aˣ) ↦ ((Units.val (sIdeleNorm ℚ S g) : ℝ≥0) : ℝ)
local notation "w" => Rat.infinitePlace

/-- The rational S-idelic norm uses the single real place and all finite places in S. -/
private theorem rat_sIdeleNorm_eq (g : Aˣ) :
    ratNorm g = ‖g.val.1 w‖ * ∏ v : S, ‖g.val.2 v‖ := by
  classical
  let eval : (Aˣ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval g))
  change eval (sIdeleNorm ℚ S) = _
  simp only [sIdeleNorm, map_mul, map_prod]
  rw [Fintype.prod_subsingleton _ w]
  simp only [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  rfl

open scoped Classical in
/-- The archimedean norm of a rational adele is the norm of its unique real coordinate. -/
private theorem rat_arch_norm_eq (x : InfiniteAdeleRing ℚ) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x‖ = ‖x w‖ := by
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace, Finset.sup'_univ_eq_ciSup, ciSup_unique]
  change mixedEmbedding.normAtPlace w _ = _
  rw [mixedEmbedding.normAtPlace_apply_of_isReal Rat.isReal_infinitePlace,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) _

/-- Multiplying by a diagonal S-unit preserves the S-idelic norm. -/
private theorem rat_sIdeleNorm_unit_mul (g : Aˣ) (u : U) :
    ratNorm (unitAtS u * g) = ratNorm g := by
  have hu : sIdeleNorm ℚ S (unitAtS u) = 1 :=
    MonoidHom.mem_ker.mp ((sIdeleNorm_spec ℚ S).2 ⟨u, rfl⟩)
  change ((↑↑(sIdeleNorm ℚ S (unitAtS u * g))) : ℝ) = _
  rw [map_mul, hu, one_mul]

/-- Every finite coordinate of an S-idele is nonzero. -/
private theorem rat_sIdele_finite_ne_zero (g : Aˣ) (v : S) : g.val.2 v ≠ 0 := by
  let ev : A →+* v.val.adicCompletion ℚ :=
    (Pi.evalRingHom _ v).comp (RingHom.snd _ _)
  exact (g.isUnit.map ev).ne_zero

/-- Among diagonal S-unit multiples, the finite norms and the sign of the
rational multiplier determine the multiplier. -/
private theorem rat_sUnit_eq_of_norms (g : Aˣ) {u z : U}
    (hfin : ∀ v : S, ‖(unitAtS u * g).val.2 v‖ = ‖(unitAtS z * g).val.2 v‖)
    (hsign : (0 ≤ (u.val.val : ℚ)) ↔ (0 ≤ (z.val.val : ℚ))) : u = z := by
  have hnorm := (rat_sIdeleNorm_unit_mul S g u).trans (rat_sIdeleNorm_unit_mul S g z).symm
  rw [rat_sIdeleNorm_eq, rat_sIdeleNorm_eq] at hnorm
  simp_rw [hfin] at hnorm
  have hprod := Finset.prod_pos (s := Finset.univ) fun v _ ↦
    norm_pos_iff.mpr (rat_sIdele_finite_ne_zero S (unitAtS z * g) v)
  have hinf := (mul_right_cancel₀ hprod.ne') hnorm
  have harch (ξ : U) :
      ‖(unitAtS ξ * g).val.1 w‖ = |(ξ.val.val : ℚ)| * ‖g.val.1 w‖ := by
    change ‖algebraMap ℚ Rat.infinitePlace.Completion ξ.val.val * g.val.1 w‖ = _
    rw [norm_mul, eq_ratCast (algebraMap ℚ Rat.infinitePlace.Completion),
      InfinitePlace.Completion.Rat.norm_infinitePlace_completion]
  rw [harch, harch] at hinf
  let ev : A →+* Rat.infinitePlace.Completion :=
    (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
  have hne : g.val.1 w ≠ 0 := (g.isUnit.map ev).ne_zero
  have habs : |u.val.val| = |z.val.val| :=
    Rat.cast_injective (mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) hinf)
  apply Units.ext
  apply Subtype.ext
  by_cases hu : 0 ≤ u.val.val
  · rwa [abs_of_nonneg hu, abs_of_nonneg (hsign.mp hu)] at habs
  · have hz : ¬ 0 ≤ z.val.val := mt hsign.mpr hu
    simpa [abs_of_neg (lt_of_not_ge hu), abs_of_neg (lt_of_not_ge hz)] using habs

/-- A nonzero finite coordinate has norm given by an integer power of its
residue field cardinality. -/
private theorem rat_finite_norm_eq_zpow (v : S) (x : v.val.adicCompletion ℚ)
    (hx : x ≠ 0) : ∃ e : ℤ, ‖x‖ = (v.val.asIdeal.absNorm : ℝ) ^ e := by
  refine ⟨WithZero.log (Valued.v x), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
    (Valued.v.ne_zero_iff.mpr hx)]
  simp


/-- Finite norm cutoffs put the translated rational S-units into an integer
grid with a shift independent of the idele. The sign distinguishes opposite units. -/
private theorem rat_sUnit_grid (R : S → ℝ) (e : Fin S.card ≃ S) :
    let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
    ∃ Q : ℝ, 0 < Q ∧ ∀ g : Aˣ,
      let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
      ∃ index : P ↪ Bool × (Fin S.card → ℕ), ∀ u : P,
        ‖(unitAtS u.val * g).val.1 w‖ * Q =
          (∏ i, q i ^ (index u).2 i) * ratNorm g := by
  classical
  let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
  have hq (i) : 1 < q i := by
    simpa only [q, Nat.one_lt_cast] using NumberField.HeightOneSpectrum.one_lt_absNorm (e i).val
  have hqpos (i) : 0 < q i := zero_lt_one.trans (hq i)
  choose N hN using fun i ↦ pow_unbounded_of_one_lt (R (e i)) (hq i)
  let Q := ∏ i, q i ^ N i
  refine ⟨Q, Finset.prod_pos (fun i _ ↦ pow_pos (hqpos i) _), fun g ↦ ?_⟩
  let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
  let y (u : P) := unitAtS u.val * g
  have hdiscrete (u : P) (i : Fin S.card) :
      ∃ a : ℤ, ‖(y u).val.2 (e i)‖ = q i ^ a :=
    rat_finite_norm_eq_zpow S (e i) _ (rat_sIdele_finite_ne_zero S (y u) (e i))
  choose a ha using hdiscrete
  let n (u : P) (i : Fin S.card) : ℕ := (↑(N i) - a u i).toNat
  have hshift (u : P) (i : Fin S.card) :
      ‖(y u).val.2 (e i)‖ * q i ^ n u i = q i ^ N i := by
    have hle : a u i ≤ (N i : ℤ) := by
      apply (zpow_right_strictMono₀ (hq i)).le_iff_le.mp
      rw [← ha u i, zpow_natCast]
      exact (u.property (e i)).trans (hN i).le
    rw [ha, ← zpow_natCast (q i) (n u i), ← zpow_add₀ (hqpos i).ne',
      Int.toNat_sub_of_le hle, add_sub_cancel, zpow_natCast]
  let index : P ↪ Bool × (Fin S.card → ℕ) :=
    ⟨fun u ↦ (decide (0 ≤ (u.val.val.val : ℚ)), n u), by
      intro u z h
      apply Subtype.ext
      apply rat_sUnit_eq_of_norms S g
      · intro v
        obtain ⟨i, rfl⟩ := e.surjective v
        have hn : n u i = n z i := congrFun (congrArg Prod.snd h) i
        apply mul_right_cancel₀ (pow_ne_zero (n u i) (hqpos i).ne')
        rw [hshift u i, hn, hshift z i]
      · exact decide_eq_decide.mp (congrArg Prod.fst h)⟩
  refine ⟨index, fun u ↦ ?_⟩
  have hQ : (∏ v : S, ‖(y u).val.2 v‖) * (∏ i, q i ^ n u i) = Q := by
    rw [← e.prod_comp (fun v ↦ ‖(y u).val.2 v‖), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ ↦ hshift u i)
  change ‖(y u).val.1 w‖ * Q = (∏ i, q i ^ n u i) * ratNorm g
  rw [← hQ, ← mul_assoc, ← rat_sIdeleNorm_eq, rat_sIdeleNorm_unit_mul, mul_comm]

/-- Compact finite support and quadratic archimedean decay suffice for the
logarithmic growth bound on the sum over rational S-units. -/
private theorem rat_sUnit_sum_log_growth (f : A → ℂ) (R : S → ℝ) (B₀ B₂ : ℝ)
    (hR : ∀ x, (¬ ∀ v, ‖x.2 v‖ ≤ R v) → f x = 0)
    (h₀ : ∀ x, ‖f x‖ ≤ B₀)
    (h₂ : ∀ x, ‖f x‖ * ‖x.1 w‖ ^ 2 ≤ B₂) :
    (fun g : Aˣ ↦ ∑' u : U, f (unitAtS u * g).val) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (ratNorm g)| ^ S.card) := by
  classical
  let e : Fin S.card ≃ S := S.equivFin.symm
  let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
  have hq (i) : 1 < q i := by
    simpa only [q, Nat.one_lt_cast] using NumberField.HeightOneSpectrum.one_lt_absNorm (e i).val
  obtain ⟨Q, _, hgrid⟩ := rat_sUnit_grid S R e
  let D := max 1 (max B₀ (B₂ * Q ^ 2))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  let φ (t : ℝ) : ℂ := (D * ((max 1 t) ^ 2)⁻¹ : ℝ)
  have hφ (t : ℝ) : ‖φ t‖ = D * ((max 1 t) ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  obtain ⟨T, C, hT, _, hseries⟩ := geometric_grid_log_bound S.card 2 (by decide) q hq φ
    ⟨D, hD, fun t _ ↦ by
      rw [hφ]
      have hp : 1 ≤ (max 1 t) ^ 2 := one_le_pow₀ (le_max_left _ _)
      exact mul_le_of_le_one_right hD.le ((inv_le_one₀ (zero_lt_one.trans_le hp)).mpr hp)⟩
    ⟨D, 1, hD, zero_lt_one, fun t ht ↦ by rw [hφ, max_eq_right ht]⟩
  refine IsBigO.of_bound (2 * C) (mem_comap.mpr ⟨Set.Ioo 0 T, Ioo_mem_nhdsGT hT, ?_⟩)
  intro g hg
  have hg' : ratNorm g ∈ Set.Ioo 0 T := hg
  obtain ⟨hseriesSummable, hseriesBound⟩ := hseries (ratNorm g) hg'.1 hg'.2
  let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
  obtain ⟨index, hindex⟩ := hgrid g
  let term (u : U) := f (unitAtS u * g).val
  let majorant (k : Fin S.card → ℕ) := ‖φ ((∏ i, q i ^ k i) * ratNorm g)‖
  have hpoint (u : P) : ‖term u.val‖ ≤ majorant (index u).2 := by
    let x := (unitAtS u.val * g).val
    change ‖f x‖ ≤ _
    dsimp only [majorant]
    rw [← hindex u, hφ]
    change ‖f x‖ ≤ D * ((max 1 (‖x.1 w‖ * Q)) ^ 2)⁻¹
    rcases le_total (‖x.1 w‖ * Q) 1 with hx | hx
    · rw [max_eq_left hx, one_pow, inv_one, mul_one]
      exact (h₀ x).trans
        ((le_max_left B₀ (B₂ * Q ^ 2)).trans (le_max_right 1 _))
    · rw [max_eq_right hx, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hx) _)).mpr
      rw [mul_pow, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right (h₂ x) (sq_nonneg Q)).trans
        ((le_max_right B₀ (B₂ * Q ^ 2)).trans (le_max_right 1 _))
  have hs : Summable majorant := hseriesSummable
  have hp : Summable (fun p : Bool × (Fin S.card → ℕ) ↦ majorant p.2) := by
    exact (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
      ⟨fun _ ↦ hs, Summable.of_finite⟩
  have hsub : Summable (fun u : P ↦ ‖term u.val‖) :=
    (hp.comp_injective index.injective).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hpoint
  have hsupport : Function.support (fun u ↦ ‖term u‖) ⊆ P :=
    Function.support_subset_iff'.mpr fun u hu ↦
      norm_eq_zero.mpr (hR _ hu)
  have hall : Summable (fun u ↦ ‖term u‖) := by
    have h := (summable_subtype_iff_indicator (s := P) (f := fun u ↦ ‖term u‖)).mp hsub
    rwa [Set.indicator_eq_self.mpr hsupport] at h
  change ‖∑' u, term u‖ ≤ (2 * C) * ‖|Real.log (ratNorm g)| ^ S.card‖
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  calc
    ‖∑' u, term u‖ ≤ ∑' u, ‖term u‖ := norm_tsum_le_tsum_norm hall
    _ = ∑' u : P, ‖term u.val‖ := (tsum_subtype_eq_of_support_subset hsupport).symm
    _ ≤ ∑' p : Bool × (Fin S.card → ℕ), majorant p.2 :=
      hsub.tsum_le_tsum_of_inj index index.injective (fun _ _ ↦ norm_nonneg _) hpoint hp
    _ = 2 * (∑' k, majorant k) := by
      rw [hp.tsum_prod, tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, two_nsmul, two_mul]
    _ ≤ (2 * C) * |Real.log (ratNorm g)| ^ S.card := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hseriesBound (by positivity)

/-- Paper: Proposition 2.4.1.1, p. 107. Over the rationals the theta
function grows at most as the absolute log norm to the number of finite
places in S, uniformly as the S-idelic norm tends to zero from above. -/
theorem sLocalAdelicTheta_rat_log_growth (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalAdelicTheta ℚ S f g) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by
  have htheta : (fun g : Aˣ ↦ sLocalAdelicTheta ℚ S f g) =
      (fun g : Aˣ ↦ ∑' u : U, f (Multiplicative.ofAdd (unitAtS u * g).val)) :=
    funext (sLocalAdelicTheta_apply ℚ S f)
  rw [htheta]
  obtain ⟨K, hK, hsupport, hdecay⟩ := sAdeleSchwartz_exists_decay_bound ℚ S f
  have hcoord (v : S) : ∃ r : ℝ, ∀ x ∈ K, ‖x v‖ ≤ r :=
    hK.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  choose R hR using hcoord
  obtain ⟨B₀, _, h₀⟩ := hdecay 0
  obtain ⟨B₂, _, h₂⟩ := hdecay 2
  refine rat_sUnit_sum_log_growth S (fun x ↦ f (Multiplicative.ofAdd x)) R B₀ B₂ ?_ ?_ ?_
  · exact fun x hx ↦ hsupport x (fun hxK ↦ hx (fun v ↦ hR v x.2 hxK))
  · intro x
    simpa only [pow_zero, mul_one] using h₀ x
  · intro x
    simpa only [rat_arch_norm_eq x.1] using h₂ x

/-- Haar measure on the norm-one S-idele classes is finite because the quotient norm is proper. -/
private theorem normOneSIdeleQuotient_isFiniteMeasure
    (K : Type*) [Field K] [NumberField K] (V : Finset (HeightOneSpectrum (𝓞 K)))
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm K V))) [Measure.IsHaarMeasure μ] :
    IsFiniteMeasure μ := by
  have hcompact : CompactSpace ↥(MonoidHom.ker (sIdeleQuotientNorm K V)) :=
    isCompact_iff_compactSpace.mp
      ((isProperMap_sIdeleQuotientNorm K V).isCompact_preimage (isCompact_singleton (x := 1)))
  exact ⟨isCompact_univ.measure_lt_top⟩

/-- The homogeneous theta average inherits a bound that depends only on the norm
when its translates by norm-one classes stay in the same norm fiber. -/
private theorem theta_integral_log_growth {I C H : Type*} [Monoid C] [MeasurableSpace H]
    (μ : Measure H) [IsFiniteMeasure μ] (q : I → C) (hq : Function.Surjective q)
    (n : C →* ℝ≥0ˣ) (r : I → ℝ) (hr : ∀ g, r g = (↑↑(n (q g)) : ℝ))
    (u : H → C) (hu : ∀ h, n (u h) = 1) (ω : H → Circle)
    (θ : I → ℂ) (θq : C → ℂ) (hθq : ∀ g, θq (q g) = θ g) (M : ℕ)
    (hθ : θ =O[comap r (𝓝[>] (0 : ℝ))] (fun g ↦ |Real.log (r g)| ^ M)) :
    (fun g ↦ ∫ h, θq (q g * u h) * (ω h : ℂ) ∂μ) =O[comap r (𝓝[>] (0 : ℝ))]
      (fun g ↦ |Real.log (r g)| ^ M) := by
  simp only [isBigO_iff, eventually_comap] at hθ ⊢
  obtain ⟨B, hB⟩ := hθ
  refine ⟨B * μ.real Set.univ, ?_⟩
  filter_upwards [hB] with t ht g hg
  have hpoint (h : H) : ‖θq (q g * u h) * (ω h : ℂ)‖ ≤ B * ‖|Real.log (r g)| ^ M‖ := by
    obtain ⟨k, hk⟩ := hq (q g * u h)
    have heq : r k = r g := by rw [hr k, hr g, hk, map_mul, hu, mul_one]
    simpa only [norm_mul, Circle.norm_coe, mul_one, ← hk, hθq, ← heq] using
      ht k (heq.trans hg)
  exact (norm_integral_le_of_norm_le_const (μ := μ) (.of_forall hpoint)).trans_eq
    (mul_right_comm _ _ _)

/-- Paper: Proposition 2.4.1.1, pp. 107, 110. Over the rationals the same
logarithmic growth bound holds for homogeneous theta for each continuous
character of the norm-one S-idele classes.
Deviation: As in §2.3, the Haar measure on those classes is explicit. -/
theorem sLocalHomogeneousAdelicTheta_rat_log_growth
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S))) [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S)))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalHomogeneousAdelicTheta ℚ S μ ω f (QuotientGroup.mk g)) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by
  have hfinite : IsFiniteMeasure μ := normOneSIdeleQuotient_isFiniteMeasure ℚ S μ
  let q : Aˣ → SIdeleQuotient ℚ S := QuotientGroup.mk
  have hq : Function.Surjective q := QuotientGroup.mk_surjective
  exact theta_integral_log_growth μ q hq (sIdeleQuotientNorm ℚ S) ratNorm
    (fun g ↦ congrArg (fun t : ℝ≥0ˣ ↦ (↑↑t : ℝ)) (sIdeleQuotientNorm_mk ℚ S g).symm)
    Subtype.val (fun h ↦ h.property) (fun h ↦ ω h) (fun g ↦ sLocalAdelicTheta ℚ S f g)
    (sLocalAdelicThetaOnClasses ℚ S f) (sLocalAdelicThetaOnClasses_mk ℚ S f) S.card
    (sLocalAdelicTheta_rat_log_growth S f)

end Rat

-- TODO(paper-gap): The geometric series in (2.4.1.5) has an unrounded
-- lower endpoint, and (2.4.1.8) loses a factor in the power of T. The
-- reduction in (2.4.1.14) changes the local support condition. The
-- application on p. 109 omits S = {∞}, where the S-units are {±1}.
-- TODO(paper-gap): The p. 110 ergodicity assertion fails for S = {∞, p} over ℚ.
-- On Hₚ with nonzero real coordinate, log |x| modulo log p is invariant.
-- Theta can be bounded at zero, for instance when S = {∞} over ℚ. Its
-- Mellin integral there fails to converge uniformly on the entire open
-- right half-plane, even for the real Gaussian with trivial character.

/-! ## The general case -/

local notation "normℝ" => normℝ[F, S]
local notation "smallNorm" => smallNorm[F, S]

-- TODO(paper-gap): In the proof of Theorem 2.4.2.1, (2.4.2.2) leaves x∞
-- free on the right after taking the supremum on the left. Equation
-- (2.4.2.3) fails for the real Gaussian times the local integer indicators
-- at 2 and 3. The count of S-unit multiples in a fixed real annulus
-- outside the ball can grow without bound. The averaged estimate
-- (2.4.2.4) alone does not give a pointwise bound.

section LogGrowth

open scoped Classical

local notation "Uₛ" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ
local notation "unitAtS" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S)))
local notation "sRank" => (Fintype.card (InfinitePlace F) + S.card - 1)

/-- For every translate of the diagonal S-units, the set with all normalized logarithms
bounded above by a common nonnegative cutoff is finite. Its cardinality grows at most
with degree `|S| - 1` in the cutoff and the absolute log of the S-idelic norm. -/
private theorem sUnit_log_box_count :
    ∃ D : ℝ, 0 < D ∧ ∀ (g : Iₛ) (r : ℝ), 0 ≤ r →
      let P : Set Uₛ := {u | ∀ v, sIdeleLog F S (unitAtS u * g) v ≤ r}
      P.Finite ∧ (P.ncard : ℝ) ≤ D * (1 + |Real.log (normℝ g)| + r) ^ sRank := by
  classical
  let V := InfinitePlace F ⊕ S
  let w : V := Sum.inl (Classical.choice (inferInstance : Nonempty (InfinitePlace F)))
  -- The sum of the logarithms determines the omitted coordinate.
  let W := {v : V // v ≠ w}
  let d := Fintype.card W
  have hd : d = sRank := by
    dsimp [d, W]
    rw [Fintype.card_subtype_compl (· = w), Fintype.card_sum, Fintype.card_coe]
    simp
  let n := Fintype.card V
  let δ := (Real.log 2 / 2) / ((n : ℝ) + 1)
  have hδ : 0 < δ := div_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num)) (by positivity)
  let E : Set Uₛ := {u | ‖sIdeleLog F S (unitAtS u)‖ ≤ Real.log 2 / 2}
  have hE : E.Finite := sUnitLog_finite_near_zero F S
  let K := 2 + ((n : ℝ) + 1) / δ
  have hK : 0 < K := by positivity
  refine ⟨(↑E.ncard + 1) * K ^ sRank, by positivity, ?_⟩
  intro g r hr
  let t := Real.log (normℝ g)
  let P : Set Uₛ := {u | ∀ v, sIdeleLog F S (unitAtS u * g) v ≤ r}
  let x (u : P) := sIdeleLog F S (unitAtS u.val * g)
  have hsum (u : P) : ∑ v, x u v = t := by
    have hu : sIdeleNorm F S (unitAtS u.val) = 1 :=
      MonoidHom.mem_ker.mp ((sIdeleNorm_spec F S).2 ⟨u.val, rfl⟩)
    rw [sIdeleLog_sum F S, map_mul, hu, one_mul]
  have hlower (u : P) (v : V) : -|t| - (n : ℝ) * r ≤ x u v := by
    have hrest : ∑ i ∈ Finset.univ.erase v, x u i ≤ (n : ℝ) * r := by
      calc
        _ ≤ ∑ _i ∈ Finset.univ.erase v, r := Finset.sum_le_sum fun i _ ↦ u.property i
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hr
    have h := (Finset.sum_erase_add Finset.univ (x u) (Finset.mem_univ v)).trans (hsum u)
    linarith [neg_abs_le t]
  let a := (-|t| - (n : ℝ) * r) / δ
  let b := r / δ
  let J := Finset.Icc ⌊a⌋ ⌊b⌋
  let cell (u : P) (v : W) : J :=
    ⟨⌊x u v / δ⌋, Finset.mem_Icc.mpr
      ⟨Int.floor_le_floor (div_le_div_of_nonneg_right (hlower u v) hδ.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (u.property v) hδ.le)⟩⟩
  have hsame {u z : P} (h : cell u = cell z) (v : W) :
      |x u v - x z v| ≤ δ := by
    have heq := congrArg Subtype.val (congrFun h v)
    change ⌊x u v / δ⌋ = ⌊x z v / δ⌋ at heq
    have hu := Int.floor_le (x u v / δ)
    have hu' := Int.lt_floor_add_one (x u v / δ)
    have hz := Int.floor_le (x z v / δ)
    have hz' := Int.lt_floor_add_one (x z v / δ)
    rw [heq] at hu hu'
    rw [abs_le]
    constructor
    · have hdiv : (x z v - x u v) / δ ≤ 1 := by rw [sub_div]; linarith
      have hh := (div_le_iff₀ hδ).mp hdiv
      linarith
    · have hdiv : (x u v - x z v) / δ ≤ 1 := by rw [sub_div]; linarith
      have hh := (div_le_iff₀ hδ).mp hdiv
      linarith
  have hclose {u z : P} (h : cell u = cell z) : u.val / z.val ∈ E := by
    have heq : sIdeleLog F S (unitAtS (u.val / z.val)) = x u - x z := by
      apply eq_sub_of_add_eq
      rw [← sIdeleLog_mul F S]
      let ι : Uₛ →* Iₛ := unitAtS
      change sIdeleLog F S (ι (u.val / z.val) * (ι z.val * g)) =
        sIdeleLog F S (ι u.val * g)
      rw [← mul_assoc, ← ι.map_mul, div_mul_cancel]
    change ‖sIdeleLog F S (unitAtS (u.val / z.val))‖ ≤ _
    rw [heq, pi_norm_le_iff_of_nonneg (by positivity)]
    have hnδ : (n : ℝ) * δ ≤ Real.log 2 / 2 := by
      have he : ((n : ℝ) + 1) * δ = Real.log 2 / 2 := by
        dsimp [δ]
        field_simp
      linarith
    intro v
    change |x u v - x z v| ≤ _
    by_cases hv : v = w
    · subst v
      have hrest (y : P) := (Finset.sum_erase_add Finset.univ (x y)
        (Finset.mem_univ w)).trans (hsum y)
      have hw : x u w - x z w = -(∑ i ∈ Finset.univ.erase w, (x u i - x z i)) := by
        rw [Finset.sum_sub_distrib]
        linarith [hrest u, hrest z]
      rw [hw, abs_neg]
      calc
        _ ≤ ∑ i ∈ Finset.univ.erase w, |x u i - x z i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.univ.erase w, δ := Finset.sum_le_sum fun i hi ↦
          hsame h ⟨i, (Finset.mem_erase.mp hi).1⟩
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hδ.le).trans hnδ
    · have hn : (1 : ℝ) ≤ n := by
        exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty V from ⟨w⟩))
      exact (hsame h ⟨v, hv⟩).trans ((le_mul_of_one_le_left hδ.le hn).trans hnδ)
  -- Relative to a representative of its cell, each unit belongs to the fixed finite set E.
  choose anchor hanchor using fun c : Set.range cell ↦ c.property
  let key (u : P) : Set.range cell := ⟨cell u, ⟨u, rfl⟩⟩
  let encode (u : P) : (W → J) × E :=
    (cell u, ⟨u.val / (anchor (key u)).val, hclose (hanchor (key u)).symm⟩)
  have hinj : Function.Injective encode := by
    intro u z h
    have hc : cell u = cell z := congrArg Prod.fst h
    have hk : key u = key z := Subtype.ext hc
    have he := congrArg (fun p : (W → J) × E ↦ p.2.val) h
    change u.val / (anchor (key u)).val = z.val / (anchor (key z)).val at he
    rw [hk] at he
    exact Subtype.ext (div_left_injective he)
  let _ := hE.fintype
  let _ : Finite P := Finite.of_injective encode hinj
  refine ⟨Set.toFinite P, ?_⟩
  have hcard : P.ncard ≤ J.card ^ d * E.ncard := by
    have hle := Nat.card_le_card_of_injective encode hinj
    change Nat.card P ≤ J.card ^ d * Nat.card E
    rw [Nat.card_prod] at hle
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun, d] using hle
  have hJ : (J.card : ℝ) ≤ K * (1 + |t| + r) := by
    have hab : a ≤ b := div_le_div_of_nonneg_right (by nlinarith [abs_nonneg t, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hr] :
      -|t| - (n : ℝ) * r ≤ r) hδ.le
    have hfloor := Int.floor_le_floor hab
    have hnonneg : 0 ≤ ⌊b⌋ + 1 - ⌊a⌋ := by omega
    have hcount : (J.card : ℝ) = (⌊b⌋ : ℝ) + 1 - (⌊a⌋ : ℝ) := by
      rw [Int.card_Icc]
      exact_mod_cast (Int.toNat_of_nonneg hnonneg)
    rw [hcount]
    calc
      _ ≤ b - a + 2 := by linarith [Int.floor_le b, Int.lt_floor_add_one a]
      _ ≤ K * (1 + |t| + r) := by
        dsimp [a, b, K]
        rw [← sub_div]
        have hnum : r - (-|t| - (n : ℝ) * r) ≤ ((n : ℝ) + 1) * (1 + |t| + r) := by
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (abs_nonneg t), abs_nonneg t]
        have hdiv := div_le_div_of_nonneg_right hnum hδ.le
        rw [mul_comm ((n : ℝ) + 1), mul_div_assoc, mul_comm (1 + |t| + r)] at hdiv
        rw [add_mul]
        linarith [abs_nonneg t]
  calc
    (P.ncard : ℝ) ≤ (J.card : ℝ) ^ d * E.ncard := by exact_mod_cast hcard
    _ ≤ (K * (1 + |t| + r)) ^ d * E.ncard :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hJ _) (by positivity)
    _ ≤ (↑E.ncard + 1) * K ^ sRank * (1 + |t| + r) ^ sRank := by
      rw [hd, mul_pow]
      calc
        _ ≤ (K ^ sRank * (1 + |t| + r) ^ sRank) * (↑E.ncard + 1) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
        _ = _ := by ring

set_option quotPrecheck false in
local notation "Aᶠₛ" => (∀ v : S, HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "arch" => InfiniteAdeleRing.ringEquiv_mixedSpace F

/-- Compact support at the finite places and bounds on the unweighted and
first-order weighted archimedean suprema control the theta series. The
constant depends only on the compact set of finite coordinates. -/
private theorem sLocalTheta_log_weighted_bound (K : Set Aᶠₛ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℬₛ) (A : ℝ), 0 ≤ A →
      (∀ x : SAdeleRing F S, x.2 ∉ K → f (Multiplicative.ofAdd x) = 0) →
      (∀ x : SAdeleRing F S, ‖f (Multiplicative.ofAdd x)‖ ≤ A) →
      (∀ x : SAdeleRing F S, ‖f (Multiplicative.ofAdd x)‖ * ‖arch x.1‖ ≤ A) →
      ∀ g : Iₛ, ‖sLocalAdelicTheta F S f g‖ ≤ C * A * (1 + |Real.log (normℝ g)|) ^ sRank := by
  classical
  refine (sUnit_log_box_count F S).elim fun D hDcount ↦ ?_
  have hD := hDcount.1
  have hcount := hDcount.2
  have hcoord (v : S) : ∃ R : ℝ, ∀ y ∈ K, ‖y v‖ ≤ R :=
    hK.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  let R (v : S) := (hcoord v).choose
  have hR (v : S) := (hcoord v).choose_spec
  let H := ∑ v : S, max 0 (R v)
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ ↦ le_max_left _ _
  have hfin (g : Iₛ) (hg : g.val.2 ∈ K) (v : S) :
      sIdeleLog F S g (Sum.inr v) ≤ H := by
    change Real.log ‖g.val.2 v‖ ≤ H
    calc
      _ ≤ ‖g.val.2 v‖ := Real.log_le_self (norm_nonneg _)
      _ ≤ max 0 (R v) := (hR v _ hg).trans (le_max_right _ _)
      _ ≤ H := Finset.single_le_sum (fun _ _ ↦ le_max_left _ _) (Finset.mem_univ v)
  have harch (g : Iₛ) (v : InfinitePlace F) :
      ‖g.val.1 v‖ ≤ ‖arch g.val.1‖ := by
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    apply Finset.le_sup'_of_le _ (Finset.mem_univ v)
    by_cases hv : v.IsReal
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hv, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
        (map_zero _) _).symm.le
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) _).symm.le
  let m (k : ℕ) := ((k : ℝ) + 1) ^ sRank * Real.exp (-(k : ℝ))
  have hm₀ (k : ℕ) : 0 ≤ m k := by dsimp [m]; positivity
  have hm : Summable m := by
    let a (j : ℕ) := (j : ℝ) ^ sRank * Real.exp (-(j : ℝ))
    have ha : Summable a := by
      simpa [a] using Real.summable_pow_mul_exp_neg_nat_mul sRank (r := 1) one_pos
    have hs := ((summable_nat_add_iff (f := a) 1).mpr ha).mul_left (Real.exp 1)
    have he (j : ℕ) : Real.exp 1 * a (j + 1) = m j := by
      dsimp [a, m]
      rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    simpa only [he] using hs
  refine ⟨D * (H + 3) ^ sRank * ∑' k, m k,
    mul_nonneg (by positivity) (tsum_nonneg hm₀), ?_⟩
  intro f A hA hsupport hbound hdecay g
  let x (u : Uₛ) := unitAtS u * g
  let term (u : Uₛ) := ‖f (Multiplicative.ofAdd (x u).val)‖
  have hs : Summable term :=
    (sLocalAdelicTheta_summableUniformlyOn_norm F S f {g} isCompact_singleton).summable
      (by rfl)
  let L := 1 + |Real.log (normℝ g)|
  have hL : 1 ≤ L := by dsimp [L]; linarith [abs_nonneg (Real.log (normℝ g))]
  let y (u : Uₛ) := max 1 ‖arch (x u).val.1‖
  have hy (u : Uₛ) : 1 ≤ y u := le_max_left _ _
  have hypos (u : Uₛ) : 0 < y u := zero_lt_one.trans_le (hy u)
  -- In shell k the majorant decays as exp(-k), and the log cutoff grows linearly.
  let k (u : Uₛ) := ⌊Real.log (y u)⌋₊
  have hterm (u : Uₛ) : term u ≤ A * Real.exp (-(k u : ℝ)) := by
    have hdec : term u * y u ≤ A := by
      rw [show y u = max 1 ‖arch (x u).val.1‖ from rfl, mul_max_of_nonneg _ _ (norm_nonneg _)]
      exact max_le (by simpa [term] using hbound (x u).val) (hdecay (x u).val)
    have hflo : (k u : ℝ) ≤ Real.log (y u) := Nat.floor_le (Real.log_nonneg (hy u))
    calc
      _ ≤ A / y u := (le_div_iff₀ (hypos u)).mpr hdec
      _ = A * Real.exp (-Real.log (y u)) := by
        rw [Real.exp_neg, Real.exp_log (hypos u), div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hflo)) hA
  let r (j : ℕ) := H + 2 * ((j : ℝ) + 1)
  have hr (j : ℕ) : 0 ≤ r j := by dsimp [r]; positivity
  let P (j : ℕ) : Set Uₛ := {u | ∀ v, sIdeleLog F S (x u) v ≤ r j}
  have hP (j : ℕ) : (P j).Finite ∧ ((P j).ncard : ℝ) ≤ D * (L + r j) ^ sRank :=
    hcount g (r j) (hr j)
  have hmem (u : Uₛ) (hu : (x u).val.2 ∈ K) : u ∈ P (k u) := by
    intro v
    rcases v with w | v
    · have hnz : (x u).val.1 w ≠ 0 :=
        (((x u).isUnit.map (RingHom.fst _ _)).map (Pi.evalRingHom _ w)).ne_zero
      have hle : Real.log ‖(x u).val.1 w‖ ≤ Real.log (y u) :=
        Real.log_le_log (norm_pos_iff.mpr hnz) ((harch (x u) w).trans (le_max_right _ _))
      have hlog : Real.log (y u) ≤ (k u : ℝ) + 1 := (Nat.lt_floor_add_one _).le
      have hm : (w.mult : ℝ) ≤ 2 := by
        by_cases hw : w.IsReal
        · simp [hw.mult_eq_one]
        · simp [(InfinitePlace.not_isReal_iff_isComplex.mp hw).mult_eq_two]
      have hmul := mul_le_mul (hle.trans hlog) hm (by positivity : 0 ≤ (w.mult : ℝ))
        (by positivity : 0 ≤ (k u : ℝ) + 1)
      change (w.mult : ℝ) * Real.log ‖(x u).val.1 w‖ ≤ r (k u)
      dsimp [r]
      linarith
    · exact (hfin (x u) hu v).trans (le_add_of_nonneg_right (by positivity))
  let M := D * (H + 3) ^ sRank * A * L ^ sRank
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hweight (j : ℕ) :
      ((P j).ncard : ℝ) * (A * Real.exp (-(j : ℝ))) ≤ M * m j := by
    have hbase : L + r j ≤ L * ((H + 3) * ((j : ℝ) + 1)) := by
      have h₁ : 1 + r j ≤ (H + 3) * ((j : ℝ) + 1) := by
        dsimp [r]
        nlinarith [mul_nonneg hH (Nat.cast_nonneg (α := ℝ) j)]
      calc
        _ ≤ L * (1 + r j) := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (hr j)]
        _ ≤ _ := mul_le_mul_of_nonneg_left h₁ (zero_le_one.trans hL)
    calc
      _ ≤ D * (L + r j) ^ sRank * (A * Real.exp (-(j : ℝ))) :=
        mul_le_mul_of_nonneg_right (hP j).2 (by positivity)
      _ ≤ D * (L * ((H + 3) * ((j : ℝ) + 1))) ^ sRank * (A * Real.exp (-(j : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) hD.le)
          (by positivity)
      _ = _ := by dsimp [M, m]; rw [mul_pow, mul_pow]; ring
  refine (congrArg norm (sLocalAdelicTheta_apply F S f g)).le.trans
    ((norm_tsum_le_tsum_norm hs).trans ?_)
  change (∑' u, term u) ≤ _
  have heq : D * (H + 3) ^ sRank * (∑' j, m j) * A * L ^ sRank = ∑' j, M * m j := by
    rw [tsum_mul_left]
    dsimp [M]
    ring
  refine (hs.tsum_le_of_sum_le (fun t ↦ ?_)).trans heq.ge
  let s := t.filter (fun u ↦ (x u).val.2 ∈ K)
  have hsum : ∑ u ∈ s, term u = ∑ u ∈ t, term u := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun u hu hn ↦ ?_
    exact norm_eq_zero.mpr (hsupport _ fun hk ↦ hn (Finset.mem_filter.mpr ⟨hu, hk⟩))
  refine hsum.ge.trans ((Finset.sum_fiberwise_of_maps_to (g := k) (s := s) (t := s.image k)
    (fun u hu ↦ Finset.mem_image_of_mem k hu) term).ge.trans ?_)
  refine (Finset.sum_le_sum (fun j _ ↦ ?_)).trans
    ((hm.mul_left M).sum_le_tsum (s.image k) (fun j _ ↦ mul_nonneg hM (hm₀ j)))
  have hsub : s.filter (fun u ↦ k u = j) ⊆ (hP j).1.toFinset := by
    intro u hu
    obtain ⟨hu, hk⟩ := Finset.mem_filter.mp hu
    exact (hP j).1.mem_toFinset.mpr (hk ▸ hmem u (Finset.mem_filter.mp hu).2)
  calc
    _ ≤ ∑ u ∈ s with k u = j, A * Real.exp (-(j : ℝ)) :=
      Finset.sum_le_sum fun u hu ↦ (Finset.mem_filter.mp hu).2 ▸ hterm u
    _ ≤ ((P j).ncard : ℝ) * (A * Real.exp (-(j : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ (hP j).1]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
    _ ≤ _ := hweight j

/-- Paper: Theorem 2.4.2.1, p. 111. Below S-idelic norm one, the theta
function is bounded by a constant times the absolute log norm to the
power `|S| - 1`, plus an additive constant. Both constants are uniform
on a bounded set of Schwartz–Bruhat functions. -/
theorem sLocalAdelicTheta_log_growth_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖sLocalAdelicTheta F S f g‖ ≤
        C₁ * |Real.log (normℝ g)| ^ (Fintype.card (InfinitePlace F) + S.card - 1) + C₂ := by
  classical
  let weight (g : Iₛ) := (1 + |Real.log (normℝ g)|) ^ sRank
  have hw (g : Iₛ) : 0 < weight g := by dsimp [weight]; positivity
  let p (g : Iₛ) : Seminorm ℂ ℬₛ :=
    let c : NNReal := ⟨(weight g)⁻¹, inv_nonneg.mpr (hw g).le⟩
    c • (normSeminorm ℂ ℂ).comp ((ContinuousMap.evalCLM ℂ g).toLinearMap.comp
      (sLocalAdelicTheta F S))
  have hp (g : Iₛ) (f : ℬₛ) : p g f = ‖sLocalAdelicTheta F S f g‖ / weight g := by
    change (weight g)⁻¹ * ‖sLocalAdelicTheta F S f g‖ = _
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
  have hbdd : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.mpr fun f ↦ by
    refine (sAdeleSchwartz_exists_decay_bound F S f).elim fun K hK ↦ ?_
    refine (hK.2.2 0).elim fun A₀ hA₀ ↦ ?_
    refine (hK.2.2 1).elim fun A₁ hA₁ ↦ ?_
    refine (sLocalTheta_log_weighted_bound F S K hK.1).elim fun D hD ↦ ?_
    refine ⟨D * (A₀ + A₁), Set.forall_mem_range.mpr fun g ↦ ?_⟩
    refine (hp g f).le.trans ((div_le_iff₀ (hw g)).mpr ?_)
    refine hD.2 f (A₀ + A₁) (add_nonneg hA₀.1 hA₁.1) hK.2.1 (fun x ↦ ?_) (fun x ↦ ?_) g
    · refine le_trans ?_ (le_add_of_nonneg_right hA₁.1)
      simpa only [pow_zero, mul_one] using hA₀.2 x
    · refine le_trans ?_ (le_add_of_nonneg_left hA₀.1)
      simpa only [pow_one] using hA₁.2 x
  -- The normalized evaluations are dominated by one seminorm continuous on every stage.
  let q : Seminorm ℂ ℬₛ := ⨆ g, p g
  have hstage (a : BruhatStructuralPair (Multiplicative (SAdeleRing F S)))
      (e : ElementaryLCAPresentation a.quotient) :
      Continuous (q ∘ schwartzBruhatStageInclusion a e) := by
    refine (sAdeleStage_exists_compact_finite F S a).elim fun K hK ↦ ?_
    refine (sLocalTheta_log_weighted_bound F S K hK.1).elim fun D hD ↦ ?_
    refine (sAdeleStage_arch_decay_seminorm F S a e 0).elim fun r₀ hr₀ ↦ ?_
    refine (sAdeleStage_arch_decay_seminorm F S a e 1).elim fun r₁ hr₁ ↦ ?_
    let c : NNReal := ⟨D, hD.1⟩
    let r : Seminorm ℂ (SchwartzBruhatStage e) := c • (r₀ + r₁)
    have hr : Continuous r := continuous_const.mul (hr₀.1.add hr₁.1)
    apply Seminorm.continuous_of_le (p := q.comp (schwartzBruhatStageInclusion a e)) hr
    intro s
    let f : ℬₛ := schwartzBruhatStageInclusion a e s
    have hval (x : SAdeleRing F S) :
        f (Multiplicative.ofAdd x) = schwartzBruhatStageRealization a e s (Multiplicative.ofAdd x) :=
      schwartzBruhatStageInclusion_apply a e s _
    change q f ≤ D * (r₀ s + r₁ s)
    refine (Seminorm.iSup_apply hbdd).trans_le (ciSup_le fun g ↦ ?_)
    refine (hp g f).le.trans ((div_le_iff₀ (hw g)).mpr ?_)
    refine hD.2 f (r₀ s + r₁ s)
      (add_nonneg (apply_nonneg r₀ s) (apply_nonneg r₁ s)) ?_ ?_ ?_ g
    · intro x hx
      exact (hval x).trans ((schwartzBruhatStageRealization_apply a e s
        (Multiplicative.ofAdd x)).trans (dite_eq_right (fun h ↦ hx (hK.2 (Multiplicative.ofAdd x) h))))
    · intro x
      refine (congrArg norm (hval x)).le.trans
        (le_trans ?_ (le_add_of_nonneg_right (apply_nonneg r₁ s)))
      simpa only [pow_zero, mul_one] using hr₀.2 s x
    · intro x
      refine (congrArg (fun z : ℂ ↦ ‖z‖ * ‖arch x.1‖) (hval x)).le.trans
        (le_trans ?_ (le_add_of_nonneg_left (apply_nonneg r₀ s)))
      simpa only [pow_one] using hr₁.2 s x
  let i : {r : Seminorm ℂ (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))) //
      ∀ (a : BruhatStructuralPair (Multiplicative (SAdeleRing F S)))
        (e : ElementaryLCAPresentation a.quotient), Continuous (r ∘ schwartzBruhatStageInclusion a e)} :=
    ⟨q, hstage⟩
  refine (((withGeneratingSeminorms_spec _ _).isVonNBounded_iff_seminorm_bounded.mp hB) i).elim
    fun C hC ↦ ?_
  refine ⟨C * 2 ^ (sRank - 1), C * 2 ^ (sRank - 1), by have := hC.1; positivity,
    by have := hC.1; positivity, ?_⟩
  intro f hf g _
  have hq : p g f ≤ q f := (le_ciSup hbdd g) f
  have hCf : q f ≤ C := (hC.2 f hf).le
  have hmain := (div_le_iff₀ (hw g)).mp ((hp g f).symm.trans_le (hq.trans hCf))
  calc
    _ ≤ C * weight g := hmain
    _ ≤ C * (2 ^ (sRank - 1) * (1 ^ sRank + |Real.log (normℝ g)| ^ sRank)) :=
      mul_le_mul_of_nonneg_left (add_pow_le zero_le_one (abs_nonneg _) _) hC.1.le
    _ = _ := by rw [one_pow]; ring

end LogGrowth

/-! ## Order of growth -/

variable (ε : ℝ) (hε : 0 < ε)

include hε

-- TODO(paper-gap): The derivative of φ(t, g) on p. 113 drops g and ω(g).
-- In (2.4.3.3) the supremum is unweighted since |g′| = 1. It can be
-- infinite, as for the Gaussian example at (2.4.2.3).

/-- A logarithmic majorant for theta gives boundedness after weighting by
a positive power of the norm, as the norm tends to zero. -/
private theorem isBigO_norm_pow_of_log_bound {G : Type*} (ν : G → ℝ) (θ : G → ℂ)
    (n : ℕ) {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (htheta : ∀ g, ν g < 1 → ‖θ g‖ ≤ C₁ * |Real.log (ν g)| ^ n + C₂) :
    (fun g ↦ (ν g ^ ε) • θ g) =O[comap ν (𝓝[>] (0 : ℝ))] (fun _ : G ↦ (1 : ℝ)) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
  have hlog : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖|Real.log t| ^ (n : ℝ)‖ ≤ 1 * ‖t ^ (-ε)‖ :=
    (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n : ℝ) (neg_neg_of_pos hε)).bound zero_lt_one
  have hreal : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      t < 1 ∧ 0 ≤ t ^ ε ∧ t ^ ε * (C₁ * |Real.log t| ^ n + C₂) ≤ C₁ + C₂ := by
    filter_upwards [hsmall, hlog] with t ht hlogt
    have hp : 0 ≤ t ^ ε := Real.rpow_nonneg ht.1.le _
    have hlogle : |Real.log t| ^ n ≤ t ^ (-ε) := by
      rwa [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (abs_nonneg (Real.log t)) n),
        Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le (-ε)), one_mul] at hlogt
    have hweighted : t ^ ε * |Real.log t| ^ n ≤ 1 := calc
      _ ≤ t ^ ε * t ^ (-ε) := mul_le_mul_of_nonneg_left hlogle hp
      _ = 1 := by rw [← Real.rpow_add ht.1, add_neg_cancel, Real.rpow_zero]
    refine ⟨ht.2, hp, ?_⟩
    calc
      t ^ ε * (C₁ * |Real.log t| ^ n + C₂)
          = C₁ * (t ^ ε * |Real.log t| ^ n) + C₂ * t ^ ε := by ring
      _ ≤ C₁ * 1 + C₂ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hweighted hC₁.le)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_one ht.1.le ht.2.le hε.le) hC₂.le)
      _ = C₁ + C₂ := by rw [mul_one, mul_one]
  have hν : Tendsto ν (comap ν (𝓝[>] (0 : ℝ))) (𝓝[>] (0 : ℝ)) := tendsto_comap
  refine IsBigO.of_bound (C₁ + C₂) ((hν.eventually hreal).mono fun g ⟨hlt, hp, hb⟩ ↦ ?_)
  rw [norm_smul, Real.norm_of_nonneg hp, norm_one, mul_one]
  exact (mul_le_mul_of_nonneg_left (htheta g hlt) hp).trans hb

/-- A bound uniform on bounded sets applies to each individual theta input. -/
private theorem isBigO_norm_pow_of_uniform_log_bound
    {G E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [ContinuousSMul ℂ E]
    (ν : G → ℝ) (θ : E → G → ℂ) (n : ℕ)
    (hlog : ∀ B : Set E, IsVonNBounded ℂ B →
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g, ν g < 1 →
        ‖θ f g‖ ≤ C₁ * |Real.log (ν g)| ^ n + C₂)
    (f : E) :
    (fun g ↦ (ν g ^ ε) • θ f g) =O[comap ν (𝓝[>] (0 : ℝ))] (fun _ : G ↦ (1 : ℝ)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, htheta⟩ := hlog {f} (isVonNBounded_singleton (𝕜 := ℂ) f)
  exact isBigO_norm_pow_of_log_bound ε hε ν (θ f) n hC₁ hC₂ (htheta f (Set.mem_singleton f))

/-- Paper: Proposition 2.4.3.1(1), p. 113. Multiplying S-local theta by
any positive real power of the S-idelic norm gives a bounded function
as the norm tends to zero from above. -/
theorem sLocalAdelicTheta_norm_pow_isBigO (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by
  exact isBigO_norm_pow_of_uniform_log_bound (G := Iₛ) (E := ℬₛ) ε hε normℝ
    (fun f g ↦ sLocalAdelicTheta F S f g) (Fintype.card (InfinitePlace F) + S.card - 1)
    (sLocalAdelicTheta_log_growth_bounded F S) f

omit hε in
/-- A norm-power bound on representatives bounds their integral when each integrand
value has the same norm as a representative at the same norm parameter. -/
private theorem norm_pow_isBigO_integral_of_representatives {G K : Type*} [MeasurableSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (r : G → ℝ) (ε : ℝ) (l : Filter ℝ)
    (θ : G → ℂ) (φ : G → K → ℂ)
    (hθ : (fun g ↦ (r g ^ ε) • θ g) =O[comap r l] (fun _ : G ↦ (1 : ℝ)))
    (hlift : ∀ g h, ∃ k, r k = r g ∧ ‖φ g h‖ = ‖θ k‖) :
    (fun g ↦ (r g ^ ε) • (∫ h, φ g h ∂μ)) =O[comap r l] (fun _ : G ↦ (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := hθ.bound
  refine IsBigO.of_bound (C * μ.real Set.univ) (eventually_comap.mpr ?_)
  filter_upwards [eventually_comap.mp hC] with t ht g hgt
  simp only [norm_one, mul_one, ← integral_smul]
  apply norm_integral_le_of_norm_le_const
  refine Eventually.of_forall fun h ↦ ?_
  obtain ⟨k, hk, hnorm⟩ := hlift g h
  simpa only [norm_smul, hk, ← hnorm, norm_one, mul_one] using ht k (hk.trans hgt)

omit hε in
/-- Multiplying an S-idele class by a norm-one class admits a representative
with the original S-idelic norm. -/
private theorem sIdele_exists_representative_mul_norm_one (g : Iₛ) (h : J₁) : ∃ k : Iₛ,
    normℝ k = normℝ g ∧ classOf k = classOf g * h.val := by
  obtain ⟨k, hk⟩ := (QuotientGroup.mk_surjective : Function.Surjective classOf) (classOf g * h.val)
  have hh : sIdeleQuotientNorm F S h.val = 1 := MonoidHom.mem_ker.mp h.property
  let n := sIdeleQuotientNorm F S
  have hn : n (classOf k) = n (classOf g) :=
    (congrArg n hk).trans ((map_mul n (classOf g) h.val).trans
      ((congrArg (n (classOf g) * ·) hh).trans (mul_one _)))
  have hnorm : sIdeleNorm F S k = sIdeleNorm F S g :=
    (sIdeleQuotientNorm_mk F S k).symm.trans (hn.trans (sIdeleQuotientNorm_mk F S g))
  exact ⟨k, congrArg (fun u : ℝ≥0ˣ ↦ (u.val : ℝ)) hnorm, hk⟩

omit hε in
/-- The character-weighted theta integrand has the norm of theta evaluated
at any representative of its argument. -/
private theorem sLocalTheta_char_norm_eq_of_representative (ω : PontryaginDual J₁) (f : ℬₛ)
    (g k : Iₛ) (h : J₁) (hk : classOf k = classOf g * h.val) :
    ‖sLocalAdelicThetaOnClasses F S f (classOf g * h.val) * (ω h : ℂ)‖ =
      ‖sLocalAdelicTheta F S f k‖ := by
  let θ : SIdeleQuotient F S → ℂ := fun c ↦ sLocalAdelicThetaOnClasses F S f c
  let z : ℂ := θ (classOf g * h.val)
  change ‖z * (ω h : ℂ)‖ = ‖sLocalAdelicTheta F S f k‖
  calc
    ‖z * (ω h : ℂ)‖ = ‖z‖ := by rw [norm_mul, Circle.norm_coe, mul_one]
    _ = ‖sLocalAdelicTheta F S f k‖ :=
      congrArg (fun w : ℂ ↦ ‖w‖) ((congrArg θ hk.symm).trans
        (sLocalAdelicThetaOnClasses_mk F S f k))
-- The section-variable linter takes minutes to traverse this proof's S-adelic instance terms.
set_option linter.unusedSectionVars false in
/-- Paper: Proposition 2.4.3.1(1), p. 113. The same small-norm bound
holds for homogeneous theta multiplied by a positive norm power.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_isBigO
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let r : Iₛ → ℝ := normℝ
  let θ : SIdeleQuotient F S → ℂ := fun c ↦ sLocalAdelicThetaOnClasses F S f c
  let θ₀ : Iₛ → ℂ := fun g ↦ sLocalAdelicTheta F S f g
  let χ : J₁ → ℂ := fun h ↦ (ω h : ℂ)
  let φ (g : Iₛ) (h : J₁) : ℂ := θ (classOf g * h.val) * χ h
  have hrep (g : Iₛ) (h : J₁) : ∃ k, r k = r g ∧ ‖φ g h‖ = ‖θ₀ k‖ := by
    obtain ⟨k, hn, hk⟩ := sIdele_exists_representative_mul_norm_one F S g h
    exact ⟨k, hn, sLocalTheta_char_norm_eq_of_representative F S ω f g k h hk⟩
  change (fun g : Iₛ ↦ (r g ^ ε) • (∫ h, φ g h ∂μ)) =O[comap r (𝓝[>] (0 : ℝ))]
    (fun _ : Iₛ ↦ (1 : ℝ))
  exact norm_pow_isBigO_integral_of_representatives μ r ε (𝓝[>] (0 : ℝ))
    θ₀ φ (sLocalAdelicTheta_norm_pow_isBigO F S ε hε f) hrep

-- Scanning the inferred adelic instances for unused section variables is expensive.
set_option linter.unusedSectionVars false in
/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the bound for theta times a positive norm power is uniform on a bounded
set of test functions. -/
theorem sLocalAdelicTheta_norm_pow_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by
  refine (sLocalAdelicTheta_log_growth_bounded F S B hB).elim fun C₁ h₁ ↦ ?_
  refine h₁.elim fun C₂ h₂ ↦ ?_
  have hC₁ := h₂.1
  have hC₂ := h₂.2.1
  have hbound := h₂.2.2
  -- The degree-n term in the exponential series bounds the logarithmic weight.
  have hlog (n : ℕ) (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) :
      t ^ ε * |Real.log t| ^ n ≤ n.factorial / ε ^ n := by
    have htε := Real.rpow_pos_of_pos ht ε
    have hexp : Real.exp (ε * |Real.log t|) = (t ^ ε)⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos ht.le ht₁), Real.rpow_def_of_pos ht,
        ← Real.exp_neg, mul_neg, mul_comm ε (Real.log t)]
    have hp := (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mp
      (Real.pow_div_factorial_le_exp (ε * |Real.log t|) (mul_nonneg hε.le (abs_nonneg _)) n)
    rw [mul_pow, hexp] at hp
    apply (le_div_iff₀ (pow_pos hε n)).mpr
    calc
      t ^ ε * |Real.log t| ^ n * ε ^ n = t ^ ε * (ε ^ n * |Real.log t| ^ n) := by
        rw [mul_assoc, mul_comm (|Real.log t| ^ n)]
      _ ≤ t ^ ε * ((t ^ ε)⁻¹ * n.factorial) := mul_le_mul_of_nonneg_left hp htε.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ htε.ne', one_mul]
  let n := Fintype.card (InfinitePlace F) + S.card - 1
  refine ⟨C₁ * (n.factorial / ε ^ n) + C₂, 1, by positivity, zero_lt_one, ?_⟩
  intro f hf g hg
  let t : ℝ := normℝ g
  have ht : 0 < t := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))
  have htε := Real.rpow_pos_of_pos ht ε
  have htε_le : t ^ ε ≤ 1 := Real.rpow_le_one ht.le hg.le hε.le
  have hweighted : C₁ * (t ^ ε * |Real.log t| ^ n) + t ^ ε * C₂ ≤
      C₁ * (n.factorial / ε ^ n) + C₂ :=
    add_le_add (mul_le_mul_of_nonneg_left (hlog n t ht hg.le) hC₁.le)
      (mul_le_of_le_one_left hC₂.le htε_le)
  change ‖(t ^ ε) • sLocalAdelicTheta F S f g‖ ≤ _
  calc
    _ = t ^ ε * ‖sLocalAdelicTheta F S f g‖ :=
      norm_smul_of_nonneg htε.le (sLocalAdelicTheta F S f g)
    _ ≤ t ^ ε * (C₁ * |Real.log t| ^ n + C₂) :=
      mul_le_mul_of_nonneg_left (hbound f hf g hg) htε.le
    _ = C₁ * (t ^ ε * |Real.log t| ^ n) + t ^ ε * C₂ := by
      rw [mul_add, mul_left_comm (t ^ ε) C₁]
    _ ≤ _ := hweighted

/-- Uniform logarithmic bounds give uniform norm-power bounds for integrals whose
pointwise norms agree with evaluations on representatives of the same norm. -/
private theorem norm_pow_integral_bounded_of_uniform_log_bound {E G K : Type*} [MeasurableSpace K]
    (ν : Measure K) [IsFiniteMeasure ν]
    (r : G → ℝ) (hr : ∀ g, 0 < r g) (θ : E → G → ℂ) (φ : E → G → K → ℂ)
    (A : Set E) (n : ℕ)
    (hlog : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ A, ∀ g, r g < 1 →
      ‖θ f g‖ ≤ C₁ * |Real.log (r g)| ^ n + C₂)
    (hrep : ∀ f g h, ∃ k, r k = r g ∧ ‖φ f g h‖ = ‖θ f k‖) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ A, ∀ g, r g < T →
      ‖(r g ^ ε) • (∫ h, φ f g h ∂ν)‖ ≤ C := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hlog⟩ := hlog
  -- The bound on pairs uses a single constant for all test functions.
  let r' : A × G → ℝ := fun p ↦ r p.2
  let θ' : A × G → ℂ := fun p ↦ θ p.1.val p.2
  let φ' (p : A × G) (h : K) : ℂ := φ p.1.val p.2 h
  have hθ := isBigO_norm_pow_of_log_bound ε hε r' θ' n hC₁ hC₂
    (fun p hp ↦ hlog p.1.val p.1.property p.2 hp)
  have hlift (p : A × G) (h : K) : ∃ q, r' q = r' p ∧ ‖φ' p h‖ = ‖θ' q‖ := by
    obtain ⟨k, hk, hnorm⟩ := hrep p.1.val p.2 h
    exact ⟨(p.1, k), hk, hnorm⟩
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp
    (norm_pow_isBigO_integral_of_representatives ν r' ε (𝓝[>] (0 : ℝ)) θ' φ' hθ hlift)
  obtain ⟨T, hT, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (eventually_comap.mp hbound)
  refine ⟨C, T, hC, hT, fun f hf g hg ↦ ?_⟩
  have hmem : r g ∈ Set.Ioo 0 T := ⟨hr g, hg⟩
  simpa only [norm_one, mul_one] using hcut hmem (⟨f, hf⟩, g) rfl

/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the corresponding homogeneous bound is uniform on a bounded set of test functions.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by
  let : IsFiniteMeasure μ := normOneSIdeleQuotient_isFiniteMeasure F S μ
  let r : Iₛ → ℝ := normℝ
  let θ (f : ℬₛ) (g : Iₛ) : ℂ := sLocalAdelicTheta F S f g
  let φ (f : ℬₛ) (g : Iₛ) (h : J₁) : ℂ :=
    sLocalAdelicThetaOnClasses F S f (classOf g * h.val) * (ω h : ℂ)
  have hrep (f : ℬₛ) (g : Iₛ) (h : J₁) : ∃ k, r k = r g ∧ ‖φ f g h‖ = ‖θ f k‖ := by
    obtain ⟨k, hn, hk⟩ := sIdele_exists_representative_mul_norm_one F S g h
    exact ⟨k, hn, sLocalTheta_char_norm_eq_of_representative F S ω f g k h hk⟩
  change ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g, r g < T →
    ‖(r g ^ ε) • (∫ h, φ f g h ∂μ)‖ ≤ C
  exact norm_pow_integral_bounded_of_uniform_log_bound (E := ℬₛ) (G := Iₛ) (K := J₁) ε hε μ r
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g)))
    θ φ B (Fintype.card (InfinitePlace F) + S.card - 1)
    (sLocalAdelicTheta_log_growth_bounded F S B hB) hrep

/-- Paper: Proposition 2.4.3.1(3), p. 113. The uniform bound for theta
times a positive norm power holds below S-idelic norm one. -/
theorem sLocalAdelicTheta_norm_pow_bounded_threshold_one
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by
  refine (sLocalAdelicTheta_log_growth_bounded F S B hB).elim fun C₁ h₁ ↦ ?_
  refine h₁.elim fun C₂ h₂ ↦ ?_
  have hC₁ := h₂.1
  have hC₂ := h₂.2.1
  have htheta := h₂.2.2
  let n := Fintype.card (InfinitePlace F) + S.card - 1
  let D : ℝ := (n.factorial : ℝ) / ε ^ n
  have hD : 0 < D := by dsimp [D]; positivity
  have hweighted (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) : t ^ ε * |Real.log t| ^ n ≤ D := by
    have hexp : Real.exp (|Real.log t| * ε) = (t ^ ε)⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos ht.le ht₁), neg_mul, Real.exp_neg,
        ← Real.rpow_def_of_pos ht]
    -- Use the nth term of the exponential series to bound the weighted log power.
    have hlog := Real.pow_div_factorial_le_exp (|Real.log t| * ε)
      (mul_nonneg (abs_nonneg (Real.log t)) hε.le) n
    rw [hexp, mul_pow] at hlog
    have hfact : 0 < (n.factorial : ℝ) := by positivity
    have hmul := (le_inv_mul_iff₀ (Real.rpow_pos_of_pos ht ε)).mp ((div_le_iff₀ hfact).mp hlog)
    exact (le_div_iff₀ (pow_pos hε n)).mpr
      ((mul_assoc (t ^ ε) (|Real.log t| ^ n) (ε ^ n)).le.trans hmul)
  have hbound (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) (z : ℂ)
      (hz : ‖z‖ ≤ C₁ * |Real.log t| ^ n + C₂) : ‖(t ^ ε) • z‖ ≤ C₁ * D + C₂ := by
    have htε := (Real.rpow_pos_of_pos ht ε).le
    rw [norm_smul, Real.norm_of_nonneg htε]
    calc
      _ ≤ t ^ ε * (C₁ * |Real.log t| ^ n + C₂) := mul_le_mul_of_nonneg_left hz htε
      _ = C₁ * (t ^ ε * |Real.log t| ^ n) + C₂ * t ^ ε := by
        rw [mul_add, mul_left_comm (t ^ ε) C₁, mul_comm (t ^ ε) C₂]
      _ ≤ C₁ * D + C₂ :=
        add_le_add (mul_le_mul_of_nonneg_left (hweighted t ht ht₁) hC₁.le)
          (mul_le_of_le_one_right hC₂.le (Real.rpow_le_one ht.le ht₁ hε.le))
  refine ⟨C₁ * D + C₂, add_pos (mul_pos hC₁ hD) hC₂, ?_⟩
  intro f hf g hg
  have hgpos : 0 < normℝ g := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))
  exact hbound (normℝ g) hgpos hg.le (sLocalAdelicTheta F S f g) (htheta f hf g hg)

/-- Paper: Proposition 2.4.3.1(3), p. 113. The corresponding uniform
homogeneous bound holds below S-idelic norm one.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded_threshold_one
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by
  let : IsFiniteMeasure μ := normOneSIdeleQuotient_isFiniteMeasure F S μ
  refine (sLocalAdelicTheta_norm_pow_bounded_threshold_one F S ε hε B hB).elim fun C hC ↦ ?_
  refine ⟨C * μ.real Set.univ, mul_pos hC.1 measureReal_univ_pos, fun f hf g hg ↦ ?_⟩
  let φ (h : J₁) := sLocalAdelicThetaOnClasses F S f (classOf g * h.val) * (ω h : ℂ)
  change ‖(normℝ g ^ ε) • (∫ h, φ h ∂μ)‖ ≤ _
  rw [← integral_smul]
  apply norm_integral_le_of_norm_le_const
  refine Eventually.of_forall fun h ↦ ?_
  obtain ⟨k, hk, hclass⟩ := sIdele_exists_representative_mul_norm_one F S g h
  have hnorm : ‖φ h‖ = ‖sLocalAdelicTheta F S f k‖ :=
    sLocalTheta_char_norm_eq_of_representative F S ω f g k h hclass
  calc
    _ = ‖normℝ g ^ ε‖ * ‖φ h‖ := norm_smul _ _
    _ = ‖normℝ k ^ ε‖ * ‖sLocalAdelicTheta F S f k‖ :=
      congrArg₂ (fun t a : ℝ ↦ ‖t ^ ε‖ * a) hk.symm hnorm
    _ = ‖(normℝ k ^ ε) • sLocalAdelicTheta F S f k‖ := (norm_smul _ _).symm
    _ ≤ C := hC.2 f hf k (hk.trans_lt hg)

/-- A bound at half the exponent leaves a positive power tending to zero. -/
private theorem tendsto_norm_pow_of_isBigO_half {G : Type*} (r : G → ℝ) (θ : G → ℂ)
    (hθ : (fun g ↦ (r g ^ (ε / 2)) • θ g) =O[comap r (𝓝[>] (0 : ℝ))]
      (fun _ ↦ (1 : ℝ))) :
    Tendsto (fun g ↦ (r g ^ ε) • θ g) (comap r (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  have hr : Tendsto r (comap r (𝓝[>] (0 : ℝ))) (𝓝[>] 0) := tendsto_comap
  have hhalf := (hr.mono_right nhdsWithin_le_nhds).rpow_const_nhds_zero (half_pos hε)
  refine (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hhalf
    hθ.isBoundedUnder_le).congr' ?_
  filter_upwards [hr.eventually self_mem_nhdsWithin] with g hg
  change (r g ^ (ε / 2)) • ((r g ^ (ε / 2)) • θ g) = (r g ^ ε) • θ g
  rw [smul_smul, ← Real.rpow_add hg, add_halves]

/-- Paper: Corollary 2.4.3.2, p. 115. Theta multiplied by any positive
real power of the S-idelic norm tends to zero as that norm tends to zero. -/
theorem sLocalAdelicTheta_norm_pow_tendsto_zero (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) smallNorm (𝓝 0) := by
  exact tendsto_norm_pow_of_isBigO_half ε hε normℝ (fun g ↦ sLocalAdelicTheta F S f g)
    (sLocalAdelicTheta_norm_pow_isBigO F S (ε / 2) (half_pos hε) f)

/-- Paper: Corollary 2.4.3.2, p. 115. The same vanishing holds for
homogeneous theta for every continuous character of the norm-one classes.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_tendsto_zero
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g))
      smallNorm (𝓝 0) := by
  exact tendsto_norm_pow_of_isBigO_half ε hε normℝ
    (fun g ↦ sLocalHomogeneousAdelicTheta F S μ ω f (classOf g))
    (sLocalHomogeneousAdelicTheta_norm_pow_isBigO F S (ε / 2) (half_pos hε) μ ω f)

end RiemannMasullo
