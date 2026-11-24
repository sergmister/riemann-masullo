module

public import RiemannMasullo.Research.StripNuclearity.HeckeArchimedean

/-! # Character-uniform bounds for the reflected gamma factors on the left line -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain NumberField Set
open scoped ComplexConjugate Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

/-- The archimedean gamma shift for the inverse unitary character is the
complex conjugate of the shift for the original character. -/
theorem heckeArchimedeanShift_inv_conj (χ : U) (v : InfinitePlace F) :
    heckeArchimedeanShift χ⁻¹ v = conj (heckeArchimedeanShift χ v) := by
  classical
  have hInv (x : v.Completionˣ) :
      infinitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ 0) x =
        (infinitePlaceRestriction F v (ideleClassNormTwist χ 0) x)⁻¹ := by
    let g := IdeleClassGroup.ofCompletion (𝓞 F) F v x
    change ((χ⁻¹ g : Circle) : ℂ) * _ ^ (0 : ℂ) = ((χ g : ℂ) * _ ^ (0 : ℂ))⁻¹
    simp only [Complex.cpow_zero, mul_one]
    rfl
  have hc {a : ℂ} (h : a.re = 0) : conj a = -a := by
    apply Complex.ext <;> simp [h]
  by_cases hv : v.IsReal
  · let p := (realHeckeCharacter_parameters χ v hv).exists.choose
    have hp := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
    have he : (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose = (-p.1, p.2) := by
      apply (realHeckeCharacter_parameters χ⁻¹ v hv).unique
        (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
      refine ⟨by simpa [p] using hp.1, fun x ↦ ?_⟩
      dsimp only [p]
      rw [hInv, hp.2 x, mul_inv, Complex.cpow_neg]
      congr 1
      rw [← inv_pow]
      split <;> simp
    have hcp : conj p.1 = -p.1 := hc hp.1
    simp only [heckeArchimedeanShift, dite_eq_left hv]
    change (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose.1 +
      ((realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose.2.val : ℂ) = conj (p.1 + (p.2.val : ℂ))
    rw [he, map_add, hcp, Complex.conj_natCast]
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let p := (complexHeckeCharacter_parameters χ v hv').exists.choose
    have hp := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec
    have he : (complexHeckeCharacter_parameters χ⁻¹ v hv').exists.choose = (-p.1, -p.2) := by
      apply (complexHeckeCharacter_parameters χ⁻¹ v hv').unique
        (complexHeckeCharacter_parameters χ⁻¹ v hv').exists.choose_spec
      refine ⟨by simpa [p] using hp.1, fun x ↦ ?_⟩
      dsimp only [p]
      rw [hInv, hp.2 x, mul_inv, Complex.cpow_neg, zpow_neg]
    have hcp : conj p.1 = -p.1 := hc hp.1
    simp only [heckeArchimedeanShift, dite_eq_right hv]
    change (complexHeckeCharacter_parameters χ⁻¹ v hv').exists.choose.1 +
      ((complexHeckeCharacter_parameters χ⁻¹ v hv').exists.choose.2.natAbs : ℂ) / 2 =
        conj (p.1 + (p.2.natAbs : ℂ) / 2)
    simp only [he, map_add, hcp, map_div₀, map_ofNat, Complex.conj_natCast, Int.natAbs_neg]

private theorem gamma_recurrence_bound (G : ℂ → ℂ) (d : ℕ) (h₀ : G 0 = 0)
    (hstep : ∀ z : ℂ, z ≠ 0 → G (z + d) = G z * z / 2 / Real.pi)
    (z : ℂ) (m : ℕ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ j < m, ‖z + (j : ℂ) * d‖ ≤ B) :
    ‖G (z + (m : ℂ) * d) / G z‖ ≤ B ^ m := by
  by_cases hg : G z = 0
  · simp [hg, hB]
  have aux (j : ℕ) (hj : j ≤ m) : G (z + (j : ℂ) * d) ≠ 0 ∧
      ‖G (z + (j : ℂ) * d)‖ ≤ ‖G z‖ * B ^ j := by
    induction j with
    | zero => simp [hg]
    | succ j ih =>
      obtain ⟨hn, hb⟩ := ih (Nat.le_of_succ_le hj)
      let w := z + (j : ℂ) * d
      have hw : w ≠ 0 := fun he ↦ hn ((congrArg G he).trans h₀)
      have he : z + ((j + 1 : ℕ) : ℂ) * d = w + d := by dsimp [w]; push_cast; ring
      rw [he, hstep w hw]
      refine ⟨div_ne_zero (div_ne_zero (mul_ne_zero hn hw) two_ne_zero)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), ?_⟩
      rw [norm_div, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
        show ‖(2 : ℂ)‖ = 2 by norm_num]
      calc
        _ ≤ ‖G w‖ * ‖w‖ := (div_le_self (by positivity) (by linarith [Real.one_le_pi_div_two])).trans
          (div_le_self (by positivity) (by norm_num))
        _ ≤ (‖G z‖ * B ^ j) * B := mul_le_mul hb (h j hj) (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ, mul_assoc]
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hg), mul_comm (B ^ m) ‖G z‖]
  exact (aux m le_rfl).2

private theorem localGamma_four_bound (realPlace : Prop) [Decidable realPlace] (z : ℂ) :
    let G := fun w ↦ if realPlace then Complex.Gammaℝ w else Complex.Gammaℂ w / 2
    ‖G (z + 4) / G z‖ ≤ (4 + ‖z‖) ^ 4 := by
  have hlocal (j d : ℕ) (h : j * d ≤ 4) : ‖z + (j : ℂ) * d‖ ≤ 4 + ‖z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    linarith [show (j : ℝ) * (d : ℝ) ≤ 4 by exact_mod_cast h]
  by_cases hr : realPlace
  · simp only [hr, ite_true]
    have hb := gamma_recurrence_bound Complex.Gammaℝ 2 (by simp [Complex.Gammaℝ_def])
      (fun w hw ↦ by simpa only [Nat.cast_ofNat] using Complex.Gammaℝ_add_two hw) z 2
      (4 + ‖z‖) (by positivity) (fun j hj ↦ hlocal j 2 (by omega))
    norm_num at hb
    rw [norm_div]
    exact hb.trans (pow_le_pow_right₀ (by linarith [norm_nonneg z]) (by norm_num : 2 ≤ 4))
  · simp only [hr, ite_false, div_div_div_cancel_right₀ (two_ne_zero' ℂ)]
    have hb := gamma_recurrence_bound Complex.Gammaℂ 1 (by simp [Complex.Gammaℂ_def])
      (fun w hw ↦ by simpa only [Nat.cast_one] using Complex.Gammaℂ_add_one hw) z 4
      (4 + ‖z‖) (by positivity) (fun j hj ↦ hlocal j 1 (by omega))
    simpa using hb

/-- Paper: Equations (B.1.1.7)–(B.1.1.11), p. 590. On the line with real part
minus three halves the reflected gamma factors differ by two recurrence steps
at real places and four at complex places. The bound holds at every height
with the character dependence displayed in its archimedean shifts.
Deviation: The page gives a fixed-character asymptotic. The recurrence here
gives a finite-height bound uniform in the character. -/
theorem heckeGammaFactor_left_quotient_bound (χ : U) (s : ℂ) (hs : s.re = -(3 / 2 : ℝ)) :
    ‖heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s‖ ≤
      (6 + |s.im| + ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖) ^
        (4 * Fintype.card (InfinitePlace F)) := by
  classical
  let B := 6 + |s.im| + ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let G (v : InfinitePlace F) (z : ℂ) := if v.IsReal then Complex.Gammaℝ z else Complex.Gammaℂ z / 2
  have hprod (ψ : U) (w : ℂ) : heckeGammaFactor ψ w = ∏ v, G v (w + heckeArchimedeanShift ψ v) := by
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v.IsReal <;> simp [G, heckeArchimedeanShift, hv, add_assoc]
  have hloc (v : InfinitePlace F) :
      ‖G v (1 - s + heckeArchimedeanShift χ⁻¹ v) / G v (s + heckeArchimedeanShift χ v)‖ ≤ B ^ 4 := by
    let b := heckeArchimedeanShift χ v
    have hconj (z : ℂ) : G v (conj z) = conj (G v z) := by
      by_cases hv : v.IsReal <;> simp [G, hv, Complex.Gammaℝ_conj, Complex.Gammaℂ_conj, map_ofNat]
    have hr : (1 - s + heckeArchimedeanShift χ⁻¹ v) = conj ((s + b) + 4) := by
      rw [heckeArchimedeanShift_inv_conj]
      apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, hs, b]
      ring
    rw [hr, hconj, norm_div, Complex.norm_conj, ← norm_div]
    refine (localGamma_four_bound v.IsReal (s + b)).trans (pow_le_pow_left₀ (by positivity) ?_ _)
    have hb : ‖b‖ ≤ ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖ :=
      Finset.single_le_sum (fun v _ ↦ norm_nonneg (heckeArchimedeanShift χ v)) (Finset.mem_univ v)
    have hs' := Complex.norm_le_abs_re_add_abs_im s
    rw [hs] at hs'
    norm_num at hs'
    dsimp only [B]
    linarith [norm_add_le s b]
  rw [hprod χ⁻¹, hprod χ, ← Finset.prod_div_distrib, norm_prod]
  exact (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hloc v)).trans_eq
    (by simp [← pow_mul, Nat.mul_comm, B])

/-- The two reflected finite Hecke functions on the line of real part minus
three halves have a uniform polynomial bound in the height and the shifts.
The hypotheses give the exact completed functional equation and the Euler
bounds at the reflected point. Pairing the character with its inverse cancels
the root number. The formula includes heights at poles of a gamma factor. -/
theorem finiteHecke_pair_left_le_of_functionalEquation (χ : U) (κ : ℝ) (c : ℂ)
    (hFE : ∀ w : ℂ, continuedCompletedHeckeL χ⁻¹ (1 - w) =
      c * Complex.exp ((κ : ℂ) * (w - 1 / 2)) * continuedCompletedHeckeL χ w)
    (E : ℝ) (hE : 0 ≤ E) (he : ∀ (ψ : U) (w : Complex.re ⁻¹' Ioi (1 : ℝ)),
      (w : ℂ).re = 5 / 2 → ‖finiteHeckeL ψ w‖ ≤ E)
    (s : ℂ) (hs : s.re = -(3 / 2 : ℝ)) :
    ‖(continuedCompletedHeckeL χ s / heckeGammaFactor χ s) *
      (continuedCompletedHeckeL χ⁻¹ s / heckeGammaFactor χ⁻¹ s)‖ ≤
      Real.exp (4 * κ) * E ^ 2 *
        (6 + ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖) ^ (8 * Fintype.card (InfinitePlace F)) *
          (1 + |s.im|) ^ (8 * Fintype.card (InfinitePlace F)) := by
  let t := 1 - s
  let Λ (ψ : U) := continuedCompletedHeckeL ψ
  let Γ (ψ : U) := heckeGammaFactor ψ
  let J := ∑ v : InfinitePlace F, ‖heckeArchimedeanShift χ v‖
  let B := 6 + |s.im| + J
  let k := 4 * Fintype.card (InfinitePlace F)
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ht : t.re = 5 / 2 := by simp [t, Complex.sub_re, hs]; norm_num
  let u : Complex.re ⁻¹' Ioi (1 : ℝ) := ⟨t, by change 1 < t.re; rw [ht]; norm_num⟩
  have hr (ψ : U) : Λ ψ t = Γ ψ t * finiteHeckeL ψ u := (continuedCompletedHeckeL_spec ψ).2 u
  have hrefl : Λ χ⁻¹ s = c * Complex.exp ((κ : ℂ) * (t - 1 / 2)) * Λ χ t := by
    simpa only [t, sub_sub_cancel] using hFE t
  have hphase : Complex.exp ((κ : ℂ) * (1 - 2 * s)) * Complex.exp ((κ : ℂ) * (s - 1 / 2)) =
      Complex.exp ((κ : ℂ) * (t - 1 / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp only [t]
    ring
  have hpair : Λ χ s * Λ χ⁻¹ s =
      Complex.exp ((κ : ℂ) * (1 - 2 * s)) * (Λ χ t * Λ χ⁻¹ t) := by
    have hr' : Λ χ⁻¹ t = c * Complex.exp ((κ : ℂ) * (s - 1 / 2)) * Λ χ s := hFE s
    rw [hrefl, hr', ← hphase]
    ring
  have hvalue : (Λ χ s / Γ χ s) * (Λ χ⁻¹ s / Γ χ⁻¹ s) =
      Complex.exp ((κ : ℂ) * (1 - 2 * s)) * ((Γ χ⁻¹ t / Γ χ s) * (Γ χ t / Γ χ⁻¹ s)) *
        (finiteHeckeL χ u * finiteHeckeL χ⁻¹ u) := by
    rw [div_mul_div_comm, hpair, hr, hr]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hnorm : ‖Complex.exp ((κ : ℂ) * (1 - 2 * s))‖ = Real.exp (4 * κ) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.sub_re, hs]
    ring
  have hg : ‖Γ χ⁻¹ t / Γ χ s‖ ≤ B ^ k := heckeGammaFactor_left_quotient_bound χ s hs
  have hg' : ‖Γ χ t / Γ χ⁻¹ s‖ ≤ B ^ k := by
    have h := heckeGammaFactor_left_quotient_bound χ⁻¹ s hs
    simpa only [inv_inv, heckeArchimedeanShift_inv_conj, Complex.norm_conj] using h
  have hb : B ≤ (6 + J) * (1 + |s.im|) := by dsimp [B]; nlinarith [abs_nonneg s.im, mul_nonneg hJ (abs_nonneg s.im)]
  have hk : k + k = 8 * Fintype.card (InfinitePlace F) := by dsimp [k]; omega
  change ‖(Λ χ s / Γ χ s) * (Λ χ⁻¹ s / Γ χ⁻¹ s)‖ ≤ _
  rw [hvalue, norm_mul, norm_mul, norm_mul, norm_mul, hnorm]
  calc
    _ ≤ Real.exp (4 * κ) * (B ^ k * B ^ k) * (E * E) := by
      gcongr
      · exact he χ u ht
      · exact he χ⁻¹ u ht
    _ = Real.exp (4 * κ) * E ^ 2 * B ^ (8 * Fintype.card (InfinitePlace F)) := by
      rw [← hk, pow_add]
      ring
    _ ≤ Real.exp (4 * κ) * E ^ 2 * ((6 + J) * (1 + |s.im|)) ^ (8 * Fintype.card (InfinitePlace F)) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hb _) (by positivity)
    _ = _ := by simp only [J, mul_pow, mul_assoc]

end RiemannMasullo.StripNuclearity
