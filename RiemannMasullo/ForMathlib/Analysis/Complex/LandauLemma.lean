module

public import RiemannMasullo.External.PrimeNumberTheoremAnd.StrongPNT

/-!
# Landau's lemma on an arbitrary disc

The vendored `FinalBound` and `ZerosBound` of PrimeNumberTheoremAnd
(`RiemannMasullo/External/PrimeNumberTheoremAnd/StrongPNT.lean`) are stated for a function
analytic on the closed unit disc, normalised by `f 0 = 1`, with an explicit finiteness
hypothesis on its zeros. This file transports them to an arbitrary closed disc
`closedBall c R` by the change of variables `w ↦ c + R * w` and the normalisation `f / f c`,
and removes the finiteness hypothesis (it follows from the identity theorem).

For `f` analytic on a neighbourhood of `closedBall c R`, with `f c ≠ 0` and
`‖f u / f c‖ ≤ B` on `closedBall c R`:

* `landau_sum_analyticOrderNatAt_le`: the zeros in `closedBall c r`, counted with multiplicity,
  number at most `log B / log (R / r)` (Jensen's bound);
* `landau_norm_logDeriv_sub_le`: for `0 < r' < r < R' < R`, `z ∈ closedBall c r'` and
  `f z ≠ 0`,
  `‖f'/f (z) - ∑_{ρ ∈ closedBall c r} m(ρ) / (z - ρ)‖ ≤ landauConstant r' r R' R * log B`,
  where `m(ρ) = analyticOrderNatAt f ρ` and the constant is scale-invariant (of size `1 / R`
  when the radii are fixed fractions of `R`);
* `landau_norm_logDeriv_sub_le_of_radius`: the same with the radii `R/4`, `R/2` and the
  explicit constant `300 / R` (`landauConstant_quarter_le`);
* `landau_neg_re_logDeriv_le`: the one-sided form
  `-Re f'/f (z) ≤ -∑_{ρ ∈ S} Re (m(ρ) / (z - ρ)) + C log B`, where the zeros outside `S` lie to
  the left of `z` (`Re ρ ≤ Re z`), so that their terms have the right sign and are dropped;
  the special cases `S = ∅` (`landau_neg_re_logDeriv_le_of_forall_re_le`) and `S = {ρ₀}`
  (`landau_neg_re_logDeriv_le_of_zero`) are the forms used in de la Vallée Poussin's argument;
* `landau_pole_norm_logDeriv_sub_le`, `landau_pole_neg_re_logDeriv_le`: the same for a
  function `f` with (at most) a simple pole at a known point `p`, through an analytic `g` with
  `f s = g s / (s - p)` for `s ≠ p`; the pole contributes `+ Re (1 / (z - p))`.

The constants are those of PrimeNumberTheoremAnd; the lemmas there are applied, not adapted.
-/

@[expose] public section

open Complex Metric Set Function Filter Topology

namespace RiemannMasullo

/-- The constant of Landau's lemma (`FinalBound`) for the radii `r' < r < R' < R`. It is
homogeneous of degree `-1` in the radii (`landauConstant_div`). -/
noncomputable def landauConstant (r' r R' R : ℝ) : ℝ :=
  16 * r ^ 2 / (r - r') ^ 3 + 1 / ((R ^ 2 / R' - R') * Real.log (R / R'))

/-- The constant of Landau's lemma is positive. -/
theorem landauConstant_pos {r' r R' R : ℝ} (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R')
    (hR'R : R' < R) : 0 < landauConstant r' r R' R := by
  have hR' : 0 < R' := by linarith
  have h1 : 0 < R ^ 2 / R' - R' := by
    rw [sub_pos, lt_div_iff₀ hR']; nlinarith
  have h2 : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  unfold landauConstant
  have h3 : 0 < r - r' := by linarith
  positivity

/-- `landauConstant` is homogeneous of degree `-1`. -/
theorem landauConstant_div {r' r R' R s : ℝ} (hs : 0 < s) (hr'r : r' < r) (hR' : 0 < R')
    (hR'R : R' < R) :
    landauConstant (r' / s) (r / s) (R' / s) (R / s) = s * landauConstant r' r R' R := by
  have h3 : r - r' ≠ 0 := by linarith
  have h1 : R ^ 2 / R' - R' ≠ 0 := by
    have : 0 < R ^ 2 / R' - R' := by rw [sub_pos, lt_div_iff₀ hR']; nlinarith
    exact this.ne'
  have h2 : Real.log (R / R') ≠ 0 := (Real.log_pos ((one_lt_div hR').mpr hR'R)).ne'
  have hRR : R / s / (R' / s) = R / R' := by field_simp
  have hsub : (R / s) ^ 2 / (R' / s) - R' / s = (R ^ 2 / R' - R') / s := by
    field_simp
  have hsub' : r / s - r' / s = (r - r') / s := by ring
  unfold landauConstant
  rw [hRR, hsub, hsub']
  field_simp

/-! ### Zeros of an analytic function in a closed disc -/

/-- An analytic function on a closed disc that does not vanish at the centre has finitely
many zeros in the disc. -/
theorem finite_zeros_closedBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    {ρ | ρ ∈ closedBall c R ∧ f ρ = 0}.Finite := by
  by_contra h
  obtain ⟨x, hx, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact h
    (isCompact_closedBall c R) (fun ρ hρ ↦ hρ.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, f z = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono fun z hz ↦ hz.2
  exact hc (hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_closedBall c R).isPreconnected hx hfreq (mem_closedBall_self hR))

/-- Analyticity on a neighbourhood of a closed disc extends to a slightly larger closed disc. -/
private theorem landau_exists_gt_analyticOnNhd {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    ∃ S, R < S ∧ AnalyticOnNhd ℂ f (closedBall c S) := by
  obtain ⟨δ, hδ, hsub⟩ :=
    (isCompact_closedBall c R).exists_cthickening_subset_open (isOpen_analyticAt ℂ f)
      (fun x hx ↦ hf x hx)
  refine ⟨δ + R, by linarith, fun x hx ↦ ?_⟩
  rw [← cthickening_closedBall hδ.le hR] at hx
  exact hsub hx

/-- The order of vanishing is zero at a point where an analytic function does not vanish. -/
private theorem landau_analyticOrderNatAt_eq_zero {f : ℂ → ℂ} {x : ℂ} (hx : f x ≠ 0) : analyticOrderNatAt f x = 0 := by
  simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hx)]

/-- A sum over a set agrees with a sum over a finset when the two agree on the support. -/
private theorem landau_finsum_mem_eq_sum {M : Type*} [AddCommMonoid M] {φ : ℂ → M}
    (A : Set ℂ) (T : Finset ℂ) (h : ∀ x, φ x ≠ 0 → (x ∈ A ↔ x ∈ T)) :
    ∑ᶠ x ∈ A, φ x = ∑ x ∈ T, φ x := by
  rw [← finsum_mem_coe_finset]
  exact finsum_mem_inter_support_eq' _ _ _ h

/-! ### The change of variables `w ↦ c + S * w` -/

private theorem landau_dist_rescale {c w : ℂ} {S : ℝ} (hS : 0 < S) :
    dist (c + (S : ℂ) * w) c = S * ‖w‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hS.le]

private theorem landau_mem_closedBall_rescale {c w : ℂ} {S t : ℝ} (hS : 0 < S) :
    c + (S : ℂ) * w ∈ closedBall c t ↔ ‖w‖ ≤ t / S := by
  rw [mem_closedBall, landau_dist_rescale hS, le_div_iff₀ hS, mul_comm]

private theorem landau_rescale_inv {c z : ℂ} {S : ℝ} (hS : 0 < S) :
    c + (S : ℂ) * ((z - c) / S) = z := by
  have : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp
  ring

private theorem landau_analyticOnNhd_rescale {f : ℂ → ℂ} {c : ℂ} {S : ℝ} (hS : 0 < S)
    (hf : AnalyticOnNhd ℂ f (closedBall c S)) :
    AnalyticOnNhd ℂ (fun w ↦ f (c + (S : ℂ) * w) / f c) (closedBall 0 1) := by
  intro w hw
  have hmem : c + (S : ℂ) * w ∈ closedBall c S := by
    rw [landau_mem_closedBall_rescale hS, div_self hS.ne']
    simpa using hw
  have h1 : AnalyticAt ℂ (fun w : ℂ ↦ c + (S : ℂ) * w) w := by fun_prop
  have h2 : AnalyticAt ℂ (f ∘ fun w : ℂ ↦ c + (S : ℂ) * w) w := AnalyticAt.comp (f := fun w : ℂ ↦ c + (S : ℂ) * w) (hf _ hmem) h1
  exact h2.div_const

private theorem landau_analyticOrderNatAt_rescale {f : ℂ → ℂ} {c w : ℂ} {S : ℝ} (hS : 0 < S)
    (hf : AnalyticAt ℂ f (c + (S : ℂ) * w)) (hc : f c ≠ 0) :
    analyticOrderNatAt (fun w ↦ f (c + (S : ℂ) * w) / f c) w =
      analyticOrderNatAt f (c + (S : ℂ) * w) := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hcomp : (fun w ↦ f (c + (S : ℂ) * w) / f c) =
      (fun u ↦ f u * (f c)⁻¹) ∘ (fun w : ℂ ↦ c + (S : ℂ) * w) := by
    funext w; simp [div_eq_mul_inv]
  have hderiv : deriv (fun w : ℂ ↦ c + (S : ℂ) * w) w ≠ 0 := by
    simpa using hS'
  rw [analyticOrderNatAt, analyticOrderNatAt, hcomp,
    analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) hderiv]
  classical
  rw [analyticOrderAt_fun_mul_const hf]
  simp [hc]

private theorem landau_logDeriv_rescale {f : ℂ → ℂ} {c w : ℂ} {S : ℝ}
    (hf : DifferentiableAt ℂ f (c + (S : ℂ) * w)) (hc : f c ≠ 0)
    (hfw : f (c + (S : ℂ) * w) ≠ 0) :
    deriv (fun w ↦ f (c + (S : ℂ) * w) / f c) w / (f (c + (S : ℂ) * w) / f c) =
      S * logDeriv f (c + (S : ℂ) * w) := by
  have haff : HasDerivAt (fun w : ℂ ↦ c + (S : ℂ) * w) (S : ℂ) w := by
    simpa using ((hasDerivAt_id w).const_mul (S : ℂ)).const_add c
  have hd : HasDerivAt (fun w ↦ f (c + (S : ℂ) * w) / f c)
      (deriv f (c + (S : ℂ) * w) * S / f c) w :=
    (hf.hasDerivAt.comp w haff).div_const (f c)
  rw [hd.deriv, logDeriv_apply]
  field_simp

/-- The zeros of the rescaled function in the disc of radius `r / S` correspond to the zeros of
`f` in `closedBall c r`, and a sum over the former is a sum over the latter. -/
private theorem landau_sum_zeros_rescale {M : Type*} [AddCommMonoid M] {f : ℂ → ℂ} {c : ℂ}
    {r S : ℝ} (hS : 0 < S) (hc : f c ≠ 0)
    (hTg : (External.PrimeNumberTheoremAnd.SetOfZeros (r / S)
      (fun w ↦ f (c + (S : ℂ) * w) / f c)).Finite)
    (hTf : {ρ | ρ ∈ closedBall c r ∧ f ρ = 0}.Finite) (φ : ℂ → M) :
    ∑ ρ ∈ hTg.toFinset, φ (c + (S : ℂ) * ρ) = ∑ ρ ∈ hTf.toFinset, φ ρ := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  refine Finset.sum_nbij' (fun ρ ↦ c + (S : ℂ) * ρ) (fun ρ ↦ (ρ - c) / S) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset, External.PrimeNumberTheoremAnd.SetOfZeros,
      mem_ofPred_eq, div_eq_zero_iff, hc, or_false] at hρ ⊢
    exact ⟨(landau_mem_closedBall_rescale hS).mpr hρ.1, hρ.2⟩
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset, External.PrimeNumberTheoremAnd.SetOfZeros,
      mem_ofPred_eq, div_eq_zero_iff, hc, or_false] at hρ ⊢
    rw [landau_rescale_inv hS, ← landau_mem_closedBall_rescale hS, landau_rescale_inv hS]
    exact hρ
  · intro ρ _
    field_simp
    ring
  · intro ρ _
    exact landau_rescale_inv hS
  · intro ρ _
    rfl


/-- The rescaled function has finitely many zeros in the closed unit disc. -/
private theorem landau_setOfZeros_rescale_finite {f : ℂ → ℂ} {c : ℂ} {S : ℝ} (hS : 0 < S)
    (hf : AnalyticOnNhd ℂ f (closedBall c S)) (hc : f c ≠ 0) :
    (External.PrimeNumberTheoremAnd.SetOfZeros 1
      (fun w ↦ f (c + (S : ℂ) * w) / f c)).Finite := by
  refine (finite_zeros_closedBall zero_le_one (landau_analyticOnNhd_rescale hS hf)
    (by simp [hc])).subset ?_
  intro ρ hρ
  exact ⟨by simpa using hρ.1, hρ.2⟩

open scoped Classical in
/-- A sum over `closedBall c r` of terms that vanish where the order of `f` is zero is a sum
over the zeros of `f` in the disc. -/
private theorem landau_finsum_eq_sum_zeros {M : Type*} [AddCommMonoid M] {f : ℂ → ℂ} {c : ℂ}
    {r : ℝ} (hTf : {ρ | ρ ∈ closedBall c r ∧ f ρ = 0}.Finite) (S : Set ℂ) (φ : ℂ → M)
    (hφ : ∀ x, f x ≠ 0 → φ x = 0) :
    ∑ᶠ x ∈ closedBall c r ∩ S, φ x = ∑ x ∈ hTf.toFinset with x ∈ S, φ x := by
  refine landau_finsum_mem_eq_sum _ _ fun x hx ↦ ?_
  have : f x = 0 := by by_contra h; exact hx (hφ x h)
  simp only [mem_inter_iff, Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq, this,
    and_true]

/-! ### Jensen's bound for the number of zeros -/

/-- **Jensen's bound** on a disc. If `f` is analytic on a neighbourhood of `closedBall c R`,
`f c ≠ 0` and `‖f u / f c‖ ≤ B` on `closedBall c R`, then for `0 < r < R` the number of zeros
of `f` in `closedBall c r`, counted with multiplicity, is at most `log B / log (R / r)`.
Rescaled from `ZerosBound` of PrimeNumberTheoremAnd. -/
theorem landau_sum_analyticOrderNatAt_le {f : ℂ → ℂ} {c : ℂ} {r R B : ℝ} (hr : 0 < r)
    (hrR : r < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B) :
    ∑ᶠ ρ ∈ closedBall c r, (analyticOrderNatAt f ρ : ℝ) ≤ Real.log B / Real.log (R / r) := by
  obtain ⟨S, hRS, hfS⟩ := landau_exists_gt_analyticOnNhd (by linarith) hf
  have hS : 0 < S := by linarith
  set g : ℂ → ℂ := fun w ↦ f (c + (S : ℂ) * w) / f c with hg
  have hgA : AnalyticOnNhd ℂ g (closedBall 0 1) := landau_analyticOnNhd_rescale hS hfS
  have hg0 : g 0 = 1 := by simp [hg, hc]
  have hgfin : (External.PrimeNumberTheoremAnd.SetOfZeros 1 g).Finite := by
    refine (finite_zeros_closedBall zero_le_one hgA (by simp [hg0])).subset ?_
    intro ρ hρ
    exact ⟨by simpa using hρ.1, hρ.2⟩
  have hgB : ∀ w : ℂ, ‖w‖ ≤ R / S → ‖g w‖ ≤ B := fun w hw ↦
    hbound _ ((landau_mem_closedBall_rescale hS).mpr hw)
  have hZ := External.PrimeNumberTheoremAnd.ZerosBound (div_pos hr hS)
    ((div_lt_one hS).mpr (by linarith)) (div_lt_div_of_pos_right hrR hS)
    ((div_lt_one hS).mpr hRS) hgA hg0 hgfin hgB
  have hTf := finite_zeros_closedBall hr.le (hf.mono (closedBall_subset_closedBall hrR.le)) hc
  have hsum : ∑ᶠ ρ ∈ closedBall c r, (analyticOrderNatAt f ρ : ℝ) =
      ∑ ρ ∈ hTf.toFinset, (analyticOrderNatAt f ρ : ℝ) := by
    refine landau_finsum_mem_eq_sum _ _ fun x hx ↦ ?_
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, iff_self_and]
    intro hxr
    by_contra hfx
    exact hx (by
      rw [landau_analyticOrderNatAt_eq_zero hfx]
      simp)
  rw [hsum, ← landau_sum_zeros_rescale hS hc
    (External.PrimeNumberTheoremAnd.finiteSetOfZeros_mono ((div_lt_one hS).mpr (by linarith))
      hgfin) hTf]
  have hRr : R / S / (r / S) = R / r := by field_simp
  rw [hRr, one_div, inv_mul_eq_div] at hZ
  refine le_of_eq_of_le ?_ (by exact_mod_cast hZ)
  push_cast
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  have hρ' := (Set.Finite.mem_toFinset _).mp hρ
  have hmem : c + (S : ℂ) * ρ ∈ closedBall c S := by
    rw [landau_mem_closedBall_rescale hS, div_self hS.ne']
    exact hρ'.1.trans ((div_lt_one hS).mpr (by linarith)).le
  rw [landau_analyticOrderNatAt_rescale hS (hfS _ hmem) hc]

/-! ### Landau's lemma -/

/-- **Landau's lemma** on a disc. Let `f` be analytic on a neighbourhood of `closedBall c R`,
with `f c ≠ 0` and `‖f u / f c‖ ≤ B` on `closedBall c R`, where `1 < B`. For radii
`0 < r' < r < R' < R` and every `z ∈ closedBall c r'` with `f z ≠ 0`,
`‖f'/f (z) - ∑_{ρ ∈ closedBall c r} m(ρ) / (z - ρ)‖ ≤ landauConstant r' r R' R * log B`,
where `m(ρ) = analyticOrderNatAt f ρ` (zero unless `f ρ = 0`). Rescaled from `FinalBound` of
PrimeNumberTheoremAnd. -/
theorem landau_norm_logDeriv_sub_le {f : ℂ → ℂ} {c z : ℂ} {r' r R' R B : ℝ}
    (hB : 1 < B) (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R') (hR'R : R' < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B)
    (hz : z ∈ closedBall c r') (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ ∈ closedBall c r, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
      landauConstant r' r R' R * Real.log B := by
  obtain ⟨S, hRS, hfS⟩ := landau_exists_gt_analyticOnNhd (by linarith) hf
  have hS : 0 < S := by linarith
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hlt : ∀ t, t < S → t / S < 1 := fun t ht ↦ (div_lt_one hS).mpr ht
  set g : ℂ → ℂ := fun w ↦ f (c + (S : ℂ) * w) / f c with hg
  have hgA : AnalyticOnNhd ℂ g (closedBall 0 1) := landau_analyticOnNhd_rescale hS hfS
  have hg0 : g 0 = 1 := by simp [hg, hc]
  have hgfin := landau_setOfZeros_rescale_finite hS hfS hc
  have hgB : ∀ w : ℂ, ‖w‖ ≤ R / S → ‖g w‖ ≤ B := fun w hw ↦
    hbound _ ((landau_mem_closedBall_rescale hS).mpr hw)
  set w : ℂ := (z - c) / S with hw
  have hzw : c + (S : ℂ) * w = z := landau_rescale_inv hS
  have hwz : w ∈ closedBall (0 : ℂ) (r' / S) \
      External.PrimeNumberTheoremAnd.SetOfZeros (R' / S) g := by
    refine ⟨?_, fun h ↦ hfz ?_⟩
    · rw [mem_closedBall, dist_zero_right, ← landau_mem_closedBall_rescale hS, hzw]
      exact hz
    · have h2 : g w = 0 := h.2
      simpa [hg, hc, hzw] using h2
  have hF := External.PrimeNumberTheoremAnd.FinalBound hB (div_pos hr' hS)
    (div_lt_div_of_pos_right hr'r hS) (hlt r (by linarith)) (div_lt_div_of_pos_right hrR' hS)
    (div_lt_div_of_pos_right hR'R hS) (hlt R hRS) hgA hg0 hgfin hgB hwz
  have hzS : z ∈ closedBall c S :=
    closedBall_subset_closedBall (by linarith) hz
  have hlog : deriv g w / g w = S * logDeriv f z := by
    have := landau_logDeriv_rescale (w := w) (hfS _ (hzw ▸ hzS)).differentiableAt hc
      (by rw [hzw]; exact hfz)
    rw [hzw] at this
    rw [show g w = f z / f c by simp [hg, hzw]]
    exact this
  have hTf := finite_zeros_closedBall (R := r) (by linarith)
    (hf.mono (closedBall_subset_closedBall (by linarith))) hc
  have hsum : ∑ ρ ∈ (External.PrimeNumberTheoremAnd.finiteSetOfZeros_mono
      (hlt r (by linarith)) hgfin).toFinset, (analyticOrderNatAt g ρ : ℂ) / (w - ρ) =
      S * ∑ᶠ ρ ∈ closedBall c r, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) := by
    have h1 := landau_finsum_eq_sum_zeros hTf univ
      (fun ρ ↦ (analyticOrderNatAt f ρ : ℂ) / (z - ρ))
      (fun x hx ↦ by simp [landau_analyticOrderNatAt_eq_zero hx])
    simp only [inter_univ, mem_univ, Finset.filter_true] at h1
    rw [h1, Finset.mul_sum, ← landau_sum_zeros_rescale hS hc
      (External.PrimeNumberTheoremAnd.finiteSetOfZeros_mono (hlt r (by linarith)) hgfin) hTf]
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hρ' := (Set.Finite.mem_toFinset _).mp hρ
    have hmem : c + (S : ℂ) * ρ ∈ closedBall c S := by
      rw [landau_mem_closedBall_rescale hS, div_self hS.ne']
      exact hρ'.1.trans (hlt r (by linarith)).le
    rw [hg, landau_analyticOrderNatAt_rescale hS (hfS _ hmem) hc]
    have hwρ : w - ρ = (z - (c + (S : ℂ) * ρ)) / S := by
      rw [hw]; field_simp; ring
    rw [hwρ, div_div_eq_mul_div]
    ring
  change _ ≤ landauConstant (r' / S) (r / S) (R' / S) (R / S) * Real.log B at hF
  rw [hlog, hsum, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hS.le,
    landauConstant_div hS hr'r (by linarith) hR'R, mul_assoc] at hF
  exact le_of_mul_le_mul_left hF hS

/-- The constant of Landau's lemma for the radii `R/4 < R/2 < 3R/4 < R` is at most `300 / R`. -/
theorem landauConstant_quarter_le {R : ℝ} (hR : 0 < R) :
    landauConstant (R / 4) (R / 2) (3 * R / 4) R ≤ 300 / R := by
  have e1 : 16 * (R / 2) ^ 2 / (R / 2 - R / 4) ^ 3 = 256 / R := by field_simp; ring
  have e2 : R / (3 * R / 4) = 4 / 3 := by field_simp
  have e3 : R ^ 2 / (3 * R / 4) - 3 * R / 4 = 7 * R / 12 := by field_simp; ring
  have hlog : 1 / 4 ≤ Real.log (4 / 3) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 4 / 3) (by norm_num)
    norm_num at this ⊢; linarith
  have h2 : 1 / (7 * R / 12 * Real.log (4 / 3)) ≤ 1 / (7 * R / 12 * (1 / 4)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hlog (by positivity))
  have h3 : 1 / (7 * R / 12 * (1 / 4)) ≤ 44 / R := by
    rw [div_le_div_iff₀ (by positivity) hR]; nlinarith
  unfold landauConstant
  rw [e1, e2, e3]
  have : 256 / R + 44 / R = 300 / R := by ring
  linarith

/-- **Landau's lemma** on a disc with fixed radii: if `f` is analytic on a neighbourhood of
`closedBall c R`, `f c ≠ 0` and `‖f u / f c‖ ≤ B` on `closedBall c R` with `1 < B`, then for
`z ∈ closedBall c (R / 4)` with `f z ≠ 0`,
`‖f'/f (z) - ∑_{ρ ∈ closedBall c (R/2)} m(ρ) / (z - ρ)‖ ≤ 300 * log B / R`. -/
theorem landau_norm_logDeriv_sub_le_of_radius {f : ℂ → ℂ} {c z : ℂ} {R B : ℝ}
    (hB : 1 < B) (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B)
    (hz : z ∈ closedBall c (R / 4)) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ᶠ ρ ∈ closedBall c (R / 2), (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
      300 * Real.log B / R := by
  refine (landau_norm_logDeriv_sub_le (r' := R / 4) (r := R / 2) (R' := 3 * R / 4) hB
    (by positivity) (by linarith) (by linarith)
    (by linarith) hf hc hbound hz hfz).trans ?_
  rw [show 300 * Real.log B / R = 300 / R * Real.log B by ring]
  exact mul_le_mul_of_nonneg_right (landauConstant_quarter_le hR)
    (Real.log_nonneg hB.le)

/-! ### The one-sided form -/

/-- From a bound for `‖L - ∑ m(ρ) / (z - ρ)‖`, a one-sided bound for `-Re L` keeping only the
zeros in `S`: the other zeros lie to the left of `z`, so their terms have nonnegative real
part. -/
private theorem landau_neg_re_le_aux {f : ℂ → ℂ} {c z L : ℂ} {r K : ℝ}
    (hTf : {ρ | ρ ∈ closedBall c r ∧ f ρ = 0}.Finite) (S : Set ℂ)
    (hS : ∀ ρ ∈ closedBall c r, f ρ = 0 → ρ ∉ S → ρ.re ≤ z.re)
    (h : ‖L - ∑ᶠ ρ ∈ closedBall c r, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ K) :
    -L.re ≤ -∑ᶠ ρ ∈ closedBall c r ∩ S, ((analyticOrderNatAt f ρ : ℂ) / (z - ρ)).re + K := by
  classical
  have h0 : ∀ x, f x ≠ 0 → (analyticOrderNatAt f x : ℂ) / (z - x) = 0 := fun x hx ↦ by
    simp [landau_analyticOrderNatAt_eq_zero hx]
  have h1 := landau_finsum_eq_sum_zeros hTf univ
    (fun ρ ↦ (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) h0
  simp only [inter_univ, mem_univ, Finset.filter_true] at h1
  rw [landau_finsum_eq_sum_zeros hTf S _ fun x hx ↦ by simp [h0 x hx]]
  rw [h1] at h
  set T := hTf.toFinset
  have hsplit := Finset.sum_filter_add_sum_filter_not T (· ∈ S)
    (fun ρ ↦ ((analyticOrderNatAt f ρ : ℂ) / (z - ρ)).re)
  have hnonneg : 0 ≤ ∑ ρ ∈ T with ρ ∉ S, ((analyticOrderNatAt f ρ : ℂ) / (z - ρ)).re := by
    refine Finset.sum_nonneg fun ρ hρ ↦ ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    have hre : 0 ≤ (z - ρ).re := by
      have := hS ρ hρ.1.1 hρ.1.2 hρ.2
      rw [sub_re]; linarith
    rw [div_eq_mul_inv, ← ofReal_natCast, re_ofReal_mul, inv_re]
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hre (normSq_nonneg _))
  have hre := (abs_le.mp (abs_re_le_norm
    (L - ∑ ρ ∈ T, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)))).1
  rw [sub_re, re_sum] at hre
  linarith

/-- **Landau's lemma, one-sided form.** Under the hypotheses of `landau_norm_logDeriv_sub_le`,
let `S` be a set containing every zero `ρ` of `f` in `closedBall c r` with `Re z < Re ρ`. Then
`-Re f'/f (z) ≤ -∑_{ρ ∈ closedBall c r ∩ S} Re (m(ρ) / (z - ρ)) + landauConstant r' r R' R * log B`.
-/
theorem landau_neg_re_logDeriv_le {f : ℂ → ℂ} {c z : ℂ} {r' r R' R B : ℝ}
    (hB : 1 < B) (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R') (hR'R : R' < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B)
    (hz : z ∈ closedBall c r') (hfz : f z ≠ 0) (S : Set ℂ)
    (hS : ∀ ρ ∈ closedBall c r, f ρ = 0 → ρ ∉ S → ρ.re ≤ z.re) :
    -(logDeriv f z).re ≤
      -∑ᶠ ρ ∈ closedBall c r ∩ S, ((analyticOrderNatAt f ρ : ℂ) / (z - ρ)).re +
        landauConstant r' r R' R * Real.log B :=
  landau_neg_re_le_aux (finite_zeros_closedBall (R := r) (by linarith)
    (hf.mono (closedBall_subset_closedBall (by linarith))) hc) S hS
    (landau_norm_logDeriv_sub_le hB hr' hr'r hrR' hR'R hf hc hbound hz hfz)

/-- **Landau's lemma, one-sided form, no zero kept.** If every zero of `f` in `closedBall c r`
satisfies `Re ρ ≤ Re z`, then `-Re f'/f (z) ≤ landauConstant r' r R' R * log B`. -/
theorem landau_neg_re_logDeriv_le_of_forall_re_le {f : ℂ → ℂ} {c z : ℂ} {r' r R' R B : ℝ}
    (hB : 1 < B) (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R') (hR'R : R' < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B)
    (hz : z ∈ closedBall c r') (hfz : f z ≠ 0)
    (hS : ∀ ρ ∈ closedBall c r, f ρ = 0 → ρ.re ≤ z.re) :
    -(logDeriv f z).re ≤ landauConstant r' r R' R * Real.log B := by
  have := landau_neg_re_logDeriv_le hB hr' hr'r hrR' hR'R hf hc hbound hz hfz ∅
    fun ρ hρ hfρ _ ↦ hS ρ hρ hfρ
  simpa using this

/-- **Landau's lemma, one-sided form, one zero kept.** If every zero of `f` in
`closedBall c r` satisfies `Re ρ ≤ Re z` and `ρ₀` is one of them, then
`-Re f'/f (z) ≤ -Re (1 / (z - ρ₀)) + landauConstant r' r R' R * log B`. This is the form used
in de la Vallée Poussin's argument. -/
theorem landau_neg_re_logDeriv_le_of_zero {f : ℂ → ℂ} {c z ρ₀ : ℂ} {r' r R' R B : ℝ}
    (hB : 1 < B) (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R') (hR'R : R' < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0)
    (hbound : ∀ u ∈ closedBall c R, ‖f u / f c‖ ≤ B)
    (hz : z ∈ closedBall c r') (hfz : f z ≠ 0)
    (hS : ∀ ρ ∈ closedBall c r, f ρ = 0 → ρ.re ≤ z.re)
    (hρ₀ : ρ₀ ∈ closedBall c r) (hfρ₀ : f ρ₀ = 0) :
    -(logDeriv f z).re ≤ -(1 / (z - ρ₀)).re + landauConstant r' r R' R * Real.log B := by
  have := landau_neg_re_logDeriv_le hB hr' hr'r hrR' hR'R hf hc hbound hz hfz {ρ₀}
    fun ρ hρ hfρ _ ↦ hS ρ hρ hfρ
  rw [inter_singleton_of_mem hρ₀, finsum_mem_singleton] at this
  refine this.trans (add_le_add_left (neg_le_neg ?_) _)
  have hm : 1 ≤ analyticOrderNatAt f ρ₀ := by
    have hA : AnalyticAt ℂ f ρ₀ :=
      hf ρ₀ (closedBall_subset_closedBall (by linarith) hρ₀)
    have htop : analyticOrderAt f ρ₀ ≠ ⊤ := by
      intro htop
      have hev : ∀ᶠ x in 𝓝 ρ₀, f x = 0 := analyticOrderAt_eq_top.mp htop
      have hfreq : ∃ᶠ x in 𝓝[≠] ρ₀, f x = 0 :=
        (hev.filter_mono nhdsWithin_le_nhds).frequently
      exact hc (hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_closedBall c R).isPreconnected
        (closedBall_subset_closedBall (by linarith) hρ₀) hfreq
        (mem_closedBall_self (by linarith)))
    have hne : analyticOrderAt f ρ₀ ≠ 0 := by
      rw [ne_eq, analyticOrderAt_eq_zero]; simp [hA, hfρ₀]
    rw [Nat.one_le_iff_ne_zero, ne_eq, analyticOrderNatAt, ENat.toNat_eq_zero]
    tauto
  have hre : 0 ≤ (1 / (z - ρ₀)).re := by
    have := hS ρ₀ hρ₀ hfρ₀
    have h0 : 0 ≤ (z - ρ₀).re := by rw [sub_re]; linarith
    rw [one_div, inv_re]
    exact div_nonneg h0 (normSq_nonneg _)
  have heq : ((analyticOrderNatAt f ρ₀ : ℂ) / (z - ρ₀)).re =
      analyticOrderNatAt f ρ₀ * (1 / (z - ρ₀)).re := by
    rw [div_eq_mul_one_div, ← ofReal_natCast, re_ofReal_mul]
  rw [heq]
  exact le_mul_of_one_le_left hre (by exact_mod_cast hm)

/-! ### Functions with a known pole -/

/-- `f = g / (s - p)` near a point `z ≠ p` of the interior: the logarithmic derivatives differ
by `1 / (z - p)`. -/
private theorem landau_pole_logDeriv {f g : ℂ → ℂ} {c p z : ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hfg : ∀ s ∈ closedBall c R, s ≠ p → f s = g s / (s - p))
    (hz : z ∈ ball c R) (hzp : z ≠ p) (hfz : f z ≠ 0) :
    g z ≠ 0 ∧ logDeriv g z = logDeriv f z + 1 / (z - p) := by
  have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
  have hev : ∀ᶠ s in 𝓝 z, g s = f s * (s - p) := by
    filter_upwards [isOpen_ball.mem_nhds hz, isOpen_ne.mem_nhds hzp] with s hs hsp
    rw [hfg s (ball_subset_closedBall hs) hsp, div_mul_cancel₀ _ (sub_ne_zero.mpr hsp)]
  have hgz : g z = f z * (z - p) := hev.self_of_nhds
  have hgz0 : g z ≠ 0 := by rw [hgz]; exact mul_ne_zero hfz hzp'
  have hfev : ∀ᶠ s in 𝓝 z, f s = g s / (s - p) := by
    filter_upwards [isOpen_ball.mem_nhds hz, isOpen_ne.mem_nhds hzp] with s hs hsp
    exact hfg s (ball_subset_closedBall hs) hsp
  have hgd : DifferentiableAt ℂ g z := (hg z (ball_subset_closedBall hz)).differentiableAt
  have hfd : DifferentiableAt ℂ f z :=
    ((hgd.div (by fun_prop) hzp').congr_of_eventuallyEq hfev)
  refine ⟨hgz0, ?_⟩
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  rw [logDeriv_fun_mul (f := f) (g := fun s ↦ s - p) z hfz hzp' hfd (by fun_prop)]
  congr 1
  rw [logDeriv_apply]
  simp

/-- **Landau's lemma with a known pole.** Let `g` be analytic on a neighbourhood of
`closedBall c R` with `g c ≠ 0` and `‖g u / g c‖ ≤ B` there (`1 < B`), and let
`f s = g s / (s - p)` for `s ≠ p` in the disc (so `f` has at most a simple pole at `p`). For
`0 < r' < r < R' < R` and `z ∈ closedBall c r'` with `z ≠ p` and `f z ≠ 0`,
`‖f'/f (z) + 1 / (z - p) - ∑_{ρ ∈ closedBall c r} m_g(ρ) / (z - ρ)‖ ≤
landauConstant r' r R' R * log B`. -/
theorem landau_pole_norm_logDeriv_sub_le {f g : ℂ → ℂ} {c p z : ℂ} {r' r R' R B : ℝ}
    (hB : 1 < B) (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R') (hR'R : R' < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hc : g c ≠ 0)
    (hfg : ∀ s ∈ closedBall c R, s ≠ p → f s = g s / (s - p))
    (hbound : ∀ u ∈ closedBall c R, ‖g u / g c‖ ≤ B)
    (hz : z ∈ closedBall c r') (hzp : z ≠ p) (hfz : f z ≠ 0) :
    ‖logDeriv f z + 1 / (z - p) -
        ∑ᶠ ρ ∈ closedBall c r, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ ≤
      landauConstant r' r R' R * Real.log B := by
  have hzb : z ∈ ball c R := by
    rw [mem_closedBall] at hz; rw [mem_ball]; linarith
  obtain ⟨hgz, hlog⟩ := landau_pole_logDeriv hg hfg hzb hzp hfz
  rw [← hlog]
  exact landau_norm_logDeriv_sub_le hB hr' hr'r hrR' hR'R hg hc hbound hz hgz

/-- **Landau's lemma with a known pole, one-sided form.** Under the hypotheses of
`landau_pole_norm_logDeriv_sub_le`, if `S` contains every zero `ρ` of `g` in `closedBall c r`
with `Re z < Re ρ`, then
`-Re f'/f (z) ≤ Re (1 / (z - p)) - ∑_{ρ ∈ closedBall c r ∩ S} Re (m_g(ρ) / (z - ρ))
  + landauConstant r' r R' R * log B`. -/
theorem landau_pole_neg_re_logDeriv_le {f g : ℂ → ℂ} {c p z : ℂ} {r' r R' R B : ℝ}
    (hB : 1 < B) (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R') (hR'R : R' < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hc : g c ≠ 0)
    (hfg : ∀ s ∈ closedBall c R, s ≠ p → f s = g s / (s - p))
    (hbound : ∀ u ∈ closedBall c R, ‖g u / g c‖ ≤ B)
    (hz : z ∈ closedBall c r') (hzp : z ≠ p) (hfz : f z ≠ 0) (S : Set ℂ)
    (hS : ∀ ρ ∈ closedBall c r, g ρ = 0 → ρ ∉ S → ρ.re ≤ z.re) :
    -(logDeriv f z).re ≤ (1 / (z - p)).re -
      ∑ᶠ ρ ∈ closedBall c r ∩ S, ((analyticOrderNatAt g ρ : ℂ) / (z - ρ)).re +
        landauConstant r' r R' R * Real.log B := by
  have h := landau_neg_re_le_aux (finite_zeros_closedBall (R := r) (by linarith)
    (hg.mono (closedBall_subset_closedBall (by linarith))) hc) S hS
    (landau_pole_norm_logDeriv_sub_le hB hr' hr'r hrR' hR'R hg hc hfg hbound hz hzp hfz)
  rw [add_re] at h
  linarith

end RiemannMasullo
