module

public import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
import RiemannMasullo.Research.PositiveStrip.SingleGenerator

/-!
# Rates for cutting off high zeros of a bounded strip multiplier

A Blaschke tail omitting zeros above height `T` is uniformly close to one up
to height `T / 2` on any strictly narrower strip. The bounds use multiplicities
and do not depend on the distances between distinct zeros.
-/

@[expose] public noncomputable section

open Metric Real Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

/-- Every height approaches an end of the strip-to-disk coordinate at least
exponentially fast, uniformly over the open strip's real coordinate. -/
theorem strip_chart_deficit_le (A k : ℝ) (hk : 0 < k) (w : ℂ)
    (hw : |w.re - A| < (π / 2) / k) :
    1 - ‖stripBlaschkeToDisk (A : ℂ) k w‖ ≤ 2 * exp (-k * |w.im|) := by
  let t : ℂ := (k : ℂ) * (Complex.I * (w - (A : ℂ)))
  let u := Complex.exp t
  let z := (u - 1) / (u + 1)
  have him : t.im = k * (w.re - A) := by simp [t]
  have hre : t.re = -k * w.im := by simp [t]
  have hphase : |t.im| < π / 2 := by
    rw [him, abs_mul, abs_of_pos hk, mul_comm]
    exact (lt_div_iff₀ hk).mp hw
  have hu : 0 < u.re := by
    rw [show u.re = exp t.re * cos t.im from Complex.exp_re _]
    exact mul_pos (exp_pos _) (cos_pos_of_mem_Ioo (abs_lt.mp hphase))
  have hn : ‖u‖ = exp (-k * w.im) := by simp only [u, Complex.norm_exp, hre]
  have h1 : 1 ≤ ‖u + 1‖ :=
    (show 1 ≤ (u + 1).re by simpa using hu.le).trans (Complex.re_le_norm _)
  have h2 : ‖u‖ ≤ ‖u + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im, add_zero]
    nlinarith
  have hne : u + 1 ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le h1)
  change 1 - ‖z‖ ≤ _
  by_cases hs : 0 ≤ w.im
  · rw [abs_of_nonneg hs, ← hn]
    have hz : 1 + z = (2 * u) / (u + 1) := by dsimp [z]; field_simp; ring
    calc
      _ ≤ ‖1 + z‖ := by simpa using norm_sub_le_norm_add (1 : ℂ) z
      _ = 2 * ‖u‖ / ‖u + 1‖ := by rw [hz, norm_div, norm_mul]; norm_num
      _ ≤ _ := div_le_self (by positivity) h1
  · rw [abs_of_neg (lt_of_not_ge hs), mul_neg, Real.exp_neg, ← hn]
    have hz : 1 - z = 2 / (u + 1) := by dsimp [z]; field_simp; ring
    calc
      _ ≤ ‖1 - z‖ := by simpa using norm_sub_norm_le (1 : ℂ) z
      _ = 2 / ‖u + 1‖ := by rw [hz, norm_div]; norm_num
      _ ≤ 2 / ‖u‖ := div_le_div_of_nonneg_left (by norm_num) (by rw [hn]; positivity) h2
      _ = _ := div_eq_mul_inv ..

/-- An explicit majorant for an exponential moment in terms of a quadratic
reciprocal moment, uniform in the family of heights and masses. -/
theorem exponential_heights_le_quadratic_mass {ι : Type*} (t mass : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hm : ∀ i, 0 ≤ mass i) (q : ℝ) (hq : 0 < q)
    (hs : Summable fun i ↦ mass i / (1 + t i) ^ 2) :
    Summable (fun i ↦ mass i * exp (-q * t i)) ∧
      ∑' i, mass i * exp (-q*t i) ≤ (1+2/q)^2 * ∑' i, mass i/(1+t i)^2 := by
  let C := 1 + 2 / q
  have hc : 0 < C := by dsimp [C]; positivity
  have hc1 : 1 ≤ C := by dsimp [C]; linarith [div_pos (by norm_num : (0 : ℝ) < 2) hq]
  have hcq : 1 ≤ C * q / 2 := by dsimp [C]; field_simp; linarith
  have hbound (i : ι) : mass i * exp (-q*t i) ≤ C^2 * (mass i/(1+t i)^2) := by
    let x := t i
    have hx : 0 ≤ x := ht i
    have h₁ : 1 + x ≤ C * exp (q * x / 2) := by
      calc
        _ ≤ C * (q * x / 2 + 1) := by nlinarith [mul_le_mul_of_nonneg_right hcq hx]
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_one_le_exp _) hc.le
    have h₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + x) h₁ 2
    have h3 : exp (q * x / 2) ^ 2 = exp (q * x) := by
      rw [sq, ← exp_add]; congr 1; ring
    rw [mul_pow, h3] at h₂
    change mass i * exp (-q * x) ≤ C ^ 2 * (mass i / (1 + x) ^ 2)
    rw [neg_mul, exp_neg, ← div_eq_mul_inv, ← mul_div_assoc, div_le_div_iff₀ (exp_pos _) (by positivity)]
    calc
      _ ≤ mass i * (C ^ 2 * exp (q * x)) := mul_le_mul_of_nonneg_left h₂ (hm i)
      _ = _ := by ring

  have h := (hs.mul_left (C^2)).of_nonneg_of_le (fun i ↦ mul_nonneg (hm i) (exp_pos _).le) hbound
  exact ⟨h,(h.tsum_le_tsum hbound (hs.mul_left (C^2))).trans_eq (tsum_mul_left)⟩

/-- A quadratic reciprocal moment controls any one exponential moment of an
unbounded family of heights. Each index is counted with its supplied mass. -/
theorem summable_exponential_heights {ι : Type*} (t mass : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hm : ∀ i, 0 ≤ mass i) (q : ℝ) (hq : 0 < q)
    (hs : Summable fun i ↦ mass i / (1 + t i) ^ 2) :
    Summable fun i ↦ mass i * exp (-q * t i) := (exponential_heights_le_quadratic_mass t mass ht hm q hq hs).1

/-- The total disk mass of zeros above `T` decays exponentially even when jets
coalesce. The input is the quadratic height moment from the zero count. -/
theorem strip_chart_tail_mass_le_explicit {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (A k : ℝ) (hk : 0 < k)
    (ha : ∀ i, |(a i).re - A| < (π / 2) / k)
    (hs : Summable fun i ↦ (m i : ℝ) / (1 + |(a i).im|) ^ 2) :
    let b := fun i ↦ stripBlaschkeToDisk (A : ℂ) k (a i)
    Summable (fun i ↦ (m i : ℝ) * (1 - ‖b i‖)) ∧
    ∃ C ≥ 0, C ≤ 2*(1+2/(k/4))^2*(∑' i, (m i : ℝ)/(1+|(a i).im|)^2) ∧
      ∀ (S : Finset ι) (T : ℝ), (∀ i ∉ S, T ≤ |(a i).im|) →
      ∑' j : {i // i ∉ S}, (m j.val : ℝ) * (1 - ‖b j.val‖) ≤ C * exp (-(3*k/4) * T) := by
  intro b
  let q := k / 4
  let g (i : ι) := (m i : ℝ) * exp (-q * |(a i).im|)
  have hq : 0 < q := by dsimp [q]; positivity
  have hmass := exponential_heights_le_quadratic_mass _ _ (fun _ ↦ abs_nonneg _)
    (fun _ ↦ Nat.cast_nonneg _) q hq hs
  have hsum : Summable g := hmass.1
  have hpos (i : ι) : 0 ≤ g i := by dsimp [g]; positivity
  have hb (i : ι) : ‖b i‖ < 1 :=
    mem_ball_zero_iff.mp (stripBlaschkeToDisk_mem hk (by simpa using ha i))
  have H (i : ι) (T : ℝ) (hT : T ≤ |(a i).im|) :
      (m i : ℝ) * (1 - ‖b i‖) ≤ (2 * exp (-(3*k/4)*T)) * g i := by
    have he : exp (-k * |(a i).im|) ≤ exp (-(3*k/4)*T) * exp (-q * |(a i).im|) := by
      rw [← exp_add, exp_le_exp]
      dsimp [q]
      nlinarith [mul_le_mul_of_nonneg_left hT hk.le]
    calc
      _ ≤ (m i : ℝ) * (2 * exp (-k * |(a i).im|)) :=
        mul_le_mul_of_nonneg_left (strip_chart_deficit_le A k hk (a i) (ha i)) (Nat.cast_nonneg _)
      _ ≤ (m i : ℝ) * (2 * (exp (-(3*k/4)*T) * exp (-q * |(a i).im|))) := by gcongr
      _ = _ := by dsimp [g]; ring
  have hs' : Summable fun i ↦ (m i : ℝ) * (1 - ‖b i‖) := by
    apply (hsum.mul_left (2 * exp (-(3*k/4)*0))).of_nonneg_of_le
      (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hb i).le))
    exact fun i ↦ H i 0 (abs_nonneg _)
  refine ⟨hs', 2 * ∑' i, g i, mul_nonneg (by norm_num) (tsum_nonneg hpos), ?_, ?_⟩
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass.2 (by norm_num : (0 : ℝ) ≤ 2)
  intro S T hT
  let c := 2 * exp (-(3*k/4)*T)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsub : (∑' j : {i // i ∉ S}, g j.val) ≤ ∑' i, g i :=
    tsum_comp_le_tsum_of_inj hsum hpos Subtype.val_injective
  calc
    _ ≤ ∑' j : {i // i ∉ S}, c * g j.val :=
      (hs'.subtype _).tsum_le_tsum (fun j ↦ H j.val T (hT j.val j.property)) ((hsum.subtype _).mul_left c)
    _ = c * ∑' j : {i // i ∉ S}, g j.val := tsum_mul_left
    _ ≤ c * ∑' i, g i := mul_le_mul_of_nonneg_left hsub hc
    _ = _ := by dsimp [c]; ring



/-- The total disk mass of zeros above `T` decays exponentially even when jets
coalesce. The input is the quadratic height moment from the zero count. -/
theorem strip_chart_tail_mass_le {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (A k : ℝ) (hk : 0 < k)
    (ha : ∀ i, |(a i).re - A| < (π / 2) / k)
    (hs : Summable fun i ↦ (m i : ℝ) / (1 + |(a i).im|) ^ 2) :
    let b := fun i ↦ stripBlaschkeToDisk (A : ℂ) k (a i)
    Summable (fun i ↦ (m i : ℝ) * (1 - ‖b i‖)) ∧
    ∃ C ≥ 0, ∀ (S : Finset ι) (T : ℝ), (∀ i ∉ S, T ≤ |(a i).im|) →
      ∑' j : {i // i ∉ S}, (m j.val : ℝ) * (1 - ‖b j.val‖) ≤ C * exp (-(3*k/4) * T) := by
  obtain ⟨hs',C,hC,-,h⟩ := strip_chart_tail_mass_le_explicit a m A k hk ha hs
  exact ⟨hs',C,hC,h⟩

/-- A common strip-width factor times the quadratic divisor mass controls the
Blaschke-tail error on each central half-window. Each omitted point keeps
its full prescribed order. -/
theorem exists_strip_tails_with_mass_bound {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (A k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hw : k*d < π/2)
    (ha : ∀ i, |(a i).re - A| < (π / 2) / k)
    (h0 : ∀ i, stripBlaschkeToDisk (A : ℂ) k (a i) ≠ 0)
    (hs : Summable fun i ↦ (m i : ℝ) / (1 + |(a i).im|) ^ 2) :
    ∃ (B : Finset ι → ℂ → ℂ) (C : ℝ), 0 ≤ C ∧
      C ≤ (2*(2/cos (k*d))) * (2*(1+2/(k/4))^2*(∑' i, (m i : ℝ)/(1+|(a i).im|)^2)) ∧
      (∀ S, AnalyticOnNhd ℂ (B S) {z | |z.re - A| < (π / 2) / k}) ∧
      (∀ S z, |z.re - A| < (π / 2) / k → ‖B S z‖ ≤ 1) ∧
      (∀ S i, i ∉ S → (m i : ℕ∞) ≤ analyticOrderAt (B S) (a i)) ∧
      ∀ S T, (∀ i ∉ S, T ≤ |(a i).im|) → ∀ z : ℂ, |z.re - A| ≤ d → |z.im| ≤ T/2 →
        ‖B S z - 1‖ ≤ C * exp (-(k/4)*T) := by
  let φ := stripBlaschkeToDisk (A : ℂ) k
  have hmap (z : ℂ) (hz : |z.re-A| < (π/2)/k) : φ z ∈ ball 0 1 :=
    stripBlaschkeToDisk_mem hk (by simpa using hz)
  have hφ (z : ℂ) (hz : |z.re-A| < (π/2)/k) : AnalyticAt ℂ φ z :=
    stripBlaschkeToDisk_analytic hk (by simpa using hz)
  obtain ⟨hsum, M, hM, hMmass, htail⟩ := strip_chart_tail_mass_le_explicit a m A k hk ha hs
  obtain ⟨D, hD, hb, hdist, hv⟩ := Blaschke.exists_holomorphic_disk_tails_bound
    (φ ∘ a) m h0 (fun i ↦ mem_ball_zero_iff.mp (hmap _ (ha i))) hsum
  let L := 2 / cos (k*d)
  have hcos : 0 < cos (k*d) := cos_pos_of_mem_Ioo ⟨by linarith [mul_nonneg hk.le hd, pi_pos], hw⟩
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨fun S ↦ D S ∘ φ, (2*L)*M, by positivity, mul_le_mul_of_nonneg_left hMmass (by positivity : 0 ≤ 2*L),
    fun S w hw ↦ (hD S _ (hmap w hw)).comp (hφ w hw),
    fun S w hw ↦ hb S _ (mem_ball_zero_iff.mp (hmap w hw)), ?_, ?_⟩
  · intro S i hi
    have hdi := hD S _ (hmap _ (ha i))
    apply natCast_le_analyticOrderAt_comp hdi (hφ _ (ha i))
    exact (natCast_le_analyticOrderAt hdi).mpr (hv S i hi)
  · intro S T hT z hz ht
    have hz' := mem_ball_zero_iff.mp (hmap z (hz.trans_lt ((lt_div_iff₀ hk).mpr (by linarith))))
    have hrec : (1 - ‖φ z‖)⁻¹ ≤ L * exp (k*|z.im|) :=
      stripReciprocal_chart_gap A k d hk hd hw z hz
    have hfac : (1 + ‖φ z‖) / (1 - ‖φ z‖) ≤ 2 * (L * exp (k*|z.im|)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (by linarith) hrec (inv_nonneg.mpr (sub_nonneg.mpr hz'.le)) (by norm_num)
    have he : exp (k*|z.im|) * exp (-(3*k/4)*T) ≤ exp (-(k/4)*T) := by
      rw [← exp_add, exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_left ht hk.le]
    calc
      _ ≤ _ := hdist S (φ z) hz'
      _ ≤ (2*(L * exp (k*|z.im|))) * (M * exp (-(3*k/4)*T)) :=
        mul_le_mul hfac (htail S T hT)
          (tsum_nonneg (fun j ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr
            (mem_ball_zero_iff.mp (hmap _ (ha j.val))).le))) (by positivity)
      _ = ((2*L)*M) * (exp (k*|z.im|) * exp (-(3*k/4)*T)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

/-- Geometric distance from the disk boundary bounds the pointwise error on the
central half of a height window. The tail still vanishes to the full prescribed
order at every omitted point. -/
theorem exists_quantitative_strip_tails {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (A k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hw : k*d < π/2)
    (ha : ∀ i, |(a i).re - A| < (π / 2) / k)
    (h0 : ∀ i, stripBlaschkeToDisk (A : ℂ) k (a i) ≠ 0)
    (hs : Summable fun i ↦ (m i : ℝ) / (1 + |(a i).im|) ^ 2) :
    ∃ (B : Finset ι → ℂ → ℂ) (C : ℝ), 0 ≤ C ∧
      (∀ S, AnalyticOnNhd ℂ (B S) {z | |z.re - A| < (π / 2) / k}) ∧
      (∀ S z, |z.re - A| < (π / 2) / k → ‖B S z‖ ≤ 1) ∧
      (∀ S i, i ∉ S → (m i : ℕ∞) ≤ analyticOrderAt (B S) (a i)) ∧
      ∀ S T, (∀ i ∉ S, T ≤ |(a i).im|) → ∀ z : ℂ, |z.re - A| ≤ d → |z.im| ≤ T/2 →
        ‖B S z - 1‖ ≤ C * exp (-(k/4)*T) := by
  obtain ⟨B,C,hC,-,h⟩ := exists_strip_tails_with_mass_bound a m A k d hk hd hw ha h0 hs
  exact ⟨B,C,hC,h⟩

/-- A two-sided resolvent gains two powers of height uniformly in a narrower
strip. This bound follows by taking the real part of its denominator. -/
theorem resolvent_norm_le {c d : ℝ} (hd : 0 ≤ d) (hgap : d < c) (z : ℂ)
    (hz : |z.re| ≤ d) :
    ‖(((c : ℂ) ^ 2 - z ^ 2)⁻¹)‖ ≤ (c ^ 2 - d ^ 2 + z.im ^ 2)⁻¹ := by
  have hm : 0 < c ^ 2 - d ^ 2 :=
    sub_pos.mpr ((sq_lt_sq₀ hd (hd.trans hgap.le)).mpr hgap)
  have hre : (c ^ 2 - d ^ 2 + z.im ^ 2) ≤ (((c : ℂ)^2 - z^2)).re := by
    have h := (sq_le_sq₀ (abs_nonneg _) hd).mpr hz
    rw [sq_abs] at h
    simp only [sq, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    nlinarith
  rw [norm_inv]
  exact inv_anti₀ (by positivity) (hre.trans (Complex.re_le_norm _))

/-- A contractive cutoff exponentially close to one on the central half-window
times the resolvent has error of order `T⁻²` throughout the narrower strip. -/
theorem cutoff_resolvent_norm_le_explicit {c d k C : ℝ} (hd : 0 ≤ d) (hgap : d < c) (hk : 0 < k)
    (hC : 0 ≤ C) :
    ∃ M ≥ 0, M ≤ 8 + (2/k^2/(c^2-d^2))*C ∧ ∀ T : ℝ, 0 < T → ∀ (b : ℂ → ℂ),
      (∀ z : ℂ, |z.re| ≤ d → ‖b z‖ ≤ 1) →
      (∀ z : ℂ, |z.re| ≤ d → |z.im| ≤ T/2 → ‖b z - 1‖ ≤ C * exp (-k*T)) →
      ∀ z : ℂ, |z.re| ≤ d →
        ‖(b z - 1) * (((c : ℂ) ^ 2 - z ^ 2)⁻¹)‖ ≤ M / T^2 := by
  let g := c^2-d^2
  have hg : 0 < g := sub_pos.mpr ((sq_lt_sq₀ hd (hd.trans hgap.le)).mpr hgap)
  let L := 2 / k^2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨max (C * L / g) 8, le_trans (by norm_num : (0 : ℝ) ≤ 8) (le_max_right _ _), ?_, ?_⟩
  · apply max_le
    · dsimp only [L,g]
      linarith only [show C*(2/k^2)/(c^2-d^2) = 2/k^2/(c^2-d^2)*C by ring]
    · linarith only [mul_nonneg (div_nonneg (by positivity : 0 ≤ 2/k^2) hg.le) hC]
  intro T hT b hbc hsmall z hz
  have hT2 : 0 < T^2 := pow_pos hT _
  rw [norm_mul]
  by_cases hmid : |z.im| ≤ T / 2
  · have he : exp (-k*T) ≤ L / T^2 := by
      rw [neg_mul, exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) hT2, one_mul]
      have h := Real.quadratic_le_exp_of_nonneg (mul_nonneg hk.le hT.le)
      dsimp [L]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [h, mul_nonneg hk.le hT.le]
    have hr : (g + z.im^2)⁻¹ ≤ g⁻¹ := inv_anti₀ hg (le_add_of_nonneg_right (sq_nonneg _))
    calc
      _ ≤ (C * (L / T^2)) * g⁻¹ := mul_le_mul ((hsmall z hz hmid).trans
        (mul_le_mul_of_nonneg_left he hC)) ((resolvent_norm_le hd hgap z hz).trans hr)
          (norm_nonneg _) (by positivity)
      _ = (C * L / g) / T^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hT2.le
  · have hhi : T/2 < |z.im| := lt_of_not_ge hmid
    have hs : T^2 ≤ 4*(g+z.im^2) := by
      have hx := (sq_le_sq₀ (by positivity : 0 ≤ T/2) (abs_nonneg _)).mpr hhi.le
      rw [sq_abs] at hx
      nlinarith
    have hres : (g + z.im^2)⁻¹ ≤ 4 / T^2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hT2, one_mul]
      exact hs
    have hb : ‖b z - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖b z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith [hbc z hz]
    calc
      _ ≤ 2 * (4 / T^2) := mul_le_mul hb ((resolvent_norm_le hd hgap z hz).trans hres) (norm_nonneg _) (by norm_num)
      _ = 8 / T^2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hT2.le

/-- A contractive cutoff exponentially close to one on the central half-window
times the resolvent has error of order `T⁻²` throughout the narrower strip. -/
theorem cutoff_resolvent_norm_le {c d k C : ℝ} (hd : 0 ≤ d) (hgap : d < c) (hk : 0 < k)
    (hC : 0 ≤ C) :
    ∃ M ≥ 0, ∀ T : ℝ, 0 < T → ∀ (b : ℂ → ℂ),
      (∀ z : ℂ, |z.re| ≤ d → ‖b z‖ ≤ 1) →
      (∀ z : ℂ, |z.re| ≤ d → |z.im| ≤ T/2 → ‖b z - 1‖ ≤ C * exp (-k*T)) →
      ∀ z : ℂ, |z.re| ≤ d →
        ‖(b z - 1) * (((c : ℂ) ^ 2 - z ^ 2)⁻¹)‖ ≤ M / T^2 := by
  obtain ⟨M,hM,-,h⟩ := cutoff_resolvent_norm_le_explicit hd hgap hk hC
  exact ⟨M,hM,h⟩

end RiemannMasullo.StripNuclearity
