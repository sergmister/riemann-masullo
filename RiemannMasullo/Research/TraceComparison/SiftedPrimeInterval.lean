module

public import Mathlib.NumberTheory.LSeries.WeakPNT

/-! # Integers surviving a prime cutoff in a moving interval

For a real parameter `Y`, remove integers divisible by a prime at most `Y`.
Above `Y` and up to `Y²`, the survivors are precisely the primes. The prime
number theorem then gives the limiting count in every fixed scaled interval
`(aY, bY]` with `1 ≤ a < b`.
-/

@[expose] public noncomputable section

open Filter

open scoped Topology

namespace RiemannMasullo

/-- Integers in `(aY, bY]` with no prime divisor at most `Y`. -/
def siftedNatInterval (Y a b : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊a * Y⌋₊ ⌊b * Y⌋₊).filter fun n ↦ ∀ p ∈ ⌊Y⌋₊.primesLE, ¬p ∣ n

/-- In `(Y, Y²]`, a composite integer always has a prime divisor at most `Y`. -/
theorem no_small_prime_divisor_iff_prime {Y : ℝ} {n : ℕ} (hY : 1 ≤ Y)
    (hn : Y < n) (hn₂ : (n : ℝ) ≤ Y ^ 2) :
    (∀ p ∈ ⌊Y⌋₊.primesLE, ¬p ∣ n) ↔ n.Prime := by
  have hY₀ : 0 ≤ Y := by linarith
  constructor
  · intro h
    by_contra hcomp
    have hn₁ : 1 < n := by exact_mod_cast hY.trans_lt hn
    have hsq : (n.minFac : ℝ) ^ 2 ≤ n := by
      exact_mod_cast Nat.minFac_sq_le_self (by omega) hcomp
    have hsmall : (n.minFac : ℝ) ≤ Y := by
      by_contra! hlarge
      nlinarith [mul_pos (sub_pos.mpr hlarge) (show 0 < (n.minFac : ℝ) + Y by positivity)]
    exact h n.minFac (Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff hY₀).mpr hsmall, Nat.minFac_prime (by omega)⟩) (Nat.minFac_dvd n)
  · intro hp p hmem hdvd
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hmem
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hprime hp).mp hdvd
    exact hn.not_ge ((Nat.le_floor_iff hY₀).mp hle)

/-- Once `Y ≥ b`, sifting the interval amounts to taking the difference of two
finite sets of primes. The left endpoint is excluded and the right is included. -/
theorem siftedNatInterval_eq_primesLE_sdiff {Y a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hbY : b ≤ Y) :
    siftedNatInterval Y a b = ⌊b * Y⌋₊.primesLE \ ⌊a * Y⌋₊.primesLE := by
  have hY : 1 ≤ Y := ha.trans (hab.trans hbY)
  have hY₀ : 0 ≤ Y := by linarith
  have hb₀ : 0 ≤ b * Y := mul_nonneg (by linarith) hY₀
  ext n
  simp only [siftedNatInterval, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]
  have core (h : ⌊a * Y⌋₊ < n ∧ n ≤ ⌊b * Y⌋₊) :
      (∀ p ∈ ⌊Y⌋₊.primesLE, ¬p ∣ n) ↔ n.Prime := by
    apply no_small_prime_divisor_iff_prime hY
    · exact (le_mul_of_one_le_left hY₀ ha).trans_lt (Nat.lt_of_floor_lt h.1)
    · calc (n : ℝ) ≤ b * Y := (Nat.le_floor_iff hb₀).mp h.2
           _ ≤ Y ^ 2 := by simpa [sq] using mul_le_mul_of_nonneg_right hbY hY₀
  constructor
  · rintro ⟨hI, hs⟩
    exact ⟨Nat.mem_primesLE.mpr ⟨hI.2, (core hI).mp hs⟩,
      fun h ↦ hI.1.not_ge (Nat.le_of_mem_primesLE h)⟩
  · rintro ⟨hu, hl⟩
    obtain ⟨hub, hp⟩ := Nat.mem_primesLE.mp hu
    have hlo : ⌊a * Y⌋₊ < n := lt_of_not_ge fun h ↦ hl (Nat.mem_primesLE.mpr ⟨h, hp⟩)
    exact ⟨⟨hlo, hub⟩, (core ⟨hlo, hub⟩).mpr hp⟩

private theorem tendsto_scaled_primeCounting (c : ℝ) (hc : 0 < c) :
    Tendsto (fun Y : ℝ ↦ Real.log Y / Y * (Nat.primeCounting ⌊c * Y⌋₊ : ℝ))
      atTop (𝓝 c) := by
  have hscale : Tendsto (fun Y : ℝ ↦ c * Y) atTop atTop := tendsto_id.const_mul_atTop hc
  have hp := (Asymptotics.isEquivalent_iff_tendsto_one (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne')).mp Nat.isEquivalent_primeCounting
  have hlog : Tendsto (fun Y : ℝ ↦ Real.log (c * Y) / Real.log Y) atTop (𝓝 1) := by
    have h := (show Tendsto (fun Y : ℝ ↦ Real.log c / Real.log Y) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add_const 1
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
    rw [Real.log_mul hc.ne' (by linarith), add_div, div_self (Real.log_pos hY).ne']
  have h := ((hp.comp hscale).mul_const c).div hlog (by norm_num)
  rw [one_mul, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ), hscale.eventually (eventually_gt_atTop 1)] with Y hY hcY
  change ((Nat.primeCounting ⌊c * Y⌋₊ : ℝ) / (c * Y / Real.log (c * Y)) * c) /
    (Real.log (c * Y) / Real.log Y) = _
  field_simp [hc.ne', (show Y ≠ 0 by linarith), (Real.log_pos hY).ne', (Real.log_pos hcY).ne']

/-- The count of integers surviving all primes up to `Y` in `(aY, bY]`,
normalized by `log Y / Y`, tends to the interval length. -/
theorem tendsto_siftedNatInterval_card {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    Tendsto (fun Y : ℝ ↦ Real.log Y / Y * ((siftedNatInterval Y a b).card : ℝ))
      atTop (𝓝 (b - a)) := by
  have h := (tendsto_scaled_primeCounting b (by linarith)).sub
    (tendsto_scaled_primeCounting a (by linarith))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop b] with Y hY
  have hf : ⌊a * Y⌋₊ ≤ ⌊b * Y⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_right hab.le (by linarith))
  rw [siftedNatInterval_eq_primesLE_sdiff ha hab.le hY, Finset.card_sdiff_of_subset
    (Nat.primesLE_mono hf), Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting,
    Nat.cast_sub (Nat.monotone_primeCounting hf), mul_sub]

end RiemannMasullo
