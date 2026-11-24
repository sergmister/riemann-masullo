module

public import RiemannMasullo.Research.TraceComparison.SiftedPrimeInterval

/-! # Removing one prime from a positive-integer sum

Multiplication by a prime outside a finite set of primes preserves the
condition of being divisible by none of them. It parametrizes exactly the
terms removed on adjoining the new prime to the sieve.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The positive integers divisible by no member of `S`. -/
def siftedPositiveNaturals (S : Finset ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∀ q ∈ S, ¬q ∣ n}

/-- The moving interval uses the same sieve with all primes at most `Y`. -/
theorem mem_siftedNatInterval_iff {Y a b : ℝ} {n : ℕ} :
    n ∈ siftedNatInterval Y a b ↔
      n ∈ Finset.Ioc ⌊a * Y⌋₊ ⌊b * Y⌋₊ ∧ n ∈ siftedPositiveNaturals ⌊Y⌋₊.primesLE := by
  rw [siftedNatInterval, Finset.mem_filter]
  exact ⟨fun ⟨hn, h⟩ ↦ ⟨hn, (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hn).1, h⟩,
    fun ⟨hn, h⟩ ↦ ⟨hn, h.2⟩⟩

/-- Multiplication by a new prime preserves the old sieve in both directions. -/
theorem mul_mem_siftedPositiveNaturals_iff {S : Finset ℕ} {p n : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hp : p.Prime) (hpS : p ∉ S) :
    p * n ∈ siftedPositiveNaturals S ↔ n ∈ siftedPositiveNaturals S := by
  constructor
  · rintro ⟨hpos, hdiv⟩
    refine ⟨?_, fun q hq hd ↦ hdiv q hq (dvd_mul_of_dvd_right hd p)⟩
    by_contra! hn
    simp [Nat.eq_zero_of_le_zero hn] at hpos
  · rintro ⟨hpos, hdiv⟩
    refine ⟨Nat.mul_pos hp.pos hpos, fun q hq hd ↦ ?_⟩
    rcases (hS q hq).dvd_mul.mp hd with hqp | hqn
    · exact hpS (((Nat.prime_dvd_prime_iff_eq (hS q hq) hp).mp hqp) ▸ hq)
    · exact hdiv q hq hqn

/-- Adjoining a new prime subtracts the old sifted sum evaluated at multiples
of that prime. Both sums start at positive integers, including one. -/
theorem tsum_siftedPositiveNaturals_insert {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {S : Finset ℕ} {p : ℕ} (hS : ∀ q ∈ S, Nat.Prime q) (hp : p.Prime) (hpS : p ∉ S)
    (F : ℕ → E) (hF : Summable F) :
    (∑' n : siftedPositiveNaturals (insert p S), F n.val) =
      (∑' n : siftedPositiveNaturals S, F n.val) -
        ∑' n : siftedPositiveNaturals S, F (p * n.val) := by
  classical
  let multiples := (fun n : ℕ ↦ p * n) '' siftedPositiveNaturals S
  have hpartition : siftedPositiveNaturals (insert p S) ∪ multiples = siftedPositiveNaturals S := by
    ext n
    constructor
    · rintro (hn | ⟨k, hk, rfl⟩)
      · exact ⟨hn.1, fun q hq ↦ hn.2 q (Finset.mem_insert_of_mem hq)⟩
      · exact (mul_mem_siftedPositiveNaturals_iff hS hp hpS).mpr hk
    · intro hn
      by_cases hd : p ∣ n
      · obtain ⟨k, rfl⟩ := hd
        exact Or.inr ⟨k, (mul_mem_siftedPositiveNaturals_iff hS hp hpS).mp hn, rfl⟩
      · refine Or.inl ⟨hn.1, fun q hq ↦ ?_⟩
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hd
        · exact hn.2 q hq
  have hdis : Disjoint (siftedPositiveNaturals (insert p S)) multiples := by
    refine Set.disjoint_left.mpr ?_
    rintro _ hn ⟨k, _, rfl⟩
    exact hn.2 p (Finset.mem_insert_self _ _) (dvd_mul_right p k)
  have hinj : Function.Injective (fun n : ℕ ↦ p * n) := fun _ _ h ↦ mul_left_cancel₀ hp.ne_zero h
  have hremoved : (∑' n : multiples, F n.val) = ∑' n : siftedPositiveNaturals S, F (p * n.val) :=
    tsum_image F hinj.injOn
  have hsum := Summable.tsum_union_of_disjoint (f := F) hdis (hF.subtype _) (hF.subtype _)
  rw [hpartition, hremoved] at hsum
  exact eq_sub_iff_add_eq.mpr hsum.symm

end RiemannMasullo
