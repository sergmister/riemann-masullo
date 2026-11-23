module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a

import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c

/-! # Chapter 5.3: printed properties of the local difference -/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField Set

local notation "Fᵥ[" F "," v "]" => HeightOneSpectrum.adicCompletion F v
local notation "vval[" F "," v "]" =>
  (Valued.v : Valuation Fᵥ[F, v] (WithZero (Multiplicative ℤ)))

/-- Paper: Lemma 5.3.1.1, p. 240. As printed: at every finite place of every
number field the difference on the full local Schwartz–Bruhat space is independent
of the choice of uniformizer, and its range is the kernel of evaluation at zero.
These are the independence and range clauses. See `finitePlaceDifference_eq_of_unitInvariant`,
`finitePlaceDifference_range_on_unitInvariants`, and ERRATA F213. -/
def Printed.finitePlaceDifference_uniformizerIndependent_and_range : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : Fᵥ[F, v]ˣ), vval[F, v].IsUniformizer π.val →
    (∀ (π' : Fᵥ[F, v]ˣ), vval[F, v].IsUniformizer π'.val →
      finitePlaceDifference v π = finitePlaceDifference v π') ∧
    range (finitePlaceDifference v π) = {f | f (Multiplicative.ofAdd 0) = 0}

/-- Paper: Lemma 5.3.1.1, p. 240. At the place 3 of ℚ take f to be the
indicator of 1 + 3ℤ₃. The differences for the uniformizers 3 and −3 give
values −1 and 0 at 3. The function f vanishes at zero. For any uniformizer π,
an equation f = Pᵥ(h) forces h(x) = Σ_{j ≥ 0} f(π^(-j)x) for x ≠ 0 by
telescoping and compact support. It follows that h(πʲ) = 1 and h(2πʲ) = 0
for all j ≥ 0, contradicting local constancy at zero. -/
theorem Printed.finitePlaceDifference_uniformizerIndependent_and_range_false :
    ¬ Printed.finitePlaceDifference_uniformizerIndependent_and_range := by
  classical
  intro h
  let v : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
  let K := Fᵥ[ℚ, v]
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let : LocallyCompactSpace (Multiplicative K) := locallyCompactSpace_adicCompletion v
  let val := (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
  obtain ⟨p, hp⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π := Units.mk0 (p : K) hp.ne_zero
  have hneg : val.IsUniformizer (-π).val := by
    change val (-(p : K)) = _
    rw [Valuation.map_neg]
    exact hp
  have hh := (h ℚ v π hp).1 (-π) hneg
  let a := Multiplicative.ofAdd (1 : K)
  let b := Multiplicative.ofAdd (-1 : K)
  have hab : a ≠ b := by
    change (1 : K) ≠ -1
    norm_num
  obtain ⟨f, -, hs, hf⟩ := schwartzBruhat_exists_local_unit
    (x := a) (U := ({b}ᶜ : Set (Multiplicative K))) isClosed_singleton.isOpen_compl hab
  have ha : f.val a = 1 := hf.eq_of_nhds
  have hb : f.val b = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem ↦ hs hmem (mem_singleton b))
  have he := congrArg (fun L ↦ (L f).val (Multiplicative.ofAdd (p : K))) hh
  change f.val _ - f.val (Multiplicative.ofAdd ((↑π⁻¹ : K) * p)) =
    f.val _ - f.val (Multiplicative.ofAdd ((↑(-π)⁻¹ : K) * p)) at he
  have hu : (↑π⁻¹ : K) * p = 1 := by simp [π, hp.ne_zero]
  have hv : (↑(-π)⁻¹ : K) * p = -1 := by simp [π, hp.ne_zero]
  rw [hu, hv, ha, hb] at he
  simp at he

end RiemannMasullo
