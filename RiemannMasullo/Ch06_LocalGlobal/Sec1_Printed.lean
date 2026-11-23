module

public import RiemannMasullo.Ch06_LocalGlobal.Sec1

/-! # Chapter 6.1: statements that are false as printed -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped MonoidAlgebra TensorProduct

namespace RiemannMasullo

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "L(" F ", " v ")" => HeightOneSpectrum.adicCompletion (R := 𝓞 F) F v
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

/-- Paper: §6.1.2, (6.1.2.2), p. 288. As printed: the full product of the multiplicative
groups outside S, inserted with identity coordinates in S, lies in the global idele group.
This is the ambient inclusion in (6.1.2.2). See `outsideIntegralIdeleUnits` and ERRATA F69. -/
def Printed.outsideLocalUnits_embed_in_ideles : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F)))
    (u : (v : {v : Places(F) // v ∉ S}) → (L(F, v.val))ˣ),
    ∃ g : IdeleGroup (𝓞 F) F, g.val.1 = 1 ∧
      (∀ v ∈ S, g.val.2 v = 1) ∧ ∀ v, g.val.2 v.val = (u v).val

/-- Paper: §6.1.2, (6.1.2.2), p. 288. Over ℚ take S to contain only the infinite place and
choose the component p at every prime p. The tuple is integral everywhere, but its coordinatewise
inverse is nonintegral at every prime, so no idele has these coordinates. -/
theorem Printed.outsideLocalUnits_embed_in_ideles_false :
    ¬ Printed.outsideLocalUnits_embed_in_ideles := by
  classical
  intro h
  let : Infinite (Places(ℚ)) := Infinite.of_injective Rat.HeightOneSpectrum.primesEquiv.symm
    Rat.HeightOneSpectrum.primesEquiv.symm.injective
  have bad (v : Places(ℚ)) : ∃ u : (L(ℚ, v))ˣ, u.val ∉ v.adicCompletionIntegers ℚ := by
    let val := (Valued.v : Valuation (L(ℚ, v)) (WithZero (Multiplicative ℤ)))
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    refine ⟨(Units.mk0 π hπ.ne_zero)⁻¹, (HeightOneSpectrum.notMem_adicCompletionIntegers _ _ v).mpr ?_⟩
    change 1 < val π⁻¹
    rw [map_inv₀]
    exact (one_lt_inv₀ (pos_iff_ne_zero.mpr hπ.val_ne_zero)).mpr hπ.val_lt_one
  choose u hu using bad
  obtain ⟨g, -, -, hg⟩ := h ℚ ∅ (fun v ↦ u v.val)
  obtain ⟨v, hv⟩ := g.val.2.property.exists
  exact hu v ((hg ⟨v, Finset.notMem_empty v⟩) ▸ hv)

open Classical in
/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5)–(6.1.2.6), p. 289. As printed: the monomial-to-ball
assignment extends to a linear homeomorphism from the projective tensor product of the S-local
tests and the Laurent polynomials with their finest locally convex topology to the relative unit
invariants. See `sLocalSchwartz_invariants_laurent_equiv` and ERRATA F70. -/
def Printed.sLocalSchwartz_invariants_projectiveLaurent_equiv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (Places(F))) (hST : S ⊂ T),
    Subsingleton (CommRing.Pic ((S : Set (Places(F))).integer F)) →
    ∀ (π : ∀ v : ↥(T \ S), (L(F, v.val))ˣ),
      (∀ v : ↥(T \ S), Valuation.IsUniformizer
        (Valued.v : Valuation (L(F, v.val)) (WithZero (Multiplicative ℤ))) (π v).val) →
      ∃ e : ProjectiveTensor ℬ(SAdeleRing F S)
          (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) ≃L[ℂ]
          (Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
            (relativeIntegralIdeleUnits F S T).subtype)),
        ∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
          (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
            f (Multiplicative.ofAdd (x.1, fun v : S ↦ x.2 ⟨v.val, hST.le v.property⟩)) *
              ∏ v : ↥(T \ S), finitePlaceBallIndicator v.val (π v) (a v)
                (x.2 ⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩)

/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5), p. 289. Over ℚ add one prime to the archimedean
stage. In ball coordinates the target is a locally convex direct sum of real Schwartz spaces,
where the seminorm `∑_{n ≥ 0} |f_n⁽ⁿ⁾(0)|` is continuous. Each Laurent zero neighborhood contains
a nonzero multiple of every monomial. Joint continuity would therefore bound the derivative of
order k+1 on a Schwartz zero neighborhood controlling derivatives only through order k. A smooth
compactly supported cutoff equal to one near zero times `exp(itx)/t^k`, scaled by a fixed nonzero
constant into that neighborhood, has unbounded derivative of order k+1 at zero. -/
theorem Printed.sLocalSchwartz_invariants_projectiveLaurent_equiv_false :
    ¬ Printed.sLocalSchwartz_invariants_projectiveLaurent_equiv := by sorry

end RiemannMasullo
