module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RamificationInertia.Basic

/-! # §7.3.1 Statements that are false as printed -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 3

local notation "chart(" field ", " places ", " χ ")" =>
  quasiCharacterNormTwist (sIdeleQuotientNorm field places)
  (isProperMap_sIdeleQuotientNorm field places).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ))
local notation "period(" places ", " v ")" =>
  (2 * Real.pi / Real.log ((v : places).val.asIdeal.absNorm : ℝ))
local notation "phase(" field ", " places ", " χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(places, v) ∧
    sLocalFiniteRestriction v (chart(field, places, χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" field ", " places ", " v ", " u ")" =>
  (‖(↑(u) : (v : places).val.adicCompletion field)‖ = ((v : places).val.asIdeal.absNorm : ℝ)⁻¹)

/-- Paper: Theorem 7.3.1.2(2), p. 341.
Each listed coefficient is called an eigendistribution of its center. The finite
sets S and T specify the finite parts of the printed S and S₀, both of which
contain all infinite places. Pullback to tests expresses the weight equation. -/
def Printed.sLocalOrbitalPrincipalParts_eigendistributions : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F))),
    IsSaturatedPlaceSet S →
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) → T ⊆ S →
    ∀ (ω : PontryaginDual (sIdeleQuotientNorm F S).ker) (c : QuasiCharacter (SIdeleQuotient F S)),
      normOneRestriction (sIdeleQuotientNorm F S) c =
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω →
      0 < sLocalRhoPoleOrder c →
      ∀ k : ℕ, sLocalRhoPoleOrder c - ((sLocalArchPolePlaces c).card +
          sLocalFinitePoleMultiplicity T c) < k → k ≤ sLocalRhoPoleOrder c →
        sLocalPrincipalPartCoeff c k ∈ sLocalEigendistributions c

/-- A function meromorphic at `0` with a simple pole there has nonzero residue. -/
private theorem sLocalOrbitalPrincipalParts_eigendistributions_false_residue_ne_zero
    {L : ℂ → ℂ} (hM : MeromorphicAt L 0)
    (hge : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt L 0)
    (hlt : meromorphicOrderAt L 0 < 0) :
    complexResidue L 0 ≠ 0 := by
  have hord : meromorphicOrderAt L 0 = ((-1 : ℤ) : WithTop ℤ) := by
    cases ho : meromorphicOrderAt L 0 with
    | top => rw [ho] at hlt; exact absurd hlt (not_lt_of_ge le_top)
    | coe n =>
      rw [ho] at hge hlt
      have h1 : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp hge
      have h2 : n < 0 := WithTop.coe_lt_coe.mp hlt
      exact congrArg (WithTop.some : ℤ → WithTop ℤ) (by omega)
  obtain ⟨H, hH, hH0, hL⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) hM).mp hord
  have he : L =ᶠ[nhdsWithin 0 ({0}ᶜ)] (fun z ↦ H z / (z - 0)) := by
    filter_upwards [hL] with z hz
    simpa only [sub_zero, zpow_neg_one, smul_eq_mul, div_eq_inv_mul] using hz
  rw [sLocalPrincipalPartCoeff_translate_congr he, complexResidue_div_sub hH]
  exact hH0

open scoped TensorProduct in
/-- A pure tensor of local tests on the `S`-adeles of `ℚ`. -/
private theorem sLocalOrbitalPrincipalParts_eigendistributions_false_tensor
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (a : (w : InfinitePlace ℚ) → SchwartzBruhat (Multiplicative w.Completion))
    (b : (v : S) → SchwartzBruhat (Multiplicative (v.val.adicCompletion ℚ))) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S)), ∀ x : SAdeleRing ℚ S,
      f (Multiplicative.ofAdd x) =
        (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v, b v (Multiplicative.ofAdd (x.2 v)) := by
  let w : InfinitePlace ℚ := default
  let e : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative w.Completion :=
    { Homeomorph.piUnique (fun i : InfinitePlace ℚ ↦ i.Completion) with map_mul' := fun _ _ ↦ rfl }
  let : T2Space (Multiplicative w.Completion) := inferInstanceAs (T2Space w.Completion)
  let : LocallyCompactSpace (Multiplicative w.Completion) :=
    inferInstanceAs (LocallyCompactSpace w.Completion)
  let : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)) :=
    ⟨(a w).val ∘ e, schwartzBruhat_mem_comp_equiv e (a w).property⟩
  obtain ⟨t, ht⟩ := sAdeleSchwartz_inductiveTensor_equiv ℚ S
  refine ⟨t (arch ⊗ₜ[ℂ] (⨂ₜ[ℂ] v : S, b v)), fun x ↦ ?_⟩
  rw [ht arch b x, Fintype.prod_subsingleton _ w]
  rfl

/-- Paper: Theorem 7.3.1.2(2), p. 341.
For ℚ take S = {∞,2,3}, S₀ = {∞,2}, and c = 1. The real Gaussian times the
integer indicators has a triple pole with leading coefficient 2/(log 2 · log 3).
Dilation of norm 2 multiplies the zeta germ by 2^s and changes the selected
second-order coefficient by (log 2) times the leading coefficient. -/
theorem Printed.sLocalOrbitalPrincipalParts_eigendistributions_false :
    ¬ Printed.sLocalOrbitalPrincipalParts_eigendistributions := by
  classical
  intro h
  let p : HeightOneSpectrum (𝓞 ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := {p}
  have hunder (w : HeightOneSpectrum (𝓞 ℚ)) : w.under (𝓞 ℚ) = w := by
    ext x
    change x ∈ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) w.asIdeal ↔ x ∈ w.asIdeal
    rw [Algebra.algebraMap_self, Ideal.comap_id]
  have hsat : IsSaturatedPlaceSet S := by
    intro v w hv hw
    have hwv : w = v := (hunder w).symm.trans (hw.trans (hunder v))
    rwa [hwv]
  have hpic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)) := by
    have hpid : IsPrincipalIdealRing (𝓞 ℚ) :=
      NumberField.classNumber_eq_one_iff.mp Rat.classNumber_eq
    have : Subsingleton (ClassGroup (𝓞 ℚ)) := inferInstance
    have : Fact (IsMulTorsion (ClassGroup (𝓞 ℚ))) :=
      ⟨fun x ↦ by rw [Subsingleton.elim x 1]; exact IsOfFinOrder.one⟩
    have : UniqueFactorizationMonoid ((S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) :=
      UniqueFactorizationMonoid.of_isLocalization
        (Localization.submonoid (S : Set (HeightOneSpectrum (𝓞 ℚ)))) _
    let : GCDMonoid ((S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) :=
      UniqueFactorizationMonoid.toGCDMonoid _
    infer_instance
  let c : QuasiCharacter (SIdeleQuotient ℚ S) := 1
  have hR := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)
  have hC := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  have hcardInf : Fintype.card (InfinitePlace ℚ) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC, add_zero]
  have harch1 : sLocalArchPolePlaces (F := ℚ) (S := S) c = Finset.univ :=
    (sLocalPolePlaces_one (F := ℚ) (S := S)).1
  have hfin1 : sLocalFinitePolePlaces (F := ℚ) (S := S) c = Finset.univ :=
    (sLocalPolePlaces_one (F := ℚ) (S := S)).2
  have harchCard : (sLocalArchPolePlaces (F := ℚ) (S := S) c).card = 1 := by
    rw [harch1, Finset.card_univ, hcardInf]
  have hfinCard : (sLocalFinitePolePlaces (F := ℚ) (S := S) c).card = 1 := by
    rw [hfin1, Finset.card_univ, Fintype.card_coe, Finset.card_singleton]
  have hord : sLocalRhoPoleOrder (F := ℚ) (S := S) c = 2 := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces, harchCard, hfinCard]
  have hfinMult : sLocalFinitePoleMultiplicity (F := ℚ) (S := S) S c = 1 := by
    rw [sLocalFinitePoleMultiplicity_one S (Finset.Subset.refl S), Finset.card_singleton]
  have hon : normOneRestriction (sIdeleQuotientNorm ℚ S) c =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
        (1 : PontryaginDual (sIdeleQuotientNorm ℚ S).ker) := by
    ext g
    rfl
  have heig : sLocalPrincipalPartCoeff (F := ℚ) (S := S) c 1 ∈ sLocalEigendistributions c :=
    h ℚ S S hsat hpic (Finset.Subset.refl S) 1 c hon (by omega) 1 (by omega) (by omega)
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (σ t)
  have hmu : sIdeleQuotientNorm ℚ S (QuotientGroup.mk u) ≠ 1 := by
    rw [hu, hσ t]; exact ht
  have hlog : (Real.log (((sIdeleQuotientNorm ℚ S (QuotientGroup.mk u) : ℝ≥0) : ℝ)) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    intro hl
    have hpos : (0 : ℝ) < ((sIdeleQuotientNorm ℚ S (QuotientGroup.mk u) : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (Units.zero_lt _)
    rcases Real.log_eq_zero.mp hl with h0 | h1 | hm1
    · linarith
    · apply hmu
      exact Units.ext (NNReal.coe_injective h1)
    · linarith
  let χ : PontryaginDual (SIdeleQuotient ℚ S) := 1
  have hc0 : chart(ℚ, S, χ) 0 = c := by
    ext g
    change ((1 : Circle) : ℂ) * _ ^ (0 : ℂ) = (1 : ℂ)
    simp
  obtain ⟨f, hf⟩ := sLocalOrbitalPrincipalParts_eigendistributions_false_tensor S
    (fun w ↦ infiniteStandardGaussian w 1)
    (fun v ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v (chart(ℚ, S, χ) 0)))
  have htr := sLocalPrincipalPartCoeff_translate (F := ℚ) (S := S) c 1 (by omega) u f
  have heq := (mem_sLocalEigendistributions c _).mp heig u f
  dsimp only at htr
  rw [heq, hord] at htr
  have hsum :
      ∑ j ∈ Finset.range (2 - 1 + 1),
        sLocalPrincipalPartCoeff c (1 + j) f *
          (Real.log (((sIdeleQuotientNorm ℚ S (QuotientGroup.mk u) : ℝ≥0) : ℝ)) : ℂ) ^ j /
            (j.factorial : ℂ) =
      sLocalPrincipalPartCoeff c 1 f +
        sLocalPrincipalPartCoeff c 2 f *
          (Real.log (((sIdeleQuotientNorm ℚ S (QuotientGroup.mk u) : ℝ≥0) : ℝ)) : ℂ) := by
    rw [show 2 - 1 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  rw [hsum] at htr
  have hc1 : c (QuotientGroup.mk u) = 1 := rfl
  rw [hc1, one_mul, one_mul] at htr
  have hlead0 : sLocalPrincipalPartCoeff (F := ℚ) (S := S) c 2 f = 0 := by
    have hmul : sLocalPrincipalPartCoeff (F := ℚ) (S := S) c 2 f *
        (Real.log (((sIdeleQuotientNorm ℚ S (QuotientGroup.mk u) : ℝ≥0) : ℝ)) : ℂ) = 0 := by
      linear_combination -htr
    exact (mul_eq_zero.mp hmul).resolve_right hlog
  have hlead := sLocalPrincipalPartCoeff_leading_formula (F := ℚ) (S := S) c (by omega) f
  dsimp only at hlead
  rw [hord, harch1, hfin1] at hlead
  simp only [Finset.sdiff_self, Finset.prod_empty, mul_one] at hlead
  let d : QuasiCharacter (SIdeleQuotient ℚ S) :=
    dualQuasiCharacter (sIdeleQuotientNorm ℚ S) (isProperMap_sIdeleQuotientNorm ℚ S).continuous c
  have hmass_eq :
      (∏ v : S, (((finiteLocalMultiplicativeTamagawaMeasure ℚ v.val)
        ((v.val.adicCompletionIntegers ℚ).units : Set (v.val.adicCompletion ℚ)ˣ)).toReal : ℂ)) *
        sLocalEpsilonFactor (F := ℚ) (S := S) c *
        sLocalNormalizedEigendistribution d (sAdeleSchwartzFourier f) =
      (∏ v : S, (((finiteLocalMultiplicativeTamagawaMeasure ℚ v.val)
        ((v.val.adicCompletionIntegers ℚ).units : Set (v.val.adicCompletion ℚ)ˣ)).toReal : ℂ)) *
        sLocalNormalizedEigendistribution (F := ℚ) (S := S) c f := by
    have h1 := (existsUnique_sLocalNormalizedEigendistribution (F := ℚ) (S := S)
      d).exists.choose_spec (sAdeleSchwartzFourier f)
    have h2 := (existsUnique_sLocalNormalizedEigendistribution (F := ℚ) (S := S)
      c).exists.choose_spec f
    have hfe := sLocalNormalizedZFunction_functionalEquation (F := ℚ) (S := S) f c
    have h1' : (∏ v : S, (((finiteLocalMultiplicativeTamagawaMeasure ℚ v.val)
          ((v.val.adicCompletionIntegers ℚ).units : Set (v.val.adicCompletion ℚ)ˣ)).toReal : ℂ)) *
        sLocalNormalizedEigendistribution d (sAdeleSchwartzFourier f) =
        sLocalNormalizedZFunction (sAdeleSchwartzFourier f) d := by
      simpa only [Complex.ofReal_prod, sLocalNormalizedEigendistribution] using h1
    have h2' : (∏ v : S, (((finiteLocalMultiplicativeTamagawaMeasure ℚ v.val)
          ((v.val.adicCompletionIntegers ℚ).units : Set (v.val.adicCompletion ℚ)ˣ)).toReal : ℂ)) *
        sLocalNormalizedEigendistribution (F := ℚ) (S := S) c f =
        sLocalNormalizedZFunction f c := by
      simpa only [Complex.ofReal_prod, sLocalNormalizedEigendistribution] using h2
    calc
      _ = sLocalEpsilonFactor (F := ℚ) (S := S) c *
          ((∏ v : S, (((finiteLocalMultiplicativeTamagawaMeasure ℚ v.val)
            ((v.val.adicCompletionIntegers ℚ).units : Set (v.val.adicCompletion ℚ)ˣ)).toReal : ℂ)) *
            sLocalNormalizedEigendistribution d (sAdeleSchwartzFourier f)) := by ring
      _ = sLocalEpsilonFactor (F := ℚ) (S := S) c *
          sLocalNormalizedZFunction (sAdeleSchwartzFourier f) d := by rw [h1']
      _ = sLocalNormalizedZFunction f c := hfe.symm
      _ = _ := h2'.symm
  rw [hmass_eq] at hlead
  have hgauss : sLocalNormalizedEigendistribution (F := ℚ) (S := S) c f = 1 := by
    rw [← hc0]
    exact sLocalNormalizedEigendistribution_gaussian (F := ℚ) (S := S) χ 0 (fun _ ↦ 1)
      (fun _ ↦ by ext g; rfl) f hf
  rw [hgauss, mul_one] at hlead
  have hne : sLocalPrincipalPartCoeff (F := ℚ) (S := S) c 2 f ≠ 0 := by
    rw [hlead]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · rw [Finset.prod_ne_zero_iff]
      intro w _
      have hf1 := sLocalPrincipalPartCoeff_leading_formula_arch_factor (F := ℚ) (S := S) c w
      have hlt : meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
          (sLocalInfiniteRestriction w (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
            (isProperMap_sIdeleQuotientNorm ℚ S).continuous c z))) 0 < 0 := by
        have hw : w ∈ sLocalArchPolePlaces (F := ℚ) (S := S) c := by
          rw [harch1]; exact Finset.mem_univ w
        exact (Finset.mem_filter.mp hw).2
      exact sLocalOrbitalPrincipalParts_eigendistributions_false_residue_ne_zero
        hf1.1.meromorphicAt hf1.2 hlt
    · rw [Finset.prod_ne_zero_iff]
      intro v _
      have hf1 := sLocalPrincipalPartCoeff_leading_formula_fin_factor (F := ℚ) (S := S) c v
      have hlt : meromorphicOrderAt (fun z ↦ finiteLocalEulerFactor v.val
          (sLocalFiniteRestriction v (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
            (isProperMap_sIdeleQuotientNorm ℚ S).continuous c z))) 0 < 0 := by
        have hv : v ∈ sLocalFinitePolePlaces (F := ℚ) (S := S) c := by
          rw [hfin1]; exact Finset.mem_univ v
        exact (Finset.mem_filter.mp hv).2
      exact sLocalOrbitalPrincipalParts_eigendistributions_false_residue_ne_zero
        hf1.1.meromorphicAt hf1.2 hlt
    · rw [Finset.prod_ne_zero_iff]
      intro v _
      apply Complex.ofReal_ne_zero.mpr
      rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
      refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
      refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).trans' zero_lt_one
  exact hne hlead0

/-- Paper: Discussion after (7.3.1.11), p. 344.
At a common pole, the phases at two places over the same rational prime differ by a unique
integer multiple of the period for that prime. The integer norm of the rational place is p. -/
def Printed.sLocalOrbitalPhase_sub : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let Jₛ := SIdeleQuotient F S
    IsSaturatedPlaceSet S →
    ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (χ : PontryaginDual Jₛ) (v w : S),
      v.val ∈ sLocalPrimaryPlaces S p → w.val ∈ sLocalPrimaryPlaces S p →
      ∀ (uᵥ : (v.val.adicCompletion F)ˣ) (u_w : (w.val.adicCompletion F)ˣ),
        uniformizerNorm(F, S, v, uᵥ) → uniformizerNorm(F, S, w, u_w) →
        ∀ (tᵥ t_w : ℝ), phase(F, S, χ, v, uᵥ, tᵥ) → phase(F, S, χ, w, u_w, t_w) →
          ∀ c : QuasiCharacter Jₛ, (∃ s, c = chart(F, S, χ) s) →
            v ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            w ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            ∃! n : ℤ, tᵥ - t_w = (n : ℝ) * (2 * Real.pi / Real.log (p.asIdeal.absNorm : ℝ))

/-- The polynomial `X ^ 3 - 2` is irreducible over `ℚ`. -/
private theorem sLocalOrbitalPhase_sub_false_irred :
    Irreducible (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)) := by
  have hm : (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).Monic :=
    Polynomial.monic_X_pow_sub_C 2 (by norm_num)
  have hd : (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).natDegree = 3 :=
    Polynomial.natDegree_X_pow_sub_C (2 : ℚ)
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Polynomial.roots_eq_zero_iff_not_isRoot hm.ne_zero]
  intro q hq
  simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero] at hq
  have h1 : (q.num : ℚ) ^ 3 = 2 * (q.den : ℚ) ^ 3 := by
    have hq' := q.num_div_den
    rw [← hq', div_pow] at hq
    have hden : ((q.den : ℚ) ^ 3) ≠ 0 := pow_ne_zero 3 (Nat.cast_ne_zero.mpr q.den_nz)
    exact (div_eq_iff hden).mp hq
  have h2 : q.num ^ 3 = 2 * (q.den : ℤ) ^ 3 := by exact_mod_cast h1
  have h3 : q.num.natAbs ^ 3 = 2 * q.den ^ 3 := by
    have := congrArg Int.natAbs h2
    simpa [Int.natAbs_pow, Int.natAbs_mul] using this
  have hnum0 : q.num.natAbs ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at h3
    have : (0 : ℕ) < 2 * q.den ^ 3 := by positivity [Nat.pos_of_ne_zero q.den_nz]
    omega
  have hfac := congrArg (fun n : ℕ ↦ n.factorization 2) h3
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_mul (by norm_num) (pow_ne_zero 3 q.den_nz), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul] at hfac
  omega

/-- The field `ℚ(∛2)` has exactly two finite places above `5`, of residue norms `5` and `25`. -/
private theorem sLocalOrbitalPhase_sub_false_field :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F)
      (v w : HeightOneSpectrum (𝓞 F)),
      let p : HeightOneSpectrum (𝓞 ℚ) :=
        Rat.HeightOneSpectrum.primesEquiv.symm ⟨5, by decide⟩
      v.under (𝓞 ℚ) = p ∧ w.under (𝓞 ℚ) = p ∧
      v.asIdeal.absNorm = 5 ∧ w.asIdeal.absNorm = 25 ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u.under (𝓞 ℚ) = p → u = v ∨ u = w := by
  classical
  let P : Polynomial ℚ := Polynomial.X ^ 3 - Polynomial.C 2
  have hP_monic : P.Monic := Polynomial.monic_X_pow_sub_C 2 (by norm_num)
  have hP_deg : P.natDegree = 3 := Polynomial.natDegree_X_pow_sub_C (2 : ℚ)
  have : Fact (Irreducible P) := ⟨sLocalOrbitalPhase_sub_false_irred⟩
  let F := AdjoinRoot P
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  let pb := AdjoinRoot.powerBasis hP_monic.ne_zero
  have : FiniteDimensional ℚ F := pb.finite
  have : NumberField F := ⟨⟩
  have hfinrank : Module.finrank ℚ F = 3 := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, hP_deg]
  let α : F := AdjoinRoot.root P
  have hα3 : α ^ 3 = 2 := by
    have h0 : Polynomial.eval₂ (algebraMap ℚ F) α P = 0 := AdjoinRoot.eval₂_root P
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      sub_eq_zero] at h0
    simpa only [map_ofNat] using h0
  have hα_int : IsIntegral ℤ α :=
    ⟨Polynomial.X ^ 3 - Polynomial.C 2, Polynomial.monic_X_pow_sub_C 2 (by norm_num), by
      simp [hα3]⟩
  let α₀ : 𝓞 F := ⟨α, hα_int⟩
  have hα₀3 : α₀ ^ 3 = 2 := Subtype.ext hα3
  -- Compute traces of `1`, `α`, `α ^ 2` via the power basis `{1, α, α ^ 2}`.
  have hpb_dim : pb.dim = 3 := by rw [AdjoinRoot.powerBasis_dim, hP_deg]
  have htr1 : Algebra.trace ℚ F 1 = 3 := by
    refine (Algebra.trace_eq_matrix_trace pb.basis 1).trans ?_
    simp only [map_one, Matrix.trace_one, Fintype.card_fin, hpb_dim]
    norm_num
  have htrα : Algebra.trace ℚ F α = 0 := by
    refine (Algebra.trace_eq_matrix_trace pb.basis α).trans ?_
    simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hi : i.val < 3 := hpb_dim ▸ i.isLt
    have hmul : α * pb.basis i =
        if hlt : i.val < 2 then pb.basis ⟨i.val + 1, by omega⟩ else (2 : ℚ) • pb.basis ⟨0, by omega⟩ := by
      rw [PowerBasis.coe_basis]
      split_ifs with hlt
      · change α * α ^ i.val = α ^ (i.val + 1); ring
      · have hi2 : i.val = 2 := by omega
        change α * α ^ i.val = (2 : ℚ) • (α ^ 0)
        rw [hi2, show α * α ^ 2 = α ^ 3 by ring, hα3, pow_zero, Algebra.smul_def, mul_one]
        rfl
    rw [hmul]
    split_ifs with hlt
    · rw [pb.basis.repr_self, Finsupp.single_apply, ite_eq_right]
      intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
    · rw [map_smul, pb.basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right]
      · simp
      · intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
  have htrα2 : Algebra.trace ℚ F (α ^ 2) = 0 := by
    refine (Algebra.trace_eq_matrix_trace pb.basis (α ^ 2)).trans ?_
    simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hi : i.val < 3 := hpb_dim ▸ i.isLt
    have hmul : α ^ 2 * pb.basis i =
        if i.val = 0 then pb.basis ⟨2, by omega⟩
        else if i.val = 1 then (2 : ℚ) • pb.basis ⟨0, by omega⟩
        else (2 : ℚ) • pb.basis ⟨1, by omega⟩ := by
      rw [PowerBasis.coe_basis]
      split_ifs with h0' h1'
      · change α ^ 2 * α ^ i.val = α ^ 2; rw [h0']; ring
      · change α ^ 2 * α ^ i.val = (2 : ℚ) • (α ^ 0)
        rw [h1', show α ^ 2 * α ^ 1 = α ^ 3 by ring, hα3, pow_zero, Algebra.smul_def, mul_one]; rfl
      · have hi2 : i.val = 2 := by omega
        change α ^ 2 * α ^ i.val = (2 : ℚ) • (α ^ 1)
        rw [hi2, show α ^ 2 * α ^ 2 = α ^ 3 * α by ring, hα3, pow_one, Algebra.smul_def]; rfl
    rw [hmul]
    split_ifs with h0' h1'
    · rw [pb.basis.repr_self, Finsupp.single_apply, ite_eq_right]
      intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
    · rw [map_smul, pb.basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right]
      · simp
      · intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
    · rw [map_smul, pb.basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right]
      · simp
      · intro h; have h' := congrArg Fin.val h; dsimp only at h'; omega
  have htr_int (x : 𝓞 F) : ∃ z : ℤ, Algebra.trace ℚ F (x : F) = z :=
    ⟨Algebra.trace ℤ (𝓞 F) x,
      Algebra.trace_localization (R := ℤ) (Rₘ := ℚ) (S := 𝓞 F) (Sₘ := F)
        (nonZeroDivisors ℤ) x⟩
  -- Show `(5, α₀ - 3)` and `(5, α₀ ^ 2 + 3 * α₀ + 4)` are proper ideals of `𝓞 F`.
  have hI1_ne : Ideal.span ({5, α₀ - 3} : Set (𝓞 F)) ≠ ⊤ := by
    intro htop
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair] at htop
    obtain ⟨a, b, hab⟩ := htop
    have hid : (α₀ - 3) * (α₀ ^ 2 + 3 * α₀ + 9) = 5 * (-5) := by
      calc (α₀ - 3) * (α₀ ^ 2 + 3 * α₀ + 9) = α₀ ^ 3 - 27 := by ring
        _ = 2 - 27 := by rw [hα₀3]
        _ = 5 * (-5) := by ring
    let q : 𝓞 F := a * (α₀ ^ 2 + 3 * α₀ + 9) - 5 * b
    have hdvd : (5 : 𝓞 F) * q = α₀ ^ 2 + 3 * α₀ + 9 := by
      calc (5 : 𝓞 F) * q
          = a * 5 * (α₀ ^ 2 + 3 * α₀ + 9) + b * (5 * (-5)) := by ring
        _ = a * 5 * (α₀ ^ 2 + 3 * α₀ + 9) + b * ((α₀ - 3) * (α₀ ^ 2 + 3 * α₀ + 9)) := by rw [← hid]
        _ = (a * 5 + b * (α₀ - 3)) * (α₀ ^ 2 + 3 * α₀ + 9) := by ring
        _ = 1 * (α₀ ^ 2 + 3 * α₀ + 9) := by rw [hab]
        _ = α₀ ^ 2 + 3 * α₀ + 9 := one_mul _
    obtain ⟨z, hz⟩ := htr_int q
    have hcoe : (5 : F) * (q : F) = α ^ 2 + 3 * α + 9 := by
      have := congrArg (algebraMap (𝓞 F) F) hdvd
      simp only [map_mul, map_add, map_pow, map_ofNat] at this
      exact this
    have htr := congrArg (Algebra.trace ℚ F) hcoe
    have htrL : Algebra.trace ℚ F ((5 : F) * (q : F)) = 5 * (z : ℚ) := by
      rw [show (5 : F) * (q : F) = (5 : ℚ) • (q : F) by rw [Algebra.smul_def]; rfl,
        map_smul, hz, smul_eq_mul]
    have htrR : Algebra.trace ℚ F (α ^ 2 + 3 * α + 9) = 27 := by
      rw [map_add, map_add, htrα2, show (3 : F) * α = (3 : ℚ) • α by rw [Algebra.smul_def]; rfl,
        map_smul, htrα, show (9 : F) = (9 : ℚ) • (1 : F) by rw [Algebra.smul_def, mul_one]; rfl,
        map_smul, htr1]
      norm_num
    have h5z : (5 : ℚ) * z = 27 := by rw [← htrL, htr, htrR]
    have h5z' : (5 : ℤ) * z = 27 := by exact_mod_cast h5z
    omega
  have hI2_ne : Ideal.span ({5, α₀ ^ 2 + 3 * α₀ + 4} : Set (𝓞 F)) ≠ ⊤ := by
    intro htop
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair] at htop
    obtain ⟨a, b, hab⟩ := htop
    have hid : (α₀ - 3) * (α₀ ^ 2 + 3 * α₀ + 4) = 5 * (-(α₀ + 2)) := by
      calc (α₀ - 3) * (α₀ ^ 2 + 3 * α₀ + 4) = α₀ ^ 3 - 5 * α₀ - 12 := by ring
        _ = 2 - 5 * α₀ - 12 := by rw [hα₀3]
        _ = 5 * (-(α₀ + 2)) := by ring
    let q : 𝓞 F := a * (α₀ - 3) - b * (α₀ + 2)
    have hdvd : (5 : 𝓞 F) * q = α₀ - 3 := by
      calc (5 : 𝓞 F) * q
          = a * 5 * (α₀ - 3) + b * (5 * (-(α₀ + 2))) := by ring
        _ = a * 5 * (α₀ - 3) + b * ((α₀ - 3) * (α₀ ^ 2 + 3 * α₀ + 4)) := by rw [← hid]
        _ = (a * 5 + b * (α₀ ^ 2 + 3 * α₀ + 4)) * (α₀ - 3) := by ring
        _ = 1 * (α₀ - 3) := by rw [hab]
        _ = α₀ - 3 := one_mul _
    obtain ⟨z, hz⟩ := htr_int q
    have hcoe : (5 : F) * (q : F) = α - 3 := by
      have := congrArg (algebraMap (𝓞 F) F) hdvd
      simp only [map_mul, map_sub, map_ofNat] at this
      exact this
    have htr := congrArg (Algebra.trace ℚ F) hcoe
    have htrL : Algebra.trace ℚ F ((5 : F) * (q : F)) = 5 * (z : ℚ) := by
      rw [show (5 : F) * (q : F) = (5 : ℚ) • (q : F) by rw [Algebra.smul_def]; rfl,
        map_smul, hz, smul_eq_mul]
    have htrR : Algebra.trace ℚ F (α - 3) = -9 := by
      rw [map_sub, htrα, show (3 : F) = (3 : ℚ) • (1 : F) by rw [Algebra.smul_def, mul_one]; rfl,
        map_smul, htr1]
      norm_num
    have h5z : (5 : ℚ) * z = -9 := by rw [← htrL, htr, htrR]
    have h5z' : (5 : ℤ) * z = -9 := by exact_mod_cast h5z
    omega
  obtain ⟨V, hVmax, hVle⟩ := Ideal.exists_le_maximal _ hI1_ne
  obtain ⟨W, hWmax, hWle⟩ := Ideal.exists_le_maximal _ hI2_ne
  have h5V : (5 : 𝓞 F) ∈ V := hVle (Ideal.subset_span (by simp))
  have hαV : α₀ - 3 ∈ V := hVle (Ideal.subset_span (by simp))
  have h5W : (5 : 𝓞 F) ∈ W := hWle (Ideal.subset_span (by simp))
  have hαW : α₀ ^ 2 + 3 * α₀ + 4 ∈ W := hWle (Ideal.subset_span (by simp))
  have hVW : V ≠ W := by
    intro heq
    subst heq
    have h22 : (22 : 𝓞 F) ∈ V := by
      have : (22 : 𝓞 F) = (α₀ ^ 2 + 3 * α₀ + 4) - (α₀ - 3) * (α₀ + 6) := by ring
      rw [this]
      exact V.sub_mem hαW (V.mul_mem_right _ hαV)
    have h1 : (1 : 𝓞 F) ∈ V := by
      have : (1 : 𝓞 F) = 9 * 5 - 2 * 22 := by norm_num
      rw [this]
      exact V.sub_mem (V.mul_mem_left 9 h5V) (V.mul_mem_left 2 h22)
    exact hVmax.ne_top (Ideal.eq_top_of_isUnit_mem V h1 isUnit_one)
  let p₅ : Ideal ℤ := Ideal.span {(5 : ℤ)}
  have hp₅_prime : Prime (5 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  have : p₅.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp₅_prime.irreducible
  have hLiesOver_of_mem (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (h5Q : (5 : 𝓞 F) ∈ Q) :
      Q.LiesOver p₅ := by
    constructor
    have hle : p₅ ≤ Ideal.comap (algebraMap ℤ (𝓞 F)) Q := by
      rw [Ideal.span_singleton_le_iff_mem]
      simpa using h5Q
    have hne : Ideal.comap (algebraMap ℤ (𝓞 F)) Q ≠ ⊤ := by
      intro htop
      have : (1 : 𝓞 F) ∈ Q := by
        have h1 : (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 F)) Q := htop ▸ Submodule.mem_top
        simpa using h1
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q this isUnit_one)
    exact Ideal.IsMaximal.eq_of_le inferInstance hne hle
  have : V.IsPrime := hVmax.isPrime
  have : W.IsPrime := hWmax.isPrime
  have : V.LiesOver p₅ := hLiesOver_of_mem V hVmax.isPrime h5V
  have : W.LiesOver p₅ := hLiesOver_of_mem W hWmax.isPrime h5W
  have hVne : V ≠ ⊥ := fun h0 ↦ by
    have : (5 : 𝓞 F) = 0 := by simp [h0] at h5V
    exact absurd (congrArg (fun x : 𝓞 F ↦ (x : F)) this) (by norm_num)
  have hWne : W ≠ ⊥ := fun h0 ↦ by
    have : (5 : 𝓞 F) = 0 := by simp [h0] at h5W
    exact absurd (congrArg (fun x : 𝓞 F ↦ (x : F)) this) (by norm_num)
  -- Show `2 ≤ W.inertiaDeg ℤ`.
  have hWf : 2 ≤ W.inertiaDeg ℤ := by
    have hpos : 0 < W.inertiaDeg ℤ := Ideal.inertiaDeg_pos (R := ℤ) (S := 𝓞 F) W
    by_contra hlt
    have h1 : W.inertiaDeg ℤ = 1 := by omega
    have hcard : Nat.card (𝓞 F ⧸ W) = 5 := by
      change Submodule.cardQuot W = 5
      rw [← Ideal.absNorm_apply, ← Ideal.natAbs_pow_inertiaDeg (5 : ℤ) W, h1]
      norm_num
    have hfin : Finite (𝓞 F ⧸ W) := Nat.finite_of_card_ne_zero (by omega)
    let : Fintype (𝓞 F ⧸ W) := Fintype.ofFinite _
    have hcard' : Fintype.card (𝓞 F ⧸ W) = Fintype.card (Fin 5) := by
      rw [← Nat.card_eq_fintype_card, hcard, Fintype.card_fin]
    let ι : Fin 5 → 𝓞 F ⧸ W := fun k ↦ (k.val : 𝓞 F ⧸ W)
    have hinj : Function.Injective ι := by
      intro a b hab
      have hsub : ((a.val : ℤ) - (b.val : ℤ) : 𝓞 F) ∈ W := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [ι, sub_eq_zero] using hab
      have hmem : (a.val : ℤ) - (b.val : ℤ) ∈ p₅ := by
        rw [Ideal.LiesOver.over (p := p₅) (P := W)]
        simpa only [Ideal.mem_comap, map_sub, map_intCast, eq_intCast] using hsub
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)
    have hsurj : Function.Surjective ι :=
      (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard'.symm)).mp hinj
    obtain ⟨k, hk⟩ := hsurj (Ideal.Quotient.mk W α₀)
    have hsub : α₀ - (k.val : 𝓞 F) ∈ W := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      exact hk.symm
    have hquad : (((k.val : ℤ) ^ 2 + 3 * (k.val : ℤ) + 4 : ℤ) : 𝓞 F) ∈ W := by
      have : (((k.val : ℤ) ^ 2 + 3 * (k.val : ℤ) + 4 : ℤ) : 𝓞 F) =
          (α₀ ^ 2 + 3 * α₀ + 4) - (α₀ - (k.val : 𝓞 F)) * (α₀ + (k.val : 𝓞 F) + 3) := by
        push_cast; ring
      rw [this]
      exact W.sub_mem hαW (W.mul_mem_right _ hsub)
    have hmem : (k.val : ℤ) ^ 2 + 3 * (k.val : ℤ) + 4 ∈ p₅ := by
      rw [Ideal.LiesOver.over (p := p₅) (P := W)]
      exact hquad
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    fin_cases k <;> simp at hc <;> omega
  -- Apply `∑ q : p₅.primesOver (𝓞 F), e(q) * f(q) = 3`.
  have hsum : ∑ q : p₅.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 3 := by
    have h1 := Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (S := 𝓞 F) (p := p₅)
    have h2 : Module.finrank ℤ (𝓞 F) = Module.finrank ℚ F := NumberField.RingOfIntegers.rank F
    omega
  let qV : p₅.primesOver (𝓞 F) := ⟨V, ⟨hVmax.isPrime, inferInstance⟩⟩
  let qW : p₅.primesOver (𝓞 F) := ⟨W, ⟨hWmax.isPrime, inferInstance⟩⟩
  have hqVW : qV ≠ qW := fun h ↦ hVW (congrArg Subtype.val h)
  have hterm_pos (q : p₅.primesOver (𝓞 F)) : 1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    have := q.2.1
    have := q.2.2
    have he : 1 ≤ q.1.ramificationIdx ℤ := Ideal.ramificationIdx_pos (R := ℤ) (S := 𝓞 F) q.1
    have hf : 1 ≤ q.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos (R := ℤ) (S := 𝓞 F) q.1
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  have hsplit : V.ramificationIdx ℤ * V.inertiaDeg ℤ +
      W.ramificationIdx ℤ * W.inertiaDeg ℤ +
      ∑ q ∈ (Finset.univ.erase qV).erase qW, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 3 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ qV),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hqVW.symm, Finset.mem_univ qW⟩)]
    ring
  have hVe : 1 ≤ V.ramificationIdx ℤ := Ideal.ramificationIdx_pos (R := ℤ) (S := 𝓞 F) V
  have hVf_pos : 1 ≤ V.inertiaDeg ℤ := Ideal.inertiaDeg_pos (R := ℤ) (S := 𝓞 F) V
  have hWe : 1 ≤ W.ramificationIdx ℤ := Ideal.ramificationIdx_pos (R := ℤ) (S := 𝓞 F) W
  have hVprod : V.inertiaDeg ℤ ≤ V.ramificationIdx ℤ * V.inertiaDeg ℤ :=
    Nat.le_mul_of_pos_left _ hVe
  have hWprod : W.inertiaDeg ℤ ≤ W.ramificationIdx ℤ * W.inertiaDeg ℤ :=
    Nat.le_mul_of_pos_left _ hWe
  have hVf1 : V.inertiaDeg ℤ = 1 := by omega
  have hWf2 : W.inertiaDeg ℤ = 2 := by omega
  have hrest0 : ∑ q ∈ (Finset.univ.erase qV).erase qW,
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 0 := by omega
  have honly (q : p₅.primesOver (𝓞 F)) : q = qV ∨ q = qW := by
    by_contra hne
    push Not at hne
    have hmem : q ∈ (Finset.univ.erase qV).erase qW :=
      Finset.mem_erase.mpr ⟨hne.2, Finset.mem_erase.mpr ⟨hne.1, Finset.mem_univ q⟩⟩
    have hle := Finset.single_le_sum (f := fun x : p₅.primesOver (𝓞 F) ↦
      x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ) (fun _ _ ↦ Nat.zero_le _) hmem
    have hpos := hterm_pos q
    omega
  -- Package `v` and `w` as `HeightOneSpectrum (𝓞 F)`.
  let v : HeightOneSpectrum (𝓞 F) := ⟨V, hVmax.isPrime, hVne⟩
  let w : HeightOneSpectrum (𝓞 F) := ⟨W, hWmax.isPrime, hWne⟩
  let p : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨5, by decide⟩
  have hgen : Rat.HeightOneSpectrum.natGenerator p = 5 :=
    congrArg Subtype.val (Equiv.apply_symm_apply Rat.HeightOneSpectrum.primesEquiv ⟨5, by decide⟩)
  have hp_span : p.asIdeal = Ideal.span {(5 : 𝓞 ℚ)} := by
    let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
    have h1 : Ideal.span {(5 : ℤ)} = p.asIdeal.map e := by
      simpa [hgen, e] using Rat.HeightOneSpectrum.span_natGenerator p
    have h2 : p.asIdeal = Ideal.comap e (Ideal.span {(5 : ℤ)}) := by
      rw [h1, p.asIdeal.comap_map_of_bijective e e.bijective]
    ext x
    rw [h2, Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨e.symm a, e.injective ?_⟩
      simpa [map_mul, map_ofNat] using ha
    · rintro ⟨a, ha⟩
      exact ⟨e a, by simp [ha, map_mul, map_ofNat]⟩
  have h5p : (5 : 𝓞 ℚ) ∈ p.asIdeal := by
    rw [hp_span]; exact Ideal.subset_span rfl
  have hunder_iff (u : HeightOneSpectrum (𝓞 F)) : u.under (𝓞 ℚ) = p ↔ (5 : 𝓞 F) ∈ u.asIdeal := by
    constructor
    · intro hu
      have : (5 : 𝓞 ℚ) ∈ (u.under (𝓞 ℚ)).asIdeal := hu ▸ h5p
      simpa only [HeightOneSpectrum.under, Ideal.mem_comap, map_ofNat] using this
    · intro h5u
      have hle : p.asIdeal ≤ (u.under (𝓞 ℚ)).asIdeal := by
        rw [hp_span, Ideal.span_singleton_le_iff_mem]
        simpa only [HeightOneSpectrum.under, Ideal.mem_comap, map_ofNat] using h5u
      exact HeightOneSpectrum.ext ((p.isMaximal.eq_of_le (u.under (𝓞 ℚ)).isPrime.ne_top hle).symm)
  refine ⟨F, inferInstance, inferInstance, v, w, (hunder_iff v).mpr h5V, (hunder_iff w).mpr h5W,
    ?_, ?_, ?_⟩
  · rw [← Ideal.natAbs_pow_inertiaDeg (5 : ℤ) V, hVf1]; norm_num
  · rw [← Ideal.natAbs_pow_inertiaDeg (5 : ℤ) W, hWf2]; norm_num
  · intro u hu
    have h5u : (5 : 𝓞 F) ∈ u.asIdeal := (hunder_iff u).mp hu
    have : u.asIdeal.LiesOver p₅ := hLiesOver_of_mem u.asIdeal u.isPrime h5u
    rcases honly ⟨u.asIdeal, ⟨u.isPrime, inferInstance⟩⟩ with h1 | h2
    · left; exact HeightOneSpectrum.ext (congrArg Subtype.val h1)
    · right; exact HeightOneSpectrum.ext (congrArg Subtype.val h2)

/-- Paper: Discussion after (7.3.1.11), p. 344.
Take F = ℚ(∛2), p = 5, and S consisting of the places over 5 together with the archimedean
places. Modulo 5, X³ - 2 factors as (X - 3)(X² + 3X + 4), with irreducible quadratic
and discriminant of X³ - 2 prime to 5. The local residue sizes are 5 and 25.
With T = 2π/log 5 and χ = |·|^(3iT/4), take the common pole c = 1.
The local phases are 3T/4 and T/4, so their difference is T/2. -/
theorem Printed.sLocalOrbitalPhase_sub_false : ¬ Printed.sLocalOrbitalPhase_sub := by
  classical
  intro h
  obtain ⟨F, _, _, v, w, hv_under, hw_under, hv_norm, hw_norm, honly⟩ :=
    sLocalOrbitalPhase_sub_false_field
  let p : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨5, by decide⟩
  let S : Finset (HeightOneSpectrum (𝓞 F)) := {v, w}
  have hsat : IsSaturatedPlaceSet S := by
    intro a b ha hb
    have ha_under : a.under (𝓞 ℚ) = p := by
      rcases Finset.mem_insert.mp ha with rfl | hmem
      · exact hv_under
      · rw [Finset.mem_singleton.mp hmem]; exact hw_under
    rcases honly b (hb.trans ha_under) with rfl | rfl <;> simp [S]
  let v' : S := ⟨v, by simp [S]⟩
  let w' : S := ⟨w, by simp [S]⟩
  have hv_mem : v'.val ∈ sLocalPrimaryPlaces S p :=
    (mem_sLocalPrimaryPlaces p v).mpr ⟨by simp [S], hv_under⟩
  have hw_mem : w'.val ∈ sLocalPrimaryPlaces S p :=
    (mem_sLocalPrimaryPlaces p w).mpr ⟨by simp [S], hw_under⟩
  have hp_norm : p.asIdeal.absNorm = 5 := by
    have hgen : Rat.HeightOneSpectrum.natGenerator p = 5 :=
      congrArg Subtype.val (Equiv.apply_symm_apply Rat.HeightOneSpectrum.primesEquiv ⟨5, by decide⟩)
    have hp_span : p.asIdeal = Ideal.span {(5 : 𝓞 ℚ)} := by
      let e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
      have h1 : Ideal.span {(5 : ℤ)} = p.asIdeal.map e := by
        simpa [hgen, e] using Rat.HeightOneSpectrum.span_natGenerator p
      have h2 : p.asIdeal = Ideal.comap e (Ideal.span {(5 : ℤ)}) := by
        rw [h1, p.asIdeal.comap_map_of_bijective e e.bijective]
      ext x
      rw [h2, Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨e.symm a, e.injective ?_⟩
        simpa [map_mul, map_ofNat] using ha
      · rintro ⟨a, ha⟩
        exact ⟨e a, by simp [ha, map_mul, map_ofNat]⟩
    rw [hp_span, Ideal.absNorm_span_singleton]
    have : Algebra.norm ℤ (5 : 𝓞 ℚ) = 5 := by
      rw [show (5 : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) 5 from rfl, Algebra.norm_algebraMap,
        NumberField.RingOfIntegers.rank ℚ, Module.finrank_self, pow_one]
    rw [this]; rfl
  let T : ℝ := 2 * Real.pi / Real.log 5
  have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hTpos : 0 < T := div_pos (mul_pos (by norm_num) Real.pi_pos) hlog5
  let χ : PontryaginDual (SIdeleQuotient F S) :=
    { toFun := fun g ↦ Circle.exp ((3 * T / 4) * Real.log (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ)))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        simp only [map_mul, Units.val_mul, NNReal.coe_mul,
          Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
            (NNReal.coe_pos.mpr (Units.zero_lt _)).ne', mul_add, Circle.exp_add]
      continuous_toFun := by
        refine Circle.exp.continuous.comp (continuous_const.mul (Continuous.log ?_ ?_))
        · exact NNReal.continuous_coe.comp (Units.continuous_val.comp
            (isProperMap_sIdeleQuotientNorm F S).continuous)
        · intro g; exact (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' }
  have huv_ex := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  have huw_ex := (Valued.v : Valuation (w.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let uᵥ : (v.adicCompletion F)ˣ := Units.mk0 huv_ex.choose huv_ex.choose_spec.ne_zero
  let u_w : (w.adicCompletion F)ˣ := Units.mk0 huw_ex.choose huw_ex.choose_spec.ne_zero
  have huv_norm : uniformizerNorm(F, S, v', uᵥ) :=
    norm_uniformizer_adicCompletion v _ huv_ex.choose_spec
  have huw_norm : uniformizerNorm(F, S, w', u_w) :=
    norm_uniformizer_adicCompletion w _ huw_ex.choose_spec
  have hchart_val (q : S) (u : (q.val.adicCompletion F)ˣ) (t : ℝ) :
      sLocalFiniteRestriction q (chart(F, S, χ) (-(t : ℂ) * Complex.I)) u =
        Complex.exp ((((3 * T / 4 - t) * Real.log ‖(u : q.val.adicCompletion F)‖ : ℝ) : ℂ) *
          Complex.I) := by
    let g : SIdeleQuotient F S :=
      QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
        ((i : S) → i.val.adicCompletion F)).symm (1, ContinuousMulEquiv.piUnits.symm
          (@Pi.mulSingle _ _ _ (Classical.decEq _) q u)))
    have hn := sLocalFiniteRestriction_norm q u
    change ((1 : PontryaginDual (SIdeleQuotient F S)) g : ℂ) *
      (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) =
      (‖(u : q.val.adicCompletion F)‖ : ℂ) at hn
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] at hn
    have hnorm_eq : ((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) =
        ‖(u : q.val.adicCompletion F)‖ := Complex.ofReal_injective hn
    have hpos : (0 : ℝ) < ‖(u : q.val.adicCompletion F)‖ := norm_pos_iff.mpr u.ne_zero
    change ((Circle.exp ((3 * T / 4) * Real.log ((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ)) : Circle) : ℂ) *
      (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) = _
    rw [hnorm_eq, Circle.coe_exp, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  let tv : ℝ := 3 * T / 4
  let tw : ℝ := T / 4
  have hphase_v : phase(F, S, χ, v', uᵥ, tv) := by
    refine ⟨?_, ?_⟩
    · have hper : period(S, v') = T := by simp [v', hv_norm, T]
      rw [hper]
      exact ⟨by dsimp only [tv]; linarith, by dsimp only [tv]; linarith⟩
    · rw [hchart_val v' uᵥ tv]
      simp [tv]
  have hphase_w : phase(F, S, χ, w', u_w, tw) := by
    refine ⟨?_, ?_⟩
    · have hper : period(S, w') = T / 2 := by
        have h25 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
          rw [show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
        simp only [w', hw_norm, Nat.cast_ofNat, h25, T]
        ring
      rw [hper]
      exact ⟨by dsimp only [tw]; linarith, by dsimp only [tw]; linarith⟩
    · rw [hchart_val w' u_w tw, huw_norm, hw_norm]
      have hlog : Real.log (((25 : ℕ) : ℝ)⁻¹) = -(2 * Real.log 5) := by
        rw [Nat.cast_ofNat, Real.log_inv, show (25 : ℝ) = 5 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [hlog]
      have harg : ((3 * T / 4 - tw) * -(2 * Real.log 5) : ℝ) = -(2 * Real.pi) := by
        dsimp only [tw, T]
        field_simp [hlog5.ne']
        ring
      rw [harg]
      push_cast
      rw [show (-(2 * (Real.pi : ℂ))) * Complex.I = -(2 * Real.pi * Complex.I) by ring,
        Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hc1 : (1 : QuasiCharacter (SIdeleQuotient F S)) =
      chart(F, S, χ) (-((3 * T / 4 : ℝ) : ℂ) * Complex.I) := by
    ext g
    have hpos : (0 : ℝ) < ((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (Units.zero_lt _)
    change (1 : ℂ) = ((Circle.exp ((3 * T / 4) * Real.log _) : Circle) : ℂ) *
      ((_ : ℝ) : ℂ) ^ (-((3 * T / 4 : ℝ) : ℂ) * Complex.I)
    rw [Circle.coe_exp, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, ← Complex.exp_add]
    have hzero : (((3 * T / 4) * Real.log (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ)) : ℝ) : ℂ) *
        Complex.I + ((Real.log (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ)) : ℝ) : ℂ) *
        (-((3 * T / 4 : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast; ring
    rw [hzero, Complex.exp_zero]
  have hv_pole : v' ∈ sLocalFinitePolePlaces (F := F) (S := S) 1 := by
    rw [(sLocalPolePlaces_one (F := F) (S := S)).2]; exact Finset.mem_univ v'
  have hw_pole : w' ∈ sLocalFinitePolePlaces (F := F) (S := S) 1 := by
    rw [(sLocalPolePlaces_one (F := F) (S := S)).2]; exact Finset.mem_univ w'
  obtain ⟨n, hn, -⟩ := h F S hsat p χ v' w' hv_mem hw_mem uᵥ u_w huv_norm huw_norm
    tv tw hphase_v hphase_w 1 ⟨-((3 * T / 4 : ℝ) : ℂ) * Complex.I, hc1⟩
    hv_pole hw_pole
  rw [hp_norm] at hn
  change tv - tw = (n : ℝ) * T at hn
  have h2n : (2 : ℝ) * (n : ℝ) = 1 := by
    have h1 : (n : ℝ) * T = (1 / 2 : ℝ) * T := by dsimp only [tv, tw] at hn; linarith
    have h2 : (n : ℝ) = 1 / 2 := mul_right_cancel₀ hTpos.ne' h1
    linarith
  have h2n' : (2 : ℤ) * n = 1 := by exact_mod_cast h2n
  omega

/-- At the trivial quasi-character every restricted finite Tate factor has a pole at `0`. -/
private theorem sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_order_neg
    {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))} (v : S) :
    meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous (1 : QuasiCharacter (SIdeleQuotient F S))
        z))) 0 < 0 := by
  have h1 : (1 : QuasiCharacter (SIdeleQuotient F S)) =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
        (1 : PontryaginDual (SIdeleQuotient F S)) := by
    ext x
    change (1 : ℂ) = (((1 : PontryaginDual (SIdeleQuotient F S)) x : Circle) : ℂ)
    rw [PontryaginDual.one_apply, Circle.coe_one]
  have hv : v ∈ sLocalFinitePolePlaces (1 : QuasiCharacter (SIdeleQuotient F S)) := by
    rw [(sLocalPolePlaces_one (F := F) (S := S)).2]
    exact Finset.mem_univ v
  have hv' := (Finset.mem_filter.mp hv).2
  rw [h1] at hv' ⊢
  exact (sLocalRhoPoleOrder_eq_card_polePlaces_finite _ v 0).mp hv'

/-- Over `ℚ` the place below a finite place is the place itself. -/
private theorem sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_under
    (w : HeightOneSpectrum (𝓞 ℚ)) : w.under (𝓞 ℚ) = w := by
  ext x
  change x ∈ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) w.asIdeal ↔ x ∈ w.asIdeal
  rw [Algebra.algebraMap_self, Ideal.comap_id]

/-- The `S`-integers of `ℚ` have trivial Picard group. -/
private theorem sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_pic
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) : Subsingleton (CommRing.Pic (S.integer ℚ)) := by
  have hpid : IsPrincipalIdealRing (𝓞 ℚ) :=
    NumberField.classNumber_eq_one_iff.mp Rat.classNumber_eq
  have : Subsingleton (ClassGroup (𝓞 ℚ)) := inferInstance
  have : Fact (IsMulTorsion (ClassGroup (𝓞 ℚ))) :=
    ⟨fun x ↦ by rw [Subsingleton.elim x 1]; exact IsOfFinOrder.one⟩
  have : UniqueFactorizationMonoid (S.integer ℚ) :=
    UniqueFactorizationMonoid.of_isLocalization (Localization.submonoid S) _
  let : GCDMonoid (S.integer ℚ) := UniqueFactorizationMonoid.toGCDMonoid _
  infer_instance

open Classical in
/-- Paper: Definition 7.3.1.4, equations (7.3.1.6)–(7.3.1.7), p. 343.
As printed: on the primary pole locus, the natural-number count of contributing
places equals the sum of the signed meromorphic orders of the restricted local
Tate factors. See `sLocalPrimaryPoleMultiplicity` and ERRATA F119. -/
def Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 ℚ)),
    IsSaturatedPlaceSet S → (sLocalPrimaryPlaces S p).Nonempty →
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ c : QuasiCharacter (SIdeleQuotient F S),
      0 < sLocalPrimaryPoleMultiplicity p c →
      let twist := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous c
      ((sLocalPrimaryPoleMultiplicity p c : ℤ) : WithTop ℤ) =
        ∑ v ∈ S.attach.filter (fun v ↦ v.val ∈ sLocalPrimaryPlaces S p),
          meromorphicOrderAt
            (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (twist z))) 0

open Classical in
/-- Paper: Definition 7.3.1.4, equations (7.3.1.6)–(7.3.1.7), p. 343.
Take F = ℚ, S with just the finite place over 2, p = 2, and c = 1.
The local numerator has a simple pole and the reflected denominator is
regular and nonzero at c, giving signed order −1. The primary count is 1. -/
theorem Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders_false :
    ¬ Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders := by
  intro h
  let p : HeightOneSpectrum (𝓞 ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  have hunder := sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_under
  have hP : sLocalPrimaryPlaces ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) p = {p} := by
    ext w
    rw [mem_sLocalPrimaryPlaces]
    exact ⟨And.left, fun hw ↦ ⟨hw, (hunder w).trans (Finset.mem_singleton.mp hw)⟩⟩
  have hsat : IsSaturatedPlaceSet ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) := by
    intro v w hv hw
    have hwv : w = v := (hunder w).symm.trans (hw.trans (hunder v))
    rwa [hwv]
  have hne : (sLocalPrimaryPlaces ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) p).Nonempty := by
    rw [hP]
    exact Finset.singleton_nonempty p
  have hmult : sLocalPrimaryPoleMultiplicity (S := {p}) p 1 = 1 := by
    rw [sLocalPrimaryPoleMultiplicity_one, hP, Finset.card_singleton]
  have H := h ℚ {p} p hsat hne
    (sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_pic _) 1 (by rw [hmult]; exact one_pos)
  dsimp only at H
  rw [hmult] at H
  have hle : (∑ v ∈ ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))).attach.filter
      (fun v ↦ v.val ∈ sLocalPrimaryPlaces {p} p),
        meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v
          (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ {p})
            (isProperMap_sIdeleQuotientNorm ℚ {p}).continuous 1 z))) 0) ≤ 0 :=
    Finset.sum_nonpos fun v _ ↦
      (sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_order_neg v).le
  rw [← H] at hle
  have h0 : ((((1 : ℕ) : ℤ)) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := hle
  exact absurd (WithTop.coe_le_coe.mp h0) (by norm_num)

end RiemannMasullo
