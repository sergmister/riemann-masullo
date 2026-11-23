module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5a
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
public import Mathlib.Topology.Algebra.RestrictedProduct.Units
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Units
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Appendix A.5.2: statements that are false as printed -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal Pointwise

section QuotientGroups

local instance printedSec5aQuotientMeasurableSpace {G : Type} [CommGroup G]
    [TopologicalSpace G] (H : Subgroup G) : MeasurableSpace (G ⧸ H) := borel _

/-- Paper: Proposition A.5.2.6, end of proof, p. 574.
As printed: for a symmetric, relatively compact Borel transversal `E` containing the identity
in its interior, a decreasing Borel family on the quotient and its specified auxiliary sets
form a D″-sequence exactly when their preimages intersected with `E` do. The ambient group is
second countable, the subgroup is closed and discrete, and counting measure on the subgroup
determines the quotient Haar measure for the given ambient measure. The D and D′ assertions
are `isDSequence_quotient_iff` and `isDPrimeSequence_quotient_iff`. See ERRATA F218. -/
def Printed.isDDoublePrimeSequence_quotient_iff : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [DiscreteTopology H],
    IsClosed (H : Set G) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
      (ν : Measure (G ⧸ H)),
    IsWeilQuotientMeasure H μ μH ν → μH {1} = 1 →
    ∀ (E : Set G), MeasurableSet E → IsCompact (closure E) → 1 ∈ interior E → E⁻¹ = E →
    Bijective (fun x : E ↦ QuotientGroup.mk' H (x : G)) →
    ∀ (U V : ℕ → Set (G ⧸ H)), (∀ k, MeasurableSet (U k)) → Antitone U →
    let lift := fun (W : ℕ → Set (G ⧸ H)) k ↦ (QuotientGroup.mk' H) ⁻¹' W k ∩ E
    IsDDoublePrimeSequence ν U V ↔ IsDDoublePrimeSequence μ (lift U) (lift V)

/-- Paper: Proposition A.5.2.6, end of proof, p. 574.
Use the discrete additive group `ℤ`, the subgroup `3ℤ`, counting measures, and the symmetric
transversal `E = {-1, 0, 1}`. In `ℤ/3ℤ` set `U 0 = V 0 = univ` and `U k = V k = {0}`
for `k ≥ 1`. These satisfy the D″ conditions with constants `2` and `1`, respectively.
The two lifts at zero are `E`, and `1 - (-1) = 2` lies outside `E`. -/
theorem Printed.isDDoublePrimeSequence_quotient_iff_false :
    ¬ Printed.isDDoublePrimeSequence_quotient_iff := by
  intro h
  let G := Multiplicative ℤ
  have : Countable G := (Equiv.countable_iff Multiplicative.toAdd).mpr inferInstance
  have : DiscreteMeasurableSpace G := ⟨fun _ ↦ (isOpen_discrete _).measurableSet⟩
  let H : Subgroup G := Subgroup.zpowers (Multiplicative.ofAdd (3 : ℤ))
  have : DiscreteMeasurableSpace H := ⟨fun _ ↦ (isOpen_discrete _).measurableSet⟩
  have hmemH (n : ℤ) : Multiplicative.ofAdd n ∈ H ↔ ∃ k : ℤ, 3 * k = n := by
    change Multiplicative.ofAdd n ∈ Subgroup.zpowers (Multiplicative.ofAdd (3 : ℤ)) ↔ _
    rw [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← ofAdd_zsmul, zsmul_eq_mul, Int.cast_id] at hk
      have h' := Multiplicative.ofAdd.injective hk
      linarith
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      rw [← ofAdd_zsmul, zsmul_eq_mul, Int.cast_id, mul_comm]
  let E : Set G := {Multiplicative.ofAdd (-1), Multiplicative.ofAdd 0, Multiplicative.ofAdd 1}
  have hE_fin : E.Finite := (Set.finite_singleton _).insert _ |>.insert _
  have hE_meas : MeasurableSet E := MeasurableSet.of_discrete
  have hE_comp : IsCompact (closure E) := by
    rw [(isClosed_discrete E).closure_eq]
    exact hE_fin.isCompact
  have hE_int : (1 : G) ∈ interior E := by
    rw [(isOpen_discrete E).interior_eq]
    exact Or.inr (Or.inl rfl)
  have hE_inv : E⁻¹ = E := by
    ext x
    simp only [Set.mem_inv, Set.mem_insert_iff, Set.mem_singleton_iff, E]
    constructor
    · rintro (hx | hx | hx)
      · right; right; rw [← inv_inv x, hx, ← ofAdd_neg]; rfl
      · right; left; rw [← inv_inv x, hx, ← ofAdd_neg]; rfl
      · left; rw [← inv_inv x, hx, ← ofAdd_neg]
    · rintro (rfl | rfl | rfl)
      · right; right; rw [← ofAdd_neg]; rfl
      · right; left; rw [← ofAdd_neg]; rfl
      · left; rw [← ofAdd_neg]
  have hbij : Bijective (fun x : E ↦ QuotientGroup.mk' H (x : G)) := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have hrel : x⁻¹ * y ∈ H := QuotientGroup.eq.mp hxy
      have hdiff : x⁻¹ * y = Multiplicative.ofAdd (Multiplicative.toAdd y - Multiplicative.toAdd x) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, toAdd_mul, toAdd_inv]
        ring
      rw [hdiff, hmemH] at hrel
      obtain ⟨k, hk⟩ := hrel
      have hx' : Multiplicative.toAdd x = -1 ∨ Multiplicative.toAdd x = 0 ∨
          Multiplicative.toAdd x = 1 := by
        rcases hx with rfl | rfl | rfl <;> simp
      have hy' : Multiplicative.toAdd y = -1 ∨ Multiplicative.toAdd y = 0 ∨
          Multiplicative.toAdd y = 1 := by
        rcases hy with rfl | rfl | rfl <;> simp
      have heq : Multiplicative.toAdd x = Multiplicative.toAdd y := by omega
      exact Subtype.ext (Multiplicative.toAdd.injective heq)
    · intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      let n : ℤ := Multiplicative.toAdd g
      let r : ℤ := (n + 1) % 3 - 1
      have hrE : Multiplicative.ofAdd r ∈ E := by
        have hcases : r = -1 ∨ r = 0 ∨ r = 1 := by omega
        rcases hcases with h1 | h2 | h3
        · exact Or.inl (congrArg Multiplicative.ofAdd h1)
        · exact Or.inr (Or.inl (congrArg Multiplicative.ofAdd h2))
        · exact Or.inr (Or.inr (congrArg Multiplicative.ofAdd h3))
      refine ⟨⟨Multiplicative.ofAdd r, hrE⟩, ?_⟩
      change QuotientGroup.mk (Multiplicative.ofAdd r) = QuotientGroup.mk g
      apply QuotientGroup.eq.mpr
      have hdiff : (Multiplicative.ofAdd r)⁻¹ * g = Multiplicative.ofAdd (n - r) := by
        rw [← ofAdd_toAdd g, ← ofAdd_neg, ← ofAdd_add]
        congr 1; dsimp only [n]; ring
      rw [hdiff, hmemH]
      exact ⟨(n + 1) / 3, by omega⟩
  have hQ_disc : DiscreteTopology (G ⧸ H) := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun q ↦ ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simpa [Set.image_singleton] using QuotientGroup.isOpenMap_coe _ (isOpen_discrete ({g} : Set G))
  have hQ_fin : Finite (G ⧸ H) := by
    have : Finite E := hE_fin.to_subtype
    exact Finite.of_surjective _ hbij.2
  have hQ_fintype : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hBorelQ : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have : DiscreteMeasurableSpace (G ⧸ H) := ⟨fun _ ↦ (isOpen_discrete _).measurableSet⟩
  have hμ_haar : (Measure.count : Measure G).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  have hμH_haar : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  have hν_haar : (Measure.count : Measure (G ⧸ H)).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  have hν_reg : (Measure.count : Measure (G ⧸ H)).Regular := inferInstance
  have hweil : IsWeilQuotientMeasure H (Measure.count : Measure G) (Measure.count : Measure H)
      (Measure.count : Measure (G ⧸ H)) := by
    refine ⟨hν_haar, hν_reg, fun f hf ↦ ?_⟩
    have hsupp : (Function.support f).Finite :=
      hf.isCompact.finite_of_discrete.subset (subset_tsupport f)
    have hintG : Integrable f (Measure.count : Measure G) := by
      refine ⟨continuous_of_discreteTopology.measurable.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_eNorm, MeasureTheory.lintegral_count]
      rw [tsum_eq_sum (s := hsupp.toFinset) fun x hx ↦ by
        have hx0 : f x = 0 := by simpa [Set.Finite.mem_toFinset, Function.mem_support] using hx
        simp [hx0]]
      exact ENNReal.sum_lt_top.mpr fun x _ ↦ eNorm_lt_top
    have hintH (q : G ⧸ H) :
        Integrable (fun x : H ↦ f (q.out * (x : G))) (Measure.count : Measure H) := by
      have hinj : Injective (fun x : H ↦ q.out * (x : G)) :=
        (mul_right_injective q.out).comp Subtype.val_injective
      have hsuppH : (Function.support (fun x : H ↦ f (q.out * (x : G)))).Finite :=
        hsupp.preimage hinj.injOn
      refine ⟨continuous_of_discreteTopology.measurable.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_eNorm, MeasureTheory.lintegral_count]
      rw [tsum_eq_sum (s := hsuppH.toFinset) fun x hx ↦ by
        have hx0 : f (q.out * (x : G)) = 0 := by
          simpa [Set.Finite.mem_toFinset, Function.mem_support] using hx
        simp [hx0]]
      exact ENNReal.sum_lt_top.mpr fun x _ ↦ eNorm_lt_top
    rw [MeasureTheory.integral_countable hintG]
    have hlhs : (∑' x : G, (Measure.count : Measure G).real {x} • f x) = ∑' x : G, f x := by
      simp [measureReal_def]
    rw [hlhs, MeasureTheory.integral_count]
    have hcoset (q : G ⧸ H) :
        lcaCosetIntegral H (Measure.count : Measure H) f q = ∑' x : H, f (q.out * (x : G)) := by
      rw [lcaCosetIntegral, MeasureTheory.integral_countable (hintH q)]
      simp [measureReal_def]
    simp_rw [hcoset]
    let e : (G ⧸ H) × H ≃ G :=
      { toFun := fun p ↦ p.1.out * (p.2 : G)
        invFun := fun g ↦
          (QuotientGroup.mk g,
            ⟨(QuotientGroup.mk g).out⁻¹ * g, QuotientGroup.eq.mp (Quotient.out_eq' _)⟩)
        left_inv := fun ⟨q, x⟩ ↦ by
          have hmk : QuotientGroup.mk (q.out * (x : G)) = q := by
            rw [QuotientGroup.mk_mul, QuotientGroup.out_eq' q,
              (QuotientGroup.eq_one_iff (x : G)).mpr x.property, mul_one]
          ext
          · exact hmk
          · change (QuotientGroup.mk (q.out * (x : G))).out⁻¹ * (q.out * (x : G)) = (x : G)
            rw [hmk, inv_mul_cancel_left]
        right_inv := fun g ↦ mul_inv_cancel_left _ _ }
    rw [← e.tsum_eq (fun x : G ↦ f x)]
    have hsumm : Summable (fun p : (G ⧸ H) × H ↦ f (e p)) := by
      have hfinp : (Function.support (fun p : (G ⧸ H) × H ↦ f (e p))).Finite :=
        hsupp.preimage e.injective.injOn
      exact summable_of_ne_finset_zero (s := hfinp.toFinset) fun p hp ↦ by
        simpa [Set.Finite.mem_toFinset, Function.mem_support] using hp
    rw [Summable.tsum_prod hsumm, tsum_fintype]
    rfl
  let U : ℕ → Set (G ⧸ H) := fun k ↦ if k = 0 then Set.univ else {1}
  have hU_meas : ∀ k, MeasurableSet (U k) := fun _ ↦ MeasurableSet.of_discrete
  have hU_anti : Antitone U := by
    intro i j hij
    by_cases hj : j = 0
    · have hi : i = 0 := Nat.eq_zero_of_le_zero (hj ▸ hij)
      simp [U, hi, hj]
    · by_cases hi : i = 0 <;> simp [U, hi, hj]
  have hQ_ddp : IsDDoublePrimeSequence (Measure.count : Measure (G ⧸ H)) U U := by
    have hcard_pos : (0 : ENNReal) < (Fintype.card (G ⧸ H) : ENNReal) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
    have hcard_lt : (Fintype.card (G ⧸ H) : ENNReal) < ⊤ := ENNReal.natCast_lt_top _
    have hD : IsDSequence (Measure.count : Measure (G ⧸ H)) U := by
      refine ⟨fun k ↦ ?_, hU_anti, (Fintype.card (G ⧸ H) : ℝ) + 1, by positivity, fun k ↦ ?_⟩
      · dsimp only [U]
        split_ifs
        · refine ⟨trivial, MeasurableSet.univ.nullMeasurableSet, ?_, ?_⟩
          · simp [Measure.count_univ]
            exact Fintype.card_pos_iff.mpr ⟨1⟩
          · simp [Measure.count_univ]
        · exact ⟨rfl, (measurableSet_singleton 1).nullMeasurableSet,
            by simp, by simp⟩
      · have hge1 : (1 : ENNReal) ≤ Measure.count (U k) := by
          have h1 : (1 : G ⧸ H) ∈ U k := by dsimp only [U]; split_ifs <;> simp
          calc (1 : ENNReal) = Measure.count ({1} : Set (G ⧸ H)) := by simp
            _ ≤ Measure.count (U k) := measure_mono (singleton_subset_iff.mpr h1)
        have hpos : (0 : ENNReal) < Measure.count (U k * (U k)⁻¹) := by
          have h1 : (1 : G ⧸ H) ∈ U k * (U k)⁻¹ := by
            have h1' : (1 : G ⧸ H) ∈ U k := by dsimp only [U]; split_ifs <;> simp
            exact ⟨1, h1', 1, by simpa using h1', mul_one 1⟩
          calc (0 : ENNReal) < Measure.count ({1} : Set (G ⧸ H)) := by simp
            _ ≤ Measure.count (U k * (U k)⁻¹) := measure_mono (singleton_subset_iff.mpr h1)
        refine ⟨hpos, ?_⟩
        calc Measure.count (U k * (U k)⁻¹)
            ≤ Measure.count (Set.univ : Set (G ⧸ H)) := measure_mono (subset_univ _)
          _ = (Fintype.card (G ⧸ H) : ENNReal) := by simp [Measure.count_univ]
          _ < ENNReal.ofReal ((Fintype.card (G ⧸ H) : ℝ) + 1) := by
            rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
              ENNReal.ofReal_one]
            exact ENNReal.lt_add_right hcard_lt.ne one_ne_zero
          _ = ENNReal.ofReal ((Fintype.card (G ⧸ H) : ℝ) + 1) * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal ((Fintype.card (G ⧸ H) : ℝ) + 1) * Measure.count (U k) := by
            gcongr
    refine ⟨⟨hD, fun W hW ↦ ⟨1, by
      dsimp only [U]
      simp only [one_ne_zero, ↓reduceIte, singleton_subset_iff]
      exact mem_of_mem_nhds hW⟩⟩, 1, one_pos, fun k ↦ ?_⟩
    refine ⟨(hU_meas k).nullMeasurableSet, ?_, by simp⟩
    dsimp only [U]
    split_ifs
    · exact subset_univ _
    · simp
  have hiff := h G H (isClosed_discrete _) Measure.count Measure.count Measure.count
    hweil (Measure.count_singleton 1) E hE_meas hE_comp hE_int hE_inv hbij U U hU_meas hU_anti
  obtain ⟨-, C, -, hC⟩ := hiff.mp hQ_ddp
  have hsub0 : ((QuotientGroup.mk' H) ⁻¹' U 0 ∩ E) * ((QuotientGroup.mk' H) ⁻¹' U 0 ∩ E)⁻¹ ⊆
      (QuotientGroup.mk' H) ⁻¹' U 0 ∩ E := (hC 0).2.1
  have hU0 : (QuotientGroup.mk' H) ⁻¹' U 0 ∩ E = E := by
    simp [U]
  rw [hU0] at hsub0
  have hmem2 : Multiplicative.ofAdd (2 : ℤ) ∈ E * E⁻¹ := by
    refine ⟨Multiplicative.ofAdd (1 : ℤ), Or.inr (Or.inr rfl),
      (Multiplicative.ofAdd (-1 : ℤ))⁻¹,
      Set.mem_inv.mpr (by rw [inv_inv]; exact Or.inl rfl), ?_⟩
    dsimp only
    rw [← ofAdd_neg, ← ofAdd_add]
    rfl
  have h2E : Multiplicative.ofAdd (2 : ℤ) ∈ E := hsub0 hmem2
  rcases h2E with h1 | h2 | h3 <;>
    have := Multiplicative.ofAdd.injective (by assumption) <;>
    omega

end QuotientGroups

section Ideles

set_option maxSynthPendingDepth 3

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "RegulatorBasis(" F ")" =>
  Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F))
set_option quotPrecheck false in
local notation "FiniteUnitsAt(" F ", " S ")" =>
  (∀ v : {v : Primes(F) // v ∈ S}, (v.val.adicCompletionIntegers F)ˣ)
set_option quotPrecheck false in
local notation "FiniteIntegralUnits(" F ")" =>
  (∀ v : Primes(F), ↥((v.adicCompletionIntegers F).units))
local notation "I(" F ")" => IdeleGroup (𝓞 F) F
local notation "C(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "outsideInclusion" =>
  Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside _ _)))
local notation "outsideNorm(" F ", " S ")" =>
  MonoidHom.comp (ideleNorm F)
    (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S))))

local instance printedSec5aInfiniteNormOneMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (infiniteIdeleNorm F).ker := borel _

local instance printedSec5aSLocalNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace (sIdeleNorm F S).ker := borel _

local instance printedSec5aSLocalQuotientNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace (sIdeleQuotientNorm F S).ker := borel _

local instance printedSec5aGlobalNormOneMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (ideleNorm F).ker := borel _

local instance printedSec5aOutsideNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace outsideNorm(F, S).ker := borel _

local instance printedSec5aGlobalClassNormOneMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (ideleClassNorm F).ker := borel _

local instance printedSec5aSClassNormOneMeasurableSpace (F : Type) [Field F] [NumberField F]
    (S : Finset (Primes(F))) : MeasurableSpace (sIdeleClassNorm F S).ker := borel _

private def IsCompactOpenUnitBasis {G : Type} [Group G] [TopologicalSpace G]
    (B : ℕ → OpenSubgroup G) : Prop :=
  (∀ k, IsCompact (B k : Set G)) ∧ Antitone B ∧
    ∀ W ∈ 𝓝 (1 : G), ∃ k, (B k : Set G) ⊆ W

private def sLocalLogSets (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F))
    (S : Finset (Primes(F))) (B : ℕ → OpenSubgroup FiniteUnitsAt(F, S)) :
    ℕ → Set (sIdeleNorm F S).ker :=
  let insert := fun g : FiniteUnitsAt(F, S) ↦ (ContinuousMulEquiv.piUnits
    (M := fun v : {v : Primes(F) // v ∈ S} ↦ v.val.adicCompletion F)).symm
    (fun v ↦ Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom (g v))
  sLocalIdeleLogNeighborhood F b S (fun k ↦ insert '' (B k : Set _))

private def globalLogSets (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F))
    (B : ℕ → OpenSubgroup FiniteIntegralUnits(F)) : ℕ → Set (ideleNorm F).ker :=
  let insert := fun g : FiniteIntegralUnits(F) ↦ RestrictedProduct.mkUnit
    (B := fun v : Primes(F) ↦ v.adicCompletionIntegers F)
    (fun v ↦ (g v).val) (Filter.Eventually.of_forall fun v ↦ (g v).property)
  ideleLogNeighborhood F b (fun k ↦ insert '' (B k : Set _))

/-- Paper: Lemma A.5.2.13(2), p. 576.
As printed: for every number field and choice of regulator basis, the archimedean log-cube
preimages are a D′-sequence and pairing them with the preimages at indices `2 * k` gives a
D″-sequence. These are the two sequence assertions of part (2). The symmetry is proved in
`inv_infiniteIdeleLogNeighborhood`. See ERRATA F219. -/
def Printed.isDPrimeSequence_infiniteIdeleLogNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F))
    (μ : Measure (infiniteIdeleNorm F).ker) [μ.IsHaarMeasure],
    let U := infiniteIdeleLogNeighborhood F b
    IsDPrimeSequence μ U ∧ IsDDoublePrimeSequence μ U (fun k ↦ U (2 * k))

/-- Paper: Lemma A.5.2.13(2), p. 576.
For `F = ℚ`, the archimedean norm-one group is `{1, -1}` and the log rank is zero.
All the sets contain `-1`, while `{1}` is an open identity neighborhood. Both sequence
conditions require a member contained in `{1}`. -/
private theorem rat_neg_one_mem_all_infiniteIdeleLogNeighborhood
    (b : RegulatorBasis(ℚ)) :
    ∃ g : (infiniteIdeleNorm ℚ).ker, g ≠ 1 ∧ ∀ k, g ∈ infiniteIdeleLogNeighborhood ℚ b k := by
  have hneg (v : InfinitePlace ℚ) : (-1 : InfiniteAdeleRing ℚ) v = -1 := rfl
  have hnorm : infiniteIdeleNorm ℚ (-1 : (InfiniteAdeleRing ℚ)ˣ) = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
      MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val, Units.val_one,
      NNReal.coe_one, NNReal.coe_prod, NNReal.coe_pow]
    refine Finset.prod_eq_one fun v _ ↦ ?_
    change ‖((-1 : InfiniteAdeleRing ℚ) v)‖ ^ v.mult = 1
    rw [hneg v, norm_neg, norm_one, one_pow]
  let g : (infiniteIdeleNorm ℚ).ker := ⟨-1, hnorm⟩
  have hgne : g ≠ 1 := by
    intro h1
    have h0 := congrArg (fun x : (infiniteIdeleNorm ℚ).ker ↦ x.val.val Rat.infinitePlace) h1
    have hv : (-1 : Rat.infinitePlace.Completion) = (1 : Rat.infinitePlace.Completion) := h0
    have h2 : algebraMap ℚ Rat.infinitePlace.Completion (2 : ℚ) = 0 := by
      have hmap : algebraMap ℚ Rat.infinitePlace.Completion (2 : ℚ) = (1 : Rat.infinitePlace.Completion) + 1 := by
        rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
      rw [hmap]
      linear_combination -hv
    have h2q : (2 : ℚ) = 0 := (algebraMap ℚ Rat.infinitePlace.Completion).injective (by simpa using h2)
    norm_num at h2q
  have hlog : infiniteIdeleLog ℚ g.val = 0 := by
    funext v
    show (v.mult : ℝ) * Real.log ‖((-1 : InfiniteAdeleRing ℚ) v)‖ = 0
    rw [hneg v, norm_neg, norm_one, Real.log_one, mul_zero]
  exact ⟨g, hgne, (mem_all_infiniteIdeleLogNeighborhood_iff ℚ b g).mpr hlog⟩

private theorem rat_infiniteIdeleNorm_ker_compactSpace :
    CompactSpace (infiniteIdeleNorm ℚ).ker := by
  have hsub : ((infiniteIdeleNorm ℚ).ker : Set (InfiniteAdeleRing ℚ)ˣ) =
      infiniteIdeleLog ℚ ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hg
      funext v
      have hsum := infiniteIdeleLog_sum_zero ℚ ⟨g, hg⟩
      rw [Fintype.sum_subsingleton _ v] at hsum
      exact hsum
    · intro hlog
      have hv : infiniteIdeleLog ℚ g Rat.infinitePlace = 0 := congrFun hlog Rat.infinitePlace
      have hnorm : ‖g.val Rat.infinitePlace‖ = 1 := by
        have hne : g.val Rat.infinitePlace ≠ 0 :=
          (Units.map (Pi.evalRingHom (fun w : InfinitePlace ℚ ↦ w.Completion)
            Rat.infinitePlace).toMonoidHom g).ne_zero
        have hpos : 0 < ‖g.val Rat.infinitePlace‖ := norm_pos_iff.mpr hne
        have hlog0 : Real.log ‖g.val Rat.infinitePlace‖ = 0 := by
          have : (Rat.infinitePlace.mult : ℝ) * Real.log ‖g.val Rat.infinitePlace‖ = 0 := hv
          have hm : (Rat.infinitePlace.mult : ℝ) ≠ 0 := by
            simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
          exact (mul_eq_zero.mp this).resolve_left hm
        exact (Real.log_eq_zero.mp hlog0).resolve_left hpos.ne' |>.resolve_right (by linarith)
      apply Units.ext
      apply NNReal.coe_injective
      simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
        MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val, Units.val_one,
        NNReal.coe_one, NNReal.coe_prod, NNReal.coe_pow]
      rw [Fintype.prod_subsingleton _ Rat.infinitePlace]
      change ‖g.val Rat.infinitePlace‖ ^ Rat.infinitePlace.mult = 1
      rw [hnorm, one_pow]
  have hcomp : IsCompact ((infiniteIdeleNorm ℚ).ker : Set (InfiniteAdeleRing ℚ)ˣ) := by
    rw [hsub]
    exact (infiniteIdeleLog_proper ℚ).isCompact_preimage isCompact_singleton
  exact isCompact_iff_compactSpace.mp hcomp

private theorem exists_isCompactOpenUnitBasis_rat :
    ∃ B : ℕ → OpenSubgroup FiniteIntegralUnits(ℚ), IsCompactOpenUnitBasis B := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  have hcount : Countable (Primes(ℚ)) := by
    have hinj : Injective (fun v : Primes(ℚ) ↦ Submodule.IsPrincipal.generator v.asIdeal) := by
      intro v w hvw
      dsimp only at hvw
      apply HeightOneSpectrum.ext
      rw [← Submodule.IsPrincipal.span_singleton_generator v.asIdeal,
        ← Submodule.IsPrincipal.span_singleton_generator w.asIdeal, hvw]
    have hOcount : Countable (𝓞 ℚ) :=
      (Equiv.countable_iff Rat.ringOfIntegersEquiv.toEquiv).mpr inferInstance
    exact hinj.countable
  have hcomp_v (v : Primes(ℚ)) : CompactSpace ↥((v.adicCompletionIntegers ℚ).units) := by
    have : CompactSpace (v.adicCompletionIntegers ℚ) := compactSpace_adicCompletionIntegers v
    exact isCompact_iff_compactSpace.mp
      (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr this))
  have htd_v (v : Primes(ℚ)) : TotallyDisconnectedSpace ↥((v.adicCompletionIntegers ℚ).units) := by
    have : TotallyDisconnectedSpace (v.adicCompletion ℚ)ˣ :=
      ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
        Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
    infer_instance
  have hfc_v (v : Primes(ℚ)) : FirstCountableTopology ↥((v.adicCompletionIntegers ℚ).units) := by
    have : FirstCountableTopology (v.adicCompletion ℚ)ˣ :=
      (Units.isInducing_embedProduct (M := v.adicCompletion ℚ)).firstCountableTopology
    exact Topology.IsInducing.subtypeVal.firstCountableTopology
  have : CompactSpace FiniteIntegralUnits(ℚ) := Pi.compactSpace
  have : TotallyDisconnectedSpace FiniteIntegralUnits(ℚ) := inferInstance
  have : FirstCountableTopology FiniteIntegralUnits(ℚ) := inferInstance
  have hbasis : (𝓝 (1 : FiniteIntegralUnits(ℚ))).HasBasis
      (fun H : OpenSubgroup FiniteIntegralUnits(ℚ) ↦ IsCompact (H : Set FiniteIntegralUnits(ℚ)))
      (fun H ↦ (H : Set FiniteIntegralUnits(ℚ))) := by
    refine ⟨fun W ↦ ⟨exists_compact_openSubgroup_sub_mem_nhds, ?_⟩⟩
    rintro ⟨H, -, hHW⟩
    exact mem_of_superset H.mem_nhds_one hHW
  obtain ⟨B, hBcomp, hB⟩ := hbasis.exists_antitone_subbasis
  exact ⟨B, hBcomp, hB.antitone, fun _ hW ↦ hB.mem_iff.mp hW⟩

theorem Printed.isDPrimeSequence_infiniteIdeleLogNeighborhood_false :
    ¬ Printed.isDPrimeSequence_infiniteIdeleLogNeighborhood := by
  intro h
  obtain ⟨b⟩ := regulator_units_mod_torsion_basis ℚ
  obtain ⟨g, hgne, hgmem⟩ := rat_neg_one_mem_all_infiniteIdeleLogNeighborhood b
  have : BorelSpace (infiniteIdeleNorm ℚ).ker := ⟨rfl⟩
  have : CompactSpace (infiniteIdeleNorm ℚ).ker := rat_infiniteIdeleNorm_ker_compactSpace
  have : T2Space (InfiniteAdeleRing ℚ) := Pi.t2Space
  have : T2Space (InfiniteAdeleRing ℚ)ˣ :=
    T2Space.of_injective_continuous Units.val_injective Units.continuous_val
  have h1 := (h ℚ b Measure.haar).1
  have hW : ({g}ᶜ : Set (infiniteIdeleNorm ℚ).ker) ∈ 𝓝 (1 : (infiniteIdeleNorm ℚ).ker) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hgne.symm)
  obtain ⟨k, hk⟩ := h1.2 _ hW
  exact hk (hgmem k) rfl

/-- Paper: Lemma A.5.2.14, p. 576.
As printed: for every number field, finite set of places containing the infinite places,
unit basis, and decreasing compact open subgroup basis of the finite integral units at those
places, the log-cube products and their images in the norm-one S-idele quotient `J¹` are
D′-sequences. This records the two D′ assertions. The product symmetry is proved in
`inv_sLocalIdeleLogNeighborhood`. See ERRATA F219. -/
def Printed.isDPrimeSequence_sLocalIdeleLogNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteUnitsAt(F, S)), IsCompactOpenUnitBasis B →
    ∀ (μ : Measure (sIdeleNorm F S).ker) [μ.IsHaarMeasure]
      (ν : Measure (sIdeleQuotientNorm F S).ker) [ν.IsHaarMeasure],
    let U := sLocalLogSets F b S B
    let q := fun g : (sIdeleNorm F S).ker ↦
      (⟨QuotientGroup.mk g.val, (sIdeleQuotientNorm_mk F S g.val).trans g.property⟩ :
        (sIdeleQuotientNorm F S).ker)
    IsDPrimeSequence μ U ∧ IsDPrimeSequence ν (fun k ↦ q '' U k)

/-- Paper: Lemma A.5.2.14, p. 576.
Take `F = ℚ(i)` and `S` consisting of the unique complex place. There are no finite factors,
so `B k` is the trivial group for all `k`. The unit rank is zero and `U k` is the whole
norm-one circle. Its image is the whole quotient circle modulo the fourth roots of unity.
Each group has a proper identity neighborhood, so neither sequence is cofinal. -/
theorem Printed.isDPrimeSequence_sLocalIdeleLogNeighborhood_false :
    ¬ Printed.isDPrimeSequence_sLocalIdeleLogNeighborhood := by
  intro h
  obtain ⟨b⟩ := regulator_units_mod_torsion_basis ℚ
  obtain ⟨g, hgne, hgmem⟩ := rat_neg_one_mem_all_infiniteIdeleLogNeighborhood b
  let S : Finset (Primes(ℚ)) := ∅
  let B : ℕ → OpenSubgroup FiniteUnitsAt(ℚ, S) := fun _ ↦ ⊤
  have hsub : Subsingleton FiniteUnitsAt(ℚ, S) := by
    refine ⟨fun x y ↦ ?_⟩
    funext ⟨v, hv⟩
    exact False.elim (Finset.notMem_empty v hv)
  have hB : IsCompactOpenUnitBasis B := by
    refine ⟨fun _ ↦ isCompact_univ, antitone_const, fun W hW ↦ ⟨0, fun x _ ↦ ?_⟩⟩
    have hx1 : x = 1 := Subsingleton.elim x 1
    rw [hx1]
    exact mem_of_mem_nhds hW
  have : BorelSpace (sIdeleNorm ℚ S).ker := ⟨rfl⟩
  have : BorelSpace (sIdeleQuotientNorm ℚ S).ker := ⟨rfl⟩
  have : T2Space (SAdeleRing ℚ S)ˣ := (sIdeleGroup_description ℚ S).2.1
  have : CompactSpace (infiniteIdeleNorm ℚ).ker := rat_infiniteIdeleNorm_ker_compactSpace
  have hsKerComp : CompactSpace (sIdeleNorm ℚ S).ker := by
    let inclInf : (infiniteIdeleNorm ℚ).ker → (sIdeleNorm ℚ S).ker := fun x ↦
      ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing ℚ)
        (∀ v : {v : Primes(ℚ) // v ∈ S}, v.val.adicCompletion ℚ)) x.val, by
          apply Units.ext
          apply NNReal.coe_injective
          have hx1 : ((infiniteIdeleNorm ℚ x.val).val : ℝ) = 1 := by
            rw [show infiniteIdeleNorm ℚ x.val = 1 from x.property]; simp
          simp only [Units.val_one, NNReal.coe_one]
          rw [← hx1]
          simp [sIdeleNorm, infiniteIdeleNorm, S]
          rfl⟩
    have hincl_cont : Continuous inclInf := by
      refine Continuous.subtype_mk ?_ _
      have hinl : Continuous (MonoidHom.inl (InfiniteAdeleRing ℚ)
          (∀ v : {v : Primes(ℚ) // v ∈ S}, v.val.adicCompletion ℚ)) :=
        continuous_id.prodMk continuous_const
      exact (hinl.units_map _).comp continuous_subtype_val
    have hincl_surj : Surjective inclInf := by
      intro y
      let xinf : (InfiniteAdeleRing ℚ)ˣ :=
        Units.map (RingHom.fst (InfiniteAdeleRing ℚ) _).toMonoidHom y.val
      have hxnorm : infiniteIdeleNorm ℚ xinf = 1 := by
        apply Units.ext
        apply NNReal.coe_injective
        have hy1 : ((sIdeleNorm ℚ S y.val).val : ℝ) = 1 := by
          rw [show sIdeleNorm ℚ S y.val = 1 from y.property]; simp
        simp only [Units.val_one, NNReal.coe_one]
        rw [← hy1]
        simp [sIdeleNorm, infiniteIdeleNorm, xinf, S]
        rfl
      refine ⟨⟨xinf, hxnorm⟩, Subtype.ext (Units.ext (Prod.ext rfl ?_))⟩
      funext ⟨v, hv⟩
      exact False.elim (Finset.notMem_empty v hv)
    exact isCompact_univ_iff.mp (hincl_surj.range_eq ▸ isCompact_range hincl_cont)
  have hsQComp : CompactSpace (sIdeleQuotientNorm ℚ S).ker := by
    let q : (sIdeleNorm ℚ S).ker → (sIdeleQuotientNorm ℚ S).ker := fun x ↦
      ⟨QuotientGroup.mk x.val, (sIdeleQuotientNorm_mk ℚ S x.val).trans x.property⟩
    have hq_cont : Continuous q :=
      (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
    have hq_surj : Surjective q := by
      rintro ⟨c, hc⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
      exact ⟨⟨y, (sIdeleQuotientNorm_mk ℚ S y).symm.trans hc⟩, rfl⟩
    exact isCompact_univ_iff.mp (hq_surj.range_eq ▸ isCompact_range hq_cont)
  have h1 := (h ℚ b S B hB Measure.haar Measure.haar).1
  let gSval : (SAdeleRing ℚ S)ˣ :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing ℚ)
      (∀ v : {v : Primes(ℚ) // v ∈ S}, v.val.adicCompletion ℚ)) g.val
  have hgSnorm : sIdeleNorm ℚ S gSval = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    have hg1 : ((infiniteIdeleNorm ℚ g.val).val : ℝ) = 1 := by
      rw [show infiniteIdeleNorm ℚ g.val = 1 from g.property]
      simp
    simp only [Units.val_one, NNReal.coe_one]
    rw [← hg1]
    simp [sIdeleNorm, infiniteIdeleNorm, gSval, S]
    rfl
  let gS : (sIdeleNorm ℚ S).ker := ⟨gSval, hgSnorm⟩
  have hgSne : gS ≠ 1 := by
    intro h1'
    apply hgne
    apply Subtype.ext
    have hfst := congrArg (fun x : (sIdeleNorm ℚ S).ker ↦
      Units.map (RingHom.toMonoidHom (RingHom.fst _ _)) x.val) h1'
    exact (Units.ext rfl : g.val = _).trans (hfst.trans (Units.ext rfl))
  have hW : ({gS}ᶜ : Set (sIdeleNorm ℚ S).ker) ∈ 𝓝 (1 : (sIdeleNorm ℚ S).ker) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hgSne.symm)
  obtain ⟨k, hk⟩ := h1.2 _ hW
  have hgSmem : gS ∈ sLocalLogSets ℚ b S B k := by
    refine ⟨⟨g, hgmem k, ?_⟩, ⟨1, trivial, ?_⟩⟩
    · apply Units.ext
      rfl
    · apply Units.ext
      funext ⟨v, hv⟩
      exact False.elim (Finset.notMem_empty v hv)
  exact hk hgSmem rfl

/-- Paper: Lemma A.5.2.16, p. 577.
As printed: for every number field, finite set of places containing the infinite places,
unit basis, and decreasing compact open subgroup basis of the finite integral units, the
log-cube products are D′-sequences in the global and the integral-outside-S norm-one idele
groups, as are their images in both norm-one class groups. This records the D′ assertions
of parts (1)–(3). The product symmetry is proved in `inv_ideleLogNeighborhood`.
See ERRATA F219. -/
def Printed.isDPrimeSequence_ideleLogNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteIntegralUnits(F)), IsCompactOpenUnitBasis B →
    ∀ (μ : Measure (ideleNorm F).ker) [μ.IsHaarMeasure]
      (μS : Measure outsideNorm(F, S).ker) [μS.IsHaarMeasure]
      (ν : Measure (ideleClassNorm F).ker) [ν.IsHaarMeasure]
      (νS : Measure (sIdeleClassNorm F S).ker) [νS.IsHaarMeasure],
    let U := globalLogSets F b B
    let incl := fun g : outsideNorm(F, S).ker ↦
      (⟨outsideInclusion g.val, g.property⟩ : (ideleNorm F).ker)
    let US := fun k ↦ incl ⁻¹' U k
    let q := fun g : (ideleNorm F).ker ↦
      (⟨QuotientGroup.mk g.val, g.property⟩ : (ideleClassNorm F).ker)
    let qS := fun g : outsideNorm(F, S).ker ↦
      (⟨QuotientGroup.mk g.val, ((sIdeleNorm_spec F S).1 g.val).symm.trans g.property⟩ :
        (sIdeleClassNorm F S).ker)
    IsDPrimeSequence μ U ∧ IsDPrimeSequence μS US ∧
      IsDPrimeSequence ν (fun k ↦ q '' U k) ∧ IsDPrimeSequence νS (fun k ↦ qS '' US k)

/-- Paper: Lemma A.5.2.16, p. 577.
Take `F = ℚ`, no finite places in `S`, and let `B k` impose congruence to `1` modulo `p^(k+1)`
at the first `k` rational primes in increasing order. The idele with real component `-1` and
all finite components `1` belongs to every product. It has nonidentity class in both quotients:
a diagonal rational with value `1` at a finite place is `1` everywhere. In each Hausdorff
group an identity neighborhood excluding the persistent element witnesses failure of D′. -/
theorem Printed.isDPrimeSequence_ideleLogNeighborhood_false :
    ¬ Printed.isDPrimeSequence_ideleLogNeighborhood := by
  intro h
  obtain ⟨b⟩ := regulator_units_mod_torsion_basis ℚ
  obtain ⟨B, hB⟩ := exists_isCompactOpenUnitBasis_rat
  obtain ⟨g, hgne, hgmem⟩ := rat_neg_one_mem_all_infiniteIdeleLogNeighborhood b
  have : BorelSpace (ideleNorm ℚ).ker := ⟨rfl⟩
  have : BorelSpace outsideNorm(ℚ, ∅).ker := ⟨rfl⟩
  have : BorelSpace (ideleClassNorm ℚ).ker := ⟨rfl⟩
  have : BorelSpace (sIdeleClassNorm ℚ ∅).ker := ⟨rfl⟩
  have : T2Space I(ℚ) := (ideleGroup_topology ℚ).1
  have : LocallyCompactSpace I(ℚ) := (ideleGroup_topology ℚ).2.1
  have : LocallyCompactSpace (ideleNorm ℚ).ker :=
    (ideleGroup_topology ℚ).2.2.2.2.2.locallyCompactSpace
  have : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  have : CompactSpace (sIdeleClassNorm ℚ ∅).ker := (sIdeleClassGroup_finiteness ℚ ∅).2.1
  have hOutsideLC : LocallyCompactSpace outsideNorm(ℚ, ∅).ker := by
    obtain ⟨e, he_cont, he_symm, -⟩ := integralAdelesOutside_factors ℚ ∅
    have : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
    have hcomp_v (v : {v : Primes(ℚ) // v ∉ (∅ : Finset (Primes(ℚ)))}) :
        CompactSpace (v.val.adicCompletionIntegers ℚ)ˣ := by
      have : CompactSpace (v.val.adicCompletionIntegers ℚ) :=
        compactSpace_adicCompletionIntegers v.val
      exact compactSpace_units_of_compactSpace _
    have : CompactSpace (∀ v : {v : Primes(ℚ) // v ∉ (∅ : Finset (Primes(ℚ)))},
        (v.val.adicCompletionIntegers ℚ)ˣ) := Pi.compactSpace
    let eU : (integralAdelesOutside ℚ ∅)ˣ ≃ₜ
        (SAdeleRing ℚ ∅ × ∀ v : {v : Primes(ℚ) // v ∉ (∅ : Finset (Primes(ℚ)))},
          v.val.adicCompletionIntegers ℚ)ˣ :=
      { toFun := Units.map e.toRingHom.toMonoidHom
        invFun := Units.map e.symm.toRingHom.toMonoidHom
        left_inv := fun u ↦ Units.ext (e.symm_apply_apply u.val)
        right_inv := fun u ↦ Units.ext (e.apply_symm_apply u.val)
        continuous_toFun := he_cont.units_map e.toRingHom.toMonoidHom
        continuous_invFun := he_symm.units_map e.symm.toRingHom.toMonoidHom }
    let eHomeo : (integralAdelesOutside ℚ ∅)ˣ ≃ₜ
        ((SAdeleRing ℚ ∅)ˣ × ∀ v : {v : Primes(ℚ) // v ∉ (∅ : Finset (Primes(ℚ)))},
          (v.val.adicCompletionIntegers ℚ)ˣ) :=
      eU.trans ((ContinuousMulEquiv.prodUnits _ _).toHomeomorph.trans
        ((Homeomorph.refl _).prodCongr (ContinuousMulEquiv.piUnits (M := fun v :
          {v : Primes(ℚ) // v ∉ (∅ : Finset (Primes(ℚ)))} ↦
            v.val.adicCompletionIntegers ℚ)).toHomeomorph))
    have : LocallyCompactSpace (integralAdelesOutside ℚ ∅)ˣ :=
      eHomeo.isClosedEmbedding.locallyCompactSpace
    have hcont_out : Continuous outsideNorm(ℚ, ∅) :=
      (ideleGroup_topology ℚ).2.2.2.2.1.comp (continuous_subtype_val.units_map _)
    have hclosed_out : IsClosed (outsideNorm(ℚ, ∅).ker : Set (integralAdelesOutside ℚ ∅)ˣ) := by
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage hcont_out
    exact hclosed_out.locallyCompactSpace
  have h1 := (h ℚ b ∅ B hB Measure.haar Measure.haar Measure.haar Measure.haar).1
  let gGval : I(ℚ) :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) g.val
  have hgGnorm : ideleNorm ℚ gGval = 1 := by
    rw [← infiniteIdeleNorm_eq_global ℚ g.val]
    exact g.property
  let gG : (ideleNorm ℚ).ker := ⟨gGval, hgGnorm⟩
  have hgGne : gG ≠ 1 := by
    intro h1'
    apply hgne
    apply Subtype.ext
    have hfst := congrArg (fun x : (ideleNorm ℚ).ker ↦
      Units.map (RingHom.toMonoidHom (RingHom.fst _ _)) x.val) h1'
    exact (Units.ext rfl : g.val = _).trans (hfst.trans (Units.ext rfl))
  have hW : ({gG}ᶜ : Set (ideleNorm ℚ).ker) ∈ 𝓝 (1 : (ideleNorm ℚ).ker) :=
    isOpen_compl_singleton.mem_nhds (by simpa using hgGne.symm)
  obtain ⟨k, hk⟩ := h1.2 _ hW
  have hgGmem : gG ∈ globalLogSets ℚ b B k := by
    refine ⟨⟨g, hgmem k, ?_⟩, ⟨1, (B k).one_mem, ?_⟩⟩
    · apply Units.ext
      rfl
    · apply Units.ext
      rfl
  exact hk hgGmem rfl

/-- Paper: Lemma A.5.2.15, (A.5.2.22), p. 577.
As printed: for every number field and finite set of places containing the infinite places,
every finite unit subgroup basis as in Lemma A.5.2.14, and every continuous homomorphic
S-norm section, the stated products and their images in `J` are symmetric. See ERRATA F220.
Deviation: This records the symmetry clause at positive indices using `normSectionNeighborhood`.
The printed formula divides by zero at index zero. The finite factor is the one at S in
(A.5.2.21), which this lemma cites. Its introductory sentence on p. 577 names the full
finite unit group. -/
def Printed.inv_sLocalNormSectionNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteUnitsAt(F, S)), IsCompactOpenUnitBasis B →
    ∀ (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ), Continuous τ → RightInverse τ (sIdeleNorm F S) →
    ∀ k : ℕ+,
      let U := normSectionNeighborhood τ
        (fun j ↦ (sIdeleNorm F S).ker.subtype '' sLocalLogSets F b S B j) k
      let image := (QuotientGroup.mk : (SAdeleRing F S)ˣ → SIdeleQuotient F S) '' U
      U⁻¹ = U ∧ image⁻¹ = image

/-- Paper: Lemma A.5.2.15, (A.5.2.22), p. 577.
Take `F = ℚ`, `S` consisting of the real place, the trivial finite unit basis, and the
section inserting the positive real in the real place. For `k = 2`, `τ (3/5)` is in the
product because the norm-one factor contains `1`. Its inverse has norm `5/3`, outside
`(1/2, 3/2)`. The same norms apply after quotienting by the diagonal units `{1, -1}`. -/
theorem Printed.inv_sLocalNormSectionNeighborhood_false :
    ¬ Printed.inv_sLocalNormSectionNeighborhood := by
  intro h
  obtain ⟨b⟩ := regulator_units_mod_torsion_basis ℚ
  let S : Finset (Primes(ℚ)) := ∅
  let B : ℕ → OpenSubgroup FiniteUnitsAt(ℚ, S) := fun _ ↦ ⊤
  have hsub : Subsingleton FiniteUnitsAt(ℚ, S) := by
    refine ⟨fun x y ↦ ?_⟩
    funext ⟨v, hv⟩
    exact False.elim (Finset.notMem_empty v hv)
  have hB : IsCompactOpenUnitBasis B := by
    refine ⟨fun _ ↦ isCompact_univ, antitone_const, fun W hW ↦ ⟨0, fun x _ ↦ ?_⟩⟩
    have hx1 : x = 1 := Subsingleton.elim x 1
    rw [hx1]
    exact mem_of_mem_nhds hW
  let proj : I(ℚ) →* (SAdeleRing ℚ S)ˣ := Units.map (adeleProjection ℚ S).toMonoidHom
  let τ : ℝ≥0ˣ →* (SAdeleRing ℚ S)ˣ := proj.comp ratIdeleNormSection
  have hproj_cont : Continuous (adeleProjection ℚ S) :=
    continuous_fst.prodMk
      (continuous_pi fun v ↦ (RestrictedProduct.continuous_eval v.val).comp continuous_snd)
  have hτ_cont : Continuous τ :=
    (hproj_cont.units_map (adeleProjection ℚ S).toMonoidHom).comp ratIdeleNormSection_continuous
  have hτ_rinv : RightInverse τ (sIdeleNorm ℚ S) := by
    intro t
    have hmem (x : AdeleRing (𝓞 ℚ) ℚ) (hx : ∀ v : Primes(ℚ), x.2 v = 1) :
        x ∈ integralAdelesOutside ℚ S := by
      simp only [integralAdelesOutside, Subring.mem_iInf]
      intro v _
      change x.2 v ∈ v.adicCompletionIntegers ℚ
      rw [hx v]
      exact (v.adicCompletionIntegers ℚ).one_mem
    let uval : integralAdelesOutside ℚ S := ⟨(ratIdeleNormSection t).val, hmem _ fun _ ↦ rfl⟩
    let uinv : integralAdelesOutside ℚ S := ⟨(ratIdeleNormSection t).inv, hmem _ fun _ ↦ rfl⟩
    let u : (integralAdelesOutside ℚ S)ˣ :=
      ⟨uval, uinv, Subtype.ext (ratIdeleNormSection t).val_inv,
        Subtype.ext (ratIdeleNormSection t).inv_val⟩
    have h1 : Units.map (integralAdelesOutside ℚ S).subtype.toMonoidHom u =
        ratIdeleNormSection t := Units.ext rfl
    have h2 : Units.map ((adeleProjection ℚ S).comp (integralAdelesOutside ℚ S).subtype).toMonoidHom u =
        τ t := Units.ext rfl
    rw [← h2, ← (sIdeleNorm_spec ℚ S).1 u, h1]
    exact ratIdeleNormSection_rightInverse t
  let k : ℕ+ := ⟨2, by norm_num⟩
  have hinv := (h ℚ b S B hB τ hτ_cont hτ_rinv k).1
  let V : ℕ → Set (SAdeleRing ℚ S)ˣ :=
    fun j ↦ (sIdeleNorm ℚ S).ker.subtype '' sLocalLogSets ℚ b S B j
  let U : Set (SAdeleRing ℚ S)ˣ := normSectionNeighborhood τ V k
  have hV1 : 1 ∈ V k := by
    refine ⟨1, ?_, rfl⟩
    rw [sLocalLogSets, one_mem_sLocalIdeleLogNeighborhood_iff]
    exact ⟨1, trivial, by apply Units.ext; funext ⟨v, hv⟩; exact False.elim (Finset.notMem_empty v hv)⟩
  have hVker : V k ⊆ (sIdeleNorm ℚ S).ker := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property
  have himg := norm_image_normSectionNeighborhood (sIdeleNorm ℚ S) τ hτ_rinv V k hV1 hVker
  let t : ℝ≥0ˣ := Units.mk0 (3 / 5 : ℝ≥0) (by norm_num)
  have ht : t ∈ sIdeleNorm ℚ S '' U := by
    rw [himg]
    change (t.val : ℝ) ∈ Ioo (1 - 1 / (k : ℝ)) (1 + 1 / (k : ℝ))
    simp only [t, k, PNat.mk_coe, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat, Set.mem_Ioo]
    norm_num
  obtain ⟨u, huU, hut⟩ := ht
  have huinv : u⁻¹ ∈ U := by
    dsimp only [U, V]
    rw [← hinv]
    exact Set.inv_mem_inv.mpr huU
  have htinv : t⁻¹ ∈ sIdeleNorm ℚ S '' U := ⟨u⁻¹, huinv, by rw [map_inv, hut]⟩
  rw [himg] at htinv
  have hlt : ((t⁻¹).val : ℝ) < 1 + 1 / (k : ℝ) := htinv.2
  simp only [t, k, PNat.mk_coe, Units.val_inv_eq_inv_val, Units.val_mk0, NNReal.coe_inv,
    NNReal.coe_div, NNReal.coe_ofNat] at hlt
  norm_num at hlt

/-- Paper: Lemma A.5.2.17, (A.5.2.24), p. 577.
As printed: for every number field and finite set of places containing the infinite places,
every finite unit subgroup basis as in Lemma A.5.2.16, and every continuous homomorphic
norm section, the products and their global class images are symmetric. If the section
lands among the ideles integral outside S, symmetry also holds there and in their S-class
images. See ERRATA F220.
Deviation: This records the symmetry clause at positive indices using `normSectionNeighborhood`.
The printed formula divides by zero at index zero. -/
def Printed.inv_ideleNormSectionNeighborhood : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (b : RegulatorBasis(F)) (S : Finset (Primes(F)))
    (B : ℕ → OpenSubgroup FiniteIntegralUnits(F)), IsCompactOpenUnitBasis B →
    ∀ (τ : ℝ≥0ˣ →* I(F)), Continuous τ → RightInverse τ (ideleNorm F) →
    ∀ k : ℕ+,
      let U := normSectionNeighborhood τ
        (fun j ↦ (ideleNorm F).ker.subtype '' globalLogSets F b B j) k
      let image := (QuotientGroup.mk : I(F) → C(F)) '' U
      let incl : (integralAdelesOutside F S)ˣ →* I(F) := outsideInclusion
      let US := incl ⁻¹' U
      let imageS := (QuotientGroup.mk : (integralAdelesOutside F S)ˣ → SIdeleClassGroup F S) '' US
      U⁻¹ = U ∧ image⁻¹ = image ∧
        ((∃ τS : ℝ≥0ˣ →* (integralAdelesOutside F S)ˣ, Continuous τS ∧ incl.comp τS = τ) →
          US⁻¹ = US ∧ imageS⁻¹ = imageS)

/-- Paper: Lemma A.5.2.17, (A.5.2.24), p. 577.
Take `F = ℚ`, no finite places in `S`, the finite subgroup basis given by congruence to `1`
modulo `p^(k+1)` at the first `k` rational primes, and `ratIdeleNormSection`. The section
has all finite components `1`, so it lands among the ideles integral outside S. At `k = 2`
its value at `3/5` belongs to the product. The inverse has norm `5/3`, outside `(1/2, 3/2)`,
also under the descended norms on both class groups. -/
theorem Printed.inv_ideleNormSectionNeighborhood_false :
    ¬ Printed.inv_ideleNormSectionNeighborhood := by
  intro h
  obtain ⟨b⟩ := regulator_units_mod_torsion_basis ℚ
  obtain ⟨B, hB⟩ := exists_isCompactOpenUnitBasis_rat
  let k : ℕ+ := ⟨2, by norm_num⟩
  have hinv := (h ℚ b ∅ B hB ratIdeleNormSection ratIdeleNormSection_continuous
    ratIdeleNormSection_rightInverse k).1
  let V : ℕ → Set I(ℚ) :=
    fun j ↦ (ideleNorm ℚ).ker.subtype '' globalLogSets ℚ b B j
  let U : Set I(ℚ) := normSectionNeighborhood ratIdeleNormSection V k
  have hV1 : 1 ∈ V k := by
    refine ⟨1, ?_, rfl⟩
    rw [globalLogSets, one_mem_ideleLogNeighborhood_iff]
    exact ⟨1, (B k).one_mem, Units.ext rfl⟩
  have hVker : V k ⊆ (ideleNorm ℚ).ker := by
    rintro _ ⟨x, -, rfl⟩
    exact x.property
  have himg := norm_image_normSectionNeighborhood (ideleNorm ℚ) ratIdeleNormSection
    ratIdeleNormSection_rightInverse V k hV1 hVker
  let t : ℝ≥0ˣ := Units.mk0 (3 / 5 : ℝ≥0) (by norm_num)
  have ht : t ∈ ideleNorm ℚ '' U := by
    rw [himg]
    change (t.val : ℝ) ∈ Ioo (1 - 1 / (k : ℝ)) (1 + 1 / (k : ℝ))
    simp only [t, k, PNat.mk_coe, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat, Set.mem_Ioo]
    norm_num
  obtain ⟨u, huU, hut⟩ := ht
  have huinv : u⁻¹ ∈ U := by
    dsimp only [U, V]
    rw [← hinv]
    exact Set.inv_mem_inv.mpr huU
  have htinv : t⁻¹ ∈ ideleNorm ℚ '' U := ⟨u⁻¹, huinv, by rw [map_inv, hut]⟩
  rw [himg] at htinv
  have hlt : ((t⁻¹).val : ℝ) < 1 + 1 / (k : ℝ) := htinv.2
  simp only [t, k, PNat.mk_coe, Units.val_inv_eq_inv_val, Units.val_mk0, NNReal.coe_inv,
    NNReal.coe_div, NNReal.coe_ofNat] at hlt
  norm_num at hlt

end Ideles

end RiemannMasullo
