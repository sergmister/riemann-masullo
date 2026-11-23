module

public import RiemannMasullo.Ch12_TraceGeometric.Sec2
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count

/-!
# Section 12.2: statements that are false as printed
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace RiemannMasullo

local instance instQuotientMeasurableSpaceSec2Printed {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : MeasurableSpace (G ⧸ H) := borel _

/-- Paper: Proposition 12.2.2.2(4), p. 509. The last sentence asserts that at every
pair in the group product, regularity for the indented lift is equivalent to regularity
of the quotient pair for the original kernel. -/
def Printed.diagonalIndentationLift_regular_iff : Prop :=
  ∀ {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [DiscreteTopology H],
    IsClosed (H : Set G) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure (G ⧸ H)),
    IsWeilQuotientMeasure H μ Measure.count ν →
    ∀ (D : Set G) (U : ℕ → Set G), IsConnected D → IsDiagonalIndentationSituation H μ D U →
    ∀ (b : G → ℝ), IsIndentation H Measure.count b →
    ∀ (u : (G ⧸ H) × (G ⧸ H) → ℂ), LocallyIntegrable u (ν.prod ν) →
    ∀ p : G × G,
      p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n)
        (diagonalIndentationLift H Measure.count b u) ↔
      (QuotientGroup.mk p.1, QuotientGroup.mk p.2) ∈
        dSequenceRegularSet (ν.prod ν) (fun n ↦
          (QuotientGroup.mk' H '' U n) ×ˢ (QuotientGroup.mk' H '' U n)) u

/-! ### A counterexample on `ℤ × ℝ`

The Lean proof below uses the multiplicative copy of `ℤ × ℝ`, the subgroup `ℤ × {0}`,
the slice `D = {0} × ℝ`, `U n = {0} × (−2⁻ⁿ, 2⁻ⁿ)` and the indentation `b` equal to one on the
slice `{0} × ℝ` and zero elsewhere. At the pair `p = ((0, 0), (1, 0))` the two points lie in
different slices, so the weight `∑ₕ b(h⁻¹ p₁) b(h⁻¹ p₂)` vanishes near `p` and every lift average
is zero, while `p` projects to the identity pair of the quotient, where the kernel
`u(x, y) = f(x) 1_{V₀}(y)` with `f = ∑ₖ 1_{Vₖ}` (`Vₖ` the image of `Uₖ`) has averages at least
`k + 1`. -/

local notation "𝔾" => Multiplicative (ℤ × ℝ)

private instance instBorelSpaceMultiplicativeIntRealSec2Printed : BorelSpace 𝔾 :=
  inferInstanceAs (BorelSpace (ℤ × ℝ))

private def Printed.sec2H : Subgroup 𝔾 where
  carrier := {x | (Multiplicative.toAdd x).2 = 0}
  mul_mem' {x y} hx hy := by simp_all
  one_mem' := by simp
  inv_mem' {x} hx := by simp_all

private def Printed.sec2D : Set 𝔾 := {x | (Multiplicative.toAdd x).1 = 0}

private def Printed.sec2U (n : ℕ) : Set 𝔾 :=
  {x | (Multiplicative.toAdd x).1 = 0 ∧ |(Multiplicative.toAdd x).2| < (2⁻¹ : ℝ) ^ n}

private def Printed.sec2b (x : 𝔾) : ℝ := if (Multiplicative.toAdd x).1 = 0 then 1 else 0

private def Printed.sec2g (t : ℝ) : 𝔾 := Multiplicative.ofAdd (0, t)

private theorem Printed.sec2_continuous_fst :
    Continuous (fun x : 𝔾 ↦ (Multiplicative.toAdd x).1) :=
  continuous_fst.comp continuous_toAdd

private theorem Printed.sec2_continuous_snd :
    Continuous (fun x : 𝔾 ↦ (Multiplicative.toAdd x).2) :=
  continuous_snd.comp continuous_toAdd

private theorem Printed.sec2_continuous_g : Continuous Printed.sec2g :=
  continuous_ofAdd.comp (continuous_const.prodMk continuous_id)

private theorem Printed.sec2_isClosed_H : IsClosed (Printed.sec2H : Set 𝔾) :=
  isClosed_eq Printed.sec2_continuous_snd continuous_const

private theorem Printed.sec2_discrete_H : DiscreteTopology Printed.sec2H := by
  refine DiscreteTopology.of_continuous_injective
    (f := fun h : Printed.sec2H ↦ (Multiplicative.toAdd (h : 𝔾)).1)
    (Printed.sec2_continuous_fst.comp continuous_subtype_val) ?_
  intro h k hhk
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  exact Prod.ext hhk (h.2.trans k.2.symm)

private theorem Printed.sec2_isOpen_D : IsOpen Printed.sec2D :=
  (isOpen_discrete ({0} : Set ℤ)).preimage Printed.sec2_continuous_fst

private theorem Printed.sec2_isClosed_D : IsClosed Printed.sec2D :=
  (isClosed_discrete ({0} : Set ℤ)).preimage Printed.sec2_continuous_fst

private theorem Printed.sec2_isConnected_D : IsConnected Printed.sec2D := by
  have : Printed.sec2D = range Printed.sec2g := by
    ext x
    refine ⟨fun hx ↦ ⟨(Multiplicative.toAdd x).2, ?_⟩, ?_⟩
    · apply Multiplicative.toAdd.injective
      exact Prod.ext hx.symm rfl
    · rintro ⟨t, rfl⟩
      rfl
  rw [this]
  exact isConnected_range Printed.sec2_continuous_g

private theorem Printed.sec2_fundamentalDomain (μ : Measure 𝔾) :
    IsIndentationFundamentalDomain Printed.sec2H μ Printed.sec2D := by
  refine ⟨⟨1, ?_⟩, fun x ↦ ?_, fun a ha ↦ ?_⟩
  · rw [Printed.sec2_isOpen_D.interior_eq]
    rfl
  · refine ⟨⟨Multiplicative.ofAdd (-(Multiplicative.toAdd x).1, 0), rfl⟩, ?_, ?_⟩
    · change (Multiplicative.toAdd
        (Multiplicative.ofAdd (-(Multiplicative.toAdd x).1, (0 : ℝ)) * x)).1 = 0
      simp
    · intro a ha
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      have ha' : (Multiplicative.toAdd ((a : 𝔾) * x)).1 = 0 := ha
      simp only [toAdd_mul, Prod.fst_add] at ha'
      refine Prod.ext ?_ a.2
      simp only [toAdd_ofAdd]
      omega
  · rw [Printed.sec2_isClosed_D.closure_eq]
    convert measure_empty (μ := μ)
    rw [eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hy'⟩
    obtain ⟨z, hz, rfl⟩ := mem_smul_set.mp hy'
    have h1 : (Multiplicative.toAdd (a : 𝔾)).1 ≠ 0 := by
      intro h0
      apply ha
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      exact Prod.ext h0 a.2
    have hy0 : (Multiplicative.toAdd ((a : 𝔾) * z)).1 = 0 := hy
    have hz0 : (Multiplicative.toAdd z).1 = 0 := hz
    simp only [toAdd_mul, Prod.fst_add] at hy0
    exact h1 (by omega)

private theorem Printed.sec2_g_mem_U {n : ℕ} {t : ℝ} (ht : |t| < (2⁻¹ : ℝ) ^ n) :
    Printed.sec2g t ∈ Printed.sec2U n := ⟨rfl, ht⟩

private theorem Printed.sec2_isOpen_U (n : ℕ) : IsOpen (Printed.sec2U n) :=
  Printed.sec2_isOpen_D.inter
    (isOpen_lt (continuous_abs.comp Printed.sec2_continuous_snd) continuous_const)

private theorem Printed.sec2_one_mem_U (n : ℕ) : (1 : 𝔾) ∈ Printed.sec2U n :=
  ⟨rfl, by simp⟩

private theorem Printed.sec2_U_subset (n : ℕ) :
    Printed.sec2U n ⊆ Printed.sec2g '' Icc (-(2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ n) := by
  intro x hx
  refine ⟨(Multiplicative.toAdd x).2, ?_, ?_⟩
  · have := abs_lt.mp hx.2
    exact ⟨by linarith, by linarith⟩
  · apply Multiplicative.toAdd.injective
    exact Prod.ext hx.1.symm rfl

private theorem Printed.sec2_isCompact_closure_U (n : ℕ) :
    IsCompact (closure (Printed.sec2U n)) := by
  have hK := (isCompact_Icc (a := -(2⁻¹ : ℝ) ^ n) (b := (2⁻¹ : ℝ) ^ n)).image
    Printed.sec2_continuous_g
  exact hK.of_isClosed_subset isClosed_closure
    (closure_minimal (Printed.sec2_U_subset n) hK.isClosed)

private theorem Printed.sec2_antitone_U : Antitone Printed.sec2U := by
  intro m n hmn x hx
  exact ⟨hx.1, hx.2.trans_le (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)⟩

private theorem Printed.sec2_inv_U (n : ℕ) : (Printed.sec2U n)⁻¹ = Printed.sec2U n := by
  ext x
  simp [Printed.sec2U, abs_neg]

private theorem Printed.sec2_mul_inv_U (n : ℕ) :
    Printed.sec2U n * (Printed.sec2U n)⁻¹ ⊆
      (Printed.sec2g ((2⁻¹ : ℝ) ^ n))⁻¹ • Printed.sec2U n ∪ Printed.sec2U n ∪
        Printed.sec2g ((2⁻¹ : ℝ) ^ n) • Printed.sec2U n := by
  rw [Printed.sec2_inv_U]
  rintro y ⟨x, hx, z, hz, rfl⟩
  have hx2 := abs_lt.mp hx.2
  have hz2 := abs_lt.mp hz.2
  have hx1 : (Multiplicative.toAdd x).1 = 0 := hx.1
  have hz1 : (Multiplicative.toAdd z).1 = 0 := hz.1
  by_cases h1 : (2⁻¹ : ℝ) ^ n ≤ (Multiplicative.toAdd x).2 + (Multiplicative.toAdd z).2
  · right
    rw [mem_smul_set_iff_inv_smul_mem]
    refine ⟨?_, ?_⟩
    · simp [Printed.sec2g, hx1, hz1]
    · simp only [Printed.sec2g, smul_eq_mul, toAdd_mul, toAdd_inv, toAdd_ofAdd, Prod.snd_add,
        Prod.snd_neg]
      rw [abs_lt]
      constructor <;> linarith
  · by_cases h2 : (Multiplicative.toAdd x).2 + (Multiplicative.toAdd z).2 ≤ -(2⁻¹ : ℝ) ^ n
    · left; left
      rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
      refine ⟨?_, ?_⟩
      · simp [Printed.sec2g, hx1, hz1]
      · simp only [Printed.sec2g, smul_eq_mul, toAdd_mul, toAdd_ofAdd, Prod.snd_add]
        rw [abs_lt]
        constructor <;> linarith
    · left; right
      refine ⟨?_, ?_⟩
      · simp [hx1, hz1]
      · simp only [toAdd_mul, Prod.snd_add]
        rw [abs_lt]
        constructor <;> linarith

private theorem Printed.sec2_cofinal (W : Set 𝔾) (hW : W ∈ 𝓝 (1 : 𝔾)) :
    ∃ k, Printed.sec2U k ⊆ W := by
  have hg0 : Printed.sec2g 0 = 1 := rfl
  have hW' : Printed.sec2g ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
    Printed.sec2_continuous_g.continuousAt.preimage_mem_nhds (hg0 ▸ hW)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW'
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨k, fun x hx ↦ ?_⟩
  have hx' : x = Printed.sec2g (Multiplicative.toAdd x).2 := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext hx.1 rfl
  rw [hx']
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact hx.2.trans hk

private theorem Printed.sec2_measure_mul_inv_U (μ : Measure 𝔾) [μ.IsHaarMeasure] (n : ℕ) :
    μ (Printed.sec2U n * (Printed.sec2U n)⁻¹) ≤ 3 * μ (Printed.sec2U n) := by
  calc _
      ≤ μ ((Printed.sec2g ((2⁻¹ : ℝ) ^ n))⁻¹ • Printed.sec2U n ∪ Printed.sec2U n ∪
        Printed.sec2g ((2⁻¹ : ℝ) ^ n) • Printed.sec2U n) :=
      measure_mono (Printed.sec2_mul_inv_U n)
    _ ≤ μ ((Printed.sec2g ((2⁻¹ : ℝ) ^ n))⁻¹ • Printed.sec2U n) +
        μ (Printed.sec2U n) +
        μ (Printed.sec2g ((2⁻¹ : ℝ) ^ n) • Printed.sec2U n) :=
      (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ = 3 * μ (Printed.sec2U n) := by rw [measure_smul, measure_smul]; ring

private theorem Printed.sec2_isDPrime (μ : Measure 𝔾) [μ.IsHaarMeasure] :
    IsDPrimeSequence μ Printed.sec2U := by
  have hpos (k : ℕ) : 0 < μ (Printed.sec2U k) :=
    (Printed.sec2_isOpen_U k).measure_pos μ ⟨1, Printed.sec2_one_mem_U k⟩
  have hfin (k : ℕ) : μ (Printed.sec2U k) < ∞ :=
    (measure_mono subset_closure).trans_lt (Printed.sec2_isCompact_closure_U k).measure_lt_top
  refine ⟨⟨fun k ↦ ⟨Printed.sec2_one_mem_U k,
    (Printed.sec2_isOpen_U k).measurableSet.nullMeasurableSet, hpos k, hfin k⟩,
    Printed.sec2_antitone_U, 4, by norm_num, fun k ↦ ⟨?_, ?_⟩⟩, Printed.sec2_cofinal⟩
  · refine (hpos k).trans_le (measure_mono fun x hx ↦ ⟨x, hx, 1, ?_, mul_one x⟩)
    rw [Printed.sec2_inv_U]
    exact Printed.sec2_one_mem_U k
  · calc _ ≤ 3 * μ (Printed.sec2U k) := Printed.sec2_measure_mul_inv_U μ k
      _ < ENNReal.ofReal 4 * μ (Printed.sec2U k) := by
        rw [ENNReal.ofReal_ofNat]
        exact (ENNReal.mul_lt_mul_iff_left (hpos k).ne' (hfin k).ne).mpr (by norm_num)

private theorem Printed.sec2_situation (μ : Measure 𝔾) [μ.IsHaarMeasure] :
    IsDiagonalIndentationSituation Printed.sec2H μ Printed.sec2D Printed.sec2U :=
  ⟨Printed.sec2_fundamentalDomain μ, Printed.sec2_isDPrime μ, fun n ↦ ⟨fun _ hx ↦ hx.1,
    Printed.sec2_isOpen_U n, Printed.sec2_isCompact_closure_U n, Printed.sec2_inv_U n⟩⟩

private theorem Printed.sec2_isIndentation :
    IsIndentation Printed.sec2H Measure.count Printed.sec2b := by
  refine ⟨?_, fun x ↦ ?_, fun K hK ↦ ?_, fun x ↦ ?_⟩
  · exact (continuous_of_discreteTopology
      (f := fun n : ℤ ↦ if n = 0 then (1 : ℝ) else 0)).comp Printed.sec2_continuous_fst
  · unfold Printed.sec2b
    split_ifs <;> norm_num
  · have hts : tsupport Printed.sec2b = Printed.sec2D := by
      have : Function.support Printed.sec2b = Printed.sec2D := by
        ext x
        simp [Printed.sec2b, Printed.sec2D, Function.mem_support]
      rw [tsupport, this, Printed.sec2_isClosed_D.closure_eq]
    let ψ : 𝔾 → 𝔾 := fun x ↦ Printed.sec2g (Multiplicative.toAdd x).2
    have hψ : Continuous ψ := Printed.sec2_continuous_g.comp Printed.sec2_continuous_snd
    have heq : tsupport Printed.sec2b ∩
        QuotientGroup.mk' Printed.sec2H ⁻¹' (QuotientGroup.mk' Printed.sec2H '' K) =
          ψ '' K := by
      rw [hts]
      ext x
      constructor
      · rintro ⟨hx, k, hk, hkx⟩
        refine ⟨k, hk, ?_⟩
        have hz' : (Multiplicative.toAdd (k⁻¹ * x)).2 = 0 := QuotientGroup.eq.mp hkx
        have hx' : (Multiplicative.toAdd x).1 = 0 := hx
        simp only [toAdd_mul, toAdd_inv, Prod.snd_add, Prod.snd_neg] at hz'
        apply Multiplicative.toAdd.injective
        refine Prod.ext hx'.symm ?_
        simp only [ψ, Printed.sec2g, toAdd_ofAdd]
        linarith
      · rintro ⟨k, hk, rfl⟩
        refine ⟨rfl, k, hk, QuotientGroup.eq.mpr ?_⟩
        show (Multiplicative.toAdd (k⁻¹ * ψ k)).2 = 0
        simp [ψ, Printed.sec2g]
    rw [heq]
    exact hK.image hψ
  · let h0 : Printed.sec2H := ⟨Multiplicative.ofAdd ((Multiplicative.toAdd x).1, 0), rfl⟩
    have hfun : (fun h : Printed.sec2H ↦ Printed.sec2b ((h : 𝔾)⁻¹ * x)) =
        ({h0} : Set Printed.sec2H).indicator 1 := by
      funext h
      by_cases hh : h = h0
      · subst hh
        simp [Printed.sec2b, h0]
      · rw [indicator_of_notMem (by simpa using hh)]
        simp only [Printed.sec2b, toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg]
        rw [ite_eq_right_iff]
        intro h1
        exfalso
        apply hh
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        refine Prod.ext ?_ h.2
        simp only [h0, toAdd_ofAdd]
        omega
    rw [hfun]
    refine ⟨(integrable_indicator_iff (measurableSet_singleton h0)).2
      (integrableOn_const (by simp)), ?_⟩
    rw [integral_indicator_one (measurableSet_singleton h0)]
    simp [Measure.real]

private theorem Printed.sec2_weight_eq_zero (p : 𝔾 × 𝔾)
    (hp : (Multiplicative.toAdd p.1).1 ≠ (Multiplicative.toAdd p.2).1) :
    diagonalIndentationWeight Printed.sec2H Measure.count Printed.sec2b p = 0 := by
  unfold diagonalIndentationWeight
  refine integral_eq_zero_of_ae (ae_of_all _ fun h ↦ ?_)
  simp only [Printed.sec2b, toAdd_mul, toAdd_inv, Prod.fst_add, Prod.fst_neg, Pi.zero_apply]
  split_ifs with h1 h2
  · exact absurd (by omega) hp
  all_goals norm_num

private theorem Printed.sec2_lift_regular (μ : Measure 𝔾)
    (u : (𝔾 ⧸ Printed.sec2H) × (𝔾 ⧸ Printed.sec2H) → ℂ) :
    ((1 : 𝔾), Multiplicative.ofAdd ((1 : ℤ), (0 : ℝ))) ∈
      dSequenceRegularSet (μ.prod μ) (fun n ↦ Printed.sec2U n ×ˢ Printed.sec2U n)
        (diagonalIndentationLift Printed.sec2H Measure.count Printed.sec2b u) := by
  refine ⟨0, tendsto_const_nhds.congr fun k ↦ ?_⟩
  symm
  rw [dSequenceAverage, setAverage_eq, setIntegral_eq_zero_of_forall_eq_zero, smul_zero]
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_smul_set.mp hy
  unfold diagonalIndentationLift
  rw [Printed.sec2_weight_eq_zero, Complex.ofReal_zero, zero_mul]
  have h1 : (Multiplicative.toAdd z.1).1 = 0 := hz.1.1
  have h2 : (Multiplicative.toAdd z.2).1 = 0 := hz.2.1
  simp [h1, h2]

private theorem Printed.sec2_mk_eq_snd {x y : 𝔾}
    (h : (QuotientGroup.mk x : 𝔾 ⧸ Printed.sec2H) = QuotientGroup.mk y) :
    (Multiplicative.toAdd x).2 = (Multiplicative.toAdd y).2 := by
  have h' : (Multiplicative.toAdd (x⁻¹ * y)).2 = 0 := QuotientGroup.eq.mp h
  simp only [toAdd_mul, toAdd_inv, Prod.snd_add, Prod.snd_neg] at h'
  linarith

private theorem Printed.sec2_isOpen_V (k : ℕ) :
    IsOpen (QuotientGroup.mk' Printed.sec2H '' Printed.sec2U k) :=
  QuotientGroup.isOpenMap_coe _ (Printed.sec2_isOpen_U k)

private theorem Printed.sec2_halving (ν : Measure (𝔾 ⧸ Printed.sec2H)) [ν.IsMulLeftInvariant]
    (k : ℕ) :
    2 * ν (QuotientGroup.mk' Printed.sec2H '' Printed.sec2U (k + 1)) ≤
      ν (QuotientGroup.mk' Printed.sec2H '' Printed.sec2U k) := by
  have : BorelSpace (𝔾 ⧸ Printed.sec2H) := ⟨rfl⟩
  let a : 𝔾 := Printed.sec2g ((2⁻¹ : ℝ) ^ (k + 1))
  let V := QuotientGroup.mk' Printed.sec2H '' Printed.sec2U (k + 1)
  let c := QuotientGroup.mk' Printed.sec2H a
  have hsub (b : 𝔾) (hb : |(Multiplicative.toAdd b).2| = (2⁻¹ : ℝ) ^ (k + 1))
      (hb1 : (Multiplicative.toAdd b).1 = 0) : b • Printed.sec2U (k + 1) ⊆ Printed.sec2U k := by
    rintro y ⟨x, hx, rfl⟩
    have hx1 : (Multiplicative.toAdd x).1 = 0 := hx.1
    refine ⟨by simp [hb1, hx1], ?_⟩
    simp only [smul_eq_mul, toAdd_mul, Prod.snd_add]
    calc _ ≤ |(Multiplicative.toAdd b).2| + |(Multiplicative.toAdd x).2| := abs_add_le _ _
      _ < (2⁻¹ : ℝ) ^ (k + 1) + (2⁻¹ : ℝ) ^ (k + 1) := by rw [hb]; linarith [hx.2]
      _ = (2⁻¹ : ℝ) ^ k := by rw [pow_succ]; ring
  have h1 : c • V ⊆ QuotientGroup.mk' Printed.sec2H '' Printed.sec2U k := by
    rw [← Set.image_smul_distrib]
    exact image_mono (hsub a (by simp [a, Printed.sec2g]) rfl)
  have h2 : c⁻¹ • V ⊆ QuotientGroup.mk' Printed.sec2H '' Printed.sec2U k := by
    rw [← map_inv, ← Set.image_smul_distrib]
    exact image_mono
      (hsub a⁻¹ (by simp [a, Printed.sec2g]) (by simp [a, Printed.sec2g]))
  have hdisj : Disjoint (c • V) (c⁻¹ • V) := by
    rw [Set.disjoint_left]
    rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨x', hx', rfl⟩, hxy⟩
    have hq : (QuotientGroup.mk (a⁻¹ * x') : 𝔾 ⧸ Printed.sec2H) =
        QuotientGroup.mk (a * x) := hxy
    have he := Printed.sec2_mk_eq_snd hq
    simp only [a, Printed.sec2g, toAdd_mul, toAdd_inv, toAdd_ofAdd, Prod.snd_add, Prod.snd_neg]
      at he
    have := abs_lt.mp hx.2
    have := abs_lt.mp hx'.2
    linarith
  have hmeas : MeasurableSet (c⁻¹ • V) :=
    ((Printed.sec2_isOpen_V (k + 1)).smul _).measurableSet
  calc 2 * ν V = ν (c • V) + ν (c⁻¹ • V) := by rw [measure_smul, measure_smul, two_mul]
    _ = ν (c • V ∪ c⁻¹ • V) := (measure_union hdisj hmeas).symm
    _ ≤ _ := measure_mono (union_subset h1 h2)

private theorem Printed.sec2_aux
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [SFinite ν]
    (V : ℕ → Set Q) (hV : Antitone V) (hmeas : ∀ k, MeasurableSet (V k))
    (hpos : ∀ k, ν (V k) ≠ 0) (hfin : ν (V 0) ≠ ∞)
    (h2 : ∀ k, 2 * ν (V (k + 1)) ≤ ν (V k)) :
    ∃ u : Q × Q → ℂ, Integrable u (ν.prod ν) ∧
      ¬ ∃ l : ℂ,
        Tendsto (fun k ↦ ⨍ z in V k ×ˢ V k, u z ∂(ν.prod ν)) atTop (𝓝 l) := by
  have hle : ∀ k, ν (V k) ≤ ν (V 0) * 2⁻¹ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc ν (V (k + 1)) ≤ ν (V k) / 2 := by
            rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num), mul_comm]
            exact h2 k
        _ = ν (V k) * 2⁻¹ := div_eq_mul_inv _ _
        _ ≤ ν (V 0) * 2⁻¹ ^ k * 2⁻¹ := by gcongr
        _ = ν (V 0) * 2⁻¹ ^ (k + 1) := by rw [pow_succ, mul_assoc]
  have hsum : ∑' k, ν (V k) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ν (V 0) * ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k) ?_ ?_
    · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.mul_ne_top hfin (by norm_num)
    · rw [← ENNReal.tsum_mul_left]
      exact tsum_le_tsum hle
  have hfinV (k : ℕ) : ν (V k) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (hV (Nat.zero_le k)))
  let F : Q → ℝ≥0∞ := fun q ↦ ∑' k, (V k).indicator 1 q
  have hFm : Measurable F := Measurable.tsum fun k ↦ measurable_one.indicator (hmeas k)
  have hFint : ∫⁻ q, F q ∂ν = ∑' k, ν (V k) := by
    rw [lintegral_tsum fun k ↦ (measurable_one.indicator (hmeas k)).aemeasurable]
    simp only [lintegral_indicator_one (hmeas _)]
  have hFne : ∫⁻ q, F q ∂ν ≠ ∞ := hFint ▸ hsum
  have hFae : ∀ᵐ q ∂ν, F q < ∞ := ae_lt_top hFm hFne
  let f : Q → ℝ := fun q ↦ (F q).toReal
  have hf : Integrable f ν := integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hFne
  let g : Q → ℝ := (V 0).indicator 1
  have hg : Integrable g ν := (integrable_indicator_iff (hmeas 0)).2 (integrableOn_const (hfinV 0))
  refine ⟨fun z ↦ ((f z.1 * g z.2 : ℝ) : ℂ), (hf.mul_prod hg).ofReal, ?_⟩
  rintro ⟨l, hl⟩
  let a : ℕ → ℝ := fun k ↦ (ν.real (V k))⁻¹ * ∫ q in V k, f q ∂ν
  have havg (k : ℕ) :
      ⨍ z in V k ×ˢ V k, ((f z.1 * g z.2 : ℝ) : ℂ) ∂(ν.prod ν) = (a k : ℂ) := by
    have hm : ν.real (V k) ≠ 0 := (ENNReal.toReal_pos (hpos k) (hfinV k)).ne'
    have hgk : ∫ y in V k, g y ∂ν = ν.real (V k) := by
      rw [setIntegral_congr_fun (hmeas k) (fun y hy ↦ indicator_of_mem (hV (Nat.zero_le k) hy) _)]
      simp
    rw [setAverage_eq, integral_complex_ofReal, setIntegral_prod_mul, hgk, measureReal_def,
      Measure.prod_prod, ENNReal.toReal_mul, ← measureReal_def]
    simp only [a, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp
  have hlow (k : ℕ) : (k + 1 : ℝ) ≤ a k := by
    have hm : 0 < ν.real (V k) := ENNReal.toReal_pos (hpos k) (hfinV k)
    have hI : (k + 1 : ℝ) * ν.real (V k) ≤ ∫ q in V k, f q ∂ν := by
      have hc : ∫ q in V k, (k + 1 : ℝ) ∂ν = (k + 1 : ℝ) * ν.real (V k) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      rw [← hc]
      refine integral_mono_ae (integrableOn_const (hfinV k)) hf.integrableOn ?_
      rw [EventuallyLE, ae_restrict_iff' (hmeas k)]
      filter_upwards [hFae] with q hq hqV
      have hsum : ((k + 1 : ℕ) : ℝ≥0∞) ≤ F q := by
        calc ((k + 1 : ℕ) : ℝ≥0∞) =
              ∑ j ∈ Finset.range (k + 1), (V j).indicator 1 q := by
              rw [Finset.sum_congr rfl fun j hj ↦ indicator_of_mem
                (hV (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hqV) (1 : Q → ℝ≥0∞)]
              simp
          _ ≤ F q := sum_le_tsum _
      have := ENNReal.toReal_mono hq.ne hsum
      rw [ENNReal.toReal_natCast] at this
      exact_mod_cast this
    rw [show a k = (ν.real (V k))⁻¹ * ∫ q in V k, f q ∂ν from rfl, le_inv_mul_iff₀ hm,
      mul_comm]
    exact hI
  have hl' : Tendsto (fun k ↦ ‖(a k : ℂ)‖) atTop (𝓝 ‖l‖) :=
    (hl.congr fun k ↦ havg k).norm
  refine not_tendsto_nhds_of_tendsto_atTop ?_ _ hl'
  refine tendsto_atTop_mono (fun k ↦ ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact ((by linarith : (k : ℝ) ≤ k + 1)).trans ((hlow k).trans (le_abs_self _))

/-- Paper: Proposition 12.2.2.2(4), p. 509. Use additive `G = ℤ × ℝ`,
`H = ℤ × {0}`, counting times Lebesgue measure, `D = {0} × ℝ`, and
`U n = {0} × (−2⁻ⁿ, 2⁻ⁿ)`. Put `a(t) = 3/4 + sgn(t) min(1, |t|^(1/8))/4`.
The indentation is `a(t)` on the integer slice 0, `1 − a(t)` on slice 1, and
zero on the others. On the quotient use the rank-one kernel
`u(t,s) = g(t) χ(s)`, where `χ(t) = max(0, min(1, 2 − |t|))` and
`g(t) = χ(t) sgn(t) |t|^(−1/4)` for `t ≠ 0`, with `g(0) = 0`.
At the origin the quotient averages are zero by oddness, but the lift averages
over squares of radius `r = 2⁻ⁿ` are `r^(−1/8)/7` and diverge.
The Lean proof uses a simpler counterexample in the same group, at a pair whose points lie
in different integer slices (see the section comment above the helper lemmas). -/
theorem Printed.diagonalIndentationLift_regular_iff_false :
    ¬ Printed.diagonalIndentationLift_regular_iff := by
  intro h
  have := Printed.sec2_discrete_H
  have : BorelSpace (𝔾 ⧸ Printed.sec2H) := ⟨rfl⟩
  have : (Measure.count : Measure Printed.sec2H).IsHaarMeasure :=
    count_isHaarMeasure_of_discreteTopology
  have : (Measure.count : Measure Printed.sec2H).Regular := count_regular_of_discreteTopology
  let μ : Measure 𝔾 := Measure.haar
  obtain ⟨ν, hν⟩ := (weilQuotientMeasure_existsUnique Printed.sec2H Printed.sec2_isClosed_H μ
    Measure.count).exists
  have := hν.1
  have hmk : Continuous (QuotientGroup.mk' Printed.sec2H) := QuotientGroup.continuous_mk
  obtain ⟨u, hu, hdiv⟩ := Printed.sec2_aux ν
    (fun k ↦ QuotientGroup.mk' Printed.sec2H '' Printed.sec2U k)
    (fun m n hmn ↦ image_mono (Printed.sec2_antitone_U hmn))
    (fun k ↦ (Printed.sec2_isOpen_V k).measurableSet)
    (fun k ↦ (Printed.sec2_isOpen_V k).measure_ne_zero ν
      ⟨_, 1, Printed.sec2_one_mem_U k, rfl⟩)
    ((measure_mono (image_mono subset_closure)).trans_lt
      ((Printed.sec2_isCompact_closure_U 0).image hmk).measure_lt_top).ne
    (Printed.sec2_halving ν)
  have key := h Printed.sec2H Printed.sec2_isClosed_H μ ν hν Printed.sec2D Printed.sec2U
    Printed.sec2_isConnected_D (Printed.sec2_situation μ) Printed.sec2b Printed.sec2_isIndentation
    u hu.locallyIntegrable (1, Multiplicative.ofAdd (1, 0))
  obtain ⟨l, hl⟩ := key.1 (Printed.sec2_lift_regular μ u)
  apply hdiv
  refine ⟨l, hl.congr fun k ↦ ?_⟩
  have h1 : ((QuotientGroup.mk (1 : 𝔾) : 𝔾 ⧸ Printed.sec2H),
      (QuotientGroup.mk (Multiplicative.ofAdd ((1 : ℤ), (0 : ℝ))) : 𝔾 ⧸ Printed.sec2H)) =
        1 :=
    Prod.ext ((QuotientGroup.eq_one_iff _).mpr (one_mem _)) ((QuotientGroup.eq_one_iff _).mpr rfl)
  rw [dSequenceAverage, h1, one_smul]


end RiemannMasullo
