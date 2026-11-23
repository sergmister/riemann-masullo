module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5b
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Appendix A.5.3–A.5.4: statements that are false as printed -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Pointwise

/-- Paper: Theorem A.5.3.1, p. 579.
As printed: let `B` be Haar-measurable for a regular Haar measure, with finite enlargement
mass. If each point of `B` centers an allowed translate of a D-sequence, finitely many disjoint
allowed translates centered in `B` have total mass strictly greater than the mass of `B`
divided by the doubling constant.
The enlargement mass uses the outer-measure reading of Remark A.5.3.2. See ERRATA F221 and
`exists_disjoint_dSequence_translates`, which assumes `B` is nonempty. -/
def Printed.exists_disjoint_dSequence_translates : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (U : ℕ → Set G) (C : ℝ),
    IsDSequence μ U → 0 < C →
    (∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k)) →
    ∀ (F : Set (Set G)), F ⊆ {V | ∃ (x : G) (k : ℕ), V = x • U k} →
    ∀ (B : Set G), NullMeasurableSet B μ → μ (B * U 0) < ∞ →
    (∀ x ∈ B, ∃ k, x • U k ∈ F) →
    ∃ (n : ℕ) (x : Fin n → G) (k : Fin n → ℕ),
      (∀ i, x i ∈ B ∧ x i • U (k i) ∈ F) ∧
      Pairwise (fun i j ↦ Disjoint (x i • U (k i)) (x j • U (k j))) ∧
      μ B / ENNReal.ofReal C < ∑ i, μ (U (k i))

/-- Paper: Theorem A.5.3.1, p. 579.
Take the trivial discrete group `Unit` with counting Haar measure, `U k = {1}` for all `k`,
`C = 2`, `F = ∅` and `B = ∅`. The hypotheses hold, and there can be no selected center.
The only possible family is empty, whose mass would have to be strictly above zero. -/
theorem Printed.exists_disjoint_dSequence_translates_false :
    ¬ Printed.exists_disjoint_dSequence_translates := by
  intro h
  let μ : Measure Unit := Measure.haar
  have hD : IsDSequence μ (fun _ ↦ ({1} : Set Unit)) := isDSequence_singleton_one μ
  have hpos : 0 < μ ({1} : Set Unit) := (hD.1 0).2.2.1
  have hfin : μ ({1} : Set Unit) < ∞ := (hD.1 0).2.2.2
  obtain ⟨n, x, k, hmem, -, hlt⟩ :=
    h Unit μ (fun _ ↦ ({1} : Set Unit)) 2 hD two_pos
      (fun _ ↦ by
        simp only [inv_singleton, inv_one, singleton_mul_singleton, mul_one,
          ENNReal.ofReal_ofNat, two_mul]
        exact ENNReal.lt_add_right hfin.ne hpos.ne')
      ∅ (empty_subset _) ∅ MeasurableSet.empty.nullMeasurableSet
      (by simp) (by simp)
  have hsum : (∑ i : Fin n, μ ({1} : Set Unit)) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ False.elim (hmem i).1
  rw [measure_empty, ENNReal.zero_div, hsum] at hlt
  exact lt_irrefl 0 hlt

private theorem multReal_isHaarMeasure :
    (Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)).IsHaarMeasure := by
  have : IsFiniteMeasureOnCompacts
      (Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)) := by
    refine ⟨fun K hK ↦ ?_⟩
    rw [Measure.map_apply MeasurableEquiv.multiplicative.measurable hK.isClosed.measurableSet]
    exact (Homeomorph.ofAdd.isCompact_preimage.mpr hK).measure_lt_top
  have : Measure.IsOpenPosMeasure
      (Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)) := by
    refine ⟨fun U hU hUne ↦ ?_⟩
    rw [Measure.map_apply MeasurableEquiv.multiplicative.measurable hU.measurableSet]
    refine (hU.preimage continuous_ofAdd).measure_ne_zero volume ?_
    obtain ⟨x, hx⟩ := hUne
    exact ⟨Multiplicative.toAdd x, by simpa using hx⟩
  have : Measure.IsMulLeftInvariant
      (Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)) := by
    refine ⟨fun g ↦ ?_⟩
    rw [Measure.map_map (continuous_const_mul g).measurable
      MeasurableEquiv.multiplicative.measurable]
    have hcomp :
        ((fun x : Multiplicative ℝ ↦ g * x) ∘ MeasurableEquiv.multiplicative) =
          (MeasurableEquiv.multiplicative : ℝ → Multiplicative ℝ) ∘
            (fun x : ℝ ↦ Multiplicative.toAdd g + x) := by
      funext x
      exact (ofAdd_add (Multiplicative.toAdd g) x).symm
    rw [hcomp, ← Measure.map_map MeasurableEquiv.multiplicative.measurable
      (measurable_const_add _), Measure.IsAddLeftInvariant.map_add_left_eq_self]
  exact ⟨⟩

private theorem multReal_measure_ofAdd_Ioo (a b : ℝ) :
    Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)
      (Multiplicative.ofAdd '' Ioo a b) = ENNReal.ofReal (b - a) := by
  have hm : MeasurableSet (Multiplicative.ofAdd '' Ioo a b) :=
    MeasurableEquiv.multiplicative.measurableSet_image.mpr measurableSet_Ioo
  rw [Measure.map_apply MeasurableEquiv.multiplicative.measurable hm]
  change volume (Multiplicative.ofAdd ⁻¹' (Multiplicative.ofAdd '' Ioo a b)) = _
  rw [preimage_image_eq _ Multiplicative.ofAdd.injective, Real.volume_Ioo]

private theorem multReal_isDPrimeSequence :
    IsDPrimeSequence (Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ))
      (fun k ↦ Multiplicative.ofAdd '' Ioo (-((1 / 2 : ℝ) ^ k)) ((1 / 2 : ℝ) ^ k)) := by
  let μ : Measure (Multiplicative ℝ) :=
    Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)
  let r : ℕ → ℝ := fun k ↦ (1 / 2 : ℝ) ^ k
  let U : ℕ → Set (Multiplicative ℝ) := fun k ↦ Multiplicative.ofAdd '' Ioo (-r k) (r k)
  have hrpos (k : ℕ) : 0 < r k := by positivity
  have hmeas (k : ℕ) : MeasurableSet (U k) :=
    MeasurableEquiv.multiplicative.measurableSet_image.mpr measurableSet_Ioo
  have hvol (k : ℕ) : μ (U k) = ENNReal.ofReal (2 * r k) := by
    rw [multReal_measure_ofAdd_Ioo]
    congr 1
    ring
  refine ⟨⟨fun k ↦ ?_, fun i j hij ↦ ?_, 3, by norm_num, fun k ↦ ?_⟩, fun W hW ↦ ?_⟩
  · refine ⟨⟨0, ⟨neg_lt_zero.mpr (hrpos k), hrpos k⟩, rfl⟩, (hmeas k).nullMeasurableSet, ?_, ?_⟩
    · rw [hvol k]
      exact ENNReal.ofReal_pos.mpr (by linarith [hrpos k])
    · rw [hvol k]
      exact ENNReal.ofReal_lt_top
  · have hle : r j ≤ r i := pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
    exact image_mono (Ioo_subset_Ioo (neg_le_neg hle) hle)
  · have hone : (1 : Multiplicative ℝ) ∈ (U k)⁻¹ := by
      rw [Set.mem_inv, inv_one]
      exact ⟨0, ⟨neg_lt_zero.mpr (hrpos k), hrpos k⟩, rfl⟩
    have hsub : U k * (U k)⁻¹ ⊆ Multiplicative.ofAdd '' Ioo (-(2 * r k)) (2 * r k) := by
      rintro z ⟨x, ⟨a, ha, rfl⟩, y, hy, rfl⟩
      rw [Set.mem_inv] at hy
      obtain ⟨b, hb, hby⟩ := hy
      have hy' : y = (Multiplicative.ofAdd b)⁻¹ := by rw [← inv_inv y, ← hby]
      dsimp only
      rw [hy', ← ofAdd_neg, ← ofAdd_add]
      refine ⟨a + -b, ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (ENNReal.ofReal_pos.mpr (by linarith [hrpos k])).trans_le
        ((hvol k).symm.le.trans (measure_mono (Set.subset_mul_left _ hone)))
    · calc
        μ (U k * (U k)⁻¹) ≤ μ (Multiplicative.ofAdd '' Ioo (-(2 * r k)) (2 * r k)) :=
          measure_mono hsub
        _ = ENNReal.ofReal (4 * r k) := by
          rw [multReal_measure_ofAdd_Ioo]
          congr 1
          ring
        _ < ENNReal.ofReal (6 * r k) :=
          ENNReal.ofReal_lt_ofReal_iff (by linarith [hrpos k]) |>.mpr (by linarith [hrpos k])
        _ = ENNReal.ofReal 3 * μ (U k) := by
          rw [hvol k, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  · have hW0 : Multiplicative.ofAdd ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
      continuous_ofAdd.continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW0
    have htend : Tendsto r atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds hε)).exists
    refine ⟨k, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have htball : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1, hk], by linarith [ht.2, hk]⟩
    exact hball htball

private theorem multReal_dSequenceAverage_eq (f : Multiplicative ℝ → ℂ) (x r : ℝ) (hr : 0 < r) :
    dSequenceAverage (Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ))
      (Multiplicative.ofAdd '' Ioo (-r) r) f (Multiplicative.ofAdd x) =
      ((2 * r)⁻¹ : ℝ) • ∫ t in (x - r)..(x + r), f (Multiplicative.ofAdd t) := by
  let μ : Measure (Multiplicative ℝ) :=
    Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)
  have htrans :
      Multiplicative.ofAdd x • (Multiplicative.ofAdd '' Ioo (-r) r) =
        Multiplicative.ofAdd '' Ioo (x - r) (x + r) := by
    ext y
    simp only [Set.mem_smul_set, Set.mem_image, smul_eq_mul]
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      rw [← ofAdd_add]
      exact ⟨x + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨Multiplicative.ofAdd (u - x),
        ⟨u - x, ⟨by linarith [hu.1], by linarith [hu.2]⟩, rfl⟩, ?_⟩
      rw [← ofAdd_add]
      congr 1
      ring
  rw [dSequenceAverage, htrans, setAverage_eq]
  have hreal : μ.real (Multiplicative.ofAdd '' Ioo (x - r) (x + r)) = 2 * r := by
    rw [measureReal_def, multReal_measure_ofAdd_Ioo,
      show x + r - (x - r) = 2 * r by ring, ENNReal.toReal_ofReal (by linarith)]
  rw [hreal]
  congr 1
  rw [setIntegral_map_equiv MeasurableEquiv.multiplicative]
  change (∫ t in Multiplicative.ofAdd ⁻¹' (Multiplicative.ofAdd '' Ioo (x - r) (x + r)),
      f (Multiplicative.ofAdd t)) = _
  rw [preimage_image_eq _ Multiplicative.ofAdd.injective, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith)]

private theorem multReal_locallyIntegrable_of_real {f₀ : ℝ → ℝ}
    (hf₀ : LocallyIntegrable f₀ volume) :
    LocallyIntegrable (fun y : Multiplicative ℝ ↦ (f₀ (Multiplicative.toAdd y) : ℂ))
      (Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hK' : IsCompact (Multiplicative.ofAdd ⁻¹' K) :=
    Homeomorph.ofAdd.isCompact_preimage.mpr hK
  have hint : IntegrableOn ((fun y : Multiplicative ℝ ↦ (f₀ (Multiplicative.toAdd y) : ℂ)) ∘
      MeasurableEquiv.multiplicative) (MeasurableEquiv.multiplicative ⁻¹' K) volume :=
    Complex.ofRealCLM.integrable_comp (hf₀.integrableOn_isCompact hK')
  exact MeasurableEquiv.multiplicative.measurableEmbedding.integrableOn_map_iff.mpr hint

private theorem exists_nhds_one_dist_lt_one {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] {g : G → ℂ}
    (huc : @UniformContinuous G ℂ (IsTopologicalGroup.rightUniformSpace G) _ g) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x y : G, y * x⁻¹ ∈ W → dist (g x) (g y) < 1 := by
  let _ : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have hpre : Prod.map g g ⁻¹' {q : ℂ × ℂ | dist q.1 q.2 < 1} ∈
      comap (fun p : G × G ↦ p.2 * p.1⁻¹) (𝓝 (1 : G)) :=
    huc (Metric.dist_mem_uniformity zero_lt_one)
  obtain ⟨W, hW, hWsub⟩ := Filter.mem_comap.mp hpre
  exact ⟨W, hW, fun x y hxy ↦ hWsub (a := (x, y)) hxy⟩

/-- Paper: Theorem A.5.4.1(1), p. 582.
As printed: on every second-countable Hausdorff locally compact abelian group with Haar
measure, every locally integrable complex function has a uniformly continuous average at
each index of any D′-sequence. The averaging operator is `dSequenceAverage`.
See ERRATA F222. -/
def Printed.uniformContinuous_dSequenceAverage : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (U : ℕ → Set G) (f : G → ℂ), IsDPrimeSequence μ U → LocallyIntegrable f μ →
    letI _printedSec5bUniformSpace : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
    ∀ k, UniformContinuous (dSequenceAverage μ (U k) f)

/-- Paper: Theorem A.5.4.1(1), p. 582.
Use the additive real line with Lebesgue measure, `U k = (-2⁻ᵏ, 2⁻ᵏ)` and `f(t) = t²`,
viewed as complex-valued. The average is `x² + 2⁻²ᵏ/3`. For fixed `k`, the points `n` and
`n + 1/n` approach each other while their averages differ by `2 + 1/n²`. -/
theorem Printed.uniformContinuous_dSequenceAverage_false :
    ¬ Printed.uniformContinuous_dSequenceAverage := by
  intro h
  let μ : Measure (Multiplicative ℝ) :=
    Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)
  have : μ.IsHaarMeasure := multReal_isHaarMeasure
  let U : ℕ → Set (Multiplicative ℝ) :=
    fun k ↦ Multiplicative.ofAdd '' Ioo (-((1 / 2 : ℝ) ^ k)) ((1 / 2 : ℝ) ^ k)
  let f : Multiplicative ℝ → ℂ := fun y ↦ (((Multiplicative.toAdd y : ℝ) ^ 2 : ℝ) : ℂ)
  have hf_loc : LocallyIntegrable f μ :=
    multReal_locallyIntegrable_of_real (continuous_pow 2).locallyIntegrable
  have huc := h (Multiplicative ℝ) μ U f multReal_isDPrimeSequence hf_loc 0
  have havg (x : ℝ) :
      dSequenceAverage μ (U 0) f (Multiplicative.ofAdd x) = (((x ^ 2 + 1 / 3 : ℝ)) : ℂ) := by
    have h0 : U 0 = Multiplicative.ofAdd '' Ioo (-1 : ℝ) (1 : ℝ) := by simp [U]
    rw [h0, multReal_dSequenceAverage_eq f x 1 zero_lt_one]
    have hint :
        (∫ t in (x - 1)..(x + 1), f (Multiplicative.ofAdd t)) =
          (((∫ t in (x - 1)..(x + 1), t ^ 2) : ℝ) : ℂ) := by
      simpa only [f, toAdd_ofAdd] using
        (intervalIntegral.integral_ofReal (a := x - 1) (b := x + 1) (f := fun t : ℝ ↦ t ^ 2))
    rw [hint, integral_pow, Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    ring
  obtain ⟨W, hW, hWsub⟩ := exists_nhds_one_dist_lt_one huc
  have hW0 : Multiplicative.ofAdd ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
    continuous_ofAdd.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hW0
  let x : ℝ := 2 / δ
  let y : ℝ := x + δ / 2
  have hmem : Multiplicative.ofAdd y * (Multiplicative.ofAdd x)⁻¹ ∈ W := by
    have hdiff : Multiplicative.ofAdd y * (Multiplicative.ofAdd x)⁻¹ =
        Multiplicative.ofAdd (δ / 2) := by
      rw [← ofAdd_neg, ← ofAdd_add]
      congr 1
      dsimp only [y]
      ring
    rw [hdiff]
    have hδball : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith
    exact hball hδball
  have hdist :
      dist (dSequenceAverage μ (U 0) f (Multiplicative.ofAdd x))
        (dSequenceAverage μ (U 0) f (Multiplicative.ofAdd y)) < 1 :=
    hWsub (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) hmem
  rw [havg x, havg y, Complex.dist_eq] at hdist
  have hnorm :
      ‖(((x ^ 2 + 1 / 3 : ℝ) : ℂ) - ((y ^ 2 + 1 / 3 : ℝ) : ℂ))‖ = 2 + δ ^ 2 / 4 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hcalc : (x ^ 2 + 1 / 3) - (y ^ 2 + 1 / 3) = -(2 + δ ^ 2 / 4) := by
      dsimp only [y, x]
      field_simp [hδ.ne']
      ring
    rw [hcalc, abs_neg, abs_of_pos (by positivity)]
  rw [hnorm] at hdist
  nlinarith [sq_nonneg δ]

/-- Paper: Corollary A.5.4.3, (A.5.4.14)–(A.5.4.15), p. 585.
As printed: for every locally integrable complex function `f`, every compactly supported
continuous function `φ`, and every D′-sequence in a second-countable Hausdorff locally
compact abelian group with Haar measure, at each point where the averages of `f` converge,
the averages of `φ * f` converge to `φ` at that point times the original limit. The averaging
operator is `dSequenceAverage` and the premise describes `dSequenceRegularSet`.
See ERRATA F223. -/
def Printed.tendsto_dSequenceAverage_mul : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (U : ℕ → Set G) (f : G → ℂ), IsDPrimeSequence μ U → LocallyIntegrable f μ →
    ∀ (φ : CompactlySupportedContinuousMap G ℂ) (x : G) (l : ℂ),
      Tendsto (fun k ↦ dSequenceAverage μ (U k) f x) atTop (𝓝 l) →
      Tendsto (fun k ↦ dSequenceAverage μ (U k) (fun y ↦ φ y * f y) x) atTop (𝓝 (φ x * l))

/-- Paper: Corollary A.5.4.3, (A.5.4.14)–(A.5.4.15), p. 585.
Use the additive real line, Lebesgue measure, `U k = (-2⁻ᵏ, 2⁻ᵏ)` and `x = 0`.
For `t ≠ 0` put `f(t) = sgn(t) |t|^(-1/2)` and set `f(0) = 0`. Multiply
`sgn(t) |t|^(1/4)` by the continuous cutoff `max 0 (min 1 (2 - |t|))` to obtain `φ`.
The odd function `f` has zero average for every index. Away from zero on these intervals,
`φ(t) * f(t) = |t|^(-1/4)`, so the averages are `(4/3) * 2^(k/4)` and diverge. -/
theorem Printed.tendsto_dSequenceAverage_mul_false :
    ¬ Printed.tendsto_dSequenceAverage_mul := by
  intro h
  let μ : Measure (Multiplicative ℝ) :=
    Measure.map MeasurableEquiv.multiplicative (volume : Measure ℝ)
  have : μ.IsHaarMeasure := multReal_isHaarMeasure
  let r : ℕ → ℝ := fun k ↦ (1 / 2 : ℝ) ^ k
  let U : ℕ → Set (Multiplicative ℝ) := fun k ↦ Multiplicative.ofAdd '' Ioo (-r k) (r k)
  let f₀ : ℝ → ℝ := fun t ↦ if 0 ≤ t then t ^ (-(1 / 2 : ℝ)) else -((-t) ^ (-(1 / 2 : ℝ)))
  let f : Multiplicative ℝ → ℂ := fun y ↦ (f₀ (Multiplicative.toAdd y) : ℂ)
  have hf₀_odd (t : ℝ) : f₀ (-t) = -f₀ t := by
    by_cases ht : 0 < t
    · have h1 : ¬ 0 ≤ -t := by linarith
      have h2 : 0 ≤ t := ht.le
      simp only [f₀, h1, h2, ↓reduceIte, neg_neg]
    · by_cases ht0 : t = 0
      · subst ht0
        simp [f₀]
      · have hneg : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
        have h1 : 0 ≤ -t := by linarith
        have h2 : ¬ 0 ≤ t := by linarith
        simp only [f₀, h1, h2, ↓reduceIte, neg_neg]
  have hf₀_loc : LocallyIntegrable f₀ volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
    let M : ℝ := max R 0 + 1
    have hM : 0 ≤ M := by positivity
    have hsub : K ⊆ Ioc (-M) M := by
      intro t ht
      have htb : |t| ≤ R := by simpa [Metric.mem_closedBall, Real.dist_eq] using hR ht
      have h1 : -R ≤ t ∧ t ≤ R := abs_le.mp htb
      have h2 : R ≤ max R 0 := le_max_left _ _
      exact ⟨by linarith, by linarith⟩
    have hint_pos : IntervalIntegrable f₀ volume 0 M := by
      refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M)
        (by norm_num : (-1 : ℝ) < -(1 / 2))).congr fun t ht ↦ ?_
      rw [uIoc_of_le hM] at ht
      simp [f₀, ht.1.le]
    have hint_neg : IntervalIntegrable f₀ volume (-M) 0 := by
      have hbase : IntervalIntegrable (fun t : ℝ ↦ -((-t) ^ (-(1 / 2 : ℝ)))) volume (-M) 0 := by
        simpa only [zero_sub, neg_zero, Pi.neg_def] using (IntervalIntegrable.neg
          (IntervalIntegrable.comp_sub_left
            (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M)
              (by norm_num : (-1 : ℝ) < -(1 / 2))) 0)).symm
      refine hbase.congr_ae ?_
      have hne : ∀ᵐ t ∂volume.restrict (uIoc (-M) 0), t ≠ 0 := by
        rw [ae_iff]
        have hzero : volume.restrict (uIoc (-M) 0) ({0} : Set ℝ) = 0 := by
          rw [Measure.restrict_apply (measurableSet_singleton 0)]
          exact measure_mono_null inter_subset_left Real.volume_singleton
        simp [hzero]
      filter_upwards [ae_restrict_mem measurableSet_uIoc, hne] with t ht ht0
      rw [uIoc_of_le (neg_nonpos.mpr hM)] at ht
      have hlt : t < 0 := lt_of_le_of_ne ht.2 ht0
      simp [f₀, not_le.mpr hlt]
    have hint_all : IntervalIntegrable f₀ volume (-M) M := hint_neg.trans hint_pos
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hint_all).mono_set hsub
  have hf_loc : LocallyIntegrable f μ := multReal_locallyIntegrable_of_real hf₀_loc
  have havg_zero (k : ℕ) : dSequenceAverage μ (U k) f 1 = 0 := by
    have hrk : 0 < r k := by positivity
    change dSequenceAverage μ (U k) f (Multiplicative.ofAdd 0) = 0
    rw [multReal_dSequenceAverage_eq f 0 (r k) hrk]
    simp only [zero_sub, zero_add]
    have hint :
        (∫ t in (-r k)..(r k), f (Multiplicative.ofAdd t)) =
          (((∫ t in (-r k)..(r k), f₀ t) : ℝ) : ℂ) := by
      simpa only [f, toAdd_ofAdd] using
        (intervalIntegral.integral_ofReal (a := -r k) (b := r k) (f := f₀))
    have hzero : ∫ t in (-r k)..(r k), f₀ t = 0 := by
      have h1 : ∫ t in (-r k)..(r k), f₀ (-t) = ∫ t in (-r k)..(r k), f₀ t := by
        simp [intervalIntegral.integral_comp_neg]
      have h2 : ∫ t in (-r k)..(r k), f₀ (-t) = -(∫ t in (-r k)..(r k), f₀ t) := by
        simp_rw [hf₀_odd]
        exact intervalIntegral.integral_neg
      linarith
    rw [hint, hzero, Complex.ofReal_zero, smul_zero]
  let g₀ : ℝ → ℝ := fun t ↦ if 0 ≤ t then t ^ (1 / 4 : ℝ) else -((-t) ^ (1 / 4 : ℝ))
  let c₀ : ℝ → ℝ := fun t ↦ max 0 (min 1 (2 - |t|))
  let φ₀ : ℝ → ℝ := fun t ↦ g₀ t * c₀ t
  have hg₀_cont : Continuous g₀ := by
    refine Continuous.if_le
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4))
      (continuous_neg.comp ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).comp
        continuous_neg))
      continuous_const continuous_id ?_
    intro t ht
    rw [← ht]
    simp
  have hc₀_cont : Continuous c₀ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))
  have hφ₀_cont : Continuous φ₀ := hg₀_cont.mul hc₀_cont
  have hφ_cont : Continuous (fun y : Multiplicative ℝ ↦ (φ₀ (Multiplicative.toAdd y) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ₀_cont.comp Homeomorph.ofAdd.symm.continuous)
  have hφ_supp : HasCompactSupport (fun y : Multiplicative ℝ ↦ (φ₀ (Multiplicative.toAdd y) : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.image continuous_ofAdd : IsCompact (Multiplicative.ofAdd '' Icc (-2 : ℝ) 2)) ?_
    intro y hy
    rw [Function.mem_support] at hy
    refine ⟨Multiplicative.toAdd y, ?_, by simp⟩
    by_contra hnot
    have hge : 2 ≤ |Multiplicative.toAdd y| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
      rcases hnot with hlt | hgt
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hc : c₀ (Multiplicative.toAdd y) = 0 := by
      dsimp only [c₀]
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    exact hy (by simp [φ₀, hc])
  let φ : CompactlySupportedContinuousMap (Multiplicative ℝ) ℂ :=
    ⟨⟨fun y ↦ (φ₀ (Multiplicative.toAdd y) : ℂ), hφ_cont⟩, hφ_supp⟩
  have hφ1 : φ 1 = 0 := by
    change (φ₀ 0 : ℂ) = 0
    simp [φ₀, g₀]
  have htend := h (Multiplicative ℝ) μ U f multReal_isDPrimeSequence hf_loc φ 1 0
    (by simp only [havg_zero]; exact tendsto_const_nhds)
  rw [hφ1, zero_mul] at htend
  have htend_re :
      Tendsto (fun k ↦ (dSequenceAverage μ (U k) (fun y ↦ φ y * f y) 1).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp htend
  have hge (k : ℕ) : 1 ≤ (dSequenceAverage μ (U k) (fun y ↦ φ y * f y) 1).re := by
    have hrk : 0 < r k := by positivity
    have hrle : r k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    change 1 ≤ (dSequenceAverage μ (U k) (fun y ↦ φ y * f y) (Multiplicative.ofAdd 0)).re
    rw [multReal_dSequenceAverage_eq (fun y ↦ φ y * f y) 0 (r k) hrk]
    simp only [zero_sub, zero_add]
    have hprod_eq (t : ℝ) :
        φ (Multiplicative.ofAdd t) * f (Multiplicative.ofAdd t) = ((φ₀ t * f₀ t : ℝ) : ℂ) := by
      simp [φ, f]
    simp_rw [hprod_eq]
    rw [intervalIntegral.integral_ofReal, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [inv_mul_eq_div, one_le_div (by linarith), intervalIntegral.integral_of_le (by linarith),
      integral_Ioc_eq_integral_Ioo]
    have hint_prod : IntegrableOn (fun t ↦ φ₀ t * f₀ t) (Ioo (-r k) (r k)) volume := by
      have hloc_prod : LocallyIntegrable (fun t ↦ φ₀ t * f₀ t) volume := by
        simpa only [smul_eq_mul] using hf₀_loc.continuous_smul hφ₀_cont
      exact (hloc_prod.integrableOn_isCompact isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hint_one : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioo (-r k) (r k)) volume :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hmono : ∫ _ in Ioo (-r k) (r k), (1 : ℝ) ≤ ∫ t in Ioo (-r k) (r k), φ₀ t * f₀ t := by
      refine integral_mono_ae hint_one hint_prod ?_
      have hne : ∀ᵐ t ∂volume.restrict (Ioo (-r k) (r k)), t ≠ 0 := by
        rw [ae_iff]
        have hzero : volume.restrict (Ioo (-r k) (r k)) ({0} : Set ℝ) = 0 := by
          rw [Measure.restrict_apply (measurableSet_singleton 0)]
          exact measure_mono_null inter_subset_left Real.volume_singleton
        simp [hzero]
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hne] with t ht ht0
      have habs : |t| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1, hrle], by linarith [ht.2, hrle]⟩
      have hc1 : c₀ t = 1 := by
        dsimp only [c₀]
        rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      have hpf : φ₀ t * f₀ t = |t| ^ (-(1 / 4 : ℝ)) := by
        dsimp only [φ₀]
        rw [hc1, mul_one]
        rcases lt_or_gt_of_ne ht0 with hlt | hgt
        · have h1 : ¬ 0 ≤ t := not_le.mpr hlt
          simp only [g₀, f₀, h1, ↓reduceIte, neg_mul_neg, abs_of_neg hlt]
          rw [← Real.rpow_add (neg_pos.mpr hlt)]
          norm_num
        · have h1 : 0 ≤ t := hgt.le
          simp only [g₀, f₀, h1, ↓reduceIte, abs_of_pos hgt]
          rw [← Real.rpow_add hgt]
          norm_num
      rw [hpf]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.mpr ht0) habs (by norm_num)
    have hone_int : ∫ _ in Ioo (-r k) (r k), (1 : ℝ) = 2 * r k := by
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioo,
        show r k - -r k = 2 * r k by ring, ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hle : (1 : ℝ) ≤ 0 := ge_of_tendsto' htend_re hge
  linarith

end RiemannMasullo
