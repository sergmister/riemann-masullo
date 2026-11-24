module

public import RiemannMasullo.Research.StripNuclearity.NormalizedDivisorialShells
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # A principal fundamental domain inside the S-local idèles

When the S-integer Picard group is trivial, every idèle class has a
representative which is a unit at all finite places outside S. A countable
open-chart selection gives a Borel fundamental domain of such representatives.
Choosing chart boundaries null for the pushforward of Tamagawa measure makes
the domain frontier null. The shell cutoffs of §11.3 are identically one
on this domain. The chart selection and the restriction argument are original.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField.AdeleRing Pointwise Topology

namespace RiemannMasullo

private theorem exists_null_frontier_transversal_from_charts {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : IsLocalHomeomorph q) (μ : Measure X) (U : ℕ → Set X)
    (ho : ∀ n, IsOpen (U n)) (hi : ∀ n, InjOn q (U n))
    (hcover : ∀ y, ∃ n, y ∈ q '' U n)
    (hsrc : ∀ n, μ (frontier (U n)) = 0) (hsat : ∀ n, μ (frontier (q ⁻¹' (q '' U n))) = 0) :
    ∃ D : Set X, MeasurableSet D ∧ U 0 ⊆ D ∧ D ⊆ (⋃ n, U n) ∧
      Bijective (fun x : D ↦ q x.val) ∧ μ (frontier D) = 0 := by
  classical
  let image (n : ℕ) := q '' U n
  let earlier (n : ℕ) := ⋃ j ∈ Finset.range n, q ⁻¹' image j
  let piece (n : ℕ) := U n ∩ (earlier n)ᶜ
  have hB (n : ℕ) : IsOpen (earlier n) := isOpen_iUnion fun j ↦
    isOpen_iUnion fun _ ↦ (hq.isOpenMap _ (ho j)).preimage hq.continuous
  refine ⟨⋃ n, piece n, MeasurableSet.iUnion (fun n ↦ (ho n).measurableSet.diff (hB n).measurableSet),
    fun x hx ↦ mem_iUnion.mpr ⟨0, hx, by simp [earlier]⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact iUnion_mono fun n ↦ sdiff_subset
  · rintro ⟨x,hx⟩ ⟨y,hy⟩ (hxy : q x = q y)
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hy
    have hmn : m = n := by
      rcases lt_trichotomy m n with h | h | h
      · have hy : q y ∈ image m := hxy ▸ mem_image_of_mem q hm.1
        exact (hn.2 (mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr h, hy⟩)).elim
      · exact h
      · have hx : q x ∈ image n := hxy.symm ▸ mem_image_of_mem q hn.1
        exact (hm.2 (mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr h, hx⟩)).elim
    subst n
    exact Subtype.ext (hi m hm.1 hn.1 hxy)
  · intro y
    let n := Nat.find (hcover y)
    obtain ⟨x,hx,hxy⟩ := Nat.find_spec (hcover y)
    have hfirst : x ∉ earlier n := by
      intro h
      obtain ⟨j,hj,hqj⟩ := mem_iUnion₂.mp h
      have hy : y ∈ image j := hxy ▸ (show q x ∈ image j from hqj)
      exact (Nat.not_lt_of_ge (Nat.find_min' (hcover y) hy)) (Finset.mem_range.mp hj)
    exact ⟨⟨x, mem_iUnion.mpr ⟨n,hx,hfirst⟩⟩,hxy⟩
  · have hP (n : ℕ) : μ (frontier (piece n)) = 0 := by
      have hBnull : μ (frontier (earlier n)) = 0 := measure_mono_null
        ((Finset.range n).frontier_biUnion_subset (fun j ↦ q ⁻¹' image j))
        (measure_iUnion_null fun j ↦ measure_iUnion_null fun _ ↦ hsat j)
      apply measure_mono_null (frontier_inter_subset (U n) (earlier n)ᶜ)
      rw [frontier_compl]
      exact measure_union_null (measure_mono_null inter_subset_left (hsrc n))
        (measure_mono_null inter_subset_right hBnull)
    -- Over any one open chart image, only it and the earlier choices can contribute.
    have hfin : LocallyFinite piece := by
      intro x
      obtain ⟨j,hj⟩ := hcover (q x)
      refine ⟨q ⁻¹' image j, ((hq.isOpenMap _ (ho j)).preimage hq.continuous).mem_nhds hj,
        (finite_le_nat j).subset ?_⟩
      rintro n ⟨z,hz,hzj⟩
      change n ≤ j
      by_contra! hn
      exact hz.2 (mem_iUnion₂.mpr ⟨j,Finset.mem_range.mpr hn,hzj⟩)
    refine measure_mono_null ?_ (measure_iUnion_null hP)
    intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hfin.closure_iUnion ▸ hx.1)
    exact mem_iUnion.mpr ⟨n,hn,fun h ↦ hx.2 (interior_mono (subset_iUnion piece n) h)⟩

/-- A local homeomorphism admits a Borel transversal in any open set meeting
every fiber, extending a prescribed open subset on which it is injective. -/
theorem exists_borel_transversal_in_open {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [SecondCountableTopology Y]
    {q : X → Y} (hq : IsLocalHomeomorph q) {A E : Set X}
    (hA : IsOpen A) (hcover : SurjOn q A univ)
    (hE : IsOpen E) (hEA : E ⊆ A) (hEi : InjOn q E) :
    ∃ D : Set X, MeasurableSet D ∧ E ⊆ D ∧ D ⊆ A ∧ Bijective (fun x : D ↦ q x.val) := by
  classical
  let Chart := {s : Set X // IsOpen s ∧ s ⊆ A ∧ InjOn q s}
  let : Nonempty Chart := ⟨⟨E, hE, hEA, hEi⟩⟩
  obtain ⟨V, hV⟩ := isLindelof_univ.indexed_countable_subcover
    (fun c : Chart ↦ q '' c.val) (fun c ↦ hq.isOpenMap _ c.property.1) (by
      intro y _
      obtain ⟨x, hx, hxy⟩ := hcover (mem_univ y)
      obtain ⟨s, hs, hxs, hi⟩ := hq.isLocallyInjective x
      refine mem_iUnion.mpr ⟨⟨s ∩ A, hs.inter hA, inter_subset_right, hi.mono inter_subset_left⟩, ?_⟩
      exact ⟨x, ⟨hxs, hx⟩, hxy⟩)
  let chart : ℕ → Chart
    | 0 => ⟨E, hE, hEA, hEi⟩
    | n+1 => V n
  have hcov (y : Y) : ∃ n, y ∈ q '' (chart n).val := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hV (mem_univ y))
    exact ⟨j+1,hj⟩
  obtain ⟨D,hm,h₀,hDU,hbij,-⟩ := exists_null_frontier_transversal_from_charts hq (0 : Measure X)
    (fun n ↦ (chart n).val) (fun n ↦ (chart n).property.1) (fun n ↦ (chart n).property.2.2)
    hcov (fun _ ↦ by simp) (fun _ ↦ by simp)
  exact ⟨D,hm,h₀,hDU.trans (iUnion_subset fun n ↦ (chart n).property.2.1),hbij⟩

private theorem exists_null_frontier_injective_chart {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [SFinite μ] {q : X → Y} (hq : IsLocalHomeomorph q)
    {A : Set X} (hA : IsOpen A) {x : X} (hx : x ∈ A) :
    ∃ s : Set X, IsOpen s ∧ x ∈ s ∧ s ⊆ A ∧ InjOn q s ∧ μ (frontier s) = 0 ∧
      μ (frontier (q ⁻¹' (q '' s))) = 0 := by
  let : PseudoMetricSpace Y := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Y
  obtain ⟨U, hU, hUx, hUi⟩ := hq.isLocallyInjective x
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset (hU.inter hA) ⟨hUx, hx⟩
  have hW := (hq.isOpenMap _ isOpen_interior).mem_nhds (mem_image_of_mem q hxK)
  obtain ⟨b, hb, hball⟩ := Metric.mem_nhds_iff.mp hW
  -- Taking the boundary with respect to the pushforward directly controls its full preimage.
  obtain ⟨r, hr, hnull⟩ := exists_null_frontier_thickening (μ.map q) ({q x} : Set Y) hb
  rw [Metric.thickening_singleton] at hnull
  let T := Metric.ball (q x) r
  have hT : IsOpen T := Metric.isOpen_ball
  have hTK : T ⊆ q '' interior K := (Metric.ball_subset_ball hr.2.le).trans hball
  have hpre : μ (q ⁻¹' frontier T) = 0 := by
    rwa [Measure.map_apply hq.continuous.measurable isClosed_frontier.measurableSet] at hnull
  let s := interior K ∩ q ⁻¹' T
  have hs : IsOpen s := isOpen_interior.inter (hT.preimage hq.continuous)
  have hsK : s ⊆ K := inter_subset_left.trans interior_subset
  have him : q '' s = T := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hTK hy
      exact ⟨z, ⟨hz,hy⟩,rfl⟩
  refine ⟨s, hs, ⟨hxK, Metric.mem_ball_self hr.1⟩, hsK.trans (hKU.trans inter_subset_right),
    hUi.mono (hsK.trans (hKU.trans inter_subset_left)), ?_, ?_⟩
  · refine measure_mono_null (fun z hz ↦ ?_) hpre
    have hzK : z ∈ K := (closure_minimal hsK hK.isClosed) hz.1
    have hzT : q z ∈ closure T := (closure_minimal
      (show s ⊆ q ⁻¹' closure T from fun _ ht ↦ subset_closure ht.2)
      (isClosed_closure.preimage hq.continuous)) hz.1
    refine ⟨hzT, fun hz' ↦ hz.2 ?_⟩
    have hzt := interior_subset hz'
    obtain ⟨w, hw, hqw⟩ := hTK hzt
    -- Compact containment keeps the boundary inside the same injective chart.
    have hwz : w = z := hUi (hKU (interior_subset hw)).1 (hKU hzK).1 hqw
    rw [hs.interior_eq]
    exact ⟨hwz ▸ hw, hzt⟩
  · rw [him, ← hq.isOpenMap.preimage_frontier_eq_frontier_preimage hq.continuous]
    exact hpre

/-- Inside an open set meeting each fiber of a local homeomorphism, one can
choose a Borel transversal containing a neighborhood of a prescribed point
and having null frontier for a given s-finite measure. -/
theorem exists_borel_null_frontier_transversal_in_open {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] (μ : Measure X) [SFinite μ] {q : X → Y} (hq : IsLocalHomeomorph q)
    {A : Set X} (hA : IsOpen A) (hcover : SurjOn q A univ) {x : X} (hx : x ∈ A) :
    ∃ D : Set X, MeasurableSet D ∧ x ∈ interior D ∧ D ⊆ A ∧
      Bijective (fun d : D ↦ q d.val) ∧ μ (frontier D) = 0 := by
  classical
  let Chart := {s : Set X // IsOpen s ∧ s ⊆ A ∧ InjOn q s ∧ μ (frontier s) = 0 ∧
    μ (frontier (q ⁻¹' (q '' s))) = 0}
  have hchart (z : X) (hz : z ∈ A) : ∃ c : Chart, z ∈ c.val := by
    obtain ⟨U,ho,hm,hs,hi,hf,hp⟩ := exists_null_frontier_injective_chart μ hq hA hz
    exact ⟨⟨U,ho,hs,hi,hf,hp⟩,hm⟩
  obtain ⟨c₀,h₀⟩ := hchart x hx
  let : Nonempty Chart := ⟨c₀⟩
  obtain ⟨V, hV⟩ := isLindelof_univ.indexed_countable_subcover (fun c : Chart ↦ q '' c.val)
    (fun c ↦ hq.isOpenMap _ c.property.1) (by
      intro y _
      obtain ⟨z,hz,rfl⟩ := hcover (mem_univ y)
      obtain ⟨c,hc⟩ := hchart z hz
      exact mem_iUnion.mpr ⟨c,mem_image_of_mem q hc⟩)
  let charts : ℕ → Chart
    | 0 => c₀
    | n+1 => V n
  have hcov (y : Y) : ∃ n, y ∈ q '' (charts n).val := by
    obtain ⟨i,hm⟩ := mem_iUnion.mp (hV (mem_univ y))
    exact ⟨i+1,hm⟩
  obtain ⟨D,hDm,hD₀,hD,hbij,hfront⟩ := exists_null_frontier_transversal_from_charts hq μ
    (fun n ↦ (charts n).val) (fun n ↦ (charts n).property.1) (fun n ↦ (charts n).property.2.2.1)
    hcov (fun n ↦ (charts n).property.2.2.2.1) (fun n ↦ (charts n).property.2.2.2.2)
  exact ⟨D,hDm,mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (c₀.property.1.mem_nhds h₀) hD₀),
    hD.trans (iUnion_subset fun n ↦ (charts n).property.2.1),hbij,hfront⟩

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "P𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "q𝔽" => QuotientGroup.mk' P𝔽

attribute [local instance] instIdeleMeasurableSpaceSec1a instIdeleClassMeasurableSpaceSec1
  instIdeleClassBorelSpaceSec1 instIdeleClassSecondCountableSec1 instIdeleClassT2Sec1
  instIdeleClassLocallyCompactSec1 idelicShellBorel idelicShellT2
  idelicShellLocallyCompact idelicShellSecondCountable idelicShellDiscrete idelicShellCountable idelicShellHaar

/-- Paper: Remark A.2.4.5, p. 555, and §11.3.2, p. 495. Triviality of the
S-integer Picard group gives a unit-outside-S representative of every idèle class. -/
theorem sLocalDivisorialStratum_surjOn_ideleClass (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    SurjOn q𝔽 (sLocalDivisorialStratum F S) univ := by
  let := hPic
  obtain ⟨e, he, -⟩ := sIdeleClassGroup_equiv_of_classNumberOne F S
  intro z _
  obtain ⟨c, rfl⟩ := e.surjective z
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨integralIdeleInsertion F S u, ?_, (he u).symm⟩
  rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
  exact mem_range_self u

local notation "μ𝔽" => multiplicativeTamagawaMeasure F

private theorem adapted_unique_principal_translate {D : Set I𝔽}
    (hDb : Bijective (fun x : D ↦ q𝔽 x.val)) (x : I𝔽) : ∃! h : P𝔽, h • x ∈ D := by
  obtain ⟨y, hy⟩ := hDb.surjective (q𝔽 x)
  have hmem : y.val*x⁻¹ ∈ P𝔽 := (QuotientGroup.eq_one_iff _).mp
    (by change q𝔽 (y.val*x⁻¹) = 1; rw [map_mul, map_inv, show q𝔽 y.val = q𝔽 x from hy, mul_inv_cancel])
  let h : P𝔽 := ⟨y.val*x⁻¹,hmem⟩
  have he : h • x = y.val := by change y.val*x⁻¹*x = y.val; group
  have hrep : h • x ∈ D := he.symm ▸ y.property
  refine ⟨h,hrep,fun h' hh' ↦ ?_⟩
  have hsame : (⟨h' • x,hh'⟩ : D) = y := hDb.injective (by
    change q𝔽 ((h' : I𝔽)*x) = q𝔽 y.val
    rw [map_mul, show q𝔽 (h' : I𝔽) = 1 from (QuotientGroup.eq_one_iff _).mpr h'.property,
      one_mul, show q𝔽 y.val = q𝔽 x from hy])
  exact Subtype.ext (mul_right_cancel ((congrArg Subtype.val hsame).trans he.symm))

private theorem adapted_isIndentationFundamentalDomain {D : Set I𝔽}
    (h1 : (1 : I𝔽) ∈ interior D) (hDb : Bijective (fun x : D ↦ q𝔽 x.val))
    (hfront : μ𝔽 (frontier D) = 0) : IsIndentationFundamentalDomain P𝔽 μ𝔽 D := by
  have htr := adapted_unique_principal_translate hDb
  refine ⟨⟨1,h1⟩,htr,fun h hne ↦ ?_⟩
  have hsub : closure D ∩ h • closure D ⊆ frontier D ∪ (h : I𝔽) • frontier D := by
    rintro x ⟨hx,ht⟩
    obtain ⟨y,hycl,hxy⟩ := Set.mem_smul_set.mp ht
    by_cases hd : x ∈ D
    · right
      refine Set.mem_smul_set.mpr ⟨y,⟨hycl,fun hy ↦ ?_⟩,hxy⟩
      exact hne ((htr y).unique (show h • y ∈ D from hxy.symm ▸ hd)
        (show (1 : P𝔽) • y ∈ D by simpa only [one_smul] using interior_subset hy))
    · exact Or.inl ⟨hx,fun hi ↦ hd (interior_subset hi)⟩
  exact measure_mono_null hsub (measure_union_null hfront (measure_smul_null hfront (h : I𝔽)))

/-- Paper: Remark 12.2.1.4, p. 507, and Situation 12.2.2.1, p. 508. With
trivial S-integer Picard group there is an S-integral Borel principal domain
containing a neighborhood of one, with Tamagawa-null frontier and null
overlap between its closure and every distinct principal translate.
Deviation: The formalized §12.2 uses the repaired domain condition, with
the overlap measured upstairs and connectedness omitted. -/
theorem exists_ideleClass_indentationFundamentalDomain_in_sLocalDivisorialStratum (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    ∃ D : Set I𝔽, MeasurableSet D ∧ (1 : I𝔽) ∈ interior D ∧ D ⊆ sLocalDivisorialStratum F S ∧
      Bijective (fun x : D ↦ q𝔽 x.val) ∧ μ𝔽 (frontier D) = 0 ∧ IsIndentationFundamentalDomain P𝔽 μ𝔽 D := by
  have hq : IsLocalHomeomorph (q𝔽 : I𝔽 → C𝔽) :=
    ((P𝔽).isQuotientCoveringMap ((ideleGroup_quotient.{_,0} F).2.2.1)).isCoveringMap.isLocalHomeomorph
  have hA : IsOpen (sLocalDivisorialStratum F S) := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
    exact (integralIdeleInsertion_isOpenEmbedding F S).isOpen_range
  have hOne : (1 : I𝔽) ∈ sLocalDivisorialStratum F S := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
    exact ⟨1,map_one _⟩
  obtain ⟨D,hm,h1,hDA,hbij,hfront⟩ := exists_borel_null_frontier_transversal_in_open μ𝔽 hq hA
    (sLocalDivisorialStratum_surjOn_ideleClass S hPic) hOne
  exact ⟨D,hm,h1,hDA,hbij,hfront,adapted_isIndentationFundamentalDomain h1 hbij hfront⟩

/-- A tail of any symmetric relatively compact open D′ sequence belongs to
the actual diagonal indentation situation for an adapted domain. -/
theorem exists_sLocalDivisorial_diagonalIndentationSituation (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) {U : ℕ → Set I𝔽}
    (hU : IsDPrimeSequence μ𝔽 U)
    (hreg : ∀ n, IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n) :
    ∃ (D : Set I𝔽) (N : ℕ), MeasurableSet D ∧ D ⊆ sLocalDivisorialStratum F S ∧
      Bijective (fun x : D ↦ q𝔽 x.val) ∧ IsDiagonalIndentationSituation P𝔽 μ𝔽 D (fun k ↦ U (N+k)) := by
  obtain ⟨D,hm,h1,hDA,hbij,-,hFD⟩ :=
    exists_ideleClass_indentationFundamentalDomain_in_sLocalDivisorialStratum S hPic
  obtain ⟨N,hN⟩ := hU.2 D (mem_interior_iff_mem_nhds.mp h1)
  obtain ⟨hbase,hmono,C,hC,hd⟩ := hU.1
  refine ⟨D,N,hm,hDA,hbij,hFD,⟨⟨fun k ↦ hbase (N+k), fun _ _ h ↦ hmono (Nat.add_le_add_left h N),
    C,hC,fun k ↦ hd (N+k)⟩, ?_⟩,fun k ↦ ⟨(hmono (Nat.le_add_right N k)).trans hN,hreg (N+k)⟩⟩
  intro W hW
  obtain ⟨k,hk⟩ := hU.2 W hW
  exact ⟨k,(hmono (Nat.le_add_left k N)).trans hk⟩

/-- Paper: §11.3, pp. 491–495, and §12.2, pp. 507–508. Under the S-class-number
hypothesis one can choose a Borel principal fundamental domain containing a
neighborhood of one and lying entirely in the S-local stratum.
Deviation: The transversal is chosen to suit the shell exhaustion. -/
theorem exists_borel_ideleClass_domain_in_sLocalDivisorialStratum (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    ∃ D : Set I𝔽, MeasurableSet D ∧ (1 : I𝔽) ∈ interior D ∧
      D ⊆ sLocalDivisorialStratum F S ∧ Bijective (fun x : D ↦ q𝔽 x.val) := by
  obtain ⟨D,hm,h1,hDA,hbij,-,-⟩ :=
    exists_ideleClass_indentationFundamentalDomain_in_sLocalDivisorialStratum S hPic
  exact ⟨D,hm,h1,hDA,hbij⟩

/-- Paper: (11.3.1.4), p. 494. Every finite shell cutoff in the saturated
primary exhaustion is one on a unit-outside-S representative. -/
theorem primaryDivisorialIndicator_eq_one_on_sLocalDivisorialStratum (S : Finset V)
    (hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    {x : I𝔽} (hx : x ∈ sLocalDivisorialStratum F S) (k : ℕ) :
    divisorialIndicator (primaryDivisorialPlaces F S k) x = 1 := by
  have hall := (iInter_primaryDivisorialStratum S hS).symm ▸ hx
  rw [divisorialIndicator_eq_indicator]
  exact Set.indicator_of_mem (mem_iInter.mp hall k) _

/-- Paper: (11.3.1.4), p. 494. Every shell difference of an arbitrary kernel
vanishes when its second coordinate lies in the S-local representative domain. -/
theorem divisorialKernelDifference_eq_zero_on_sLocalDivisorialStratum (S : Finset V)
    (hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    (K : I𝔽 × I𝔽 → ℂ) {xy : I𝔽 × I𝔽} (hxy : xy.2 ∈ sLocalDivisorialStratum F S) (k : ℕ) :
    divisorialKernelDifference S k K xy = 0 := by
  simp only [divisorialKernelDifference, primaryDivisorialIndicator_eq_one_on_sLocalDivisorialStratum S hS hxy,
    sub_self, zero_mul]

local notation "ν𝔽" => ideleClassTamagawaMeasure F
local notation "countP" => (Measure.count : Measure P𝔽)

/-- Paper: (11.3.1.4), p. 494. On an adapted domain each integrated skew
shell vanishes for every lifted kernel, without any regularity assumption. -/
theorem integral_adapted_idelic_shell_eq_zero (S : Finset V)
    (hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    {D : Set I𝔽} (hD : MeasurableSet D) (hDA : D ⊆ sLocalDivisorialStratum F S)
    (K : I𝔽 × I𝔽 → ℂ) (k : ℕ) :
    (∫ x in D, ∫ h : P𝔽, divisorialKernelDifference S k K (((h : I𝔽)⁻¹ * x), x) ∂countP ∂μ𝔽) = 0 := by
  calc
    _ = ∫ _x in D, (0 : ℂ) ∂μ𝔽 := by
      refine setIntegral_congr_fun hD fun x hx ↦ ?_
      have hz (h : P𝔽) := divisorialKernelDifference_eq_zero_on_sLocalDivisorialStratum S hS K
        (xy := (((h : I𝔽)⁻¹ * x),x)) (hDA hx) k
      simp only [hz, integral_zero]
    _ = 0 := integral_zero _ _

/-- Paper: (12.2.2.3)–(12.2.2.4), p. 508, and the restriction in §12.3,
p. 514. On the adapted Borel representatives the S-restricted, normalized
skew integral is exactly the Tamagawa integral of the original quotient
diagonal. This holds for any kernel with integrable quotient diagonal.
Deviation: The left-hand kernel is the normalized global lift on this
chosen domain. The additive S-local cutoff operator requires its own
comparison. -/
theorem integral_adapted_sLocal_normalized_skew_eq_quotient_diagonal (S : Finset V)
    {D : Set I𝔽} (hD : MeasurableSet D) (hDA : D ⊆ sLocalDivisorialStratum F S)
    (hDb : Bijective (fun x : D ↦ q𝔽 x.val)) {b : I𝔽 → ℝ} (hb : IsIndentation P𝔽 countP b)
    (u : C𝔽 × C𝔽 → ℂ) (hi : Integrable (fun x ↦ u (x,x)) ν𝔽) :
    (∫ x in D, ∫ h : P𝔽, (sLocalDivisorialStratum F S).indicator
      (fun _ ↦ diagonalIndentationLift P𝔽 countP b u (((h : I𝔽)⁻¹ * x), x)) x ∂countP ∂μ𝔽) =
      ∫ x, u (x,x) ∂ν𝔽 := by
  calc
    _ = ∫ x in D, u (q𝔽 x, q𝔽 x) ∂μ𝔽 := by
      refine setIntegral_congr_fun hD fun x hx ↦ ?_
      simp only [Set.indicator_of_mem (hDA hx)]
      exact integral_normalized_idelic_skew_fiber hb u x
    _ = _ := (weilFundamentalDomain_integral P𝔽 (ideleGroup_quotient.{_,0} F).2.1 μ𝔽
      hD hDb ν𝔽 (ideleClassTamagawaMeasure_isWeil F) hi).symm

local notation "smooth(" U "," u ")" => dSequenceKernelSmoothening ν𝔽 (fun n ↦ q𝔽 '' U n) u
local notation "lift(" b "," U "," u "," z ")" =>
  diagonalIndentationLift P𝔽 countP b smooth(U,u) ((((z).2 : I𝔽)⁻¹ * (z).1), (z).1)

/-- Paper: (12.2.2.3)–(12.2.2.4), p. 508, and §12.3, p. 514. For the
adapted indentation situation the normalized skew lift is integrable on
the actual product measure. Its integral with the S-local mask equals the
full smoothened quotient diagonal, under the diagonal regularity and
integrability assumptions of §12.2.
Deviation: The mask is evaluated on representatives in the chosen domain.
Identification with the kernel of the additive local cutoff is a further step. -/
theorem integral_adapted_sLocal_smoothened_skew_eq_quotient_diagonal (S : Finset V)
    {D : Set I𝔽} (hDm : MeasurableSet D) (hDA : D ⊆ sLocalDivisorialStratum F S)
    (hDb : Bijective (fun x : D ↦ q𝔽 x.val)) {U : ℕ → Set I𝔽}
    (hD : IsDiagonalIndentationSituation P𝔽 μ𝔽 D U)
    {b : I𝔽 → ℝ} (hb : IsIndentation P𝔽 countP b) {u : C𝔽 × C𝔽 → ℂ}
    (hu : LocallyIntegrable u ((ν𝔽).prod ν𝔽))
    (hreg : ∀ᵐ x ∂ν𝔽, (x,x) ∈ dSequenceRegularSet ((ν𝔽).prod ν𝔽)
      (fun n ↦ (q𝔽 '' U n) ×ˢ (q𝔽 '' U n)) u)
    (hi : Integrable (fun x ↦ smooth(U,u) (x,x)) ν𝔽) :
    let m := ((μ𝔽).restrict D).prod countP
    let A := (Prod.fst : I𝔽 × P𝔽 → I𝔽) ⁻¹' sLocalDivisorialStratum F S
    Integrable (fun z ↦ lift(b,U,u,z)) m ∧
      (∫ z in A, lift(b,U,u,z) ∂m) = ∫ x, smooth(U,u) (x,x) ∂ν𝔽 := by
  intro m A
  have hclosed : IsClosed (P𝔽 : Set I𝔽) := (ideleGroup_quotient.{_,0} F).2.1
  have hskew := integrable_diagonalIndentationLift_left P𝔽 hclosed (ideleClassTamagawaMeasure_isWeil F)
    hD hb hu hreg hi
  have hA : MeasurableSet (sLocalDivisorialStratum F S) := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
    exact (integralIdeleInsertion_isOpenEmbedding F S).isOpen_range.measurableSet
  have hr := integral_normalized_idelic_skew_restrict hb smooth(U,u) (sLocalDivisorialStratum F S)
    ((μ𝔽).restrict D) hskew
  rw [Measure.restrict_restrict hA, inter_eq_right.mpr hDA] at hr
  exact ⟨hskew,hr.trans (weilFundamentalDomain_integral P𝔽 hclosed μ𝔽 hDm hDb
    ν𝔽 (ideleClassTamagawaMeasure_isWeil F) hi).symm⟩

end RiemannMasullo
