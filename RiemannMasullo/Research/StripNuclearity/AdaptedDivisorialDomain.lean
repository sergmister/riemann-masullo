module

public import RiemannMasullo.Research.StripNuclearity.NormalizedDivisorialShells

/-! # A principal fundamental domain inside the S-local idèles

When the S-integer Picard group is trivial, every idèle class has a
representative which is a unit at all finite places outside S. A countable
open-chart selection gives a Borel fundamental domain of such representatives.
The shell cutoffs of §11.3 are identically one on this domain.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField.AdeleRing Pointwise Topology

namespace RiemannMasullo

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
  let Q (n : ℕ) := q '' (chart n).val
  let D := ⋃ n, (chart n).val ∩ q ⁻¹' disjointed Q n
  have hpre (n : ℕ) : MeasurableSet (q ⁻¹' Q n) :=
    ((hq.isOpenMap _ (chart n).property.1).preimage hq.continuous).measurableSet
  refine ⟨D, MeasurableSet.iUnion fun n ↦ (chart n).property.1.measurableSet.inter ?_, ?_, ?_, ?_⟩
  · simp only [disjointed_eq_inter_compl, preimage_inter, preimage_iInter, preimage_compl]
    exact (hpre n).inter (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ (hpre j).compl)
  · intro x hx
    refine mem_iUnion.mpr ⟨0, hx, ?_⟩
    change q x ∈ disjointed Q 0
    rw [show disjointed Q 0 = Q 0 from disjointed_bot Q]
    exact mem_image_of_mem q hx
  · intro x hx
    obtain ⟨n, hn, -⟩ := mem_iUnion.mp hx
    exact (chart n).property.2.1 hn
  · constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ (he : q x = q y)
      obtain ⟨i, hix, hqx⟩ := mem_iUnion.mp hx
      obtain ⟨j, hjy, hqy⟩ := mem_iUnion.mp hy
      have hij : i = j := by
        by_contra hn
        exact (disjoint_left.mp (disjoint_disjointed Q hn)) hqx (he.symm ▸ hqy)
      subst j
      exact Subtype.ext ((chart i).property.2.2 hix hjy he)
    · intro y
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hV (mem_univ y))
      have hy : y ∈ ⋃ n, disjointed Q n := by
        rw [iUnion_disjointed]
        exact mem_iUnion.mpr ⟨i+1, hi⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      obtain ⟨x, hx, hxy⟩ := disjointed_subset Q j hj
      have hchosen : q x ∈ disjointed Q j := hxy.symm ▸ hj
      exact ⟨⟨x, mem_iUnion.mpr ⟨j, hx, hchosen⟩⟩, hxy⟩

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "P𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "q𝔽" => QuotientGroup.mk' P𝔽

attribute [local instance] instIdeleMeasurableSpaceSec1a instIdeleClassMeasurableSpaceSec1
  instIdeleClassBorelSpaceSec1 instIdeleClassSecondCountableSec1 idelicShellBorel idelicShellT2
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

/-- Paper: §11.3, pp. 491–495, and §12.2, pp. 507–508. Under the S-class-number
hypothesis one can choose a Borel principal fundamental domain containing a
neighborhood of one and lying entirely in the S-local stratum.
Deviation: The transversal is chosen to suit the shell exhaustion. -/
theorem exists_borel_ideleClass_domain_in_sLocalDivisorialStratum (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) :
    ∃ D : Set I𝔽, MeasurableSet D ∧ (1 : I𝔽) ∈ interior D ∧
      D ⊆ sLocalDivisorialStratum F S ∧ Bijective (fun x : D ↦ q𝔽 x.val) := by
  have hq : IsLocalHomeomorph (q𝔽 : I𝔽 → C𝔽) :=
    ((P𝔽).isQuotientCoveringMap ((ideleGroup_quotient.{_,0} F).2.2.1)).isCoveringMap.isLocalHomeomorph
  have hA : IsOpen (sLocalDivisorialStratum F S) := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
    exact (integralIdeleInsertion_isOpenEmbedding F S).isOpen_range
  have hOne : (1 : I𝔽) ∈ sLocalDivisorialStratum F S := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
    exact ⟨1, map_one _⟩
  obtain ⟨E, hE, h1, hEi⟩ := hq.isLocallyInjective 1
  have hU := hE.inter hA
  obtain ⟨D, hDm, hUD, hDA, hDb⟩ := exists_borel_transversal_in_open hq hA
    (sLocalDivisorialStratum_surjOn_ideleClass S hPic) hU inter_subset_right (hEi.mono inter_subset_left)
  exact ⟨D, hDm, mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds ⟨h1,hOne⟩) hUD),
    hDA, hDb⟩

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

local notation "μ𝔽" => multiplicativeTamagawaMeasure F
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

end RiemannMasullo
