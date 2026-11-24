module

public import RiemannMasullo.Research.StripNuclearity.RationalAngularSupport
public import RiemannMasullo.AppA_AlgebraicNT.Sec5a
import all RiemannMasullo.Research.StripNuclearity.IdeleAngularProfiles

/-! # Domains and averaging neighborhoods for the rational comparison -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Pointwise Topology
open RiemannMasullo.StripNuclearity
namespace RiemannMasullo

/-- A finite subgroup of a locally compact second-countable abelian group has
a Borel fundamental domain for the action by translations. -/
theorem exists_borel_finite_subgroup_domain {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [Finite H] (μ : Measure G) :
    ∃ D : Set G, MeasurableSet D ∧ IsFundamentalDomain H D μ := by
  let : IsClosed (H : Set G) := (Set.toFinite (H : Set G)).isClosed
  let q := Quotient.mk (MulAction.orbitRel H G)
  obtain ⟨D, hm, -, hb⟩ := exists_borel_orbit_transversal (H:=H) (X:=G) MeasurableSet.empty (injOn_empty q)
  refine ⟨D, hm, IsFundamentalDomain.mk' hm.nullMeasurableSet fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := hb.surjective (q x)
  obtain ⟨h, hh⟩ := Quotient.eq.mp hy
  have he : h • x = y.val := hh
  refine ⟨h, show h • x ∈ D by rw [he]; exact y.property, fun k hk ↦ ?_⟩
  have hz : (⟨k • x, hk⟩ : D) = y := hb.injective
    ((Quotient.sound (s:=MulAction.orbitRel H G) (a:=k • x) (b:=x) ⟨k,rfl⟩).trans hy.symm)
  exact Subtype.ext (mul_right_cancel ((congrArg Subtype.val hz).trans he.symm))

local notation "R" => Multiplicative ℝ
private abbrev logVolume : Measure R := (volume : Measure ℝ)

private theorem log_intervals :
    ∃ U : ℕ → Set R, IsDPrimeSequence logVolume U ∧ ∀ n, IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n := by
  let r (n : ℕ) : ℝ := (1/2)^n
  have hp (n : ℕ) : 0 < r n := pow_pos (by norm_num) _
  have ha : Antitone r := pow_right_anti₀ (by norm_num) (by norm_num)
  have hl : Tendsto r atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let U (n : ℕ) : Set R := Multiplicative.toAdd ⁻¹' Ioo (-(r n)) (r n)
  have hvol (n : ℕ) : logVolume (U n) = ENNReal.ofReal (2*r n) := by
    change volume (Ioo (-(r n)) (r n)) = _
    rw [Real.volume_Ioo]; congr 1; ring
  have hd (n : ℕ) : logVolume (U n * (U n)⁻¹) ≤ ENNReal.ofReal (4*r n) := by
    have hs : U n * (U n)⁻¹ ⊆ (Multiplicative.toAdd ⁻¹' Ioo (-(2*r n)) (2*r n)) := by
      rintro z ⟨x,hx,y,hy,rfl⟩
      change -r n < x.toAdd ∧ x.toAdd < r n at hx
      change -r n < -y.toAdd ∧ -y.toAdd < r n at hy
      change -(2*r n) < x.toAdd + y.toAdd ∧ x.toAdd + y.toAdd < 2*r n
      constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
    apply (measure_mono hs).trans_eq
    change volume (Ioo (-(2*r n)) (2*r n)) = _
    rw [Real.volume_Ioo]; congr 1; ring
  have ho (n : ℕ) : IsOpen (U n) := isOpen_Ioo (a := -(r n)) (b := r n)
  have h1 (n : ℕ) : (1:R) ∈ U n := ⟨neg_lt_zero.mpr (hp n),hp n⟩
  refine ⟨U,⟨⟨fun n ↦ ⟨h1 n,(ho n).measurableSet.nullMeasurableSet,hvol n ▸ ENNReal.ofReal_pos.mpr
    (mul_pos two_pos (hp n)),hvol n ▸ ENNReal.ofReal_lt_top⟩,
    fun i j hij ↦ preimage_mono (Ioo_subset_Ioo (neg_le_neg (ha hij)) (ha hij)),3,by norm_num,fun n ↦ ?_⟩, ?_⟩, ?_⟩
  · refine ⟨lt_of_lt_of_le (hvol n ▸ ENNReal.ofReal_pos.mpr (mul_pos two_pos (hp n)))
      (measure_mono (subset_mul_left _ (show (1:R) ∈ (U n)⁻¹ by simpa using h1 n))), (hd n).trans_lt ?_⟩
    rw [hvol, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith [hp n]) |>.mpr (by linarith [hp n])
  · intro W hW
    change W ∈ 𝓝 (0:ℝ) at hW
    obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp hW
    obtain ⟨n,hn⟩ := (hl.eventually (gt_mem_nhds hε)).exists
    refine ⟨n,fun x hx ↦ he ?_⟩
    change dist x.toAdd 0 < ε
    rw [Real.dist_eq,sub_zero]
    exact (abs_lt.mpr hx).trans hn
  · intro n
    refine ⟨ho n, ?_, ?_⟩
    · change IsCompact (closure (Ioo (-(r n)) (r n)))
      rw [closure_Ioo (by linarith [hp n])]
      exact isCompact_Icc
    · ext x
      change (-r n < -x.toAdd ∧ -x.toAdd < r n) ↔ (-r n < x.toAdd ∧ x.toAdd < r n)
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

private theorem chart_sequence {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (U : ℕ → Set G) (hU : IsDPrimeSequence μ U)
    (hr : ∀ n, IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n) :
    IsDPrimeSequence ν (fun n ↦ e '' U n) ∧
      ∀ n, IsOpen (e '' U n) ∧ IsCompact (closure (e '' U n)) ∧ (e '' U n)⁻¹ = e '' U n := by
  let η := μ.map e
  let : η.IsHaarMeasure := e.isHaarMeasure_map μ
  let c := ν.haarScalarFactor η
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have mass (B : Set G) : ν (e '' B) = (c : ℝ≥0∞) * μ B := by
    rw [Measure.isMulLeftInvariant_eq_smul ν η,smul_apply]
    change (c : ℝ≥0∞) * η (e '' B) = _
    congr 1
    exact (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.map_apply μ _).trans
      (congrArg μ (Set.preimage_image_eq _ e.injective))
  obtain ⟨⟨hbase,hanti,C,hC,hd⟩,hco⟩ := hU
  have he (B : Set G) : e '' (B * B⁻¹) = e '' B * (e '' B)⁻¹ := by
    rw [Set.image_mul (m:=e),Set.image_inv]
  refine ⟨⟨⟨fun n ↦ ?_,fun _ _ hij ↦ image_mono (hanti hij),C,hC,fun n ↦ ?_⟩,?_⟩, ?_⟩
  · refine ⟨⟨1,(hbase n).1,map_one _⟩,(e.toHomeomorph.isOpenMap _ (hr n).1).measurableSet.nullMeasurableSet,?_⟩
    rw [mass]
    exact ⟨ENNReal.mul_pos (by exact_mod_cast hc.ne') (hbase n).2.2.1.ne',
      ENNReal.mul_lt_top ENNReal.coe_lt_top (hbase n).2.2.2⟩
  · rw [← he, mass, mass, mul_left_comm]
    exact ⟨ENNReal.mul_pos (by exact_mod_cast hc.ne') (hd n).1.ne',
      ENNReal.mul_lt_mul_right (by exact_mod_cast hc.ne') ENNReal.coe_ne_top (hd n).2⟩
  · intro W hW
    obtain ⟨n,hn⟩ := hco (e ⁻¹' W) (e.continuous.continuousAt.preimage_mem_nhds (by simpa using hW))
    exact ⟨n,image_subset_iff.mpr hn⟩
  · intro n
    exact ⟨e.toHomeomorph.isOpenMap _ (hr n).1, e.toHomeomorph.image_closure _ ▸ (hr n).2.1.image e.continuous,
      (Set.image_inv e.toMonoidHom (U n)).symm.trans (congrArg (e '' ·) (hr n).2.2)⟩

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1 instIdeleClassHaarMeasureSec1

/-- Paper: Definition A.5.2.1, p. 569, and §12.2, pp. 507–508. The rational
idèle classes admit a decreasing regular D′ sequence of symmetric relatively
compact open neighborhoods. The angular factors are compact open subgroups.
Deviation: Shrinking the angular factors removes the obstruction in F219. -/
theorem exists_rational_regular_diagonal_sequence :
    ∃ U : ℕ → Set (IdeleClassGroup (𝓞 ℚ) ℚ), IsDPrimeSequence (ideleClassTamagawaMeasure ℚ) U ∧
      ∀ n, IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ (U n)⁻¹ = U n := by
  let K := (ideleClassNorm ℚ).ker
  let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
  let : TotallyDisconnectedSpace K := ratIdeleClassNormKer_totallyDisconnected
  let : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let μK : Measure K := Measure.haarMeasure ⊤
  let m := (⟨ideleClassNorm ℚ,(isProperMap_ideleClassNorm ℚ).continuous⟩ : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ)
  let σ := (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
    IdeleGroup (𝓞 ℚ) ℚ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ).comp ⟨canonicalIdeleNormSection ℚ,canonicalIdeleNormSection_continuous ℚ⟩
  obtain ⟨e,-⟩ := RiemannMasullo.StripNuclearity.exists_normSection_logChart m
    ⟨isProperMap_ideleClassNorm ℚ,ideleClassNorm_ne_one (F:=ℚ)⟩ σ (canonicalIdeleNormSection_rightInverse ℚ)
  obtain ⟨K₀,hK,hcomp⟩ := exists_isDDoublePrimeSequence_of_totallyDisconnected μK
  obtain ⟨W,hW,hr⟩ := log_intervals
  let : logVolume.IsHaarMeasure := by
    let : IsFiniteMeasureOnCompacts logVolume := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    let : Measure.IsOpenPosMeasure logVolume := inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    let : logVolume.IsMulLeftInvariant := ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let Z (n : ℕ) := (K₀ n : Set K) ×ˢ W n
  have hz (n : ℕ) : IsOpen (Z n) ∧ IsCompact (closure (Z n)) ∧ (Z n)⁻¹ = Z n := by
    refine ⟨(K₀ n).isOpen.prod (hr n).1, ?_, ?_⟩
    · rw [show Z n = _ from rfl, closure_prod_eq]
      rw [(K₀ n).isClosed.closure_eq]
      exact (hcomp n).1.prod (hr n).2.1
    · rw [show Z n = _ from rfl, Set.inv_prod, inv_coe_set, (hr n).2.2]
  have hp : IsDPrimeSequence (μK.prod logVolume) Z := by
    obtain ⟨⟨hb,ha,C,hC,hd⟩,hco⟩ := hW
    refine ⟨⟨fun n ↦ ?_, fun i j hij ↦ prod_mono (hK.1.1.2.1 hij) (ha hij), C,hC,fun n ↦ ?_⟩, ?_⟩
    · refine ⟨⟨(K₀ n).one_mem,(hb n).1⟩,(hz n).1.measurableSet.nullMeasurableSet,?_⟩
      rw [show Z n = _ from rfl, Measure.prod_prod]
      exact ⟨ENNReal.mul_pos (hK.1.1.1 n).2.2.1.ne' (hb n).2.2.1.ne',
        ENNReal.mul_lt_top (hK.1.1.1 n).2.2.2 (hb n).2.2.2⟩
    · change 0 < (μK.prod logVolume) ((↑(K₀ n) ×ˢ W n) * (↑(K₀ n) ×ˢ W n)⁻¹) ∧ _
      have hmul : (K₀ n : Set K) * (K₀ n : Set K) = (K₀ n : Set K) :=
        (K₀ n).toSubgroup.toSubmonoid.coe_mul_self_eq
      simp only [Z, Set.inv_prod, inv_coe_set, Set.prod_mul_prod_comm,
        hmul, Measure.prod_prod, mul_left_comm (ENNReal.ofReal C)]
      exact ⟨ENNReal.mul_pos (hK.1.1.1 n).2.2.1.ne' (hd n).1.ne',
        ENNReal.mul_lt_mul_right (hK.1.1.1 n).2.2.1.ne' (hK.1.1.1 n).2.2.2.ne (hd n).2⟩
    · intro A hA
      obtain ⟨B,hB,E,hE,hBE⟩ := mem_nhds_prod_iff.mp hA
      obtain ⟨i,hi⟩ := hK.1.2 B hB
      obtain ⟨j,hj⟩ := hco E hE
      exact ⟨max i j,(prod_mono ((hK.1.1.2.1 (le_max_left i j)).trans hi)
        ((ha (le_max_right i j)).trans hj)).trans hBE⟩
  exact ⟨fun n ↦ e '' Z n,chart_sequence e (μK.prod logVolume) (ideleClassTamagawaMeasure ℚ) Z hp hz⟩

end RiemannMasullo
