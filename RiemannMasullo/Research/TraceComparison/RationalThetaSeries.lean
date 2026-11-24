module
public import RiemannMasullo.Research.TraceComparison.RationalThetaSpan
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # The physical rational radial theta representative -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField.AdeleRing NNReal SchwartzMap
namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "U" => (v : V) → (v.adicCompletionIntegers ℚ)ˣ
local notation "realCoord" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "𝓢ℝ" => SchwartzMap ℝ ℂ

private theorem finite_integral_iff (x : ℚ) :
    (∀ v : V, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x := by
  have h := diagonal_mem_integralAdelesOutside ℚ ∅ x
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty,
    not_false_eq_true, forall_const, Finset.coe_empty, integer_empty, Algebra.mem_bot] at h
  rw [show (∀ v : V, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔
    ∃ r : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ r = x from h]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨Rat.ringOfIntegersEquiv r, (Rat.ringOfIntegersEquiv_apply_coe r).trans hr⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, (map_intCast _ n).trans hn⟩⟩

private theorem finite_unit_mul_iff (x : ℚ) (g : 𝔸ˣ) (u : U)
    (hg : ∀ v, g.val.2 v = (u v).val.val) :
    (∀ v : V, ((algebraMap ℚ 𝔸 x) * g.val).2 v ∈ v.adicCompletionIntegers ℚ) ↔
      ∃ n : ℤ, (n : ℚ) = x := by
  rw [← finite_integral_iff]
  constructor
  · intro hm v
    have he : (u v).val.val * (u v).inv.val = 1 := congrArg Subtype.val (u v).val_inv
    have h := (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm v) (u v).inv.property
    change ((algebraMap ℚ 𝔸 x).2 v * g.val.2 v) * (u v).inv.val ∈ _ at h
    change (algebraMap ℚ 𝔸 x).2 v ∈ (v.adicCompletionIntegers ℚ).toSubring
    simpa only [hg, mul_assoc, he, mul_one] using h
  · intro hm v
    change (algebraMap ℚ 𝔸 x).2 v * g.val.2 v ∈ _
    rw [hg]
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm v) (u v).val.property

private theorem norm_of_integral_unit_representative (g : 𝔸ˣ) (u : U)
    (hg : ∀ v, g.val.2 v = (u v).val.val) {t : ℝ≥0ˣ}
    (ht : realCoord (g.val.1 Rat.infinitePlace) = t.val) :
    ((ideleNorm ℚ g).val : ℝ) = t.val := by
  rw [((ideleNorm_spec ℚ).1 _).2, Fintype.prod_subsingleton _ Rat.infinitePlace]
  have hfin (v : V) : ‖g.val.2 v‖ = 1 := by
    rw [hg]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (u v))).mp
    exact ⟨(u v).val.property, (u v).inv.property⟩
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one]
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) (g.val.1 Rat.infinitePlace)
  change ‖realCoord (g.val.1 Rat.infinitePlace)‖ = _ at h
  rw [← h, ht]
  simp [InfinitePlace.mult, Rat.isReal_infinitePlace]

private theorem hasSum_integer_theta (f : 𝓢ℝ) (hf : f 0 = 0)
    (g : 𝔸ˣ) (u : U) (hg : ∀ v, g.val.2 v = (u v).val.val) {t : ℝ}
    (ht : realCoord (g.val.1 Rat.infinitePlace) = t) :
    HasSum (fun n : ℤ ↦ f ((n : ℝ) * t))
      (adelicTheta (ratStandardAdelicTest f) (QuotientGroup.mk g)) := by
  classical
  let F (r : ℚˣ) := ratStandardAdelicTest f (Multiplicative.ofAdd (algebraMap ℚ 𝔸 (r : ℚ) * g.val))
  let G (n : ℤ) := f ((n : ℝ) * t)
  have hterm (r : ℚˣ) : F r = if ∃ n : ℤ, (n : ℚ) = r.val then f ((r.val : ℝ) * t) else 0 := by
    dsimp only [F]
    rw [ratStandardAdelicTest_apply, finite_unit_mul_iff _ g u hg]
    congr 2
    change realCoord (algebraMap ℚ Rat.infinitePlace.Completion (r : ℚ) * g.val.1 Rat.infinitePlace) = _
    rw [map_mul, ht]
    simp
  have hG0 : G 0 = 0 := by simp [G, hf]
  let i (n : Function.support G) : ℚˣ := Units.mk0 (n.val : ℚ) (by
    exact_mod_cast (show n.val ≠ 0 from fun h ↦ n.property (h ▸ hG0)))
  have hi : Injective i := by
    intro a b h
    apply Subtype.ext
    exact_mod_cast (show (a.val : ℚ) = b.val from congrArg Units.val h)
  have hval (n : Function.support G) : F (i n) = G n.val := by
    rw [hterm, ite_eq_left (show ∃ m : ℤ, (m : ℚ) = (i n).val from ⟨n.val, rfl⟩)]
    change f (((n.val : ℚ) : ℝ) * t) = _
    simp [G]
  have hcov : Function.support F ⊆ Set.range i := by
    intro r hr
    change F r ≠ 0 at hr
    rw [hterm] at hr
    split at hr
    · rename_i h
      obtain ⟨n, hn⟩ := h
      have hG : G n ≠ 0 := by simpa [G, ← hn] using hr
      exact ⟨⟨n, hG⟩, Units.ext hn⟩
    · exact (hr rfl).elim
  rw [adelicTheta_mk]
  apply (hasSum_iff_hasSum_of_ne_zero_bij (f := F) (g := G) i hi hcov hval).mp
  apply Summable.hasSum
  have H := (adelicAverage_summableUniformlyOn (ratStandardAdelicTest f) {(g, (0 : 𝔸))}
    isCompact_singleton).summable (Set.mem_singleton (g, (0 : 𝔸)))
  exact (show Summable (fun r ↦ ‖F r‖) by simpa [F, mul_comm] using H).of_norm

/-- The actual unaveraged adelic theta on rational idele classes is twice the scalar positive
integer theta of an even test vanishing at zero. Its value depends only on the idelic norm. -/
theorem ratStandardAdelicTest_theta (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (x : Cℚ) :
    adelicTheta (ratStandardAdelicTest f) x =
      2 * ∑' n : ℕ, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ)) := by
  obtain ⟨e, herep⟩ := ratIdeleClassGroup_decomposition
  obtain ⟨⟨t, u⟩, rfl⟩ := e.surjective x
  obtain ⟨g, harch, hfin, hclass⟩ := herep t u
  rw [hclass]
  have hnorm : ((ideleClassNorm ℚ (QuotientGroup.mk g)).val : ℝ) = t.val :=
    norm_of_integral_unit_representative g u hfin harch
  rw [hnorm]
  have hsum := hasSum_integer_theta f hf g u hfin harch
  rw [← hsum.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat _ hsum.summable]
  · simp only [Int.cast_zero, zero_mul, hf, zero_add, Int.cast_natCast, nsmul_eq_mul]
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f ((n : ℝ) * t.val))]
    simp
  · intro n
    simpa only [Int.cast_neg, neg_mul] using he ((n : ℝ) * t.val)

local instance : MeasurableSpace Cℚ := borel _
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)

/-- The trivial homogeneous average used in Chapter 10 contributes its norm-one Tamagawa
mass to the physical positive-integer theta formula. -/
theorem ratStandardAdelicTest_homogeneousTheta (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (x : Cℚ) :
    homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x =
      mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ))) := by
  let H := (ideleClassNorm ℚ).ker
  change (∫ k : H, adelicTheta (ratStandardAdelicTest f) (k.val * x) * _ ∂_) = _
  have hr (k : H) : ideleClassNorm ℚ (k.val * x) = ideleClassNorm ℚ x := by
    rw [map_mul, show ideleClassNorm ℚ k.val = 1 from k.property, one_mul]
  simp only [ratStandardAdelicTest_theta f he hf, hr, PontryaginDual.one_apply,
    Circle.coe_one, mul_one, integral_const, Measure.real, Complex.real_smul]

local notation "mℚ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "W(" α ", " β ", " s ")" =>
  CompactIntervalSobolev (ideleClassTamagawaMeasure ℚ) (logIdeleClassNorm ℚ) α β s
local notation "I(" a ", " h ", " s ")" =>
  actionIsotype ((exists_globalThetaSobolevAction (F := ℚ) a h s).choose.comp (ideleClassNorm ℚ).ker.subtype) 1

/-- The physical scalar profile lifted by the idelic norm, including the exact Haar factor
from the Chapter 10 homogeneous average. At the central exponent the first factor is a square root. -/
def ratRadialThetaProfile (a : ℝ) (f : 𝓢ℝ) (x : Cℚ) : ℂ :=
  ((((ideleClassNorm ℚ x).val : ℝ) ^ a : ℝ) : ℂ) *
    (mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ))))

private theorem weighted_homogeneous_eq (a : ℝ) (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) :
    modulationWeight mℚ a (homogeneousAdelicTheta 1 (ratStandardAdelicTest f)) =
      ratRadialThetaProfile a f := by
  funext x
  change _ * homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x = _
  rw [ratStandardAdelicTest_homogeneousTheta f he hf x]
  rfl

private theorem closure_eq_range_of_dense_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {i : X → Y} (hi : IsClosedEmbedding i) {s : Set Y}
    (hs : s ⊆ Set.range i) (hd : Dense (i ⁻¹' s)) : closure s = Set.range i := by
  refine Set.Subset.antisymm (closure_minimal hs hi.isClosed_range) ?_
  rintro _ ⟨x, rfl⟩
  exact (Set.mapsTo_preimage i s).closure hi.continuous (hd x)

private theorem exists_geometric_profile (a : ℝ) {α β s : ℝ} (hI : α ≤ β) (hs : 0 ≤ s)
    (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ)) (h0 : f 0 = 0) (hF : 𝓕 f 0 = 0) :
    ∃ y : I(a, hI, hs), (y.val.val : Cℚ → ℂ) =ᵐ[ideleClassTamagawaMeasure ℚ] ratRadialThetaProfile a f := by
  let j := (exists_globalHomogeneousThetaSobolevInclusion (F := ℚ) (a := a) hI hs 1).choose
  let F : adelePolarSubspace ℚ := ⟨ratStandardAdelicTest f, (ratStandardAdelicTest_polar_iff f).2 ⟨h0, hF⟩⟩
  let z : globalPolarFreeThetaSubmodule (F := ℚ) 1 :=
    ⟨Submodule.Quotient.mk F.val, ⟨F.val, F.property, rfl⟩⟩
  have hz : z.val = Submodule.Quotient.mk F.val := rfl
  refine ⟨j z, ?_⟩
  have hy := ((exists_globalHomogeneousThetaSobolevInclusion (F := ℚ) (a := a) hI hs 1).choose_spec.2.2 F z hz).2
  exact hy.trans (Eventually.of_forall (congrFun (weighted_homogeneous_eq a f he h0)))

/-- The closure of the actual scalar even bandlimited theta profiles in the full idelic
Sobolev space is precisely its Chapter 10 geometric trivial angular component.
Both polar moments vanish before passage to the closure, and the Fourier bound can grow. -/
theorem ratRadialTheta_closure_eq_globalThetaSobolev_trivial (a : ℝ) {α β s : ℝ}
    (hI : α ≤ β) (hs : 0 ≤ s) :
    closure {w : W(α, β, s) | ∃ f : 𝓢ℝ, Function.Even (f : ℝ → ℂ) ∧
      HasCompactSupport ((𝓕 f : 𝓢ℝ) : ℝ → ℂ) ∧ f 0 = 0 ∧ 𝓕 f 0 = 0 ∧
      (w : Cℚ → ℂ) =ᵐ[ideleClassTamagawaMeasure ℚ] ratRadialThetaProfile a f} =
        Set.range (fun y : I(a, hI, hs) ↦ y.val.val) := by
  let incl (y : I(a, hI, hs)) : W(α, β, s) := y.val.val
  have hH : IsClosed (globalThetaSobolev ℚ a hI hs : Set W(α, β, s)) :=
    Submodule.isClosed_topologicalClosure _
  have hi : IsClosedEmbedding incl :=
    hH.isClosedEmbedding_subtypeVal.comp (isClosed_actionIsotype _ _).isClosedEmbedding_subtypeVal
  apply closure_eq_range_of_dense_preimage hi
  · rintro w ⟨f, he, _, h0, hF, hw⟩
    obtain ⟨y, hy⟩ := exists_geometric_profile a hI hs f he h0 hF
    exact ⟨y, Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq (hy.trans hw.symm))⟩
  · apply (rat_even_bandlimited_globalThetaSobolev_dense a hI hs).mono
    rintro y ⟨f, he, hb, h0, hF, hy⟩
    exact ⟨f, he, hb, h0, hF, hy.trans (Eventually.of_forall (congrFun (weighted_homogeneous_eq a f he h0)))⟩

end RiemannMasullo.StripNuclearity
