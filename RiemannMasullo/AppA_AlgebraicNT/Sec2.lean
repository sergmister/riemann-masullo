module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Orbital structures on adeles and ideles

Appendix A.2.1–A.2.2 of Masullo. We use the Minkowski embedding to specify the
archimedean parallelepiped for a chosen integral basis. Idelic norms take values in
the positive reals `ℝ≥0ˣ`, as in §A.1.
-/

@[expose] public section

noncomputable section

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open InfinitePlace.Completion
open scoped Classical NNRat NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F

section Additive

variable {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))

-- TODO(paper-gap): (A.2.1.1) uses only r₁ + r₂ indices and bounds absolute values.
-- The proof on p. 554 specifies [0,1)^[F:ℚ] in the real basis induced by the integral basis.

/-- Paper: Definition A.2.1.1, p. 545. The infinite fundamental domain is the half-open
parallelepiped of the chosen integral basis in Minkowski space, pulled back to the completions.
Deviation: We use the signed real coordinates and all the basis vectors specified on p. 554. -/
def infiniteAdeleFundamentalDomain : Set (InfiniteAdeleRing F) :=
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  (InfiniteAdeleRing.ringEquiv_mixedSpace F) ⁻¹'
    ZSpan.fundamentalDomain ((b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F))

/-- Paper: Definition A.2.1.1, p. 545. Along any basis vector, precisely the real
multiples with coefficient in the half-open unit interval belong to the infinite domain.
Deviation: This checks the coordinate convention given on p. 554. -/
theorem infiniteAdeleFundamentalDomain_basis_line (i : ι) (t : ℝ) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • mixedEmbedding F (b i : F)) ∈
      infiniteAdeleFundamentalDomain F b ↔ t ∈ Set.Ico 0 1 := by
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  have hB : B i = mixedEmbedding F (b i : F) := by
    simp only [B, Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
    rfl
  simp only [infiniteAdeleFundamentalDomain, Set.mem_preimage, RingEquiv.apply_symm_apply]
  change t • mixedEmbedding F (b i : F) ∈ ZSpan.fundamentalDomain B ↔ _
  rw [← hB, ZSpan.mem_fundamentalDomain, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single', mul_one]
  refine ⟨fun h ↦ ?_, fun ht k ↦ ?_⟩
  · simpa only [Finsupp.single_eq_same] using h i
  · by_cases h : k = i
    · simpa only [h, Finsupp.single_eq_same] using ht
    · rw [Finsupp.single_eq_of_ne h]
      exact ⟨le_rfl, zero_lt_one⟩

/-- Paper: Definition A.2.1.1, p. 545. The adelic fundamental domain consists of the
adeles in the infinite parallelepiped whose finite components are all integral.
Deviation: Its infinite factor uses the coordinate convention on p. 554. -/
def adeleFundamentalDomain : Set 𝔸[F] :=
  {a | a.1 ∈ infiniteAdeleFundamentalDomain F b ∧ a ∈ integralAdelesOutside F ∅}

/-- Paper: Definition A.2.1.1, p. 545. The adelic domain contains exactly one
diagonal element of the number field, namely zero. -/
theorem diagonal_mem_adeleFundamentalDomain (x : F) :
    algebraMap F 𝔸[F] x ∈ adeleFundamentalDomain F b ↔ x = 0 := by
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  simp only [adeleFundamentalDomain, Set.mem_ofPred_eq, AdeleRing.algebraMap_fst_def,
    infiniteAdeleFundamentalDomain, Set.mem_preimage,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  change mixedEmbedding F x ∈ ZSpan.fundamentalDomain B ∧ _ ↔ _
  constructor
  · rintro ⟨hinf, hfin⟩
    have hx := (diagonal_mem_integralAdelesOutside F ∅ x).mp hfin
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    apply mixedEmbedding_injective F
    rw [map_zero]
    apply B.ext_elem
    intro i
    have hi := (ZSpan.mem_fundamentalDomain B).mp hinf i
    change B.repr (e r : mixedEmbedding.mixedSpace F) i ∈ Set.Ico 0 1 at hi
    rw [Module.Basis.ofZLatticeBasis_repr_apply, Set.mem_Ico] at hi
    let n := (b.map e).repr (e r) i
    have hnonneg : 0 ≤ n := by exact_mod_cast hi.1
    have hlt : n < 1 := by exact_mod_cast hi.2
    have hn : n = 0 := by omega
    change B.repr (e r : mixedEmbedding.mixedSpace F) i = B.repr 0 i
    rw [Module.Basis.ofZLatticeBasis_repr_apply, map_zero, Finsupp.zero_apply]
    exact_mod_cast hn
  · rintro rfl
    rw [map_zero, map_zero, ZSpan.mem_fundamentalDomain]
    refine ⟨fun i ↦ ?_, (integralAdelesOutside F ∅).zero_mem⟩
    rw [map_zero, Finsupp.zero_apply]
    exact ⟨le_rfl, zero_lt_one⟩

/-- Paper: §A.2.1, p. 545. The adelic fundamental domain has compact closure. -/
theorem adeleFundamentalDomain_precompact : IsCompact (closure (adeleFundamentalDomain F b)) := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans
      ((Homeomorph.piCongrRight fun w ↦ (isometryEquivRealOfIsReal w.2).toHomeomorph).prodCongr
        ((Homeomorph.piCongrRight fun w ↦
          (isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let integral (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) : 𝔸ᶠ[F] :=
    ⟨fun v ↦ x v, Filter.Eventually.of_forall fun v ↦ (x v).property⟩
  have hIntegral : Continuous integral :=
    continuous_restrictedProduct_of_uniform
      (fun v ↦ continuous_subtype_val.comp (continuous_apply v))
      (Filter.Eventually.of_forall fun v x ↦ (x v).property)
  apply ((B.parallelepiped.isCompact.image h.symm.continuous).prod
    (isCompact_range hIntegral)).closure_of_subset
  rintro a ⟨haInf, haf⟩
  refine ⟨⟨h a.1, ZSpan.fundamentalDomain_subset_parallelepiped B haInf, h.symm_apply_apply _⟩, ?_⟩
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
    true_implies] at haf
  exact ⟨fun v ↦ ⟨a.2 v, haf v⟩, rfl⟩

/-- Paper: §A.2.1, p. 545. The adelic fundamental domain has nonempty interior. -/
theorem adeleFundamentalDomain_interior : (interior (adeleFundamentalDomain F b)).Nonempty := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hm : Continuous m := by
    change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  have hIntegral : IsOpen (integralAdelesOutside F ∅ : Set 𝔸[F]) := by
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred, Finset.notMem_empty,
      not_false_eq_true, true_implies]
    exact (RestrictedProduct.isOpen_forall_mem (fun v : HeightOneSpectrum (𝓞 F) ↦
      Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd
  let coords : 𝔸[F] → ι → ℝ := fun a ↦ B.equivFun (m a.1)
  let cube := Set.pi Set.univ (fun _ : ι ↦ Set.Ioo (0 : ℝ) 1)
  let U := (coords ⁻¹' cube) ∩ (integralAdelesOutside F ∅ : Set 𝔸[F])
  have hU : IsOpen U :=
    ((isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo).preimage
      ((continuous_equivFun_basis B).comp (hm.comp continuous_fst))).inter hIntegral
  let a : 𝔸[F] := (m.symm (B.equivFun.symm fun _ ↦ 1 / 2), 0)
  refine ⟨a, mem_interior.mpr ⟨U, ?_, hU, ?_⟩⟩
  · rintro x ⟨hx, hInt⟩
    refine ⟨(ZSpan.mem_fundamentalDomain B).mpr fun i ↦ ?_, hInt⟩
    exact Set.Ioo_subset_Ico_self (hx i (Set.mem_univ i))
  · refine ⟨?_, ?_⟩
    · change B.equivFun (m (m.symm (B.equivFun.symm fun _ ↦ 1 / 2))) ∈ cube
      rw [RingEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact fun _ _ ↦ ⟨by norm_num, by norm_num⟩
    · change a ∈ integralAdelesOutside F ∅
      simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
        true_implies]
      exact fun v ↦ (v.adicCompletionIntegers F).zero_mem

/-- Paper: §A.2.1, p. 545. Every nonzero diagonal translation moves the fundamental
domain off itself, including its half-open boundary. -/
theorem adeleFundamentalDomain_disjoint (x : F) (hx : x ≠ 0) :
    Disjoint (algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b) (adeleFundamentalDomain F b) := by
  rw [Set.disjoint_left]
  intro y hy hyDomain
  obtain ⟨a, ha, rfl⟩ := Set.mem_vadd_set.mp hy
  have hxFin : algebraMap F 𝔸[F] x ∈ integralAdelesOutside F ∅ := by
    have h := (integralAdelesOutside F ∅).sub_mem hyDomain.2 ha.2
    change (algebraMap F 𝔸[F] x + a) - a ∈ integralAdelesOutside F ∅ at h
    rwa [add_sub_cancel_right] at h
  have hxInt := (diagonal_mem_integralAdelesOutside F ∅ x).mp hxFin
  simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hxInt
  obtain ⟨r, rfl⟩ := hxInt
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let z := mixedEmbedding F (algebraMap (𝓞 F) F r)
  have hz : z ∈ Submodule.span ℤ (Set.range B) := by
    rw [(b.map e).ofZLatticeBasis_span ℝ]
    exact ⟨r, rfl⟩
  have haInf : m a.1 ∈ ZSpan.fundamentalDomain B := ha.1
  have hyInf : z + m a.1 ∈ ZSpan.fundamentalDomain B := by
    have h := hyDomain.1
    change m ((algebraMap F 𝔸[F] (algebraMap (𝓞 F) F r)).1 + a.1) ∈
      ZSpan.fundamentalDomain B at h
    rwa [map_add, AdeleRing.algebraMap_fst_def,
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at h
  have h := ZSpan.fract_eq_self.mpr hyInf
  rw [ZSpan.fract_zSpan_add B _ hz, ZSpan.fract_eq_self.mpr haInf] at h
  apply hx (mixedEmbedding_injective F ?_)
  rw [map_zero]
  exact add_eq_right.mp h.symm

/-- Paper: Lemma A.2.1.2, p. 545. The additive translates by field elements
of the adelic fundamental domain cover the adele ring. -/
theorem adeleFundamentalDomain_cover :
    (⋃ x : F, algebraMap F 𝔸[F] x +ᵥ adeleFundamentalDomain F b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  -- Choose a representative of the adelic class that is integral at all finite places.
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let q := QuotientAddGroup.mk' P
  obtain ⟨-, -, -, -, -, -, -, -, ⟨e, he⟩, -⟩ := adele_additive_quotient.{_, 0} F
  obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk'_surjective _ (e.symm (q a))
  have hq : q a = q a₀.val := by
    rw [← he, ha₀, e.apply_symm_apply]
  obtain ⟨x, hx⟩ : a - a₀.val ∈ P := QuotientAddGroup.eq_iff_sub_mem.mp hq
  -- Translate by an integer to put the archimedean component in the parallelepiped.
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let i := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map i).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  obtain ⟨z, hz, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (m a₀.val.1)
  have hspan : Submodule.span ℤ (Set.range B) = mixedEmbedding.integerLattice F :=
    (b.map i).ofZLatticeBasis_span ℝ
  have hz' : z.val ∈ mixedEmbedding.integerLattice F := hspan ▸ z.property
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, mixedEmbedding F (r : F) = z.val := hz'
  let d := algebraMap F 𝔸[F] (r : F)
  refine Set.mem_iUnion.mpr ⟨x - (r : F), Set.mem_vadd_set.mpr
    ⟨a₀.val + d, ⟨?_, ?_⟩, ?_⟩⟩
  · change m (a₀.val.1 + d.1) ∈ ZSpan.fundamentalDomain B
    rw [map_add, show d.1 = algebraMap F (InfiniteAdeleRing F) (r : F) from rfl,
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hr, add_comm]
    exact hz
  · have hd : d ∈ integralAdelesOutside F ∅ := by
      apply (diagonal_mem_integralAdelesOutside F ∅ _).mpr
      simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot]
      exact ⟨r, rfl⟩
    exact (integralAdelesOutside F ∅).add_mem a₀.property hd
  · change algebraMap F 𝔸[F] (x - (r : F)) + (a₀.val + d) = a
    change algebraMap F 𝔸[F] x = a - a₀.val at hx
    rw [map_sub, hx, show algebraMap F 𝔸[F] (r : F) = d from rfl]
    abel

/-- Paper: Lemma A.2.1.2, p. 545. Only finitely many field translates of the
closure of the fundamental domain meet a given compact subset of the adeles. -/
theorem adeleFundamentalDomain_finite_translates (K : Set 𝔸[F]) (hK : IsCompact K) :
    {x : F | ((algebraMap F 𝔸[F] x +ᵥ closure (adeleFundamentalDomain F b)) ∩ K).Nonempty}.Finite := by
  let d := algebraMap F 𝔸[F]
  let D := closure (adeleFundamentalDomain F b)
  obtain ⟨hinj, hclosed, hdiscrete, -⟩ := adele_additive_quotient.{_, 0} F
  have hdiff : IsCompact (K - D) := by
    change IsCompact (Set.image2 (· - ·) K D)
    rw [← Set.image_prod]
    exact (hK.prod (adeleFundamentalDomain_precompact F b)).image
      (continuous_fst.sub continuous_snd)
  have hfinite : ((K - D) ∩ Set.range d).Finite :=
    (hdiff.inter_right hclosed).finite (hdiscrete.mono Set.inter_subset_right)
  refine (hfinite.preimage hinj.injOn).subset ?_
  rintro x ⟨y, hy, hyK⟩
  obtain ⟨a, ha, rfl⟩ := Set.mem_vadd_set.mp hy
  exact ⟨Set.mem_sub.mpr ⟨d x + a, hyK, a, ha, add_sub_cancel_right _ _⟩, ⟨x, rfl⟩⟩

/-- Paper: Example A.2.1.3, p. 545. For the rational field the domain is the interval
from zero inclusive to one exclusive times the product of the finite local integer rings. -/
def ratAdeleFundamentalDomain : Set 𝔸[ℚ] :=
  {a | extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace) ∈ Set.Ico 0 1 ∧
    a ∈ integralAdelesOutside ℚ ∅}

/-- Paper: Example A.2.1.3, pp. 545–546. The interval description agrees with the
general adelic domain for the integral basis consisting of one. -/
private theorem ratAdeleFundamentalDomain_eq (b : Module.Basis Unit ℤ (𝓞 ℚ)) (hb : (b () : ℚ) = 1) :
    ratAdeleFundamentalDomain = adeleFundamentalDomain ℚ b := by
  ext a
  change (_ ∈ Set.Ico (0 : ℝ) 1 ∧ _) ↔ (_ ∈ infiniteAdeleFundamentalDomain ℚ b ∧ _)
  apply and_congr_left'
  let t := extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace)
  have h : InfiniteAdeleRing.ringEquiv_mixedSpace ℚ a.1 = t • mixedEmbedding ℚ (b () : ℚ) := by
    rw [hb, map_one]
    apply Prod.ext
    · funext v
      obtain ⟨v, hv⟩ := v
      obtain rfl := Subsingleton.elim v Rat.infinitePlace
      change t = t * 1
      exact (mul_one _).symm
    · funext v
      obtain ⟨v, hv⟩ := v
      obtain rfl := Subsingleton.elim v Rat.infinitePlace
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr hv Rat.isReal_infinitePlace).elim
  have hm := infiniteAdeleFundamentalDomain_basis_line ℚ b () t
  rwa [← h, RingEquiv.symm_apply_apply, Iff.comm] at hm

/-- Paper: Example A.2.1.3, p. 545. Every rational adele belongs to exactly one
rational translate of the displayed domain. -/
theorem ratAdeleFundamentalDomain_unique_translate (a : 𝔸[ℚ]) :
    ∃! q : ℚ, a ∈ algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain := by
  let b := (Module.Basis.singleton Unit ℤ).map Rat.ringOfIntegersEquiv.symm.toAddEquiv.toIntLinearEquiv
  have hb : (b () : ℚ) = 1 := by simp [b, Module.Basis.singleton_apply]
  rw [ratAdeleFundamentalDomain_eq b hb]
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp ((adeleFundamentalDomain_cover ℚ b).symm ▸ Set.mem_univ a)
  refine ⟨q, hq, ?_⟩
  intro r hr
  by_contra hne
  have hd := adeleFundamentalDomain_disjoint ℚ b (r - q) (sub_ne_zero.mpr hne)
  have hdis : Disjoint (algebraMap ℚ 𝔸[ℚ] r +ᵥ adeleFundamentalDomain ℚ b)
      (algebraMap ℚ 𝔸[ℚ] q +ᵥ adeleFundamentalDomain ℚ b) := by
    rw [Set.disjoint_vadd_set_right, ← add_vadd, add_comm, ← sub_eq_add_neg, ← map_sub]
    exact hd
  exact Set.disjoint_left.mp hdis hr hq

/-- Paper: Example A.2.1.3, p. 546. Each member of the rationally indexed cover
has compact closure. -/
theorem ratAdeleFundamentalDomain_precompact_translate (q : ℚ) :
    IsCompact (closure (algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain)) := by
  let b := (Module.Basis.singleton Unit ℤ).map Rat.ringOfIntegersEquiv.symm.toAddEquiv.toIntLinearEquiv
  have hb : (b () : ℚ) = 1 := by simp [b, Module.Basis.singleton_apply]
  rw [ratAdeleFundamentalDomain_eq b hb, closure_vadd]
  exact (adeleFundamentalDomain_precompact ℚ b).vadd _

end Additive

section NormSections

section RationalDecomposition

open scoped WithZero

local notation "RatFinitePlace" => HeightOneSpectrum (𝓞 ℚ)

/-- A positive generator of a rational prime ideal has trivial valuation at every other prime. -/
private theorem exists_pos_rat_uniformizer (v : RatFinitePlace) :
    ∃ p : ℚ, 0 < p ∧ ∀ w : RatFinitePlace, w.valuation ℚ p =
      if w = v then WithZero.exp (-1 : ℤ) else 1 := by
  let : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm
      Rat.ringOfIntegersEquiv.symm.surjective
  let r := Submodule.IsPrincipal.generator v.asIdeal
  have hr : r ≠ 0 := fun h ↦ v.ne_bot ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr h)
  have hspan : Ideal.span {r} = v.asIdeal := Ideal.span_singleton_generator _
  refine ⟨|(r : ℚ)|, abs_pos.mpr (by exact_mod_cast hr), fun w ↦ ?_⟩
  have habs : w.valuation ℚ |(r : ℚ)| = w.valuation ℚ (r : ℚ) := by
    rcases abs_choice (r : ℚ) with h | h <;> simp [h]
  rw [habs, HeightOneSpectrum.valuation_of_algebraMap]
  split_ifs with h
  · subst w
    exact v.intValuation_singleton hr hspan.symm
  · apply HeightOneSpectrum.intValuation_eq_one_iff.mpr
    intro hm
    have hle : v.asIdeal ≤ w.asIdeal := hspan ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isMaximal.ne_top hle).symm)

/-- Multiplying the positive prime generators to the prescribed powers matches all finite valuations. -/
private theorem exists_pos_rat_matching_idele (g : 𝕀[ℚ]) :
    ∃ q : ℚ≥0ˣ, ∀ w : RatFinitePlace, w.valuation ℚ (q.val : ℚ) = Valued.v (g.val.2 w) := by
  classical
  choose p hp hval using exists_pos_rat_uniformizer
  let n (v : RatFinitePlace) := -WithZero.log (Valued.v (g.val.2 v))
  have hfin : {v : RatFinitePlace | Valued.v (g.val.2 v) ≠ 1}.Finite :=
    Filter.eventually_cofinite.mp (AdeleRing.isUnit_iff.mp g.isUnit).2.2
  let S := hfin.toFinset
  let r := ∏ v ∈ S, p v ^ n v
  have hr : 0 < r := Finset.prod_pos (fun v _ ↦ zpow_pos (hp v) _)
  let q : ℚ≥0ˣ := Units.mk0 ⟨r, hr.le⟩ (fun h ↦ hr.ne' (congrArg (fun x : ℚ≥0 ↦ (x : ℚ)) h))
  refine ⟨q, fun w ↦ ?_⟩
  change w.valuation ℚ r = _
  rw [show r = ∏ v ∈ S, p v ^ n v from rfl, map_prod]
  simp only [map_zpow₀, hval]
  by_cases hw : w ∈ S
  · rw [Finset.prod_eq_single w (fun v _ hv ↦ by simp [Ne.symm hv]) (by simp [hw])]
    have hne : Valued.v (g.val.2 w) ≠ (0 : ℤᵐ⁰) :=
      (Valuation.ne_zero_iff _).mpr ((AdeleRing.isUnit_iff.mp g.isUnit).2.1 w)
    simp [n, ← WithZero.exp_zsmul, WithZero.exp_log hne]
  · have hone : Valued.v (g.val.2 w) = (1 : ℤᵐ⁰) := by simpa [S] using hw
    rw [hone]
    exact Finset.prod_eq_one fun v hv ↦ by simp [show w ≠ v from fun he ↦ hw (he ▸ hv)]

private abbrev RatLocalUnits := (v : RatFinitePlace) → (v.adicCompletionIntegers ℚ)ˣ

private def ratRealIdele : ℝˣ →* 𝕀[ℚ] :=
  (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace).comp
    (Units.map (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toMonoidHom)

private def ratFiniteIntegralMap : ((v : RatFinitePlace) → v.adicCompletionIntegers ℚ) →* 𝔸[ℚ] where
  toFun x := (1, ⟨fun v ↦ (x v).val, Filter.Eventually.of_forall fun v ↦ (x v).property⟩)
  map_one' := rfl
  map_mul' _ _ := Prod.ext (one_mul 1).symm rfl

private def ratIntegralIdele : RatLocalUnits →* 𝕀[ℚ] :=
  (Units.map ratFiniteIntegralMap).comp
    (ContinuousMulEquiv.piUnits (M := fun v : RatFinitePlace ↦ v.adicCompletionIntegers ℚ)).symm

private def ratPosPrincipal : ℚ≥0ˣ →* 𝕀[ℚ] :=
  (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ).comp (Units.map (NNRat.castHom ℚ).toMonoidHom)

private def ratIdeleFactors : ℝˣ × ℚ≥0ˣ × RatLocalUnits →* 𝕀[ℚ] :=
  ratRealIdele.coprod (ratPosPrincipal.coprod ratIntegralIdele)

private theorem ratIdeleFactors_continuous :
    letI : TopologicalSpace ℚ≥0ˣ := ⊥
    Continuous ratIdeleFactors := by
  let : TopologicalSpace ℚ≥0ˣ := ⊥
  let : DiscreteTopology ℚ≥0ˣ := ⟨rfl⟩
  have hreal : Continuous ratRealIdele := by
    unfold ratRealIdele IdeleGroup.ofCompletion
    simp only [MonoidHom.coe_comp]
    apply Continuous.comp <;> apply Continuous.units_map
    · exact (continuous_mulSingle (A := InfinitePlace.Completion) Rat.infinitePlace).prodMk
        continuous_const
    · exact (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous
  have hInt : Continuous ratFiniteIntegralMap :=
    continuous_const.prodMk (continuous_restrictedProduct_of_uniform
      (fun v ↦ continuous_subtype_val.comp (continuous_apply v))
      (Filter.Eventually.of_forall fun v x ↦ (x v).property))
  have hUnits : Continuous ratIntegralIdele :=
    (hInt.units_map _).comp
      (ContinuousMulEquiv.piUnits (M := fun v : RatFinitePlace ↦ v.adicCompletionIntegers ℚ)).symm.continuous
  have hprincipal : Continuous ratPosPrincipal := continuous_of_discreteTopology
  change Continuous (fun x : ℝˣ × ℚ≥0ˣ × RatLocalUnits ↦
    ratRealIdele x.1 * (ratPosPrincipal x.2.1 * ratIntegralIdele x.2.2))
  exact (hreal.comp continuous_fst).mul
    ((hprincipal.comp continuous_snd.fst).mul (hUnits.comp continuous_snd.snd))

private abbrev ratRealCoordinate (g : 𝕀[ℚ]) : ℝ :=
  extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (g.val.1 Rat.infinitePlace)

private theorem ratIdeleFactors_infinite (t : ℝˣ) (q : ℚ≥0ˣ) (h : RatLocalUnits) :
    ratRealCoordinate (ratIdeleFactors (t, q, h)) = t.val * ((q.val : ℚ) : ℝ) := by
  change extensionEmbeddingOfIsReal _ (_ * (_ * 1)) = _
  rw [mul_one, map_mul]
  congr 1
  · change extensionEmbeddingOfIsReal _ (Pi.mulSingle Rat.infinitePlace
      ((ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm t.val) Rat.infinitePlace) = t.val
    rw [Pi.mulSingle_eq_same]
    exact (ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply _
  · change extensionEmbeddingOfIsReal _ (algebraMap ℚ Rat.infinitePlace.Completion (q.val : ℚ)) = _
    simp

private theorem ratIdeleFactors_finite (t : ℝˣ) (q : ℚ≥0ˣ) (h : RatLocalUnits)
    (v : RatFinitePlace) : (ratIdeleFactors (t, q, h)).val.2 v =
      algebraMap ℚ (v.adicCompletion ℚ) (q.val : ℚ) * (h v).val.val := by
  change (ratRealIdele t).val.2 v * ((ratPosPrincipal q).val.2 v * (ratIntegralIdele h).val.2 v) = _
  rw [show (ratRealIdele t).val.2 v = 1 from rfl, one_mul]
  rfl

private theorem ratIdeleFactors_norm (t : ℝˣ) (q : ℚ≥0ˣ) (h : RatLocalUnits) :
    ((ideleNorm ℚ (ratIdeleFactors (t, q, h))).val : ℝ) = |t.val| := by
  have hprincipal : ideleNorm ℚ (ratPosPrincipal q) = 1 :=
    (ideleNorm_spec ℚ).2 (show ratPosPrincipal q ∈ IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ from ⟨_, rfl⟩)
  have hstrip : ideleNorm ℚ (ratIdeleFactors (t, q, h)) = ideleNorm ℚ (ratIdeleFactors (t, 1, h)) := by
    simp only [ratIdeleFactors, MonoidHom.coprod_apply, map_mul, hprincipal, map_one, one_mul]
  rw [hstrip, ((ideleNorm_spec ℚ).1 _).2, Fintype.prod_subsingleton _ Rat.infinitePlace]
  have hfin (v : RatFinitePlace) : ‖(ratIdeleFactors (t, 1, h)).val.2 v‖ = 1 := by
    rw [ratIdeleFactors_finite]
    simp only [Units.val_one, NNRat.coe_one, map_one, one_mul]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (h v))).mp
    exact ⟨(h v).val.property, (h v).inv.property⟩
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one]
  have hnorm := (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) ((ratIdeleFactors (t, 1, h)).val.1 Rat.infinitePlace)
  change ‖ratRealCoordinate (ratIdeleFactors (t, 1, h))‖ = _ at hnorm
  rw [← hnorm, ratIdeleFactors_infinite]
  simp [InfinitePlace.mult, Rat.isReal_infinitePlace]

private theorem ratIdeleFactors_injective : Injective ratIdeleFactors := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨t, q, h⟩ he
  have hnorm := ratIdeleFactors_norm t q h
  rw [he, map_one] at hnorm
  have hinf := ratIdeleFactors_infinite t q h
  rw [he] at hinf
  have hinf' : 1 = (t : ℝ) * ((q.val : ℚ) : ℝ) := by
    change extensionEmbeddingOfIsReal _ (1 : Rat.infinitePlace.Completion) = _ at hinf
    rwa [map_one] at hinf
  have hqpos : 0 < ((q.val : ℚ) : ℝ) := by
    exact_mod_cast (NNRat.coe_pos.mpr (pos_iff_ne_zero.mpr q.ne_zero))
  have hq : q = 1 := by
    apply Units.ext
    have heq := congrArg abs hinf'
    rw [abs_one, abs_mul, abs_of_pos hqpos, ← hnorm] at heq
    change 1 = 1 * ((q.val : ℚ) : ℝ) at heq
    rw [one_mul] at heq
    apply Subtype.ext
    change (q.val : ℚ) = 1
    exact_mod_cast heq.symm
  subst q
  have ht : t = 1 := by
    apply Units.ext
    simpa using hinf'.symm
  subst t
  refine Prod.ext rfl (Prod.ext rfl (funext fun v ↦ Units.ext (Subtype.ext ?_)))
  have hv := ratIdeleFactors_finite 1 1 h v
  rw [he] at hv
  change (h v).val.val = 1
  change (1 : v.adicCompletion ℚ) = algebraMap ℚ _ (1 : ℚ) * (h v).val.val at hv
  simpa using hv.symm

private theorem ratIdeleFactors_surjective : Surjective ratIdeleFactors := by
  intro g
  obtain ⟨q, hq⟩ := exists_pos_rat_matching_idele g
  let a : ℚˣ := Units.map (NNRat.castHom ℚ).toMonoidHom q
  let ev (v : RatFinitePlace) :=
    (RestrictedProduct.evalRingHom (fun w : RatFinitePlace ↦ w.adicCompletion ℚ) v).comp
      (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))
  let localRatio (v : RatFinitePlace) :=
    Units.map (ev v).toMonoidHom g / Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom a
  have hunit (v : RatFinitePlace) : localRatio v ∈ (v.adicCompletionIntegers ℚ).units := by
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    rw [show (localRatio v).val = _ from Units.val_div_eq_div_val _ _]
    change Valued.v (g.val.2 v / algebraMap ℚ (v.adicCompletion ℚ) (q.val : ℚ)) = 1
    have hval : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (q.val : ℚ)) = v.valuation ℚ (q.val : ℚ) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) _
    rw [map_div₀, hval, hq, div_self]
    exact (Valuation.ne_zero_iff _).mpr ((AdeleRing.isUnit_iff.mp g.isUnit).2.1 v)
  let h : RatLocalUnits := fun v ↦
    (v.adicCompletionIntegers ℚ).toSubring.toSubmonoid.unitsEquivUnitsType ⟨localRatio v, hunit v⟩
  let inf := (Pi.evalRingHom InfinitePlace.Completion Rat.infinitePlace).comp
    (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))
  let real := (ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom.comp inf
  let t := Units.map real.toMonoidHom g / Units.map (algebraMap ℚ ℝ).toMonoidHom a
  refine ⟨(t, q, h), Units.ext (Prod.ext ?_ ?_)⟩
  · funext w
    obtain rfl := Subsingleton.elim w Rat.infinitePlace
    apply (ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    change ratRealCoordinate (ratIdeleFactors (t, q, h)) = ratRealCoordinate g
    rw [ratIdeleFactors_infinite]
    rw [show t.val = _ from Units.val_div_eq_div_val _ _]
    exact div_mul_cancel₀ _ (Units.map (algebraMap ℚ ℝ).toMonoidHom a).ne_zero
  · apply RestrictedProduct.ext
    intro v
    refine (ratIdeleFactors_finite t q h v).trans ?_
    change _ * (localRatio v).val = _
    rw [show (localRatio v).val = _ from Units.val_div_eq_div_val _ _]
    exact mul_div_cancel₀ _ (Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom a).ne_zero

/-- Paper: Equations (A.2.2.1)–(A.2.2.2), p. 546. Rational ideles split into a real
unit, a discrete positive rational and a tuple of local integer units. The rational
factor acts diagonally, and the idelic norm is the absolute value of the real factor. -/
theorem ratIdeleGroup_decomposition :
    letI : TopologicalSpace ℚ≥0ˣ := ⊥
    let U := (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ
    ∃ e : (ℝˣ × ℚ≥0ˣ × U) ≃ₜ* 𝕀[ℚ], ∀ t q h,
      let g := e (t, q, h)
      let a : ℚ := q.val
      extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (g.val.1 Rat.infinitePlace) =
        t.val * (a : ℝ) ∧
      (∀ v, g.val.2 v = algebraMap ℚ (v.adicCompletion ℚ) a * (h v).val.val) ∧
      ((ideleNorm ℚ g).val : ℝ) = |t.val| := by
  let : TopologicalSpace ℚ≥0ˣ := ⊥
  let : DiscreteTopology ℚ≥0ˣ := ⟨rfl⟩
  have (v : RatFinitePlace) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  have : LocallyCompactSpace 𝕀[ℚ] := (ideleGroup_topology ℚ).2.1
  have : T2Space 𝕀[ℚ] := (ideleGroup_topology ℚ).1
  let e := MulEquiv.ofBijective ratIdeleFactors ⟨ratIdeleFactors_injective, ratIdeleFactors_surjective⟩
  have : CompactSpace RatLocalUnits := by infer_instance
  have : SigmaCompactSpace ℝˣ := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
  have : Countable ℚ≥0 := (Subtype.val_injective (p := fun x : ℚ ↦ 0 ≤ x)).countable
  have : Countable ℚ≥0ˣ := Units.val_injective.countable
  have : SigmaCompactSpace ℚ≥0ˣ := by infer_instance
  have hop := ratIdeleFactors.isOpenMap_of_sigmaCompact
    ratIdeleFactors_surjective ratIdeleFactors_continuous
  refine ⟨{ e with
    continuous_toFun := ratIdeleFactors_continuous
    continuous_invFun := e.toEquiv.continuous_symm_iff.mpr hop }, ?_⟩
  intro t q h
  exact ⟨ratIdeleFactors_infinite t q h, ratIdeleFactors_finite t q h, ratIdeleFactors_norm t q h⟩

end RationalDecomposition

private abbrev ratClassProjection := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)

private def ratClassRepresentative : ℝ≥0ˣ × RatLocalUnits →* 𝕀[ℚ] :=
  ratIdeleFactors.comp (((Units.map NNReal.toRealHom.toMonoidHom).comp (MonoidHom.fst _ _)).prod
    ((1 : ℝ≥0ˣ × RatLocalUnits →* ℚ≥0ˣ).prod (MonoidHom.snd _ _)))

private theorem ratClassMap_injective :
    Injective (ratClassProjection.comp ratClassRepresentative) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨t, h⟩ he
  let u := Units.map NNReal.toRealHom.toMonoidHom t
  change ratClassProjection (ratIdeleFactors (u, 1, h)) = 1 at he
  have hprincipal := (QuotientGroup.eq_one_iff _).mp he
  -- The product formula fixes the positive real coordinate of a principal representative.
  have hn := (ideleNorm_spec ℚ).2 hprincipal
  have hnorm := ratIdeleFactors_norm u 1 h
  rw [hn] at hnorm
  have ht : t = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    change (t.val : ℝ) = 1
    change 1 = |(t.val : ℝ)| at hnorm
    exact (abs_of_nonneg (NNReal.coe_nonneg t.val)).symm.trans hnorm.symm
  subst t
  obtain ⟨r, hr⟩ := hprincipal
  have hinf := ratIdeleFactors_infinite u 1 h
  rw [← hr] at hinf
  change extensionEmbeddingOfIsReal _ (algebraMap ℚ Rat.infinitePlace.Completion (r : ℚ)) = _ at hinf
  have hrval : (r : ℚ) = 1 := by
    have : ((r : ℚ) : ℝ) = 1 := by simpa [u] using hinf
    exact_mod_cast this
  have hr1 : r = 1 := Units.ext hrval
  rw [hr1, map_one] at hr
  have hf : (u, (1 : ℚ≥0ˣ), h) = 1 := ratIdeleFactors_injective (hr.symm.trans (map_one _).symm)
  exact Prod.ext rfl (congrArg (fun x : ℝˣ × ℚ≥0ˣ × RatLocalUnits ↦ x.2.2) hf)

private theorem ratIdeleFactors_neg_one :
    ratIdeleFactors (-1, 1, fun _ ↦ -1) = IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (-1) := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · funext w
    obtain rfl := Subsingleton.elim w Rat.infinitePlace
    apply (ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    change ratRealCoordinate (ratIdeleFactors _) =
      extensionEmbeddingOfIsReal _ (algebraMap ℚ Rat.infinitePlace.Completion ((-1 : ℚˣ) : ℚ))
    rw [ratIdeleFactors_infinite]
    simp
  · apply RestrictedProduct.ext
    intro v
    refine (ratIdeleFactors_finite _ _ _ v).trans ?_
    change algebraMap ℚ _ ((1 : ℚ≥0ˣ).val : ℚ) * _ = algebraMap ℚ _ ((-1 : ℚˣ) : ℚ)
    simp

private theorem ratClassMap_surjective :
    Surjective (ratClassProjection.comp ratClassRepresentative) := by
  let M := ratClassProjection.comp ratIdeleFactors
  -- Positive principal ideles disappear in the quotient.
  have drop (t : ℝˣ) (q : ℚ≥0ˣ) (h : RatLocalUnits) : M (t, q, h) = M (t, 1, h) := by
    have hq : ratClassProjection (ratPosPrincipal q) = ratClassProjection (ratPosPrincipal 1) := by
      rw [map_one, map_one]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
    simp only [M, MonoidHom.comp_apply, ratIdeleFactors, MonoidHom.coprod_apply, map_mul, hq]
  -- Changing both the real sign and all finite signs multiplies by the principal idele −1.
  let ε : RatLocalUnits := fun _ ↦ -1
  have hε : M (-1, 1, ε) = M 1 := by
    rw [map_one]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨-1, ratIdeleFactors_neg_one.symm⟩
  intro c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨⟨t, q, h⟩, rfl⟩ := ratIdeleFactors_surjective g
  let p := Units.map Real.nnabs.toMonoidHom t
  let u := Units.map NNReal.toRealHom.toMonoidHom p
  have hu : (u : ℝ) = |(t : ℝ)| := Real.coe_nnabs _
  rcases le_total 0 (t : ℝ) with ht | ht
  · refine ⟨(p, h), ?_⟩
    change M (u, 1, h) = M (t, q, h)
    rw [show u = t from Units.ext (hu.trans (abs_of_nonneg ht)), drop t q h]
  · refine ⟨(p, ε * h), ?_⟩
    change M (u, 1, ε * h) = M (t, q, h)
    have ht' : u = -t := Units.ext (hu.trans (abs_of_nonpos ht))
    calc
      M (u, 1, ε * h) = M ((-1, 1, ε) * (t, 1, h)) := by simp [ht']
      _ = M (1 * (t, 1, h)) := by simp only [map_mul, hε]
      _ = M (t, 1, h) := by rw [one_mul]
      _ = M (t, q, h) := (drop t q h).symm

/-- Paper: Equation (A.2.2.3), p. 546. Rational idele classes identify with the product
of the positive reals and the finite integral units, by sending the tuple to its class. -/
theorem ratIdeleClassGroup_decomposition :
    let U := (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ
    ∃ e : (ℝ≥0ˣ × U) ≃ₜ* IdeleClassGroup (𝓞 ℚ) ℚ, ∀ t h, ∃ g : 𝕀[ℚ],
      extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (g.val.1 Rat.infinitePlace) = t.val ∧
      (∀ v, g.val.2 v = (h v).val.val) ∧ e (t, h) = QuotientGroup.mk g := by
  have hrep : Continuous ratClassRepresentative := by
    let : TopologicalSpace ℚ≥0ˣ := ⊥
    have hu : Continuous (Units.map NNReal.toRealHom.toMonoidHom) :=
      NNReal.continuous_coe.units_map _
    exact ratIdeleFactors_continuous.comp
      ((hu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
  obtain ⟨_, _, _, _, hquot, hT2, hloc, _⟩ := ideleGroup_quotient.{0, 0} ℚ
  have (v : HeightOneSpectrum (𝓞 ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  have : CompactSpace RatLocalUnits := by infer_instance
  have : SigmaCompactSpace ℝ≥0ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  have : SigmaCompactSpace ℝ≥0ˣ := Units.isClosedEmbedding_embedProduct.sigmaCompactSpace
  let f := ratClassProjection.comp ratClassRepresentative
  have hf : Continuous f := hquot.continuous.comp hrep
  let e := MulEquiv.ofBijective f ⟨ratClassMap_injective, ratClassMap_surjective⟩
  have hopen := f.isOpenMap_of_sigmaCompact ratClassMap_surjective hf
  refine ⟨{ e with
    continuous_toFun := hf
    continuous_invFun := e.toEquiv.continuous_symm_iff.mpr hopen }, fun t h ↦
      ⟨ratClassRepresentative (t, h), ?_, fun v ↦ ?_, rfl⟩⟩
  · change ratRealCoordinate (ratIdeleFactors (_, 1, h)) = _
    simpa using ratIdeleFactors_infinite (Units.map NNReal.toRealHom.toMonoidHom t) 1 h
  · change (ratIdeleFactors (_, 1, h)).val.2 v = _
    simpa using ratIdeleFactors_finite (Units.map NNReal.toRealHom.toMonoidHom t) 1 h v

-- TODO(paper-gap): A.2.2.1 writes an idele-valued section and a class-group norm in
-- the same identity. The introductory paragraph on p. 546 specifies the quotient map.

/-- Paper: Lemma A.2.2.1, p. 546. The rational section inserts a positive real at
the unique real place of the rationals and one at every finite place. -/
def ratIdeleNormSection : ℝ≥0ˣ →* 𝕀[ℚ] :=
  let atInfinity := (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRingHom
  (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace).comp
    (Units.map (atInfinity.comp NNReal.toRealHom).toMonoidHom)

/-- Paper: Lemma A.2.2.1, p. 546. Insertion at the real place is continuous. -/
theorem ratIdeleNormSection_continuous : Continuous ratIdeleNormSection := by
  unfold ratIdeleNormSection IdeleGroup.ofCompletion
  simp only [MonoidHom.coe_comp]
  apply Continuous.comp <;> apply Continuous.units_map
  · exact (continuous_mulSingle (A := InfinitePlace.Completion) Rat.infinitePlace).prodMk
      continuous_const
  · exact (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous.comp
      NNReal.continuous_coe

/-- Paper: Lemma A.2.2.1, p. 546. The rational section is a right inverse to the
idelic norm before passage to classes. -/
theorem ratIdeleNormSection_rightInverse : RightInverse ratIdeleNormSection (ideleNorm ℚ) := by
  intro t
  apply Units.ext
  change Real.toNNReal ‖(ratIdeleNormSection t).val‖ = t.val
  rw [AdeleRing.norm_apply_of_isUnit (ratIdeleNormSection t).isUnit,
    Fintype.prod_subsingleton _ Rat.infinitePlace]
  have hfin (v : HeightOneSpectrum (𝓞 ℚ)) : (ratIdeleNormSection t).val.2 v = 1 := rfl
  simp only [hfin, norm_one, finprod_one, mul_one]
  have hnorm : ‖(ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm (t.val : ℝ)‖ =
      ‖(t.val : ℝ)‖ :=
    (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.isometry.norm_map_of_map_zero
      (map_zero (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm) _
  simp [ratIdeleNormSection, InfinitePlace.mult, Rat.isReal_infinitePlace, hnorm]

/-- Paper: Lemma A.2.2.1, p. 546. The class of the rational section has the
prescribed class norm.
Deviation: The paper's class-valued statement requires composition with the quotient map. -/
theorem ratIdeleNormSection_class_rightInverse :
    RightInverse ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)).comp
      ratIdeleNormSection) (ideleClassNorm ℚ) := by
  exact ratIdeleNormSection_rightInverse

/-- Paper: Lemma A.2.2.2, p. 546. Scalar extension from the rational adeles is the
unique adelic extension of the rational embedding supplied by Lemma A.1.2.1. -/
def rationalAdeleEmbedding : 𝔸[ℚ] →+* 𝔸[F] :=
  let ⟨_, _, _, _, _, _, _, _, _, extensions⟩ := adele_additive_quotient ℚ
  (extensions F (algebraMap ℚ F)).1.exists.choose

/-- Paper: Lemma A.2.2.2, p. 546. The scalar embedding on adeles extends the
diagonal rational embedding and respects the places below each component. -/
theorem rationalAdeleEmbedding_spec : IsAdeleExtension ℚ (algebraMap ℚ F) (rationalAdeleEmbedding F) := by
  unfold rationalAdeleEmbedding
  split
  rename_i extensions
  exact (extensions F (algebraMap ℚ F)).1.exists.choose_spec

/-- Paper: Lemma A.2.2.2, p. 546. The relative idelic norm to the rationals is
the determinant of multiplication on the adele algebra, restricted to units. -/
def relativeIdeleNormRat : 𝕀[F] →* 𝕀[ℚ] :=
  letI := (rationalAdeleEmbedding F).toAlgebra
  Units.map (Algebra.norm 𝔸[ℚ])

section AdeleBasis

open Filter
open scoped RestrictedProduct

local notation "dF(" F ")" => algebraMap F (𝔸ᶠ[F])

/-- The finite adeles whose component at every finite place lies in the local integer ring. -/
def finiteIntegralAdeles : Subring (𝔸ᶠ[F]) :=
  ⨅ v : HeightOneSpectrum (𝓞 F),
    ((v.adicCompletionIntegers F).toSubring).comap (RestrictedProduct.evalRingHom _ v)

local notation "IF(" F ")" => finiteIntegralAdeles F

/-- Membership in the integral finite adeles is tested at each finite place. -/
theorem mem_finiteIntegralAdeles_iff (a : 𝔸ᶠ[F]) :
    a ∈ IF(F) ↔ ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F := by
  simp only [finiteIntegralAdeles, Subring.mem_iInf]
  rfl

/-- With no exceptional places, integrality is determined by the finite component. -/
private theorem mem_integralAdelesOutside_iff_snd (a : 𝔸[F]) :
    a ∈ integralAdelesOutside F ∅ ↔ a.2 ∈ IF(F) := by
  rw [mem_finiteIntegralAdeles_iff]
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty,
    not_false_eq_true, true_implies]
  rfl

/-- A diagonal finite adele is everywhere integral exactly when it comes from a field integer. -/
private theorem finiteDiagonal_mem_integral (x : F) :
    dF(F) x ∈ IF(F) ↔ ∃ r : 𝓞 F, (r : F) = x := by
  rw [← show (algebraMap F 𝔸[F] x).2 = dF(F) x from rfl,
    ← mem_integralAdelesOutside_iff_snd, diagonal_mem_integralAdelesOutside]
  simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot]
  rfl

/-- Every finite adele differs from a diagonal field element by an integral finite adele. -/
private theorem finiteAdele_sub_diagonal (a : 𝔸ᶠ[F]) :
    ∃ x : F, a - dF(F) x ∈ IF(F) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨e, he⟩, -⟩ := adele_additive_quotient.{_, 0} F
  let q := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)
  let A : 𝔸[F] := (0, a)
  obtain ⟨a₀, ha₀⟩ := QuotientAddGroup.mk'_surjective _ (e.symm (q A))
  have hq : q A = q a₀.val := by rw [← he, ha₀, e.apply_symm_apply]
  obtain ⟨x, hx⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hq
  have hx' : dF(F) x = a - a₀.val.2 := congrArg Prod.snd hx
  exact ⟨x, by simpa only [hx', sub_sub_cancel] using
    (mem_integralAdelesOutside_iff_snd F a₀.val).mp a₀.property⟩

/-- The product of the local integer rings is compact in the finite adele ring. -/
private theorem isCompact_finiteIntegralAdeles : IsCompact (IF(F) : Set (𝔸ᶠ[F])) := by
  let integral (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) : 𝔸ᶠ[F] :=
    ⟨fun v ↦ x v, Eventually.of_forall fun v ↦ (x v).property⟩
  have hIntegral : Continuous integral :=
    continuous_restrictedProduct_of_uniform
      (fun v ↦ continuous_subtype_val.comp (continuous_apply v))
      (Eventually.of_forall fun v x ↦ (x v).property)
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  convert isCompact_range hIntegral using 1
  ext a
  rw [SetLike.mem_coe, mem_finiteIntegralAdeles_iff]
  exact ⟨fun ha ↦ ⟨fun v ↦ ⟨a v, ha v⟩, by apply RestrictedProduct.ext; intro v; rfl⟩,
    fun ⟨x, hx⟩ v ↦ hx ▸ (x v).property⟩

/-- Every integral finite adele is congruent to a diagonal field integer modulo any
positive integer times the integral finite adeles. -/
private theorem finiteIntegralAdeles_mod_nat (a : 𝔸ᶠ[F]) (ha : a ∈ IF(F))
    (n : ℕ) (hn : n ≠ 0) :
    ∃ (z : 𝓞 F) (u : 𝔸ᶠ[F]), u ∈ IF(F) ∧ a = dF(F) (z : F) + (n : 𝔸ᶠ[F]) * u := by
  obtain ⟨x, hx⟩ := finiteAdele_sub_diagonal F (dF(F) (n : F)⁻¹ * a)
  let u := dF(F) (n : F)⁻¹ * a - dF(F) x
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h : (n : 𝔸ᶠ[F]) * u = a - dF(F) ((n : F) * x) := by
    dsimp [u]
    rw [mul_sub, ← map_natCast (dF(F)) n, ← mul_assoc, ← map_mul, ← map_mul,
      mul_inv_cancel₀ hnF, map_one, one_mul]
  have hz : dF(F) ((n : F) * x) ∈ IF(F) := by
    rw [← sub_sub_cancel a (dF(F) ((n : F) * x)), ← h]
    exact (IF(F)).sub_mem ha ((IF(F)).mul_mem (natCast_mem (IF(F)) n) hx)
  obtain ⟨z, hz⟩ := (finiteDiagonal_mem_integral F _).mp hz
  exact ⟨z, u, hx, by rw [hz, h, add_sub_cancel]⟩

/-- A finite adele divisible by every positive integer within the integral finite adeles is zero. -/
theorem finiteAdele_eq_zero_of_forall_nat_mul (a : 𝔸ᶠ[F])
    (h : ∀ n : ℕ, n ≠ 0 → ∃ u : 𝔸ᶠ[F], u ∈ IF(F) ∧ a = (n : 𝔸ᶠ[F]) * u) :
    a = 0 := by
  apply FiniteAdeleRing.ext
  intro w
  by_contra hw
  let P := w.asIdeal.under ℤ
  have hP : P ≠ ⊥ := Ideal.under_ne_bot ℤ w.ne_bot
  obtain ⟨z, hzP, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  let n := z.natAbs
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hnP : (n : ℤ) ∈ P := by
    rcases Int.natAbs_eq z with he | he
    · rw [show (n : ℤ) = z from he.symm]
      exact hzP
    · have hneg : (n : ℤ) = -z := by
        simpa only [neg_neg] using congrArg Neg.neg he.symm
      rw [hneg]
      exact P.neg_mem hzP
  have hnval : Valued.v (n : w.adicCompletion F) < 1 := by
    rw [← map_natCast (algebraMap F (w.adicCompletion F)),
      show Valued.v (algebraMap F (w.adicCompletion F) (n : F)) = _ from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) _]
    change w.valuation F (n : F) < 1
    have hp : (n : 𝓞 F) ∈ w.asIdeal := by simpa [P, Ideal.under] using hnP
    simpa only [map_natCast] using (w.valuation_lt_one_iff_mem (K := F) (n : 𝓞 F)).2 hp
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.mk0 (Valued.v (a w)) ((Valuation.ne_zero_iff _).mpr hw)
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hnval γ
  obtain ⟨u, hu, he⟩ := h (n ^ k) (pow_ne_zero _ hn)
  have huval : Valued.v (u w) ≤ 1 :=
    (mem_finiteIntegralAdeles_iff F u).mp hu w
  have hwa : a w = (n : w.adicCompletion F) ^ k * u w := by
    let ev : 𝔸ᶠ[F] →+* w.adicCompletion F :=
      RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F) w
    have he' := congrArg ev he
    rw [map_mul, map_natCast ev (n ^ k), Nat.cast_pow] at he'
    exact he'
  have hc : Valued.v (a w) ≤ Valued.v (n : w.adicCompletion F) ^ k := by
    rw [hwa, map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le huval
  exact (not_lt_of_ge hc) hk

/-- The diagonal integral basis gives unique finite adelic coordinates over the rational finite
adeles for a continuous scalar map preserving diagonals and integrality. -/
private theorem finiteAdele_integralBasis_bijective
    (g : 𝔸ᶠ[ℚ] →+* 𝔸ᶠ[F]) (hg : Continuous g)
    (hdiag : ∀ x : ℚ, g (dF(ℚ) x) = dF(F) (algebraMap ℚ F x))
    (hint : Set.MapsTo g (IF(ℚ) : Set (𝔸ᶠ[ℚ])) (IF(F) : Set (𝔸ᶠ[F]))) :
    Bijective (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → 𝔸ᶠ[ℚ] ↦
      ∑ i, g (c i) * dF(F) (integralBasis F i)) := by
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let b := integralBasis F
  let φ : (ι → 𝔸ᶠ[ℚ]) →+ 𝔸ᶠ[F] :=
    { toFun := fun c ↦ ∑ i, g (c i) * dF(F) (b i)
      map_zero' := by simp
      map_add' := fun c e ↦ by simp [add_mul, Finset.sum_add_distrib] }
  change Bijective φ
  let S : Set (ι → 𝔸ᶠ[ℚ]) := Set.pi Set.univ fun _ ↦ (IF(ℚ) : Set (𝔸ᶠ[ℚ]))
  have hS (c : ι → 𝔸ᶠ[ℚ]) : c ∈ S ↔ ∀ i, c i ∈ IF(ℚ) := by simp [S]
  have hi (c : ι → 𝔸ᶠ[ℚ]) (hc : c ∈ S) : φ c ∈ IF(F) :=
    sum_mem fun i _ ↦ (IF(F)).mul_mem (hint ((hS c).mp hc i))
      ((finiteDiagonal_mem_integral F _).mpr ⟨RingOfIntegers.basis F i, (integralBasis_apply F i).symm⟩)
  have hd (q : ι → ℚ) : φ (fun i ↦ dF(ℚ) (q i)) = dF(F) (b.equivFun.symm q) := by
    change (∑ i, g (dF(ℚ) (q i)) * dF(F) (b i)) = _
    simp only [hdiag, Module.Basis.equivFun_symm_apply, map_sum, Algebra.smul_def, map_mul]
    rfl
  have hcoords (z : 𝓞 F) (i : ι) : dF(ℚ) (b.equivFun (z : F) i) ∈ IF(ℚ) := by
    apply (finiteDiagonal_mem_integral ℚ _).mpr
    refine ⟨((RingOfIntegers.basis F).repr z i : ℤ), ?_⟩
    simp only [Module.Basis.equivFun_apply, b, integralBasis_repr_apply, map_intCast]
    rfl
  have hc : Continuous φ := by
    change Continuous fun c : ι → 𝔸ᶠ[ℚ] ↦ ∑ i, g (c i) * dF(F) (b i)
    exact continuous_finsetSum _ fun i _ ↦ (hg.comp (continuous_apply i)).mul continuous_const
  -- Approximate each coefficient by a rational. A relation forces the resulting
  -- rational combination to be a field integer, so its coefficients are integral.
  have hkernel (c : ι → 𝔸ᶠ[ℚ]) (hzero : φ c = 0) : c ∈ S := by
    choose q hq using fun i ↦ finiteAdele_sub_diagonal ℚ (c i)
    let u : ι → 𝔸ᶠ[ℚ] := fun i ↦ c i - dF(ℚ) (q i)
    have hu : u ∈ S := (hS u).mpr hq
    have he : c = (fun i ↦ dF(ℚ) (q i)) + u := by
      funext i
      exact (add_sub_cancel _ _).symm
    rw [he, map_add, hd, add_eq_zero_iff_eq_neg] at hzero
    obtain ⟨z, hz⟩ := (finiteDiagonal_mem_integral F _).mp
      (hzero ▸ (IF(F)).neg_mem (hi u hu))
    have hqz : b.equivFun (z : F) = q := by rw [hz, LinearEquiv.apply_symm_apply]
    rw [he]
    exact (hS _).mpr fun i ↦ (IF(ℚ)).add_mem (hqz ▸ hcoords z i) (hq i)
  constructor
  · apply (injective_iff_map_eq_zero φ).mpr
    intro c hzero
    funext i
    apply finiteAdele_eq_zero_of_forall_nat_mul ℚ
    intro n hn
    -- Apply the same argument after dividing all coefficients by the given integer.
    let t := dF(ℚ) (n : ℚ)⁻¹
    let u : ι → 𝔸ᶠ[ℚ] := fun j ↦ t * c j
    have he : φ u = g t * φ c := by
      change (∑ j, g (t * c j) * dF(F) (b j)) = g t * ∑ j, g (c j) * dF(F) (b j)
      simp only [map_mul, mul_assoc, Finset.mul_sum]
    have hu : φ u = 0 := by rw [he, hzero, mul_zero]
    refine ⟨u i, (hS u).mp (hkernel u hu) i, ?_⟩
    change c i = (n : 𝔸ᶠ[ℚ]) * (dF(ℚ) (n : ℚ)⁻¹ * c i)
    rw [← mul_assoc, ← map_natCast (dF(ℚ)) n, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), map_one, one_mul]
  · have : T2Space (𝔸ᶠ[F]) := by
      change T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F])
      infer_instance
    have hcompact : IsCompact (φ '' S) := by
      apply IsCompact.image _ hc
      exact isCompact_univ_pi fun _ ↦ isCompact_finiteIntegralAdeles ℚ
    have hIntSurj (a : 𝔸ᶠ[F]) (ha : a ∈ IF(F)) : a ∈ φ '' S := by
      -- Each congruence class meets the compact image of the integral coefficients.
      -- Intersect these conditions and use separation by positive integer multiples.
      let T (n : {n : ℕ // n ≠ 0}) : Set (𝔸ᶠ[F]) :=
        (φ '' S) ∩ (fun x ↦ a - x) ⁻¹' ((fun u ↦ (n.val : 𝔸ᶠ[F]) * u) '' IF(F))
      have hclosed (n : {n : ℕ // n ≠ 0}) :
          IsClosed ((fun x : 𝔸ᶠ[F] ↦ a - x) ⁻¹' ((fun u ↦ (n.val : 𝔸ᶠ[F]) * u) '' IF(F))) :=
        ((isCompact_finiteIntegralAdeles F).image (continuous_const.mul continuous_id)).isClosed.preimage
          (continuous_const.sub continuous_id)
      have hdirected : Directed (· ⊇ ·) T := by
        intro n m
        have hsub (k l : {n : ℕ // n ≠ 0}) :
            T ⟨k.val * l.val, mul_ne_zero k.property l.property⟩ ⊆ T k := by
          rintro x ⟨hx, u, hu, he⟩
          exact ⟨hx, (l.val : 𝔸ᶠ[F]) * u,
            (IF(F)).mul_mem (natCast_mem _ _) hu, by simpa only [Nat.cast_mul, mul_assoc] using he⟩
        refine ⟨⟨n.val * m.val, mul_ne_zero n.property m.property⟩, hsub n m, ?_⟩
        simpa only [mul_comm n.val m.val] using hsub m n
      have hnonempty (n : {n : ℕ // n ≠ 0}) : (T n).Nonempty := by
        obtain ⟨z, u, hu, he⟩ := finiteIntegralAdeles_mod_nat F a ha n n.property
        let q := b.equivFun (z : F)
        have hp : φ (fun i ↦ dF(ℚ) (q i)) = dF(F) (z : F) := by
          rw [hd, LinearEquiv.symm_apply_apply]
        exact ⟨dF(F) (z : F), ⟨_, (hS _).mpr (hcoords z), hp⟩, u, hu,
          (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he.symm))⟩
      have : Nonempty {n : ℕ // n ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T
        hdirected hnonempty (fun n ↦ hcompact.inter_right (hclosed n))
        (fun n ↦ hcompact.isClosed.inter (hclosed n))
      have hxa : a - x = 0 := finiteAdele_eq_zero_of_forall_nat_mul F _ fun n hn ↦ by
        obtain ⟨_, u, hu, he⟩ := Set.mem_iInter.mp hx ⟨n, hn⟩
        exact ⟨u, hu, he.symm⟩
      exact (sub_eq_zero.mp hxa).symm ▸ (Set.mem_iInter.mp hx ⟨1, one_ne_zero⟩).1
    intro a
    obtain ⟨x, hx⟩ := finiteAdele_sub_diagonal F a
    obtain ⟨u, -, hu⟩ := hIntSurj _ hx
    let q := b.equivFun x
    refine ⟨u + (fun i ↦ dF(ℚ) (q i)), ?_⟩
    rw [map_add, hu, hd, LinearEquiv.symm_apply_apply, sub_add_cancel]

/-- The infinite component of scalar extension depends only on the input infinite component. -/
theorem rationalAdeleEmbedding_fst_eq (a b : 𝔸[ℚ]) (h : a.1 = b.1) :
    (rationalAdeleEmbedding F a).1 = (rationalAdeleEmbedding F b).1 := by
  let f := rationalAdeleEmbedding F
  have hzero : (f (a - b)).1 = 0 := by
    funext w
    apply (rationalAdeleEmbedding_spec F).2.2.1 w (a - b)
    change (a.1 - b.1) _ = 0
    rw [h, sub_self]
    rfl
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- The diagonal integral basis gives unique infinite adelic coordinates over the rational
infinite adeles. -/
private theorem infiniteAdele_integralBasis_bijective :
    Bijective (fun c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ ↦
      ∑ i, (rationalAdeleEmbedding F (c i, 0)).1 *
        algebraMap F (InfiniteAdeleRing F) (integralBasis F i)) := by
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let e : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique InfinitePlace.Completion).trans
      (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph
  have hm : Continuous m := by
    simp only [m]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  let f := rationalAdeleEmbedding F
  have hs := rationalAdeleEmbedding_spec F
  let j (r : ℝ) : mixedEmbedding.mixedSpace F := m (f (e.symm r, 0)).1
  have hj : Continuous j :=
    hm.comp (continuous_fst.comp (hs.1.comp (e.symm.continuous.prodMk continuous_const)))
  -- Both continuous real scalar maps agree on the dense rational diagonal.
  have hreal : j = algebraMap ℝ (mixedEmbedding.mixedSpace F) := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).equalizer hj
      (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace F))
    funext q
    change j (q : ℝ) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (q : ℝ)
    have hq : e ((algebraMap ℚ 𝔸[ℚ] q).1) = (q : ℝ) := by
      change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (algebraMap ℚ Rat.infinitePlace.Completion q) = (q : ℝ)
      simp
    have harg : e.symm (q : ℝ) = (algebraMap ℚ 𝔸[ℚ] q).1 := e.symm_apply_eq.mpr hq.symm
    have h := rationalAdeleEmbedding_fst_eq F (e.symm (q : ℝ), 0) (algebraMap ℚ 𝔸[ℚ] q) harg
    change m (f (e.symm (q : ℝ), 0)).1 = _
    rw [h, hs.2.1, AdeleRing.algebraMap_fst_def]
    exact DFunLike.congr_fun (Subsingleton.elim
      (m.toRingHom.comp ((algebraMap F (InfiniteAdeleRing F)).comp (algebraMap ℚ F)))
      ((algebraMap ℝ (mixedEmbedding.mixedSpace F)).comp (algebraMap ℚ ℝ))) q
  let b := mixedEmbedding.latticeBasis F
  let p := Equiv.piCongrRight (fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ↦ e.toEquiv)
  have he (c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ) :
      m (∑ i, (f (c i, 0)).1 * algebraMap F (InfiniteAdeleRing F) (integralBasis F i)) =
        b.equivFun.symm (p c) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h : m (f (c i, 0)).1 = algebraMap ℝ (mixedEmbedding.mixedSpace F) (e (c i)) := by
      simpa only [j, e.symm_apply_apply] using congrFun hreal (e (c i))
    rw [map_mul, h, Algebra.smul_def, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      ← mixedEmbedding.latticeBasis_apply]
    rfl
  have hcomp : Bijective (fun (c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ) ↦
      m (∑ i, (f (c i, 0)).1 * algebraMap F (InfiniteAdeleRing F) (integralBasis F i))) :=
    (show (fun (c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → InfiniteAdeleRing ℚ) ↦
        m (∑ i, (f (c i, 0)).1 *
        algebraMap F (InfiniteAdeleRing F) (integralBasis F i))) = b.equivFun.symm ∘ p from
      funext he) ▸ b.equivFun.symm.bijective.comp p.bijective
  exact ⟨fun _ _ h ↦ hcomp.injective (congrArg m h),
    fun y ↦ let ⟨c, hc⟩ := hcomp.surjective (m y); ⟨c, m.injective hc⟩⟩

/-- The diagonal images of the integral basis form a basis over the rational adeles. -/
theorem exists_adelicIntegralBasis :
    letI := (rationalAdeleEmbedding F).toAlgebra
    ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) 𝔸[ℚ] 𝔸[F],
      ∀ i, b i = algebraMap F 𝔸[F] (integralBasis F i) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  let f := rationalAdeleEmbedding F
  have hs := rationalAdeleEmbedding_spec F
  have hfin (a : 𝔸[ℚ]) : (f a).2 = (f (0, a.2)).2 := by
    let a' : 𝔸[ℚ] := (0, a.2)
    have h : (f (a - a')).2 = 0 := by
      apply FiniteAdeleRing.ext
      intro w
      exact hs.2.2.2 (w.under (𝓞 ℚ)) w rfl (a - a') (by change a.2 _ - a.2 _ = 0; simp)
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  let g : 𝔸ᶠ[ℚ] →+* 𝔸ᶠ[F] :=
    { toFun := fun a ↦ (f (0, a)).2
      map_zero' := congrArg Prod.snd (map_zero f)
      map_one' := (hfin 1).symm.trans (congrArg Prod.snd (map_one f))
      map_add' := fun a b ↦ by
        have h : ((0, a) : 𝔸[ℚ]) + (0, b) = (0, a + b) := Prod.ext (zero_add _) rfl
        rw [← h, map_add]
        rfl
      map_mul' := fun a b ↦ by
        have h : ((0, a) : 𝔸[ℚ]) * (0, b) = (0, a * b) := Prod.ext (zero_mul _) rfl
        rw [← h, map_mul]
        rfl }
  have hg : Continuous g := continuous_snd.comp (hs.1.comp (continuous_const.prodMk continuous_id))
  have hgfin (a : 𝔸[ℚ]) : (f a).2 = g a.2 := hfin a
  have hgdiag (x : ℚ) : g (dF(ℚ) x) = dF(F) (algebraMap ℚ F x) := by
    rw [← AdeleRing.algebraMap_snd_def, ← hgfin, hs.2.1, AdeleRing.algebraMap_snd_def]
  have hgint : Set.MapsTo g (IF(ℚ) : Set (𝔸ᶠ[ℚ])) (IF(F) : Set (𝔸ᶠ[F])) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, extensions⟩ := adele_additive_quotient ℚ
    obtain ⟨r, -, -, -, -, -, hr, -, -⟩ := (extensions F (algebraMap ℚ F)).2 f hs
    intro a ha
    let x : integralAdelesOutside ℚ ∅ :=
      ⟨(1, a), (mem_integralAdelesOutside_iff_snd ℚ _).mpr ha⟩
    change g ((x : 𝔸[ℚ]).2) ∈ IF(F)
    rw [← hgfin (x : 𝔸[ℚ])]
    apply (mem_integralAdelesOutside_iff_snd F _).mp
    rw [← hr]
    exact (r x).property
  have hinf (a : 𝔸[ℚ]) : (f a).1 = (f (a.1, 0)).1 :=
    rationalAdeleEmbedding_fst_eq F a (a.1, 0) rfl
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let v (i : ι) := algebraMap F 𝔸[F] (integralBasis F i)
  let φ : (ι → 𝔸[ℚ]) →ₗ[𝔸[ℚ]] 𝔸[F] :=
    ∑ i, (LinearMap.proj i).smulRight (v i)
  have hφ (a : ι → 𝔸[ℚ]) : φ a = ∑ i, f (a i) * v i := by
    simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Algebra.smul_def]
    rfl
  let φinf (a : ι → InfiniteAdeleRing ℚ) :=
    ∑ i, (f (a i, 0)).1 * algebraMap F (InfiniteAdeleRing F) (integralBasis F i)
  let φf (a : ι → 𝔸ᶠ[ℚ]) := ∑ i, g (a i) * dF(F) (integralBasis F i)
  have hinf' (a : ι → 𝔸[ℚ]) : (φ a).1 = φinf (fun i ↦ (a i).1) := by
    rw [hφ]
    change (RingHom.fst _ _) (∑ i, f (a i) * v i) = _
    simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * (v i).1) (hinf (a i))
  have hfin' (a : ι → 𝔸[ℚ]) : (φ a).2 = φf (fun i ↦ (a i).2) := by
    rw [hφ]
    change (RingHom.snd _ _) (∑ i, f (a i) * v i) = _
    simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * (v i).2) (hgfin (a i))
  have hinfbij : Bijective φinf := infiniteAdele_integralBasis_bijective F
  have hfinbij : Bijective φf := finiteAdele_integralBasis_bijective F g hg hgdiag hgint
  have hbij : Bijective φ := by
    constructor
    · intro a b h
      have h1 := hinfbij.injective ((hinf' a).symm.trans ((congrArg Prod.fst h).trans (hinf' b)))
      have h2 := hfinbij.injective ((hfin' a).symm.trans ((congrArg Prod.snd h).trans (hfin' b)))
      exact funext fun i ↦ Prod.ext (congrFun h1 i) (congrFun h2 i)
    · intro a
      obtain ⟨x, hx⟩ := hinfbij.surjective a.1
      obtain ⟨y, hy⟩ := hfinbij.surjective a.2
      refine ⟨fun i ↦ (x i, y i), Prod.ext ?_ ?_⟩
      · exact (hinf' _).trans hx
      · exact (hfin' _).trans hy
  refine ⟨(Pi.basisFun 𝔸[ℚ] ι).map (LinearEquiv.ofBijective φ hbij), fun i ↦ ?_⟩
  change φ (Pi.basisFun 𝔸[ℚ] ι i) = v i
  rw [Pi.basisFun_apply, hφ, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, map_one, one_mul]
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, map_zero, zero_mul]
  · exact fun h ↦ (h (Finset.mem_univ i)).elim

/-- Paper: Lemma A.2.2.2, p. 546. The adele algebra on which the relative norm
takes a determinant is finite free of the field degree.
Deviation: This sanity check rules out the default determinant on modules without a finite basis. -/
theorem rationalAdeleEmbedding_hasBasis :
    letI := (rationalAdeleEmbedding F).toAlgebra
    Nonempty (Module.Basis (Fin (Module.finrank ℚ F)) 𝔸[ℚ] 𝔸[F]) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b, -⟩ := exists_adelicIntegralBasis F
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ Fin (Module.finrank ℚ F) :=
    (Fintype.equivFin _).trans (finCongr (Module.finrank_eq_card_basis (integralBasis F)).symm)
  exact ⟨b.reindex e⟩

end AdeleBasis

open scoped RestrictedProduct in
/-- Paper: Lemma A.2.2.2, p. 546. The relative norm to the rational ideles is continuous. -/
theorem relativeIdeleNormRat_continuous : Continuous (relativeIdeleNormRat F) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  have : SigmaCompactSpace 𝔸[ℚ] := by
    let K (q : ℚ) := closure (algebraMap ℚ 𝔸[ℚ] q +ᵥ ratAdeleFundamentalDomain)
    have hcover : ⋃ q, K q = Set.univ := by
      apply Set.eq_univ_of_forall
      intro a
      obtain ⟨q, hq, _⟩ := ratAdeleFundamentalDomain_unique_translate a
      exact Set.mem_iUnion.mpr ⟨q, subset_closure hq⟩
    exact ⟨hcover ▸ isSigmaCompact_iUnion_of_isCompact K
      ratAdeleFundamentalDomain_precompact_translate⟩
  have (v : HeightOneSpectrum (𝓞 F)) : LocallyCompactSpace (v.adicCompletion F) :=
    locallyCompactSpace_adicCompletion v
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
  have : LocallyCompactSpace 𝔸[F] := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  have : T2Space 𝔸[F] := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  -- The finite sum map is continuous and open, so its inverse gives continuous coordinates.
  have hsum : Continuous (fun c ↦ b.equivFun.symm c) := by
    simp only [Module.Basis.equivFun_symm_apply, Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ ↦
      ((rationalAdeleEmbedding_spec F).1.comp (continuous_apply i)).mul continuous_const
  have hcoords : Continuous b.equivFun :=
    b.equivFun.symm.toEquiv.continuous_symm_iff.mpr
      (b.equivFun.symm.toLinearMap.toAddMonoidHom.isOpenMap_of_sigmaCompact
        b.equivFun.symm.surjective hsum)
  unfold relativeIdeleNormRat
  apply Continuous.units_map
  change Continuous (fun x : 𝔸[F] ↦ Algebra.norm 𝔸[ℚ] x)
  simp_rw [Algebra.norm_eq_matrix_det b]
  apply Continuous.matrix_det
  refine continuous_matrix fun i j ↦ ?_
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul, ← Module.Basis.equivFun_apply]
  exact (continuous_apply i).comp (hcoords.comp (continuous_id.mul continuous_const))

section RelativeNorm

local notation "ιF" => Module.Free.ChooseBasisIndex ℤ (𝓞 F)
local notation "dQ" => algebraMap ℚ 𝔸[ℚ]
local notation "dL" => algebraMap F 𝔸[F]

/-- Diagonal rational coordinates lift to adelic coordinates in the diagonal integral basis. -/
private theorem adelicIntegralBasis_sum
    (b : letI := (rationalAdeleEmbedding F).toAlgebra; Module.Basis ιF 𝔸[ℚ] 𝔸[F])
    (hb : ∀ i, b i = dL (integralBasis F i)) (q : ιF → ℚ) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    (∑ i, dQ (q i) • b i) = dL ((integralBasis F).equivFun.symm q) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [hb, Algebra.smul_def, map_mul]
  exact congrArg (· * dL (integralBasis F i)) ((rationalAdeleEmbedding_spec F).2.1 (q i))

/-- The determinant norm on a diagonal adele is the diagonal of the field norm. -/
private theorem rationalAdeleNorm_diagonal
    (b : letI := (rationalAdeleEmbedding F).toAlgebra; Module.Basis ιF 𝔸[ℚ] 𝔸[F])
    (hb : ∀ i, b i = dL (integralBasis F i)) (x : F) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    Algebra.norm 𝔸[ℚ] (dL x) = dQ (Algebra.norm ℚ x) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (integralBasis F), RingHom.map_det]
  congr 1
  ext i j
  change (Algebra.leftMulMatrix b (dL x)) i j =
    dQ ((Algebra.leftMulMatrix (integralBasis F) x) i j)
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul]
  let y := x * integralBasis F j
  change b.repr (dL y) i = dQ ((integralBasis F).repr y i)
  have h := adelicIntegralBasis_sum F b hb ((integralBasis F).equivFun y)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← h, ← b.equivFun_symm_apply]
  change b.equivFun (b.equivFun.symm _) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Projecting the determinant is polynomial in the projected coordinates of the input. -/
private theorem rationalAdeleNorm_eval_sum {K : Type*} [CommRing K]
    (b : letI := (rationalAdeleEmbedding F).toAlgebra; Module.Basis ιF 𝔸[ℚ] 𝔸[F])
    (p : 𝔸[ℚ] →+* K) (c : ιF → 𝔸[ℚ]) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    p (Algebra.norm 𝔸[ℚ] (∑ i, c i • b i)) =
      (∑ i, p (c i) • (Algebra.leftMulMatrix b (b i)).map p).det := by
  let := (rationalAdeleEmbedding F).toAlgebra
  rw [Algebra.norm_eq_matrix_det b, p.map_det, map_sum]
  congr 1
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.sum_apply, map_sum,
    map_smul, Matrix.smul_apply, smul_eq_mul, map_mul]

/-- A projected determinant identity extends from diagonal elements by density in the
scalar coordinates. The scalar `r` retains the projected coordinates on both sides. -/
private theorem rationalAdeleNorm_compare {K : Type*} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (p : 𝔸[ℚ] →+* K) (s : K → 𝔸[ℚ]) (hs : Continuous s)
    (hdense : DenseRange (p ∘ dQ))
    (r : 𝔸[ℚ]) (hr : ∀ c, r * s (p c) = r * c)
    (n : K → ℝ) (hn : Continuous n) (g : 𝔸[F] → ℝ) (hg : Continuous g)
    (hgr : ∀ a, g (rationalAdeleEmbedding F r * a) = g a)
    (hdiag : ∀ x : F, n (p (dQ (Algebra.norm ℚ x))) = g (dL x)) (a : 𝔸[F]) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    n (p (Algebra.norm 𝔸[ℚ] a)) = g a := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b, hb⟩ := exists_adelicIntegralBasis F
  let z (c : ιF → 𝔸[ℚ]) : 𝔸[F] := ∑ i, c i • b i
  let P (t : ιF → K) : Matrix ιF ιF K := ∑ i, t i • (Algebra.leftMulMatrix b (b i)).map p
  have hproject (c : ιF → 𝔸[ℚ]) : p (Algebra.norm 𝔸[ℚ] (z c)) = (P (p ∘ c)).det :=
    rationalAdeleNorm_eval_sum F b p c
  have hreplace (c : ιF → 𝔸[ℚ]) : g (z (s ∘ p ∘ c)) = g (z c) := by
    rw [← hgr (z (s ∘ p ∘ c)), ← hgr (z c)]
    change g (r • z (s ∘ p ∘ c)) = g (r • z c)
    simp only [z, Finset.smul_sum, smul_smul, Function.comp_apply, hr]
  have hleft : Continuous (fun t ↦ n (P t).det) := by
    apply hn.comp
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    refine continuous_finsetSum _ fun σ _ ↦ continuous_const.mul
      (continuous_finsetProd _ fun j _ ↦ ?_)
    simp only [P, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const
  have hright : Continuous (fun t ↦ g (z (s ∘ t))) := by
    apply hg.comp
    simp only [z, Function.comp_apply, Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ ↦
      ((rationalAdeleEmbedding_spec F).1.comp (hs.comp (continuous_apply i))).mul
        continuous_const
  have hd : DenseRange (fun q : ιF → ℚ ↦ p ∘ dQ ∘ q) :=
    DenseRange.piMap fun _ ↦ hdense
  have he := hd.equalizer hleft hright (by
    funext q
    change n (P (p ∘ dQ ∘ q)).det = g (z (s ∘ p ∘ dQ ∘ q))
    have hz : z (dQ ∘ q) = dL ((integralBasis F).equivFun.symm q) :=
      adelicIntegralBasis_sum F b hb q
    rw [← hproject (dQ ∘ q), hreplace (dQ ∘ q), hz, rationalAdeleNorm_diagonal F b hb]
    exact hdiag _)
  let c := b.equivFun a
  have hc : z c = a := (b.equivFun_symm_apply c).symm.trans (b.equivFun.symm_apply_apply a)
  calc
    n (p (Algebra.norm 𝔸[ℚ] a)) = n (P (p ∘ c)).det := by rw [← hc, hproject]
    _ = g (z (s ∘ p ∘ c)) := congrFun he (p ∘ c)
    _ = g a := (hreplace c).trans (congrArg g hc)

/-- The archimedean factor of the adelic determinant norm agrees with the normalized
archimedean product on the original adele. -/
private theorem rationalAdeleNorm_infinite (a : 𝔸[F]) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    ‖(Algebra.norm 𝔸[ℚ] a).1‖ = ‖a.1‖ := by
  have hQ : Continuous (fun x : InfiniteAdeleRing ℚ ↦ ‖x‖) := by
    simp only [InfiniteAdeleRing.norm_def]
    exact continuous_finsetProd _ fun w _ ↦ (continuous_apply w).norm.pow _
  have hF : Continuous (fun x : InfiniteAdeleRing F ↦ ‖x‖) := by
    simp only [InfiniteAdeleRing.norm_def]
    exact continuous_finsetProd _ fun w _ ↦ (continuous_apply w).norm.pow _
  let r : 𝔸[ℚ] := (1, 0)
  refine rationalAdeleNorm_compare F (RingHom.fst _ _) (fun t ↦ (t, 0))
    (continuous_id.prodMk continuous_const)
    (InfiniteAdeleRing.denseRange_algebraMap ℚ) r ?_ norm hQ
    (fun a ↦ ‖a.1‖) (hF.comp continuous_fst) ?_ ?_ a
  · intro c
    exact Prod.ext rfl (by change (0 : 𝔸ᶠ[ℚ]) * 0 = 0 * c.2; simp)
  · intro x
    change ‖(rationalAdeleEmbedding F r).1 * x.1‖ = ‖x.1‖
    rw [rationalAdeleEmbedding_fst_eq F r 1 rfl, map_one]
    change ‖1 * x.1‖ = ‖x.1‖
    rw [one_mul]
  · intro x
    change ‖algebraMap ℚ (InfiniteAdeleRing ℚ) (Algebra.norm ℚ x)‖ =
      ‖algebraMap F (InfiniteAdeleRing F) x‖
    rw [InfiniteAdeleRing.coe_norm_eq_abs_norm, InfiniteAdeleRing.coe_norm_eq_abs_norm,
      Algebra.norm_self, MonoidHom.id_apply]

attribute [local instance] FractionRing.liftAlgebra in
/-- The multiplicity of a rational prime in a relative ideal norm is the sum of the
multiplicities above it, weighted by the inertia degrees. -/
private theorem multiplicity_relNorm_rat (v : HeightOneSpectrum (𝓞 ℚ))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    let s := (Ideal.hasFiniteMulSupport hI).toFinset
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 ℚ) I) =
      ∑ w ∈ s with w.under (𝓞 ℚ) = v, multiplicity w.asIdeal I * w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  let s := (Ideal.hasFiniteMulSupport hI).toFinset
  let N : Ideal (𝓞 F) →*₀ Ideal (𝓞 ℚ) := Ideal.relNorm (𝓞 ℚ)
  let m (w : HeightOneSpectrum (𝓞 F)) := multiplicity w.asIdeal I
  have hpow (w : HeightOneSpectrum (𝓞 F)) :
      N (w.maxPowDividing I) = (w.under (𝓞 ℚ)).asIdeal ^ (m w * w.asIdeal.inertiaDeg (𝓞 ℚ)) := by
    let u := w.under (𝓞 ℚ)
    have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
    have := w.isMaximal
    have := u.isMaximal
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow,
      Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal u.asIdeal, ← pow_mul, Nat.mul_comm]
  have hfac : ∏ w ∈ s, N (w.maxPowDividing I) = N I := by
    rw [← map_prod, ← finprod_eq_prod _ (Ideal.hasFiniteMulSupport hI),
      Ideal.finprod_heightOneSpectrum_factorization hI]
  have hmult (w : HeightOneSpectrum (𝓞 F)) :
      emultiplicity v.asIdeal (N (w.maxPowDividing I)) =
        if w.under (𝓞 ℚ) = v then ((m w * w.asIdeal.inertiaDeg (𝓞 ℚ) : ℕ) : ℕ∞) else 0 := by
    rw [hpow]
    split_ifs with hw
    · rw [hw, emultiplicity_pow_self_of_prime v.prime]
    · have hnd : ¬ v.asIdeal ∣ (w.under (𝓞 ℚ)).asIdeal := by
        intro h
        exact hw (HeightOneSpectrum.ext ((w.under (𝓞 ℚ)).isMaximal.eq_of_le
          v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)))
      rw [emultiplicity_pow v.prime, emultiplicity_eq_zero.mpr hnd, mul_zero]
  have h := (Finset.emultiplicity_prod v.prime s (fun w ↦ N (w.maxPowDividing I))).symm
  rw [hfac, (Ideal.finiteMultiplicity v.isPrime.ne_top
    (mt (Ideal.relNorm_eq_bot_iff (R := 𝓞 ℚ)).mp hI)).emultiplicity_eq_multiplicity] at h
  simp only [hmult, ← Finset.sum_filter] at h
  exact_mod_cast h.symm

/-- The normalized norm of an integer at a finite place is the inverse residue
cardinality raised to its multiplicity. -/
private theorem norm_int_finitePlace {K : Type*} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {z : 𝓞 K} (hz : z ≠ 0) :
    ‖algebraMap K (w.adicCompletion K) (z : K)‖ =
      (w.asIdeal.absNorm : ℝ)⁻¹ ^ multiplicity w.asIdeal (Ideal.span {z}) := by
  have h := (FinitePlace.mk w).apply_mul_absNorm_pow_eq_one hz
  rw [FinitePlace.maximalIdeal_mk, FinitePlace.mk_apply] at h
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h

/-- The finite-place norm identity for nonzero field integers. -/
private theorem norm_fieldNorm_ratFinitePlace_int (v : HeightOneSpectrum (𝓞 ℚ))
    {z : 𝓞 F} (hz : z ≠ 0) :
    ‖algebraMap ℚ (v.adicCompletion ℚ) (Algebra.norm ℚ (z : F))‖ =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
        ‖algebraMap F (w.adicCompletion F) (z : F)‖ := by
  let I : Ideal (𝓞 F) := Ideal.span {z}
  have hI : I ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hz
  let y := Algebra.intNorm (𝓞 ℚ) (𝓞 F) z
  have hy : (y : ℚ) = Algebra.norm ℚ (z : F) := Algebra.algebraMap_intNorm z
  have hy0 : y ≠ 0 := by
    intro h
    apply (Algebra.norm_ne_zero_iff.mpr (by exact_mod_cast hz) : Algebra.norm ℚ (z : F) ≠ 0)
    rw [← hy, h]
    rfl
  rw [← hy, norm_int_finitePlace v hy0, ← Ideal.relNorm_singleton]
  change (v.asIdeal.absNorm : ℝ)⁻¹ ^ multiplicity v.asIdeal (Ideal.relNorm (𝓞 ℚ) I) = _
  rw [multiplicity_relNorm_rat F v I hI]
  let s := (Ideal.hasFiniteMulSupport hI).toFinset
  let p := (v.asIdeal.absNorm : ℝ)⁻¹
  rw [← Finset.prod_pow_eq_pow_sum]
  symm
  have hprod : (∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
      ‖algebraMap F (w.adicCompletion F) (z : F)‖) =
      ∏ w ∈ s with w.under (𝓞 ℚ) = v, ‖algebraMap F (w.adicCompletion F) (z : F)‖ := by
    apply finprod_cond_eq_prod_of_cond_iff
    intro w hw
    rw [Finset.mem_filter]
    refine ⟨fun h ↦ ⟨(Ideal.hasFiniteMulSupport hI).mem_toFinset.mpr ?_, h⟩, And.right⟩
    intro hOne
    apply hw
    change w.maxPowDividing (Ideal.span {z}) = 1 at hOne
    change ‖FinitePlace.embedding w (algebraMap (𝓞 F) F z)‖ = 1
    simpa only [hOne, map_one, Nat.cast_one, mul_one] using
      HeightOneSpectrum.embedding_mul_absNorm F w hz
  rw [hprod]
  apply Finset.prod_congr rfl
  intro w hw
  have huv := (Finset.mem_filter.mp hw).2
  have : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal huv.symm⟩
  have hcard := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  rw [norm_int_finitePlace w hz]
  change (w.asIdeal.absNorm : ℝ)⁻¹ ^ multiplicity w.asIdeal I =
    p ^ (multiplicity w.asIdeal I * w.asIdeal.inertiaDeg (𝓞 ℚ))
  rw [← hcard, Nat.cast_pow, ← inv_pow, ← pow_mul, Nat.mul_comm]

/-- The places of a number field above a fixed rational finite place form a finite set. -/
private theorem finite_finitePlacesOver_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    {w : HeightOneSpectrum (𝓞 F) | w.under (𝓞 ℚ) = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 F)).subset ?_).of_finite_image
    (HeightOneSpectrum.asIdeal_injective.injOn)
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩⟩

/-- The absolute value of a field norm at a rational finite prime is the product of
the normalized absolute values of the element at the primes above it. -/
private theorem norm_fieldNorm_ratFinitePlace (v : HeightOneSpectrum (𝓞 ℚ)) (x : F) :
    ‖algebraMap ℚ (v.adicCompletion ℚ) (Algebra.norm ℚ x)‖ =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
        ‖algebraMap F (w.adicCompletion F) x‖ := by
  let s := (finite_finitePlacesOver_rat F v).toFinset
  have hprod (a : F) : (∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v),
      ‖algebraMap F (w.adicCompletion F) a‖) =
      ∏ w ∈ s, ‖algebraMap F (w.adicCompletion F) a‖ :=
    finprod_mem_eq_finite_toFinset_prod _ (finite_finitePlacesOver_rat F v)
  by_cases hx : x = 0
  · subst x
    have := v.isMaximal
    obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) v.asIdeal
    let w : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
    have hw : w.under (𝓞 ℚ) = v := HeightOneSpectrum.ext hPv.over.symm
    rw [Algebra.norm_zero, map_zero, norm_zero, hprod]
    symm
    exact Finset.prod_eq_zero ((finite_finitePlacesOver_rat F v).mem_toFinset.mpr hw)
      (by rw [map_zero, norm_zero])
  · obtain ⟨z, t, ht, hzt⟩ := IsFractionRing.div_surjective (𝓞 F) x
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hz : z ≠ 0 := by
      intro h
      exact hx (by rw [← hzt, h, map_zero, zero_div])
    have hnorm (a b : F) : Algebra.norm ℚ (a / b) = Algebra.norm ℚ a / Algebra.norm ℚ b := by
      simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
    rw [← hzt, hnorm, map_div₀, norm_div, norm_fieldNorm_ratFinitePlace_int F v hz,
      norm_fieldNorm_ratFinitePlace_int F v ht0, hprod, hprod, hprod]
    simp only [map_div₀, norm_div, Finset.prod_div_distrib]


open scoped RestrictedProduct in
/-- At each rational finite place, the adelic determinant has absolute value equal to
the product of the normalized local factors above that place. -/
theorem rationalAdeleNorm_finitePlace (v : HeightOneSpectrum (𝓞 ℚ)) (a : 𝔸[F]) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    ‖(Algebra.norm 𝔸[ℚ] a).2 v‖ =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v), ‖a.2 w‖ := by
  let p : 𝔸[ℚ] →+* v.adicCompletion ℚ :=
    (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletion ℚ) v).comp
      (RingHom.snd _ _)
  let e : v.adicCompletion ℚ → 𝔸ᶠ[ℚ] := fun t ↦ ⟨Pi.single v t, by
    filter_upwards [Filter.eventually_cofinite_ne v] with w hw
    rw [Pi.single_eq_of_ne hw]
    exact (w.adicCompletionIntegers ℚ).zero_mem⟩
  have he : Continuous e := by
    apply continuous_restrictedProduct_of_uniform
    · intro w
      change Continuous (fun t : v.adicCompletion ℚ ↦ Pi.single v t w)
      by_cases hw : w = v
      · subst w
        simp only [Pi.single_eq_same]
        exact continuous_id
      · simp only [Pi.single_eq_of_ne hw]
        exact continuous_const
    · filter_upwards [Filter.eventually_cofinite_ne v] with w hw t
      change Pi.single v t w ∈ w.adicCompletionIntegers ℚ
      rw [Pi.single_eq_of_ne hw]
      exact (w.adicCompletionIntegers ℚ).zero_mem
  let r : 𝔸[ℚ] := (0, e 1)
  let g (x : 𝔸[F]) := ∏ᶠ (w : HeightOneSpectrum (𝓞 F)) (_ : w.under (𝓞 ℚ) = v), ‖x.2 w‖
  have hprod (x : 𝔸[F]) :
      g x = ∏ w ∈ (finite_finitePlacesOver_rat F v).toFinset, ‖x.2 w‖ :=
    finprod_mem_eq_finite_toFinset_prod _ (finite_finitePlacesOver_rat F v)
  have hg : Continuous g := by
    change Continuous (fun x ↦ g x)
    simp only [hprod]
    exact continuous_finsetProd _ fun w _ ↦ ((RestrictedProduct.continuous_eval w).comp
      continuous_snd).norm
  refine rationalAdeleNorm_compare F p (fun t ↦ (0, e t)) (continuous_const.prodMk he)
    (v.denseRange_algebraMap ℚ) r ?_ norm continuous_norm g hg ?_
    (norm_fieldNorm_ratFinitePlace F v) a
  · intro c
    refine Prod.ext ?_ ?_
    · change (0 : InfiniteAdeleRing ℚ) * 0 = 0 * c.1
      simp
    · apply FiniteAdeleRing.ext
      intro w
      change Pi.single v 1 w * Pi.single v (c.2 v) w = Pi.single v 1 w * c.2 w
      by_cases hw : w = v
      · subst w
        simp
      · simp [Pi.single_eq_of_ne hw]
  · intro x
    simp only [hprod]
    apply Finset.prod_congr rfl
    intro w hw
    have h := (finite_finitePlacesOver_rat F v).mem_toFinset.mp hw
    have hwv : v.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F)) := by
      rw [← h]
      rfl
    have hr : (r.2 v : v.adicCompletion ℚ) = 1 := Pi.single_eq_same v 1
    have hf := (rationalAdeleEmbedding_spec F).2.2.2 v w hwv (r - 1)
      (by change r.2 v - 1 = 0; rw [hr, sub_self])
    rw [map_sub, map_one] at hf
    change (rationalAdeleEmbedding F r).2 w - 1 = 0 at hf
    change ‖(rationalAdeleEmbedding F r).2 w * x.2 w‖ = ‖x.2 w‖
    rw [sub_eq_zero.mp hf, one_mul]

/-- The finite product of projected determinant norms is the finite factor
of the idelic norm on the original idele. -/
private theorem relativeIdeleNormRat_finite (a : 𝕀[F]) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖(relativeIdeleNormRat F a).val.2 v‖) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖a.val.2 w‖ := by
  let f (w : HeightOneSpectrum (𝓞 F)) := ‖a.val.2 w‖
  have hf : f.HasFiniteMulSupport := ((ideleNorm_spec F).1 a).1
  rw [finprod_eq_prod f hf, ← finprod_prod_filter (HeightOneSpectrum.under (𝓞 ℚ)) hf.toFinset f]
  apply finprod_congr
  intro v
  refine (rationalAdeleNorm_finitePlace F v a.val).trans ?_
  apply finprod_cond_eq_prod_of_cond_iff f
  intro w hw
  rw [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨hf.mem_toFinset.mpr hw, h⟩, And.right⟩

/-- Paper: Lemma A.2.2.2, p. 546. Taking the rational idelic norm after the relative
norm gives the idelic norm of the original idele. -/
theorem ideleNorm_comp_relativeIdeleNormRat :
    (ideleNorm ℚ).comp (relativeIdeleNormRat F) = ideleNorm F := by
  apply MonoidHom.ext
  intro a
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm ℚ (relativeIdeleNormRat F a)).val : ℝ) = ((ideleNorm F a).val : ℝ)
  rw [((ideleNorm_spec ℚ).1 _).2, ((ideleNorm_spec F).1 a).2, relativeIdeleNormRat_finite F a]
  rw [← InfiniteAdeleRing.norm_def, ← InfiniteAdeleRing.norm_def]
  rw [show ‖(relativeIdeleNormRat F a).val.1‖ = ‖a.val.1‖ from
    rationalAdeleNorm_infinite F a.val]

end RelativeNorm

/-- Paper: Example A.2.1.3, p. 546. Rational translates of the compact closure
of the fundamental domain give a countable compact cover of the rational adeles. -/
private theorem rationalAdele_sigmaCompactSpace : SigmaCompactSpace 𝔸[ℚ] := by
  let b := RingOfIntegers.basis ℚ
  let D := adeleFundamentalDomain ℚ b
  let K (q : ℚ) := algebraMap ℚ 𝔸[ℚ] q +ᵥ closure D
  refine SigmaCompactSpace.of_countable (Set.range K) (Set.countable_range K) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact IsCompact.vadd _ (adeleFundamentalDomain_precompact ℚ b)
  · rw [Set.sUnion_range]
    exact eq_top_mono (Set.iUnion_mono fun _ ↦ Set.vadd_set_mono (subset_closure (s := D)))
      (adeleFundamentalDomain_cover ℚ b)

open scoped RestrictedProduct in
/-- The normalized adelic trace gives a continuous retraction of scalar extension
on the adele rings. -/
private theorem rationalAdeleEmbedding_isClosedEmbedding :
    IsClosedEmbedding (rationalAdeleEmbedding F) := by
  let : Algebra 𝔸[ℚ] 𝔸[F] := (rationalAdeleEmbedding F).toAlgebra
  have hF : Continuous (algebraMap 𝔸[ℚ] 𝔸[F]) := (rationalAdeleEmbedding_spec F).1
  have : T2Space 𝔸[F] := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  have : LocallyCompactSpace 𝔸[F] := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : SigmaCompactSpace 𝔸[ℚ] := rationalAdele_sigmaCompactSpace
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  let e := b.equivFun.symm
  have he : Continuous e := by
    change Continuous (fun a ↦ e a)
    simp only [e, Module.Basis.equivFun_symm_apply, Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ ↦
      (hF.comp (continuous_apply i)).mul continuous_const
  -- The open mapping theorem gives continuity of the inverse coordinate map.
  have hcoords : Continuous e.symm :=
    e.toEquiv.continuous_symm_iff.mpr (e.toAddMonoidHom.isOpenMap_of_sigmaCompact e.surjective he)
  let tr := Algebra.trace 𝔸[ℚ] 𝔸[F]
  have htr' : Continuous (fun a ↦ tr (e a)) := by
    simp only [e, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const
  have htr : Continuous tr :=
    (htr'.comp hcoords).congr (fun x ↦ congrArg tr (e.apply_symm_apply x))
  let d := Module.finrank ℚ F
  let c := algebraMap ℚ 𝔸[ℚ] (d : ℚ)⁻¹
  have hleft : LeftInverse (fun x ↦ c * tr x) (algebraMap 𝔸[ℚ] 𝔸[F]) := by
    intro a
    change c * tr (algebraMap 𝔸[ℚ] 𝔸[F] a) = a
    rw [Algebra.trace_algebraMap_of_basis b, Fintype.card_fin, nsmul_eq_mul]
    change c * ((d : 𝔸[ℚ]) * a) = a
    rw [← mul_assoc, ← map_natCast (algebraMap ℚ 𝔸[ℚ]) d, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := F)).ne'),
      map_one, one_mul]
  exact hleft.isClosedEmbedding (continuous_const.mul htr) hF

open scoped RestrictedProduct in
/-- Paper: Lemma A.2.2.2, p. 546. Scalar extension embeds the rational ideles as a
closed subgroup of the ideles of the field. -/
theorem rationalIdeleEmbedding_isClosedEmbedding :
    IsClosedEmbedding (Units.map (rationalAdeleEmbedding F).toMonoidHom) := by
  have : T2Space 𝔸[ℚ] := by
    change T2Space (((v : InfinitePlace ℚ) → v.Completion) ×
      (Πʳ v : HeightOneSpectrum (𝓞 ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
    infer_instance
  exact (rationalAdeleEmbedding_isClosedEmbedding F).units_map

/-- Paper: Lemma A.2.2.2, p. 546. The relative norm of an extended rational
idele is the original idele raised to the field degree. -/
theorem relativeIdeleNormRat_on_rational (g : 𝕀[ℚ]) :
    relativeIdeleNormRat F (Units.map (rationalAdeleEmbedding F).toMonoidHom g) =
      g ^ Module.finrank ℚ F := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  apply Units.ext
  change Algebra.norm 𝔸[ℚ] (algebraMap 𝔸[ℚ] 𝔸[F] g.val) = g.val ^ Module.finrank ℚ F
  simpa only [Fintype.card_fin] using Algebra.norm_algebraMap_of_basis b g.val

/-- Paper: Definition A.2.2.3, p. 547. The canonical section takes the positive
root of order the field degree, applies the rational section and extends scalars. -/
def canonicalIdeleNormSection : ℝ≥0ˣ →* 𝕀[F] :=
  (Units.map (rationalAdeleEmbedding F).toMonoidHom).comp
    (ratIdeleNormSection.comp (Units.map (NNReal.rpowMonoidHom (Module.finrank ℚ F : ℝ)⁻¹)))

/-- Paper: Lemma A.2.2.4, p. 547. The canonical homomorphism is continuous. -/
theorem canonicalIdeleNormSection_continuous : Continuous (canonicalIdeleNormSection F) := by
  simp only [canonicalIdeleNormSection, MonoidHom.coe_comp]
  exact ((rationalAdeleEmbedding_spec F).1.units_map _).comp
    (ratIdeleNormSection_continuous.comp
      ((NNReal.continuous_rpow_const (by positivity)).units_map _))

/-- Paper: Lemma A.2.2.4, p. 547. The canonical homomorphism splits the idelic norm. -/
theorem canonicalIdeleNormSection_rightInverse :
    RightInverse (canonicalIdeleNormSection F) (ideleNorm F) := by
  intro t
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  let root := Units.map (NNReal.rpowMonoidHom (Module.finrank ℚ F : ℝ)⁻¹) t
  let g := ratIdeleNormSection root
  have hrelative : relativeIdeleNormRat F (canonicalIdeleNormSection F t) =
      g ^ Module.finrank ℚ F := by
    apply Units.ext
    change Algebra.norm 𝔸[ℚ] (algebraMap 𝔸[ℚ] 𝔸[F] g.val) = g.val ^ Module.finrank ℚ F
    simpa only [Fintype.card_fin] using Algebra.norm_algebraMap_of_basis b g.val
  rw [← ideleNorm_comp_relativeIdeleNormRat, MonoidHom.comp_apply, hrelative, map_pow,
    show ideleNorm ℚ g = root from ratIdeleNormSection_rightInverse root]
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow t.val (Module.finrank_pos (R := ℚ) (M := F)).ne'

/-- Paper: Lemma A.2.2.4, p. 547. Every infinite component of the canonical section
is the positive real root of order the field degree, viewed in the local field. -/
theorem canonicalIdeleNormSection_infinite (t : ℝ≥0ˣ) (v : InfinitePlace F) :
    extensionEmbedding v ((canonicalIdeleNormSection F t).val.1 v) =
      (((t.val : ℝ) ^ (Module.finrank ℚ F : ℝ)⁻¹ : ℝ) : ℂ) := by
  let e := ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let a (x : ℝ) : 𝔸[ℚ] := (Pi.mulSingle Rat.infinitePlace (e.symm x), 1)
  let f := rationalAdeleEmbedding F
  have hf := rationalAdeleEmbedding_spec F
  let j (x : ℝ) : ℂ := extensionEmbedding v ((f (a x)).1 v)
  have ha : Continuous a :=
    ((continuous_mulSingle (A := InfinitePlace.Completion) Rat.infinitePlace).comp
      (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous).prodMk continuous_const
  have hj : Continuous j :=
    (isometry_extensionEmbedding v).continuous.comp
      ((continuous_apply v).comp (continuous_fst.comp (hf.1.comp ha)))
  have hreal : j = Complex.ofReal := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).equalizer hj Complex.continuous_ofReal
    funext q
    have hdiag : (a (q : ℝ)).1 = (algebraMap ℚ 𝔸[ℚ] q).1 := by
      funext w
      obtain rfl := Subsingleton.elim w Rat.infinitePlace
      change Pi.mulSingle Rat.infinitePlace (e.symm (q : ℝ)) Rat.infinitePlace =
        algebraMap ℚ Rat.infinitePlace.Completion q
      simp only [Pi.mulSingle_eq_same, map_ratCast, eq_ratCast]
    change extensionEmbedding v ((f (a (q : ℝ))).1 v) = ((q : ℝ) : ℂ)
    rw [rationalAdeleEmbedding_fst_eq F _ _ hdiag, hf.2.1]
    change extensionEmbedding v (algebraMap F v.Completion (algebraMap ℚ F q)) = ((q : ℝ) : ℂ)
    simp only [eq_ratCast, map_ratCast, Complex.ofReal_ratCast]
  change j ((t.val : ℝ) ^ (Module.finrank ℚ F : ℝ)⁻¹) = _
  exact congrFun hreal _

/-- Paper: Lemma A.2.2.4, p. 547. The finite part of the canonical section is one. -/
theorem canonicalIdeleNormSection_finite (t : ℝ≥0ˣ) :
    (canonicalIdeleNormSection F t).val.2 = 1 := by
  apply FiniteAdeleRing.ext
  intro w
  let v := w.under (𝓞 ℚ)
  let a : 𝔸[ℚ] := (ratIdeleNormSection
    (Units.map (NNReal.rpowMonoidHom (Module.finrank ℚ F : ℝ)⁻¹) t)).val
  let f := (RestrictedProduct.evalRingHom (fun u : HeightOneSpectrum (𝓞 F) ↦
    u.adicCompletion F) w).comp ((RingHom.snd _ _).comp (rationalAdeleEmbedding F))
  have ha : (a - 1).2 v = 0 := by
    change (1 : v.adicCompletion ℚ) - 1 = 0
    exact sub_self 1
  have h := (rationalAdeleEmbedding_spec F).2.2.2 v w rfl (a - 1) ha
  change f (a - 1) = 0 at h
  change f a = 1
  simpa only [map_sub, map_one, sub_eq_zero] using h

/-- Paper: Definition A.2.2.5, p. 547. This local homomorphism sends a positive real
to its specified real power inside the completion at an infinite place. -/
def infinitePlaceRealPower (v : InfinitePlace F) (r : ℝ) : ℝ≥0ˣ →* v.Completionˣ :=
  let realScalars := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace F))
  let atPlace := (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v).comp realScalars
  Units.map ((atPlace.comp NNReal.toRealHom).toMonoidHom.comp (NNReal.rpowMonoidHom r))

/-- Paper: Definition A.2.2.5, p. 547. Under the archimedean embedding the value
is the positive real power itself, including at a complex place. -/
theorem infinitePlaceRealPower_apply (v : InfinitePlace F) (r : ℝ) (t : ℝ≥0ˣ) :
    extensionEmbedding v (infinitePlaceRealPower F v r t).val = (((t.val : ℝ) ^ r : ℝ) : ℂ) := by
  let x : ℝ := (t.val : ℝ) ^ r
  let y := algebraMap ℝ (mixedEmbedding.mixedSpace F) x
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  change extensionEmbedding v (e.symm y v) = (x : ℂ)
  have h := e.apply_symm_apply y
  by_cases hv : v.IsReal
  · simpa only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, y, Prod.algebraMap_apply,
      Pi.algebraMap_apply, Algebra.algebraMap_self_apply, extensionEmbeddingOfIsReal_apply] using
      congrArg (fun z : mixedEmbedding.mixedSpace F => (z.1 ⟨v, hv⟩ : ℂ)) h
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    simpa only [e, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, y, Prod.algebraMap_apply,
      Pi.algebraMap_apply] using!
      congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩) h

/-- Paper: Definition A.2.2.5, p. 547. The single-place section inserts the positive
root of order the local degree at the chosen infinite place and one elsewhere. -/
def singlePlaceIdeleNormSection (v : InfinitePlace F) : ℝ≥0ˣ →* 𝕀[F] :=
  (IdeleGroup.ofCompletion (𝓞 F) F v).comp (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹)

/-- Paper: Lemma A.2.2.6, p. 547. The section at one infinite place is continuous. -/
theorem singlePlaceIdeleNormSection_continuous (v : InfinitePlace F) :
    Continuous (singlePlaceIdeleNormSection F v) := by
  unfold singlePlaceIdeleNormSection IdeleGroup.ofCompletion
  simp only [MonoidHom.coe_comp]
  apply Continuous.comp
  · apply Continuous.units_map
    exact (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  · apply Continuous.of_coeHom_comp
    apply (isometry_extensionEmbedding v).isEmbedding.continuous_iff.mpr
    change Continuous (fun t : ℝ≥0ˣ ↦
      extensionEmbedding v (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ t).val)
    simp only [infinitePlaceRealPower_apply]
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by positivity : 0 ≤ (v.mult : ℝ)⁻¹)).comp
        (NNReal.continuous_coe.comp Units.continuous_val))

/-- Paper: Lemma A.2.2.6, p. 547. The section at one infinite place splits the idelic norm. -/
theorem singlePlaceIdeleNormSection_rightInverse (v : InfinitePlace F) :
    RightInverse (singlePlaceIdeleNormSection F v) (ideleNorm F) := by
  intro t
  apply Units.ext
  apply NNReal.eq
  rw [((ideleNorm_spec F).1 (singlePlaceIdeleNormSection F v t)).2]
  let x := (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ t).val
  change (∏ w : InfinitePlace F, ‖Pi.mulSingle v x w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(1 : w.adicCompletion F)‖) = (t.val : ℝ)
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ _), Pi.mulSingle_eq_same]
  · have ht : 0 ≤ (t.val : ℝ) := t.val.coe_nonneg
    have hx : ‖x‖ = (t.val : ℝ) ^ (v.mult : ℝ)⁻¹ := by
      rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) x]
      change ‖extensionEmbedding v (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ t).val‖ = _
      rw [infinitePlaceRealPower_apply, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg ht _)]
    rw [hx, ← Real.rpow_mul_natCast ht, inv_mul_cancel₀ v.mult_coe_ne_zero, Real.rpow_one]
  · intro w _ hw
    simp only [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]

/-- Paper: Definition A.2.2.7, p. 547. The diagonal section inserts a positive real
power at every infinite place, dividing the exponent by both the local degree and the
number of infinite places. Its finite components are one. -/
def diagonalIdeleNormSection : ℝ≥0ˣ →* 𝕀[F] :=
  ∏ v : InfinitePlace F, (IdeleGroup.ofCompletion (𝓞 F) F v).comp
    (infinitePlaceRealPower F v ((v.mult : ℝ) * Fintype.card (InfinitePlace F))⁻¹)

/-- Paper: Lemma A.2.2.8, p. 547. The diagonal homomorphism is continuous. -/
theorem diagonalIdeleNormSection_continuous : Continuous (diagonalIdeleNormSection F) := by
  simp only [diagonalIdeleNormSection, MonoidHom.coe_finsetProd, Finset.prod_fn,
    MonoidHom.coe_comp]
  refine continuous_finsetProd _ fun v _ ↦ ?_
  apply Continuous.comp
  · unfold IdeleGroup.ofCompletion
    apply Continuous.units_map
    exact (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  · apply Continuous.of_coeHom_comp
    apply (isometry_extensionEmbedding v).isEmbedding.continuous_iff.mpr
    change Continuous (fun t : ℝ≥0ˣ ↦ extensionEmbedding v (infinitePlaceRealPower F v _ t).val)
    simp only [infinitePlaceRealPower_apply]
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by positivity)).comp
        (NNReal.continuous_coe.comp Units.continuous_val))

/-- Paper: Lemma A.2.2.8, p. 547. The diagonal homomorphism splits the idelic norm. -/
theorem diagonalIdeleNormSection_rightInverse :
    RightInverse (diagonalIdeleNormSection F) (ideleNorm F) := by
  intro t
  let n := Fintype.card (InfinitePlace F)
  let root := Units.map (NNReal.rpowMonoidHom (n : ℝ)⁻¹) t
  have hpower (v : InfinitePlace F) :
      infinitePlaceRealPower F v ((v.mult : ℝ) * n)⁻¹ t =
        infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ root := by
    apply Units.ext
    apply (isometry_extensionEmbedding v).injective
    rw [infinitePlaceRealPower_apply, infinitePlaceRealPower_apply]
    apply congrArg Complex.ofReal
    change ((t.val : ℝ) ^ ((v.mult : ℝ) * n)⁻¹ : ℝ) =
      (((t.val ^ (n : ℝ)⁻¹ : ℝ≥0) : ℝ) ^ (v.mult : ℝ)⁻¹ : ℝ)
    rw [NNReal.coe_rpow, ← Real.rpow_mul t.val.coe_nonneg, mul_inv_rev]
  have hsection : diagonalIdeleNormSection F t =
      ∏ v : InfinitePlace F, singlePlaceIdeleNormSection F v root := by
    simp only [diagonalIdeleNormSection, MonoidHom.finsetProd_apply, MonoidHom.comp_apply,
      singlePlaceIdeleNormSection]
    exact Finset.prod_congr rfl fun v _ ↦ congrArg _ (hpower v)
  have hnorm (v : InfinitePlace F) : ideleNorm F (singlePlaceIdeleNormSection F v root) = root :=
    singlePlaceIdeleNormSection_rightInverse F v root
  rw [hsection, map_prod]
  simp only [hnorm, Finset.prod_const, Finset.card_univ]
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow t.val Fintype.card_ne_zero

-- TODO(paper-gap): The hypothesis of A.2.2.9 says only "continuous section". A
-- continuous right inverse need not even preserve one. The start of §A.2.2 specifies homomorphisms.

/-- Paper: Lemma A.2.2.9, p. 547. Multiplying a section value by a norm-one idele
identifies the product of the positive reals and the kernel with the full topological group.
Deviation: We use a homomorphic section, as in the introduction to §A.2.2. -/
theorem ideleNormSection_product (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s)
    (hn : RightInverse s (ideleNorm F)) :
    ∃ e : (ℝ≥0ˣ × (ideleNorm F).ker) ≃ₜ* 𝕀[F], ∀ t g, e (t, g) = s t * g.val := by
  have hNorm : Continuous (ideleNorm F) := (ideleGroup_topology F).2.2.2.2.1
  have hKer (g : 𝕀[F]) : (s (ideleNorm F g))⁻¹ * g ∈ (ideleNorm F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hn _, inv_mul_cancel]
  let e : (ℝ≥0ˣ × (ideleNorm F).ker) ≃ₜ* 𝕀[F] :=
    { toFun := fun p ↦ s p.1 * p.2.val
      invFun := fun g ↦ (ideleNorm F g, ⟨(s (ideleNorm F g))⁻¹ * g, hKer g⟩)
      left_inv := by
        rintro ⟨t, g⟩
        have ht : ideleNorm F (s t * g.val) = t := by
          rw [map_mul, hn t, MonoidHom.mem_ker.mp g.property, mul_one]
        refine Prod.ext ht (Subtype.ext ?_)
        change (s (ideleNorm F (s t * g.val)))⁻¹ * (s t * g.val) = g.val
        rw [ht, inv_mul_cancel_left]
      right_inv := fun g ↦ mul_inv_cancel_left (s (ideleNorm F g)) g
      map_mul' := by
        rintro ⟨t, g⟩ ⟨u, h⟩
        change s (t * u) * (g.val * h.val) = (s t * g.val) * (s u * h.val)
        rw [map_mul, mul_mul_mul_comm]
      continuous_toFun := (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := hNorm.prodMk (((hs.comp hNorm).inv.mul continuous_id).subtype_mk hKer) }
  exact ⟨e, fun _ _ ↦ rfl⟩

end NormSections

end RiemannMasullo
