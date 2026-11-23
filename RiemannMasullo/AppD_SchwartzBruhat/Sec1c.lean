module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
public import Mathlib.Analysis.Calculus.Deriv.Basic
import all RiemannMasullo.AppC_LCTVS.Sec2a_part2
import RiemannMasullo.AppC_LCTVS.Sec3a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import RiemannMasullo.ForMathlib.MeasureTheory.Function.ContinuousMapDense
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Barrelled
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Compactness.CompactlyCoherentSpace
import Mathlib.Topology.ContinuousMap.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Symmetric
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Compact
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.TensorProduct.Bounded
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.TensorProduct.StrongDual
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Differential operators, Poisson summation, supports and translations

Masullo, §§D.1.6–D.1.9, pp. 765–783.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal TensorProduct Topology

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section DifferentialOperators

/-- Paper: Definition D.1.6.1, p. 765. The topological Lie algebra is the
space of continuous one-parameter subgroups with the compact-open topology. -/
abbrev LCATopologicalLie (G : Type*) [Group G] [TopologicalSpace G] :=
  Multiplicative ℝ →ₜ* G

/-- Paper: Definition D.1.6.1, p. 765. Each one-parameter subgroup of the real
line is scalar multiplication by its value at time one.
Deviation: Sanity check on the additive real line. -/
theorem lcaTopologicalLie_real (a : LCATopologicalLie (Multiplicative ℝ)) (t : ℝ) :
    (a (Multiplicative.ofAdd t)).toAdd =
      t * (a (Multiplicative.ofAdd 1)).toAdd := by
  let f : ℝ →+ ℝ := AddMonoidHom.toMultiplicative.symm a.toMonoidHom
  have hf : Continuous f := a.continuous
  change f t = t * f 1
  simpa only [smul_eq_mul, mul_one] using map_real_smul f hf t (1 : ℝ)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

-- TODO(paper-gap): D.1.6.4 claims local compactness of the compact-open hom groups.
-- For the countable product of circles the one-parameter subgroup space is ℝ^ℕ.

omit hT2 in
/-- If evaluation identifies `G` with its Pontryagin bidual, transposing character
evaluation gives the inverse to dualizing one-parameter subgroups. -/
theorem lcaTopologicalLie_dual_of_bidual
    (eG : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (heG : ∀ x χ, eG x χ = χ x) :
    ∃ e : LCATopologicalLie G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  let evalReal := pontryaginDual_eval (G := Multiplicative ℝ)
  let eGinv : PontryaginDual (PontryaginDual G) →ₜ* G := eG.symm
  let dual := PontryaginDual.mapHom (Multiplicative ℝ) G
  let inverse (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)) :
      LCATopologicalLie G :=
    eGinv.comp ((PontryaginDual.map b).comp evalReal)
  have hEval (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ))
      (t : Multiplicative ℝ) (χ : PontryaginDual G) : χ (inverse b t) = b χ t := by
    calc
      χ (inverse b t) = eG (inverse b t) χ := (heG _ _).symm
      _ = evalReal t (b χ) := by
        change eG (eG.symm (PontryaginDual.map b (evalReal t))) χ = _
        rw [eG.apply_symm_apply, PontryaginDual.map_apply]
      _ = b χ t := rfl
  have hLeft : Function.LeftInverse inverse dual := by
    intro a
    apply ContinuousMonoidHom.ext
    intro t
    apply eG.injective
    apply PontryaginDual.ext
    intro χ
    rw [heG, heG, hEval (dual a)]
    rfl
  have hRight : Function.RightInverse inverse dual :=
    fun b ↦ ContinuousMonoidHom.ext fun χ ↦ PontryaginDual.ext fun t ↦ hEval b t χ
  have hCont : Continuous inverse :=
    eGinv.continuous_comp_right.comp
      (evalReal.continuous_comp_left.comp
        (PontryaginDual.mapHom (PontryaginDual G) (PontryaginDual (Multiplicative ℝ))).continuous)
  exact ⟨{ toFun := dual
           invFun := inverse
           left_inv := hLeft
           right_inv := hRight
           map_mul' := map_mul dual
           continuous_toFun := dual.continuous
           continuous_invFun := hCont }, fun _ ↦ rfl⟩

/-- Paper: Lemma D.1.6.4, p. 766. Precomposition of characters with a
one-parameter subgroup gives the canonical compact-open topological group isomorphism.
Deviation: The local compactness assertion fails for an infinite product of circles. -/
theorem lcaTopologicalLie_dual :
    ∃ e : LCATopologicalLie G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  obtain ⟨eG, heG⟩ := pontryaginDual_bidual (G := G)
  exact lcaTopologicalLie_dual_of_bidual eG heG

/-- Paper: Definition D.1.6.5, p. 766. Differentiate the orbit curve of a
function along a one-parameter subgroup at time zero. -/
def bruhatDirectionalDeriv (a : LCATopologicalLie G) (f : G → ℂ) (x : G) : ℂ :=
  deriv (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0

omit hTop hT2 hLC in
/-- Paper: Definition D.1.6.5, p. 766. Differentiation along the identity
one-parameter subgroup of the real line recovers the ordinary derivative.
Deviation: Sanity check on the additive real line. -/
theorem bruhatDirectionalDeriv_real
    (a : LCATopologicalLie (Multiplicative ℝ))
    (ha : ∀ t, a (Multiplicative.ofAdd t) = Multiplicative.ofAdd t)
    (f : Multiplicative ℝ → ℂ) (x : ℝ) :
    bruhatDirectionalDeriv a f (Multiplicative.ofAdd x) =
      deriv (f ∘ Multiplicative.ofAdd) x := by
  simp only [bruhatDirectionalDeriv, ha]
  change deriv (fun t : ℝ ↦ (f ∘ Multiplicative.ofAdd) (x + t)) 0 = _
  rw [deriv_comp_const_add, add_zero]

/-- Every point belongs to the open subgroup of a structural pair with the given good subgroup. -/
private theorem exists_bruhatStructuralPair_mem (k : Subgroup G) (hk : IsBruhatGoodSubgroup k)
    (x : G) : ∃ p : BruhatStructuralPair G, OrderDual.ofDual p.val.2 = k ∧ x ∈ p.val.1 := by
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := PontryaginDual G)
  have hCompact : IsCompact (k : Set G) := by
    refine (isClosedEmbedding_pontryaginDual_eval.isCompact_preimage
      (hPolar _ (hk.2.1.mem_nhds (lcaAnnihilator k).one_mem))).of_isClosed_subset hk.1 ?_
    intro y hy χ hχ
    change χ y ∈ Metric.closedBall 1 r
    rw [(mem_lcaAnnihilator_iff k χ).mp hχ ⟨y, hy⟩]
    exact Metric.mem_closedBall_self hr.le
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hK : IsCompact K := (hUc.union hCompact).insert x
  have hK₁ : K ∈ 𝓝 (1 : G) :=
    mem_of_superset hU (subset_union_left.trans (subset_insert _ _))
  have hH : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hK₁ Subgroup.subset_closure)
  have hGen : IsCompactlyGeneratedGroup H :=
    ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK₁,
      IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
        (Subtype.range_coe.symm ▸ Subgroup.subset_closure),
      Subgroup.closure_preimage_eq_top K⟩
  exact ⟨⟨(H, OrderDual.toDual k), hH, hGen, hk,
    fun y hy ↦ Subgroup.subset_closure (mem_insert_of_mem _ (Or.inr hy))⟩,
    rfl, Subgroup.subset_closure (mem_insert _ _)⟩

omit hT2 hLC in
/-- On an elementary presentation of a structural quotient, a translated one-parameter
subgroup lifts to an affine line in the real and torus cover of a single discrete fiber. -/
private theorem contDiff_bruhatOrbit_of_presentation (a : LCATopologicalLie G) {f : G → ℂ}
    (p : BruhatStructuralPair G) {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (e : p.quotient ≃ₜ* Multiplicative (ElementaryLieGroup m n r F))
    (f₀ : p.quotient → ℂ) (hf₀ : ∀ x : p.val.1, f₀ (QuotientGroup.mk x) = f x.val)
    (hCover : ∀ (z : Fin r → ℤ) (b : F),
      ContDiff ℝ 1 (fun xt ↦ f₀ (e.symm (Multiplicative.ofAdd (elementaryCover xt z b)))))
    (x : p.val.1) :
    ContDiff ℝ 1 (fun t : ℝ ↦ f (x.val * a (Multiplicative.ofAdd t))) := by
  have haMem (t : ℝ) : a (Multiplicative.ofAdd t) ∈ p.val.1 := by
    have haCont : Continuous (fun t : ℝ ↦ a (Multiplicative.ofAdd t)) := a.continuous
    exact isPreconnected_range haCont |>.subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨0, map_one a⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let aH : Multiplicative ℝ →* p.val.1 := a.toMonoidHom.codRestrict p.val.1 haMem
  let q : p.val.1 →* p.quotient := QuotientGroup.mk' _
  let c : ℝ →+ ElementaryLieGroup m n r F :=
    AddMonoidHom.toMultiplicative.symm (e.toMulEquiv.toMonoidHom.comp (q.comp aH))
  have hc : Continuous c :=
    e.continuous.comp (QuotientGroup.continuous_mk.comp (a.continuous.subtype_mk haMem))
  let cR := (AddMonoidHom.fst _ _).comp c
  let cT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp c)
  have hR (t : ℝ) : (c t).1 = t • (c 1).1 := by
    change cR t = t • cR 1
    simpa only [smul_eq_mul, mul_one] using
      map_real_smul cR (continuous_fst.comp hc) t (1 : ℝ)
  choose v hv using fun i : Fin n ↦ exists_addCircle_coe_mul_eq
    ((Pi.evalAddMonoidHom _ i).comp cT) ((continuous_apply i).comp hc.snd.fst)
  have hD (t : ℝ) : (c t).2.2 = 0 := by
    have h := hc.snd.snd.isConst_of_preconnectedSpace t 0
    rw [map_zero c] at h
    exact h
  let y := (e (q x)).toAdd
  obtain ⟨u, hu⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
  let w := (y.1, u)
  let d := ((c 1).1, WithLp.toLp 2 v)
  have hLine (t : ℝ) : elementaryCover (w + t • d) y.2.2.1 y.2.2.2 = y + c t := by
    refine Prod.ext (congrArg (y.1 + ·) (hR t).symm) (Prod.ext ?_ ?_)
    · funext i
      have hui := congrArg (fun z : ElementaryLieGroup m n r F ↦ z.2.1 i) hu
      change ((u i + t * v i : ℝ) : AddCircle (1 : ℝ)) = y.2.1 i + (c t).2.1 i
      rw [AddCircle.coe_add, show (u i : AddCircle (1 : ℝ)) = y.2.1 i from hui, hv i t]
      rfl
    · change y.2.2 = y.2.2 + (c t).2.2
      rw [hD, add_zero]
  have hOrbit (t : ℝ) :
      f (x.val * a (Multiplicative.ofAdd t)) =
        f₀ (e.symm (Multiplicative.ofAdd
          (elementaryCover (w + t • d) y.2.2.1 y.2.2.2))) := by
    rw [hLine]
    change f ((x * aH (Multiplicative.ofAdd t)).val) =
      f₀ (e.symm (e (q x) * e (q (aH (Multiplicative.ofAdd t)))))
    rw [← map_mul, e.symm_apply_apply, ← map_mul]
    exact (hf₀ _).symm
  simp only [hOrbit]
  exact (hCover y.2.2.1 y.2.2.2).comp
    (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- A structural pair can be restricted around a point while keeping its good subgroup,
so that the new quotient has an elementary presentation. The original pair itself
has such a presentation by Lemma D.1.5.2(1). -/
theorem BruhatStructuralPair.exists_elementary_subpair_mem
    (p : BruhatStructuralPair G) (x : p.val.1) :
    ∃ q : BruhatStructuralPair G, q.val.1 ≤ p.val.1 ∧
      OrderDual.ofDual q.val.2 = OrderDual.ofDual p.val.2 ∧
      x.val ∈ q.val.1 ∧ Nonempty (ElementaryLCAPresentation q.quotient) :=
  ⟨p, le_rfl, rfl, x.property, p.elementary⟩

/-- Paper: Definition D.1.6.5, p. 766. For a Bruhat C¹ function the orbit
derivative exists at time zero for every starting point. -/
theorem hasDerivAt_bruhatDirectionalDeriv (a : LCATopologicalLie G) {f : G → ℂ}
    (hf : IsBruhatContDiff 1 f) (x : G) :
    HasDerivAt (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t)))
      (bruhatDirectionalDeriv a f x) 0 := by
  obtain ⟨k, hk, _, hDescent⟩ := hf
  obtain ⟨p, hp, hx⟩ := exists_bruhatStructuralPair_mem k hk x
  obtain ⟨q, _, hq, hxq, ⟨e⟩⟩ := p.exists_elementary_subpair_mem ⟨x, hx⟩
  obtain ⟨f₀, hf₀, hCover⟩ := hDescent q (hq.trans hp)
  have h : ContDiff ℝ 1 (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) :=
    contDiff_bruhatOrbit_of_presentation a q
      (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
      e.equiv f₀ hf₀ (hCover e) ⟨x, hxq⟩
  exact (h.differentiable one_ne_zero 0).hasDerivAt

-- TODO(paper-gap): The proofs of D.1.6.6 and D.1.6.7 use support in an open
-- compactly generated subgroup. A global smooth function need not have such support.

omit hTop hT2 hLC in
/-- Paper: Lemma D.1.6.6, p. 767. On an elementary group, differentiability of
class C¹ on each lifted discrete fiber gives continuity of the orbit derivative. -/
private theorem continuous_elementary_orbitDeriv {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (a : ℝ →+ ElementaryLieGroup m n r F) (ha : Continuous a)
    {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ z b, ContDiff ℝ 1 (fun u ↦ f (elementaryCover u z b))) :
    Continuous (fun x ↦ deriv (fun t ↦ f (x + a t)) 0) := by
  let V := EuclideanSpace ℝ (Fin m)
  let W := EuclideanSpace ℝ (Fin n)
  let D := (Fin r → ℤ) × F
  let aV : ℝ →+ V := (AddMonoidHom.fst _ _).comp a
  have haV : Continuous aV := continuous_fst.comp ha
  have hD (t : ℝ) : (a t).2.2 = 0 := by
    have hc : Continuous (fun t ↦ (a t).2.2) := continuous_snd.comp (continuous_snd.comp ha)
    have hconst : (a t).2.2 = (a 0).2.2 :=
      (isPreconnected_range hc).subsingleton (mem_range_self t) (mem_range_self 0)
    exact hconst.trans (by rw [map_zero]; rfl)
  -- The lift through each circle cover is additive by uniqueness of lifts.
  have hLift (i : Fin n) : ∃ v : ℝ, ∀ t : ℝ, ((t * v : ℝ) : AddCircle (1 : ℝ)) = (a t).2.1 i := by
    let q : ℝ → AddCircle (1 : ℝ) := (↑)
    let g : C(ℝ, AddCircle (1 : ℝ)) :=
      ⟨fun t ↦ (a t).2.1 i, (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp ha))⟩
    have hg0 : q 0 = g 0 := by simp [q, g, a.map_zero]
    have hq := AddCircle.isCoveringMap_coe (1 : ℝ)
    obtain ⟨b, ⟨hb0, hb⟩, _⟩ := hq.existsUnique_continuousMap_lifts g 0 0 hg0
    have hb' (t : ℝ) : q (b t) = (a t).2.1 i := congrFun hb t
    have hadd (s t : ℝ) : b (s + t) = b s + b t := by
      have heq : q ∘ (fun p : ℝ × ℝ ↦ b (p.1 + p.2)) =
          q ∘ (fun p : ℝ × ℝ ↦ b p.1 + b p.2) := by
        funext p
        change q (b (p.1 + p.2)) = q (b p.1 + b p.2)
        rw [show q (b p.1 + b p.2) = q (b p.1) + q (b p.2) from QuotientAddGroup.mk_add _ _ _,
          hb', hb', hb', map_add]
        rfl
      exact congrFun (hq.eq_of_comp_eq (b.continuous.comp (continuous_fst.add continuous_snd))
        ((b.continuous.comp continuous_fst).add (b.continuous.comp continuous_snd))
        heq (0, 0) (by simp [hb0])) (s, t)
    let bHom : ℝ →+ ℝ := ⟨⟨b, hb0⟩, hadd⟩
    refine ⟨b 1, fun t ↦ ?_⟩
    have ht : b t = t * b 1 := by
      change bHom t = t * bHom 1
      simpa only [smul_eq_mul, mul_one] using map_real_smul bHom b.continuous t (1 : ℝ)
    rw [← ht]
    exact hb' t
  choose w hw using hLift
  let v : V × W := (aV 1, WithLp.toLp 2 w)
  have hOrbit (u : V × W) (d : D) (t : ℝ) :
      elementaryCover u d.1 d.2 + a t = elementaryCover (u + t • v) d.1 d.2 := by
    have ht : aV t = t • aV 1 := by
      simpa only [smul_eq_mul, mul_one] using map_real_smul aV haV t (1 : ℝ)
    change (u.1 + aV t, (fun i ↦ (u.2 i : AddCircle (1 : ℝ)) + (a t).2.1 i),
      d + (a t).2.2) = (u.1 + t • v.1, (fun i ↦ ((u.2 i + t * w i : ℝ) : AddCircle (1 : ℝ))), d)
    simp only [ht, v, hD, add_zero, QuotientAddGroup.mk_add, hw]
  let q : (V × W) × D → ElementaryLieGroup m n r F :=
    fun p ↦ elementaryCover p.1 p.2.1 p.2.2
  have hqW : IsOpenQuotientMap (fun u : W ↦ fun i ↦ (u i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  have hq : IsOpenQuotientMap q :=
    (Homeomorph.prodAssoc V (Fin n → AddCircle (1 : ℝ)) D).isOpenQuotientMap.comp
      ((IsOpenQuotientMap.id.prodMap hqW).prodMap IsOpenQuotientMap.id)
  apply hq.continuous_comp_iff.mp
  rw [continuous_iff_continuousAt]
  intro p
  let g (d : D) (u : V × W) := f (elementaryCover u d.1 d.2)
  have hg (d : D) : ContDiff ℝ 1 (g d) := hf d.1 d.2
  have hd : ∀ᶠ p' : (V × W) × D in 𝓝 p, p'.2 = p.2 :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_discrete {p.2}).mem_nhds (mem_singleton _))
  have hEq (u : V × W) (d : D) :
      deriv (fun t ↦ f (elementaryCover u d.1 d.2 + a t)) 0 = fderiv ℝ (g d) u v := by
    have hPath : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have hBase : (fun t : ℝ ↦ u + t • v) 0 = u := by simp
    have hFDeriv := ((hg d).differentiable one_ne_zero (u + (0 : ℝ) • v)).hasFDerivAt
    have hDeriv := (hFDeriv.comp_hasDerivAt 0 hPath).deriv
    simp only [hBase] at hDeriv
    simpa only [Function.comp_def, g, hOrbit] using hDeriv
  refine (((hg p.2).continuous_fderiv_apply one_ne_zero).comp
    (continuous_fst.prodMk (continuous_const (y := v)))).continuousAt.congr ?_
  filter_upwards [hd] with p' hp'
  exact hp' ▸ (hEq p'.1 p'.2).symm

/-- A good subgroup is contained, together with any prescribed point, in an
open compactly generated subgroup. -/
private theorem exists_structuralPair_at (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) (x : G) :
    ∃ p : BruhatStructuralPair G, x ∈ p.val.1 ∧ OrderDual.ofDual p.val.2 = k := by
  let J := lcaAnnihilator k
  let : DiscreteTopology (PontryaginDual G ⧸ J) := QuotientGroup.discreteTopology hk.2.1
  let π : PontryaginDual G →ₜ* (PontryaginDual G ⧸ J) :=
    ⟨QuotientGroup.mk' J, QuotientGroup.continuous_mk⟩
  let eval := pontryaginDual_eval (G := G)
  -- The dual of the discrete quotient is compact, and evaluation is a closed embedding.
  have hkCompact : IsCompact (k : Set G) := by
    have hRange : IsCompact (range (PontryaginDual.map π)) :=
      isCompact_range (PontryaginDual.map π).continuous
    have hkPreimage : (k : Set G) = eval ⁻¹' range (PontryaginDual.map π) := by
      ext y
      change y ∈ k ↔ eval y ∈ range (PontryaginDual.map π)
      rw [← lcaDualAnnihilator_annihilator k hk.1, mem_lcaDualAnnihilator_iff]
      constructor
      · intro hy
        let χ : PontryaginDual (PontryaginDual G ⧸ J) :=
          { toMonoidHom := QuotientGroup.lift J (eval y).toMonoidHom (fun z hz ↦ hy ⟨z, hz⟩)
            continuous_toFun := (QuotientGroup.isQuotientMap_mk J).continuous_iff.mpr
              (eval y).continuous }
        exact ⟨χ, PontryaginDual.ext fun _ ↦ rfl⟩
      · rintro ⟨χ, hχ⟩ z
        change eval y z.val = 1
        rw [← hχ, PontryaginDual.map_apply]
        have hz : π z.val = 1 := (QuotientGroup.eq_one_iff z.val).mpr z.property
        rw [hz, map_one]
    rw [hkPreimage]
    exact isClosedEmbedding_pontryaginDual_eval.isCompact_preimage hRange
  obtain ⟨U, hU, hUnhds⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hSub : K ⊆ (H : Set G) := Subgroup.subset_closure
  have hK : K ∈ 𝓝 (1 : G) :=
    mem_of_superset hUnhds (subset_union_left.trans (subset_insert _ _))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hK hSub)
  have hGenerated : IsCompactlyGeneratedGroup H :=
    ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
        ((hU.union hkCompact).insert x), Subgroup.closure_preimage_eq_top K⟩
  exact ⟨⟨(H, OrderDual.toDual k), hH, hGenerated, hk,
    subset_union_right.trans ((subset_insert _ _).trans hSub)⟩, hSub (mem_insert _ _), rfl⟩

/-- Paper: Lemma D.1.6.6, p. 767. An open structural subgroup can be shrunk around
a prescribed point, keeping the same good subgroup, so that the quotient has an
elementary presentation.
Deviation: Local form of the reduction to elementary groups. The original pair itself
has an elementary quotient by Lemma D.1.5.2(1). -/
theorem BruhatStructuralPair.exists_elementary_refinement (p : BruhatStructuralPair G)
    (x : p.val.1) :
    ∃ q : BruhatStructuralPair G, q.val.1 ≤ p.val.1 ∧ x.val ∈ q.val.1 ∧
      OrderDual.ofDual q.val.2 = OrderDual.ofDual p.val.2 ∧
      Nonempty (ElementaryLCAPresentation q.quotient) :=
  ⟨p, le_rfl, x.property, rfl, p.elementary⟩

/-- Paper: Lemma D.1.6.6, p. 767. A first derivative of a Bruhat C¹ function
is continuous. -/
theorem bruhatDirectionalDeriv_continuous (a : LCATopologicalLie G) {f : G → ℂ}
    (hf : IsBruhatContDiff 1 f) :
    Continuous (bruhatDirectionalDeriv a f) := by
  obtain ⟨k, hk, _, hDescend⟩ := hf
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨p₀, hx₀, hp₀⟩ := exists_structuralPair_at k hk x
  obtain ⟨p, _, hx, hp, ⟨e⟩⟩ := p₀.exists_elementary_refinement ⟨x, hx₀⟩
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend p (hp.trans hp₀)
  let H := p.val.1
  have hH : IsOpen (H : Set G) := p.property.1
  have ha (t : Multiplicative ℝ) : a t ∈ H := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    have hRange : IsPreconnected (range a) := isPreconnected_range a.continuous
    exact hRange.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩
      ⟨1, ⟨1, map_one a⟩, H.one_mem⟩ (mem_range_self t)
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let φ := e.equiv
  let aH : Multiplicative ℝ →* H := a.toMonoidHom.codRestrict H ha
  let q : H →* p.quotient := QuotientGroup.mk' _
  let aq : Multiplicative ℝ →* Multiplicative E := φ.toMulEquiv.toMonoidHom.comp (q.comp aH)
  let aE : ℝ →+ E := AddMonoidHom.toMultiplicative.symm aq
  have hq : Continuous q := QuotientGroup.continuous_mk
  have hφ : Continuous φ := φ.continuous
  have haE : Continuous aE := hφ.comp (hq.comp (a.continuous.subtype_mk ha))
  let g : E → ℂ := fun y ↦ f₀ (φ.symm (Multiplicative.ofAdd y))
  have hDeriv := continuous_elementary_orbitDeriv aE haE (f := g) (hSmooth e)
  have hCont : Continuous (fun y : H ↦ deriv (fun t : ℝ ↦ g ((φ (q y)).toAdd + aE t)) 0) :=
    hDeriv.comp (hφ.comp hq)
  have hEq (y : H) :
      deriv (fun t : ℝ ↦ g ((φ (q y)).toAdd + aE t)) 0 = bruhatDirectionalDeriv a f y.val := by
    unfold bruhatDirectionalDeriv
    congr 1
    funext t
    let b := aH (Multiplicative.ofAdd t)
    change f₀ (φ.symm (φ (q y) * φ (q b))) = f (y.val * a (Multiplicative.ofAdd t))
    rw [← show φ (q y * q b) = φ (q y) * φ (q b) from φ.map_mul _ _,
      φ.symm_apply_apply, ← map_mul q]
    exact hf₀ (y * b)
  rw [show (fun y : H ↦ deriv (fun t : ℝ ↦ g ((φ (q y)).toAdd + aE t)) 0) =
      bruhatDirectionalDeriv a f ∘ (Subtype.val : H → G) from funext hEq] at hCont
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
    (hCont.continuousAt (x := (⟨x, hx⟩ : H)))

omit hTop hT2 hLC in
/-- Translation by an elementary one-parameter subgroup lifts on each discrete fiber
to translation by a real multiple of a fixed vector. -/
private theorem exists_elementaryCover_translation {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (c : ℝ →+ ElementaryLieGroup m n r F) (hc : Continuous c) :
    ∃ v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n),
      ∀ u (z : Fin r → ℤ) (b : F) (t : ℝ),
        elementaryCover (u + t • v) z b = elementaryCover u z b + c t := by
  let cR := (AddMonoidHom.fst _ _).comp c
  let cT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp c)
  have hR (t : ℝ) : (c t).1 = t • (c 1).1 := by
    change cR t = t • cR 1
    simpa only [smul_eq_mul, mul_one] using map_real_smul cR hc.fst t (1 : ℝ)
  choose w hw using fun i : Fin n ↦ exists_addCircle_coe_mul_eq
    ((Pi.evalAddMonoidHom _ i).comp cT) ((continuous_apply i).comp hc.snd.fst)
  have hD (t : ℝ) : (c t).2.2 = 0 := by
    have h := hc.snd.snd.isConst_of_preconnectedSpace t 0
    rw [map_zero c] at h
    exact h
  refine ⟨((c 1).1, WithLp.toLp 2 w), fun u z b t ↦ ?_⟩
  refine Prod.ext (congrArg (u.1 + ·) (hR t).symm) (Prod.ext ?_ ?_)
  · funext i
    change ((u.2 i + t * w i : ℝ) : AddCircle (1 : ℝ)) =
      (u.2 i : AddCircle (1 : ℝ)) + (c t).2.1 i
    rw [AddCircle.coe_add, hw i t]
    rfl
  · change (z, b) = (z, b) + (c t).2.2
    rw [hD, add_zero]

omit hT2 hLC in
/-- On each structural quotient, differentiation along a one-parameter subgroup
lowers the order of Bruhat differentiability by one and preserves the good subgroup. -/
private theorem IsBruhatContDiff.directionalDeriv {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff (p + 1) f) (a : LCATopologicalLie G) :
    IsBruhatContDiff p (bruhatDirectionalDeriv a f) := by
  obtain ⟨k, hk, hInv, hDescent⟩ := hf
  refine ⟨k, hk, ?_, ?_⟩
  · intro h x
    simp only [bruhatDirectionalDeriv, mul_assoc, hInv]
  · intro q hq
    obtain ⟨f₀, hf₀, hSmooth⟩ := hDescent q hq
    have ha (t : Multiplicative ℝ) : a t ∈ q.val.1 := by
      let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
      exact (isPreconnected_range a.continuous).subset_isClopen
        ⟨q.val.1.isClosed_of_isOpen q.property.1, q.property.1⟩
        ⟨1, ⟨1, map_one a⟩, q.val.1.one_mem⟩ (mem_range_self t)
    let aH := a.toMonoidHom.codRestrict q.val.1 ha
    let π : q.val.1 →* q.quotient := QuotientGroup.mk' _
    let aQ := π.comp aH
    let df₀ (y : q.quotient) := deriv (fun t : ℝ ↦ f₀ (y * aQ (Multiplicative.ofAdd t))) 0
    refine ⟨df₀, ?_, ?_⟩
    · intro x
      unfold df₀ bruhatDirectionalDeriv
      congr 1
      funext t
      change f₀ (π x * π (aH (Multiplicative.ofAdd t))) = _
      rw [← map_mul π]
      exact hf₀ (x * aH (Multiplicative.ofAdd t))
    · intro e z b
      let c := AddMonoidHom.toMultiplicative.symm (e.equiv.toMulEquiv.toMonoidHom.comp aQ)
      have hc : Continuous c :=
        e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (a.continuous.subtype_mk ha))
      obtain ⟨v, hv⟩ := exists_elementaryCover_translation c hc
      let g := fun u ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z b)))
      have hg : ContDiff ℝ ((p : ℕ∞) + 1) g := by
        simpa only [Nat.cast_add, Nat.cast_one, WithTop.coe_add, WithTop.coe_one]
          using hSmooth e z b
      have hd : ContDiff ℝ (p : ℕ∞) (fun u ↦ fderiv ℝ g u v) :=
        (hg.contDiff_fderiv_apply le_rfl).comp (contDiff_id.prodMk contDiff_const)
      convert hd using 1
      funext u
      have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
      have hOrbit (t : ℝ) : g (u + t • v) =
          f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z b)) *
            aQ (Multiplicative.ofAdd t)) := by
        dsimp only [g]
        rw [hv]
        change f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z b) *
          e.equiv (aQ (Multiplicative.ofAdd t)))) = _
        rw [map_mul, e.equiv.symm_apply_apply]
      have h := (hg.differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq 0 hLine
        (by simp)
      simpa only [df₀, Function.comp_def, hOrbit] using h.deriv

/-- Paper: Lemma D.1.6.6, p. 767. The first derivative of a Bruhat smooth
function is Bruhat smooth. -/
theorem bruhatDirectionalDeriv_mem_smooth (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) :
    bruhatDirectionalDeriv a f ∈ bruhatSmoothSubmodule := by
  have hf := (mem_bruhatSmoothSubmodule_iff f.val).mp f.property
  exact (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦ (hf (p + 1)).directionalDeriv a

/-- Paper: Lemma D.1.6.6, p. 767. The first derivative satisfies the product
rule on pairs of Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_mul (a : LCATopologicalLie G) {f g : G → ℂ}
    (hf : IsBruhatContDiff 1 f) (hg : IsBruhatContDiff 1 g) :
    bruhatDirectionalDeriv a (f * g) =
      f * bruhatDirectionalDeriv a g + g * bruhatDirectionalDeriv a f := by
  funext x
  have h := ((hasDerivAt_bruhatDirectionalDeriv a hf x).fun_mul
    (hasDerivAt_bruhatDirectionalDeriv a hg x)).deriv
  simpa only [bruhatDirectionalDeriv, Pi.mul_apply, Pi.add_apply,
    ofAdd_zero, map_one, mul_one, mul_comm, add_comm] using h

/-- Paper: Definition D.1.6.5, p. 766. The orbit derivative is additive on
Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_add (a : LCATopologicalLie G)
    (f g : bruhatContDiffSubmodule (G := G) 1) :
    bruhatDirectionalDeriv a (f + g : bruhatContDiffSubmodule 1) =
      bruhatDirectionalDeriv a f + bruhatDirectionalDeriv a g := by
  funext x
  have hf := hasDerivAt_bruhatDirectionalDeriv a f.property x
  have hg := hasDerivAt_bruhatDirectionalDeriv a g.property x
  exact (hf.add hg).deriv

/-- Paper: Definition D.1.6.5, p. 766. The orbit derivative commutes with
complex scalar multiplication on Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_smul (a : LCATopologicalLie G)
    (f : bruhatContDiffSubmodule (G := G) 1) (c : ℂ) :
    bruhatDirectionalDeriv a (c • f : bruhatContDiffSubmodule 1) =
      c • bruhatDirectionalDeriv a f := by
  funext x
  simp only [bruhatDirectionalDeriv, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

/-- Paper: Definition D.1.6.5, p. 766. Orbit differentiation is a complex
linear map from Bruhat C¹ functions to continuous functions. -/
def bruhatDirectionalDerivLinear (a : LCATopologicalLie G) :
    bruhatContDiffSubmodule (G := G) 1 →ₗ[ℂ] C(G, ℂ) where
  toFun f := ⟨bruhatDirectionalDeriv a f,
    bruhatDirectionalDeriv_continuous a ((mem_bruhatContDiffSubmodule_iff 1 f.val).mp f.property)⟩
  map_add' f g := ContinuousMap.ext (congrFun (bruhatDirectionalDeriv_add a f g))
  map_smul' c f := ContinuousMap.ext (congrFun (bruhatDirectionalDeriv_smul a f c))

/-- Paper: Definition D.1.6.5, p. 766. Evaluation of the bundled map agrees
with the derivative of the orbit curve. -/
theorem bruhatDirectionalDerivLinear_apply (a : LCATopologicalLie G)
    (f : bruhatContDiffSubmodule (G := G) 1) (x : G) :
    bruhatDirectionalDerivLinear a f x = bruhatDirectionalDeriv a f x := rfl

/-- Paper: Lemma D.1.6.7(1), p. 767. The first-order operator is the complex
linear directional derivative acting on the smooth submodule. -/
def bruhatFirstOrder (a : LCATopologicalLie G) :
    Module.End ℂ (bruhatSmoothSubmodule (G := G)) where
  toFun f := ⟨bruhatDirectionalDeriv a f, bruhatDirectionalDeriv_mem_smooth a f⟩
  map_add' f g := Subtype.ext
    (bruhatDirectionalDeriv_add a ⟨f, (Submodule.mem_iInf _).mp f.property 1⟩
      ⟨g, (Submodule.mem_iInf _).mp g.property 1⟩)
  map_smul' c f := Subtype.ext
    (bruhatDirectionalDeriv_smul a ⟨f, (Submodule.mem_iInf _).mp f.property 1⟩ c)

/-- Paper: Lemma D.1.6.7(1), p. 767. Evaluation of the first-order operator
gives the orbit derivative. -/
theorem bruhatFirstOrder_apply (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) (x : G) :
    (bruhatFirstOrder a f : G → ℂ) x = bruhatDirectionalDeriv a f x := rfl

omit [CommGroup G] [TopologicalSpace G] hTop hT2 hLC in
/-- An affine map from a real normed space to an elementary group pulls back
functions that are smooth on each covered discrete fiber to smooth functions. -/
private theorem contDiff_comp_affine_elementary {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    {p : ℕ∞} (a : E →+ ElementaryLieGroup m n r F) (ha : Continuous a)
    (c : ElementaryLieGroup m n r F) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ z b, ContDiff ℝ p (fun u ↦ f (elementaryCover u z b))) :
    ContDiff ℝ p (fun x ↦ f (a x + c)) := by
  let aR := (AddMonoidHom.fst _ _).comp a
  let aT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp a)
  choose l hl hlift using fun i : Fin n ↦ exists_addCircle_addMonoidHom_lift
    ((Pi.evalAddMonoidHom _ i).comp aT) ((continuous_apply i).comp ha.snd.fst)
  let aLift : E →+ EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
    aR.prod ((EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap.toAddMonoidHom.comp
      (AddMonoidHom.pi l))
  have hLiftCont : Continuous aLift :=
    ha.fst.prodMk ((PiLp.continuous_toLp 2 _).comp (continuous_pi hl))
  have hDiscrete (x : E) : (a x).2.2 = 0 := by
    have h := ha.snd.snd.isConst_of_preconnectedSpace x 0
    rw [map_zero a] at h
    exact h
  obtain ⟨u, hu⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
  have hLift (x : E) :
      elementaryCover (aLift x + (c.1, u)) c.2.2.1 c.2.2.2 = a x + c := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      have hui := congrArg (fun y : ElementaryLieGroup m n r F ↦ y.2.1 i) hu
      change ((l i x + u i : ℝ) : AddCircle (1 : ℝ)) = (a x).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hlift i x]
      exact congrArg ((a x).2.1 i + ·) hui
    · change c.2.2 = (a x).2.2 + c.2.2
      rw [hDiscrete, zero_add]
  simp_rw [← hLift]
  exact (hf _ _).comp ((aLift.toRealLinearMap hLiftCont).contDiff.add contDiff_const)

/-- Left translation preserves each finite order of Bruhat differentiability
with the same good subgroup. -/
private theorem IsBruhatContDiff.comp_mul_left {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff p f) (g : G) : IsBruhatContDiff p (fun x ↦ f (g * x)) := by
  obtain ⟨k, hk, hInv, hDescend⟩ := hf
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · simpa only [mul_left_comm] using hInv h (g * x)
  let I := OpenCompactlyGeneratedSubgroups G
  have hColimit := openCompactlyGeneratedSubgroups_colimit (G := G)
  let : IsDirectedOrder I := hColimit.1
  obtain ⟨J, hgJ⟩ := hColimit.2.1 g
  obtain ⟨H, haH, hJH⟩ := exists_ge_ge (⟨a.val.1, a.property.1, a.property.2.1⟩ : I) J
  have hkA : k ≤ a.val.1 := ha ▸ a.property.2.2.2
  let b : BruhatStructuralPair G :=
    ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk, hkA.trans haH⟩
  let i := Subgroup.inclusion (show a.val.1 ≤ H.val from haH)
  let j : a.quotient →* b.quotient := QuotientGroup.map _ _ i (by
    intro x hx
    change (x : G) ∈ OrderDual.ofDual a.val.2 at hx
    change (x : G) ∈ k
    rwa [ha] at hx)
  have hi : Continuous i :=
    (continuous_subtype_val : Continuous ((↑) : a.val.1 → G)).subtype_mk _
  have hj : Continuous j := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hi)
  let gH : b.val.1 := ⟨g, hJH hgJ⟩
  let qg : b.quotient := QuotientGroup.mk gH
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend b rfl
  refine ⟨fun y ↦ f₀ (qg * j y), fun x ↦ hf₀ (gH * i x), ?_⟩
  obtain ⟨e'⟩ := b.elementary
  intro e z d
  let E := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let S := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let T := ElementaryLieGroup e'.realDim e'.torusDim e'.latticeRank e'.finiteFactor
  let cover : E →+ S :=
    { toFun := fun xt ↦ elementaryCover xt 0 0
      map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
      map_add' := fun x y ↦ Prod.ext rfl
        (Prod.ext (funext fun l ↦ AddCircle.coe_add (1 : ℝ) (x.2 l) (y.2 l)) (zero_add _).symm) }
  have hCover : Continuous cover :=
    continuous_fst.prodMk
      ((continuous_pi fun l ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
        ((PiLp.continuous_apply 2 _ l).comp continuous_snd)).prodMk
          (continuous_const.prodMk continuous_const))
  let L : S →+ T := AddMonoidHom.toMultiplicative.symm
    (e'.equiv.toMulEquiv.toMonoidHom.comp (j.comp e.equiv.symm.toMulEquiv.toMonoidHom))
  have hL : Continuous L := e'.equiv.continuous.comp (hj.comp e.equiv.symm.continuous)
  let c : T := (e'.equiv qg).toAdd + L (elementaryCover 0 z d)
  let φ : T → ℂ := fun y ↦ f₀ (e'.equiv.symm (Multiplicative.ofAdd y))
  have hAffine (xt : E) :
      φ (L (cover xt) + c) =
        f₀ (qg * j (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt z d)))) := by
    have hShift : cover xt + elementaryCover 0 z d = elementaryCover xt z d := by
      refine Prod.ext (add_zero _) (Prod.ext ?_ (zero_add _))
      funext l
      change (xt.2 l : AddCircle (1 : ℝ)) + ((0 : ℝ) : AddCircle (1 : ℝ)) =
        (xt.2 l : AddCircle (1 : ℝ))
      rw [AddCircle.coe_zero, add_zero]
    rw [show L (cover xt) + c =
      (e'.equiv qg).toAdd + (L (cover xt) + L (elementaryCover 0 z d)) from
        add_left_comm _ _ _, ← map_add, hShift]
    change f₀ (e'.equiv.symm (e'.equiv qg * e'.equiv (j _))) = _
    rw [← map_mul, e'.equiv.symm_apply_apply]
    rfl
  simpa only [AddMonoidHom.comp_apply, hAffine] using
    contDiff_comp_affine_elementary (L.comp cover) (hL.comp hCover) c (f := φ) (hSmooth e')

/-- Paper: Lemma D.1.6.7(1), p. 767. The directional derivative commutes
with left translations. -/
theorem bruhatFirstOrder_translate (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) (g : G) :
    ∃ f' : bruhatSmoothSubmodule (G := G),
      (∀ x : G, f'.val x = f.val (g⁻¹ * x)) ∧
      ∀ x : G, (bruhatFirstOrder a f').val x = (bruhatFirstOrder a f).val (g⁻¹ * x) := by
  have hf := (mem_bruhatSmoothSubmodule_iff f.val).mp f.property
  refine ⟨⟨fun x ↦ f.val (g⁻¹ * x), (mem_bruhatSmoothSubmodule_iff _).mpr
    (fun p ↦ (hf p).comp_mul_left g⁻¹)⟩, fun _ ↦ rfl, fun x ↦ ?_⟩
  change deriv (fun t : ℝ ↦ f.val (g⁻¹ * (x * a (Multiplicative.ofAdd t)))) 0 =
    deriv (fun t : ℝ ↦ f.val ((g⁻¹ * x) * a (Multiplicative.ofAdd t))) 0
  simp only [mul_assoc]

/-- Paper: Lemma D.1.6.7(1), p. 767. First-order operators add under
pointwise multiplication of one-parameter subgroups. -/
theorem bruhatFirstOrder_mul (a b : LCATopologicalLie G) :
    bruhatFirstOrder (a * b) = bruhatFirstOrder a + bruhatFirstOrder b := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change bruhatDirectionalDeriv (a * b) f x =
    bruhatDirectionalDeriv a f x + bruhatDirectionalDeriv b f x
  -- Use a structural quotient containing the point and both subgroup images.
  have hf : IsBruhatContDiff 1 (f : G → ℂ) := (Submodule.mem_iInf _).mp f.property 1
  obtain ⟨k, hk, _, hDescent⟩ := hf
  obtain ⟨p, hp, hx⟩ := exists_bruhatStructuralPair_mem k hk x
  obtain ⟨e⟩ := p.elementary
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescent p hp
  have hMem (c : LCATopologicalLie G) (t : Multiplicative ℝ) : c t ∈ p.val.1 := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range c.continuous).subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨1, map_one c⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let lift (c : LCATopologicalLie G) := c.toMonoidHom.codRestrict p.val.1 (hMem c)
  let q := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _ : p.val.1 →* p.quotient)
  let cE (c : LCATopologicalLie G) := AddMonoidHom.toMultiplicative.symm (q.comp (lift c))
  have hcE (c : LCATopologicalLie G) : Continuous (cE c) :=
    e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (c.continuous.subtype_mk (hMem c)))
  have hMul (t : ℝ) : cE (a * b) t = cE a t + cE b t := by
    change (q (lift a (Multiplicative.ofAdd t) * lift b (Multiplicative.ofAdd t))).toAdd = _
    rw [map_mul]
    rfl
  -- Evaluate all three derivatives in the same lift of the discrete fiber.
  obtain ⟨va, ha⟩ := exists_elementaryCover_translation (cE a) (hcE a)
  obtain ⟨vb, hb⟩ := exists_elementaryCover_translation (cE b) (hcE b)
  let y := (q ⟨x, hx⟩).toAdd
  obtain ⟨w, hw⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
  let u := (y.1, w)
  let g := fun v ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover v y.2.2.1 y.2.2.2)))
  have hg : HasFDerivAt g (fderiv ℝ g u) u :=
    ((hSmooth e y.2.2.1 y.2.2.2).differentiable_one u).hasFDerivAt
  have hDeriv (c : LCATopologicalLie G) (v : EuclideanSpace ℝ (Fin e.realDim) ×
      EuclideanSpace ℝ (Fin e.torusDim))
      (hv : ∀ t : ℝ, elementaryCover (u + t • v) y.2.2.1 y.2.2.2 = y + cE c t) :
      bruhatDirectionalDeriv c f x = fderiv ℝ g u v := by
    have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have hOrbit (t : ℝ) : g (u + t • v) = (f : G → ℂ) (x * c (Multiplicative.ofAdd t)) := by
      dsimp only [g]
      rw [hv]
      change f₀ (e.equiv.symm (q ⟨x, hx⟩ * q (lift c (Multiplicative.ofAdd t)))) = _
      rw [← map_mul q]
      let z := (⟨x, hx⟩ : p.val.1) * lift c (Multiplicative.ofAdd t)
      change f₀ (e.equiv.symm (e.equiv (QuotientGroup.mk z))) = (f : G → ℂ) z.val
      rw [e.equiv.symm_apply_apply]
      exact hf₀ z
    have h := hg.comp_hasDerivAt_of_eq 0 hLine (by simp)
    simpa only [Function.comp_def, hOrbit, bruhatDirectionalDeriv] using h.deriv
  rw [hDeriv a va (fun t ↦ (ha u _ _ t).trans (congrArg (· + cE a t) hw)),
    hDeriv b vb (fun t ↦ (hb u _ _ t).trans (congrArg (· + cE b t) hw)),
    hDeriv (a * b) (va + vb)]
  · exact map_add (fderiv ℝ g u) va vb
  · intro t
    rw [smul_add, ← add_assoc, hb, ha, hw, add_assoc, hMul]

/-- Paper: Lemma D.1.6.7(1), p. 767. Scaling the real parameter scales
the first-order operator by the same factor. -/
theorem bruhatFirstOrder_scale (a : LCATopologicalLie G) (c : ℝ) :
    let scale : LCATopologicalLie (Multiplicative ℝ) :=
      ⟨(c • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative,
        continuous_const_mul c⟩
    bruhatFirstOrder (a.comp scale) = c • bruhatFirstOrder a := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  let orbit : ℝ → ℂ := fun t ↦ f.val (x * a (Multiplicative.ofAdd t))
  change deriv (fun t ↦ orbit (c * t)) 0 = c • deriv orbit 0
  simpa only [mul_zero] using deriv_comp_mul_left c orbit 0

omit [CommGroup G] [TopologicalSpace G] hTop hT2 hLC in
/-- A weighted mixed partial of a fixed-direction derivative on the elementary cover
is controlled by finitely many seminorms of the original function.
The weights are unchanged and one derivative index is raised by one. -/
private theorem elementarySchwartz_directional_bound {m n r : ℕ} {F : Type*}
    (v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (i : ElementarySchwartzIndex m n r) :
    ∃ p : Seminorm ℂ (ElementarySchwartz m n r F), Continuous p ∧
      ∀ (f : ElementarySchwartz m n r F) (g : ElementaryLieGroup m n r F → ℂ),
        (∀ u z b, g (elementaryCover u z b) =
          fderiv ℝ (fun w ↦ f (elementaryCover w z b)) u v) →
        elementarySchwartzBound g i ≤ ENNReal.ofReal (p f) := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let basis : Module.Basis (Fin m ⊕ Fin n) ℝ X :=
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.prod (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let ν : Fin m ⊕ Fin n → ElementarySchwartzIndex m n r
    | .inl j => (i.1, i.2.1 + Pi.single j 1, i.2.2.1, i.2.2.2)
    | .inr j => (i.1, i.2.1, i.2.2.1 + Pi.single j 1, i.2.2.2)
  let q : Seminorm ℂ (ElementarySchwartz m n r F) :=
    Finset.univ.sup (fun j ↦ elementarySchwartzSeminorm (ν j))
  let C : ℝ≥0 := ∑ j, ‖basis.repr v j‖₊
  have hq : Continuous q := Seminorm.continuous_finsetSup fun j _ ↦
    (withGeneratingSeminorms_spec _ _).continuous_seminorm (ν j)
  refine ⟨C • q, ?_, fun f g hg ↦ ?_⟩
  · exact hq.const_smul (C : ℝ)
  -- Adding a coordinate direction increments its multiplicity in the list of partials.
  let dirs {k : ℕ} (d : Fin k → X) (α : Fin k → ℕ) : List X :=
    (List.ofFn fun j ↦ List.replicate (α j) (d j)).flatten
  have hInsert {k : ℕ} (d : Fin k → X) (α : Fin k → ℕ) (j : Fin k) :
      (d j :: dirs d α).Perm (dirs d (α + Pi.single j 1)) := by
    let indices (α : Fin k → ℕ) :=
      (List.finRange k).flatMap fun l ↦ List.replicate (α l) l
    have hMap (α : Fin k → ℕ) : (indices α).map d = dirs d α := by
      simp only [indices, dirs, List.ofFn_eq_map, List.map_flatMap, List.map_replicate,
        List.flatten_eq_flatMap, List.flatMap_map, id_eq]
    have hCount (α : Fin k → ℕ) (l : Fin k) : (indices α).count l = α l := by
      rw [List.count_flatMap, ← Fin.sum_univ_def]
      simp [List.count_replicate]
    have hPerm : (j :: indices α).Perm (indices (α + Pi.single j 1)) := by
      rw [List.perm_iff_count]
      intro l
      simp only [List.count_cons, hCount, beq_iff_eq, Pi.add_apply, Pi.single_apply, eq_comm (a := j)]
    simpa only [List.map_cons, hMap] using hPerm.map d
  let dR (j : Fin m) : X := (EuclideanSpace.single j 1, 0)
  let dT (j : Fin n) : X := (0, EuclideanSpace.single j 1)
  let R := dirs dR i.2.1
  let S := dirs dT i.2.2.1
  let D := R ++ S
  refine iSup_le fun u ↦ iSup_le fun z ↦ iSup_le fun b ↦ ?_
  let l : X → ℂ := fun w ↦ f (elementaryCover w z b)
  have hl : ContDiff ℝ ∞ l := f.property.1 z b
  let weight : ℂ := (∏ k, (u.1 k : ℂ) ^ i.1 k) * (∏ k, (z k : ℂ) ^ i.2.2.2 k)
  let T : X →L[ℝ] ℂ := iteratedFDeriv ℝ D.length (fderiv ℝ l) u D.get
  have hPartial : elementaryPartial g i.2.1 i.2.2.1 u z b = T v := by
    have hFun : (fun w ↦ g (elementaryCover w z b)) =
        (ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ l := funext fun w ↦ hg w z b
    change iteratedFDeriv ℝ D.length (fun w ↦ g (elementaryCover w z b)) u D.get = T v
    rw [hFun, (ContinuousLinearMap.apply ℝ ℂ v).iteratedFDeriv_comp_left
      (hl.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)]
    rfl
  have hLast (d : X) :
      iteratedFDeriv ℝ (D ++ [d]).length l u (D ++ [d]).get = T d := by
    let eval (s : Σ k, Fin k → X) := iteratedFDeriv ℝ s.1 l u s.2
    have hEval := congrArg eval (List.equivSigmaTuple.apply_symm_apply
      ⟨D.length + 1, Fin.snoc D.get d⟩)
    change iteratedFDeriv ℝ (List.ofFn (Fin.snoc D.get d)).length l u
      (List.ofFn (Fin.snoc D.get d)).get = iteratedFDeriv ℝ (D.length + 1) l u
      (Fin.snoc D.get d) at hEval
    have hList : List.ofFn (Fin.snoc D.get d) = D ++ [d] := by
      rw [List.ofFn_succ', Fin.snoc_last, List.concat_eq_append]
      simp only [Fin.snoc_castSucc, List.ofFn_get]
    rw [hList] at hEval
    rw [hEval, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have hCoord (j : Fin m ⊕ Fin n) :
      T (basis j) = elementaryPartial f (ν j).2.1 (ν j).2.2.1 u z b := by
    cases j with
    | inl j =>
      have hBasis : basis (.inl j) = dR j := by
        apply Prod.ext
        · exact (Module.Basis.prod_apply_inl_fst _ _ j).trans
            (EuclideanSpace.basisFun_apply _ _ j)
        · exact Module.Basis.prod_apply_inl_snd _ _ j
      rw [hBasis, ← hLast]
      have hPerm : (D ++ [dR j]).Perm (dirs dR (i.2.1 + Pi.single j 1) ++ S) :=
        (show (D ++ [dR j]).Perm (dR j :: D) by simp).trans
          ((hInsert dR i.2.1 j).append_right S)
      exact iteratedFDeriv_apply_list_perm hl id hPerm u
    | inr j =>
      have hBasis : basis (.inr j) = dT j := by
        apply Prod.ext
        · exact Module.Basis.prod_apply_inr_fst _ _ j
        · exact (Module.Basis.prod_apply_inr_snd _ _ j).trans
            (EuclideanSpace.basisFun_apply _ _ j)
      rw [hBasis, ← hLast]
      have hPerm : (D ++ [dT j]).Perm (R ++ dirs dT (i.2.2.1 + Pi.single j 1)) := by
        rw [show D = R ++ S from rfl, List.append_assoc]
        have hMove : (S ++ [dT j]).Perm (dT j :: S) := by
          simp
        exact (hMove.trans (hInsert dT i.2.2.1 j)).append_left R
      exact iteratedFDeriv_apply_list_perm hl id hPerm u
  have hPoint (j : Fin m ⊕ Fin n) : ‖weight * T (basis j)‖ ≤ q f := by
    rw [hCoord]
    refine le_trans ?_ (Seminorm.le_finset_sup_apply (Finset.mem_univ j))
    have h : (‖weight * elementaryPartial f (ν j).2.1 (ν j).2.2.1 u z b‖₊ : ℝ≥0∞) ≤
        elementarySchwartzBound f (ν j) := by
      cases j <;> exact le_iSup_of_le u (le_iSup_of_le z (le_iSup_of_le b le_rfl))
    exact ENNReal.toReal_mono (f.property.2 (ν j)).ne h
  rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_le_ofReal_iff (apply_nonneg (C • q) f)]
  change ‖weight * elementaryPartial g i.2.1 i.2.2.1 u z b‖ ≤ _
  rw [hPartial]
  -- Expand the direction in the product basis and bound each term by the same seminorm.
  have hSum : weight * T v = ∑ j, basis.repr v j • (weight * T (basis j)) := by
    conv_lhs => rw [← basis.sum_repr v]
    simp only [map_sum, map_smul, Finset.mul_sum, Algebra.mul_smul_comm]
  calc
    ‖weight * T v‖ ≤ ∑ j, ‖basis.repr v j • (weight * T (basis j))‖ := by
      rw [hSum]
      exact norm_sum_le _ _
    _ ≤ ∑ j, ‖basis.repr v j‖ * q f := by
      simp only [norm_smul]
      exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hPoint j) (norm_nonneg _)
    _ = (C • q) f := by simp [C, ← Finset.sum_mul, smul_apply, NNReal.smul_def]

omit [CommGroup G] [TopologicalSpace G] hTop hT2 hLC in
/-- On every elementary stage an orbit derivative is a continuous linear operator,
and every orbit curve of a stage function is differentiable at zero. -/
private theorem elementarySchwartz_orbitDeriv {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (c : ℝ →+ ElementaryLieGroup m n r F) (hc : Continuous c) :
    ∃ B : ElementarySchwartz m n r F →L[ℂ] ElementarySchwartz m n r F,
      ∀ f y, HasDerivAt (fun t : ℝ ↦ f (y + c t)) (B f y) 0 := by
  obtain ⟨v, hv⟩ := exists_elementaryCover_translation c hc
  let D (f : ElementarySchwartz m n r F) (y : ElementaryLieGroup m n r F) :=
    deriv (fun t : ℝ ↦ f (y + c t)) 0
  have hDeriv (f : ElementarySchwartz m n r F) (u) (z) (b) :
      HasDerivAt (fun t : ℝ ↦ f (elementaryCover u z b + c t))
        (fderiv ℝ (fun w ↦ f (elementaryCover w z b)) u v) 0 := by
    have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have h := ((f.property.1 z b).differentiable (by simp) u).hasFDerivAt
    simpa only [Function.comp_def, hv] using h.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hLift (f : ElementarySchwartz m n r F) (u) (z) (b) :
      D f (elementaryCover u z b) = fderiv ℝ (fun w ↦ f (elementaryCover w z b)) u v :=
    (hDeriv f u z b).deriv
  have hDiff (f : ElementarySchwartz m n r F) (y : ElementaryLieGroup m n r F) :
      HasDerivAt (fun t : ℝ ↦ f (y + c t)) (D f y) 0 := by
    obtain ⟨w, hw⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
    change elementaryCover (y.1, w) y.2.2.1 y.2.2.2 = y at hw
    rw [← hw, hLift]
    exact hDeriv f _ _ _
  choose p hp hBound using elementarySchwartz_directional_bound (r := r) (F := F) v
  have hMem (f : ElementarySchwartz m n r F) : D f ∈ elementarySchwartzSubmodule m n r F := by
    refine ⟨fun z b ↦ ?_, fun i ↦ (hBound i f (D f) (fun u z b ↦ hLift f u z b)).trans_lt
      ENNReal.ofReal_lt_top⟩
    simp only [hLift]
    exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp
      ((f.property.1 z b).fderiv_right (m := ∞) (by simp))
  let B : ElementarySchwartz m n r F →ₗ[ℂ] ElementarySchwartz m n r F :=
    { toFun := fun f ↦ ⟨D f, hMem f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦
        ((hDiff f y).add (hDiff g y)).deriv)
      map_smul' := fun d f ↦ Subtype.ext (funext fun y ↦
        ((hDiff f y).const_smul d).deriv) }
  refine ⟨⟨B, ?_⟩, hDiff⟩
  apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp B
  intro i
  apply Seminorm.continuous_of_le (hp i)
  intro f
  change (elementarySchwartzBound (D f) i).toReal ≤ p i f
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hBound i f (D f) (fun u z b ↦ hLift f u z b))).trans_eq
      (ENNReal.toReal_ofReal (apply_nonneg (p i) f))

omit hT2 hLC in
/-- Differentiation on a structural stage agrees with differentiation on its
elementary quotient, including the zero extension off the open subgroup. -/
private theorem schwartzBruhatStage_orbitDeriv (a : LCATopologicalLie G)
    (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient) :
    ∃ B : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e,
      ∀ f x, HasDerivAt (fun t : ℝ ↦ schwartzBruhatStageRealization p e f
        (x * a (Multiplicative.ofAdd t))) (schwartzBruhatStageRealization p e (B f) x) 0 := by
  classical
  have hMem (t : Multiplicative ℝ) : a t ∈ p.val.1 := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range a.continuous).subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨1, map_one a⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let aH := a.toMonoidHom.codRestrict p.val.1 hMem
  let q := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _ : p.val.1 →* p.quotient)
  let c := AddMonoidHom.toMultiplicative.symm (q.comp aH)
  have hc : Continuous c :=
    e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (a.continuous.subtype_mk hMem))
  obtain ⟨B, hB⟩ := elementarySchwartz_orbitDeriv c hc
  refine ⟨B, fun f x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ p.val.1
  · rw [dite_eq_left hx]
    let y := (q ⟨x, hx⟩).toAdd
    have hEq (t : ℝ) : schwartzBruhatStageRealization p e f
        (x * a (Multiplicative.ofAdd t)) = f (y + c t) := by
      rw [schwartzBruhatStageRealization_apply, dite_eq_left (p.val.1.mul_mem hx (hMem _))]
      change f (q (⟨x, hx⟩ * aH (Multiplicative.ofAdd t))).toAdd = f (y + c t)
      rw [map_mul q]
      rfl
    simp only [hEq]
    exact hB f y
  · rw [dite_eq_right hx]
    have hEq (t : ℝ) : schwartzBruhatStageRealization p e f
        (x * a (Multiplicative.ofAdd t)) = 0 := by
      rw [schwartzBruhatStageRealization_apply, dite_eq_right]
      exact fun ht ↦ hx ((p.val.1.mul_mem_cancel_right (hMem _)).mp ht)
    simp only [hEq]
    exact hasDerivAt_const 0 (0 : ℂ)

include hT2 hLC in
/-- Paper: Lemma D.1.6.7(1), p. 767. The directional derivative restricts
to a continuous complex linear endomorphism of the Schwartz–Bruhat space. -/
theorem bruhatFirstOrder_schwartz :
    ∀ a : LCATopologicalLie G, ∃ A : SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ f x, A f x = bruhatDirectionalDeriv a f x := by
  classical
  intro a
  choose B hB using schwartzBruhatStage_orbitDeriv a
  have hStage (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (f : SchwartzBruhatStage e) :
      bruhatDirectionalDeriv a (schwartzBruhatStageRealization p e f) =
        schwartzBruhatStageRealization p e (B p e f) :=
    funext fun x ↦ (hB p e f x).deriv
  let P (f : G → ℂ) : Prop :=
    (∀ x : G, DifferentiableAt ℝ (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0) ∧
      bruhatDirectionalDeriv a f ∈ schwartzBruhatSubmodule G
  have hMem (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (g : G → ℂ) (hg : g ∈ (schwartzBruhatStageRealization p e).range) : P g := by
    obtain ⟨s, rfl⟩ := hg
    exact ⟨fun x ↦ (hB p e s x).differentiableAt, hStage p e s ▸
      (schwartzBruhatStageInclusion p e (B p e s)).property⟩
  have hZero : P 0 := by
    refine ⟨fun _ ↦ differentiableAt_const _, ?_⟩
    have h : bruhatDirectionalDeriv a (0 : G → ℂ) = 0 := by
      funext x
      exact (hasDerivAt_const 0 (0 : ℂ)).deriv
    rw [h]
    exact (schwartzBruhatSubmodule G).zero_mem
  have hAdd (g h : G → ℂ) (hg : P g) (hh : P h) : P (g + h) := by
    refine ⟨fun x ↦ (hg.1 x).add (hh.1 x), ?_⟩
    have hEq : bruhatDirectionalDeriv a (g + h) =
        bruhatDirectionalDeriv a g + bruhatDirectionalDeriv a h :=
      funext fun x ↦ deriv_add (hg.1 x) (hh.1 x)
    rw [hEq]
    exact (schwartzBruhatSubmodule G).add_mem hg.2 hh.2
  have hAll (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) : P f :=
    Submodule.iSup_induction _ (motive := P) hf
      (fun p g hg ↦ Submodule.iSup_induction _ (motive := P) hg (hMem p) hZero hAdd)
      hZero hAdd
  let A : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G :=
    { toFun := fun f ↦ ⟨bruhatDirectionalDeriv a f, (hAll f.val f.property).2⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦
        deriv_add ((hAll f.val f.property).1 x) ((hAll g.val g.property).1 x))
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ by
        change deriv (fun t : ℝ ↦ c * f (x * a (Multiplicative.ofAdd t))) 0 =
          c * deriv (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0
        exact congrFun (deriv_const_mul_field' c) 0) }
  refine ⟨⟨A, ?_⟩, fun _ _ ↦ rfl⟩
  apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp A
  intro p
  let q := p.val.comp A
  have hq (s : BruhatStructuralPair G) (e : ElementaryLCAPresentation s.quotient) :
      Continuous (q ∘ schwartzBruhatStageInclusion s e) := by
    have hEq : q ∘ schwartzBruhatStageInclusion s e =
        (p.val ∘ schwartzBruhatStageInclusion s e) ∘ B s e := by
      funext f
      apply congrArg p.val
      exact Subtype.ext (hStage s e f)
    rw [hEq]
    exact (p.property s e).comp (B s e).continuous
  let q' : {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (s : BruhatStructuralPair G) (e : ElementaryLCAPresentation s.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion s e)} := ⟨q, hq⟩
  exact (withGeneratingSeminorms_spec (schwartzBruhatSubmodule G) Subtype.val).continuous_seminorm q'

/-- Paper: Lemma D.1.6.7(2), p. 767. First-order operators commute on the
smooth submodule. -/
theorem bruhatFirstOrder_commute (a b : LCATopologicalLie G) :
    Commute (bruhatFirstOrder a) (bruhatFirstOrder b) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change bruhatDirectionalDeriv a (bruhatDirectionalDeriv b f) x =
    bruhatDirectionalDeriv b (bruhatDirectionalDeriv a f) x
  -- Descend the two-parameter orbit through a structural quotient containing x.
  have hf : IsBruhatContDiff 2 (f : G → ℂ) := (Submodule.mem_iInf _).mp f.property 2
  obtain ⟨k, hk, _, hDescent⟩ := hf
  obtain ⟨p, hp, hx⟩ := exists_bruhatStructuralPair_mem k hk x
  obtain ⟨e⟩ := p.elementary
  obtain ⟨f₀, hf₀, hCover⟩ := hDescent p hp
  have hMem (c : LCATopologicalLie G) (t : Multiplicative ℝ) : c t ∈ p.val.1 := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range c.continuous).subset_isClopen
      ⟨p.val.1.isClosed_of_isOpen p.property.1, p.property.1⟩
      ⟨1, ⟨1, map_one c⟩, p.val.1.one_mem⟩ (mem_range_self t)
  let lift (c : LCATopologicalLie G) := c.toMonoidHom.codRestrict p.val.1 (hMem c)
  let q := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _ : p.val.1 →* p.quotient)
  let cE (c : LCATopologicalLie G) := AddMonoidHom.toMultiplicative.symm (q.comp (lift c))
  have hcE (c : LCATopologicalLie G) : Continuous (cE c) :=
    e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (c.continuous.subtype_mk (hMem c)))
  let orbit (st : ℝ × ℝ) :=
    (f : G → ℂ) (x * a (Multiplicative.ofAdd st.1) * b (Multiplicative.ofAdd st.2))
  have hOrbit : ContDiff ℝ 2 orbit := by
    let c := (cE a).coprod (cE b)
    have hc : Continuous c := ((hcE a).comp continuous_fst).add ((hcE b).comp continuous_snd)
    let φ := fun y ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd y))
    have hEq (st : ℝ × ℝ) : φ (c st + (q ⟨x, hx⟩).toAdd) = orbit st := by
      let y := (⟨x, hx⟩ : p.val.1) * lift a (Multiplicative.ofAdd st.1) *
        lift b (Multiplicative.ofAdd st.2)
      change f₀ (e.equiv.symm ((q (lift a (Multiplicative.ofAdd st.1)) *
        q (lift b (Multiplicative.ofAdd st.2))) * q ⟨x, hx⟩)) = f.val y.val
      rw [mul_comm _ (q ⟨x, hx⟩), ← mul_assoc, ← map_mul, ← map_mul]
      change f₀ (e.equiv.symm (e.equiv (QuotientGroup.mk y))) = f.val y.val
      rw [e.equiv.symm_apply_apply]
      exact hf₀ y
    simpa [hEq] using
      contDiff_comp_affine_elementary c hc (q ⟨x, hx⟩).toAdd (f := φ) (hCover e)
  have hFirst (u v : ℝ × ℝ) :
      deriv (fun t : ℝ ↦ orbit (u + t • v)) 0 = fderiv ℝ orbit u v := by
    have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    exact ((hOrbit.differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hLine (by simp)).deriv
  have hSecond (u v : ℝ × ℝ) :
      deriv (fun t : ℝ ↦ fderiv ℝ orbit (t • u) v) 0 =
        fderiv ℝ (fderiv ℝ orbit) 0 u v := by
    have hd := ((hOrbit.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) 0).hasFDerivAt
    have h := hd.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id (0 : ℝ)).smul_const u) (by simp)
    simpa using (h.clm_apply (hasDerivAt_const 0 v)).deriv
  have ha (t : ℝ) : bruhatDirectionalDeriv a f (x * b (Multiplicative.ofAdd t)) =
      fderiv ℝ orbit (0, t) (1, 0) := by
    simpa [bruhatDirectionalDeriv, orbit, mul_right_comm] using hFirst (0, t) (1, 0)
  have hb (s : ℝ) : bruhatDirectionalDeriv b f (x * a (Multiplicative.ofAdd s)) =
      fderiv ℝ orbit (s, 0) (0, 1) := by
    simpa [bruhatDirectionalDeriv, orbit] using hFirst (s, 0) (0, 1)
  change deriv (fun s : ℝ ↦ bruhatDirectionalDeriv b f (x * a (Multiplicative.ofAdd s))) 0 =
    deriv (fun t : ℝ ↦ bruhatDirectionalDeriv a f (x * b (Multiplicative.ofAdd t))) 0
  simp_rw [ha, hb]
  have hSymm := hOrbit.contDiffAt (x := 0) |>.isSymmSndFDerivAt (by simp)
  have hMixed := (hSecond (1, 0) (0, 1)).trans
    ((hSymm.eq (1, 0) (0, 1)).trans (hSecond (0, 1) (1, 0)).symm)
  simpa only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] using hMixed

/-- Paper: Definition D.1.6.8(1), p. 768. Invariant differential operators
form the unital complex subalgebra generated by the first-order operators. -/
def bruhatDiffAlgebra (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    Subalgebra ℂ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Algebra.adjoin ℂ (range (bruhatFirstOrder (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The invariant differential operator
algebra is commutative. -/
theorem bruhatDiffAlgebra_commute (D E : bruhatDiffAlgebra G) : Commute D E := by
  have hcomm : (range (bruhatFirstOrder (G := G))).Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    exact bruhatFirstOrder_commute a b
  let : IsMulCommutative (bruhatDiffAlgebra G) := Algebra.isMulCommutative_adjoin ℂ hcomm
  exact mul_comm' D E

/-- Paper: Definition D.1.6.8(1), p. 768. The first-order generator belongs to
the differential operator algebra. -/
def bruhatDiffGenerator (a : LCATopologicalLie G) : bruhatDiffAlgebra G :=
  ⟨bruhatFirstOrder a, Algebra.subset_adjoin ⟨a, rfl⟩⟩

/-- Paper: Definition D.1.6.8(1), p. 768. The complex degree-one space is
the complex span of the first-order generators inside the differential operator algebra. -/
def bruhatDiffDegreeOne : Submodule ℂ (bruhatDiffAlgebra G) :=
  Submodule.span ℂ (range (bruhatDiffGenerator (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The real degree-one space is the
real span of first-order operators.
Deviation: This span is taken inside the ambient endomorphism algebra, where every
element of the span belongs to the differential operator algebra. -/
def bruhatDiffDegreeOneReal : Submodule ℝ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Submodule.span ℝ (range (bruhatFirstOrder (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The complex first-order space
contains each generator and excludes the identity operator.
Deviation: Sanity check distinguishing the span from the unital algebra. -/
theorem bruhatDiffDegreeOne_sanity (a : LCATopologicalLie G) :
    bruhatDiffGenerator a ∈ bruhatDiffDegreeOne ∧
      (1 : bruhatDiffAlgebra G) ∉ bruhatDiffDegreeOne := by
  refine ⟨Submodule.subset_span ⟨a, rfl⟩, ?_⟩
  -- The good subgroup witnessing smoothness of zero works for any constant.
  obtain ⟨k, hk, _, _⟩ := isBruhatContDiff_zero (G := G) 0
  have hone : (fun _ : G ↦ (1 : ℂ)) ∈ bruhatSmoothSubmodule := by
    apply (mem_bruhatSmoothSubmodule_iff _).2
    intro p
    refine ⟨k, hk, fun _ _ ↦ rfl, fun q _ ↦ ⟨fun _ ↦ 1, fun _ ↦ rfl, ?_⟩⟩
    intro e z b
    exact contDiff_const
  let f : bruhatSmoothSubmodule (G := G) := ⟨fun _ ↦ 1, hone⟩
  let ev : bruhatDiffAlgebra G →ₗ[ℂ] bruhatSmoothSubmodule (G := G) :=
    (LinearMap.applyₗ f).comp (bruhatDiffAlgebra G).val.toLinearMap
  have hspan : bruhatDiffDegreeOne ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    funext x
    change bruhatDirectionalDeriv b (fun _ ↦ 1) x = 0
    exact deriv_const (0 : ℝ) (1 : ℂ)
  intro h
  have hz : ev 1 = 0 := LinearMap.mem_ker.mp (hspan h)
  exact one_ne_zero (congrArg (fun g : bruhatSmoothSubmodule (G := G) ↦ g.val 1) hz)

/-- Paper: Definition D.1.6.8(1), p. 768. The real degree-one space consists
of individual first-order operators, by real linearity in the direction. -/
theorem mem_bruhatDiffDegreeOneReal_iff
    (D : Module.End ℂ (bruhatSmoothSubmodule (G := G))) :
    D ∈ bruhatDiffDegreeOneReal ↔ ∃ a : LCATopologicalLie G, D = bruhatFirstOrder a := by
  change D ∈ Submodule.span ℝ (Set.range (bruhatFirstOrder (G := G))) ↔ _
  constructor
  · intro hD
    induction hD using Submodule.span_induction with
    | mem E hE =>
      obtain ⟨a, rfl⟩ := hE
      exact ⟨a, rfl⟩
    | zero =>
      exact ⟨_, by simpa only [zero_smul] using
        (bruhatFirstOrder_scale (1 : LCATopologicalLie G) 0).symm⟩
    | add E F _ _ hE hF =>
      obtain ⟨a, rfl⟩ := hE
      obtain ⟨b, rfl⟩ := hF
      exact ⟨a * b, (bruhatFirstOrder_mul a b).symm⟩
    | smul c E _ hE =>
      obtain ⟨a, rfl⟩ := hE
      exact ⟨_, (bruhatFirstOrder_scale a c).symm⟩
  · rintro ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, rfl⟩

/-- Paper: Definition D.1.6.8(2), p. 768. A word acts by applying its first
letter first and its last letter last. -/
def bruhatDiffWord (w : List (LCATopologicalLie G)) : bruhatDiffAlgebra G :=
  (w.reverse.map bruhatDiffGenerator).prod

/-- Paper: Definition D.1.6.8(2), p. 768. A one-letter word evaluates to its
first-order generator. -/
theorem bruhatDiffWord_singleton (a : LCATopologicalLie G) :
    bruhatDiffWord [a] = bruhatDiffGenerator a := by
  simp [bruhatDiffWord]

/-- Paper: Definition D.1.6.8(2), p. 768. Each operator has a presentation
as a finite linear combination of words in the first-order generators. -/
theorem bruhatDiff_exists_presentation (D : bruhatDiffAlgebra G) :
    ∃ c : List (LCATopologicalLie G) →₀ ℂ, c.sum (fun w z ↦ z • bruhatDiffWord w) = D := by
  let incl := (bruhatDiffAlgebra G).val
  have hWords :
      ↑(Submonoid.closure (range (bruhatFirstOrder (G := G)))) ⊆
        range (incl ∘ bruhatDiffWord) := by
    intro A hA
    induction hA using Submonoid.closure_induction with
    | mem A hA =>
        obtain ⟨a, rfl⟩ := hA
        refine ⟨[a], ?_⟩
        rw [Function.comp_apply, bruhatDiffWord_singleton]
        rfl
    | one =>
        exact ⟨[], incl.map_one⟩
    | mul A B _ _ hA hB =>
        obtain ⟨u, rfl⟩ := hA
        obtain ⟨v, rfl⟩ := hB
        refine ⟨v ++ u, ?_⟩
        simp only [Function.comp_apply, bruhatDiffWord, List.reverse_append, List.map_append,
          List.prod_append, map_mul]
  have hD : D.val ∈ Submodule.span ℂ (Submonoid.closure (range (bruhatFirstOrder (G := G))) :
      Set (Module.End ℂ (bruhatSmoothSubmodule (G := G)))) := by
    rw [← Algebra.adjoin_eq_span]
    exact D.property
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (Submodule.span_mono hWords hD)
  refine ⟨c, Subtype.ext ?_⟩
  change incl.toLinearMap (c.sum (fun w z ↦ z • bruhatDiffWord w)) = D.val
  simpa only [Finsupp.sum, map_sum, map_smul, AlgHom.toLinearMap_apply, Function.comp_apply]
    using hc

/-- Paper: Definition D.1.6.8(2), p. 768. The degree is the smallest possible
maximum word length among finite presentations of the operator.
Deviation: Finset supremum sets the empty presentation's length to zero. -/
def bruhatDiffDegree (D : bruhatDiffAlgebra G) : ℕ :=
  sInf {n : ℕ | ∃ c : List (LCATopologicalLie G) →₀ ℂ,
    c.sum (fun w z ↦ z • bruhatDiffWord w) = D ∧ n = c.support.sup List.length}

/-- Paper: Remark D.1.6.11, p. 768. A character gives a Bruhat smooth
function via its circle-valued character map.
Deviation: The global differentiability definition in §D.1.5 allows any
good subgroup in the kernel, so the symbol can use the character itself. -/
theorem pontryaginDual_mem_bruhatSmooth (χ : PontryaginDual G) :
    (fun x : G ↦ (χ x : ℂ)) ∈ bruhatSmoothSubmodule := by
  obtain ⟨H, hχ⟩ := (openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).2.1 χ
  let k := lcaDualAnnihilator H.val
  have hkClosed : IsClosed (k : Set G) := by
    have hSet : (k : Set G) = ⋂ ψ : H.val, (ψ.val : G → Circle) ⁻¹' {1} := by
      ext x
      simp only [k, SetLike.mem_coe, mem_lcaDualAnnihilator_iff, mem_iInter, mem_preimage,
        mem_singleton_iff]
    rw [hSet]
    exact isClosed_iInter fun ψ ↦ isClosed_singleton.preimage ψ.val.continuous
  have hk : IsBruhatGoodSubgroup k :=
    ⟨hkClosed, (lcaAnnihilator_dualAnnihilator_of_open H.val H.property.1).symm ▸ H.property⟩
  have hTrivial (x : k) : χ x.val = 1 :=
    (mem_lcaDualAnnihilator_iff H.val x.val).mp x.property ⟨χ, hχ⟩
  apply (mem_bruhatSmoothSubmodule_iff _).2
  intro p
  refine ⟨k, hk, fun x y ↦ ?_, fun a ha ↦ ?_⟩
  · change (χ (x.val * y) : ℂ) = (χ y : ℂ)
    rw [map_mul, hTrivial, one_mul]
  · let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let χH : a.val.1 →* Circle := χ.toMonoidHom.comp a.val.1.subtype
    have hN : N ≤ χH.ker := by
      intro x hx
      have hxk : (x : G) ∈ k := ha ▸ hx
      exact MonoidHom.mem_ker.mpr (hTrivial ⟨x, hxk⟩)
    let χ₀ : a.quotient →* Circle := QuotientGroup.lift N χH hN
    have hχ₀ : Continuous χ₀ := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (χ.continuous.comp continuous_subtype_val)
    refine ⟨fun x ↦ (χ₀ x : ℂ), fun x ↦ rfl, fun e z b ↦ ?_⟩
    -- Lift the character on the vector cover of the identity fiber to a linear phase.
    let E := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
    let S := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
    let cover : E →+ S :=
      { toFun := fun xt ↦ elementaryCover xt 0 0
        map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
        map_add' := fun x y ↦ Prod.ext rfl (Prod.ext
          (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm) }
    have hCover : Continuous cover := continuous_fst.prodMk
      ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
        ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const)
    let ψ := χ₀.comp e.equiv.symm.toMulEquiv.toMonoidHom
    let circleEquiv : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
    let phase : E →+ AddCircle (1 : ℝ) :=
      { toFun := fun x ↦ circleEquiv.symm (ψ (Multiplicative.ofAdd (cover x)))
        map_zero' := by
          apply circleEquiv.injective
          simp [circleEquiv, AddCircle.homeomorphCircle_apply]
        map_add' := by
          intro x y
          apply circleEquiv.injective
          have hAdd (u v : AddCircle (1 : ℝ)) :
              circleEquiv (u + v) = circleEquiv u * circleEquiv v := by
            simp only [circleEquiv, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
          change circleEquiv (circleEquiv.symm (ψ (Multiplicative.ofAdd (cover (x + y))))) = _
          simp only [circleEquiv.apply_symm_apply, hAdd, map_add]
          exact map_mul ψ (Multiplicative.ofAdd (cover x)) (Multiplicative.ofAdd (cover y)) }
    have hPhase : Continuous phase :=
      circleEquiv.symm.continuous.comp (hχ₀.comp (e.equiv.symm.continuous.comp hCover))
    obtain ⟨L, hL⟩ := exists_addCircle_coe_linearMap_eq phase hPhase
    have hExp (x : E) : ψ (Multiplicative.ofAdd (cover x)) = Circle.exp (2 * Real.pi * L x) := by
      have h := congrArg circleEquiv (hL x)
      have hApply : circleEquiv (phase x) = ψ (Multiplicative.ofAdd (cover x)) :=
        circleEquiv.apply_symm_apply _
      simpa only [hApply, circleEquiv, AddCircle.homeomorphCircle_apply,
        AddCircle.toCircle_apply_mk, div_one] using h.symm
    -- Moving to the fiber indexed by z and b multiplies the character by a constant.
    have hShift (x : E) : cover x + elementaryCover 0 z b = elementaryCover x z b := by
      refine Prod.ext (add_zero _) (Prod.ext ?_ (zero_add _))
      funext j
      change (x.2 j : AddCircle (1 : ℝ)) + ((0 : ℝ) : AddCircle (1 : ℝ)) =
        (x.2 j : AddCircle (1 : ℝ))
      rw [AddCircle.coe_zero, add_zero]
    have hFormula (x : E) : (ψ (Multiplicative.ofAdd (elementaryCover x z b)) : ℂ) =
        Complex.exp (↑(2 * Real.pi * L x) * Complex.I) *
          (ψ (Multiplicative.ofAdd (elementaryCover 0 z b)) : ℂ) := by
      rw [← hShift x]
      change (ψ (Multiplicative.ofAdd (cover x) *
        Multiplicative.ofAdd (elementaryCover 0 z b)) : ℂ) = _
      rw [map_mul, hExp, Circle.coe_mul, Circle.coe_exp]
    change ContDiff ℝ _ (fun x : E ↦ (ψ (Multiplicative.ofAdd (elementaryCover x z b)) : ℂ))
    rw [funext hFormula]
    exact (((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul L.contDiff)).mul
      contDiff_const).cexp).mul contDiff_const

/-- A scalar directional derivative must vanish on constants and hence on all
characters. Character separation then forces its one-parameter subgroup to be trivial. -/
private theorem bruhatDiffGenerator_ne_smul_one (a : LCATopologicalLie G) (ha : a ≠ 1)
    (z : ℂ) : bruhatDiffGenerator a ≠ z • (1 : bruhatDiffAlgebra G) := by
  intro h
  have hEval (f : bruhatSmoothSubmodule (G := G)) (x : G) :
      bruhatDirectionalDeriv a f x = z * f.val x :=
    congrArg (fun D : bruhatDiffAlgebra G ↦ (D.val f).val x) h
  let f₁ : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth 1⟩
  have hz : z = 0 := by
    simpa [f₁, bruhatDirectionalDeriv] using (hEval f₁ 1).symm
  apply ha
  apply ContinuousMonoidHom.ext
  intro u
  change a u = 1
  apply (pontryaginDual_pairing_separates (G := G)).1
  funext χ
  apply Circle.coe_injective
  let f : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩
  let g : ℝ → ℂ := fun t ↦ f.val (a (Multiplicative.ofAdd t))
  have hf := (mem_bruhatSmoothSubmodule_iff f.val).mp f.property 1
  have hg (t : ℝ) : HasDerivAt (fun s ↦ g (t + s)) 0 0 := by
    have hOrbit :
        (fun s : ℝ ↦ f.val (a (Multiplicative.ofAdd t) * a (Multiplicative.ofAdd s))) =
          (fun s : ℝ ↦ g (t + s)) :=
      funext fun s ↦ congrArg f.val (a.map_mul (Multiplicative.ofAdd t) (Multiplicative.ofAdd s)).symm
    have hDeriv := hasDerivAt_bruhatDirectionalDeriv a hf (a (Multiplicative.ofAdd t))
    rw [hEval f, hz, zero_mul, hOrbit] at hDeriv
    exact hDeriv
  have hDiff : Differentiable ℝ g := fun t ↦
    (differentiableAt_iff_comp_const_add (b := t)).mpr
      (by simpa only [neg_add_cancel] using (hg t).differentiableAt)
  have hZero (t : ℝ) : deriv g t = 0 := by
    simpa only [deriv_comp_const_add, add_zero] using (hg t).deriv
  have hConst := is_const_of_deriv_eq_zero hDiff hZero u.toAdd 0
  change (χ (a u) : ℂ) = (χ (a 1) : ℂ) at hConst
  rwa [map_one a] at hConst

/-- Paper: Remark D.1.6.9, p. 768. A nontrivial one-parameter subgroup
gives a differential operator of degree one. -/
theorem bruhatDiffDegree_generator (a : LCATopologicalLie G) (ha : a ≠ 1) :
    bruhatDiffDegree (bruhatDiffGenerator a) = 1 := by
  classical
  let lengths : Set ℕ := {n | ∃ c : List (LCATopologicalLie G) →₀ ℂ,
    c.sum (fun w z ↦ z • bruhatDiffWord w) = bruhatDiffGenerator a ∧
      n = c.support.sup List.length}
  change sInf lengths = 1
  have hOne : 1 ∈ lengths := by
    refine ⟨Finsupp.single [a] 1, ?_, ?_⟩
    · rw [Finsupp.sum_single_index (h := fun w z ↦ z • bruhatDiffWord w) (zero_smul _ _),
        one_smul, bruhatDiffWord_singleton]
    · rw [Finsupp.support_single _ one_ne_zero, Finset.sup_singleton, List.length_singleton]
  refine le_antisymm (csInf_le' hOne) (le_csInf ⟨1, hOne⟩ ?_)
  rintro n ⟨c, hc, rfl⟩
  by_contra! h
  have hSupport : c.support ⊆ {[]} := by
    intro w hw
    have hLength : w.length ≤ c.support.sup List.length := Finset.le_sup hw
    exact Finset.mem_singleton.mpr (List.length_eq_zero_iff.mp (by omega))
  rw [Finsupp.sum_of_support_subset c hSupport (fun w z ↦ z • bruhatDiffWord w)
    (fun _ _ ↦ zero_smul _ _), Finset.sum_singleton] at hc
  exact bruhatDiffGenerator_ne_smul_one a ha (c []) hc.symm

/-- Paper: Definition D.1.6.10, p. 768. The symbol evaluates the differential
operator applied to a character at the group identity. -/
def bruhatDiffSymbol (D : bruhatDiffAlgebra G) (χ : PontryaginDual G) : ℂ :=
  (D.val ⟨fun x : G ↦ (χ x : ℂ), pontryaginDual_mem_bruhatSmooth χ⟩).val 1

/-- Paper: Definition D.1.6.10, p. 768. The identity operator has constant
symbol one.
Deviation: Sanity check on the normalization of the symbol. -/
theorem bruhatDiffSymbol_one (χ : PontryaginDual G) :
    bruhatDiffSymbol (1 : bruhatDiffAlgebra G) χ = 1 := by
  simp [bruhatDiffSymbol]

omit hTop hT2 hLC in
/-- Paper: Example D.1.6.12, p. 768. On the real line, the symbol of the
ordinary derivative at the character of frequency ξ is 2πiξ. -/
theorem bruhatDiffSymbol_real (ξ : ℝ) (χ : PontryaginDual (Multiplicative ℝ))
    (hχ : ∀ x : ℝ, χ (Multiplicative.ofAdd x) = Real.fourierChar (ξ * x)) :
    bruhatDiffSymbol (bruhatDiffGenerator (ContinuousMonoidHom.id (Multiplicative ℝ))) χ =
      2 * ↑Real.pi * Complex.I * (ξ : ℂ) := by
  change deriv (fun t : ℝ ↦ (χ (1 * Multiplicative.ofAdd t) : ℂ)) 0 = _
  simp only [one_mul, hχ]
  have hZero : deriv (fun t ↦ (Real.fourierChar t : ℂ)) 0 = 2 * ↑Real.pi * Complex.I := by
    simpa only [Real.fourierChar_apply', mul_zero, Circle.exp_zero, Circle.coe_one, mul_one]
      using Real.deriv_fourierChar 0
  simpa only [mul_zero, hZero, Complex.real_smul, mul_comm (ξ : ℂ)] using
    deriv_comp_mul_left ξ (fun t ↦ (Real.fourierChar t : ℂ)) 0

/-- Paper: Lemma D.1.6.13, p. 769. A character is an eigenfunction of a word
of first derivatives, with eigenvalue the product of the individual symbols. -/
theorem bruhatDiffWord_character (w : List (LCATopologicalLie G))
    (χ : PontryaginDual G) (x : G) :
    ((bruhatDiffWord w).val ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩).val x =
      (w.map (fun a ↦ bruhatDiffSymbol (bruhatDiffGenerator a) χ)).prod * (χ x : ℂ) :=
  by
    let f : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩
    have hGenerator (a : LCATopologicalLie G) :
        (bruhatDiffGenerator a).val f = bruhatDiffSymbol (bruhatDiffGenerator a) χ • f := by
      apply Subtype.ext
      funext y
      change bruhatDirectionalDeriv a (fun z ↦ (χ z : ℂ)) y =
        bruhatDirectionalDeriv a (fun z ↦ (χ z : ℂ)) 1 * (χ y : ℂ)
      simp only [bruhatDirectionalDeriv, one_mul, map_mul, Circle.coe_mul, deriv_const_mul_field]
      exact mul_comm _ _
    change ((bruhatDiffWord w).val f).val x = _
    induction w with
    | nil => simp [bruhatDiffWord, f]
    | cons a w ih =>
      have hWord : bruhatDiffWord (a :: w) = bruhatDiffWord w * bruhatDiffGenerator a := by
        simp [bruhatDiffWord, List.reverse_cons, List.prod_append]
      rw [hWord]
      change ((bruhatDiffWord w).val ((bruhatDiffGenerator a).val f)).val x = _
      rw [hGenerator, map_smul]
      change bruhatDiffSymbol (bruhatDiffGenerator a) χ * ((bruhatDiffWord w).val f).val x = _
      rw [ih, List.map_cons, List.prod_cons, mul_assoc]

/-- Paper: Lemma D.1.6.13, p. 769. The symbol of a word is the product
of its first-order symbols. -/
theorem bruhatDiffSymbol_word (w : List (LCATopologicalLie G)) (χ : PontryaginDual G) :
    bruhatDiffSymbol (bruhatDiffWord w) χ =
      (w.map (fun a ↦ bruhatDiffSymbol (bruhatDiffGenerator a) χ)).prod := by
  simpa only [bruhatDiffSymbol, map_one, Circle.coe_one, mul_one] using
    bruhatDiffWord_character w χ 1

/-- Paper: Lemma D.1.6.13, p. 769. The symbol is invariant under every
compact subgroup of the dual. -/
theorem bruhatDiffSymbol_compact_invariant (D : bruhatDiffAlgebra G)
    (K : Subgroup (PontryaginDual G)) (hK : IsCompact (K : Set (PontryaginDual G)))
    (χ : PontryaginDual G) (k : K) :
    bruhatDiffSymbol D (χ * k.val) = bruhatDiffSymbol D χ := by
  let U := lcaDualAnnihilator K
  have hU : IsOpen (U : Set G) := by
    convert (isOpen_lcaAnnihilator K hK).preimage
      (pontryaginDual_eval (G := G)).continuous using 1
    ext x
    exact (mem_lcaDualAnnihilator_iff K x).trans
      (mem_lcaAnnihilator_iff K (pontryaginDual_eval x)).symm
  -- Every operator in the generated algebra preserves agreement on the open annihilator.
  have hD : ∀ (f g : bruhatSmoothSubmodule (G := G)), EqOn f.val g.val U →
      EqOn (D.val f).val (D.val g).val U := by
    refine Algebra.adjoin_induction (s := range (bruhatFirstOrder (G := G)))
      (p := fun A _ ↦ ∀ (f g : bruhatSmoothSubmodule (G := G)), EqOn f.val g.val U →
        EqOn (A f).val (A g).val U) ?_ ?_ ?_ ?_ D.property
    · rintro _ ⟨a, rfl⟩ f g hfg x hx
      rw [bruhatFirstOrder_apply, bruhatFirstOrder_apply, bruhatDirectionalDeriv]
      have hOrbit : Continuous (fun t : ℝ ↦ x * a (Multiplicative.ofAdd t)) :=
        continuous_const.mul a.continuous
      have hAt : x * a (Multiplicative.ofAdd (0 : ℝ)) = x := by
        change x * a 1 = x
        rw [map_one, mul_one]
      have hNear := hOrbit.tendsto' 0 x hAt (hU.mem_nhds hx)
      exact EventuallyEq.deriv_eq (mem_of_superset hNear fun _ ht ↦ hfg ht)
    · intro c f g hfg x hx
      change (c • f).val x = (c • g).val x
      simp only [Submodule.coe_smul, Pi.smul_apply, hfg hx]
    · intro A B _ _ hA hB f g hfg x hx
      simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, hA f g hfg hx, hB f g hfg hx]
    · intro A B _ _ hA hB f g hfg
      exact hA (B f) (B g) (hB f g hfg)
  refine hD ⟨_, pontryaginDual_mem_bruhatSmooth (χ * k.val)⟩
    ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩ (fun x hx ↦ ?_) U.one_mem
  have hkx : k.val x = 1 := (mem_lcaDualAnnihilator_iff K x).mp hx k
  change (↑(χ x * k.val x) : ℂ) = ↑(χ x)
  rw [hkx, mul_one]

/-- Paper: Lemma D.1.6.14, p. 769. Real first-order operators correspond
bijectively and real-linearly to continuous real-valued homomorphisms on the dual.
The exponential formula is the commutativity of the diagram on characters.
Deviation: Real linearity is expressed by the pointwise laws on the target. -/
theorem bruhatDiffDegreeOne_frequency :
    ∃ σ : bruhatDiffDegreeOneReal (G := G) ≃ (PontryaginDual G →ₜ* Multiplicative ℝ),
      (∀ D E χ, (σ (D + E) χ).toAdd = (σ D χ).toAdd + (σ E χ).toAdd) ∧
      (∀ (c : ℝ) D χ, (σ (c • D) χ).toAdd = c * (σ D χ).toAdd) ∧
      ∀ (a : LCATopologicalLie G) (D : bruhatDiffDegreeOneReal (G := G)),
        D.val = bruhatFirstOrder a → ∀ χ (t : ℝ),
          Real.fourierChar ((σ D χ).toAdd * t) = χ (a (Multiplicative.ofAdd t)) :=
  by
    obtain ⟨dual, hDual⟩ := lcaTopologicalLie_dual (G := G)
    obtain ⟨realDual, hRealDual⟩ := exists_realPontryaginDualEquiv
    have hPair (r : Multiplicative ℝ) (t : ℝ) :
        realDual r (Multiplicative.ofAdd t) = Real.fourierChar (r.toAdd * t) :=
      hRealDual r.toAdd t
    let postcomp : (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)) ≃
        (PontryaginDual G →ₜ* Multiplicative ℝ) :=
      { toFun := fun b ↦ (realDual.symm : _ →ₜ* _).comp b
        invFun := fun b ↦ (realDual : _ →ₜ* _).comp b
        left_inv := fun b ↦ ContinuousMonoidHom.ext fun χ ↦ realDual.apply_symm_apply (b χ)
        right_inv := fun b ↦ ContinuousMonoidHom.ext fun χ ↦ realDual.symm_apply_apply (b χ) }
    let freq := dual.toEquiv.trans postcomp
    have hFreq (a : LCATopologicalLie G) (χ : PontryaginDual G) (t : ℝ) :
        Real.fourierChar ((freq a χ).toAdd * t) = χ (a (Multiplicative.ofAdd t)) := by
      rw [← hPair]
      change realDual (realDual.symm (dual a χ)) (Multiplicative.ofAdd t) = _
      rw [realDual.apply_symm_apply, hDual, PontryaginDual.map_apply]
    -- The derivative of each character at the identity determines its frequency.
    have hDeriv (a : LCATopologicalLie G) (χ : PontryaginDual G) :
        bruhatDirectionalDeriv a (fun x ↦ (χ x : ℂ)) 1 =
          (freq a χ).toAdd • (2 * ↑Real.pi * Complex.I) := by
      simp only [bruhatDirectionalDeriv, one_mul, ← hFreq a χ]
      have hZero : deriv (fun t ↦ (Real.fourierChar t : ℂ)) 0 = 2 * ↑Real.pi * Complex.I := by
        simpa only [Real.fourierChar_apply', mul_zero, Circle.exp_zero, Circle.coe_one, mul_one]
          using Real.deriv_fourierChar 0
      simpa only [mul_zero, hZero] using
        deriv_comp_mul_left (freq a χ).toAdd (fun t ↦ (Real.fourierChar t : ℂ)) 0
    let firstOrder (a : LCATopologicalLie G) : bruhatDiffDegreeOneReal (G := G) :=
      ⟨bruhatFirstOrder a, Submodule.subset_span ⟨a, rfl⟩⟩
    have hInjective : Function.Injective firstOrder := by
      intro a b hab
      apply freq.injective
      apply ContinuousMonoidHom.ext
      intro χ
      let f : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩
      have h := congrArg (fun D : bruhatDiffDegreeOneReal (G := G) ↦ (D.val f).val 1) hab
      change bruhatDirectionalDeriv a (fun x ↦ (χ x : ℂ)) 1 =
        bruhatDirectionalDeriv b (fun x ↦ (χ x : ℂ)) 1 at h
      rw [hDeriv, hDeriv] at h
      exact smul_left_injective ℝ (by simp [Real.pi_ne_zero]) h
    have hSurjective : Function.Surjective firstOrder := by
      intro D
      obtain ⟨a, ha⟩ := (mem_bruhatDiffDegreeOneReal_iff D.val).mp D.property
      exact ⟨a, Subtype.ext ha.symm⟩
    let firstOrderEquiv := Equiv.ofBijective firstOrder ⟨hInjective, hSurjective⟩
    let σ := firstOrderEquiv.symm.trans freq
    have hσ (D : bruhatDiffDegreeOneReal (G := G)) (a : LCATopologicalLie G)
        (ha : D.val = bruhatFirstOrder a) : σ D = freq a := by
      have h : firstOrderEquiv a = D := Subtype.ext ha.symm
      change freq (firstOrderEquiv.symm D) = freq a
      rw [← h, Equiv.symm_apply_apply]
    refine ⟨σ, ?_, ?_, fun a D ha χ t ↦ by rw [hσ D a ha, hFreq]⟩
    · intro D E χ
      obtain ⟨a, rfl⟩ := hSurjective D
      obtain ⟨b, rfl⟩ := hSurjective E
      rw [hσ _ (a * b) (bruhatFirstOrder_mul a b).symm, hσ _ a rfl, hσ _ b rfl]
      change (realDual.symm (dual (a * b) χ)).toAdd =
        (realDual.symm (dual a χ)).toAdd + (realDual.symm (dual b χ)).toAdd
      rw [map_mul, ContinuousMonoidHom.mul_apply, map_mul]
      rfl
    · intro c D χ
      obtain ⟨a, rfl⟩ := hSurjective D
      let scale : LCATopologicalLie (Multiplicative ℝ) :=
        ⟨(c • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative,
          continuous_const_mul c⟩
      rw [hσ _ (a.comp scale) (bruhatFirstOrder_scale a c).symm, hσ _ a rfl]
      change freq (a.comp scale) χ = Multiplicative.ofAdd (c * (freq a χ).toAdd)
      apply realDual.injective
      apply PontryaginDual.ext
      intro t
      change realDual (freq (a.comp scale) χ) (Multiplicative.ofAdd t.toAdd) =
        realDual (Multiplicative.ofAdd (c * (freq a χ).toAdd)) (Multiplicative.ofAdd t.toAdd)
      rw [hPair, hPair, hFreq]
      change χ (a (Multiplicative.ofAdd (c * t.toAdd))) =
        Real.fourierChar ((c * (freq a χ).toAdd) * t.toAdd)
      rw [show (c * (freq a χ).toAdd) * t.toAdd = (freq a χ).toAdd * (c * t.toAdd) by ring,
        hFreq]

/-- Paper: Corollary D.1.6.15, p. 770. The first-order symbol is the real
frequency multiplied by 2πi. The frequency is identified by the character pairing. -/
theorem bruhatDiffSymbol_generator (a : LCATopologicalLie G) (χ : PontryaginDual G)
    (r : ℝ) (hr : ∀ t : ℝ, Real.fourierChar (r * t) = χ (a (Multiplicative.ofAdd t))) :
    bruhatDiffSymbol (bruhatDiffGenerator a) χ = 2 * ↑Real.pi * Complex.I * (r : ℂ) := by
  have h := bruhatDiffSymbol_real r (PontryaginDual.map a χ) (fun t ↦ (hr t).symm)
  change deriv (fun t : ℝ ↦ (PontryaginDual.map a χ (1 * Multiplicative.ofAdd t) : ℂ)) 0 = _ at h
  change deriv (fun t : ℝ ↦ (χ (1 * a (Multiplicative.ofAdd t)) : ℂ)) 0 = _
  simpa only [one_mul, PontryaginDual.map_apply] using h

end DifferentialOperators

/-- Smoothness on the covering space descends to continuity on each discrete fiber. -/
private theorem elementarySchwartz_continuousFunction {m n r : ℕ} {F : Type*}
    [TopologicalSpace F] [DiscreteTopology F] (f : ElementarySchwartz m n r F) : Continuous f.val := by
  let q (t : EuclideanSpace ℝ (Fin n)) : Fin n → AddCircle (1 : ℝ) := fun j ↦ (t j : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q := by
    exact (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  let e := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ))
    ((Fin r → ℤ) × F)
  apply e.isQuotientMap.continuous_iff.mpr
  apply continuous_prod_of_discrete_right.mpr
  intro z
  exact (IsOpenQuotientMap.id.prodMap hq).isQuotientMap.continuous_iff.mpr
    (f.property.1 z.1 z.2).continuous

section FourierPairing

open scoped BoundedContinuousFunction ZeroAtInfty

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Every stage realization extends to a bounded continuous function on the group. -/
private theorem schwartzBruhat_boundedContinuous (f : SchwartzBruhat G) :
    ∃ g : G →ᵇ ℂ, ∀ x, g x = f x := by
  classical
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  let p := elementarySchwartzSeminorm (m := e.realDim) (n := e.torusDim) (r := e.latticeRank)
    (F := e.finiteFactor) (0,0,0,0)
  have hb (y) : ‖s y‖ ≤ p s := by
    change (‖s y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound s.val (0,0,0,0)).toReal
    apply ENNReal.toReal_mono (s.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun w ↦ (‖s w‖₊ : ENNReal)) y
  have hopen := a.property.1
  have hclosed := a.val.1.isClosed_of_isOpen hopen
  let u := schwartzBruhatStageRealization a e s
  have hu : Continuous u := by
    rw [← continuousOn_univ, ← union_compl_self (a.val.1 : Set G),
      continuousOn_union_iff_of_isOpen hopen hclosed.isOpen_compl]
    constructor
    · rw [continuousOn_iff_continuous_domRestrict]
      refine ((elementarySchwartz_continuousFunction s).comp (continuous_toAdd.comp
        (e.equiv.continuous.comp QuotientGroup.continuous_mk))).congr fun y ↦ ?_
      change _ = schwartzBruhatStageRealization a e s (y : G)
      rw [schwartzBruhatStageRealization_apply, dite_eq_left y.property]
      rfl
    · apply continuousOn_const.congr
      intro y hy
      change schwartzBruhatStageRealization a e s y = 0
      rw [schwartzBruhatStageRealization_apply, dite_eq_right (show y ∉ a.val.1 from hy)]
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup u hu (p s) (fun x ↦ ?_), congrFun hs⟩
  dsimp only [u]
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact hb _
  · rw [norm_zero]
    exact apply_nonneg p s

variable [MeasurableSpace G] [BorelSpace G]
private local instance inverseFourierDualMeasurableSpace : MeasurableSpace (PontryaginDual G) := borel _
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (ν : @Measure (PontryaginDual G) (borel _))
omit [μ.IsHaarMeasure] in
/-- The inverse Fourier integral and the forward transform are adjoint on integrable
test functions. Compactly supported approximations provide a product-measurable kernel
even when the product topology and product σ-algebra have different Borel sets. -/
private theorem lcaInverseFourier_integral_pairing
    {u : PontryaginDual G → ℂ} {q : G → ℂ} (hu : Integrable u ν) (hq : Integrable q μ)
    [ν.Regular] :
    (∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ) =
      ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨S, -, hqZero, hSσ⟩ := hq.aefinStronglyMeasurable.exists_set_sigmaFinite
  obtain ⟨T, -, huZero, hTσ⟩ := hu.aefinStronglyMeasurable.exists_set_sigmaFinite
  let := hSσ
  let := hTσ
  have hqZero := ae_imp_of_ae_restrict hqZero
  have huZero := ae_imp_of_ae_restrict huZero
  obtain ⟨Q, hQc, hQ, htQ⟩ := exists_tendsto_ae_compactSupport hq
  obtain ⟨U, hUc, hU, htU⟩ := exists_tendsto_ae_compactSupport hu
  let K (x : G) (χ : PontryaginDual G) := (u χ * (χ x : ℂ)) * star (q x)
  let A (n : ℕ) (p : G × PontryaginDual G) := (U n p.2 * (p.2 p.1 : ℂ)) * star (Q n p.1)
  have hEval : Continuous (fun p : G × PontryaginDual G ↦ (p.2 p.1 : ℂ)) :=
    continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_snd).prodMk continuous_fst))
  have hA (n : ℕ) : StronglyMeasurable (A n) := by
    apply HasCompactSupport.stronglyMeasurable_of_prod
      ((((hU n).comp continuous_snd).mul hEval).mul ((hQ n).comp continuous_fst).star)
    refine HasCompactSupport.intro ((hQc n).prod (hUc n)) ?_
    intro p hp
    by_cases hq : p.1 ∈ tsupport (Q n)
    · have hu : U n p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun hu ↦ hp ⟨hq, hu⟩)
      simp [hu]
    · simp [image_eq_zero_of_notMem_tsupport hq]
  let k (p : G × PontryaginDual G) := limUnder atTop (fun n ↦ A n p)
  have hk : StronglyMeasurable k := StronglyMeasurable.limUnder hA
  have hLimit : ∀ᵐ x ∂μ, ∀ᵐ χ ∂ν, k (x, χ) = K x χ := by
    filter_upwards [htQ] with x hx
    filter_upwards [htU] with χ hχ
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hLimit' : ∀ᵐ χ ∂ν, ∀ᵐ x ∂μ, k (x, χ) = K x χ := by
    filter_upwards [htU] with χ hχ
    filter_upwards [htQ] with x hx
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hChar (x : G) : AEStronglyMeasurable (fun χ : PontryaginDual G ↦ (χ x : ℂ)) ν :=
    (hEval.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hRow (x : G) : Integrable (K x) ν :=
    (hu.mul_bdd (c := 1) (hChar x) (.of_forall fun χ ↦ (Circle.norm_coe (χ x)).le)).mul_const _
  have hInt : Integrable k ((μ.restrict S).prod (ν.restrict T)) := by
    apply (integrable_prod_iff hk.aestronglyMeasurable).2
    have hLim : ∀ᵐ x ∂μ.restrict S, (fun χ ↦ k (x, χ)) =ᵐ[ν.restrict T] K x :=
      ae_restrict_of_ae (hLimit.mono fun _ hx ↦ ae_restrict_of_ae hx)
    refine ⟨hLim.mono fun x hx ↦ (hRow x).restrict.congr hx.symm, ?_⟩
    refine (hq.norm.mul_const (∫ χ in T, ‖u χ‖ ∂ν)).restrict.congr ?_
    filter_upwards [hLim] with x hx
    symm
    calc
      _ = ∫ χ in T, ‖K x χ‖ ∂ν := integral_congr_ae (hx.mono fun χ hχ ↦ congrArg norm hχ)
      _ = _ := by simp [K, integral_mul_const, mul_comm]
  have hrowEq : ∀ᵐ x ∂μ, (∫ χ in T, k (x, χ) ∂ν) = ∫ χ, K x χ ∂ν := by
    filter_upwards [hLimit] with x hx
    rw [integral_congr_ae (ae_restrict_of_ae hx)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem]
  have hcolEq : ∀ᵐ χ ∂ν, (∫ x in S, k (x, χ) ∂μ) = ∫ x, K x χ ∂μ := by
    filter_upwards [hLimit'] with χ hχ
    rw [integral_congr_ae (ae_restrict_of_ae hχ)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem]
  calc
    _ = ∫ x, ∫ χ, K x χ ∂ν ∂μ := by simp_rw [K, integral_mul_const]
    _ = ∫ x in S, ∫ χ, K x χ ∂ν ∂μ := by
      symm
      exact setIntegral_eq_integral_of_ae_compl_eq_zero
        (hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem])
    _ = ∫ x in S, ∫ χ in T, k (x, χ) ∂ν ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hrowEq.mono fun _ hx ↦ hx.symm))
    _ = ∫ χ in T, ∫ x in S, k (x, χ) ∂μ ∂ν := integral_integral_swap hInt
    _ = ∫ χ in T, ∫ x, K x χ ∂μ ∂ν := integral_congr_ae (ae_restrict_of_ae hcolEq)
    _ = ∫ χ, ∫ x, K x χ ∂μ ∂ν := setIntegral_eq_integral_of_ae_compl_eq_zero
      (huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem])
    _ = _ := by
      congr with χ
      simp only [K, mul_assoc, integral_const_mul, lcaFourier, Complex.star_def,
        ← integral_conj, map_mul, starRingEnd_self_apply]
      congr 1
      apply integral_congr_ae
      exact .of_forall fun x ↦ mul_comm _ _

/-- Invert an integrable Plancherel transform by pairing against indicators of finite-measure sets. -/
private theorem lcaInverseFourier_zeroAtInfty (hν : IsLCAPlancherelMeasure μ ν)
    (v : Lp ℂ 2 μ) (u : PontryaginDual G → ℂ) (hu : Integrable u ν)
    (hv : ((lcaFourier_unitary μ ν hν).exists.choose v : PontryaginDual G → ℂ) =ᵐ[ν] u) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] (v : G → ℂ) ∧
      ∀ x, F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨H, hH⟩ := lcaFourier_zeroAtInfty ν hu
  let e : CocompactMap G (PontryaginDual (PontryaginDual G)) :=
    ⟨⟨pontryaginDual_eval, pontryaginDual_eval.continuous⟩,
      isClosedEmbedding_pontryaginDual_eval.tendsto_cocompact⟩
  let F : C₀(G, ℂ) := (H.comp e).comp
    ⟨⟨Inv.inv, continuous_inv⟩, (Homeomorph.inv G).isClosedEmbedding.tendsto_cocompact⟩
  have hF (x : G) : F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
    change H (pontryaginDual_eval x⁻¹) = _
    rw [hH]
    unfold lcaFourier
    apply integral_congr_ae
    exact .of_forall fun χ ↦ by
      change u χ * star (χ x⁻¹ : ℂ) = _
      rw [map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  refine ⟨F, ?_, hF⟩
  -- The nonzero set of a function in C₀ lies in a countable union of compact sets.
  let K (n : ℕ) : Set G := {x | 1 / ((n : ℝ) + 1) ≤ ‖F x‖}
  have hK (n : ℕ) : IsCompact (K n) := by
    have hc : IsClosed (K n) := isClosed_le continuous_const F.continuous.norm
    obtain ⟨L, hL, hsub⟩ := mem_cocompact.mp
      ((Metric.tendsto_nhds.mp F.zero_at_infty') _ (by positivity : 0 < 1 / ((n : ℝ) + 1)))
    exact hL.of_isClosed_subset hc fun x hx ↦ by
      by_contra hxL
      change 1 / ((n : ℝ) + 1) ≤ ‖F x‖ at hx
      have hlt : dist (F x) 0 < 1 / ((n : ℝ) + 1) := hsub hxL
      exact not_lt_of_ge hx (dist_zero_right (F x) ▸ hlt)
  let S := ⋃ n, K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  have hFS : ∀ x ∈ Sᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hne)
    exact hx (mem_iUnion.mpr ⟨n, hn.le⟩)
  have hσ : SigmaFinite (μ.restrict S) := by
    refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hS.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
    · rw [← iUnion_union]
      exact union_compl_self S
  have hFin : AEFinStronglyMeasurable (F : G → ℂ) μ :=
    (F.continuous.stronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite
      hS hFS hσ).aefinStronglyMeasurable
  apply AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq _ _ _
    hFin ((Lp.memLp v).aefinStronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top)
  · intro A _ hA
    let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA.ne
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F.toBCF‖
      (.of_forall F.toBCF.norm_coe_le_norm)
  · exact fun A _ hA ↦ integrableOn_Lp_of_measure_ne_top v (by norm_num) hA.ne
  · intro A hA hAμ
    let q : G → ℂ := A.indicator fun _ ↦ 1
    have hq : Integrable q μ := memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 hA.nullMeasurableSet 1 (.inr hAμ.ne))
    have hq₂ : MemLp q 2 μ := memLp_indicator_const 2 hA.nullMeasurableSet 1 (.inr hAμ.ne)
    let U := (lcaFourier_unitary μ ν hν).exists.choose
    have hU := (lcaFourier_unitary μ ν hν).exists.choose_spec q hq hq₂
    have hIndic (g : G → ℂ) : (∫ x, g x * star (q x) ∂μ) = ∫ x in A, g x ∂μ := by
      rw [← integral_indicator hA]
      congr with x
      by_cases hx : x ∈ A <;> simp [q, hx]
    calc
      _ = ∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ := by
        simp_rw [← hF]
        exact (hIndic F).symm
      _ = ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν :=
        lcaInverseFourier_integral_pairing μ ν hu hq
      _ = inner ℂ (U (hq₂.toLp q)) (U v) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hv, hU] with χ hχ hχ'
        rw [RCLike.inner_apply, starRingEnd_apply, hχ, hχ']
      _ = inner ℂ (hq₂.toLp q) v := U.inner_map_map _ _
      _ = _ := by
        rw [← hIndic v, L2.inner_def]
        exact integral_congr_ae (hq₂.coeFn_toLp.mono fun x hx ↦ by
          change inner ℂ ((hq₂.toLp q) x) (v x) = v x * star (q x)
          rw [RCLike.inner_apply, starRingEnd_apply, hx])

end FourierPairing

section StructuralProjectors

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
private local instance projectorDualMeasurableSpace : MeasurableSpace (PontryaginDual G) := borel _
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Translation invariance makes the average of evaluations the indicator of the double annihilator. -/
private theorem integral_annihilator_eval (J : Subgroup G) (hJ : IsClosed (J : Set G))
    (η : Measure (lcaAnnihilator J)) [η.IsHaarMeasure] [IsProbabilityMeasure η] (x : G) :
    (∫ ψ : lcaAnnihilator J, (ψ.val x : ℂ) ∂η) = (J : Set G).indicator 1 x := by
  classical
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  by_cases hx : x ∈ J
  · rw [indicator_of_mem hx]
    simp only [fun ψ : lcaAnnihilator J ↦ (mem_lcaAnnihilator_iff J ψ.val).mp ψ.property ⟨x,hx⟩,
      Circle.coe_one,integral_const, Measure.real,measure_univ, ENNReal.toReal_one, one_smul, Pi.one_apply]
  · rw [indicator_of_notMem hx]
    have hnx : x ∉ lcaDualAnnihilator (lcaAnnihilator J) := by rwa [lcaDualAnnihilator_annihilator J hJ]
    obtain ⟨ψ,hψ⟩ := not_forall.mp (mt (mem_lcaDualAnnihilator_iff _ x).mpr hnx)
    have ht := integral_mul_left_eq_self (μ := η) (fun z : lcaAnnihilator J ↦ (z.val x : ℂ)) ψ
    change (∫ z : lcaAnnihilator J, (ψ.val x : ℂ) * (z.val x : ℂ) ∂η) = _ at ht
    rw [integral_const_mul] at ht
    by_contra hn
    exact hψ (Circle.ext ((mul_eq_right₀ hn).mp ht))

/-- Pair the twisted function with probability Haar on the annihilator to compute the transform of a cutoff. -/
private theorem lcaFourier_cutoff (J : Subgroup G) (hJ : IsOpen (J : Set G))
    (η : Measure (lcaAnnihilator J)) [η.IsHaarMeasure] [IsProbabilityMeasure η]
    {f : G → ℂ} (hf : Integrable f μ) (χ : PontryaginDual G) :
    lcaFourier μ ((J : Set G).indicator f) χ = ∫ ψ : lcaAnnihilator J, lcaFourier μ f (χ * ψ.val) ∂η := by
  classical
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hJc := J.isClosed_of_isOpen hJ
  have hA := isCompact_lcaAnnihilator J hJ
  let : CompactSpace (lcaAnnihilator J) := isCompact_iff_compactSpace.mp hA
  let ν := η.map (Subtype.val : lcaAnnihilator J → PontryaginDual G)
  let : ν.InnerRegular := Measure.InnerRegular.map_of_continuous continuous_subtype_val
  let : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.map _ η))
  have hmap (u : PontryaginDual G → ℂ) : (∫ ψ, u ψ ∂ν) = ∫ ψ : lcaAnnihilator J, u ψ.val ∂η :=
    hA.isClosed.isClosedEmbedding_subtypeVal.integral_map u
  let t (y : G) := f y * star (χ y : ℂ)
  have ht : Integrable t μ := integrable_fourierIntegrand μ hf χ
  have heq (ψ : PontryaginDual G) : lcaFourier μ t ψ = lcaFourier μ f (χ * ψ) := by
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      change (f y * star (χ y : ℂ)) * star (ψ y : ℂ) = f y * star ((χ y : ℂ) * (ψ y : ℂ))
      rw [star_mul]
      ring
  have h := lcaInverseFourier_integral_pairing μ ν (u := fun _ ↦ 1) (q := t) (integrable_const _) ht
  simp only [one_mul,heq] at h
  rw [hmap] at h
  have heval (x : G) : (∫ ψ : PontryaginDual G, (ψ x : ℂ) ∂ν) = (J : Set G).indicator 1 x :=
    (hmap _).trans (integral_annihilator_eval J hJc η x)
  simp_rw [heval] at h
  have h' := congrArg star h
  simp only [Complex.star_def, ← integral_conj, map_mul, starRingEnd_self_apply] at h'
  refine Eq.trans ?_ h'
  unfold lcaFourier
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ J <;> simp [hx,t]

/-- Apply the Weil formula to a compact average at trivial characters and translation invariance elsewhere. -/
private theorem lcaFourier_compact_average (K : Subgroup G) (hK : IsCompact (K : Set G))
    (η : Measure K) [η.IsHaarMeasure] [IsProbabilityMeasure η]
    {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hav : ∀ x, g x = ∫ k : K, f (x * k.val) ∂η) (χ : PontryaginDual G) :
    lcaFourier μ g χ = (lcaAnnihilator K : Set (PontryaginDual G)).indicator (lcaFourier μ f) χ := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hinv (x : G) (k : K) : g (x * k.val) = g x := by
    rw [hav,hav]
    simpa only [Subgroup.coe_mul,mul_assoc] using
      (integral_mul_left_eq_self (μ := η) (fun h : K ↦ f (x * h.val)) k)
  by_cases hχ : χ ∈ lcaAnnihilator K
  · rw [indicator_of_mem hχ]
    let : MeasurableSpace (G ⧸ K) := borel _
    obtain ⟨μQ,hQ,-⟩ := weilQuotientMeasure_existsUnique K hK.isClosed μ η
    let t (u : G → ℂ) (x : G) := u x * star (χ x : ℂ)
    have hgt := integrable_fourierIntegrand μ hg χ
    have hft := integrable_fourierIntegrand μ hf χ
    change (∫ x, t g x ∂μ) = ∫ x, t f x ∂μ
    refine (weilQuotientIntegral_L1 K hK.isClosed μ η μQ hQ hgt).2.2.trans ?_
    refine Eq.trans ?_ (weilQuotientIntegral_L1 K hK.isClosed μ η μQ hQ hft).2.2.symm
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    have hχk (k : K) : χ (z.out * k.val) = χ z.out := by
      rw [map_mul,(mem_lcaAnnihilator_iff K χ).mp hχ k,mul_one]
    change (∫ k : K, g (z.out * k.val) * star (χ (z.out * k.val) : ℂ) ∂η) =
      ∫ k : K, f (z.out * k.val) * star (χ (z.out * k.val) : ℂ) ∂η
    simp_rw [hχk, hinv, integral_mul_const]
    simp [hav]
  · rw [indicator_of_notMem hχ]
    obtain ⟨k,hk⟩ := not_forall.mp (mt (mem_lcaAnnihilator_iff K χ).mpr hχ)
    have h := lcaFourier_translate μ g k.val χ
    have he : (fun x ↦ g (k.val * x)) = g := funext fun x ↦ by rw [mul_comm,hinv]
    rw [he] at h
    by_contra hn
    exact hk (Circle.ext ((mul_eq_right₀ hn).mp h.symm))

/-- Normalized Haar integration is independent of the chosen Borel measurable-space instance. -/
private theorem integral_eq_normalized_compact_haar {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [CompactSpace H] [m : MeasurableSpace H] [hB : BorelSpace H]
    (η : Measure H) [η.IsHaarMeasure] [IsProbabilityMeasure η] (u : H → ℂ) :
    (letI : MeasurableSpace H := borel _
     let : BorelSpace H := ⟨rfl⟩
     ∫ y, u y ∂Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩, by simp⟩ : TopologicalSpace.PositiveCompacts H)) =
      ∫ y, u y ∂η := by
  obtain rfl := hB.measurable_eq
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let U : TopologicalSpace.PositiveCompacts H := ⟨⟨univ,isCompact_univ⟩,by simp⟩
  let : IsProbabilityMeasure (Measure.haarMeasure U) := ⟨Measure.haarMeasure_self⟩
  change (∫ y, u y ∂Measure.haarMeasure U) = _
  rw [Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.haarMeasure U) η]

/-- Compute the structural stage projection using any normalized Haar measure on its kernel. -/
private theorem schwartzBruhatStageAverage_normalized (a : BruhatStructuralPair G)
    (hK : IsCompact ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G))
    (η : Measure ↥(OrderDual.ofDual a.val.2)) [η.IsHaarMeasure] [IsProbabilityMeasure η]
    (f : G → ℂ) (x : G) : schwartzBruhatStageAverage a f x =
      (a.val.1 : Set G).indicator (fun x ↦ ∫ k : ↥(OrderDual.ofDual a.val.2), f (x * k.val) ∂η) x := by
  classical
  let K := OrderDual.ofDual a.val.2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  by_cases hx : x ∈ a.val.1
  · rw [indicator_of_mem hx]
    unfold schwartzBruhatStageAverage
    rw [ite_eq_left hx]
    refine (integral_eq_normalized_compact_haar η (fun k : K ↦ f (k.val * x))).trans ?_
    simp only [mul_comm _ x]
  · rw [indicator_of_notMem hx]
    unfold schwartzBruhatStageAverage
    rw [ite_eq_right hx]

end StructuralProjectors

section FourierDifferentiation

open scoped Pointwise Interval

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Powers of a symmetric compact generating set cover the group. -/
private theorem sigmaCompact_of_compactlyGenerated (hG : IsCompactlyGeneratedGroup G) : SigmaCompactSpace G := by
  obtain ⟨U,-,hc,hu⟩ := hG
  let C := U ∪ U⁻¹
  have hC : IsCompact C := hc.union hc.inv
  have hi : C⁻¹ = C := by simp [C,union_comm]
  have hall (x : G) (hx : x ∈ Subgroup.closure U) : ∃ n : ℕ, x ∈ C^n := by
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact ⟨1, by simpa using (show x ∈ C from Or.inl hx)⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i,hi⟩ := hx
      obtain ⟨j,hj⟩ := hy
      exact ⟨i+j, pow_add C i j ▸ Set.mul_mem_mul hi hj⟩
    | inv x _ hx =>
      obtain ⟨i,hi'⟩ := hx
      exact ⟨i, by simpa only [← inv_pow,hi] using (Set.inv_mem_inv.mpr hi')⟩
  have he : ⋃ n : ℕ, C^n = univ := iUnion_eq_univ_iff.mpr fun x ↦ hall x (by rw [hu]; trivial)
  have hp (n : ℕ) : IsCompact (C^n) := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [pow_succ] using ih.mul hC
  exact ⟨⟨fun n ↦ C^n,hp,he⟩⟩

/-- A Schwartz function is supported on a σ-compact open subgroup. -/
private theorem schwartzBruhat_supported_open (f : SchwartzBruhat G) :
    ∃ J : Subgroup G, IsOpen (J : Set G) ∧ IsSigmaCompact (J : Set G) ∧ ∀ x ∉ J, f x = 0 := by
  classical
  obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  let J := a.val.1
  let : LocallyCompactSpace J := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : SigmaCompactSpace J := sigmaCompact_of_compactlyGenerated a.property.2.1
  refine ⟨J,a.property.1,?_,fun x hx ↦ ?_⟩
  · exact Subtype.range_coe (s := (J : Set G)) ▸ isSigmaCompact_range continuous_subtype_val
  · exact (congrFun hs x).symm.trans ((schwartzBruhatStageRealization_apply a e s x).trans (dite_eq_right hx))

/-- The Haar measure restricted to a σ-compact support is σ-finite. -/
private theorem sigmaFinite_restrict_sigmaCompact [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {S : Set G} (hS : IsSigmaCompact S) : SigmaFinite (μ.restrict S) := by
  obtain ⟨K,hK,hKS⟩ := hS
  have hm : MeasurableSet S := hKS ▸ MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
  · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hm.compl),union_inter_distrib_right,
      compl_inter_self,union_empty]
    exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
  · rw [← iUnion_union,hKS,union_compl_self]

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Integrate along a unit time interval, then use translation invariance on the σ-compact support. -/
private theorem integral_orbit_derivative_zero (a : LCATopologicalLie G) {w v : G → ℂ}
    (hw : Integrable w μ) (hv : Integrable v μ) (hc : Continuous v)
    (J : Subgroup G) (hJ : IsOpen (J : Set G)) (hσ : IsSigmaCompact (J : Set G))
    (h0 : ∀ x ∉ J, v x = 0)
    (hd : ∀ x : G, HasDerivAt (fun t : ℝ ↦ w (x * a (Multiplicative.ofAdd t))) (v x) 0) :
    ∫ x, v x ∂μ = 0 := by
  let b (t : ℝ) := a (Multiplicative.ofAdd t)
  have hb : Continuous b := a.continuous.comp continuous_ofAdd
  have hmem (t : ℝ) : b t ∈ J := by
    let : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    exact (isPreconnected_range a.continuous).subset_isClopen ⟨J.isClosed_of_isOpen hJ,hJ⟩
      ⟨1,⟨1,map_one a⟩,J.one_mem⟩ (mem_range_self _)
  have htime (x : G) (t : ℝ) : HasDerivAt (fun s ↦ w (x * b s)) (v (x * b t)) t := by
    have h : HasDerivAt (fun s : ℝ ↦ w ((x * b t) * b s)) (v (x * b t)) (t - t) := sub_self t ▸ hd (x * b t)
    convert h.comp_sub_const t t using 1
    funext s
    have he : b t * b (s - t) = b s := by
      change a (Multiplicative.ofAdd t) * a (Multiplicative.ofAdd (s-t)) = _
      rw [← map_mul, ← ofAdd_add, add_sub_cancel]
    rw [mul_assoc,he]
  let k (t : ℝ) (x : G) := v (x * b t)
  have hFTC (x : G) : (∫ t in (0:ℝ)..1, k t x) = w (x * b 1) - w x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ htime x t)
      ((hc.comp (continuous_const.mul hb)).intervalIntegrable (μ := volume) 0 1)
    simpa only [k,b,ofAdd_zero,map_one,mul_one] using h
  let S : Set G := J
  let : SigmaFinite (μ.restrict S) := sigmaFinite_restrict_sigmaCompact μ hσ
  have hk0 (t : ℝ) (x : G) (hx : x ∉ S) : k t x = 0 :=
    h0 _ (fun hm ↦ hx ((J.mul_mem_cancel_right (hmem t)).mp hm))
  have hrow (t : ℝ) : (∫ x in S, k t x ∂μ) = ∫ x, v x ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hk0 t)).trans (integral_mul_right_eq_self v (b t))
  have hnorm (t : ℝ) : (∫ x in S, ‖k t x‖ ∂μ) = ∫ x, ‖v x‖ ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by rw [hk0 t x hx,norm_zero])).trans ?_
    exact integral_mul_right_eq_self (fun x ↦ ‖v x‖) (b t)
  have hkc : Continuous (Function.uncurry k) := hc.comp (continuous_snd.mul (hb.comp continuous_fst))
  let : IsFiniteMeasure (volume.restrict (uIoc (0:ℝ) 1)) := isFiniteMeasure_restrict.mpr (by simp)
  have hint : Integrable (Function.uncurry k) ((volume.restrict (uIoc (0:ℝ) 1)).prod (μ.restrict S)) := by
    refine (integrable_prod_iff hkc.aestronglyMeasurable).mpr ⟨.of_forall fun t ↦
      ((measurePreserving_mul_right μ (b t)).integrable_comp_of_integrable hv).restrict, ?_⟩
    simpa only [Function.uncurry_apply_pair,hnorm] using
      (integrable_const (μ := volume.restrict (uIoc (0:ℝ) 1)) (∫ x, ‖v x‖ ∂μ))
  have he := intervalIntegral_integral_swap hint
  simp_rw [hrow,hFTC] at he
  have hzero (x : G) (hx : x ∉ S) : w (x * b 1) - w x = 0 := by
    rw [← hFTC]
    simp only [fun t ↦ hk0 t x hx, intervalIntegral.integral_zero]
  have hw1 : Integrable (fun x ↦ w (x * b 1)) μ :=
    (measurePreserving_mul_right μ (b 1)).integrable_comp_of_integrable hw
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_sub hw1 hw,
    integral_mul_right_eq_self,sub_self] at he
  simpa using he

/-- The integrated orbit derivative of a function times a conjugate character vanishes. -/
private theorem lcaFourier_generator (a : LCATopologicalLie G) (f g : SchwartzBruhat G)
    (hg : ∀ x, g x = bruhatDirectionalDeriv a f x)
    (hf₁ : Integrable (f : G → ℂ) μ) (hg₁ : Integrable (g : G → ℂ) μ) (χ : PontryaginDual G) :
    lcaFourier μ g χ = bruhatDiffSymbol (bruhatDiffGenerator a) χ * lcaFourier μ f χ := by
  let c := bruhatDiffSymbol (bruhatDiffGenerator a) χ
  let u : SchwartzBruhat G := g - c • f
  let w (x : G) := f x * star (χ x : ℂ)
  let v (x : G) := u x * star (χ x : ℂ)
  have hμ : Integrable u.val μ := hg₁.sub (hf₁.const_mul c)
  obtain ⟨J,ho,hs,h0⟩ := schwartzBruhat_supported_open u
  obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous u
  have hc : Continuous v := (b.continuous.congr hb).mul (continuous_subtype_val.comp χ.continuous).star
  have hdχ := hasDerivAt_bruhatDirectionalDeriv a
    ((mem_bruhatSmoothSubmodule_iff _).mp (pontryaginDual_mem_bruhatSmooth χ) 1) (1 : G)
  have hchar : HasDerivAt (fun t : ℝ ↦ (χ (a (Multiplicative.ofAdd t)) : ℂ)) c 0 := by
    change HasDerivAt _ (bruhatDirectionalDeriv a (fun x : G ↦ (χ x : ℂ)) 1) 0
    simpa only [one_mul] using hdχ
  have hd (x : G) : HasDerivAt (fun t : ℝ ↦ w (x * a (Multiplicative.ofAdd t))) (v x) 0 := by
    have hχ : HasDerivAt (fun t : ℝ ↦ star (χ (a (Multiplicative.ofAdd t)) : ℂ)) (-c) 0 := by
      have h := HasDerivAt.comp_const_sub (0:ℝ) (0:ℝ) (f := fun t : ℝ ↦ (χ (a (Multiplicative.ofAdd t)) : ℂ))
        (show HasDerivAt _ c (0 - 0) by simpa only [sub_zero] using hchar)
      convert h using 1
      funext t
      simp only [zero_sub,ofAdd_neg,map_inv,Circle.coe_inv_eq_conj,Complex.star_def]
    have hf := hasDerivAt_bruhatDirectionalDeriv a (schwartzBruhat_isBruhatSmooth f 1) x
    have h := hf.fun_mul (hχ.const_mul (star (χ x : ℂ)))
    convert h using 1
    · funext t
      simp only [w,map_mul,Circle.coe_mul,star_mul]
      ring
    · change (g x - c * f x) * star (χ x : ℂ) = _
      simp only [hg,ofAdd_zero,map_one,mul_one,Circle.coe_one,star_one]
      ring
  have hz := integral_orbit_derivative_zero μ a (w := w) (v := v) (integrable_fourierIntegrand μ hf₁ χ)
    (integrable_fourierIntegrand μ hμ χ) hc J ho hs (fun x hx ↦ by simp [v,h0 x hx]) hd
  have hi (x : G) : v x = g x * star (χ x : ℂ) - c * (f x * star (χ x : ℂ)) := by
    change (g x - c * f x) * star (χ x : ℂ) = _
    ring
  simp_rw [hi] at hz
  rw [integral_sub (integrable_fourierIntegrand μ hg₁ χ) ((integrable_fourierIntegrand μ hf₁ χ).const_mul c),
    integral_const_mul] at hz
  exact sub_eq_zero.mp hz

/-- A Fourier multiplier identity on generators extends to the algebra they generate. -/
private theorem symbol_action_adjoin {V E ι : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup E] [Module ℂ E] (i : E →ₗ[ℂ] V) (A : E →ₗ[ℂ] (ι → ℂ)) (ch : ι → V)
    (s : Set (Module.End ℂ V))
    (hgen : ∀ L ∈ s, ∃ c : ι → ℂ, (∀ χ, L (ch χ) = c χ • ch χ) ∧
      ∀ z, ∃ y, i y = L (i z) ∧ ∀ χ, A y χ = c χ * A z χ)
    {L : Module.End ℂ V} (hL : L ∈ Algebra.adjoin ℂ s) :
    ∃ c : ι → ℂ, (∀ χ, L (ch χ) = c χ • ch χ) ∧
      ∀ z, ∃ y, i y = L (i z) ∧ ∀ χ, A y χ = c χ * A z χ := by
  apply Algebra.adjoin_induction (p := fun M _ ↦ ∃ c : ι → ℂ,
    (∀ χ, M (ch χ) = c χ • ch χ) ∧ ∀ z, ∃ y, i y = M (i z) ∧ ∀ χ, A y χ = c χ * A z χ)
    hgen _ _ _ hL
  · intro c
    refine ⟨fun _ ↦ c, fun χ ↦ rfl, fun z ↦ ⟨c • z,i.map_smul c z, fun χ ↦ ?_⟩⟩
    rw [A.map_smul]
    rfl
  · rintro L M _ _ ⟨c,hc,lc⟩ ⟨d,hd,ld⟩
    refine ⟨c+d,fun χ ↦ ?_, fun z ↦ ?_⟩
    · change L (ch χ) + M (ch χ) = (c χ + d χ) • ch χ
      rw [hc,hd,add_smul]
    · obtain ⟨u,hu,fu⟩ := lc z
      obtain ⟨v,hv,fv⟩ := ld z
      refine ⟨u+v, (i.map_add _ _).trans (congrArg₂ (·+·) hu hv), fun χ ↦ ?_⟩
      rw [A.map_add]
      change A u χ + A v χ = (c χ + d χ) * A z χ
      rw [fu,fv,add_mul]
  · rintro L M _ _ ⟨c,hc,lc⟩ ⟨d,hd,ld⟩
    refine ⟨c*d, fun χ ↦ ?_, fun z ↦ ?_⟩
    · change L (M (ch χ)) = (c χ * d χ) • ch χ
      rw [hd,map_smul,hc,smul_smul,mul_comm]
    · obtain ⟨u,hu,fu⟩ := ld z
      obtain ⟨v,hv,fv⟩ := lc u
      refine ⟨v,hv.trans (congrArg L hu), fun χ ↦ ?_⟩
      change A v χ = (c χ * d χ) * A z χ
      rw [fv,fu,mul_assoc]

private def smoothInclusion : SchwartzBruhat G →ₗ[ℂ] bruhatSmoothSubmodule (G := G) :=
    { toFun := fun z ↦ ⟨z.val,(mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth z)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

private def smoothCharacter (χ : PontryaginDual G) : bruhatSmoothSubmodule (G := G) := ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩

private theorem generator_character (a : LCATopologicalLie G) (χ : PontryaginDual G) :
    bruhatFirstOrder a (smoothCharacter χ) = bruhatDiffSymbol (bruhatDiffGenerator a) χ • smoothCharacter χ := by
  apply Subtype.ext
  funext x
  change bruhatDirectionalDeriv a (fun y : G ↦ (χ y : ℂ)) x =
    bruhatDirectionalDeriv a (fun y : G ↦ (χ y : ℂ)) 1 * (χ x : ℂ)
  simp only [bruhatDirectionalDeriv,one_mul,map_mul,Circle.coe_mul,deriv_const_mul_field]
  exact mul_comm _ _

private theorem generator_schwartz_lift (B : SchwartzBruhat G →ₗ[ℂ] (PontryaginDual G → ℂ))
    (hB : ∀ z : SchwartzBruhat G, Integrable z.val μ ∧ ∀ χ, B z χ = lcaFourier μ z χ)
    (a : LCATopologicalLie G) (z : SchwartzBruhat G) :
    ∃ y : SchwartzBruhat G, smoothInclusion (G := G) y = bruhatFirstOrder a (smoothInclusion (G := G) z) ∧
      ∀ χ, B y χ = bruhatDiffSymbol (bruhatDiffGenerator a) χ * B z χ := by
  let L := (bruhatFirstOrder_schwartz (G := G) a).choose
  have hL := (bruhatFirstOrder_schwartz (G := G) a).choose_spec
  refine ⟨L z, ?_, fun χ ↦ ?_⟩
  · apply Subtype.ext
    exact funext (hL z)
  exact ((hB (L z)).2 χ).trans ((lcaFourier_generator μ a z (L z) (hL z)
    (hB z).1 (hB (L z)).1 χ).trans (congrArg (_ * ·) ((hB z).2 χ).symm))

end FourierDifferentiation

section AveragingAndFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

variable (K : Subgroup G)

/-- Use the whole compactly generated group as the open subgroup of the structural pair. -/
private def fullBruhatStage {K : Subgroup G} (hG : IsCompactlyGeneratedGroup G) (hk : IsBruhatGoodSubgroup K) :
    BruhatStructuralPair G :=
  ⟨(⊤, OrderDual.toDual K), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv
      (show G ≃ₜ* (⊤ : Subgroup G) from
        ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩) hG, hk, le_top⟩

omit hTop hT2 hLC in
private theorem fullBruhatStage_quotientEquiv {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    {K : Subgroup G} (hG : IsCompactlyGeneratedGroup G) (hk : IsBruhatGoodSubgroup K)
    (p : G →* Q) (hp : IsOpenQuotientMap p) (hker : p.ker = K) :
    ∃ w : (fullBruhatStage hG hk).quotient ≃ₜ* Q,
      ∀ x : G, w (QuotientGroup.mk ⟨x, Subgroup.mem_top x⟩) = p x := by
  let i : (⊤ : Subgroup G) ≃ₜ* G := ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  let t := p.comp (⊤ : Subgroup G).subtype
  have ht : IsOpenQuotientMap t := hp.comp i.toHomeomorph.isOpenQuotientMap
  have hker' : K.comap (⊤ : Subgroup G).subtype = t.ker := by rw [← hker]; rfl
  let w := (QuotientGroup.quotientMulEquivOfEq hker').trans
    (QuotientGroup.quotientKerEquivOfSurjective t ht.surjective)
  let v := w.toContinuousMulEquiv fun s ↦ by
    rw [← (QuotientGroup.isQuotientMap_mk _).isOpen_preimage]
    exact ht.isQuotientMap.isOpen_preimage
  exact ⟨v, fun _ ↦ rfl⟩

private theorem schwartzBruhatStage_surjective_of_maximal (a : BruhatStructuralPair G) (d : ElementaryLCAPresentation a.quotient)
    (hmax : ∀ b, b ≤ a) : Function.Surjective (schwartzBruhatStageInclusion a d) := by
  intro f
  exact ((mem_schwartzBruhatSubmodule_iff f.val).mp f.property).elim fun b hb ↦ hb.elim fun e' he ↦
    he.elim fun s hs ↦ (schwartzBruhatStage_transition (hmax b) e' d).elim
      fun k hk ↦ ⟨k s, Subtype.ext ((hk.1 s).trans hs)⟩

omit hTop hT2 hLC in
private theorem continuousLinearEquiv_of_surjective_retraction {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (j : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hr : Function.LeftInverse R j) (hs : Function.Surjective j) :
    ∃ I : E ≃L[ℂ] F, ∀ x, I x = j x := by
  let l := LinearEquiv.ofBijective j.toLinearMap ⟨hr.injective,hs⟩
  refine ⟨{l with continuous_toFun := j.continuous, continuous_invFun := ?_}, fun _ ↦ rfl⟩
  exact R.continuous.congr fun f ↦ by
    obtain ⟨s,rfl⟩ := hs f
    exact (hr s).trans (l.symm_apply_apply s).symm

/-- On an elementary group the largest structural stage has zero kernel and realizes the whole space. -/
private theorem elementarySchwartz_equiv_schwartzBruhat (e : ElementaryLCAPresentation G) :
    ∃ I : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhat G,
      ∀ f (x : G), I f x = f (e.equiv x).toAdd := by
  classical
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  have hG := hE.1
  have hEu := hE.2
  let hk := (isBruhatGoodSubgroup_bot_iff (G := G)).mpr hEu
  let a := fullBruhatStage hG hk
  have hW := fullBruhatStage_quotientEquiv hG hk (MonoidHom.id G) IsOpenQuotientMap.id (by simp)
  let w := hW.choose
  have hw := hW.choose_spec
  let d : ElementaryLCAPresentation a.quotient := {e with equiv := w.trans e.equiv}
  let j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G :=
    ⟨schwartzBruhatStageInclusion a d, (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _
      fun q ↦ q.property a d⟩
  have hmax (b : BruhatStructuralPair G) : b ≤ a := ⟨le_top, (bot_le : (⊥ : Subgroup G) ≤ OrderDual.ofDual b.val.2)⟩
  have hret := schwartzBruhatStage_average_retraction a d
  have hI := continuousLinearEquiv_of_surjective_retraction j hret.choose hret.choose_spec.1 (schwartzBruhatStage_surjective_of_maximal a d hmax)
  refine ⟨hI.choose, fun f x ↦ ?_⟩
  rw [hI.choose_spec]
  change schwartzBruhatStageRealization a d f x = _
  have hx : x ∈ a.val.1 := Subgroup.mem_top x
  rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
  change f (e.equiv (w (QuotientGroup.mk _))).toAdd = _
  exact congrArg (fun y : G ↦ f (e.equiv y).toAdd) (hw x)

end AveragingAndFourier

section CoordinateCharacterization

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

omit hT2 in
private theorem exists_dual_weight_direction (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (hb : ∀ x χ, b x χ = χ x) (ρ : G →ₜ* Multiplicative ℝ) :
    ∃ a : LCATopologicalLie (PontryaginDual G), ∀ x,
      bruhatDiffSymbol (bruhatDiffGenerator a) (b x) = 2 * ↑Real.pi * Complex.I * ((ρ x).toAdd : ℂ) := by
  obtain ⟨d,hd⟩ := exists_realPontryaginDualEquiv
  let a := (PontryaginDual.map ρ).comp (d : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))
  refine ⟨a,fun x ↦ bruhatDiffSymbol_generator a (b x) _ fun t ↦ ?_⟩
  rw [hb]
  change Real.fourierChar ((ρ x).toAdd*t) = d (Multiplicative.ofAdd t) (ρ x)
  rw [mul_comm]
  exact (hd t (ρ x).toAdd).symm

/-- Products of real-valued homomorphisms are symbols of suitably normalized words on the dual. -/
private theorem bruhat_realHom_weights (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (hb : ∀ x χ, b x χ = χ x) (L : List (G →ₜ* Multiplicative ℝ)) :
    ∃ E : bruhatDiffAlgebra (PontryaginDual G), ∀ x,
      bruhatDiffSymbol E (b x) = (L.map (fun ρ ↦ ((ρ x).toAdd : ℂ))).prod := by
  choose a ha using exists_dual_weight_direction b hb
  let z : ℂ := 2 * ↑Real.pi * Complex.I
  have hz : z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨(z^L.length)⁻¹ • bruhatDiffWord (L.map a), fun x ↦ ?_⟩
  change (z^L.length)⁻¹ * bruhatDiffSymbol (bruhatDiffWord (L.map a)) (b x) = _
  rw [bruhatDiffSymbol_word]
  have hprod : ((L.map a).map (fun c ↦ bruhatDiffSymbol (bruhatDiffGenerator c) (b x))).prod =
      z^L.length * (L.map (fun ρ ↦ ((ρ x).toAdd : ℂ))).prod := by
    induction L with
    | nil => simp
    | cons ρ l ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ha,ih]
      change z * _ * _ = _
      ring
  rw [hprod,inv_mul_cancel_left₀ (pow_ne_zero _ hz)]

/-- Bruhat smoothness descends to ordinary smoothness on every fiber of the full elementary stage. -/
private theorem smooth_elementary_cover (e : ElementaryLCAPresentation G) (f : bruhatSmoothSubmodule (G := G))
    (z : Fin e.latticeRank → ℤ) (d : e.finiteFactor) :
    ContDiff ℝ ∞ (fun u ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d)))) := by
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  let hbot := (isBruhatGoodSubgroup_bot_iff (G := G)).mpr hE.2
  let a := fullBruhatStage hE.1 hbot
  have hW := fullBruhatStage_quotientEquiv hE.1 hbot (MonoidHom.id G) IsOpenQuotientMap.id (by simp)
  let w := hW.choose
  let e' : ElementaryLCAPresentation a.quotient := {e with equiv := w.trans e.equiv}
  apply contDiff_infty.mpr
  intro n
  obtain ⟨k,hk,_,hdesc⟩ := (mem_bruhatSmoothSubmodule_iff _).mp f.property n
  have H := bruhatContDiff_descend_of_le hk hdesc a (show OrderDual.ofDual a.val.2 ≤ k from bot_le)
  let f₀ := H.choose
  have h (x : G) : f₀ (w.symm x) = f.val x := by
    let t : a.val.1 := ⟨x,Subgroup.mem_top _⟩
    have hw : w (QuotientGroup.mk t) = x := hW.choose_spec x
    exact (congrArg f₀ (w.symm_apply_eq.mpr hw.symm)).trans (H.choose_spec.1 t)
  have hcd := H.choose_spec.2 e' z d
  have heq : (fun u ↦ f₀ (e'.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d)))) =
      fun u ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d))) := funext fun u ↦ h _
  exact heq ▸ hcd

private theorem elementaryCover_add {m n r : ℕ} {F : Type*} [AddCommGroup F]
    (u v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a a' : Fin r → ℤ) (b b' : F) :
    elementaryCover u a b + elementaryCover v a' b' = elementaryCover (u+v) (a+a') (b+b') := by
  exact Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_add _ _ _).symm) rfl)

/-- A vector of the real and torus cover defines a one-parameter subgroup realizing its directional derivative. -/
private theorem exists_direction_cover (e : ElementaryLCAPresentation G)
    (v : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
    ∃ a : LCATopologicalLie G, ∀ (f : bruhatSmoothSubmodule (G := G)) u z d,
      (bruhatFirstOrder a f).val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d))) =
        fderiv ℝ (fun w ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover w z d)))) u v := by
  let V := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let c := (elementaryCoverZeroHom (r := e.latticeRank) (F := e.finiteFactor)).comp L.toLinearMap.toAddMonoidHom
  let a : LCATopologicalLie G := (e.equiv.symm : _ →ₜ* _).comp ⟨AddMonoidHom.toMultiplicative c,
    elementaryCoverZeroHom_continuous_isOpenMap.1.comp L.continuous⟩
  refine ⟨a,fun f u z d ↦ ?_⟩
  let g (w : V) := f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover w z d)))
  have hLine : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have h := ((smooth_elementary_cover e f z d).differentiable (by simp) u).hasFDerivAt
  have horb (t : ℝ) : e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d)) * a (Multiplicative.ofAdd t) =
      e.equiv.symm (Multiplicative.ofAdd (elementaryCover (u+t • v) z d)) := by
    change e.equiv.symm _ * e.equiv.symm (Multiplicative.ofAdd (elementaryCover (t • v) 0 0)) = _
    rw [← map_mul,← ofAdd_add,elementaryCover_add,add_zero,add_zero]
  change deriv (fun t : ℝ ↦ f.val (_ * a (Multiplicative.ofAdd t))) 0 = _
  simp only [horb]
  exact (h.comp_hasDerivAt_of_eq 0 hLine (by simp)).deriv

/-- Appending a direction differentiates the original function before evaluating the preceding mixed partial. -/
private theorem iteratedFDeriv_append_singleton {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (u v : V) (D : List V) :
    iteratedFDeriv ℝ (D ++ [v]).length f u (D ++ [v]).get =
      iteratedFDeriv ℝ D.length (fun y ↦ fderiv ℝ f y v) u D.get := by
  let eval (s : Σ k, Fin k → V) := iteratedFDeriv ℝ s.1 f u s.2
  have hEval := congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨D.length + 1, Fin.snoc D.get v⟩)
  change iteratedFDeriv ℝ (List.ofFn (Fin.snoc D.get v)).length f u (List.ofFn (Fin.snoc D.get v)).get =
    iteratedFDeriv ℝ (D.length + 1) f u (Fin.snoc D.get v) at hEval
  have hList : List.ofFn (Fin.snoc D.get v) = D ++ [v] := by
    rw [List.ofFn_succ',Fin.snoc_last,List.concat_eq_append]
    simp only [Fin.snoc_castSucc,List.ofFn_get]
  rw [hList] at hEval
  rw [hEval,iteratedFDeriv_succ_apply_right,Fin.init_snoc,Fin.snoc_last]
  change _ = iteratedFDeriv ℝ D.length ((ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ f) u D.get
  rw [(ContinuousLinearMap.apply ℝ ℂ v).iteratedFDeriv_comp_left
    (hf.fderiv_right (m := ∞) (by simp)).contDiffAt (by simp)]
  rfl

/-- Products of the directional generators realize all ordered iterated derivatives on the cover. -/
private theorem exists_diff_cover_word (e : ElementaryLCAPresentation G)
    (L : List (EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim))) :
    ∃ D : bruhatDiffAlgebra G, ∀ (f : bruhatSmoothSubmodule (G := G)) u z d,
      (D.val f).val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover u z d))) =
        iteratedFDeriv ℝ L.length (fun v ↦ f.val (e.equiv.symm (Multiplicative.ofAdd (elementaryCover v z d)))) u L.get := by
  induction L using List.reverseRecOn with
  | nil =>
    exact ⟨1,fun _ _ _ _ ↦ rfl⟩
  | append_singleton l v ih =>
    obtain ⟨D,hD⟩ := ih
    obtain ⟨a,ha⟩ := exists_direction_cover e v
    refine ⟨D * bruhatDiffGenerator a,fun f u z d ↦ ?_⟩
    change (D.val (bruhatFirstOrder a f)).val _ = _
    rw [hD,iteratedFDeriv_append_singleton (smooth_elementary_cover e f z d)]
    exact congrArg (fun w ↦ iteratedFDeriv ℝ l.length w u l.get) (funext fun x ↦ ha f x z d)

private def coordinateRealHom (e : ElementaryLCAPresentation G) (i : Fin e.realDim) : G →ₜ* Multiplicative ℝ :=
  let l := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin e.realDim ↦ ℝ) i).toLinearMap.toAddMonoidHom
  let a := l.comp (AddMonoidHom.fst _ _)
  (show Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) →ₜ* Multiplicative ℝ from
    ⟨AddMonoidHom.toMultiplicative a, (PiLp.continuous_apply 2 _ i).comp continuous_fst⟩).comp e.equiv

private def coordinateLatticeHom (e : ElementaryLCAPresentation G) (i : Fin e.latticeRank) : G →ₜ* Multiplicative ℝ :=
  let a := (Int.castAddHom ℝ).comp ((Pi.evalAddMonoidHom _ i).comp ((AddMonoidHom.fst _ _).comp
    ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))))
  (show Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) →ₜ* Multiplicative ℝ from
    ⟨AddMonoidHom.toMultiplicative a, by
      change Continuous (fun y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor ↦ (y.2.2.1 i : ℝ))
      exact (continuous_of_discreteTopology (f := fun z : Fin e.latticeRank → ℤ ↦ (z i : ℝ))).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))⟩).comp e.equiv

/-- Every real and lattice coordinate monomial is the pullback of a symbol along the given biduality map. -/
private theorem exists_elementary_weight (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (α : Fin e.realDim → ℕ) (δ : Fin e.latticeRank → ℕ) :
    ∃ E : bruhatDiffAlgebra (PontryaginDual G), ∀ y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor,
      bruhatDiffSymbol E (b (e.equiv.symm (Multiplicative.ofAdd y))) =
        (∏ i, (y.1 i : ℂ)^α i) * (∏ j, (y.2.2.1 j : ℂ)^δ j) := by
  let powers {n : ℕ} (β : Fin n → ℕ) (ρ : Fin n → G →ₜ* Multiplicative ℝ) :=
    (List.ofFn fun i ↦ List.replicate (β i) (ρ i)).flatten
  have hp {n : ℕ} (β : Fin n → ℕ) (ρ : Fin n → G →ₜ* Multiplicative ℝ) (x : G) :
      ((powers β ρ).map (fun c ↦ ((c x).toAdd : ℂ))).prod = ∏ i, ((ρ i x).toAdd : ℂ)^β i := by
    simp [powers,List.map_flatten,List.prod_flatten,List.map_ofFn,Function.comp_def,List.prod_replicate,List.prod_ofFn]
  obtain ⟨E,hE⟩ := bruhat_realHom_weights b hb (powers α (coordinateRealHom e) ++ powers δ (coordinateLatticeHom e))
  refine ⟨E,fun y ↦ ?_⟩
  rw [hE,List.map_append,List.prod_append,hp,hp]
  have hr (i : Fin e.realDim) : (coordinateRealHom e i (e.equiv.symm (.ofAdd y))).toAdd = y.1 i := by
    change (e.equiv (e.equiv.symm (.ofAdd y))).toAdd.1 i = _
    rw [e.equiv.apply_symm_apply]
    rfl
  have hz (i : Fin e.latticeRank) : (coordinateLatticeHom e i (e.equiv.symm (.ofAdd y))).toAdd = (y.2.2.1 i : ℝ) := by
    change ((e.equiv (e.equiv.symm (.ofAdd y))).toAdd.2.2.1 i : ℝ) = _
    rw [e.equiv.apply_symm_apply]
    rfl
  simp only [hr,hz,Complex.ofReal_intCast]

/-- Bounded symbol-weighted derivatives bound each defining seminorm on the full elementary stage. -/
private theorem elementarySchwartz_of_symbols (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (f : bruhatSmoothSubmodule (G := G))
    (hf : ∀ (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)),
      ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * (D.val f).val x‖ ≤ C) :
    f.val ∈ schwartzBruhatSubmodule G := by
  let g (y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) := f.val (e.equiv.symm (.ofAdd y))
  have hm : g ∈ elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor := by
    refine ⟨smooth_elementary_cover e f,fun i ↦ ?_⟩
    let dirs := (List.ofFn fun j ↦ List.replicate (i.2.1 j)
      ((EuclideanSpace.single j (1:ℝ), 0) : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim))).flatten ++
      (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
    obtain ⟨D,hD⟩ := exists_diff_cover_word e dirs
    obtain ⟨E,hE⟩ := exists_elementary_weight e b hb i.1 i.2.2.2
    obtain ⟨C,hC⟩ := hf D E
    refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup_le fun u ↦ iSup_le fun z ↦ iSup_le fun d ↦ ?_) ENNReal.ofReal_lt_top
    let y := elementaryCover u z d
    have hd : (D.val f).val (e.equiv.symm (.ofAdd y)) = elementaryPartial g i.2.1 i.2.2.1 u z d := hD f u z d
    have h := hC (e.equiv.symm (.ofAdd y))
    rw [hE,hd] at h
    rw [ENNReal.coe_nnreal_eq]
    exact ENNReal.ofReal_le_ofReal h
  obtain ⟨I,hI⟩ := elementarySchwartz_equiv_schwartzBruhat e
  let s : SchwartzBruhatStage e := ⟨g,hm⟩
  have he : (I s).val = f.val := funext fun x ↦ (hI s x).trans (congrArg f.val (e.equiv.symm_apply_apply x))
  exact he ▸ (I s).property

/-- A continuous real-valued homomorphism kills the compact factors and is linear in the real and lattice coordinates. -/
private theorem elementaryRealHom_polynomial {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (h : ElementaryLieGroup m n r F →+ ℝ) (hh : Continuous h) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ, ∀ y : ElementaryLieGroup m n r F,
      MvPolynomial.eval (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p = (h y : ℂ) := by
  classical
  let V := EuclideanSpace ℝ (Fin m)
  let Z := Fin r → ℤ
  let K := (Fin n → AddCircle (1 : ℝ)) × F
  let G := ElementaryLieGroup m n r F
  let J := Fin m ⊕ Fin r
  let eR : V →+ G :=
    ⟨⟨fun x ↦ (x, 0, 0, 0), rfl⟩, fun _ _ ↦
      Prod.ext rfl (Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (zero_add _).symm))⟩
  let eZ : Z →+ G :=
    ⟨⟨fun a ↦ (0, 0, a, 0), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext (zero_add _).symm (Prod.ext rfl (zero_add _).symm))⟩
  let eK : K →+ G :=
    ⟨⟨fun z ↦ (0, z.1, 0, z.2), rfl⟩, fun _ _ ↦
      Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl))⟩
  let e (j : J) : G := Sum.elim
    (fun i ↦ eR (EuclideanSpace.single i 1)) (fun i ↦ eZ (Pi.single i 1)) j
  let coord (j : J) : G →+ ℝ := Sum.elim
    (fun i : Fin m ↦
      ⟨⟨fun g : G ↦ g.1 i, rfl⟩, fun _ _ ↦ rfl⟩)
    (fun i : Fin r ↦
      (Int.castAddHom ℝ).comp ⟨⟨fun g : G ↦ g.2.2.1 i, rfl⟩, fun _ _ ↦ rfl⟩) j
  have hlinear (h : G →+ ℝ) (hh : Continuous h) (g : G) :
      h g = ∑ j, coord j g * h (e j) := by
    let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
    let hK := h.comp eK
    have hKcont : Continuous hK :=
      hh.comp (continuous_const.prodMk (continuous_fst.prodMk
        (continuous_const.prodMk continuous_snd)))
    have hvanish (z : K) : hK z = 0 := by
      obtain ⟨M, hM⟩ := (isCompact_range hKcont.norm).bddAbove
      by_contra hz
      obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖hK z‖)
      have hle := hM (Set.mem_range_self (N • z))
      change ‖hK (N • z)‖ ≤ M at hle
      rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_natCast] at hle
      exact (not_lt_of_ge hle) ((div_lt_iff₀ (norm_pos_iff.mpr hz)).mp hN)
    let hR := (h.comp eR).toRealLinearMap (hh.comp (continuous_id.prodMk continuous_const))
    let basisR := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    let basisZ := Pi.basisFun ℤ (Fin r)
    have hr (x : V) : h (eR x) = ∑ i, x i * h (eR (EuclideanSpace.single i 1)) := by
      have he := congrArg hR (basisR.sum_repr x)
      simpa [hR, basisR, smul_eq_mul] using he.symm
    have hz (a : Z) : h (eZ a) = ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1)) := by
      have he := congrArg (h.comp eZ) (basisZ.sum_repr a)
      rw [map_sum] at he
      simp_rw [map_zsmul, zsmul_eq_mul] at he
      simpa [basisZ] using he.symm
    rcases g with ⟨x, z, a, b⟩
    have hdecomp : (x, z, a, b) = eR x + eZ a + eK (z, b) := by
      change (x, z, a, b) = ((x + 0) + 0, (0 + 0) + z, (0 + a) + 0, (0 + 0) + b)
      simp
    have hKzero : h (eK (z, b)) = 0 := hvanish (z, b)
    rw [Fintype.sum_sum_type]
    change h (x, z, a, b) =
      (∑ i, x i * h (eR (EuclideanSpace.single i 1))) +
        ∑ i, (a i : ℝ) * h (eZ (Pi.single i 1))
    rw [hdecomp, map_add, map_add, hKzero, add_zero, hr, hz]
  refine ⟨∑ j, MvPolynomial.X j * MvPolynomial.C (h (e j) : ℂ),fun y ↦ ?_⟩
  rw [hlinear h hh y]
  simp only [map_sum,map_mul,MvPolynomial.eval_X,MvPolynomial.eval_C,Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun j _ ↦ by
    cases j with
    | inl i => rfl
    | inr i => simp [coord]

omit hT2 in
private theorem bruhatSymbol_generator_polynomial (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (a : LCATopologicalLie (PontryaginDual G)) :
    ∃ p : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ, ∀ x,
      let y := (e.equiv x).toAdd
      bruhatDiffSymbol (bruhatDiffGenerator a) (b x) =
        MvPolynomial.eval (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p := by
  obtain ⟨σ,_,_,hσ⟩ := bruhatDiffDegreeOne_frequency (G := PontryaginDual G)
  let D : bruhatDiffDegreeOneReal (G := PontryaginDual G) :=
    ⟨bruhatFirstOrder a,Submodule.subset_span ⟨a,rfl⟩⟩
  let L := (σ D).comp ((b : G →ₜ* PontryaginDual (PontryaginDual G)).comp (e.equiv.symm : Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) →ₜ* G))
  let h := AddMonoidHom.toMultiplicative.symm L.toMonoidHom
  obtain ⟨p,hp⟩ := elementaryRealHom_polynomial (F := e.finiteFactor) h L.continuous
  let z : ℂ := 2 * ↑Real.pi * Complex.I
  refine ⟨MvPolynomial.C z * p,fun x ↦ ?_⟩
  dsimp only
  rw [map_mul (MvPolynomial.eval _),MvPolynomial.eval_C,hp]
  have he : h (e.equiv x).toAdd = (σ D (b x)).toAdd := by
    change (σ D (b (e.equiv.symm (e.equiv x)))).toAdd = _
    rw [e.equiv.symm_apply_apply]
  rw [he]
  exact bruhatDiffSymbol_generator a (b x) _ (hσ a D rfl (b x))

/-- The finite word presentation identifies a symbol with a polynomial in the noncompact coordinates. -/
private theorem bruhatSymbol_polynomial (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (E : bruhatDiffAlgebra (PontryaginDual G)) :
    ∃ p : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ, ∀ x,
      let y := (e.equiv x).toAdd
      bruhatDiffSymbol E (b x) = MvPolynomial.eval
        (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p := by
  classical
  choose p hp using bruhatSymbol_generator_polynomial e b
  obtain ⟨c,hc⟩ := bruhatDiff_exists_presentation E
  let word (w : List (LCATopologicalLie (PontryaginDual G))) := (w.map p).prod
  refine ⟨c.sum (fun w z ↦ MvPolynomial.C z * word w),fun x ↦ ?_⟩
  let ev : bruhatDiffAlgebra (PontryaginDual G) →ₗ[ℂ] ℂ :=
    (LinearMap.proj 1).comp ((bruhatSmoothSubmodule (G := PontryaginDual G)).subtype.comp
      ((LinearMap.applyₗ (smoothCharacter (b x))).comp (bruhatDiffAlgebra (PontryaginDual G)).val.toLinearMap))
  change ev E = _
  rw [← hc]
  simp only [Finsupp.sum,map_sum,map_mul,map_smul,MvPolynomial.eval_C,smul_eq_mul]
  refine Finset.sum_congr rfl fun w _ ↦ congrArg (c w * ·) ?_
  change bruhatDiffSymbol (bruhatDiffWord w) (b x) = _
  rw [bruhatDiffSymbol_word]
  simp only [word,map_list_prod,List.map_map,Function.comp_def,hp]

/-- The algebra generated by the one-parameter derivatives preserves the Schwartz submodule. -/
private theorem bruhatDiff_preserves_schwartz (D : bruhatDiffAlgebra G) :
    ∀ f : bruhatSmoothSubmodule (G := G), f.val ∈ schwartzBruhatSubmodule G →
      (D.val f).val ∈ schwartzBruhatSubmodule G := by
  refine Algebra.adjoin_induction (s := range (bruhatFirstOrder (G := G)))
    (p := fun A _ ↦ ∀ f : bruhatSmoothSubmodule (G := G), f.val ∈ schwartzBruhatSubmodule G →
      (A f).val ∈ schwartzBruhatSubmodule G) ?_ ?_ ?_ ?_ D.property
  · rintro _ ⟨a,rfl⟩ f hf
    let s : SchwartzBruhat G := ⟨f.val,hf⟩
    obtain ⟨A,hA⟩ := bruhatFirstOrder_schwartz (G := G) a
    have he : (A s).val = (bruhatFirstOrder a f).val := funext (hA s)
    exact he ▸ (A s).property
  · intro c f hf
    exact (schwartzBruhatSubmodule G).smul_mem c hf
  · intro A B _ _ hA hB f hf
    exact (schwartzBruhatSubmodule G).add_mem (hA f hf) (hB f hf)
  · intro A B _ _ hA hB f hf
    exact hA (B f) (hB f hf)

private theorem polynomial_weight_bounded {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (f : ElementarySchwartz m n r F) :
    ∃ C : ℝ, ∀ y : ElementaryLieGroup m n r F, ‖MvPolynomial.eval
      (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) p * f y‖ ≤ C := by
  obtain ⟨q,_,hq⟩ := elementarySchwartz_polynomial_weight_continuous_seminorm (F := F) p 0 0
  refine ⟨q f,fun y ↦ ?_⟩
  obtain ⟨w,hw⟩ := elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1
  rw [norm_mul]
  apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg q f)).mp
  rw [hq]
  refine le_iSup_of_le (y.1,w) (le_iSup_of_le y.2.2.1 (le_iSup_of_le y.2.2.2 ?_))
  rw [elementaryPartial_zero, hw]

/-- The polynomial seminorms bound the symbol times a Schwartz function on an elementary group. -/
private theorem bruhatSymbol_weight_bounded (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (E : bruhatDiffAlgebra (PontryaginDual G))
    (g : SchwartzBruhat G) :
    Continuous (fun x ↦ bruhatDiffSymbol E (b x) * g x) ∧
      ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * g x‖ ≤ C := by
  obtain ⟨p,hp⟩ := bruhatSymbol_polynomial e b E
  let ψ (x : G) := (e.equiv x).toAdd
  let coord (y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))
  have hc : Continuous coord := by
    apply continuous_pi
    intro j
    cases j with
    | inl i => exact Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ i).comp continuous_fst)
    | inr i =>
      exact (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ℂ))).comp
        ((continuous_apply i).comp continuous_snd.snd.fst)
  have hψ : Continuous ψ := continuous_toAdd.comp e.equiv.continuous
  obtain ⟨u,hu⟩ := schwartzBruhat_boundedContinuous (G := G) g
  refine ⟨(((MvPolynomial.continuous_eval p).comp (hc.comp hψ)).mul u.continuous).congr
    (fun x ↦ congrArg₂ (· * ·) (hp x).symm (hu x)),?_⟩
  obtain ⟨I,hI⟩ := elementarySchwartz_equiv_schwartzBruhat e
  let s := I.symm g
  obtain ⟨C,hC⟩ := polynomial_weight_bounded p s
  refine ⟨C,fun x ↦ ?_⟩
  have hs : s (ψ x) = g x := (hI s x).symm.trans (congrArg (fun w : SchwartzBruhat G ↦ w x) (I.apply_symm_apply g))
  exact (congrArg norm (congrArg₂ (· * ·) (hp x) hs.symm)).le.trans (hC (ψ x))

include hTop hT2 hLC in
/-- Paper: Lemma D.1.6.16, p. 770. On an elementary group a smooth function
is Schwartz exactly when each symbol times each differentiated function is
continuous and globally bounded. The dual symbols are evaluated through biduality. -/
theorem mem_schwartzBruhat_iff_bruhatDiff_bounded (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (f : bruhatSmoothSubmodule (G := G)) :
    (f : G → ℂ) ∈ schwartzBruhatSubmodule G ↔
      ∀ (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)),
        Continuous (fun x ↦ bruhatDiffSymbol E (b x) * (D.val f).val x) ∧
        ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * (D.val f).val x‖ ≤ C := by
  constructor
  · intro hf D E
    exact bruhatSymbol_weight_bounded e b E ⟨(D.val f).val, bruhatDiff_preserves_schwartz D f hf⟩
  · intro h
    exact elementarySchwartz_of_symbols e b hb f (fun D E ↦ (h D E).2)

end CoordinateCharacterization

section SchwartzIntegrability

/-- The product measurable structure on an elementary group agrees with its Borel
structure. -/
private theorem elementaryLieGroup_borelSpace {m n r : ℕ} {Fk : Type*}
    [TopologicalSpace Fk] [MeasurableSpace Fk] [BorelSpace Fk] :
    BorelSpace (ElementaryLieGroup m n r Fk) := by
  let : BorelSpace ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := inferInstance
  exact inferInstanceAs (BorelSpace (EuclideanSpace ℝ (Fin m) ×
    (Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk))

/-- Rapid decay in the real and lattice directions makes an elementary Schwartz function
integrable for any Haar measure on its elementary group. -/
private theorem elementarySchwartz_integrable {m n r : ℕ} {Fk : Type*} [AddCommGroup Fk]
    [TopologicalSpace Fk] [DiscreteTopology Fk] [Finite Fk] [MeasurableSpace Fk] [BorelSpace Fk]
    (f : ElementarySchwartz m n r Fk) (μ : Measure (ElementaryLieGroup m n r Fk))
    [μ.IsAddHaarMeasure] : Integrable f μ := by
  let : (Measure.count : Measure ℤ).IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : (Measure.count : Measure Fk).IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let : MeasurableAdd ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin r → ℤ) × Fk) := inferInstance
  let : BorelSpace ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := inferInstance
  let : MeasurableAdd ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) :=
    ContinuousAdd.measurableAdd
  let νL : Measure ((Fin r → ℤ) × Fk) :=
    (Measure.pi fun _ : Fin r ↦ (Measure.count : Measure ℤ)).prod Measure.count
  let : νL.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SFinite νL := by dsimp [νL]; infer_instance
  let νT : Measure ((Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × Fk) := volume.prod νL
  let : νT.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SFinite νT := by dsimp [νT, νL]; infer_instance
  let ν : Measure (ElementaryLieGroup m n r Fk) := volume.prod νT
  let : BorelSpace (ElementaryLieGroup m n r Fk) := elementaryLieGroup_borelSpace
  let : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  apply Integrable.smul_measure_nnreal
  let A (x : EuclideanSpace ℝ (Fin m)) := (1 + ‖x‖ ^ 2) ^ (m + 1)
  let B (k : ℤ) := 1 + (k : ℝ) ^ 2
  have hA : Integrable (fun x ↦ (A x)⁻¹) volume := by
    have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℝ) < 2 * (m + 1 : ℕ) := by
      simp
      linarith [Nat.cast_nonneg (α := ℝ) m]
    convert integrable_rpow_neg_one_add_norm_sq (μ := volume) hdim using 1
    funext x
    rw [show -(2 * ((m + 1 : ℕ) : ℝ)) / 2 = -((m + 1 : ℕ) : ℝ) by ring,
      Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hB : Integrable (fun k ↦ (B k)⁻¹) Measure.count := by
    rw [integrable_count_iff]
    have hs := Real.summable_one_div_int_pow.mpr (show 1 < 2 by decide)
    apply hs.of_norm_bounded_eventually
    filter_upwards [show ∀ᶠ k : ℤ in cofinite, k ≠ 0 from (finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
    have hpos : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)
    simp only [B, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : 0 < 1 + (k : ℝ) ^ 2), one_div]
    exact inv_anti₀ hpos (by linarith)
  let D (w : ElementaryLieGroup m n r Fk) := A w.1 * ∏ k, B (w.2.2.1 k)
  let P : MvPolynomial (Fin m ⊕ Fin r) ℂ :=
    (1 + ∑ i : Fin m, MvPolynomial.X (Sum.inl i) ^ 2) ^ (m + 1) *
      ∏ j : Fin r, (1 + MvPolynomial.X (Sum.inr j) ^ 2)
  obtain ⟨C,hC⟩ := polynomial_weight_bounded P f
  have hP (y : ElementaryLieGroup m n r Fk) : MvPolynomial.eval
      (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) P = (D y : ℂ) := by
    simp [P,D,A,B,EuclideanSpace.real_norm_sq_eq]
  have hdom : Integrable (fun w ↦ C * (D w)⁻¹) ν := by
    have hπ := Integrable.fintype_prod (ι := Fin r) (fun _ ↦ hB)
    have hf : Integrable (fun _ : Fk ↦ (1 : ℝ)) (Measure.count : Measure Fk) := integrable_const _
    have ht : Integrable (fun _ : Fin n → AddCircle (1 : ℝ) ↦ (1 : ℝ)) volume :=
      integrable_const _
    convert (hA.mul_prod (ht.mul_prod (hπ.mul_prod hf))).const_mul C using 1
    funext w
    simp only [D, mul_inv_rev, one_mul, mul_one, Finset.prod_inv_distrib]
    ring
  refine hdom.mono' (elementarySchwartz_continuousFunction f).aestronglyMeasurable
    (Eventually.of_forall fun w ↦ ?_)
  have hD : 0 < D w := by dsimp [D, A, B]; positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hD, mul_comm]
  have h := hC w
  rwa [hP,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD] at h

/-- The compact annihilator of the open dual subgroup recovers the original good subgroup. -/
private theorem isCompact_of_bruhatGoodSubgroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) : IsCompact (k : Set G) := by
  have h := isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  rwa [lcaDualAnnihilator_annihilator k hk.1] at h

open scoped Pointwise in
/-- A Schwartz–Bruhat stage is integrable after pullback along the quotient by its compact
kernel and extension by zero from its open subgroup. -/
private theorem schwartzBruhatStage_integrable {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) :
    Integrable (schwartzBruhatStageRealization a e f) μ := by
  let H := a.val.1
  let K := OrderDual.ofDual a.val.2
  let L := K.comap H.subtype
  have hH : IsOpen (H : Set G) := a.property.1
  have hK : IsCompact (L : Set H) :=
    (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_of_bruhatGoodSubgroup K a.property.2.2.1)
  let q := QuotientGroup.mk' L
  have hq : IsProperMap q := by
    refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe hK, ?_⟩
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L y
    change IsCompact (QuotientGroup.mk ⁻¹' {QuotientGroup.mk x})
    rw [← image_singleton, QuotientGroup.preimage_image_mk_eq_mul]
    exact isCompact_singleton.mul hK
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let : MeasurableSpace e.finiteFactor := borel _
  let : BorelSpace e.finiteFactor := ⟨rfl⟩
  let : BorelSpace E := elementaryLieGroup_borelSpace
  let : T2Space (Multiplicative E) := inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin e.realDim) ×
    (Fin e.torusDim → AddCircle (1 : ℝ)) × (Fin e.latticeRank → ℤ) × e.finiteFactor))
  let p : H →* Multiplicative E := e.equiv.toMonoidHom.comp q
  have hp : IsProperMap p := e.equiv.toHomeomorph.isProperMap.comp hq
  let ν := μ.comap H.subtype
  let : ν.IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := ContinuousMul.measurableMul) μ (f := H.subtype)
      hH.isOpenEmbedding_subtypeVal
  let ρ := ν.map p
  have hρ : ρ.IsHaarMeasure := Measure.isHaarMeasure_map ν p hp.continuous
    (e.equiv.surjective.comp (QuotientGroup.mk'_surjective L))
    (isProperMap_iff_tendsto_cocompact.mp hp).2
  let ρ' : Measure E := ρ
  let : ρ'.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hρ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hρ.toIsOpenPosMeasure
      map_add_left_eq_self := fun x ↦ hρ.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  have hf : Integrable f ρ' := elementarySchwartz_integrable f ρ'
  have hcomp : Integrable (fun x : H ↦ f (Multiplicative.toAdd (p x))) ν :=
    hf.comp_measurable hp.continuous.measurable
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := (H : Set G))
  · rw [integrableOn_iff_comap_subtypeVal hH.measurableSet]
    refine hcomp.congr (Eventually.of_forall fun x ↦ ?_)
    exact ((schwartzBruhatStageRealization_apply a e f x.val).trans
      (dite_eq_left x.property)).symm
  · intro x hx
    exact (schwartzBruhatStageRealization_apply a e f x).trans (dite_eq_right hx)

/-- Rapid decay on the elementary stages gives Haar integrability on the full group. -/
theorem SchwartzBruhat.integrable {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : SchwartzBruhat G) : Integrable f.val μ := by
  obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  exact hs ▸ schwartzBruhatStage_integrable μ a e s

/-- The Fourier integral is linear on the space of Schwartz tests. -/
private theorem schwartzBruhat_fourier_linear {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    ∃ B : SchwartzBruhat G →ₗ[ℂ] (PontryaginDual G → ℂ), ∀ f χ, B f χ = lcaFourier μ f χ := by
  refine ⟨{ toFun := fun f ↦ lcaFourier μ f
            map_add' := ?_
            map_smul' := ?_ },fun _ _ ↦ rfl⟩
  · intro f g
    funext χ
    change (∫ x, (f x + g x) * star (χ x : ℂ) ∂μ) = _ + _
    simp_rw [add_mul]
    exact integral_add (integrable_fourierIntegrand μ (SchwartzBruhat.integrable μ f) χ)
      (integrable_fourierIntegrand μ (SchwartzBruhat.integrable μ g) χ)
  · intro c f
    funext χ
    change (∫ x, (c * f x) * star (χ x : ℂ) ∂μ) = c * _
    simp_rw [mul_assoc,integral_const_mul]
    rfl

end SchwartzIntegrability

section FourierTransport

variable {A B : Type*} [CommGroup A] [TopologicalSpace A]
    [CommGroup B] [TopologicalSpace B]

/-- A topological group isomorphism restricts to a subgroup and its image. -/
private def fourierSubgroupMap (d : A ≃ₜ* B) (U : Subgroup A) :
    U ≃ₜ* U.map d.toMulEquiv.toMonoidHom where
  toMulEquiv := d.toMulEquiv.subgroupMap U
  continuous_toFun := (d.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (d.symm.continuous.comp continuous_subtype_val).subtype_mk _

variable [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A]
    [IsTopologicalGroup B] [T2Space B] [LocallyCompactSpace B]

/-- Transport of structural pairs preserves their open subgroups and good kernels. -/
private def fourierTransportPair (d : A ≃ₜ* B) (a : BruhatStructuralPair A) :
    BruhatStructuralPair B := by
  let U := a.val.1
  let N := OrderDual.ofDual a.val.2
  let D := d.toMulEquiv.toMonoidHom
  let φ := PontryaginDual.map (d.symm : B →ₜ* A)
  let ψ := PontryaginDual.map (d : A →ₜ* B)
  let δ : PontryaginDual A ≃ₜ* PontryaginDual B :=
    { φ with
      toFun := φ
      invFun := ψ
      left_inv := fun χ ↦ PontryaginDual.ext fun x ↦ by
        change χ (d.symm (d x)) = χ x
        rw [d.symm_apply_apply]
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ by
        change χ (d (d.symm x)) = χ x
        rw [d.apply_symm_apply]
      continuous_invFun := ψ.continuous }
  have hann : (lcaAnnihilator N).map δ.toMulEquiv.toMonoidHom = lcaAnnihilator (N.map D) := by
    ext χ
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, mem_lcaAnnihilator_iff,
      mem_lcaAnnihilator_iff]
    constructor
    · intro h x
      obtain ⟨y, hy, hxy⟩ := x.property
      calc
        χ (x : B) = χ (D y) := (congrArg χ hxy).symm
        _ = 1 := h ⟨y, hy⟩
    · intro h x
      exact h ⟨D x, Subgroup.mem_map_of_mem D x.property⟩
  refine ⟨(U.map D, OrderDual.toDual (N.map D)), ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact d.toHomeomorph.isOpenMap _ a.property.1
  · exact isCompactlyGeneratedGroup_of_continuousMulEquiv (fourierSubgroupMap d U)
      a.property.2.1
  · exact d.toHomeomorph.isClosedMap _ a.property.2.2.1.1
  · change IsOpen (lcaAnnihilator (N.map D) : Set (PontryaginDual B))
    rw [← hann]
    exact δ.toHomeomorph.isOpenMap _ a.property.2.2.1.2.1
  · change IsCompactlyGeneratedGroup (lcaAnnihilator (N.map D))
    rw [← hann]
    exact isCompactlyGeneratedGroup_of_continuousMulEquiv
      (fourierSubgroupMap δ (lcaAnnihilator N)) a.property.2.2.1.2.2
  · exact Subgroup.map_mono a.property.2.2.2

/-- Transport of pairs induces the corresponding isomorphism on their quotients. -/
private def fourierTransportQuotient (d : A ≃ₜ* B) (a : BruhatStructuralPair A) :
    a.quotient ≃ₜ* (fourierTransportPair d a).quotient := by
  let b := fourierTransportPair d a
  let dU : a.val.1 ≃ₜ* b.val.1 := fourierSubgroupMap d a.val.1
  let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
  let M := (OrderDual.ofDual b.val.2).comap b.val.1.subtype
  have hNM : N.map dU.toMulEquiv.toMonoidHom = M := by
    ext y
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap]
    change d.symm (y : B) ∈ OrderDual.ofDual a.val.2 ↔
      (y : B) ∈ (OrderDual.ofDual a.val.2).map d.toMulEquiv.toMonoidHom
    exact Subgroup.mem_map_equiv.symm
  let q := QuotientGroup.congr N M dU.toMulEquiv hNM
  exact
    { toMulEquiv := q
      continuous_toFun := isQuotientMap_quotient_mk'.continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp dU.continuous)
      continuous_invFun := isQuotientMap_quotient_mk'.continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp dU.symm.continuous) }

/-- The transported presentation uses the same elementary coordinates. -/
private abbrev fourierTransportPresentation (d : A ≃ₜ* B) (a : BruhatStructuralPair A)
    (e : ElementaryLCAPresentation a.quotient) :
    ElementaryLCAPresentation (fourierTransportPair d a).quotient :=
  { e with equiv := (fourierTransportQuotient d a).symm.trans e.equiv }

/-- Pushing a realized stage through a group isomorphism just changes its quotient
presentation, leaving its elementary Schwartz space unchanged. -/
private theorem fourierTransportStage (d : A ≃ₜ* B) (a : BruhatStructuralPair A)
    (e : ElementaryLCAPresentation a.quotient) :
    (LinearMap.funLeft ℂ ℂ d.symm).comp (schwartzBruhatStageRealization a e) =
      schwartzBruhatStageRealization (fourierTransportPair d a) (fourierTransportPresentation d a e) := by
  classical
  let b := fourierTransportPair d a
  let q := fourierTransportQuotient d a
  let e' := fourierTransportPresentation d a e
  refine LinearMap.ext fun s ↦ funext (d.surjective.forall.mpr ?_)
  intro x
  have hmem : d x ∈ b.val.1 ↔ x ∈ a.val.1 := by
    change d x ∈ a.val.1.map d.toMulEquiv.toMonoidHom ↔ _
    exact Subgroup.mem_map_iff_mem d.injective
  change schwartzBruhatStageRealization a e s (d.symm (d x)) =
    schwartzBruhatStageRealization b e' s (d x)
  rw [d.symm_apply_apply, schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ a.val.1
  · rw [dite_eq_left hx, dite_eq_left (hmem.mpr hx)]
    have hq : q (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨d x, hmem.mpr hx⟩ := rfl
    change s (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))) =
      s (Multiplicative.toAdd (e.equiv (q.symm (QuotientGroup.mk ⟨d x, hmem.mpr hx⟩))))
    rw [← hq, q.symm_apply_apply]
  · rw [dite_eq_right hx, dite_eq_right (hx ∘ hmem.mp)]

/-- Pushing a function through a group isomorphism is continuous for the
Schwartz–Bruhat topology because it carries each stage into a stage. -/
private theorem schwartzBruhat_fourierTransport (d : A ≃ₜ* B) :
    ∃ T : SchwartzBruhat A →L[ℂ] SchwartzBruhat B,
      ∀ (f : SchwartzBruhat A) (y : B), T f y = f (d.symm y) := by
  let L := LinearMap.funLeft ℂ ℂ d.symm
  have hL : (schwartzBruhatSubmodule A).map L ≤ schwartzBruhatSubmodule B := by
    simp only [schwartzBruhatSubmodule, Submodule.map_iSup, iSup_le_iff]
    intro a e
    rintro w ⟨_, ⟨s, rfl⟩, rfl⟩
    exact Submodule.mem_iSup_of_mem (fourierTransportPair d a)
      (Submodule.mem_iSup_of_mem (fourierTransportPresentation d a e)
        ⟨s, (LinearMap.congr_fun (fourierTransportStage d a e) s).symm⟩)
  let T : SchwartzBruhat A →ₗ[ℂ] SchwartzBruhat B :=
    (L.comp (schwartzBruhatSubmodule A).subtype).codRestrict (schwartzBruhatSubmodule B)
      (fun f ↦ hL ⟨f, f.property, rfl⟩)
  refine ⟨⟨T, ?_⟩, fun _ _ ↦ rfl⟩
  let pB : {p : Seminorm ℂ (schwartzBruhatSubmodule B) //
      ∀ (b : BruhatStructuralPair B) (e : ElementaryLCAPresentation b.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion b e)} →
          Seminorm ℂ (schwartzBruhatSubmodule B) := Subtype.val
  refine (withGeneratingSeminorms_spec _ pB).continuous_of_continuous_comp T fun p ↦ ?_
  let q := p.val.comp T
  have hq (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (q ∘ schwartzBruhatStageInclusion a e) := by
    let b := fourierTransportPair d a
    let e' := fourierTransportPresentation d a e
    have heq (s : SchwartzBruhatStage e) :
        schwartzBruhatStageInclusion b e' s = T (schwartzBruhatStageInclusion a e s) :=
      Subtype.ext (LinearMap.congr_fun (fourierTransportStage d a e) s).symm
    exact (p.property b e').congr fun s ↦ congrArg (fun f ↦ p.val f) (heq s)
  let i : {p : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} := ⟨q, hq⟩
  exact (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

end FourierTransport

section AveragingAndFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

variable (K : Subgroup G)

section CompactAveraging

local instance sec1cCompactSubgroupMeasurableSpace : MeasurableSpace K := borel _

private theorem fullBruhatStage_average (hG : IsCompactlyGeneratedGroup G) (hk : IsBruhatGoodSubgroup K)
    (μK : Measure K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK] (f : G → ℂ) (x : G)
    (hK : IsCompact (K : Set G)) : schwartzBruhatStageAverage (fullBruhatStage hG hk) f x =
      ∫ k : K, f (x * k.val) ∂μK := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : BorelSpace K := ⟨rfl⟩
  let U : TopologicalSpace.PositiveCompacts K := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let : IsProbabilityMeasure (Measure.haarMeasure U) := ⟨Measure.haarMeasure_self⟩
  change (if x ∈ (⊤ : Subgroup G) then ∫ k : K, f (k.val * x) ∂Measure.haarMeasure U else 0) = _
  rw [ite_eq_left (Subgroup.mem_top x), Measure.isHaarMeasure_eq_of_isProbabilityMeasure (Measure.haarMeasure U) μK]
  simp_rw [mul_comm _ x]

/-- Paper: Lemma D.1.6.18, p. 772. Normalized Haar averaging over a compact
subgroup of an elementary group gives a continuous surjection of Schwartz spaces. -/
theorem elementary_schwartzBruhat_average (e : ElementaryLCAPresentation G)
    (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK] :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      (∀ (f : SchwartzBruhat G) (x : G),
        Integrable (fun k : K ↦ f (x * k.val)) μK ∧
        P f (QuotientGroup.mk x) = ∫ k : K, f (x * k.val) ∂μK) ∧
      Function.Surjective P := by
  classical
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK.isClosed
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : BorelSpace K := ⟨rfl⟩
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  have hOpen := isOpen_lcaAnnihilator K hK
  have hk : IsBruhatGoodSubgroup K := ⟨hK.isClosed, hOpen,
    isCompactlyGeneratedGroup_closedSubgroup (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean hE.2)
      _ ((lcaAnnihilator K).isClosed_of_isOpen hOpen)⟩
  let a := fullBruhatStage hE.1 hk
  have hW := fullBruhatStage_quotientEquiv hE.1 hk (QuotientGroup.mk' K)
    QuotientGroup.isOpenQuotientMap_mk (QuotientGroup.ker_mk' K)
  let w := hW.choose
  have hw := hW.choose_spec
  let d := Classical.choice a.elementary
  let eQ : ElementaryLCAPresentation (G ⧸ K) := {d with equiv := w.symm.trans d.equiv}
  have hI := elementarySchwartz_equiv_schwartzBruhat eQ
  let I := hI.choose
  have hR := schwartzBruhatStage_average_retraction a d
  let R := hR.choose
  refine ⟨I.toContinuousLinearMap.comp R, fun f x ↦ ⟨?_, ?_⟩,
    I.surjective.comp (show Function.LeftInverse R (schwartzBruhatStageInclusion a d) from hR.choose_spec.1).surjective⟩
  · have hI' := elementarySchwartz_equiv_schwartzBruhat e
    let s := hI'.choose.symm f
    have hs (y : G) : f y = s (e.equiv y).toAdd :=
      (congrArg (fun z : SchwartzBruhat G ↦ z y) (hI'.choose.apply_symm_apply f)).symm.trans
        (hI'.choose_spec s y)
    have hc : Continuous f.val := by
      exact ((elementarySchwartz_continuousFunction s).comp (continuous_toAdd.comp e.equiv.continuous)).congr fun y ↦ (hs y).symm
    exact (hc.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · change I (R f) (QuotientGroup.mk x) = _
    rw [hI.choose_spec]
    change R f (d.equiv (w.symm (QuotientGroup.mk x))).toAdd = _
    have hwx : w.symm (QuotientGroup.mk x) = QuotientGroup.mk (⟨x, Subgroup.mem_top x⟩ : a.val.1) :=
      w.toEquiv.symm_apply_eq.mpr (hw x).symm
    refine (congrArg (fun y : a.quotient ↦ R f (d.equiv y).toAdd) hwx).trans ?_
    have h := hR.choose_spec.2 f x
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx] at h
    refine h.trans ?_
    exact fullBruhatStage_average K hE.1 hk μK f x hK

end CompactAveraging

section FibreIntegral

omit hTop hT2 hLC in
/-- Paper: Definition D.1.3.1, p. 750. An elementary Schwartz function is continuous
on the elementary group. Its lifts along the covering map are smooth on each discrete
fibre, and the covering map is open. -/
theorem elementarySchwartz_continuous {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (f : ElementarySchwartz m n r F) :
    Continuous (f : ElementaryLieGroup m n r F → ℂ) := by
  have hf := (show elementarySchwartzSubmodule m n r F from f).property.1
  let π : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) :=
    fun xt ↦ (xt.1, fun i ↦ (xt.2 i : AddCircle (1 : ℝ)))
  have hπ : IsOpenQuotientMap π := by
    have h1 : IsOpenQuotientMap
        (Pi.map fun _ : Fin n ↦ (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))) :=
      IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
    let e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
    have h2 : IsOpenQuotientMap e := ⟨e.surjective, e.continuous, e.isOpenMap⟩
    exact IsOpenQuotientMap.id.prodMap (h1.comp h2)
  have hfib : ∀ a b, Continuous
      (fun p : EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) ↦ f (p.1, p.2, a, b)) :=
    fun a b ↦ by
      rw [← hπ.continuous_comp_iff]
      exact (hf a b).continuous
  rw [continuous_iff_continuousAt]
  rintro ⟨x, z, a, b⟩
  have hopen : IsOpen {p : ElementaryLieGroup m n r F | p.2.2 = (a, b)} :=
    (isOpen_discrete {(a, b)}).preimage (continuous_snd.comp continuous_snd)
  have heq : (f : ElementaryLieGroup m n r F → ℂ) =ᶠ[𝓝 (x, z, a, b)]
      fun p ↦ f (p.1, p.2.1, a, b) := by
    filter_upwards [hopen.mem_nhds rfl] with p hp
    obtain ⟨p1, p2, p3, p4⟩ := p
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rfl
  exact ((hfib a b).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).continuousAt.congr heq.symm

omit hTop hT2 hLC in
/-- Paper: Definition D.1.5.1(1), p. 760. A good subgroup is compact. It is the
annihilator of its open annihilator (Lemma D.1.4.6(1)), and by duality the annihilator
of an open subgroup of the dual is compact (Lemma D.1.4.6(4)). -/
theorem IsBruhatGoodSubgroup.isCompact [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] {k : Subgroup G} (hk : IsBruhatGoodSubgroup k) :
    IsCompact (k : Set G) := by
  obtain ⟨hkc, hko, -⟩ := hk
  have hJ := isCompact_lcaAnnihilator (G := PontryaginDual G) (lcaAnnihilator k) hko
  have hpre : (k : Set G) = pontryaginDual_eval ⁻¹'
      (lcaAnnihilator (lcaAnnihilator k) : Set (PontryaginDual (PontryaginDual G))) := by
    conv_lhs => rw [← lcaDualAnnihilator_annihilator k hkc]
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage, mem_lcaDualAnnihilator_iff,
      mem_lcaAnnihilator_iff]
    rfl
  rw [hpre]
  exact isClosedEmbedding_pontryaginDual_eval.isCompact_preimage hJ

omit hTop hT2 hLC in
/-- Compact generation passes to the target of a continuous, open and surjective
homomorphism. -/
theorem isCompactlyGeneratedGroup_of_surjective {X : Type*} [CommGroup X] [TopologicalSpace X]
    (f : X →* G) (hf : Continuous f) (hfo : IsOpenMap f) (hs : Function.Surjective f)
    (h : IsCompactlyGeneratedGroup X) : IsCompactlyGeneratedGroup G := by
  obtain ⟨U, hU, hUc, hGen⟩ := h
  refine ⟨f '' U, ?_, hUc.image hf, ?_⟩
  · have := hfo.image_mem_nhds hU
    rwa [map_one] at this
  · rw [← MonoidHom.map_closure, hGen, Subgroup.map_top_of_surjective f hs]

/-- Paper: Theorem D.1.7.1, p. 776. The images of the two subgroups of a structural
pair in the quotient by a closed subgroup form a structural pair of the quotient.
The image of the good subgroup is compact, and its annihilator is a closed subgroup
of the compactly generated annihilator of the good subgroup. -/
theorem BruhatStructuralPair.exists_quotient (hK : IsClosed (K : Set G))
    (a : BruhatStructuralPair G) :
    ∃ b : BruhatStructuralPair (G ⧸ K),
      b.val.1 = a.val.1.map (QuotientGroup.mk' K) ∧
        OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K) := by
  obtain ⟨hHo, hHcg, hCgood, hCH⟩ := a.property
  have : IsClosed (K : Set G) := hK
  have hCc := hCgood.isCompact
  let q := QuotientGroup.mk' K
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hqc : Continuous q := QuotientGroup.continuous_mk
  refine ⟨⟨(a.val.1.map q, OrderDual.toDual ((OrderDual.ofDual a.val.2).map q)),
    ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · change IsOpen ((a.val.1.map q : Subgroup (G ⧸ K)) : Set (G ⧸ K))
    rw [Subgroup.coe_map]
    exact hqo _ hHo
  · -- The open subgroup of the quotient is compactly generated.
    let f := q.subgroupMap a.val.1
    have hfc : Continuous f := (hqc.comp continuous_subtype_val).subtype_mk _
    have hfo : IsOpenMap f := by
      intro O hO
      have hO' : IsOpen (q '' (Subtype.val '' O)) := hqo _ (hHo.isOpenMap_subtype_val _ hO)
      convert hO'.preimage continuous_subtype_val using 1
      ext y
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨o.val, ⟨o, ho, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, hy⟩
        exact ⟨o, ho, Subtype.ext hy⟩
    exact isCompactlyGeneratedGroup_of_surjective f hfc hfo
      (q.subgroupMap_surjective a.val.1) hHcg
  · -- The image of the good subgroup is good.
    have hCq : IsCompact (((OrderDual.ofDual a.val.2).map q : Subgroup (G ⧸ K)) : Set (G ⧸ K)) := by
      rw [Subgroup.coe_map]
      exact hCc.image hqc
    refine ⟨hCq.isClosed, isOpen_lcaAnnihilator _ hCq, ?_⟩
    obtain ⟨ε, hε⟩ := lcaQuotientDual_equiv_annihilator K hK
    set C := OrderDual.ofDual a.val.2
    obtain ⟨-, hCo, hCcg⟩ := hCgood
    have : LocallyCompactSpace (lcaAnnihilator C) :=
      hCo.isOpenEmbedding_subtypeVal.locallyCompactSpace
    let M : Subgroup (lcaAnnihilator C) := (lcaAnnihilator K).comap (lcaAnnihilator C).subtype
    have hKc : IsClosed (lcaAnnihilator K : Set (PontryaginDual G)) := by
      have : (lcaAnnihilator K : Set (PontryaginDual G)) =
          (PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)) ⁻¹' {1} := rfl
      rw [this]
      exact isClosed_singleton.preimage (PontryaginDual.map _).continuous
    have hMc : IsClosed (M : Set (lcaAnnihilator C)) := hKc.preimage continuous_subtype_val
    have hM := isCompactlyGeneratedGroup_closedSubgroup hCcg M hMc
    refine isCompactlyGeneratedGroup_of_continuousMulEquiv ?_ hM
    have hto : ∀ ψ : M, ε.symm ⟨ψ.val.val, ψ.2⟩ ∈ lcaAnnihilator (C.map q) := by
      intro ψ
      rw [mem_lcaAnnihilator_iff]
      rintro ⟨_, c, hc, rfl⟩
      have h1 := hε (ε.symm ⟨ψ.val.val, ψ.2⟩) c
      rw [ContinuousMulEquiv.apply_symm_apply] at h1
      change (ε.symm ⟨ψ.val.val, ψ.2⟩) (QuotientGroup.mk c) = 1
      rw [← h1]
      exact (mem_lcaAnnihilator_iff C _).mp ψ.val.2 ⟨c, hc⟩
    have hinv₁ : ∀ χ : lcaAnnihilator (C.map q), (ε χ.val).val ∈ lcaAnnihilator C := by
      intro χ
      rw [mem_lcaAnnihilator_iff]
      intro c
      rw [hε]
      exact (mem_lcaAnnihilator_iff _ _).mp χ.2 ⟨q c, c, c.2, rfl⟩
    exact
      { toFun := fun ψ ↦ ⟨ε.symm ⟨ψ.val.val, ψ.2⟩, hto ψ⟩
        invFun := fun χ ↦ ⟨⟨(ε χ.val).val, hinv₁ χ⟩, (ε χ.val).2⟩
        left_inv := fun ψ ↦ by
          apply Subtype.ext; apply Subtype.ext
          simp
        right_inv := fun χ ↦ by
          apply Subtype.ext
          change ε.symm ⟨(ε χ.val).val, (ε χ.val).2⟩ = χ.val
          simp
        map_mul' := fun ψ₁ ψ₂ ↦ by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          rw [← map_mul]
          rfl
        continuous_toFun := (ε.symm.continuous.comp
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
        continuous_invFun := ((continuous_subtype_val.comp
          (ε.continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _ }
  · exact Subgroup.map_mono hCH

/-- Paper: Theorem D.1.7.1, p. 776. When the structural pair `b` of the quotient by `K`
is the image of the structural pair `a`, the quotient map of `G` induces a continuous,
open and surjective homomorphism from the elementary quotient of `a` to that of `b`.
Its kernel is the image of `K ∩ a.val.1`. -/
theorem BruhatStructuralPair.exists_quotient_hom (a : BruhatStructuralPair G)
    (b : BruhatStructuralPair (G ⧸ K))
    (hb₁ : b.val.1 = a.val.1.map (QuotientGroup.mk' K))
    (hb₂ : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K)) :
    ∃ p : a.quotient →* b.quotient, Continuous p ∧ IsOpenMap p ∧ Function.Surjective p ∧
      p.ker = (K.comap a.val.1.subtype).map
        (QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)) ∧
      ∀ (x : G) (hx : x ∈ a.val.1) (hq : (QuotientGroup.mk x : G ⧸ K) ∈ b.val.1),
        p (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨QuotientGroup.mk x, hq⟩ := by
  obtain ⟨hHo, -, -, hCH⟩ := a.property
  let H := a.val.1
  let C := OrderDual.ofDual a.val.2
  let N := C.comap H.subtype
  let Nb := (OrderDual.ofDual b.val.2).comap b.val.1.subtype
  let q := QuotientGroup.mk' K
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hqc : Continuous q := QuotientGroup.continuous_mk
  let f₀ : H →* b.val.1 := (q.comp H.subtype).codRestrict b.val.1 fun h ↦ by
    rw [hb₁]; exact ⟨h.val, h.2, rfl⟩
  have hf₀ : ∀ h : H, (f₀ h).val = q h.val := fun h ↦ rfl
  have hf₀c : Continuous f₀ := (hqc.comp continuous_subtype_val).subtype_mk _
  have hf₀o : IsOpenMap f₀ := by
    intro O hO
    have hO' : IsOpen (q '' (Subtype.val '' O)) := hqo _ (hHo.isOpenMap_subtype_val _ hO)
    convert hO'.preimage continuous_subtype_val using 1
    ext y
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o.val, ⟨o, ho, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨o, ho, rfl⟩, hy⟩
      exact ⟨o, ho, Subtype.ext hy⟩
  have hf₀s : Function.Surjective f₀ := by
    rintro ⟨y, hy⟩
    rw [hb₁] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let f₁ : H →* b.quotient := (QuotientGroup.mk' Nb).comp f₀
  have hN : N ≤ f₁.ker := by
    intro h hh
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_comap, Subgroup.coe_subtype, hf₀, hb₂]
    exact ⟨h.val, hh, rfl⟩
  let p : a.quotient →* b.quotient := QuotientGroup.lift N f₁ hN
  have hpmk : ∀ h : H, p (QuotientGroup.mk h) = QuotientGroup.mk (f₀ h) := fun h ↦ rfl
  have hcomp : (p ∘ (QuotientGroup.mk : H → a.quotient)) = (QuotientGroup.mk' Nb) ∘ f₀ :=
    funext hpmk
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr ?_
    rw [hcomp]
    exact QuotientGroup.continuous_mk.comp hf₀c
  · intro U hU
    have hU' : p '' U =
        ((QuotientGroup.mk' Nb) ∘ f₀) '' ((QuotientGroup.mk : H → a.quotient) ⁻¹' U) := by
      rw [← hcomp, Set.image_comp, Set.image_preimage_eq _ (QuotientGroup.mk_surjective)]
    rw [hU', Set.image_comp]
    exact QuotientGroup.isOpenMap_coe _ (hf₀o _ (hU.preimage QuotientGroup.continuous_mk))
  · intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨h, rfl⟩ := hf₀s y
    exact ⟨QuotientGroup.mk h, rfl⟩
  · ext y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, hpmk, QuotientGroup.eq_one_iff, Subgroup.mem_comap,
      Subgroup.coe_subtype, hf₀, hb₂]
    constructor
    · rintro ⟨c, hc, hch⟩
      have hk : c⁻¹ * h.val ∈ K := QuotientGroup.eq.mp hch
      have hkH : c⁻¹ * h.val ∈ H := H.mul_mem (H.inv_mem (hCH hc)) h.2
      refine ⟨⟨c⁻¹ * h.val, hkH⟩, hk, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
      change (c⁻¹ * h.val)⁻¹ * h.val ∈ C
      simpa using hc
    · rintro ⟨k, hk, hkh⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hkh
      refine ⟨(k⁻¹ * h).val, hkh, ?_⟩
      change (QuotientGroup.mk ((k⁻¹ * h : H) : G) : G ⧸ K) = QuotientGroup.mk h.val
      rw [QuotientGroup.eq]
      have : ((k⁻¹ * h : H) : G)⁻¹ * h.val = k.val := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
        rw [mul_assoc, mul_comm (k : G), inv_mul_cancel_left]
      rw [this]
      exact hk
  · intro x hx hq
    rw [hpmk]
    rfl

section

omit hTop hT2 hLC
open Function
open scoped Pointwise

/-- Translating a compact set gives a uniform bound on the Haar mass of its intersection
with a closed subgroup. Translate a point in the intersection to the identity. -/
private theorem fiberIntegral_measure_translate {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (K : Subgroup A) (hK : IsClosed (K : Set A)) (ν : Measure K) [ν.IsHaarMeasure]
    (C : Set A) (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ x : A, ν {k : K | x * k.val ∈ C} ≤ M := by
  let D := (Subtype.val : K → A) ⁻¹' (C⁻¹ * C)
  have hD : IsCompact D := hK.isClosedEmbedding_subtypeVal.isCompact_preimage (hC.inv.mul hC)
  refine ⟨ν D, hD.measure_lt_top, fun x ↦ ?_⟩
  by_cases h : ∃ k : K, x * k.val ∈ C
  · obtain ⟨k₀, hk₀⟩ := h
    calc ν {k : K | x * k.val ∈ C} ≤ ν ((k₀⁻¹ * ·) ⁻¹' D) := by
          apply measure_mono
          intro k hk
          exact ⟨(x * k₀.val)⁻¹, Set.inv_mem_inv.mpr hk₀, x*k.val, hk, by
            change (x * k₀.val)⁻¹ * (x * k.val) = k₀.val⁻¹ * k.val
            group⟩
      _ = _ := measure_preimage_mul _ _ _
  · rw [show {k : K | x * k.val ∈ C} = ∅ from Set.eq_empty_iff_forall_notMem.mpr
      (fun k hk ↦ h ⟨k,hk⟩), measure_empty]
    exact bot_le

private def fiberCoord {m n r : ℕ} {F : Type*} (g : ElementaryLieGroup m n r F) :
    Fin m ⊕ Fin r → ℝ := Sum.elim (fun i ↦ g.1 i) (fun j ↦ (g.2.2.1 j : ℝ))

private def fiberWeight {J : Type*} [Fintype J] (x : J → ℝ) : ℝ := ∏ j, (1 + (x j)^2)⁻¹

/-- The reciprocal quadratic product weight has uniformly bounded integrals on all cosets.
Partition the real and lattice coordinates into unit boxes indexed by an integer lattice. -/
private theorem fiberIntegral_weight {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (e : ElementaryLCAPresentation A) (K : Subgroup A) (hK : IsClosed (K : Set A))
    (ν : Measure K) [ν.IsHaarMeasure] :
    ∃ C : ℝ, ∀ y : A,
      let w := fun k : K ↦ fiberWeight (fiberCoord (e.equiv (y * k.val)).toAdd)
      Integrable w ν ∧ (∫ k, w k ∂ν) ≤ C := by
  classical
  let J := Fin e.realDim ⊕ Fin e.latticeRank
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let coord (x : A) := fiberCoord (e.equiv x).toAdd
  have hc : Continuous coord := by
    apply continuous_pi
    intro j
    cases j with
    | inl i => exact (PiLp.continuous_apply 2 _ i).comp e.equiv.continuous.fst
    | inr i =>
      exact (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ℝ))).comp
        ((continuous_apply i).comp e.equiv.continuous.snd.snd.fst)
  let box : Set E := ((EuclideanSpace.equiv (Fin e.realDim) ℝ) ⁻¹'
      (Set.pi univ fun _ : Fin e.realDim ↦ Icc (0:ℝ) 1)) ×ˢ (univ ×ˢ ({0} ×ˢ univ))
  have hbox : IsCompact box := (((EuclideanSpace.equiv (Fin e.realDim) ℝ).toHomeomorph.isProperMap.isCompact_preimage
      (isCompact_univ_pi fun _ ↦ isCompact_Icc)).prod
      (isCompact_univ.prod (isCompact_singleton.prod isCompact_univ)))
  obtain ⟨M,hM,hm⟩ := fiberIntegral_measure_translate K hK ν _ (e.equiv.toHomeomorph.isProperMap.isCompact_preimage hbox)
  let label (x : A) (j : J) := ⌊coord x j⌋
  have hlabel : Measurable label := Measurable.of_eval fun j ↦
    ((continuous_apply j).comp hc).measurable.floor
  have hcell (y : A) (i : J → ℤ) : ν {k : K | label (y*k.val) = i} ≤ M := by
    let c : A := e.equiv.symm (.ofAdd ((WithLp.toLp 2 (fun j ↦ (i (.inl j) : ℝ))), 0,
      (fun j ↦ i (.inr j)), 0))
    apply le_trans (measure_mono ?_) (hm (c⁻¹*y))
    intro k hk
    have he : label (y*k.val) = i := hk
    have htrans : e.equiv (c⁻¹ * y * k.val) = (e.equiv c)⁻¹ * e.equiv (y*k.val) := by simp [mul_assoc]
    change (e.equiv (c⁻¹*y*k.val)).toAdd ∈ box
    rw [htrans,show e.equiv c = _ from e.equiv.apply_symm_apply _]
    refine ⟨fun j _ ↦ ⟨?_,?_⟩, trivial, ?_, trivial⟩
    · change 0 ≤ -(i (.inl j) : ℝ) + coord (y*k.val) (.inl j)
      rw [← he]
      dsimp [label]
      linarith [Int.floor_le (coord (y*k.val) (.inl j))]
    · change -(i (.inl j) : ℝ) + coord (y*k.val) (.inl j) ≤ 1
      rw [← he]
      have := Int.lt_floor_add_one (coord (y*k.val) (.inl j))
      dsimp [label]
      linarith
    · change -(fun j ↦ i (Sum.inr j)) + (e.equiv (y*k.val)).toAdd.2.2.1 = 0
      ext j
      have h := congrFun he (Sum.inr j)
      change ⌊((e.equiv (y*k.val)).toAdd.2.2.1 j : ℝ)⌋ = i (.inr j) at h
      simp [Pi.add_apply, Pi.neg_apply, ← h]
  let d (i : J → ℤ) := fiberWeight fun j ↦ (i j : ℝ)
  have hd : Summable d := summable_lattice_product
  have hd0 i : 0 ≤ d i := Finset.prod_nonneg fun _ _ ↦ by positivity
  let B : ℝ := 8 ^ Fintype.card J
  have hB : 0 ≤ B := by positivity
  refine ⟨(B * M.toReal) * ∑' i, d i, fun y ↦ ?_⟩
  let w (k : K) := fiberWeight (coord (y * k.val))
  let S (i : J → ℤ) := {k : K | label (y*k.val) = i}
  have hS (i) : MeasurableSet (S i) := measurableSet_singleton i |>.preimage
    (hlabel.comp (continuous_const.mul continuous_subtype_val).measurable)
  have hcov : ⋃ i, S i = univ := iUnion_eq_univ_iff.mpr fun k ↦ ⟨_,rfl⟩
  have hw (k : K) : 0 ≤ w k := Finset.prod_nonneg fun _ _ ↦ by positivity
  have hwc : Continuous w := continuous_finsetProd _ fun j _ ↦
    (continuous_const.add ((((continuous_apply j).comp hc).comp
      (continuous_const.mul continuous_subtype_val)).pow 2)).inv₀ (fun k ↦ by change 1 + coord (y*k.val) j ^ 2 ≠ 0; positivity)
  have hbound (i) (k : K) (hk : k ∈ S i) : w k ≤ B * d i := by
    change label (y*k.val) = i at hk
    subst i
    dsimp [w,d,B,fiberWeight]
    rw [show (8:ℝ) ^ Fintype.card J = ∏ _ : J, (8:ℝ) from by simp, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun j _ ↦ ?_)
    let t := coord (y*k.val) j
    change (1+t^2)⁻¹ ≤ 8 * (1+(⌊t⌋:ℝ)^2)⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
    have h1 := Int.floor_le t
    have h2 := Int.lt_floor_add_one t
    nlinarith [sq_nonneg (t - 2*(⌊t⌋:ℝ)), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2.le),
      sq_nonneg t]
  have hm' (i) : ν (S i) < ⊤ := (hcell y i).trans_lt hM
  have hi (i) : IntegrableOn w (S i) ν :=
    (integrableOn_const (C := B * d i) (hs := (hm' i).ne)).mono' hwc.aestronglyMeasurable
      (ae_restrict_mem (hS i) |>.mono fun k hk ↦ by
        simpa [Real.norm_of_nonneg (hw k)] using hbound i k hk)
  have hI (i) : ∫ k in S i, ‖w k‖ ∂ν ≤ (B*M.toReal)*d i := by
    calc _ ≤ ∫ _ in S i, B * d i ∂ν := integral_mono_ae (hi i).norm
          (integrableOn_const (C := B * d i) (hs := (hm' i).ne))
          ((ae_restrict_mem (hS i)).mono fun k hk ↦ by simpa [Real.norm_of_nonneg (hw k)] using hbound i k hk)
      _ = (ν (S i)).toReal * (B*d i) := by rw [setIntegral_const, smul_eq_mul]; rfl
      _ ≤ _ := by
        calc _ ≤ M.toReal * (B*d i) := mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hM.ne (hcell y i)) (mul_nonneg hB (hd0 _))
          _ = _ := by ring
  have hsum := hd.mul_left (B*M.toReal)
  have hs := hsum.of_nonneg_of_le (fun i ↦ integral_nonneg fun k ↦ norm_nonneg (w k)) hI
  have hint := integrableOn_iUnion_of_summable_integral_norm hi hs
  rw [hcov, integrableOn_univ] at hint
  refine ⟨hint,?_⟩
  change ∫ k, w k ∂ν ≤ _
  have hdj : Pairwise (Disjoint on S) := fun i j hij ↦ Set.disjoint_left.mpr
    fun k hi hj ↦ hij ((show label (y*k.val) = i from hi).symm.trans hj)
  calc _ = ∑' i, ∫ k in S i, w k ∂ν := by
          rw [← integral_iUnion (fun i ↦ hS i) hdj, hcov, setIntegral_univ]
          rwa [hcov, integrableOn_univ]
    _ ≤ ∑' i, (B*M.toReal)*d i := by
          simpa only [Real.norm_of_nonneg (hw _)] using hs.tsum_le_tsum hI hsum
    _ = _ := tsum_mul_left

/-- In a finite-dimensional parameter, differentiate a family of integrals whose
directional derivatives again belong to the family, with local integrable majorants. -/
private theorem integral_family_fderiv {V T X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace X] (ν : Measure X) (F : T → V → X → ℂ)
    (hm : ∀ t u, AEStronglyMeasurable (F t u) ν)
    (hd : ∀ t u k, DifferentiableAt ℝ (fun v ↦ F t v k) u)
    (D : T → V → T) (hD : ∀ t u k v, fderiv ℝ (fun w ↦ F t w k) u v = F (D t v) u k)
    (hb : ∀ t u, ∃ b : X → ℝ, Integrable b ν ∧ ∀ᶠ z in 𝓝 u, ∀ k, ‖F t z k‖ ≤ b k) :
    (∀ t, ContDiff ℝ ∞ (fun u ↦ ∫ k, F t u k ∂ν)) ∧
      ∀ t u v, fderiv ℝ (fun w ↦ ∫ k, F t w k ∂ν) u v = ∫ k, F (D t v) u k ∂ν := by
  classical
  let I := Fin (Module.finrank ℝ V)
  let B := Module.finBasis ℝ V
  let ℓ (i : I) := (ContinuousLinearMap.proj i).comp B.equivFunL.toContinuousLinearMap
  let d t u k := fderiv ℝ (fun w ↦ F t w k) u
  have hmeas (t u) : AEStronglyMeasurable (d t u) ν := by
    have he (k) : d t u k = ∑ i : I, (ContinuousLinearMap.smulRightL ℝ V ℂ (ℓ i)) (F (D t (B i)) u k) := by
      ext v
      change d t u k v = _
      conv_lhs => rw [← B.sum_repr v, map_sum]
      simp only [map_smul, sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
      exact Finset.sum_congr rfl fun i _ ↦ congrArg ((B.repr v i) • ·) (hD t u k (B i))
    rw [show d t u = _ from funext he]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
      (ContinuousLinearMap.smulRightL ℝ V ℂ (ℓ i)).continuous.comp_aestronglyMeasurable (hm _ _)
  have hcalc (t u) : HasFDerivAt (fun w ↦ ∫ k, F t w k ∂ν) (∫ k, d t u k ∂ν) u ∧ Integrable (d t u) ν := by
    obtain ⟨c,hc,hB⟩ := B.exists_opNorm_le (F := ℂ)
    choose b hi hle using fun i : I ↦ hb (D t (B i)) u
    let bound (k : X) := c * ∑ i : I, |b i k|
    have hbi : Integrable bound ν := (integrable_finsetSum _ fun i _ ↦ (hi i).abs).const_mul _
    have hev : ∀ᶠ w in 𝓝 u, ∀ k, ‖d t w k‖ ≤ bound k := by
      filter_upwards [eventually_all.mpr hle] with w hw k
      apply hB (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
      intro i
      exact (hD t w k (B i) ▸ hw i k : ‖fderiv ℝ (fun v ↦ F t v k) w (B i)‖ ≤ b i k) |>.trans
        ((le_abs_self _).trans (Finset.single_le_sum (f := fun i ↦ |b i k|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)))
    obtain ⟨b₀,hi₀,h₀⟩ := hb t u
    have hfi := hi₀.mono' (hm t u) (.of_forall (mem_of_mem_nhds h₀))
    refine ⟨hasFDerivAt_integral_of_dominated_of_fderiv_le (s := {w | ∀ k, ‖d t w k‖ ≤ bound k})
      (bound := bound) hev (.of_forall (hm t)) hfi (hmeas t u) (.of_forall fun k w hw ↦ hw k)
      hbi (.of_forall fun k w _ ↦ (hd t w k).hasFDerivAt), hbi.mono' (hmeas t u) (.of_forall (mem_of_mem_nhds hev))⟩
  have hval (t u v) : fderiv ℝ (fun w ↦ ∫ k, F t w k ∂ν) u v = ∫ k, F (D t v) u k ∂ν := by
    rw [(hcalc t u).1.fderiv, ContinuousLinearMap.integral_apply (hcalc t u).2]
    exact integral_congr_ae (.of_forall fun k ↦ hD t u k v)
  refine ⟨fun t ↦ contDiff_infty.mpr (fun n ↦ ?_), hval⟩
  induction n generalizing t with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun u ↦ (hcalc t u).1.continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ]
    apply contDiff_succ_iff_fderiv_apply.mpr
    refine ⟨fun u ↦ (hcalc t u).1.differentiableAt, by simp, fun v ↦ ?_⟩
    simp only [hval]
    exact ih _

private theorem fiberCoord_add {m n r : ℕ} {F : Type*} [AddCommGroup F]
    (x y : ElementaryLieGroup m n r F) : fiberCoord (x+y) = fiberCoord x + fiberCoord y := by
  funext j
  cases j with
  | inl i => rfl
  | inr i => exact Int.cast_add ..

private theorem fiberWeight_shift {J : Type*} [Fintype J] (x z : J → ℝ)
    (hz : ∀ j, |z j| ≤ 1) : fiberWeight (x+z) ≤ 3 ^ Fintype.card J * fiberWeight x := by
  unfold fiberWeight
  rw [show (3:ℝ) ^ Fintype.card J = ∏ _ : J, (3:ℝ) from by simp, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) (fun j _ ↦ ?_)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
  simp only [Pi.add_apply]
  obtain ⟨h₁,h₂⟩ := abs_le.mp (hz j)
  nlinarith [sq_nonneg (x j + 2*z j), sq_nonneg (x j + z j),
    mul_nonneg (sub_nonneg.mpr h₂) (show 0 ≤ 1 + z j by linarith)]

private theorem fiberIntegral_decay {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (P : MvPolynomial (Fin m ⊕ Fin r) ℂ) (s : ElementarySchwartz m n r F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ElementaryLieGroup m n r F,
      ‖MvPolynomial.eval (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) P * s y‖ ≤
        C * fiberWeight (fiberCoord y) := by
  let R : MvPolynomial (Fin m ⊕ Fin r) ℂ := ∏ j, (1 + MvPolynomial.X j ^ 2)
  obtain ⟨C,hC⟩ := polynomial_weight_bounded (R*P) s
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun y ↦ ?_⟩
  let coord := Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))
  let W := ∏ j, (1 + (fiberCoord y j)^2)
  have he (i) : coord i = (fiberCoord y i : ℂ) := by
    cases i with
    | inl i => rfl
    | inr i => exact (Complex.ofReal_intCast _).symm
  have hW : 0 < W := Finset.prod_pos fun _ _ ↦ by positivity
  have hR : MvPolynomial.eval coord R = (W : ℂ) := by simp [R,W,he]
  have h := hC y
  change ‖MvPolynomial.eval coord (R*P) * s y‖ ≤ C at h
  rw [MvPolynomial.eval_mul, mul_assoc, norm_mul, hR, Complex.norm_real, Real.norm_of_nonneg hW.le] at h
  rw [show fiberWeight (fiberCoord y) = W⁻¹ from by simp [fiberWeight,W, Finset.prod_inv_distrib], ← div_eq_mul_inv,
    le_div_iff₀ hW, mul_comm]
  exact h

private theorem fiberIntegral_orbit_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (L : V →L[ℝ] EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    ∀ (s : ElementarySchwartz m n r F) (v : V), ∃ t : ElementarySchwartz m n r F,
      ∀ (z : ElementaryLieGroup m n r F) u,
        let Fz := fun w ↦ s (z + elementaryCover (L w) 0 0)
        DifferentiableAt ℝ Fz u ∧ fderiv ℝ Fz u v = t (z + elementaryCover (L u) 0 0) := by
  intro s v
  let q := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  let l : ℝ →L[ℝ] _ := (ContinuousLinearMap.id ℝ ℝ).smulRight (L v)
  let c := q.comp l.toLinearMap.toAddMonoidHom
  obtain ⟨B,hB⟩ := elementarySchwartz_orbitDeriv c (elementaryCoverZeroHom_continuous_isOpenMap.1.comp l.continuous)
  refine ⟨B s, fun z u ↦ ?_⟩
  obtain ⟨w,hw⟩ := elementaryCover_surjective z.2.2.1 z.2.2.2 z.1 z.2.1
  change elementaryCover (z.1,w) z.2.2.1 z.2.2.2 = z at hw
  let Fz (a : V) := s (z + q (L a))
  have he (a) : Fz a = s (elementaryCover ((z.1,w) + L a) z.2.2.1 z.2.2.2) := by
    change s (z + elementaryCover (L a) 0 0) = _
    conv_lhs => rw [← hw]
    rw [elementaryCover_add, add_zero, add_zero]
  have hd : DifferentiableAt ℝ Fz u :=
    (funext he) ▸ (((s.property.1 _ _).comp (contDiff_const.add L.contDiff)).differentiable (by simp) u)
  refine ⟨hd, ?_⟩
  have hline : HasDerivAt (fun a : ℝ ↦ u + a • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hh (a : ℝ) : Fz (u+a•v) = s ((z + q (L u)) + c a) := by
    simp only [Fz, map_add, map_smul, ← add_assoc]
    rfl
  change HasDerivAt (fun a : ℝ ↦ Fz (u+a•v)) _ 0 at h
  rw [show (fun a : ℝ ↦ Fz (u+a•v)) = _ from funext hh] at h
  exact h.unique (hB s _)

/-- On each affine lift, mixed partials of the integral are integrals of Schwartz derivatives.
The derivative test depends only on the original test and the list of directions. -/
private theorem fiberIntegral_charts {A V : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ElementaryLCAPresentation A) (K : Subgroup A) (ν : Measure K)
    (L : V →L[ℝ] EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim))
    (hw : ∀ y : A, Integrable (fun k : K ↦ fiberWeight (fiberCoord (e.equiv (y * k.val)).toAdd)) ν) :
    let Ψ (s : SchwartzBruhatStage e) (y : A) (u : V) := ∫ k : K,
      s ((e.equiv (y*k.val)).toAdd + elementaryCover (L u) 0 0) ∂ν
    (∀ s y, ContDiff ℝ ∞ (Ψ s y)) ∧ ∀ (dirs : List V) (s : SchwartzBruhatStage e),
      ∃ t : SchwartzBruhatStage e, ∀ y u, iteratedFDeriv ℝ dirs.length (Ψ s y) u dirs.get = Ψ t y u := by
  classical
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let J := Fin e.realDim ⊕ Fin e.latticeRank
  let σ := (elementaryCoverZeroHom (r := e.latticeRank) (F := e.finiteFactor)).comp L.toLinearMap.toAddMonoidHom
  let g (u : V) := e.equiv.symm (.ofAdd (σ u))
  have hg (u) : e.equiv (g u) = .ofAdd (σ u) := e.equiv.apply_symm_apply _
  let z (y : A) (u : V) (k : K) : E := (e.equiv (y*k.val)).toAdd + σ u
  have hz (y u k) : z y u k = (e.equiv (y*g u*k.val)).toAdd := by
    rw [mul_right_comm y, map_mul _ (y*k.val), hg]
    rfl
  let F (y : A) (s : SchwartzBruhatStage e) (u : V) (k : K) := s (z y u k)
  let Ψ (s : SchwartzBruhatStage e) (y : A) (u : V) := ∫ k, F y s u k ∂ν
  choose D hD using fiberIntegral_orbit_deriv (r := e.latticeRank) (F := e.finiteFactor) L
  have hcalc (y : A) : (∀ s, ContDiff ℝ ∞ (Ψ s y)) ∧ ∀ s u v,
      fderiv ℝ (Ψ s y) u v = Ψ (D s v) y u := by
    refine integral_family_fderiv ν (F y) ?_ ?_ D ?_ ?_
    · intro s u
      exact ((elementarySchwartz_continuousFunction s).comp
        ((show Continuous (fun k : K ↦ (e.equiv (y*k.val)).toAdd) from
          e.equiv.continuous.comp (continuous_const.mul continuous_subtype_val)).add continuous_const)).aestronglyMeasurable
    · exact fun s u k ↦ (hD s 0 (e.equiv (y*k.val)).toAdd u).1
    · exact fun s u k v ↦ (hD s v (e.equiv (y*k.val)).toAdd u).2
    · intro s u
      obtain ⟨C,hC,hCs⟩ := fiberIntegral_decay 1 s
      let M : ℝ := 3 ^ Fintype.card J
      let w (k : K) := fiberWeight (fiberCoord (z y u k))
      have hw' : Integrable w ν := by simpa only [w,hz] using hw (y*g u)
      refine ⟨fun k ↦ (C*M) * w k, hw'.const_mul _, ?_⟩
      have hc (j : J) : Continuous (fun v : V ↦ fiberCoord (σ v) j) := by
        cases j with
        | inl i => exact (PiLp.continuous_apply 2 _ i).comp L.continuous.fst
        | inr i => exact (show Continuous (fun _ : V ↦ (0:ℝ)) from continuous_const).congr (fun _ ↦ by simp [σ, elementaryCoverZeroHom, elementaryCover, fiberCoord])
      have hev (j : J) : ∀ᶠ v in 𝓝 u, |fiberCoord (σ v) j - fiberCoord (σ u) j| ≤ 1 :=
        ((Metric.tendsto_nhds.mp ((hc j).tendsto u)) 1 one_pos).mono fun _ h ↦ h.le
      filter_upwards [eventually_all.mpr hev] with v hv k
      have he : fiberCoord (z y v k) = fiberCoord (z y u k) + (fiberCoord (σ v) - fiberCoord (σ u)) := by
        dsimp only [z]
        rw [fiberCoord_add,fiberCoord_add]
        abel
      calc ‖F y s v k‖ ≤ C * fiberWeight (fiberCoord (z y v k)) := by simpa [F] using hCs (z y v k)
        _ ≤ C * (M * w k) := mul_le_mul_of_nonneg_left (he ▸ fiberWeight_shift _ _ hv) hC
        _ = _ := (mul_assoc ..).symm
  refine ⟨fun s y ↦ (hcalc y).1 s, fun dirs ↦ ?_⟩
  induction dirs using List.reverseRecOn with
  | nil => exact fun s ↦ ⟨s,fun _ _ ↦ rfl⟩
  | append_singleton l v ih =>
    intro s
    obtain ⟨t,ht⟩ := ih (D s v)
    refine ⟨t, fun y u ↦ ?_⟩
    change iteratedFDeriv ℝ _ (Ψ s y) u _ = Ψ t y u
    rw [iteratedFDeriv_append_singleton ((hcalc y).1 s), show (fun w ↦ fderiv ℝ (Ψ s y) w v) = Ψ (D s v) y
      from funext fun w ↦ (hcalc y).2 s w v]
    exact ht y u

end

-- TODO(paper-gap): The proof of D.1.7.1 cites Lemma D.1.6.18 for the elementary case,
-- but that lemma only averages over compact subgroups. The kernel below can be
-- noncompact, as for ℤ ⊂ ℝ, where the coset integral is a periodization.

omit hTop hT2 hLC in
/-- Paper: Lemma D.1.6.18 and Theorem D.1.7.1, pp. 772 and 776. On an elementary group,
the integral of a Schwartz function along the kernel of a continuous, open and surjective
homomorphism onto another elementary group exists on every coset, and is a Schwartz
function on the target.
Deviation: The kernel is any closed subgroup, not only a compact one. The target
presentation is arbitrary. -/
theorem elementary_fiberIntegral {A B : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A]
    [BorelSpace A] [CommGroup B] [TopologicalSpace B]
    (e : ElementaryLCAPresentation A) (e' : ElementaryLCAPresentation B)
    (p : A →* B) (hp : Continuous p) (hpo : IsOpenMap p) (hps : Function.Surjective p)
    (ν : Measure p.ker) [ν.IsHaarMeasure] (φ : SchwartzBruhatStage e) :
    (∀ y : A, Integrable (fun l : p.ker ↦ φ (Multiplicative.toAdd (e.equiv (y * l)))) ν) ∧
      ∃ ψ : SchwartzBruhatStage e', ∀ y : A,
        ψ (Multiplicative.toAdd (e'.equiv (p y))) =
          ∫ l : p.ker, φ (Multiplicative.toAdd (e.equiv (y * l))) ∂ν := by
  classical
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let E' := ElementaryLieGroup e'.realDim e'.torusDim e'.latticeRank e'.finiteFactor
  let V := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let V' := EuclideanSpace ℝ (Fin e'.realDim) × EuclideanSpace ℝ (Fin e'.torusDim)
  let π : E →+ E' := AddMonoidHom.toMultiplicative.symm
    ((e'.equiv.toMonoidHom.comp p).comp e.equiv.symm.toMonoidHom)
  have hc : Continuous π := e'.equiv.continuous.comp (hp.comp e.equiv.symm.continuous)
  have ho : IsOpenMap π := e'.equiv.isOpenMap.comp (hpo.comp e.equiv.symm.isOpenMap)
  have hker : IsClosed (p.ker : Set A) := by
    let : T2Space (Multiplicative E') := inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin e'.realDim) ×
      (Fin e'.torusDim → AddCircle (1:ℝ)) × (Fin e'.latticeRank → ℤ) × e'.finiteFactor))
    have : T2Space B := e'.equiv.toHomeomorph.isEmbedding.t2Space
    exact isClosed_singleton.preimage hp
  obtain ⟨M,hM⟩ := fiberIntegral_weight e p.ker hker ν
  let val (y : A) := (e.equiv y).toAdd
  let W (y : A) := fiberWeight (fiberCoord (val y))
  have hi (t : SchwartzBruhatStage e) (y : A) : Integrable (fun k : p.ker ↦ t (val (y*k.val))) ν := by
    obtain ⟨C,_,h⟩ := fiberIntegral_decay 1 t
    exact ((hM y).1.const_mul C).mono'
      (((elementarySchwartz_continuousFunction t).comp (e.equiv.continuous.comp
        (continuous_const.mul continuous_subtype_val))).aestronglyMeasurable)
      (.of_forall fun k ↦ by simpa [val] using h (val (y*k.val)))
  refine ⟨hi φ, ?_⟩
  let Aφ (y : A) := ∫ k : p.ker, φ (val (y*k.val)) ∂ν
  have hinv {y y' : A} (h : p y = p y') : Aφ y = Aφ y' := by
    let k₀ : p.ker := ⟨y'⁻¹*y, by change p (y'⁻¹*y) = 1; simp [h]⟩
    calc Aφ y = ∫ k : p.ker, φ (val (y' * (k₀ * k).val)) ∂ν := by
          apply integral_congr_ae
          exact .of_forall fun k ↦ congrArg (fun x ↦ φ (val x)) (by dsimp [k₀]; group)
      _ = Aφ y' := integral_mul_left_eq_self (fun k : p.ker ↦ φ (val (y' * k.val))) k₀
  let inv (b : E') := Function.surjInv hps (e'.equiv.symm (.ofAdd b))
  let f (b : E') := Aφ (inv b)
  have hf (y : A) : f (e'.equiv (p y)).toAdd = Aφ y := hinv (by
    change p (Function.surjInv hps _) = p y
    rw [Function.rightInverse_surjInv hps]
    exact e'.equiv.symm_apply_apply _)
  let q := elementaryCoverZeroHom (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  obtain ⟨L,hL⟩ := elementary_linear_section (π.comp q) (hc.comp elementaryCoverZeroHom_continuous_isOpenMap.1)
    (ho.comp elementaryCoverZeroHom_continuous_isOpenMap.2)
  let Y (y : A) (u : V') := y * e.equiv.symm (.ofAdd (q (L u)))
  let Ψ (t : SchwartzBruhatStage e) (y : A) (u : V') := ∫ k : p.ker, t (val (y*k.val) + q (L u)) ∂ν
  have hYk (y u) (k : p.ker) : val (Y y u * k.val) = val (y*k.val) + q (L u) := by
    dsimp only [Y,val]
    rw [mul_right_comm, map_mul, e.equiv.apply_symm_apply]
    rfl
  have hY (a b u) : (e'.equiv (p (Y (inv (elementaryCover 0 a b)) u))).toAdd = elementaryCover u a b := by
    let y := inv (elementaryCover 0 a b)
    have hpy : (e'.equiv (p y)).toAdd = elementaryCover 0 a b :=
      congrArg Multiplicative.toAdd ((congrArg e'.equiv (Function.rightInverse_surjInv hps _)).trans
        (e'.equiv.apply_symm_apply _))
    have hpu : (e'.equiv (p (e.equiv.symm (.ofAdd (q (L u)))))).toAdd = elementaryCover u 0 0 := hL u
    change (e'.equiv (p (y * _))).toAdd = _
    rw [map_mul, map_mul]
    change (e'.equiv (p y)).toAdd + _ = _
    rw [hpy,hpu,elementaryCover_add,zero_add,add_zero,add_zero]
  have hΨ (a b) : (fun u ↦ f (elementaryCover u a b)) = Ψ φ (inv (elementaryCover 0 a b)) := by
    funext u
    rw [← hY a b u, hf]
    apply integral_congr_ae
    exact .of_forall fun k ↦ congrArg φ.val (hYk _ _ k)
  obtain ⟨hcd,hdirs⟩ := fiberIntegral_charts e p.ker ν L (fun y ↦ (hM y).1)
  refine ⟨⟨f, fun a b ↦ hΨ a b ▸ hcd φ _, fun i ↦ ?_⟩,hf⟩
  let dirs : List V' := (List.ofFn fun j ↦ List.replicate (i.2.1 j) (EuclideanSpace.single j 1,0)).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
  obtain ⟨t,ht⟩ := hdirs dirs φ
  obtain ⟨P,hP⟩ := elementary_open_quotient_weight (⊤ : AddSubgroup E) isOpen_univ
    (π.comp (⊤ : AddSubgroup E).subtype) (hc.comp continuous_subtype_val) i.1 i.2.2.2
  obtain ⟨C,hC,hdec⟩ := fiberIntegral_decay P t
  refine lt_of_le_of_lt (b := ENNReal.ofReal (C*M)) (iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_)
    ENNReal.ofReal_lt_top
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  let y := inv (elementaryCover 0 a b)
  let y₁ := Y y u
  let wt : ℂ := (∏ j, (u.1 j : ℂ)^i.1 j) * ∏ j, (a j : ℂ)^i.2.2.2 j
  have hder : elementaryPartial f i.2.1 i.2.2.1 u a b = ∫ k : p.ker, t (val (y₁*k.val)) ∂ν := by
    change iteratedFDeriv ℝ dirs.length (fun w ↦ f (elementaryCover w a b)) u dirs.get = _
    rw [hΨ a b]
    refine (ht y u).trans ?_
    exact integral_congr_ae (.of_forall fun k ↦ congrArg t.val (hYk _ _ k).symm)
  have htarget (k : p.ker) : π (val (y₁ * k.val)) = elementaryCover u a b := by
    have hk : p k.val = 1 := k.property
    change (e'.equiv (p (e.equiv.symm (e.equiv (y₁ * k.val))))).toAdd = _
    rw [e.equiv.symm_apply_apply, map_mul, hk, mul_one]
    exact hY a b u
  have hpt (k : p.ker) : ‖wt * t (val (y₁*k.val))‖ ≤ C * W (y₁*k.val) := by
    let z := val (y₁*k.val)
    have h := hP (⟨z, AddSubgroup.mem_top _⟩ : (⊤ : AddSubgroup E))
    change MvPolynomial.eval _ P = (∏ j, ((π z).1 j : ℂ)^i.1 j) * ∏ j, ((π z).2.2.1 j : ℂ)^i.2.2.2 j at h
    rw [htarget k] at h
    have hh := hdec z
    change MvPolynomial.eval (Sum.elim (fun i ↦ (z.1 i : ℂ)) (fun j ↦ (z.2.2.1 j : ℂ))) P = wt at h
    rwa [h] at hh
  change ‖wt * elementaryPartial f _ _ u a b‖ ≤ C * M
  rw [hder, ← integral_const_mul]
  calc _ ≤ ∫ k : p.ker, ‖wt * t (val (y₁*k.val))‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ k : p.ker, C * W (y₁*k.val) ∂ν := integral_mono ((hi t y₁).const_mul wt).norm ((hM y₁).1.const_mul C) hpt
    _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (hM y₁).2 hC

end FibreIntegral

variable [MeasurableSpace G] [hBorel : BorelSpace G]

local instance sec1cDualMeasurableSpace : MeasurableSpace (PontryaginDual G) := borel _
local instance sec1cQuotientMeasurableSpace : MeasurableSpace (G ⧸ K) := borel _
local instance sec1cQuotientDualMeasurableSpace :
    MeasurableSpace (PontryaginDual (G ⧸ K)) := borel _

variable (μ : Measure G) [hHaar : μ.IsHaarMeasure] [hRegular : μ.Regular]

include hBorel hHaar hRegular

/-- Paper: Lemma D.1.6.19(1), p. 773. An invariant differential operator
preserves Schwartz–Bruhat functions, and on the Fourier side it acts by
multiplication by its symbol. Both integrals are defined on integrable functions. -/
theorem lcaFourier_bruhatDiff (D : bruhatDiffAlgebra G) (f : SchwartzBruhat G) :
    ∃ (hf : (f : G → ℂ) ∈ bruhatSmoothSubmodule)
      (g : SchwartzBruhat G), (g : G → ℂ) = (D.val ⟨f, hf⟩).val ∧
      Integrable (f : G → ℂ) μ ∧ Integrable (g : G → ℂ) μ ∧
      lcaFourier μ g = bruhatDiffSymbol D * lcaFourier μ f := by
  classical
  obtain ⟨B,hB⟩ := schwartzBruhat_fourier_linear μ
  have hb (z : SchwartzBruhat G) : Integrable z.val μ ∧ ∀ χ, B z χ = lcaFourier μ z χ :=
    ⟨SchwartzBruhat.integrable μ z, hB z⟩
  have hgen (L : Module.End ℂ (bruhatSmoothSubmodule (G := G))) (hL : L ∈ range (bruhatFirstOrder (G := G))) :
      ∃ c : PontryaginDual G → ℂ, (∀ χ, L (smoothCharacter χ) = c χ • smoothCharacter χ) ∧
        ∀ z : SchwartzBruhat G, ∃ y, smoothInclusion (G := G) y = L (smoothInclusion (G := G) z) ∧ ∀ χ, B y χ = c χ * B z χ := by
    obtain ⟨a,rfl⟩ := hL
    exact ⟨bruhatDiffSymbol (bruhatDiffGenerator a), generator_character a, generator_schwartz_lift μ B hb a⟩
  have hP := symbol_action_adjoin (smoothInclusion (G := G)) B smoothCharacter _ hgen (L := D.val) D.property
  obtain ⟨c,hc,hL⟩ := hP
  obtain ⟨g,hg,hF⟩ := hL f
  refine ⟨(smoothInclusion (G := G) f).property,g,congrArg Subtype.val hg,(hb f).1,(hb g).1,funext fun χ ↦ ?_⟩
  have hs : bruhatDiffSymbol D χ = c χ := by
    change (D.val (smoothCharacter χ)).val 1 = _
    rw [hc]
    change c χ * (χ 1 : ℂ) = c χ
    rw [map_one,Circle.coe_one,mul_one]
  change lcaFourier μ g χ = bruhatDiffSymbol D χ * lcaFourier μ f χ
  rw [hs]
  exact (hB g χ).symm.trans ((hF χ).trans (congrArg (c χ * ·) (hB f χ)))

section FourierTransform

omit hTop hT2 hLC hBorel hHaar hRegular

open Function
open scoped Pointwise

private theorem stageRealization_mul_kernel (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (x u : G) (hu : u ∈ OrderDual.ofDual a.val.2) :
    schwartzBruhatStageRealization a e s (x * u) = schwartzBruhatStageRealization a e s x := by
  have hu' := a.property.2.2.2 hu
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ a.val.1
  · rw [dite_eq_left (a.val.1.mul_mem hx hu'), dite_eq_left hx]
    let v : a.val.1 := ⟨u,hu'⟩
    have hv : v ∈ (OrderDual.ofDual a.val.2).comap a.val.1.subtype := hu
    exact congrArg (fun z : a.quotient ↦ s (e.equiv z).toAdd) (QuotientGroup.mk_mul_of_mem ⟨x,hx⟩ hv)
  · rw [dite_eq_right (fun h ↦ hx ((a.val.1.mul_mem_cancel_right hu').mp h)), dite_eq_right hx]

private theorem continuous_to_stage_of_realization {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) (B : E →ₗ[ℂ] SchwartzBruhatStage d)
    (h : ∀ x : G, ∃ L : E →L[ℂ] ℂ, ∀ s, L s = schwartzBruhatStageRealization b d (B s) x) :
    Continuous B := by
  apply continuous_toElementarySchwartz_of_eval
  intro y
  obtain ⟨q,hq⟩ := d.equiv.surjective (Multiplicative.ofAdd y)
  obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨L,hL⟩ := h x.val
  refine ⟨L,fun s ↦ ?_⟩
  exact (hL s).trans ((schwartzBruhatStageRealization_apply b d (B s) _).trans
    ((dite_eq_left x.property).trans (congrArg (fun t ↦ B s (Multiplicative.toAdd t)) hq)))

/-- Multiplication by a continuous real additive functional preserves elementary tests. -/
private theorem elementary_frequency_mul {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (ρ : ElementaryLieGroup m n r F →+ ℝ) (hρ : Continuous ρ) (s : ElementarySchwartz m n r F) :
    (fun x ↦ (ρ x : ℂ) * s x) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  let E := ElementaryLieGroup m n r F
  let V := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let q := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  let l := (ρ.comp q).toRealLinearMap (hρ.comp elementaryCoverZeroHom_continuous_isOpenMap.1)
  let R (u : V) (a : Fin r → ℤ) (b : F) : ℂ := ρ (elementaryCover u a b)
  have hR (u a b) : R u a b = (l u : ℂ) + (ρ (elementaryCover (0 : V) a b) : ℂ) := by
    change (ρ (elementaryCover u a b) : ℂ) = (ρ (elementaryCover u 0 0) : ℂ) + _
    rw [← Complex.ofReal_add, ← map_add, elementaryCover_add,add_zero,zero_add,zero_add]
  let L := Complex.ofRealCLM.comp l
  have hsm (a b) : ContDiff ℝ ∞ (fun u ↦ R u a b) := by
    simp_rw [hR]
    exact L.contDiff.add contDiff_const
  have hD (u a b v) : fderiv ℝ (fun w ↦ R w a b) u v = L v := by
    simp_rw [hR]
    exact congrArg (fun D : V →L[ℝ] ℂ ↦ D v) ((L.hasFDerivAt.add_const _).fderiv)
  let X (s t : ElementarySchwartz m n r F) (a : Fin r → ℤ) (b : F) (u : V) :=
    R u a b * s (elementaryCover u a b) + t (elementaryCover u a b)
  have hX (s t : ElementarySchwartz m n r F) (a b) : ContDiff ℝ ∞ (X s t a b) :=
    ((hsm a b).mul (s.property.1 a b)).add (t.property.1 a b)
  have hdir (s : ElementarySchwartz m n r F) (v : V) : ∃ t : ElementarySchwartz m n r F, ∀ u a b,
      fderiv ℝ (fun w ↦ s (elementaryCover w a b)) u v = t (elementaryCover u a b) := by
    obtain ⟨t,h⟩ := fiberIntegral_orbit_deriv (ContinuousLinearMap.id ℝ V) s v
    refine ⟨t,fun u a b ↦ ?_⟩
    simpa only [ContinuousLinearMap.id_apply,elementaryCover_add,zero_add,add_zero] using
      (h (elementaryCover 0 a b) u).2
  have hit (dirs : List V) (s t : ElementarySchwartz m n r F) : ∃ s' t' : ElementarySchwartz m n r F,
      ∀ a b u, iteratedFDeriv ℝ dirs.length (X s t a b) u dirs.get = X s' t' a b u := by
    induction dirs using List.reverseRecOn generalizing s t with
    | nil => exact ⟨s,t,fun a b u ↦ by simp⟩
    | append_singleton dirs v ih =>
      obtain ⟨s₁,hs⟩ := hdir s v
      obtain ⟨t₁,ht⟩ := hdir t v
      obtain ⟨s',t',h⟩ := ih s₁ (L v • s + t₁)
      refine ⟨s',t',fun a b u ↦ ?_⟩
      have he : (fun w ↦ fderiv ℝ (X s t a b) w v) = X s₁ (L v • s + t₁) a b := by
        funext w
        dsimp only [X]
        have h₁ := (hsm a b).differentiable (by simp) w
        have h₂ := (s.property.1 a b).differentiable (by simp) w
        have h₃ := (t.property.1 a b).differentiable (by simp) w
        have hm : DifferentiableAt ℝ (fun u ↦ R u a b * s (elementaryCover u a b)) w := h₁.mul h₂
        rw [fderiv_fun_add hm h₃, fderiv_fun_mul h₁ h₂]
        simp only [add_apply,smul_apply,hD,hs,ht,smul_eq_mul]
        change _ = _ + (L v * s _ + t₁ _)
        ring
      rw [iteratedFDeriv_append_singleton (hX s t a b),he,h]
  obtain ⟨P,hP⟩ := elementary_real_hom_polynomial ρ hρ
  refine ⟨fun a b ↦ (hsm a b).mul (s.property.1 a b),fun i ↦ ?_⟩
  let dirs : List V := (List.ofFn fun j ↦ List.replicate (i.2.1 j) (EuclideanSpace.single j 1,0)).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
  obtain ⟨s',t',h⟩ := hit dirs s 0
  let W : MvPolynomial (Fin m ⊕ Fin r) ℂ := (∏ j, MvPolynomial.X (Sum.inl j)^i.1 j) *
    ∏ j, MvPolynomial.X (Sum.inr j)^i.2.2.2 j
  obtain ⟨C,hC⟩ := polynomial_weight_bounded (W*P) s'
  obtain ⟨D,hD'⟩ := polynomial_weight_bounded W t'
  refine lt_of_le_of_lt (b := ENNReal.ofReal (C+D)) (iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) ENNReal.ofReal_lt_top
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  let x := elementaryCover u a b
  have he := h a b u
  have hzero : X s 0 a b = fun w ↦ R w a b * s (elementaryCover w a b) := by
    funext w
    exact add_zero _
  rw [hzero] at he
  change ‖_ * iteratedFDeriv ℝ dirs.length _ u dirs.get‖ ≤ _
  rw [he]
  have h₁ := hC x
  have h₂ := hD' x
  simp only [MvPolynomial.eval_mul,hP,W,map_prod,map_pow,MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr] at h₁ h₂
  dsimp only [X,R]
  rw [mul_add,←mul_assoc]
  exact (norm_add_le ..).trans (add_le_add h₁ h₂)

private theorem dualStagePairing {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (a : BruhatStructuralPair G) (b : BruhatStructuralPair (PontryaginDual G))
    (hJ : b.val.1 = lcaAnnihilator (OrderDual.ofDual a.val.2))
    (hK : OrderDual.ofDual b.val.2 = lcaAnnihilator a.val.1) :
    ∃ d : b.quotient →ₜ* PontryaginDual a.quotient, ∀ (χ : b.val.1) (x : a.val.1),
      d (QuotientGroup.mk χ) (QuotientGroup.mk x) = χ.val x.val := by
  let J := a.val.1
  let N := (OrderDual.ofDual a.val.2).comap J.subtype
  let M := (OrderDual.ofDual b.val.2).comap b.val.1.subtype
  let : LocallyCompactSpace J := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let ι : J →ₜ* G := ⟨J.subtype,continuous_subtype_val⟩
  let res := PontryaginDual.map ι
  let h (χ : b.val.1) : res χ.val ∈ lcaAnnihilator N := by
    have hχ : χ.val ∈ lcaAnnihilator (OrderDual.ofDual a.val.2) := hJ ▸ χ.property
    rw [mem_lcaAnnihilator_iff] at hχ
    exact (mem_lcaAnnihilator_iff _ _).mpr fun x ↦ hχ ⟨x.val.val,x.property⟩
  let toAnn : b.val.1 →ₜ* lcaAnnihilator N :=
    ⟨(res.toMonoidHom.comp b.val.1.subtype).codRestrict _ h,
      (res.continuous.comp continuous_subtype_val).subtype_mk h⟩
  obtain ⟨e,he⟩ := lcaQuotientDual_equiv_annihilator N (a.property.2.2.1.1.preimage continuous_subtype_val)
  let t : b.val.1 →ₜ* PontryaginDual a.quotient := (e.symm : _ →ₜ* _).comp toAnn
  have ht (χ : b.val.1) (x : J) : t χ (QuotientGroup.mk x) = χ.val x.val := by
    rw [←he]
    change (e (e.symm (toAnn χ))).val x = _
    rw [e.apply_symm_apply]
    rfl
  have hk : M ≤ t.toMonoidHom.ker := by
    intro χ hχ
    change χ.val ∈ OrderDual.ofDual b.val.2 at hχ
    rw [hK,mem_lcaAnnihilator_iff] at hχ
    apply PontryaginDual.ext
    intro z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N z
    exact (ht χ x).trans (hχ x)
  let d := QuotientGroup.lift M t.toMonoidHom hk
  have hd : Continuous d := (QuotientGroup.isQuotientMap_mk M).continuous_iff.mpr t.continuous
  exact ⟨⟨d,hd⟩,ht⟩

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

private theorem fourier_mul_frequency (ρ : PontryaginDual G →ₜ* Multiplicative ℝ)
    (f : SchwartzBruhat G) :
    ∃ g : SchwartzBruhat G, ∀ χ, lcaFourier μ g χ = ((ρ χ).toAdd : ℂ) * lcaFourier μ f χ := by
  obtain ⟨σ,_,_,hσ⟩ := bruhatDiffDegreeOne_frequency (G := G)
  let D := σ.symm ρ
  obtain ⟨a,ha⟩ := (mem_bruhatDiffDegreeOneReal_iff D.val).mp D.property
  let z : ℂ := 2 * ↑Real.pi * Complex.I
  have hz : z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hdir (χ) : bruhatDiffSymbol (bruhatDiffGenerator a) χ = z * ((ρ χ).toAdd : ℂ) :=
    bruhatDiffSymbol_generator a χ _ (fun t ↦ by simpa [D] using hσ a D ha χ t)
  obtain ⟨_,g,_,_,_,hg⟩ := lcaFourier_bruhatDiff μ (bruhatDiffGenerator a) f
  obtain ⟨B,hB⟩ := schwartzBruhat_fourier_linear μ
  refine ⟨z⁻¹ • g,fun χ ↦ ?_⟩
  rw [← hB, B.map_smul,Pi.smul_apply,smul_eq_mul,hB,congrFun hg χ,Pi.mul_apply,hdir]
  field_simp

private theorem fourier_mul_polynomial {ι : Type*} (ρ : ι → PontryaginDual G →ₜ* Multiplicative ℝ)
    (P : MvPolynomial ι ℂ) (f : SchwartzBruhat G) :
    ∃ g : SchwartzBruhat G, ∀ χ, lcaFourier μ g χ =
      MvPolynomial.eval (fun i ↦ ((ρ i χ).toAdd : ℂ)) P * lcaFourier μ f χ := by
  classical
  obtain ⟨B,hB⟩ := schwartzBruhat_fourier_linear μ
  induction P using MvPolynomial.induction_on with
  | C c =>
    exact ⟨c • f,fun χ ↦ by rw [MvPolynomial.eval_C,← hB,B.map_smul,Pi.smul_apply,smul_eq_mul,hB]⟩
  | add p q hp hq =>
    obtain ⟨g,hg⟩ := hp
    obtain ⟨k,hk⟩ := hq
    refine ⟨g+k,fun χ ↦ ?_⟩
    calc
      lcaFourier μ (g+k) χ = (B g + B k) χ :=
        (hB (g+k) χ).symm.trans (congrFun (B.map_add g k) χ)
      _ = _ + _ := congrArg₂ (· + ·) ((hB g χ).trans (hg χ)) ((hB k χ).trans (hk χ))
      _ = _ := by rw [MvPolynomial.eval_add,add_mul]
  | mul_X p i hp =>
    obtain ⟨g,hg⟩ := hp
    obtain ⟨k,hk⟩ := fourier_mul_frequency μ (ρ i) g
    refine ⟨k,fun χ ↦ (hk χ).trans ?_⟩
    rw [hg χ, MvPolynomial.eval_mul, MvPolynomial.eval_X, mul_left_comm, mul_assoc]

private theorem extend_real_character_open {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (J : Subgroup A) (hJ : IsOpen (J : Set A)) (ρ : J →ₜ* Multiplicative ℝ) :
    ∃ τ : A →ₜ* Multiplicative ℝ, ∀ x : J, τ x.val = ρ x := by
  obtain ⟨L,hL⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    J.subtype.toAdditive (show Function.Injective J.subtype.toAdditive from @Subtype.val_injective _ _) ρ.toMonoidHom.toAdditiveLeft
  let τ := L.toMultiplicativeRight
  have he (x : J) : τ x.val = ρ x := DFunLike.congr_fun hL (Additive.ofMul x)
  have hc : Continuous τ := by
    apply continuous_of_continuousAt_one τ
    have hn : Filter.map Subtype.val (𝓝 (1 : J)) = 𝓝 (1 : A) := hJ.isOpenEmbedding_subtypeVal.map_nhds_eq 1
    rw [ContinuousAt,map_one,← hn,tendsto_map'_iff]
    have ht : Tendsto ρ (𝓝 (1 : J)) (𝓝 1) := (show Continuous ρ from ρ.continuous).tendsto' 1 1 (map_one ρ)
    exact ht.congr (fun x ↦ (he x).symm)
  exact ⟨⟨τ,hc⟩,he⟩
private theorem frequency_of_dual_direction (a : LCATopologicalLie (PontryaginDual G)) :
    ∃ ρ : G →ₜ* Multiplicative ℝ, ∀ t : ℝ, ∀ x, a (.ofAdd t) x = Real.fourierChar ((ρ x).toAdd * t) := by
  let b := (pontryaginDual_bidual (G := G)).choose
  have hb := (pontryaginDual_bidual (G := G)).choose_spec
  obtain ⟨σ,_,_,hσ⟩ := bruhatDiffDegreeOne_frequency (G := PontryaginDual G)
  let D : bruhatDiffDegreeOneReal (G := PontryaginDual G) :=
    ⟨bruhatFirstOrder a,Submodule.subset_span ⟨a,rfl⟩⟩
  refine ⟨(σ D).comp (b : G →ₜ* _), fun t x ↦ ?_⟩
  exact (hb x (a (.ofAdd t))).symm.trans (hσ a D rfl (b x) t).symm

end
/-- In an affine family of characters every dual derivative is a Fourier integral of another
test on the same source stage. The new test is independent of the base character. -/
private theorem fourier_charts {A V X : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace X] [MeasurableSpace A] [BorelSpace A] (ν : Measure X) (q : X → A) (hq : Measurable q)
    (e : ElementaryLCAPresentation A) (α : Multiplicative V →ₜ* PontryaginDual A)
    (hi : ∀ s : SchwartzBruhatStage e, Integrable (fun k ↦ s (e.equiv (q k)).toAdd) ν) :
    let Ψ (s : SchwartzBruhatStage e) (χ : PontryaginDual A) (u : V) := ∫ k,
      s (e.equiv (q k)).toAdd * star ((χ * α (.ofAdd u)) (q k) : ℂ) ∂ν
    (∀ s χ, ContDiff ℝ ∞ (Ψ s χ)) ∧ ∀ (dirs : List V) (s : SchwartzBruhatStage e),
      ∃ t : SchwartzBruhatStage e, ∀ χ u, iteratedFDeriv ℝ dirs.length (Ψ s χ) u dirs.get = Ψ t χ u := by
  classical
  let c : ℂ := -(2 * ↑Real.pi * Complex.I)
  let F (χ : PontryaginDual A) (s : SchwartzBruhatStage e) (u : V) (k : X) :=
    s (e.equiv (q k)).toAdd * star ((χ * α (.ofAdd u)) (q k) : ℂ)
  let Ψ (s : SchwartzBruhatStage e) (χ : PontryaginDual A) (u : V) := ∫ k, F χ s u k ∂ν
  let line (v : V) := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let a (v : V) : LCATopologicalLie (PontryaginDual A) := α.comp
    ⟨AddMonoidHom.toMultiplicative (line v).toLinearMap.toAddMonoidHom,(line v).continuous⟩
  choose ρ hρ using fun v ↦ frequency_of_dual_direction (a v)
  have hmul (s : SchwartzBruhatStage e) (v : V) : ∃ t : SchwartzBruhatStage e, ∀ x : A,
      t (e.equiv x).toAdd = c * ((ρ v x).toAdd : ℂ) * s (e.equiv x).toAdd := by
    let L := (ρ v).comp (ContinuousMonoidHom.toContinuousMonoidHom e.equiv.symm)
    let r := AddMonoidHom.toMultiplicative.symm L.toMonoidHom
    let t : SchwartzBruhatStage e := ⟨_,elementary_frequency_mul r L.continuous s⟩
    refine ⟨c • t,fun x ↦ ?_⟩
    have he : r (e.equiv x).toAdd = (ρ v x).toAdd := congrArg (fun w ↦ (ρ v w).toAdd) (e.equiv.symm_apply_apply x)
    change c * ((r (e.equiv x).toAdd : ℂ) * _) = _
    rw [he,mul_assoc]
  choose D hD using hmul
  have hd (χ : PontryaginDual A) (s : SchwartzBruhatStage e) (u : V) (k : X) :
      DifferentiableAt ℝ (fun w ↦ F χ s w k) u := by
    let ψ : PontryaginDual (Multiplicative V) := (pontryaginDual_eval (q k)).comp α
    have hψ : ContDiff ℝ ∞ (fun w : V ↦ (ψ (.ofAdd w) : ℂ)) := contDiff_vector_character ψ
    exact (contDiff_const.mul (Complex.conjCLE.contDiff.comp ((contDiff_const (c := (χ (q k) : ℂ))).mul hψ))).differentiable (by simp) u
  have hcalc (χ : PontryaginDual A) : (∀ s, ContDiff ℝ ∞ (Ψ s χ)) ∧ ∀ s u v,
      fderiv ℝ (Ψ s χ) u v = Ψ (D s v) χ u := by
    refine integral_family_fderiv ν (F χ) ?_ (hd χ) D ?_ ?_
    · intro s u
      exact (hi s).aestronglyMeasurable.mul
        (((continuous_subtype_val.comp (χ * α (.ofAdd u)).continuous).star.measurable).comp hq).aestronglyMeasurable
    · intro s u k v
      let z := q k
      let r := (ρ v z).toAdd
      have he (t : ℝ) : F χ s (u + t • v) k = F χ s u k * (Real.fourierChar (-r*t) : ℂ) := by
        have hα : α (.ofAdd (u+t•v)) = α (.ofAdd u) * a v (.ofAdd t) := map_mul α _ _
        change _ * star ((χ * α (.ofAdd (u+t•v))) z : ℂ) = _
        rw [hα,←mul_assoc]
        change _ * star (((χ * α (.ofAdd u)) z * a v (.ofAdd t) z : Circle) : ℂ) = _
        rw [hρ,Circle.coe_mul,star_mul,neg_mul,Real.fourierChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
        simp only [F,r,z,Complex.star_def,mul_assoc]
        ring
      have hline : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
      have h := (hd χ s u k).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
      change HasDerivAt (fun t : ℝ ↦ F χ s (u+t•v) k) _ 0 at h
      rw [show (fun t : ℝ ↦ F χ s (u+t•v) k) = _ from funext he] at h
      have h' := ((Real.hasDerivAt_fourierChar (-r*0)).scomp 0 ((hasDerivAt_id (0:ℝ)).const_mul (-r))).const_mul (F χ s u k)
      rw [h.unique h']
      change _ = _ * star _
      rw [hD]
      simp only [F,mul_zero,AddChar.map_zero_eq_one,Circle.coe_one,mul_one,Complex.real_smul,Complex.ofReal_neg,r,c,z]
      ring
    · intro s u
      refine ⟨fun k ↦ ‖s (e.equiv (q k)).toAdd‖,(hi s).norm,.of_forall fun w k ↦ ?_⟩
      simp [F]
  refine ⟨fun s χ ↦ (hcalc χ).1 s, fun dirs ↦ ?_⟩
  induction dirs using List.reverseRecOn with
  | nil => exact fun s ↦ ⟨s,fun _ _ ↦ rfl⟩
  | append_singleton l v ih =>
    intro s
    obtain ⟨t,ht⟩ := ih (D s v)
    refine ⟨t,fun χ u ↦ ?_⟩
    change iteratedFDeriv ℝ _ (Ψ s χ) u _ = Ψ t χ u
    rw [iteratedFDeriv_append_singleton ((hcalc χ).1 s), show (fun w ↦ fderiv ℝ (Ψ s χ) w v) = Ψ (D s v) χ
      from funext fun w ↦ (hcalc χ).2 s w v]
    exact ht χ u

/-- Polynomial decay of the transforms of all tests on a stage bounds the mixed
partials of their transforms on the dual stage. -/
private theorem elementary_fourier_mem {A B X : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [CommGroup B] [TopologicalSpace B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace X] (ν : Measure X) (q : X → A) (hq : Measurable q)
    (e : ElementaryLCAPresentation A) (d : ElementaryLCAPresentation B) (p : B →ₜ* PontryaginDual A)
    (hi : ∀ s : SchwartzBruhatStage e, Integrable (fun k ↦ s (e.equiv (q k)).toAdd) ν) :
    let F (s : SchwartzBruhatStage e) (y : ElementaryLieGroup d.realDim d.torusDim d.latticeRank d.finiteFactor) :=
      ∫ k, s (e.equiv (q k)).toAdd * star (p (d.equiv.symm (.ofAdd y)) (q k) : ℂ) ∂ν
    (∀ (s : SchwartzBruhatStage e) (P : MvPolynomial (Fin d.realDim ⊕ Fin d.latticeRank) ℂ), ∃ M : ℝ, ∀ y,
      ‖MvPolynomial.eval (Sum.elim (fun j ↦ (y.1 j : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) P * F s y‖ ≤ M) →
      ∀ s, F s ∈ elementarySchwartzSubmodule d.realDim d.torusDim d.latticeRank d.finiteFactor := by
  intro F hbound s
  let V := EuclideanSpace ℝ (Fin d.realDim) × EuclideanSpace ℝ (Fin d.torusDim)
  let γ := elementaryCoverZeroHom (m := d.realDim) (n := d.torusDim) (r := d.latticeRank) (F := d.finiteFactor)
  let α : Multiplicative V →ₜ* PontryaginDual A := p.comp ((ContinuousMonoidHom.toContinuousMonoidHom d.equiv.symm).comp
    ⟨AddMonoidHom.toMultiplicative γ,elementaryCoverZeroHom_continuous_isOpenMap.1⟩)
  let χ (a : Fin d.latticeRank → ℤ) (b : d.finiteFactor) := p (d.equiv.symm (.ofAdd (elementaryCover (0:V) a b)))
  let Ψ (t : SchwartzBruhatStage e) (c : PontryaginDual A) (u : V) := ∫ k,
    t (e.equiv (q k)).toAdd * star ((c * α (.ofAdd u)) (q k) : ℂ) ∂ν
  have he (a b u) : χ a b * α (.ofAdd u) = p (d.equiv.symm (.ofAdd (elementaryCover u a b))) := by
    change p (d.equiv.symm (.ofAdd (elementaryCover (0:V) a b))) * p (d.equiv.symm (.ofAdd (elementaryCover u 0 0))) = _
    rw [←map_mul,←map_mul]
    congr 2
    change Multiplicative.ofAdd (elementaryCover (0:V) a b + elementaryCover u 0 0) = _
    rw [elementaryCover_add,zero_add,add_zero,add_zero]
  have hF (t : SchwartzBruhatStage e) (a b u) : F t (elementaryCover u a b) = Ψ t (χ a b) u := by simp only [Ψ,he,F]
  obtain ⟨hsm,hder⟩ := fourier_charts ν q hq e α hi
  refine ⟨fun a b ↦ by simp_rw [hF]; exact hsm s _,fun i ↦ ?_⟩
  let dirs : List V := (List.ofFn fun j ↦ List.replicate (i.2.1 j) (EuclideanSpace.single j 1,0)).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
  obtain ⟨t,ht⟩ := hder dirs s
  let W : MvPolynomial (Fin d.realDim ⊕ Fin d.latticeRank) ℂ :=
    (∏ j, MvPolynomial.X (Sum.inl j)^i.1 j) * ∏ j, MvPolynomial.X (Sum.inr j)^i.2.2.2 j
  obtain ⟨M,hM⟩ := hbound t W
  refine lt_of_le_of_lt (b := ENNReal.ofReal M) (iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) ENNReal.ofReal_lt_top
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  change ‖_ * iteratedFDeriv ℝ dirs.length (fun w ↦ F s (elementaryCover w a b)) u dirs.get‖ ≤ M
  simp_rw [hF]
  rw [ht (χ a b)]
  change ‖_ * Ψ t (χ a b) u‖ ≤ M
  rw [←hF]
  simpa only [W,MvPolynomial.eval_mul,map_prod,map_pow,MvPolynomial.eval_X,Sum.elim_inl,Sum.elim_inr,elementaryCover]
    using hM (elementaryCover u a b)

/-- A linear map of functions that has continuous Schwartz lifts on every source stage
has a continuous lift to the full Schwartz–Bruhat spaces. -/
private theorem schwartzBruhat_lift_stages {G H : Type*} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (T : SchwartzBruhat G →ₗ[ℂ] (H → ℂ)) (h : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      ∃ B : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat H, ∀ s, (B s).val = T (schwartzBruhatStageInclusion a e s)) :
    ∃ L : SchwartzBruhat G →L[ℂ] SchwartzBruhat H, ∀ s, (L s).val = T s := by
  have hmem (f : SchwartzBruhat G) : T f ∈ schwartzBruhatSubmodule H := by
    obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
    let B := (h a e).choose
    have hB := (h a e).choose_spec
    have he : schwartzBruhatStageInclusion a e s = f := Subtype.ext hs
    rw [←he,← hB s]
    exact (B s).property
  let L : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat H := T.codRestrict _ hmem
  have hc : Continuous L := by
    apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp L fun p ↦ ?_
    let P : SeminormFamily ℂ (SchwartzBruhat G) {q : Seminorm ℂ (schwartzBruhatSubmodule G) //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
    have hP : WithSeminorms P := ⟨rfl⟩
    refine hP.continuous_seminorm ⟨p.val.comp L,?_⟩
    intro a e
    let B := (h a e).choose
    have hB := (h a e).choose_spec
    have he (s : SchwartzBruhatStage e) : B s = L (schwartzBruhatStageInclusion a e s) := Subtype.ext (hB s)
    exact (((withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm p).comp B.continuous).congr
      fun s ↦ congrArg (fun x ↦ p.val x) (he s)
  exact ⟨⟨L,hc⟩,fun _ ↦ rfl⟩

section FourierStages

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

private theorem fourierStage_weight (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (b : BruhatStructuralPair (PontryaginDual G))
    (d : ElementaryLCAPresentation b.quotient)
    (F : SchwartzBruhatStage e → ElementaryLieGroup d.realDim d.torusDim d.latticeRank d.finiteFactor → ℂ)
    (hf : ∀ (s : SchwartzBruhatStage e) (χ : b.val.1), F s (d.equiv (QuotientGroup.mk χ)).toAdd =
      lcaFourier μ (schwartzBruhatStageRealization a e s) χ.val) (s : SchwartzBruhatStage e)
    (P : MvPolynomial (Fin d.realDim ⊕ Fin d.latticeRank) ℂ) : ∃ M : ℝ, ∀ y,
      ‖MvPolynomial.eval (Sum.elim (fun j ↦ (y.1 j : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) P * F s y‖ ≤ M := by
  let ζ := Sum.elim (coordinateRealHom d) (coordinateLatticeHom d)
  let qb : b.val.1 →ₜ* b.quotient := ⟨QuotientGroup.mk' _,QuotientGroup.continuous_mk⟩
  choose γ hγ using fun i ↦ extend_real_character_open b.val.1 b.property.1 ((ζ i).comp qb)
  obtain ⟨g,hg⟩ := fourier_mul_polynomial μ γ P (schwartzBruhatStageInclusion a e s)
  refine ⟨∫ x, ‖g x‖ ∂μ,fun y ↦ ?_⟩
  obtain ⟨χ,hχ⟩ := QuotientGroup.mk'_surjective ((OrderDual.ofDual b.val.2).comap b.val.1.subtype)
    (d.equiv.symm (.ofAdd y))
  have hy : d.equiv (qb χ) = .ofAdd y := hχ ▸ d.equiv.apply_symm_apply _
  have hcoords : (fun i ↦ ((γ i χ.val).toAdd : ℂ)) =
      Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun i ↦ (y.2.2.1 i : ℂ)) := by
    funext i
    rw [hγ]
    cases i with
    | inl i =>
      change (((d.equiv (qb χ)).toAdd.1 i : ℝ) : ℂ) = _
      rw [hy]; rfl
    | inr i =>
      change ((((d.equiv (qb χ)).toAdd.2.2.1 i : ℤ) : ℝ) : ℂ) = _
      rw [hy]; simp
  have he : F s y = lcaFourier μ (schwartzBruhatStageRealization a e s) χ.val :=
    (congrArg (fun z ↦ F s (Multiplicative.toAdd z)) hy).symm.trans (hf s χ)
  have hg' := hg χ.val
  rw [hcoords] at hg'
  change ‖_ * F s y‖ ≤ _
  rw [he]
  exact (congrArg norm hg'.symm).le.trans (norm_lcaFourier_le_integral_norm μ g χ.val)

private theorem fourierStage_coordinates (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (b : BruhatStructuralPair (PontryaginDual G))
    (d : ElementaryLCAPresentation b.quotient) (p : b.quotient →ₜ* PontryaginDual a.quotient)
    (hp : ∀ (χ : b.val.1) (x : a.val.1), p (QuotientGroup.mk χ) (QuotientGroup.mk x) = χ.val x.val) :
    let J := a.val.1
    let q : J →* a.quotient := QuotientGroup.mk' _
    let F (s : SchwartzBruhatStage e) (y : ElementaryLieGroup d.realDim d.torusDim d.latticeRank d.finiteFactor) :=
      ∫ x : J, s (e.equiv (q x)).toAdd * star (p (d.equiv.symm (.ofAdd y)) (q x) : ℂ) ∂μ.comap J.subtype
    (∀ s (χ : b.val.1), F s (d.equiv (QuotientGroup.mk χ)).toAdd =
      lcaFourier μ (schwartzBruhatStageRealization a e s) χ.val) ∧
      ∀ s, F s ∈ elementarySchwartzSubmodule d.realDim d.torusDim d.latticeRank d.finiteFactor := by
  intro J q F
  let : LocallyCompactSpace J := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.mpr (a.property.2.2.1.1.preimage continuous_subtype_val)
  let : MeasurableSpace a.quotient := borel _
  let : BorelSpace a.quotient := ⟨rfl⟩
  let ν := μ.comap J.subtype
  have hJ : IsOpen (J : Set G) := a.property.1
  have hon (s : SchwartzBruhatStage e) (x : J) :
      schwartzBruhatStageRealization a e s x.val = s (e.equiv (q x)).toAdd :=
    (schwartzBruhatStageRealization_apply a e s _).trans (dite_eq_left x.property)
  have hoff (s : SchwartzBruhatStage e) {x : G} (hx : x ∉ J) : schwartzBruhatStageRealization a e s x = 0 :=
    (schwartzBruhatStageRealization_apply a e s _).trans (dite_eq_right hx)
  have hi (s : SchwartzBruhatStage e) : Integrable (fun x : J ↦ s (e.equiv (q x)).toAdd) ν :=
    ((integrableOn_iff_comap_subtypeVal hJ.measurableSet).mp (schwartzBruhatStage_integrable μ a e s).integrableOn).congr
      (.of_forall (hon s))
  have hf (s : SchwartzBruhatStage e) (χ : b.val.1) : F s (d.equiv (QuotientGroup.mk χ)).toAdd =
      lcaFourier μ (schwartzBruhatStageRealization a e s) χ.val := by
    let g (x : G) := schwartzBruhatStageRealization a e s x * star (χ.val x : ℂ)
    calc _ = ∫ x : J, g x.val ∂ν := by
           apply integral_congr_ae
           refine .of_forall fun x ↦ ?_
           change _ * star (p (d.equiv.symm (d.equiv (QuotientGroup.mk χ))) (q x) : ℂ) = _ * _
           rw [d.equiv.symm_apply_apply, ←hon]
           exact congrArg (fun z : Circle ↦ _ * star (z : ℂ)) (hp χ x)
         _ = ∫ x in J, g x ∂μ := integral_subtype_comap hJ.measurableSet g
         _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [g,hoff s hx]
  refine ⟨hf, elementary_fourier_mem ν q QuotientGroup.continuous_mk.measurable e d p hi ?_⟩
  exact fourierStage_weight μ a e b d F hf

private def linearMapOfInjectiveRealization {E U V : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {f : U →ₗ[ℂ] V} (hf : Injective f) (T : E →ₗ[ℂ] V) (t : E → U) (ht : ∀ x, f (t x) = T x) : E →ₗ[ℂ] U where
  toFun := t
  map_add' x y := hf (by rw [ht,map_add,map_add,ht,ht])
  map_smul' c x := hf (by rw [ht,map_smul,map_smul,ht]; rfl)

private theorem fourierStage_realizes (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    ∀ (b : BruhatStructuralPair (PontryaginDual G)) (d : ElementaryLCAPresentation b.quotient),
      b.val.1 = lcaAnnihilator (OrderDual.ofDual a.val.2) → OrderDual.ofDual b.val.2 = lcaAnnihilator a.val.1 → ∃ B : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhatStage d,
      ∀ s, schwartzBruhatStageRealization b d (B s) = lcaFourier μ (schwartzBruhatStageRealization a e s) := by
  intro b d hJ hK
  let p := (dualStagePairing a b hJ hK).choose
  have hp := (dualStagePairing a b hJ hK).choose_spec
  have hf := (fourierStage_coordinates μ a e b d p hp).1
  have hm := (fourierStage_coordinates μ a e b d p hp).2
  let t (s : SchwartzBruhatStage e) : SchwartzBruhatStage d := ⟨_,hm s⟩
  have hval (s : SchwartzBruhatStage e) : schwartzBruhatStageRealization b d (t s) =
      lcaFourier μ (schwartzBruhatStageRealization a e s) := by
    funext χ
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with h
    · exact hf s ⟨χ,h⟩
    · have hχ : χ ∉ lcaAnnihilator (OrderDual.ofDual a.val.2) := hJ ▸ h
      obtain ⟨k,hk⟩ := not_forall.mp (mt (mem_lcaAnnihilator_iff _ χ).mpr hχ)
      let g := schwartzBruhatStageRealization a e s
      have htr := lcaFourier_translate μ g k.val χ
      have hfun : (fun x ↦ g (k.val * x)) = g := funext fun x ↦ by
        rw [mul_comm]
        exact stageRealization_mul_kernel a e s x k.val k.property
      rw [hfun] at htr
      by_contra hn
      exact hk (Circle.ext ((mul_eq_right₀ (Ne.symm hn)).mp htr.symm))
  let L := (schwartzBruhat_fourier_linear μ).choose
  have hL := (schwartzBruhat_fourier_linear μ).choose_spec
  let T := L.comp (schwartzBruhatStageInclusion a e)
  have he (s : SchwartzBruhatStage e) : schwartzBruhatStageRealization b d (t s) = T s :=
    (hval s).trans (funext fun χ ↦ (hL (schwartzBruhatStageInclusion a e s) χ).symm)
  have hi : Function.Injective (schwartzBruhatStageRealization b d) := fun _ _ h ↦
    schwartzBruhatStageInclusion_injective b d (Subtype.ext h)
  let B := linearMapOfInjectiveRealization (f := schwartzBruhatStageRealization b d) hi T t he
  exact ⟨B,hval⟩

private theorem fourierStage_eval (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (χ : PontryaginDual G) : ∃ f : SchwartzBruhatStage e →L[ℂ] ℂ,
      ∀ s, f s = lcaFourier μ (schwartzBruhatStageRealization a e s) χ := by
  let X := SchwartzBruhatStage e
  let : TopologicalSpace.MetrizableSpace X := elementarySchwartz_isFrechet.choose_spec.2.1
  let : BarrelledSpace ℂ X := elementarySchwartz_barrelled
  let C : X →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun s x ↦ schwartzBruhatStageRealization a e s x * star (χ x : ℂ)
      map_add' := fun s t ↦ funext fun x ↦ by simp only [map_add, Pi.add_apply,add_mul]
      map_smul' := fun c s ↦ funext fun x ↦ by simp only [map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc] }
  exact exists_integralCLM_of_pointwise_continuous μ C (fun x ↦ (continuous_schwartzBruhatStage_eval a e x).mul_const _)
    (fun s ↦ integrable_fourierIntegrand μ (schwartzBruhatStage_integrable μ a e s) χ)

private theorem fourierStage_clm (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    ∃ B : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat (PontryaginDual G), ∀ s,
      (B s).val = lcaFourier μ (schwartzBruhatStageRealization a e s) := by
  let b := a.dual.choose
  let d := b.elementary.some
  have h := fourierStage_realizes μ a e b d a.dual.choose_spec.1 a.dual.choose_spec.2
  let B := h.choose
  have hval (s) : schwartzBruhatStageRealization b d (B s) = lcaFourier μ (schwartzBruhatStageRealization a e s) := h.choose_spec s
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := elementarySchwartz_barrelled
  have hc : Continuous B := by
    refine continuous_to_stage_of_realization b d B fun χ ↦ ?_
    let h := fourierStage_eval μ a e χ
    exact ⟨h.choose,fun s ↦ (h.choose_spec s).trans (congrFun (hval s) χ).symm⟩
  exact ⟨(schwartzBruhatStageCLM b d).comp ⟨B,hc⟩,hval⟩

private theorem fourierSchwartzCLM :
    ∃ L : SchwartzBruhat G →L[ℂ] SchwartzBruhat (PontryaginDual G), ∀ s, (L s).val = lcaFourier μ s := by
  let T := (schwartzBruhat_fourier_linear μ).choose
  have hT := (schwartzBruhat_fourier_linear μ).choose_spec
  have h := schwartzBruhat_lift_stages T (fun a e ↦ by
    let h := fourierStage_clm μ a e
    exact ⟨h.choose,fun s ↦ (h.choose_spec s).trans (funext (hT (schwartzBruhatStageInclusion a e s))).symm⟩)
  exact ⟨h.choose,fun s ↦ (h.choose_spec s).trans (funext (hT s))⟩

end FourierStages

end FourierTransform

/-- Paper: Lemma D.1.6.19(2), p. 773. The Fourier integral maps Schwartz–Bruhat functions
on `G` to Schwartz–Bruhat functions on the dual, by a continuous linear map.
This is the first assertion of part (2); the isomorphism property is deduced from it below. -/
theorem schwartzBruhat_fourier_continuousLinear :
    ∃ T : SchwartzBruhat G →L[ℂ] SchwartzBruhat (PontryaginDual G),
      ∀ (f : SchwartzBruhat G) χ, T f χ = lcaFourier μ f χ := by
  let T := (fourierSchwartzCLM μ).choose
  have hT := (fourierSchwartzCLM μ).choose_spec
  refine ⟨T, fun f χ ↦ ?_⟩
  change (T f).val χ = lcaFourier μ f χ
  exact congrFun (hT f) χ

/-- Once Fourier transforms of Schwartz–Bruhat functions are known to be Schwartz–Bruhat,
they are integrable, so Plancherel inversion holds pointwise. -/
private theorem schwartzBruhat_fourier_inversion (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) (g : SchwartzBruhat G) (x : G) :
    g x = ∫ χ : PontryaginDual G, lcaFourier μ g χ * (χ x : ℂ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨A, hA⟩ := schwartzBruhat_fourier_continuousLinear μ
  have hg := SchwartzBruhat.integrable μ g
  have hu : Integrable (lcaFourier μ g) ν :=
    (SchwartzBruhat.integrable ν (A g)).congr (.of_forall (hA g))
  obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous g
  have hg₂ : MemLp (g : G → ℂ) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
    simpa only [sq] using hg.norm.mul_bdd (c := ‖b‖) hg.norm.aestronglyMeasurable
      (.of_forall fun y ↦ by simpa only [Real.norm_of_nonneg (norm_nonneg _), ← hb] using b.norm_coe_le_norm y)
  have hv := (lcaFourier_unitary μ ν hν).exists.choose_spec (g : G → ℂ) hg hg₂
  obtain ⟨F,hF,hFx⟩ := lcaInverseFourier_zeroAtInfty μ ν hν _ _ hu hv
  have heq : (F : G → ℂ) = b :=
    Measure.eq_of_ae_eq ((hF.trans hg₂.coeFn_toLp).trans (.of_forall fun y ↦ (hb y).symm)) F.continuous b.continuous
  exact (hb x).symm.trans ((congrFun heq x).symm.trans (hFx x))

/-- The inverse Fourier integral `g ↦ (x ↦ ∫ g χ · χ x dν)` maps Schwartz–Bruhat functions
on the dual continuously to Schwartz–Bruhat functions on `G`: it is the Fourier transform on
the dual followed by transport along `x ↦ (evaluation at x⁻¹)` to the double dual. -/
private theorem exists_schwartzBruhat_inverseFourier (ν : Measure (PontryaginDual G))
    [ν.IsHaarMeasure] [ν.Regular] :
    ∃ S : SchwartzBruhat (PontryaginDual G) →L[ℂ] SchwartzBruhat G,
      Function.Injective S ∧ ∀ g x, S g x = ∫ χ : PontryaginDual G, g χ * (χ x : ℂ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hb₀ := pontryaginDual_bidual (G := G)
  let b := hb₀.choose
  have hb := hb₀.choose_spec
  let c : G ≃ₜ* PontryaginDual (PontryaginDual G) :=
    { toMulEquiv := (MulEquiv.inv G).trans b.toMulEquiv
      continuous_toFun := b.continuous.comp continuous_inv
      continuous_invFun := continuous_inv.comp b.symm.continuous }
  have hc (x : G) (χ : PontryaginDual G) : c x χ = (χ x)⁻¹ := by
    change b x⁻¹ χ = _
    rw [hb, map_inv]
  have hT'₀ := schwartzBruhat_fourier_continuousLinear ν
  let T' := hT'₀.choose
  have hT' := hT'₀.choose_spec
  have hR₀ := schwartzBruhat_fourierTransport c.symm
  let R := hR₀.choose
  have hR := hR₀.choose_spec
  refine ⟨R.comp T', ?_, fun g x ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 (ξ : PontryaginDual (PontryaginDual G)) : lcaFourier ν g ξ = 0 := by
      obtain ⟨x, rfl⟩ := c.surjective ξ
      refine (hT' g (c x)).symm.trans ?_
      exact (hR (T' g) x).symm.trans (congrArg (fun h : SchwartzBruhat G ↦ h x) hg)
    have hae := ae_eq_zero_of_lcaFourier_eq_zero ν (SchwartzBruhat.integrable ν g) h0
    obtain ⟨u, hu⟩ := schwartzBruhat_boundedContinuous g
    have hu0 : (u : PontryaginDual G → ℂ) = 0 :=
      Measure.eq_of_ae_eq (hae.mono fun ξ h ↦ (hu ξ).trans h) u.continuous continuous_const
    apply Subtype.ext
    funext ξ
    exact (hu ξ).symm.trans (congrFun hu0 ξ)
  refine (hR (T' g) x).trans ((hT' g _).trans ?_)
  refine integral_congr_ae (.of_forall fun χ ↦ ?_)
  change g χ * star ((c x χ : Circle) : ℂ) = g χ * (χ x : ℂ)
  rw [hc, Circle.coe_inv_eq_conj, Complex.star_def, Complex.conj_conj]

/-- Paper: Lemma D.1.6.19(2), p. 773. The Fourier integral gives a continuous
linear isomorphism of the two Schwartz–Bruhat spaces. -/
theorem schwartzBruhat_fourier_equiv :
    ∃ F : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat (PontryaginDual G),
      ∀ f : SchwartzBruhat G, Integrable (f : G → ℂ) μ ∧
        ∀ χ, F f χ = lcaFourier μ f χ := by
  have hν₀ := lcaPlancherelMeasure_existsUnique μ
  let ν := hν₀.exists.choose
  have hν : IsLCAPlancherelMeasure μ ν := hν₀.exists.choose_spec
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  have hT₀ := schwartzBruhat_fourier_continuousLinear μ
  let T := hT₀.choose
  have hT := hT₀.choose_spec
  have hS₀ := exists_schwartzBruhat_inverseFourier μ ν
  let S := hS₀.choose
  have hSinj := hS₀.choose_spec.1
  have hS := hS₀.choose_spec.2
  have hST (f : SchwartzBruhat G) : S (T f) = f := by
    apply Subtype.ext
    funext x
    refine (hS (T f) x).trans (Eq.trans ?_ (schwartzBruhat_fourier_inversion μ ν hν f x).symm)
    refine integral_congr_ae (.of_forall fun χ ↦ ?_)
    exact congrArg (· * (χ x : ℂ)) (hT f χ)
  exact ⟨ContinuousLinearEquiv.equivOfInverse T S hST (fun g ↦ hSinj (hST (S g))),
    fun f ↦ ⟨SchwartzBruhat.integrable μ f, fun χ ↦ hT f χ⟩⟩

/-- Both Schwartz functions and their transforms are integrable, so Plancherel inversion holds pointwise. -/
private theorem schwartzBruhat_inverse_integral (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν)
    (g : SchwartzBruhat G) (x : G) :
    Integrable (fun χ : PontryaginDual G ↦ lcaFourier μ g χ * (χ x : ℂ)) ν ∧
      g x = ∫ χ : PontryaginDual G, lcaFourier μ g χ * (χ x : ℂ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨A, hA⟩ := schwartzBruhat_fourier_equiv μ
  have hg := SchwartzBruhat.integrable μ g
  have hu : Integrable (lcaFourier μ g) ν :=
    (SchwartzBruhat.integrable ν (A g)).congr (.of_forall (hA g).2)
  have hm : Continuous (fun χ : PontryaginDual G ↦ (χ x : ℂ)) :=
    continuous_subtype_val.comp (pontryaginDual_eval (G := G) x).continuous
  refine ⟨hu.mul_bdd (c := 1) hm.aestronglyMeasurable (.of_forall fun χ ↦ (Circle.norm_coe (χ x)).le), ?_⟩
  obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous g
  have hg₂ : MemLp (g : G → ℂ) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
    simpa only [sq] using hg.norm.mul_bdd (c := ‖b‖) hg.norm.aestronglyMeasurable
      (.of_forall fun y ↦ by simpa only [Real.norm_of_nonneg (norm_nonneg _), ← hb] using b.norm_coe_le_norm y)
  have hv := (lcaFourier_unitary μ ν hν).exists.choose_spec (g : G → ℂ) hg hg₂
  obtain ⟨F,hF,hFx⟩ := lcaInverseFourier_zeroAtInfty μ ν hν _ _ hu hv
  have heq : (F : G → ℂ) = b :=
    Measure.eq_of_ae_eq ((hF.trans hg₂.coeFn_toLp).trans (.of_forall fun y ↦ (hb y).symm)) F.continuous b.continuous
  exact (hb x).symm.trans ((congrFun heq x).symm.trans (hFx x))

-- TODO(paper-gap): (D.1.6.25) has different domains on its two sides. Its right side
-- is an inverse transform on G, whereas the left side is a Fourier transform on the dual.
-- The direction of the Fourier transform on the right in (D.1.6.26) is also reversed.
-- The footnotes on pp. 771, 773 and 775 leave the measure comparison to be checked.

/-- Paper: Lemma D.1.6.19(3), p. 773. Normalized structural averaging and
extension by zero intertwine with Fourier transform at the dual structural pair.
Deviation: This is the projector identity described after (D.1.6.26), with the
forward transform on both paths and both compact averages taken with mass one.
The ill-typed inverse-transform formula (D.1.6.25) is left open. -/
theorem lcaFourier_structural_projectors (a : BruhatStructuralPair G)
    (μK : Measure ↥(OrderDual.ofDual a.val.2))
    [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (νJ : Measure (lcaAnnihilator a.val.1))
    [νJ.IsHaarMeasure] [IsProbabilityMeasure νJ]
    (f : SchwartzBruhat G) :
    let avg := (a.val.1 : Set G).indicator
      (fun x ↦ ∫ k : ↥(OrderDual.ofDual a.val.2), f (x * k.val) ∂μK)
    Integrable (f : G → ℂ) μ ∧ Integrable avg μ ∧
      (∀ x : G, Integrable (fun k : ↥(OrderDual.ofDual a.val.2) ↦ f (x * k.val)) μK) ∧
      (∀ χ : PontryaginDual G,
        Integrable (fun ψ : lcaAnnihilator a.val.1 ↦ lcaFourier μ f (χ * ψ.val)) νJ) ∧
      lcaFourier μ avg =
        (lcaAnnihilator (OrderDual.ofDual a.val.2) : Set (PontryaginDual G)).indicator
          (fun χ ↦ ∫ ψ : lcaAnnihilator a.val.1, lcaFourier μ f (χ * ψ.val) ∂νJ) := by
  classical
  intro avg
  let J := a.val.1
  let K := OrderDual.ofDual a.val.2
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hK := isCompact_of_bruhatGoodSubgroup K a.property.2.2.1
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (lcaAnnihilator J) := isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator _ a.property.1)
  have hf := SchwartzBruhat.integrable μ f
  let e := Classical.choice a.elementary
  obtain ⟨R,_,hR⟩ := schwartzBruhatStage_average_retraction a e
  let g : SchwartzBruhat G := schwartzBruhatStageInclusion a e (R f)
  have hg : g.val = avg := funext fun x ↦
    (hR f x).trans (schwartzBruhatStageAverage_normalized a hK μK f x)
  have hav : Integrable avg μ := hg ▸ SchwartzBruhat.integrable μ g
  refine ⟨hf,hav,?_,?_,?_⟩
  · intro x
    obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous f
    exact ((b.continuous.comp (continuous_const.mul continuous_subtype_val)).congr
      fun k : K ↦ hb (x * k.val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro χ
    obtain ⟨F,hF⟩ := lcaFourier_zeroAtInfty μ hf
    exact ((F.continuous.comp (continuous_const.mul continuous_subtype_val)).congr
      fun ψ : lcaAnnihilator J ↦ hF (χ * ψ.val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · let c := (J : Set G).indicator f.val
    have hcut (x : G) : avg x = ∫ k : K, c (x * k.val) ∂μK := by
      by_cases hx : x ∈ J
      · have hc (k : K) : c (x * k.val) = f (x * k.val) := indicator_of_mem
          (J.mul_mem hx (a.property.2.2.2 k.property)) _
        simp only [hc]
        exact indicator_of_mem hx _
      · have hc (k : K) : c (x * k.val) = 0 := indicator_of_notMem
          (fun hm ↦ hx ((J.mul_mem_cancel_right (a.property.2.2.2 k.property)).mp hm)) _
        change (J : Set G).indicator _ x = _
        rw [indicator_of_notMem hx]
        simp only [hc]
        exact (integral_const (μ := μK) (0 : ℂ)).trans (smul_zero _) |>.symm
    funext χ
    refine (lcaFourier_compact_average μ K hK μK (hf.indicator a.property.1.measurableSet) hav hcut χ).trans ?_
    exact congrArg (fun u : PontryaginDual G → ℂ ↦ (lcaAnnihilator K : Set (PontryaginDual G)).indicator u χ)
      (funext (lcaFourier_cutoff μ J a.property.1 νJ hf))

omit hHaar hRegular
variable (μK : Measure K) [hHaarK : μK.IsHaarMeasure] [hRegularK : μK.Regular]
variable (hK : IsClosed (K : Set G))

include hK hHaarK hRegularK

-- TODO(paper-gap): The proof of D.1.7.1 uses properness of G → G/k and
-- openness of k. For k = ℤ in G = ℝ both assertions fail.

open Classical in
/-- Paper: Theorem D.1.7.1, p. 776. Let `π` be the quotient of an open subgroup `H` by a
compact subgroup, and `L` the image of `K ∩ H` under it. For a suitable Haar measure on `L`,
integrating a function on `H`, extended by zero, over a coset of `K` through a point of `H`
is the same as integrating its descent over the matching coset of `L`. -/
theorem exists_haar_fiberIntegral_eq {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A]
    [BorelSpace A] (H : Subgroup G) (hH : IsOpen (H : Set G)) (π : H →* A) (hπ : Continuous π)
    (hπo : IsOpenMap π) (hπs : Function.Surjective π) (hπk : IsCompact (π.ker : Set H))
    (L : Subgroup A) (hL : L = (K.comap H.subtype).map π) :
    ∃ ν : Measure L, ν.IsHaarMeasure ∧ ∀ g : A → ℂ, Continuous g → ∀ h : H,
      (Integrable (fun k : K ↦ if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0) μK ↔
        Integrable (fun l : L ↦ g (π h * l)) ν) ∧
      ∫ k : K, (if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0) ∂μK =
        ∫ l : L, g (π h * l) ∂ν := by
  subst hL
  -- `π` is proper: it is closed, with compact fibres.
  have hπp : IsProperMap π := by
    refine isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨hπ, fun F hF ↦ ?_, fun y ↦ ?_⟩
    · have hq : IsQuotientMap π := hπo.isQuotientMap hπ hπs
      rw [← hq.isClosed_preimage]
      convert hF.mul_right_of_isCompact hπk using 1
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_mul, SetLike.mem_coe, MonoidHom.mem_ker]
      constructor
      · rintro ⟨f, hf, hfx⟩
        exact ⟨f, hf, f⁻¹ * x, by rw [map_mul, map_inv, hfx, inv_mul_cancel], by simp⟩
      · rintro ⟨f, hf, k, hk, rfl⟩
        exact ⟨f, hf, by rw [map_mul, hk, mul_one]⟩
    · obtain ⟨h₀, rfl⟩ := hπs y
      convert hπk.image (Homeomorph.mulLeft h₀).continuous using 1
      ext x
      constructor
      · intro hx
        have hx' : π x = π h₀ := hx
        refine ⟨h₀⁻¹ * x, ?_, by simp⟩
        change π (h₀⁻¹ * x) = 1
        rw [map_mul, map_inv, hx', inv_mul_cancel]
      · rintro ⟨k, hk, rfl⟩
        have hk' : π k = 1 := hk
        change π (h₀ * k) = π h₀
        rw [map_mul, hk', mul_one]
  -- The open subgroup `K ∩ H` of `K` and the restricted Haar measure.
  have : LocallyCompactSpace K := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let K' : Subgroup K := H.comap K.subtype
  have hK'o : IsOpen (K' : Set K) := hH.preimage continuous_subtype_val
  have hK'c : IsClosed (K' : Set K) := Subgroup.isClosed_of_isOpen K' hK'o
  have : LocallyCompactSpace K' := hK'o.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let μ' : Measure K' := Measure.comap Subtype.val μK
  have hμ' : μ'.IsHaarMeasure := Measure.IsHaarMeasure.comap μK (mH := inferInstance)
    (f := K'.subtype) hK'o.isOpenEmbedding_subtypeVal
  let ι : K' →* H := (K.subtype.comp K'.subtype).codRestrict H fun k ↦ k.2
  have hιc : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hLc : IsClosed (((K.comap H.subtype).map π : Subgroup A) : Set A) := by
    rw [Subgroup.coe_map]
    exact hπp.isClosedMap _ (hK.preimage continuous_subtype_val)
  have : LocallyCompactSpace ((K.comap H.subtype).map π) :=
    hLc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let ρ : K' →* (K.comap H.subtype).map π :=
    (π.comp ι).codRestrict _ fun k ↦ ⟨ι k, k.val.2, rfl⟩
  have hρc : Continuous ρ := (hπ.comp hιc).subtype_mk _
  have hρs : Function.Surjective ρ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨⟨x.val, hx⟩, x.2⟩, rfl⟩
  have hK'G : IsClosedEmbedding (fun k : K' ↦ k.val.val) :=
    hK.isClosedEmbedding_subtypeVal.comp hK'c.isClosedEmbedding_subtypeVal
  have hρp : Tendsto ρ (cocompact K') (cocompact _) := by
    refine (isProperMap_iff_tendsto_cocompact.mp
      (isProperMap_iff_isCompact_preimage.mpr ⟨hρc, fun S hS ↦ ?_⟩)).2
    have hT := (hπp.isCompact_preimage (hS.image continuous_subtype_val)).image
      continuous_subtype_val
    convert hK'G.isCompact_preimage hT using 1
    ext k
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hk
      exact ⟨ι k, ⟨ρ k, hk, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨s, hs, hsx⟩, hxk⟩
      have : x = ι k := Subtype.ext hxk
      subst this
      have : s = ρ k := Subtype.ext hsx
      rwa [← this]
  let ν : Measure ((K.comap H.subtype).map π) := μ'.map ρ
  have hν : ν.IsHaarMeasure := Measure.isHaarMeasure_map μ' ρ hρc hρs hρp
  refine ⟨ν, hν, fun g hg h ↦ ?_⟩
  set F : K → ℂ := fun k ↦ if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0 with hFdef
  let Φ : (K.comap H.subtype).map π → ℂ := fun l ↦ g (π h * l)
  have hΦ : Continuous Φ := hg.comp (continuous_const.mul continuous_subtype_val)
  have hF0 : ∀ k, k ∉ (K' : Set K) → F k = 0 := by
    intro k hk
    refine dite_eq_right fun hhk ↦ hk ?_
    have : k.val = h.val⁻¹ * (h.val * k.val) := by group
    change k.val ∈ H
    rw [this]
    exact H.mul_mem (H.inv_mem h.2) hhk
  have hFρ : ∀ k : K', F k.val = Φ (ρ k) := by
    intro k
    have hhk : h.val * k.val.val ∈ H := H.mul_mem h.2 k.2
    simp only [F, dite_eq_left hhk, Φ]
    rw [show (⟨_, hhk⟩ : H) = h * ι k from rfl, map_mul]
    rfl
  have hmeas : MeasurableSet (K' : Set K) := hK'o.measurableSet
  have hsupp : Function.support F ⊆ (K' : Set K) := fun k hk ↦ by
    by_contra h'
    exact hk (hF0 k h')
  have hcomp : F ∘ (Subtype.val : K' → K) = Φ ∘ ρ := funext hFρ
  constructor
  · rw [← integrableOn_iff_integrable_of_support_subset hsupp,
      integrableOn_iff_comap_subtypeVal hmeas]
    change _ ↔ Integrable Φ (μ'.map ρ)
    rw [integrable_map_measure hΦ.aestronglyMeasurable hρc.aemeasurable]
    exact iff_of_eq (congrArg (fun f : K' → ℂ ↦ Integrable f μ') hcomp)
  · calc ∫ k : K, F k ∂μK = ∫ k in (K' : Set K), F k ∂μK :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hF0).symm
      _ = ∫ k : K', F k.val ∂μ' := (integral_subtype_comap hmeas F).symm
      _ = ∫ k : K', Φ (ρ k) ∂μ' := integral_congr_ae (Eventually.of_forall hFρ)
      _ = ∫ l, Φ l ∂ν :=
          (integral_map hρc.aemeasurable hΦ.aestronglyMeasurable).symm

/-- Paper: Theorem D.1.7.1, p. 776. A single stage function, pulled back from the
elementary quotient of a structural pair and extended by zero, is integrable on every
coset, and its coset integral is a Schwartz–Bruhat function on the quotient.
Deviation: This is the case of one stage of the inductive limit; the general case
follows by additivity. -/
theorem lcaCosetIntegral_stageRealization_mem (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (φ : SchwartzBruhatStage e) :
    (∀ x : G, Integrable (fun k : K ↦ schwartzBruhatStageRealization a e φ (x * k.val)) μK) ∧
      lcaCosetIntegral K μK (schwartzBruhatStageRealization a e φ) ∈
        schwartzBruhatSubmodule (G ⧸ K) := by
  classical
  let H := a.val.1
  let C := OrderDual.ofDual a.val.2
  obtain ⟨hHo, -, hCgood, hCH⟩ := a.property
  have hCc : IsCompact (C : Set G) := hCgood.isCompact
  have : IsClosed (K : Set G) := hK
  obtain ⟨b, hb₁, hb₂⟩ := a.exists_quotient K hK
  have : LocallyCompactSpace H := hHo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨e'⟩ := BruhatStructuralPair.elementary b
  let : MeasurableSpace a.quotient := borel _
  have : BorelSpace a.quotient := ⟨rfl⟩
  let N := C.comap H.subtype
  have : IsClosed (N : Set H) := hCc.isClosed.preimage continuous_subtype_val
  let π : H →* a.quotient := QuotientGroup.mk' N
  have hπ : Continuous π := QuotientGroup.continuous_mk
  have hπo : IsOpenMap π := QuotientGroup.isOpenMap_coe
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπk : IsCompact (π.ker : Set H) := by
    rw [QuotientGroup.ker_mk', Subtype.isCompact_iff]
    convert hCc using 1
    ext x
    simp only [Set.mem_image, SetLike.mem_coe]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ hy, fun hx ↦ ⟨⟨x, hCH hx⟩, hx, rfl⟩⟩
  obtain ⟨p, hpc, hpo, hps, hpker, hpmk⟩ := a.exists_quotient_hom K b hb₁ hb₂
  obtain ⟨ν, hν, hfib⟩ := exists_haar_fiberIntegral_eq K μK hK H hHo π hπ hπo hπs hπk p.ker hpker
  obtain ⟨hint, ψ, hψ⟩ :=
    elementary_fiberIntegral (A := a.quotient) (B := b.quotient) e e' p hpc hpo hps ν φ
  let g : a.quotient → ℂ := fun y ↦ φ (Multiplicative.toAdd (e.equiv y))
  have hg : Continuous g :=
    (elementarySchwartz_continuous φ).comp (continuous_toAdd.comp e.equiv.continuous)
  have hR : ∀ x : G, schwartzBruhatStageRealization a e φ x =
      if hx : x ∈ H then g (π ⟨x, hx⟩) else 0 := fun x ↦ by
    rw [schwartzBruhatStageRealization_apply]
    rfl
  -- On a coset through a point of `H`, the integral is computed in the elementary quotient.
  have hkey : ∀ h : H,
      Integrable (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k.val)) μK ∧
        ∫ k : K, schwartzBruhatStageRealization a e φ (h.val * k.val) ∂μK =
          ψ (Multiplicative.toAdd (e'.equiv (p (π h)))) := fun h ↦ by
    have hh := hfib g hg h
    have hfun : (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k.val)) =
        fun k ↦ if hk : h.val * k.val ∈ H then g (π ⟨_, hk⟩) else 0 := by
      funext k
      rw [schwartzBruhatStageRealization_apply]
      split_ifs with hk
      · exact congrArg (fun y ↦ φ (Multiplicative.toAdd (e.equiv y)))
          (QuotientGroup.mk'_apply N _).symm
      · rfl
    exact ⟨(congrArg (fun F : K → ℂ ↦ Integrable F μK) hfun).mpr (hh.1.mpr (hint (π h))),
      (congrArg (fun F : K → ℂ ↦ ∫ k, F k ∂μK) hfun).trans (hh.2.trans (hψ (π h)).symm)⟩
  -- A point whose coset meets `H` is a point of `H` times a point of `K`.
  have hsplit : ∀ x : G, (QuotientGroup.mk x : G ⧸ K) ∈ b.val.1 →
      ∃ h : H, ∃ k₀ : K, x = h.val * k₀.val := fun x hx ↦ by
    rw [hb₁] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨⟨y, hy⟩, ⟨y⁻¹ * x, QuotientGroup.eq.mp hyx⟩, ?_⟩
    simp
  -- Off the cosets meeting `H` the function vanishes.
  have hzero : ∀ x : G, (QuotientGroup.mk x : G ⧸ K) ∉ b.val.1 →
      ∀ k : K, schwartzBruhatStageRealization a e φ (x * k.val) = 0 := fun x hx k ↦ by
    rw [hR]
    refine dite_eq_right fun hxk ↦ hx ?_
    rw [hb₁]
    exact ⟨x * k.val, hxk, by simp⟩
  have htrans : ∀ (h : H) (k₀ : K),
      (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k₀.val * k.val)) =
        fun k ↦ schwartzBruhatStageRealization a e φ (h.val * (k₀ * k).val) := fun h k₀ ↦ by
    funext k
    simp [mul_assoc]
  have hintegrable : ∀ x : G,
      Integrable (fun k : K ↦ schwartzBruhatStageRealization a e φ (x * k.val)) μK := by
    intro x
    by_cases hx : (QuotientGroup.mk x : G ⧸ K) ∈ b.val.1
    · obtain ⟨h, k₀, rfl⟩ := hsplit x hx
      rw [htrans h k₀]
      exact (hkey h).1.comp_mul_left k₀
    · simp_rw [hzero x hx]
      exact integrable_zero _ _ _
  refine ⟨hintegrable, ?_⟩
  have hfun : lcaCosetIntegral K μK (schwartzBruhatStageRealization a e φ) =
      schwartzBruhatStageRealization b e' ψ := by
    funext q
    have h1 := schwartzBruhatStageRealization_apply b e' ψ q
    show (∫ k : K, schwartzBruhatStageRealization a e φ ((Quotient.out q) * k.val) ∂μK) = _
    have hq : (QuotientGroup.mk (Quotient.out q) : G ⧸ K) = q := QuotientGroup.out_eq' q
    split_ifs at h1 with hqb
    · have hqb' : (QuotientGroup.mk (Quotient.out q) : G ⧸ K) ∈ b.val.1 := by rw [hq]; exact hqb
      refine Eq.trans ?_ h1.symm
      have hs := hsplit (Quotient.out q) hqb'
      let h : H := Classical.choose hs
      have hs' := Classical.choose_spec hs
      let k₀ : K := Classical.choose hs'
      have hx : Quotient.out q = h.val * k₀.val := Classical.choose_spec hs'
      clear_value h k₀
      have hhq : (QuotientGroup.mk h.val : G ⧸ K) = q := by
        rw [← hq, hx, QuotientGroup.eq]
        simp
      have hhb : (QuotientGroup.mk h.val : G ⧸ K) ∈ b.val.1 := by rw [hhq]; exact hqb
      have hpq : p (π h) = QuotientGroup.mk ⟨q, hqb⟩ :=
        (hpmk h.val h.2 hhb).trans (congrArg _ (Subtype.ext hhq))
      have e1 : (fun k : K ↦ schwartzBruhatStageRealization a e φ (Quotient.out q * k.val)) =
          fun k ↦ schwartzBruhatStageRealization a e φ (h.val * (k₀ * k).val) := by
        funext k
        simp only [hx, mul_assoc, Subgroup.coe_mul]
      calc ∫ k : K, schwartzBruhatStageRealization a e φ (Quotient.out q * k.val) ∂μK
          = ∫ k : K, schwartzBruhatStageRealization a e φ (h.val * (k₀ * k).val) ∂μK :=
            congrArg (fun F : K → ℂ ↦ ∫ k, F k ∂μK) e1
        _ = ∫ k : K, schwartzBruhatStageRealization a e φ (h.val * k.val) ∂μK :=
            integral_mul_left_eq_self
              (fun k : K ↦ schwartzBruhatStageRealization a e φ (h.val * k.val)) k₀
        _ = ψ (Multiplicative.toAdd (e'.equiv (p (π h)))) := (hkey h).2
        _ = _ := congrArg (fun y ↦ ψ (Multiplicative.toAdd (e'.equiv y))) hpq
    · have hqb' : (QuotientGroup.mk (Quotient.out q) : G ⧸ K) ∉ b.val.1 := by rw [hq]; exact hqb
      refine Eq.trans ?_ h1.symm
      simp_rw [hzero (Quotient.out q) hqb']
      exact integral_zero _ _
  rw [hfun]
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem e' ⟨ψ, rfl⟩)

omit [TopologicalSpace G] hTop hT2 hLC hBorel hK hHaarK hRegularK in
/-- The coset integral is additive on functions whose restrictions to all cosets
are integrable. -/
theorem lcaCosetIntegral_add (f g : G → ℂ)
    (hf : ∀ x : G, Integrable (fun k : K ↦ f (x * k.val)) μK)
    (hg : ∀ x : G, Integrable (fun k : K ↦ g (x * k.val)) μK) :
    lcaCosetIntegral K μK (f + g) = lcaCosetIntegral K μK f + lcaCosetIntegral K μK g := by
  funext q
  simp only [lcaCosetIntegral, Pi.add_apply]
  exact integral_add (hf _) (hg _)

/-- Paper: Theorem D.1.7.1, p. 776. The integral of a Schwartz–Bruhat function
over each coset exists and gives a Schwartz–Bruhat function on the quotient. -/
theorem lcaCosetIntegral_mem_schwartzBruhat (f : SchwartzBruhat G) :
    (∀ x : G, Integrable (fun k : K ↦ f (x * k.val)) μK) ∧
      lcaCosetIntegral K μK f ∈ schwartzBruhatSubmodule (G ⧸ K) := by
  have hf := (show schwartzBruhatSubmodule G from f).property
  generalize (show schwartzBruhatSubmodule G from f).val = g at hf ⊢
  let P : (G → ℂ) → Prop := fun g ↦
    (∀ x : G, Integrable (fun k : K ↦ g (x * k.val)) μK) ∧
      lcaCosetIntegral K μK g ∈ schwartzBruhatSubmodule (G ⧸ K)
  have hzero : P 0 := by
    refine ⟨fun x ↦ integrable_zero _ _ _, ?_⟩
    have : lcaCosetIntegral K μK (0 : G → ℂ) = 0 := by
      funext q
      simp [lcaCosetIntegral]
    rw [this]
    exact zero_mem _
  have hadd : ∀ g₁ g₂, P g₁ → P g₂ → P (g₁ + g₂) := fun g₁ g₂ h₁ h₂ ↦ by
    refine ⟨fun x ↦ (h₁.1 x).add (h₂.1 x), ?_⟩
    rw [lcaCosetIntegral_add K μK g₁ g₂ h₁.1 h₂.1]
    exact add_mem h₁.2 h₂.2
  refine Submodule.iSup_induction (motive := P) _ hf (fun a g ha ↦ ?_) hzero hadd
  refine Submodule.iSup_induction (motive := P) _ ha (fun e g he ↦ ?_) hzero hadd
  obtain ⟨φ, rfl⟩ := LinearMap.mem_range.mp he
  exact lcaCosetIntegral_stageRealization_mem K μK hK a e φ

/-- Paper: (D.1.7.1)–(D.1.7.2), p. 776. Take the existing coset integral with
values in the Schwartz–Bruhat space on the quotient. -/
def schwartzBruhatCosetIntegral (f : SchwartzBruhat G) : SchwartzBruhat (G ⧸ K) :=
  ⟨lcaCosetIntegral K μK f, (lcaCosetIntegral_mem_schwartzBruhat K μK hK f).2⟩

/-- Paper: (D.1.7.2), p. 776. At a quotient point represented by x the
Schwartz–Bruhat coset integral is the integral along the translate by x. -/
theorem schwartzBruhatCosetIntegral_mk (f : SchwartzBruhat G) (x : G) :
    schwartzBruhatCosetIntegral K μK hK f (QuotientGroup.mk x) =
      ∫ k : K, f (x * k.val) ∂μK := by
  show lcaCosetIntegral K μK f (QuotientGroup.mk x) = _
  exact lcaCosetIntegral_mk K μK f x ((lcaCosetIntegral_mem_schwartzBruhat K μK hK f).1 x)

include hHaar hRegular in
/-- Paper: Theorem D.1.7.1(1), p. 776. The coset integral is obtained by integrating
the Fourier transform over the annihilator against the quotient's dual Haar measure.
Deviation: The dual of the quotient is used directly and its characters
are pulled back to G, so the integral uses the specified Plancherel normalization. -/
theorem schwartzBruhat_poisson (μQ : Measure (G ⧸ K)) (hQ : IsWeilQuotientMeasure K μ μK μQ)
    (νQ : Measure (PontryaginDual (G ⧸ K))) (hνQ : IsLCAPlancherelMeasure μQ νQ)
    (f : SchwartzBruhat G) (x : G) :
    let q : G →ₜ* G ⧸ K := ⟨QuotientGroup.mk' K, continuous_quotient_mk'⟩
    Integrable (f : G → ℂ) μ ∧
      Integrable (fun χ ↦ lcaFourier μ f (PontryaginDual.map q χ) * (χ (q x) : ℂ)) νQ ∧
      schwartzBruhatCosetIntegral K μK hK f (q x) =
        ∫ χ, lcaFourier μ f (PontryaginDual.map q χ) * (χ (q x) : ℂ) ∂νQ := by
  intro q
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK
  let : BorelSpace (G ⧸ K) := ⟨rfl⟩
  let : μQ.IsHaarMeasure := hQ.1
  let : μQ.Regular := hQ.2.1
  let g := schwartzBruhatCosetIntegral K μK hK f
  have hf := SchwartzBruhat.integrable μ f
  have hfour (χ : PontryaginDual (G ⧸ K)) : lcaFourier μ f (PontryaginDual.map q χ) = lcaFourier μQ g χ := by
    let t (y : G) := f y * star (χ (q y) : ℂ)
    have hmeas : Continuous (fun y ↦ star (χ (q y) : ℂ)) :=
      (continuous_subtype_val.comp (χ.continuous.comp q.continuous)).star
    have ht : Integrable t μ := hf.mul_bdd (c := 1) hmeas.aestronglyMeasurable
      (.of_forall fun y ↦ by simp)
    change (∫ y, t y ∂μ) = _
    rw [(weilQuotientIntegral_L1 K hK μ μK μQ hQ ht).2.2]
    unfold lcaFourier
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective z
    have htk (k : K) : t (y * k.val) = f (y * k.val) * star (χ (q y) : ℂ) := by
      have hqk : q k.val = 1 := (QuotientGroup.eq_one_iff k.val).mpr k.property
      simp only [t, map_mul q, hqk, mul_one]
    have hfi := (lcaCosetIntegral_mem_schwartzBruhat K μK hK f).1 y
    have hti : Integrable (fun k : K ↦ t (y * k.val)) μK :=
      (hfi.mul_const _).congr (.of_forall fun k ↦ (htk k).symm)
    rw [lcaCosetIntegral_mk K μK t y hti]
    simp_rw [htk, integral_mul_const]
    exact congrArg (fun z : ℂ ↦ z * _) (schwartzBruhatCosetIntegral_mk K μK hK f y).symm
  refine ⟨hf, ?_⟩
  simp only [hfour]
  exact schwartzBruhat_inverse_integral μQ νQ hνQ g (q x)

section CosetIntegration

omit hK hHaarK hRegularK hBorel hTop hT2 hLC

/-- An annihilator is the intersection of the closed kernels of point evaluations. -/
private theorem closed_lcaAnnihilator {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (K : Subgroup G) :
    IsClosed (lcaAnnihilator K : Set (PontryaginDual G)) := by
  have he : (lcaAnnihilator K : Set (PontryaginDual G)) =
      ⋂ k : K, {χ : PontryaginDual G | χ k.val = 1} := by
    ext χ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_lcaAnnihilator_iff]
  rw [he]
  exact isClosed_iInter fun k ↦ isClosed_eq (pontryaginDual_eval (G := G) k.val).continuous continuous_const

private theorem compactlyGenerated_of_closedEmbedding {H L : Type*} [CommGroup H] [CommGroup L]
    [TopologicalSpace H] [TopologicalSpace L] [IsTopologicalGroup L] [T2Space L] [LocallyCompactSpace L]
    (f : H →* L) (hf : IsClosedEmbedding f) (hL : IsCompactlyGeneratedGroup L) :
    IsCompactlyGeneratedGroup H := by
  have hr : IsCompactlyGeneratedGroup f.range := isCompactlyGeneratedGroup_closedSubgroup hL f.range hf.isClosed_range
  let e := MulEquiv.ofBijective f.rangeRestrict ⟨fun _ _ h ↦ hf.injective (congrArg Subtype.val h),
    fun ⟨_,x,hx⟩ ↦ ⟨x,Subtype.ext hx⟩⟩
  have hd : IsInducing f.rangeRestrict := IsInducing.subtypeVal.of_comp_iff.mp hf.isInducing
  let d : H ≃ₜ* f.range := ⟨e,hd.continuous,
    (e.toEquiv.toHomeomorphOfIsInducing hd).symm.continuous⟩
  exact isCompactlyGeneratedGroup_of_continuousMulEquiv d.symm hr

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Pullback embeds the annihilator of the image as a closed subgroup of the original annihilator. -/
private theorem isBruhatGoodSubgroup_quotient_map (K : Subgroup G) (hK : IsClosed (K : Set G))
    (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) :
    IsBruhatGoodSubgroup (k.map (QuotientGroup.mk' K)) := by
  let : IsClosed (K : Set G) := hK
  let q := QuotientGroup.mk' K
  let k' := k.map q
  have hkc := isCompact_of_bruhatGoodSubgroup k hk
  have hk' : IsCompact (k' : Set (G ⧸ K)) := hkc.image QuotientGroup.continuous_mk
  refine ⟨hk'.isClosed,isOpen_lcaAnnihilator k' hk',?_⟩
  obtain ⟨e,he⟩ := lcaQuotientDual_equiv_annihilator K hK
  let i := (lcaAnnihilator K).subtype.comp (e.toMonoidHom.comp (lcaAnnihilator k').subtype)
  let f := i.codRestrict (lcaAnnihilator k) fun χ ↦ (mem_lcaAnnihilator_iff k _).mpr fun u ↦ by
    change (e χ.val).val u.val = 1
    rw [he]
    exact (mem_lcaAnnihilator_iff k' _).mp χ.property ⟨q u.val,⟨u.val,u.property,rfl⟩⟩
  have hi : IsClosedEmbedding i := (closed_lcaAnnihilator K).isClosedEmbedding_subtypeVal.comp
    (e.toHomeomorph.isClosedEmbedding.comp (closed_lcaAnnihilator k').isClosedEmbedding_subtypeVal)
  let : LocallyCompactSpace (lcaAnnihilator k) := hk.2.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  exact compactlyGenerated_of_closedEmbedding f
    (IsClosedEmbedding.of_comp_iff (closed_lcaAnnihilator k).isClosedEmbedding_subtypeVal |>.mp hi) hk.2.2

/-- The images of the open and compact subgroups form a structural pair on the quotient. -/
private theorem bruhatStructuralPair_quotient_map (K : Subgroup G) (hK : IsClosed (K : Set G))
    (a : BruhatStructuralPair G) :
    ∃ b : BruhatStructuralPair (G ⧸ K), b.val.1 = a.val.1.map (QuotientGroup.mk' K) ∧
      OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K) := by
  let q := QuotientGroup.mk' K
  let J := a.val.1
  let M := J.map q
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have ho : IsOpen (M : Set (G ⧸ K)) := hq.isOpenMap _ a.property.1
  let f := (q.comp J.subtype).codRestrict M (fun x ↦ ⟨x.val,x.property,rfl⟩)
  have hf : IsOpenMap f := (hq.isOpenMap.comp a.property.1.isOpenEmbedding_subtypeVal.isOpenMap).subtype_mk _
  have hc : Continuous f := (hq.continuous.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective f := fun ⟨_,x,hx,h⟩ ↦ ⟨⟨x,hx⟩,Subtype.ext h⟩
  obtain ⟨U,hU,hcU,hg⟩ := a.property.2.1
  have hM : IsCompactlyGeneratedGroup M := by
    refine ⟨f '' U,?_,hcU.image hc,?_⟩
    · simpa only [map_one] using hf.image_mem_nhds hU
    · rw [← MonoidHom.map_closure,hg,Subgroup.map_top_of_surjective f hs]
  exact ⟨⟨(M,OrderDual.toDual ((OrderDual.ofDual a.val.2).map q)),ho,hM,
    isBruhatGoodSubgroup_quotient_map K hK _ a.property.2.2.1,Subgroup.map_mono a.property.2.2.2⟩,rfl,rfl⟩

/-- Normalized averaging fixes a supported, kernel-invariant function. -/
private theorem stageAverage_eq_self_of_invariant (b : BruhatStructuralPair G) (f : G → ℂ)
    (hzero : ∀ x ∉ b.val.1, f x = 0) (hinv : ∀ x k, k ∈ OrderDual.ofDual b.val.2 → f (x*k) = f x)
    (x : G) : schwartzBruhatStageAverage b f x = f x := by
  classical
  let k := OrderDual.ofDual b.val.2
  let : MeasurableSpace k := borel k
  let : BorelSpace k := ⟨rfl⟩
  have hk := isCompact_of_bruhatGoodSubgroup k b.property.2.2.1
  let : CompactSpace k := isCompact_iff_compactSpace.mp hk
  let U : TopologicalSpace.PositiveCompacts k := ⟨⟨univ,isCompact_univ⟩, by simp⟩
  let : IsProbabilityMeasure (Measure.haarMeasure U) := ⟨Measure.haarMeasure_self⟩
  by_cases hx : x ∈ b.val.1
  · unfold schwartzBruhatStageAverage
    rw [ite_eq_left hx]
    change (∫ u : k, f (u.val*x) ∂Measure.haarMeasure U) = f x
    simp only [mul_comm _ x,fun u : k ↦ hinv x u u.property, integral_const]
    simp
  · unfold schwartzBruhatStageAverage
    rw [ite_eq_right hx,hzero x hx]

variable [MeasurableSpace G] [BorelSpace G] (K : Subgroup G) (μK : Measure K) [μK.IsHaarMeasure] [μK.Regular]
variable (hK : IsClosed (K : Set G))


private theorem cosetIntegral_add_apply (f g : SchwartzBruhat G) (y : G ⧸ K) :
    schwartzBruhatCosetIntegral K μK hK (f+g) y =
      schwartzBruhatCosetIntegral K μK hK f y + schwartzBruhatCosetIntegral K μK hK g y := by
  induction y using QuotientGroup.induction_on with
  | _ x =>
    simp only [schwartzBruhatCosetIntegral_mk]
    exact integral_add ((lcaCosetIntegral_mem_schwartzBruhat K μK hK f).1 x)
      ((lcaCosetIntegral_mem_schwartzBruhat K μK hK g).1 x)

private theorem cosetIntegral_smul_apply (c : ℂ) (f : SchwartzBruhat G) (y : G ⧸ K) :
    schwartzBruhatCosetIntegral K μK hK (c • f) y = c • schwartzBruhatCosetIntegral K μK hK f y := by
  induction y using QuotientGroup.induction_on with
  | _ x =>
    simp only [schwartzBruhatCosetIntegral_mk]
    exact integral_smul c _

private def cosetIntegralLinear : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat (G ⧸ K) where
  toFun := schwartzBruhatCosetIntegral K μK hK
  map_add' f g := Subtype.ext (funext (cosetIntegral_add_apply K μK hK f g))
  map_smul' c f := Subtype.ext (funext (cosetIntegral_smul_apply K μK hK c f))

/-- Integration sends a stage into the fixed space of its image stage projector. -/
private theorem cosetIntegral_stageAverage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (b : BruhatStructuralPair (G ⧸ K))
    (hJ : b.val.1 = a.val.1.map (QuotientGroup.mk' K))
    (hk : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K))
    (s : SchwartzBruhatStage e) (x : G ⧸ K) :
    let f := schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s)
    schwartzBruhatStageAverage b f x = f x := by
  let : IsClosed (K : Set G) := hK
  let q := QuotientGroup.mk' K
  let f : SchwartzBruhat G := schwartzBruhatStageInclusion a e s
  have hmk := schwartzBruhatCosetIntegral_mk K μK hK f
  dsimp only
  apply stageAverage_eq_self_of_invariant
  · intro y hy
    obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective y
    refine (hmk z).trans ?_
    have hz (u : K) : z*u.val ∉ a.val.1 := by
      intro h
      apply hy
      rw [hJ]
      exact ⟨z*u.val,h,QuotientGroup.mk_mul_of_mem z u.property⟩
    change (∫ u : K, schwartzBruhatStageRealization a e s (z*u.val) ∂μK) = 0
    have h0 (u : K) : schwartzBruhatStageRealization a e s (z * u.val) = 0 :=
      (schwartzBruhatStageRealization_apply a e s _).trans (dite_eq_right (hz u))
    simp only [h0, integral_zero]
  · intro y k hk'
    obtain ⟨z,rfl⟩ := QuotientGroup.mk_surjective y
    rw [hk] at hk'
    obtain ⟨v,hv,rfl⟩ := hk'
    refine (hmk (z*v)).trans (Eq.trans ?_ (hmk z).symm)
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    change schwartzBruhatStageRealization a e s (z*v*u.val) = _
    rw [mul_right_comm]
    exact stageRealization_mul_kernel a e s _ v hv


open scoped BoundedContinuousFunction in
/-- The zero-order seminorm controls evaluation uniformly on the elementary group. -/
private theorem elementarySchwartz_continuousEval {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    Continuous (fun p : ElementarySchwartz m n r F × ElementaryLieGroup m n r F ↦ p.1 p.2) := by
  let E := ElementarySchwartz m n r F
  let X := ElementaryLieGroup m n r F
  let q := (elementarySchwartzSeminorm (m := m) (n := n) (r := r) (F := F) (0,0,0,0))
  have hb (f : E) (x : X) : ‖f x‖ ≤ q f := by
    change (‖f x‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0,0,0,0)).toReal
    apply ENNReal.toReal_mono (f.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun y ↦ (‖f y‖₊ : ENNReal)) x
  let L : E →ₗ[ℂ] (X →ᵇ ℂ) :=
    { toFun := fun f ↦ BoundedContinuousFunction.ofNormedAddCommGroup f.val
        (elementarySchwartz_continuousFunction f) (q f) (hb f)
      map_add' := fun _ _ ↦ BoundedContinuousFunction.ext (fun _ ↦ rfl)
      map_smul' := fun _ _ ↦ BoundedContinuousFunction.ext (fun _ ↦ rfl) }
  have hL : Continuous L := by
    refine (norm_withSeminorms ℂ _).continuous_of_continuous_comp L fun _ ↦ ?_
    exact Seminorm.continuous_of_le (elementarySchwartz_withSeminorms.continuous_seminorm (0,0,0,0))
      (fun f ↦ BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg q f) (hb f))
  exact continuous_eval.comp ((hL.comp continuous_fst).prodMk continuous_snd)

private theorem stageIntegral_eval_continuous (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (z : G) :
    ∃ L : SchwartzBruhatStage e →L[ℂ] ℂ, ∀ s,
      L s = schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s) (QuotientGroup.mk z) := by
  let X := SchwartzBruhatStage e
  let : TopologicalSpace.MetrizableSpace X := elementarySchwartz_isFrechet.choose_spec.2.1
  let : BarrelledSpace ℂ X := elementarySchwartz_barrelled
  let C : X →ₗ[ℂ] (K → ℂ) := (LinearMap.funLeft ℂ ℂ (fun k : K ↦ z*k.val)).comp (schwartzBruhatStageRealization a e)
  have hc (k : K) : Continuous (fun s : X ↦ C s k) := by
    classical
    change Continuous (fun s : X ↦ schwartzBruhatStageRealization a e s (z*k.val))
    simp only [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · exact elementarySchwartz_continuousEval.comp (continuous_id.prodMk continuous_const)
    · exact continuous_const
  have hi (s : X) : Integrable (C s) μK :=
    (lcaCosetIntegral_mem_schwartzBruhat K μK hK (schwartzBruhatStageInclusion a e s)).1 z
  obtain ⟨L,hL⟩ := exists_integralCLM_of_pointwise_continuous μK C hc hi
  exact ⟨L, fun s ↦ (hL s).trans (schwartzBruhatCosetIntegral_mk K μK hK (schwartzBruhatStageInclusion a e s) z).symm⟩

private theorem stageIntegral_eval_quotient (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (y : G ⧸ K) : ∃ L : SchwartzBruhatStage e →L[ℂ] ℂ, ∀ s,
      L s = schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s) y := by
  exact QuotientGroup.induction_on y (stageIntegral_eval_continuous K μK hK a e)

/-- The coset integral factors continuously through a single elementary quotient stage. -/
private theorem cosetIntegral_continuous_on_stage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Continuous (fun s : SchwartzBruhatStage e ↦ schwartzBruhatCosetIntegral K μK hK (schwartzBruhatStageInclusion a e s)) := by
  classical
  let : IsClosed (K : Set G) := hK
  let b := (bruhatStructuralPair_quotient_map K hK a).choose
  have hJ := (bruhatStructuralPair_quotient_map K hK a).choose_spec.1
  have hk := (bruhatStructuralPair_quotient_map K hK a).choose_spec.2
  let d := Classical.choice b.elementary
  let j := schwartzBruhatStageInclusion b d
  have hret := schwartzBruhatStage_average_retraction b d
  let R := hret.choose
  let A := (cosetIntegralLinear K μK hK).comp (schwartzBruhatStageInclusion a e)
  let B := R.toLinearMap.comp A
  have hval (s : SchwartzBruhatStage e) (x : G ⧸ K) :
      schwartzBruhatStageRealization b d (B s) x = A s x :=
    (hret.choose_spec.2 (A s) x).trans (cosetIntegral_stageAverage K μK hK a e b hJ hk s x)
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := elementarySchwartz_barrelled
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  have hB : Continuous B := by
    refine continuous_to_stage_of_realization b d B fun x ↦ ?_
    let H := stageIntegral_eval_quotient K μK hK a e x
    exact ⟨H.choose, fun s ↦ (H.choose_spec s).trans (hval s x).symm⟩
  have hj : Continuous (show SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhat (G ⧸ K) from j) :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property b d
  exact (hj.comp hB).congr fun s ↦ Subtype.ext (funext (hval s))

end CosetIntegration

/-- Paper: Theorem D.1.7.1(2), p. 776. The coset integral on Schwartz–Bruhat
functions is a continuous linear map. -/
theorem schwartzBruhatCosetIntegral_continuousLinear :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      ∀ f, P f = schwartzBruhatCosetIntegral K μK hK f := by
  let A := cosetIntegralLinear K μK hK
  have hA : Continuous A := by
    apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp A fun p ↦ ?_
    let P : SeminormFamily ℂ (SchwartzBruhat G) {q : Seminorm ℂ (SchwartzBruhat G) //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
    have hP : WithSeminorms P := ⟨rfl⟩
    refine hP.continuous_seminorm ⟨p.val.comp A,?_⟩
    intro a e
    exact ((withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm p).comp
      (cosetIntegral_continuous_on_stage K μK hK a e)
  exact ⟨⟨A,hA⟩,fun _ ↦ rfl⟩

section CosetLifts

omit hK hHaarK hRegularK hBorel hTop hT2 hLC

open Function
open scoped Pointwise

section

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- A compactly supported function smooth on every fiber has finite weighted partials. -/
private theorem elementarySchwartz_of_compactSupport {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) (hc : HasCompactSupport f) :
    f ∈ elementarySchwartzSubmodule m n r F := by
  classical
  refine ⟨hf, fun i ↦ ?_⟩
  let E := EuclideanSpace ℝ (Fin m)
  let N := EuclideanSpace ℝ (Fin n)
  let T := Fin n → AddCircle (1 : ℝ)
  let Z := Fin r → ℤ
  let q (v : N) : T := fun j ↦ (v j : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q := (IsOpenQuotientMap.piMap
    (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  let lift (t : T) := hq.surjective.hasRightInverse.choose t
  have hl (t : T) : q (lift t) = t := hq.surjective.hasRightInverse.choose_spec t
  let d (y : ElementaryLieGroup m n r F) := elementaryPartial f i.2.1 i.2.2.1
    (y.1, lift y.2.1) y.2.2.1 y.2.2.2
  have hd (v : E × N) (z : Z) (b : F) :
      d (elementaryCover v z b) = elementaryPartial f i.2.1 i.2.2.1 v z b := by
    apply (elementaryPartial_descends _ _ _ _ _ (hf z b)).2
    exact Prod.ext rfl (Prod.ext (hl (q v.2)) rfl)
  have hdc : Continuous d := by
    apply (Homeomorph.prodAssoc E T (Z × F)).isQuotientMap.continuous_iff.mpr
    apply continuous_prod_of_discrete_right.mpr
    intro z
    apply (IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff.mp
    exact ((elementaryPartial_descends _ _ _ _ _ (hf z.1 z.2)).1.continuous).congr
      (fun w ↦ (hd w z.1 z.2).symm)
  have hdz {y : ElementaryLieGroup m n r F} (hy : y ∉ tsupport f) : d y = 0 := by
    let v : E × N := (y.1, lift y.2.1)
    let p (w : E × N) := elementaryCover w y.2.2.1 y.2.2.2
    have hp : Continuous p := continuous_fst.prodMk ((hq.continuous.comp continuous_snd).prodMk continuous_const)
    have hpv : p v = y := Prod.ext rfl (Prod.ext (hl y.2.1) rfl)
    have hv : v ∉ tsupport (f ∘ p) := fun hv ↦ hy (hpv ▸ tsupport_comp_subset_preimage f hp hv)
    have h0 (j : ℕ) : iteratedFDeriv ℝ j (f ∘ p) v = 0 := by
      by_contra hn
      exact hv (support_iteratedFDeriv_subset j hn)
    dsimp only [d, elementaryPartial]
    change (iteratedFDeriv ℝ _ (f ∘ p) v) _ = 0
    rw [h0]
    rfl
  let w (y : ElementaryLieGroup m n r F) : ℂ :=
    ((∏ j, (y.1 j : ℂ) ^ i.1 j) * (∏ j, (y.2.2.1 j : ℂ) ^ i.2.2.2 j)) * d y
  have hw : Continuous w := by
    apply Continuous.mul _ hdc
    apply Continuous.mul
    · fun_prop
    · exact (continuous_of_discreteTopology (f := fun z : Z ↦ ∏ j, (z j : ℂ) ^ i.2.2.2 j)).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have hwK : HasCompactSupport w := HasCompactSupport.intro hc fun y hy ↦ by simp [w, hdz hy]
  obtain ⟨C,hC⟩ := hw.bounded_above_of_compact_support hwK
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun v ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [ENNReal.coe_nnreal_eq]
  apply ENNReal.ofReal_le_ofReal
  have h := hC (elementaryCover v a b)
  dsimp only [w] at h
  rw [hd] at h
  exact h

end

private theorem elementary_orbit_deriv_comp {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    (p : ElementaryLieGroup m n r F →+ ElementaryLieGroup m' n' r' F') (hp : Continuous p)
    (v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (s : ElementarySchwartz m' n' r' F') :
    ∃ t : ElementarySchwartz m' n' r' F', ∀ u a b,
      fderiv ℝ (fun w ↦ s (p (elementaryCover w a b))) u v = t (p (elementaryCover u a b)) := by
  let l := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let q := (elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F))
  let c := p.comp (q.comp l.toLinearMap.toAddMonoidHom)
  obtain ⟨D,hD⟩ := elementarySchwartz_orbitDeriv c (hp.comp (elementaryCoverZeroHom_continuous_isOpenMap.1.comp l.continuous))
  refine ⟨D s,fun u a b ↦ ?_⟩
  have hsm := contDiff_comp_elementaryHom p hp s.property.1 a b
  have hline : HasDerivAt (fun t : ℝ ↦ u + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have h := ((hsm.differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp))
  have he (t : ℝ) : p (elementaryCover u a b) + c t = p (elementaryCover (u+t•v) a b) := by
    change _ + p (elementaryCover (t•v) 0 0) = _
    rw [← map_add, elementaryCover_add, add_zero, add_zero]
  have h' := hD s (p (elementaryCover u a b))
  simp_rw [he] at h'
  exact h.unique h'

section Graph

variable {m n r m₁ n₁ r₁ m₂ n₂ r₂ : ℕ} {F F₁ F₂ : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F₁] [TopologicalSpace F₁] [DiscreteTopology F₁] [Finite F₁]
    [AddCommGroup F₂] [TopologicalSpace F₂] [DiscreteTopology F₂] [Finite F₂]
local notation "A₀" => ElementaryLieGroup m n r F
local notation "B₀" => ElementaryLieGroup m₁ n₁ r₁ F₁
local notation "C₀" => ElementaryLieGroup m₂ n₂ r₂ F₂
local notation "S₁" => ElementarySchwartz m₁ n₁ r₁ F₁
local notation "S₂" => ElementarySchwartz m₂ n₂ r₂ F₂

/-- Products of two pullbacks are Schwartz when their noncompact coordinates control the source coordinates. -/
private theorem elementary_graph_mem (p : A₀ →+ B₀) (q : A₀ →+ C₀) (hp : Continuous p) (hq : Continuous q)
    (hcoord : ∀ j : Fin m ⊕ Fin r, ∃ (a : B₀ →+ ℝ) (b : C₀ →+ ℝ), Continuous a ∧ Continuous b ∧
      ∀ x, fiberCoord x j = a (p x) + b (q x)) (s : S₁) (t : S₂) :
    (fun x ↦ s (p x) * t (q x)) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  let J := Fin m ⊕ Fin r
  let V := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let ev {m n r : ℕ} {F : Type} (P : MvPolynomial (Fin m ⊕ Fin r) ℂ) (y : ElementaryLieGroup m n r F) :=
    MvPolynomial.eval (Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (y.2.2.1 j : ℂ))) P
  choose a b ha hb hab using hcoord
  choose P hP using fun j ↦ elementary_real_hom_polynomial (a j) (ha j)
  choose Q hQ using fun j ↦ elementary_real_hom_polynomial (b j) (hb j)
  let w (l : List J) (x : A₀) := (l.map (fun j ↦ (fiberCoord x j : ℂ))).prod
  have hw (l : List J) (R : MvPolynomial (Fin m₁ ⊕ Fin r₁) ℂ) (T : MvPolynomial (Fin m₂ ⊕ Fin r₂) ℂ)
      (s : S₁) (t : S₂) : ∃ C : ℝ, ∀ x : A₀,
        ‖w l x * ((ev R (p x)*s (p x)) * (ev T (q x)*t (q x)))‖ ≤ C := by
    induction l generalizing R T with
    | nil =>
      obtain ⟨c,hc⟩ := polynomial_weight_bounded R s
      obtain ⟨d,hd⟩ := polynomial_weight_bounded T t
      refine ⟨c*d,fun x ↦ ?_⟩
      change ‖1 * ((_ * s (p x)) * (_ * t (q x)))‖ ≤ c*d
      rw [one_mul,norm_mul]
      exact mul_le_mul (hc (p x)) (hd (q x)) (norm_nonneg _) ((norm_nonneg _).trans (hc (p x)))
    | cons j l ih =>
      obtain ⟨c,hc⟩ := ih (P j * R) T
      obtain ⟨d,hd⟩ := ih R (Q j * T)
      refine ⟨c+d,fun x ↦ ?_⟩
      refine le_trans (le_of_eq (congrArg norm (show _ =
        w l x * ((ev (P j * R) (p x)*s (p x))*(ev T (q x)*t (q x))) +
        w l x * ((ev R (p x)*s (p x))*(ev (Q j * T) (q x)*t (q x))) from ?_))) ((norm_add_le ..).trans (add_le_add (hc x) (hd x)))
      simp only [w,List.map_cons,List.prod_cons, hab j x, Complex.ofReal_add, ev,MvPolynomial.eval_mul, hP, hQ]
      ring
  let X (s : S₁) (t : S₂) (a : Fin r → ℤ) (b : F) (u : V) :=
    s (p (elementaryCover u a b)) * t (q (elementaryCover u a b))
  have hs (s : S₁) (a : Fin r → ℤ) (b : F) := contDiff_comp_elementaryHom p hp s.property.1 a b
  have ht (t : S₂) (a : Fin r → ℤ) (b : F) := contDiff_comp_elementaryHom q hq t.property.1 a b
  have hdiff (dirs : List V) (l : List J) (s : S₁) (t : S₂) : ∃ C : ℝ, ∀ u a b,
      ‖w l (elementaryCover u a b) * iteratedFDeriv ℝ dirs.length (X s t a b) u dirs.get‖ ≤ C := by
    induction dirs using List.reverseRecOn generalizing s t with
    | nil =>
      obtain ⟨C,h⟩ := hw l 1 1 s t
      exact ⟨C, fun u a b ↦ by simpa [X,ev] using h (elementaryCover u a b)⟩
    | append_singleton dirs v ih =>
      obtain ⟨s',h₁⟩ := elementary_orbit_deriv_comp p hp v s
      obtain ⟨t',h₂⟩ := elementary_orbit_deriv_comp q hq v t
      obtain ⟨c,hc⟩ := ih s' t
      obtain ⟨d,hd⟩ := ih s t'
      refine ⟨c+d,fun u a b ↦ ?_⟩
      have he : (fun w ↦ fderiv ℝ (X s t a b) w v) = X s' t a b + X s t' a b := by
        funext w
        dsimp only [X,Pi.add_apply]
        rw [fderiv_fun_mul ((hs s a b).differentiable (by simp) w) ((ht t a b).differentiable (by simp) w)]
        simp only [add_apply, smul_apply, h₁, h₂, smul_eq_mul]
        ring
      rw [iteratedFDeriv_append_singleton ((hs s a b).mul (ht t a b)),he,
        iteratedFDeriv_add_apply (((hs s' a b).mul (ht t a b)).contDiffAt.of_le (mod_cast le_top))
          (((hs s a b).mul (ht t' a b)).contDiffAt.of_le (mod_cast le_top)),add_apply,mul_add]
      exact (norm_add_le ..).trans (add_le_add (hc u a b) (hd u a b))
  refine ⟨fun a b ↦ (hs s a b).mul (ht t a b), fun i ↦ ?_⟩
  let dirs : List V := (List.ofFn fun j ↦ List.replicate (i.2.1 j) (EuclideanSpace.single j 1,0)).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
  let l : List J := (List.ofFn fun j ↦ List.replicate (i.1 j) (Sum.inl j)).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.2 j) (Sum.inr j)).flatten
  obtain ⟨C,hC⟩ := hdiff dirs l s t
  refine lt_of_le_of_lt (b := ENNReal.ofReal C) (iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) ENNReal.ofReal_lt_top
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have hwgt : w l (elementaryCover u a b) = (∏ j, (u.1 j : ℂ)^i.1 j) * ∏ j, (a j : ℂ)^i.2.2.2 j := by
    simp [w,l,List.map_flatten,List.prod_flatten,List.map_ofFn, Function.comp_def,List.prod_ofFn,fiberCoord,elementaryCover]
  exact hwgt ▸ hC u a b

end Graph

private def fiberCoordHom {m n r : ℕ} {F : Type} [AddCommGroup F] (j : Fin m ⊕ Fin r) :
    ElementaryLieGroup m n r F →+ ℝ where
  toFun x := fiberCoord x j
  map_zero' := by cases j <;> simp [fiberCoord]
  map_add' x y := congrFun (fiberCoord_add x y) j

private theorem fiberCoordHom_continuous {m n r : ℕ} {F : Type} [AddCommGroup F] [TopologicalSpace F]
    (j : Fin m ⊕ Fin r) : Continuous (fiberCoordHom (n := n) (F := F) j) := by
  cases j with
  | inl i => exact (PiLp.continuous_apply 2 _ i).comp continuous_fst
  | inr i =>
    exact (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ℝ))).comp
      ((continuous_apply i).comp continuous_snd.snd.fst)

private theorem elementary_positive_test {m n r : ℕ} {F : Type} [AddCommGroup F] [TopologicalSpace F]
    [DiscreteTopology F] [Finite F] : ∃ s : ElementarySchwartz m n r F,
      ∀ x, ∃ t : ℝ, 0 < t ∧ s x = (t : ℂ) := by
  let E := ElementaryLieGroup m n r F
  let R (l : ℕ) := ElementaryLieGroup l 0 0 PUnit
  let p : E →+ R m := (AddMonoidHom.inl _ _).comp (AddMonoidHom.fst _ _)
  let lattice : E →+ EuclideanSpace ℝ (Fin r) :=
    { toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ (x.2.2.1 i : ℝ))
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by ext i; exact Int.cast_add .. }
  let q : E →+ R r := (AddMonoidHom.inl _ _).comp lattice
  have hp : Continuous p := continuous_fst.prodMk continuous_const
  have hq : Continuous q :=
    ((continuous_of_discreteTopology (f := fun z : Fin r → ℤ ↦ WithLp.toLp 2 (fun i ↦ (z i : ℝ)))).comp
      continuous_snd.snd.fst).prodMk continuous_const
  have hcoord (j : Fin m ⊕ Fin r) : ∃ (a : R m →+ ℝ) (b : R r →+ ℝ), Continuous a ∧ Continuous b ∧
      ∀ x, fiberCoord x j = a (p x) + b (q x) := by
    cases j with
    | inl i => exact ⟨fiberCoordHom (.inl i),0,fiberCoordHom_continuous _,continuous_zero,fun x ↦ (add_zero _).symm⟩
    | inr i => exact ⟨0,fiberCoordHom (.inl i),continuous_zero,fiberCoordHom_continuous _,fun x ↦ (zero_add _).symm⟩
  have hr (l : ℕ) : ∃ s : ElementarySchwartz l 0 0 PUnit, ∀ x, s x = (Real.exp (-‖x.1‖^2) : ℝ) := by
    obtain ⟨g,hg⟩ := exists_gaussian_schwartz (E := EuclideanSpace ℝ (Fin l)) 1 one_pos
    refine ⟨⟨_, (elementarySchwartzSubmodule_real_iff (g : _ → ℂ)).mpr ⟨g,rfl⟩⟩,fun x ↦ ?_⟩
    simpa using hg x.1
  obtain ⟨s,hs⟩ := hr m
  obtain ⟨t,ht⟩ := hr r
  refine ⟨⟨_,elementary_graph_mem p q hp hq hcoord s t⟩, fun x ↦
    ⟨Real.exp (-‖(p x).1‖^2) * Real.exp (-‖(q x).1‖^2), by positivity, ?_⟩⟩
  change s (p x)*t (q x) = _
  rw [hs,ht,Complex.ofReal_mul]

/-- Lift the vector and free lattice factors through an open quotient. The remaining
coordinates lie in the compact torus and finite factors. -/
private theorem elementary_split_noncompact {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    (p : ElementaryLieGroup m n r F →+ ElementaryLieGroup m' n' r' F')
    (hp : Continuous p) (ho : IsOpenMap p) (hs : Surjective p) :
    ∃ τ : ElementaryLieGroup m' n' r' F' →+ ElementaryLieGroup m n r F, Continuous τ ∧
      ∀ z, p (τ z) = (z.1,0,z.2.2.1,0) := by
  let A := ElementaryLieGroup m n r F
  let B := ElementaryLieGroup m' n' r' F'
  let q := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  obtain ⟨L,hL⟩ := elementary_linear_section (p.comp q) (hp.comp elementaryCoverZeroHom_continuous_isOpenMap.1)
    (ho.comp elementaryCoverZeroHom_continuous_isOpenMap.2)
  let v : EuclideanSpace ℝ (Fin m') →+ A :=
    q.comp ((L.comp (ContinuousLinearMap.inl ℝ _ _)).toLinearMap.toAddMonoidHom)
  have hv : Continuous v := elementaryCoverZeroHom_continuous_isOpenMap.1.comp
    (L.continuous.comp (ContinuousLinearMap.inl ℝ _ _).continuous)
  let j : (Fin r' → ℤ) →+ B := (AddMonoidHom.inr _ _).comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
  let b := Pi.basisFun ℤ (Fin r')
  choose w hw using fun i ↦ hs (j (b i))
  let k := (b.constr ℤ w).toAddMonoidHom
  have hk : p.comp k = j := by
    have he : (p.comp k).toIntLinearMap = j.toIntLinearMap := by
      apply b.ext
      intro i
      change p (b.constr ℤ w (b i)) = _
      rw [b.constr_basis]
      exact hw i
    exact DFunLike.ext _ _ fun z ↦ DFunLike.congr_fun he z
  let T : B →+ A := v.comp (AddMonoidHom.fst _ _) + k.comp ((AddMonoidHom.fst _ _).comp
    ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _)))
  refine ⟨T,(hv.comp continuous_fst).add ((continuous_of_discreteTopology (f := k)).comp continuous_snd.snd.fst),fun z ↦ ?_⟩
  change p (v z.1 + k z.2.2.1) = _
  rw [map_add, show p (k z.2.2.1) = _ from DFunLike.congr_fun hk z.2.2.1,
    show p (v z.1) = elementaryCover (z.1,0) 0 0 from hL _]
  simp [j,elementaryCover,Pi.zero_def]

/-- Split off the real and lattice factors, then normalize a positive test over the compact remainder. -/
private theorem elementary_fiberIntegral_lift {A B : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [MeasurableSpace A]
    [BorelSpace A] [CommGroup B] [TopologicalSpace B]
    (e : ElementaryLCAPresentation A) (e' : ElementaryLCAPresentation B)
    (p : A →* B) (hp : Continuous p) (ho : IsOpenMap p) (hs : Function.Surjective p)
    (ν : Measure p.ker) [ν.IsHaarMeasure] (s : SchwartzBruhatStage e') :
    ∃ t : SchwartzBruhatStage e, ∀ y : A,
      (∫ k : p.ker, t (e.equiv (y*k.val)).toAdd ∂ν) = s (e'.equiv (p y)).toAdd := by
  classical
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let E' := ElementaryLieGroup e'.realDim e'.torusDim e'.latticeRank e'.finiteFactor
  let C := ElementaryLieGroup 0 e'.torusDim 0 e'.finiteFactor
  let π : E →+ E' := AddMonoidHom.toMultiplicative.symm
    ((e'.equiv.toMonoidHom.comp p).comp e.equiv.symm.toMonoidHom)
  have hc : Continuous π := e'.equiv.continuous.comp (hp.comp e.equiv.symm.continuous)
  have hπ (y : A) : π (e.equiv y).toAdd = (e'.equiv (p y)).toAdd :=
    congrArg (fun x ↦ (e'.equiv (p x)).toAdd) (e.equiv.symm_apply_apply y)
  obtain ⟨τ,hτ,hsec⟩ := elementary_split_noncompact π hc
    (e'.equiv.isOpenMap.comp (ho.comp e.equiv.symm.isOpenMap)) (e'.equiv.surjective.comp (hs.comp e.equiv.symm.surjective))
  let r := AddMonoidHom.id E - τ.comp π
  have hr : Continuous r := continuous_id.sub (hτ.comp hc)
  let c : E' →+ C := {
    toFun z := (0,z.2.1,0,z.2.2.2)
    map_zero' := rfl
    map_add' _ _ := Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl)) }
  let j : C →+ E' := {
    toFun z := (0,z.2.1,0,z.2.2.2)
    map_zero' := rfl
    map_add' _ _ := Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl)) }
  have hc' : Continuous c := continuous_const.prodMk (continuous_snd.fst.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hj : Continuous j := continuous_const.prodMk (continuous_snd.fst.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hrπ (z : E) : π (r z) = j (c (π z)) := by
    change π (z-τ (π z)) = _
    rw [map_sub,hsec]
    exact Prod.ext (sub_self _) (Prod.ext (sub_zero _) (Prod.ext (sub_self _) (sub_zero _)))
  obtain ⟨θ,hθ⟩ := elementary_positive_test (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  obtain ⟨hint,η,hη⟩ := elementary_fiberIntegral e e' p hp ho hs ν θ
  have hne (z : E') : η z ≠ 0 := by
    obtain ⟨y,hy⟩ := hs (e'.equiv.symm (.ofAdd z))
    have hy' : (e'.equiv (p y)).toAdd = z := by rw [hy,e'.equiv.apply_symm_apply]; rfl
    rw [←hy',hη]
    let f (k : p.ker) := θ (e.equiv (y*k.val)).toAdd
    have hpos (k) : 0 < (f k).re := by
      obtain ⟨t,ht,he⟩ := hθ (e.equiv (y*k.val)).toAdd
      change 0 < (θ _).re
      rwa [he,Complex.ofReal_re]
    have h : 0 < ∫ k, (f k).re ∂ν := by
      apply (integral_pos_iff_support_of_nonneg (fun k ↦ (hpos k).le) (hint y).re).mpr
      rw [show support (fun k ↦ (f k).re) = univ from eq_univ_of_forall fun k ↦ (hpos k).ne']
      exact isOpen_univ.measure_pos ν univ_nonempty
    intro hz
    change 0 < ∫ k, RCLike.re (f k) ∂ν at h
    rw [integral_re (show Integrable f ν from hint y)] at h
    exact (ne_of_gt h) (congrArg Complex.re hz)
  let d (z : C) := (η (j z))⁻¹
  have hd : d ∈ elementarySchwartzSubmodule 0 e'.torusDim 0 e'.finiteFactor := by
    apply elementarySchwartz_of_compactSupport _ (HasCompactSupport.of_compactSpace _)
    exact fun a b ↦ (contDiff_comp_elementaryHom j hj η.property.1 a b).inv fun u ↦ hne _
  let d' : ElementarySchwartz 0 e'.torusDim 0 e'.finiteFactor := ⟨d,hd⟩
  have hs' : (fun z ↦ s z * d' (c z)) ∈
      elementarySchwartzSubmodule e'.realDim e'.torusDim e'.latticeRank e'.finiteFactor :=
    elementary_graph_mem (AddMonoidHom.id E') c continuous_id hc'
      (fun i ↦ ⟨fiberCoordHom i,0,fiberCoordHom_continuous _,continuous_zero, fun z ↦ (add_zero _).symm⟩) s d'
  let s' : SchwartzBruhatStage e' := ⟨_,hs'⟩
  have hcoord (i) : ∃ (a : E' →+ ℝ) (b : E →+ ℝ), Continuous a ∧ Continuous b ∧
      ∀ x, fiberCoord x i = a (π x) + b (r x) := by
    let b := fiberCoordHom (n := e.torusDim) (F := e.finiteFactor) i
    refine ⟨b.comp τ,b,(fiberCoordHom_continuous _).comp hτ,fiberCoordHom_continuous _,fun x ↦ ?_⟩
    change b x = b (τ (π x)) + b (x - τ (π x))
    rw [map_sub]; abel
  refine ⟨⟨_,elementary_graph_mem π r hc hr hcoord s' θ⟩, fun y ↦ ?_⟩
  let z := (e.equiv y).toAdd
  let z' := π z
  let y' := e.equiv.symm (.ofAdd (r z))
  have hkπ (k : p.ker) : π (e.equiv k.val).toAdd = 0 := by
    rw [hπ,show p k.val = 1 from k.property,map_one]
    rfl
  have hy' : (e.equiv y').toAdd = r z := congrArg Multiplicative.toAdd (e.equiv.apply_symm_apply _)
  have hpr : (e'.equiv (p y')).toAdd = j (c z') := (hπ y').symm.trans (hy' ▸ hrπ z)
  have hfun (k : p.ker) : s' (π (e.equiv (y*k.val)).toAdd) * θ (r (e.equiv (y*k.val)).toAdd) =
      s' z' * θ (e.equiv (y'*k.val)).toAdd := by
    rw [map_mul e.equiv y _, map_mul e.equiv y' _]
    change s' (π (z + (e.equiv k.val).toAdd)) * θ (r (z + (e.equiv k.val).toAdd)) = _ * θ ((e.equiv y').toAdd + _)
    rw [map_add, hkπ, add_zero, map_add,hy']
    have hrk : r (e.equiv k.val).toAdd = (e.equiv k.val).toAdd := by
      change (e.equiv k.val).toAdd - τ (π (e.equiv k.val).toAdd) = _
      rw [hkπ, map_zero,sub_zero]
    rw [hrk]
  change (∫ k : p.ker, s' (π (e.equiv (y*k.val)).toAdd) * θ (r (e.equiv (y*k.val)).toAdd) ∂ν) = _
  simp_rw [hfun,integral_const_mul, ← hη y',hpr,← hπ y]
  change (s z' * (η (j (c z')))⁻¹) * η (j (c z')) = s z'
  field_simp [hne]

section
variable {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H]

private theorem exists_good_subgroup_image_in_kernel (f : G →ₜ* H) (b : BruhatStructuralPair H) :
    ∃ k : Subgroup G, IsBruhatGoodSubgroup k ∧ k.map f.toMonoidHom ≤ OrderDual.ofDual b.val.2 := by
  let : LocallyCompactSpace b.val.1 := b.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : T1Space b.quotient := QuotientGroup.t1Space_iff.mpr (b.property.2.2.1.1.preimage continuous_subtype_val)
  obtain ⟨e⟩ := b.elementary
  obtain ⟨W,hW,hpowers⟩ := exists_nhds_one_of_isLocallyEuclidean (locallyEuclidean_of_elementaryPresentation e)
  let π : b.val.1 →* b.quotient := QuotientGroup.mk' _
  have hpre : π ⁻¹' W ∈ 𝓝 (1 : b.val.1) := QuotientGroup.continuous_mk.continuousAt.preimage_mem_nhds
    (by change W ∈ 𝓝 (π 1); rwa [map_one])
  have him : Subtype.val '' (π ⁻¹' W) ∈ 𝓝 (1 : H) :=
    b.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hpre
  obtain ⟨A,hA⟩ := exists_lcaDualAnnihilator_subset_nhds (f.continuous.continuousAt.preimage_mem_nhds
    (show Subtype.val '' (π ⁻¹' W) ∈ 𝓝 (f 1) by rwa [map_one]))
  let k := lcaDualAnnihilator A.val
  have hk : IsBruhatGoodSubgroup k := by
    refine ⟨(isCompact_lcaDualAnnihilator _ A.property.1).isClosed,?_⟩
    rw [show lcaAnnihilator k = A.val from lcaAnnihilator_dualAnnihilator_of_open _ A.property.1]
    exact A.property
  refine ⟨k,hk,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨y,_,hy⟩ := hA hx
  change (f x) ∈ OrderDual.ofDual b.val.2
  change y.val = f x at hy
  rw [←hy]
  apply (b.quotient_mk_eq_one y).mp
  apply hpowers
  intro n
  obtain ⟨z,hz,hz'⟩ := hA (k.pow_mem hx n)
  change z.val = f (x^n) at hz'
  have he : z = y^n := Subtype.ext (by simpa only [map_pow, Subgroup.coe_pow,hy] using hz')
  exact (show (QuotientGroup.mk y : b.quotient)^n = π z by rw [he,map_pow];rfl) ▸ hz

omit [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] in
private theorem exists_image_open_subgroup (p : G →ₜ* H) (hp : IsOpenQuotientMap p)
    (J : OpenCompactlyGeneratedSubgroups H) :
    ∃ L : OpenCompactlyGeneratedSubgroups G, J.val ≤ L.val.map p.toMonoidHom := by
  obtain ⟨C,_,hc,hgen⟩ := J.property.2
  let I := OpenCompactlyGeneratedSubgroups G
  let : IsDirectedOrder I := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  let : Nonempty I := ⟨((openCompactlyGeneratedSubgroups_colimit (G := G)).2.1 1).choose⟩
  let V (i : I) := p '' (i.val : Set G)
  have hcvr : Subtype.val '' C ⊆ ⋃ i, V i := by
    rintro _ ⟨x,_,rfl⟩
    obtain ⟨g,hg⟩ := hp.surjective x.val
    obtain ⟨i,hi⟩ := (openCompactlyGeneratedSubgroups_colimit (G := G)).2.1 g
    exact mem_iUnion.mpr ⟨i,g,hi,hg⟩
  obtain ⟨i,hi⟩ := (hc.image continuous_subtype_val).elim_directed_cover V
    (fun j ↦ hp.isOpenMap _ j.property.1) hcvr (directed_of_isDirected_le (fun _ _ h ↦ image_mono h))
  have hsub : C ⊆ ((i.val.map p.toMonoidHom).comap J.val.subtype : Set J.val) :=
    fun x hx ↦ hi ⟨x,hx,rfl⟩
  have htop : ⊤ ≤ (i.val.map p.toMonoidHom).comap J.val.subtype := hgen ▸ (Subgroup.closure_le _).mpr hsub
  exact ⟨i,fun x hx ↦ htop (Subgroup.mem_top ⟨x,hx⟩)⟩

private theorem exists_cofinal_image_stage (K : Subgroup G) (hK : IsClosed (K : Set G))
    (b : BruhatStructuralPair (G ⧸ K)) :
    ∃ a : BruhatStructuralPair G, b ≤ (bruhatStructuralPair_quotient_map K hK a).choose := by
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK
  let q : G →ₜ* G ⧸ K := ⟨QuotientGroup.mk' K,QuotientGroup.continuous_mk⟩
  obtain ⟨k,hk,hsmall⟩ := exists_good_subgroup_image_in_kernel q b
  obtain ⟨L,hL⟩ := exists_image_open_subgroup q QuotientGroup.isOpenQuotientMap_mk ⟨b.val.1,b.property.1,b.property.2.1⟩
  obtain ⟨M,hM⟩ := exists_openCompactlyGeneratedSubgroup_contains (isCompact_of_bruhatGoodSubgroup k hk)
  let := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  obtain ⟨J,hLJ,hMJ⟩ := exists_ge_ge L M
  let a : BruhatStructuralPair G := ⟨(J.val,OrderDual.toDual k),J.property.1,J.property.2,hk,hM.trans hMJ⟩
  refine ⟨a,?_,?_⟩
  · rw [(bruhatStructuralPair_quotient_map K hK a).choose_spec.1]
    exact hL.trans (Subgroup.map_mono hLJ)
  · change OrderDual.ofDual (bruhatStructuralPair_quotient_map K hK a).choose.val.2 ≤ _
    rw [(bruhatStructuralPair_quotient_map K hK a).choose_spec.2]
    exact hsmall

end

private theorem cosetIntegral_local_lift {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (μK : Measure K) [μK.IsHaarMeasure] [μK.Regular] (hK : IsClosed (K : Set G))
    (a : BruhatStructuralPair G) (b : BruhatStructuralPair (G ⧸ K))
    (hJ : b.val.1 = a.val.1.map (QuotientGroup.mk' K))
    (hk : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K))
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient) (s : SchwartzBruhatStage d) :
    ∃ t : SchwartzBruhatStage e, ∀ (y : G) (_hy : y ∈ a.val.1) (hz : QuotientGroup.mk y ∈ b.val.1),
      (∫ k : K, schwartzBruhatStageRealization a e t (y*k.val) ∂μK) =
        s (d.equiv (QuotientGroup.mk ⟨QuotientGroup.mk y,hz⟩)).toAdd := by
  classical
  let : IsClosed (K : Set G) := hK
  let H := a.val.1
  let C := OrderDual.ofDual a.val.2
  let : LocallyCompactSpace H := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : MeasurableSpace a.quotient := borel _
  let : BorelSpace a.quotient := ⟨rfl⟩
  let N := C.comap H.subtype
  let : IsClosed (N : Set H) := a.property.2.2.1.1.preimage continuous_subtype_val
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.mpr (inferInstance : IsClosed (N : Set H))
  let q : H →* a.quotient := QuotientGroup.mk' N
  have hqc : IsCompact (q.ker : Set H) := by
    rw [QuotientGroup.ker_mk']
    exact (H.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_of_bruhatGoodSubgroup C a.property.2.2.1)
  let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : LocallyCompactSpace a.quotient := inferInstanceAs (LocallyCompactSpace (H ⧸ N))
  let : T2Space a.quotient := inferInstanceAs (T2Space (H ⧸ N))
  obtain ⟨p,hp,ho,hs,hker,hmk⟩ := a.exists_quotient_hom K b hJ hk
  obtain ⟨ν,hν,hfib⟩ := exists_haar_fiberIntegral_eq (A := a.quotient) K μK hK H a.property.1 q QuotientGroup.continuous_mk
    QuotientGroup.isOpenMap_coe (QuotientGroup.mk'_surjective N) hqc p.ker hker
  let : ν.IsHaarMeasure := hν
  have hLift := elementary_fiberIntegral_lift (A := a.quotient) (B := b.quotient) e d p hp ho hs ν s
  obtain ⟨t,ht⟩ := hLift
  refine ⟨t, fun y hy hz ↦ ?_⟩
  let v : H := ⟨y,hy⟩
  let f (x : a.quotient) := t (e.equiv x).toAdd
  have hc : Continuous f := (elementarySchwartz_continuousFunction t).comp e.equiv.continuous
  have hi := (hfib f hc v).2
  have he (k : K) : schwartzBruhatStageRealization a e t (y*k.val) =
      if h : y*k.val ∈ H then f (q ⟨_,h⟩) else 0 := by
    rw [schwartzBruhatStageRealization_apply]
    rfl
  simp_rw [he]
  exact hi.trans ((ht (q v)).trans (congrArg (fun w ↦ s (d.equiv w).toAdd) (hmk y hy hz)))

private theorem cosetIntegral_lift_stage {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (μK : Measure K) [μK.IsHaarMeasure] [μK.Regular] (hK : IsClosed (K : Set G))
    (a : BruhatStructuralPair G) (b : BruhatStructuralPair (G ⧸ K))
    (hJ : b.val.1 = a.val.1.map (QuotientGroup.mk' K))
    (hk : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).map (QuotientGroup.mk' K))
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient) (s : SchwartzBruhatStage d) :
    ∃ f : SchwartzBruhat G, (schwartzBruhatCosetIntegral K μK hK f).val = schwartzBruhatStageRealization b d s := by
  classical
  let : IsClosed (K : Set G) := hK
  obtain ⟨t,ht⟩ := cosetIntegral_local_lift K μK hK a b hJ hk e d s
  let T : SchwartzBruhat G := schwartzBruhatStageInclusion a e t
  refine ⟨T,funext fun z ↦ ?_⟩
  by_cases hz : z ∈ b.val.1
  · have hzmap : z ∈ a.val.1.map (QuotientGroup.mk' K) := hJ ▸ hz
    obtain ⟨y,hy,hyz⟩ := hzmap
    change (QuotientGroup.mk y : G ⧸ K) = z at hyz
    subst z
    refine (schwartzBruhatCosetIntegral_mk K μK hK T y).trans ((ht y hy hz).trans ?_)
    exact ((schwartzBruhatStageRealization_apply b d s _).trans (dite_eq_left hz)).symm
  · obtain ⟨y,hyz⟩ := QuotientGroup.mk'_surjective K z
    change (QuotientGroup.mk y : G ⧸ K) = z at hyz
    subst z
    have hzero (k : K) : T (y*k.val) = 0 := by
      refine (schwartzBruhatStageRealization_apply a e t _).trans (dite_eq_right ?_)
      intro h
      apply hz
      rw [hJ]
      exact ⟨y*k.val,h,by simp⟩
    refine (schwartzBruhatCosetIntegral_mk K μK hK T y).trans (Eq.trans ?_
      (((schwartzBruhatStageRealization_apply b d s _).trans (dite_eq_right hz)).symm))
    simp_rw [hzero,integral_zero]

end CosetLifts

/-- Paper: Theorem D.1.7.1(2), p. 776. Every Schwartz–Bruhat function on the
quotient is the coset integral of a Schwartz–Bruhat function on the group. -/
theorem schwartzBruhatCosetIntegral_surjective :
    Function.Surjective (schwartzBruhatCosetIntegral K μK hK) := by
  intro s
  let : IsClosed (K : Set G) := hK
  obtain ⟨b,d,t,ht⟩ := (mem_schwartzBruhatSubmodule_iff s.val).mp s.property
  obtain ⟨a,ha⟩ := exists_cofinal_image_stage K hK b
  let hex := bruhatStructuralPair_quotient_map K hK a
  obtain ⟨e⟩ := hex.choose.elementary
  obtain ⟨j,hj,_⟩ := schwartzBruhatStage_transition ha d e
  obtain ⟨e₀⟩ := a.elementary
  obtain ⟨f,hf⟩ := cosetIntegral_lift_stage K μK hK a hex.choose hex.choose_spec.1 hex.choose_spec.2 e₀ e (j t)
  exact ⟨f,Subtype.ext (hf.trans ((hj t).trans ht))⟩

omit hK hHaarK hRegularK hBorel hTop hT2 hLC in
/-- An embedded Fréchet stage gives its range the same additive uniformity. -/
private theorem frechet_range_of_embedding {X E : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] [PolynormableSpace ℂ E] (i : X →L[ℂ] E) (hi : IsEmbedding i)
    (hX : IsFrechetTVS X) : IsFrechetTVS i.range := by
  obtain ⟨_, _, hmetr, hcomp⟩ := hX
  have he : IsEmbedding i.rangeRestrict := IsEmbedding.subtypeVal.of_comp_iff.mp hi
  have hs : Function.Surjective i.rangeRestrict := fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩
  let m := (Equiv.ofBijective i.rangeRestrict ⟨he.injective, hs⟩).toHomeomorphOfIsInducing he.isInducing
  refine ⟨inferInstance, inferInstance, m.symm.isEmbedding.metrizableSpace, ?_⟩
  let : UniformSpace i.range := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup i.range := isUniformAddGroup_of_addCommGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq] at hcomp
  exact ((AddMonoidHom.isUniformInducing_of_isInducing (f := i.rangeRestrict) he.isInducing).completeSpace_congr hs).mp hcomp

omit hK hHaarK hRegularK hBorel hTop hT2 hLC in
/-- Using the embedded ranges puts the Fréchet stages in the universe of the limit. -/
private theorem isLFSpace_of_embedded_stages {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, UniformSpace (X n)] [∀ n, IsUniformAddGroup (X n)]
    (j : ∀ n, X n →L[ℂ] X (n+1)) (i : ∀ n, X n →L[ℂ] E) (h : IsInjectiveLCLimit j i)
    (he : ∀ n, IsEmbedding (i n)) (hX : ∀ n, IsFrechetTVS (X n)) : IsLFSpace E := by
  apply (lfSpace_quotient_properties (E := E)).1
  refine ⟨inferInstance, fun n ↦ (i n).range, monotone_nat_of_le_succ (fun n x hx ↦ ?_),
    fun n ↦ frechet_range_of_embedding (i n) (he n) (hX n), h.exhaustive, ?_⟩
  · obtain ⟨v, rfl⟩ := hx
    exact ⟨j n v, DFunLike.congr_fun (h.compatible n) v⟩
  · refine h.topology_eq.trans (congrArg (fun P : Seminorm ℂ E → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology) ?_)
    funext p
    apply propext
    apply forall_congr'
    intro n
    have hi : IsEmbedding (i n).rangeRestrict := IsEmbedding.subtypeVal.of_comp_iff.mp (he n)
    have hs : Function.Surjective (i n).rangeRestrict := fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩
    exact (hi.isInducing.isOpenQuotientMap_of_surjective hs).isQuotientMap.continuous_iff
      (g := p ∘ (i n).range.subtype) |>.symm

omit hK hHaarK hRegularK hBorel [MeasurableSpace G] in
/-- A cofinal sequence of structural stages presents the Schwartz–Bruhat space as LF. -/
private theorem schwartzBruhat_isLF [SecondCountableTopology G] : IsLFSpace (SchwartzBruhat G) := by
  classical
  let E := SchwartzBruhat G
  let : T2Space E := schwartzBruhat_t2
  obtain ⟨a, e, j, _, hcof, hj, _⟩ := schwartzBruhat_exists_topologicallyExact (G := G)
  let i (n : ℕ) : SchwartzBruhatStage (e n) →L[ℂ] E :=
    ⟨schwartzBruhatStageInclusion (a n) (e n), (schwartzBruhatStage_isEmbedding _ _).continuous⟩
  have hFac (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) :
      ∃ n, ∃ k : SchwartzBruhatStage d →L[ℂ] SchwartzBruhatStage (e n),
        ∀ x, i n (k x) = schwartzBruhatStageInclusion b d x := by
    let n := (hcof b).choose
    have h := schwartzBruhatStage_transition (hcof b).choose_spec d (e n)
    exact ⟨n, h.choose, fun x ↦ Subtype.ext (h.choose_spec.1 x)⟩
  refine isLFSpace_of_embedded_stages (X := fun n ↦ SchwartzBruhatStage (e n)) j i ?_ (fun n ↦ schwartzBruhatStage_isEmbedding _ _)
    (fun n ↦ elementarySchwartz_isFrechet)
  refine ⟨fun n ↦ (schwartzBruhatStage_isEmbedding (a n) (e n)).injective,
    fun n ↦ ContinuousLinearMap.ext (fun x ↦ Subtype.ext (hj n x)), ?_, ?_⟩
  · intro x
    exact ((mem_schwartzBruhatSubmodule_iff x.val).mp x.property).elim fun b hb ↦
      hb.elim fun d hd ↦ hd.elim fun v hv ↦ (hFac b d).elim fun n hn ↦ hn.elim fun k hk ↦
        ⟨n, k v, (hk v).trans (Subtype.ext hv)⟩
  · apply congrArg (fun P : Seminorm ℂ E → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ E)).topology)
    funext p
    exact propext ⟨fun h n ↦ h (a n) (e n), fun h b d ↦ by
      exact (hFac b d).elim fun n hn ↦ hn.elim fun k hk ↦
        ((h n).comp k.continuous).congr fun x ↦ congrArg p (hk x)⟩

omit hK hHaarK hRegularK hBorel hTop hT2 hLC in
/-- Apply the LF open mapping theorem to a map represented by a continuous linear surjection. -/
private theorem quotientMap_of_LF_surjection {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [AddCommGroup F]
    [Module ℂ F] [TopologicalSpace F] (hE : IsLFSpace E) (hF : IsLFSpace F)
    (f : E → F) (hf : ∃ P : E →L[ℂ] F, ∀ x, P x = f x) (hs : Function.Surjective f) :
    IsQuotientMap f := by
  obtain ⟨P, hP⟩ := hf
  have heq : ⇑P = f := funext hP
  subst f
  obtain ⟨_, X, _, _, _, hX, j, i, h⟩ := hE
  exact (isOpenMap_of_surjective_toLF hF hX i (fun n ↦ by
    rintro _ ⟨v, rfl⟩
    exact ⟨j n v, DFunLike.congr_fun (h.compatible n) v⟩) h.exhaustive P hs).isQuotientMap
      P.continuous hs

/-- Paper: Theorem D.1.7.1(2), p. 776. Under second countability the coset
integral is a topological quotient map. -/
theorem schwartzBruhatCosetIntegral_isQuotientMap [SecondCountableTopology G] :
    IsQuotientMap (schwartzBruhatCosetIntegral K μK hK) := by
  let : T1Space (G ⧸ K) := QuotientGroup.t1Space_iff.mpr hK
  let : ContinuousSMul ℂ (SchwartzBruhat G) := (withGeneratingSeminorms_spec _ _).continuousSMul
  exact quotientMap_of_LF_surjection (schwartzBruhat_isLF (G := G))
    (schwartzBruhat_isLF (G := G ⧸ K)) _ (schwartzBruhatCosetIntegral_continuousLinear K μK hK)
    (schwartzBruhatCosetIntegral_surjective K μK hK)

end AveragingAndFourier

section DistributionKernels

open UniformSpace Function Bornology
open scoped Pointwise ComplexOrder

section StageTensors

variable {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H]

private theorem exists_stage_for_map {L : Type*} [CommGroup L] [TopologicalSpace L] [IsTopologicalGroup L]
    [T2Space L] [LocallyCompactSpace L] (f : G →ₜ* H) (b : BruhatStructuralPair H)
    (g : L →ₜ* G) (hL : IsCompactlyGeneratedGroup L) :
    ∃ a : BruhatStructuralPair G, (∀ l, g l ∈ a.val.1) ∧
      (OrderDual.ofDual a.val.2).map f.toMonoidHom ≤ OrderDual.ofDual b.val.2 := by
  obtain ⟨k,hk,hsmall⟩ := exists_good_subgroup_image_in_kernel f b
  obtain ⟨C,_,hc,hgen⟩ := hL
  obtain ⟨J,hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains
    ((hc.image g.continuous).union (isCompact_of_bruhatGoodSubgroup k hk))
  have hkJ : k ≤ J.val := fun x hx ↦ hJ (Or.inr hx)
  have hsub : C ⊆ (J.val.comap g.toMonoidHom : Set L) := fun x hx ↦ hJ (Or.inl ⟨x,hx,rfl⟩)
  have htop : ⊤ ≤ J.val.comap g.toMonoidHom := hgen ▸ (Subgroup.closure_le _).mpr hsub
  exact ⟨⟨(J.val,OrderDual.toDual k),J.property.1,J.property.2,hk,hkJ⟩,fun x ↦ htop (Subgroup.mem_top x),hsmall⟩

private theorem exists_rectangular_stage_bounds (a : BruhatStructuralPair (G × H)) :
    ∃ (u : BruhatStructuralPair G) (v : BruhatStructuralPair H),
      a.val.1 ≤ u.val.1.prod v.val.1 ∧
        (OrderDual.ofDual u.val.2).prod (OrderDual.ofDual v.val.2) ≤ OrderDual.ofDual a.val.2 := by
  let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let left : a.val.1 →ₜ* G := ⟨(MonoidHom.fst G H).comp a.val.1.subtype,continuous_fst.comp continuous_subtype_val⟩
  let right : a.val.1 →ₜ* H := ⟨(MonoidHom.snd G H).comp a.val.1.subtype,continuous_snd.comp continuous_subtype_val⟩
  obtain ⟨u,hJ,hk⟩ := exists_stage_for_map (ContinuousMonoidHom.inl G H) a left a.property.2.1
  obtain ⟨v,hL,hl⟩ := exists_stage_for_map (ContinuousMonoidHom.inr G H) a right a.property.2.1
  refine ⟨u,v,fun x hx ↦ ⟨hJ ⟨x,hx⟩,hL ⟨x,hx⟩⟩,?_⟩
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  have h₁ : (x,1) ∈ OrderDual.ofDual a.val.2 := hk ⟨x,hx,rfl⟩
  have h₂ : (1,y) ∈ OrderDual.ofDual a.val.2 := hl ⟨y,hy,rfl⟩
  simpa using (OrderDual.ofDual a.val.2).mul_mem h₁ h₂

private def completedInductiveMap {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [PolynormableSpace ℂ C] [T2Space C]
    [AddCommGroup D] [Module ℂ D] [TopologicalSpace D] [PolynormableSpace ℂ D] [T2Space D]
    (f : A →L[ℂ] C) (g : B →L[ℂ] D) :
    Completion (InductiveTensor A B) →L[ℂ] Completion (InductiveTensor C D) :=
  (show InductiveTensor A B →L[ℂ] InductiveTensor C D from
    ⟨inductiveTensorMap f.toLinearMap g.toLinearMap,inductiveTensorMap_continuous f g⟩).completion

private theorem completedInductiveMap_pure {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [PolynormableSpace ℂ C] [T2Space C]
    [AddCommGroup D] [Module ℂ D] [TopologicalSpace D] [PolynormableSpace ℂ D] [T2Space D]
    (f : A →L[ℂ] C) (g : B →L[ℂ] D) (x : A) (y : B) :
    completedInductiveMap f g (Completion.coe' (α := InductiveTensor A B) (x ⊗ₜ[ℂ] y)) =
      Completion.coe' (α := InductiveTensor C D) (f x ⊗ₜ[ℂ] g y) :=
  ContinuousLinearMap.completion_apply_coe _ _

private theorem stageTensor_change {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    (ha : IsFrechetTVS A) (hb : IsFrechetTVS B) :
    ∃ e : Completion (InductiveTensor A B) ≃L[ℂ] Completion (ProjectiveTensor A B), ∀ (x : A) (y : B),
      e (Completion.coe' (α := InductiveTensor A B) (x ⊗ₜ[ℂ] y)) =
        Completion.coe' (α := ProjectiveTensor A B) (x ⊗ₜ[ℂ] y) := by
  let L : InductiveTensor A B →L[ℂ] ProjectiveTensor A B := ⟨LinearMap.id, continuous_inductiveTensor_to_projectiveTensor⟩
  have he : IsHomeomorph L.completion := completedInductiveTensor_to_projectiveTensor_of_frechet ha hb
  exact ⟨ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective L.completion.toLinearMap he.bijective) he,
    fun x y ↦ L.completion_apply_coe (show InductiveTensor A B from x ⊗ₜ[ℂ] y)⟩

end StageTensors

section ElementarySlices

variable {m n r m₁ n₁ r₁ m₂ n₂ r₂ : ℕ} {F F₁ F₂ : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F₁] [TopologicalSpace F₁] [DiscreteTopology F₁] [Finite F₁]
    [AddCommGroup F₂] [TopologicalSpace F₂] [DiscreteTopology F₂] [Finite F₂]
local notation "Z" => ElementaryLieGroup m n r F
local notation "X" => ElementaryLieGroup m₁ n₁ r₁ F₁
local notation "Y" => ElementaryLieGroup m₂ n₂ r₂ F₂
local notation "SZ" => ElementarySchwartz m n r F
local notation "SX" => ElementarySchwartz m₁ n₁ r₁ F₁
local notation "SY" => ElementarySchwartz m₂ n₂ r₂ F₂
local notation "VX" => EuclideanSpace ℝ (Fin m₁) × EuclideanSpace ℝ (Fin n₁)

private theorem slice_smooth (p : X →+ Z) (hp : Continuous p) (s : SZ) (z : Z) (a : Fin r₁ → ℤ) (b : F₁) :
    ContDiff ℝ ∞ (fun u ↦ s (p (elementaryCover u a b) + z)) := by
  apply contDiff_comp_elementaryHom p hp (f := fun v ↦ s (v+z)) _ a b
  intro c d
  obtain ⟨w,hw⟩ := elementaryCover_surjective z.2.2.1 z.2.2.2 z.1 z.2.1
  have he (u) : elementaryCover u c d + z = elementaryCover (u+(z.1,w)) (c+z.2.2.1) (d+z.2.2.2) := by
    change elementaryCover (z.1,w) z.2.2.1 z.2.2.2 = z at hw
    conv_lhs => rw [← hw]
    rw [elementaryCover_add]
  simp_rw [he]
  exact (s.property.1 _ _).comp (contDiff_id.add contDiff_const)

/-- Differentiating a slice in a fixed list of directions differentiates the same ambient
test for every translate. -/
private theorem slice_derivatives (p : X →+ Z) (hp : Continuous p) (dirs : List VX) (s : SZ) :
    ∃ t : SZ, ∀ (z : Z) a b u,
      iteratedFDeriv ℝ dirs.length (fun w ↦ s (p (elementaryCover w a b) + z)) u dirs.get =
        t (p (elementaryCover u a b) + z) := by
  induction dirs using List.reverseRecOn generalizing s with
  | nil => exact ⟨s,fun _ _ _ _ ↦ by simp⟩
  | append_singleton dirs v ih =>
    let l := (ContinuousLinearMap.id ℝ ℝ).smulRight v
    let q := elementaryCoverZeroHom (m := m₁) (n := n₁) (r := r₁) (F := F₁)
    let c := p.comp (q.comp l.toLinearMap.toAddMonoidHom)
    obtain ⟨D,hD⟩ := elementarySchwartz_orbitDeriv c (hp.comp (elementaryCoverZeroHom_continuous_isOpenMap.1.comp l.continuous))
    obtain ⟨t,ht⟩ := ih (D s)
    refine ⟨t,fun z a b u ↦ ?_⟩
    have hs := slice_smooth p hp s z a b
    have hder (w : VX) : fderiv ℝ (fun v ↦ s (p (elementaryCover v a b) + z)) w v = D s (p (elementaryCover w a b) + z) := by
      have hline : HasDerivAt (fun k : ℝ ↦ w + k • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
      have h := ((hs.differentiable (by simp) w).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp))
      have he (k : ℝ) : p (elementaryCover w a b) + z + c k = p (elementaryCover (w+k•v) a b) + z := by
        change _ + z + p (elementaryCover (k•v) 0 0) = _
        rw [add_right_comm,←map_add,elementaryCover_add,add_zero,add_zero]
      have h' := hD s (p (elementaryCover w a b) + z)
      simp_rw [he] at h'
      exact h.unique h'
    rw [iteratedFDeriv_append_singleton hs,funext hder]
    exact ht z a b u

private theorem slice_partial (e : X × Y ≃ₜ+ Z) (s : SZ) (β : Fin m₁ → ℕ) (γ : Fin n₁ → ℕ) :
    ∃ t : SZ, ∀ (y : Y) u a b,
      elementaryPartial (fun x ↦ s (e (x,y))) β γ u a b = t (e (elementaryCover u a b,y)) := by
  let p := e.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl X Y)
  let dirs : List VX := (List.ofFn fun i ↦ List.replicate (β i) (EuclideanSpace.single i 1,0)).flatten ++
    (List.ofFn fun i ↦ List.replicate (γ i) (0,EuclideanSpace.single i 1)).flatten
  obtain ⟨t,ht⟩ := slice_derivatives p (e.continuous.comp (continuous_id.prodMk continuous_const)) dirs s
  have he (x : X) (y : Y) : p x + e (0,y) = e (x,y) := by
    change e (x,0) + e (0,y) = _
    rw [←map_add]; simp
  refine ⟨t,fun y u a b ↦ ?_⟩
  simpa only [elementaryPartial,dirs,he] using ht (e (0,y)) a b u

private def sliceWeight {m n r : ℕ} {F : Type} (i : ElementarySchwartzIndex m n r)
    (y : ElementaryLieGroup m n r F) := elementarySchwartzMonomial i.1 i.2.2.2 y.1 y.2.2.1

private theorem weight_of_hom (p : Z →+ X) (hp : Continuous p) (i : ElementarySchwartzIndex m₁ n₁ r₁) :
    ∃ P : MvPolynomial (Fin m ⊕ Fin r) ℂ, ∀ z : Z,
      MvPolynomial.eval (Sum.elim (fun j ↦ (z.1 j : ℂ)) (fun j ↦ (z.2.2.1 j : ℂ))) P = sliceWeight i (p z) := by
  choose P hP using fun j : Fin m₁ ⊕ Fin r₁ ↦ elementary_real_hom_polynomial ((fiberCoordHom j).comp p)
    ((fiberCoordHom_continuous j).comp hp)
  refine ⟨(∏ j, (P (.inl j))^(i.1 j)) * ∏ j, (P (.inr j))^(i.2.2.2 j),fun z ↦ ?_⟩
  simp [sliceWeight,elementarySchwartzMonomial,hP,fiberCoordHom,fiberCoord]

/-- All rows of a fixed test, multiplied by any fixed weight in the column variables,
lie in a bounded subset of the row Schwartz space. -/
private theorem bounded_weighted_rows (e : X × Y ≃ₜ+ Z) (s : SZ) (j : ElementarySchwartzIndex m₂ n₂ r₂) :
    ∃ T : Y → SX, (∀ y x, T y x = sliceWeight j y * s (e (x,y))) ∧ IsVonNBounded ℂ (range T) := by
  let p := (AddMonoidHom.fst X Y).comp e.symm.toAddEquiv.toAddMonoidHom
  let q := (AddMonoidHom.snd X Y).comp e.symm.toAddEquiv.toAddMonoidHom
  let k := e.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inl X Y)
  have hk : Continuous k := e.continuous.comp (continuous_id.prodMk continuous_const)
  let row (y : Y) (x : X) := s (e (x,y))
  have hrow (y : Y) (a : Fin r₁ → ℤ) (b : F₁) : ContDiff ℝ ∞ (fun u ↦ row y (elementaryCover u a b)) := by
    have he (x : X) : k x + e (0,y) = e (x,y) := by change e (x,0) + e (0,y) = _; rw [←map_add]; simp
    simpa only [he] using slice_smooth k hk s (e (0,y)) a b
  let f (y : Y) := sliceWeight j y • row y
  have hf (i : ElementarySchwartzIndex m₁ n₁ r₁) : ∃ C : ℝ, ∀ y, elementarySchwartzBound (f y) i ≤ ENNReal.ofReal C := by
    obtain ⟨t,ht⟩ := slice_partial e s i.2.1 i.2.2.1
    obtain ⟨P,hP⟩ := weight_of_hom p (continuous_fst.comp e.symm.continuous) i
    obtain ⟨Q,hQ⟩ := weight_of_hom q (continuous_snd.comp e.symm.continuous) j
    obtain ⟨C,hC⟩ := polynomial_weight_bounded (P*Q) t
    refine ⟨C,fun y ↦ iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    let x : X := elementaryCover u a b
    have h := hC (e (x,y))
    rw [MvPolynomial.eval_mul,hP,hQ,show p (e (x,y)) = x from congrArg Prod.fst (e.symm_apply_apply _),
      show q (e (x,y)) = y from congrArg Prod.snd (e.symm_apply_apply _),mul_assoc] at h
    rw [show elementaryPartial (f y) _ _ u a b = sliceWeight j y * t (e (x,y)) from
      (elementaryPartial_smul _ (hrow y) _ _ u a b).trans (congrArg (sliceWeight j y * ·) (ht y u a b))]
    exact h
  let T (y : Y) : SX := ⟨f y,fun a b ↦ contDiff_const.mul (hrow y a b),fun i ↦ (hf i).choose_spec y |>.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨T,fun _ _ ↦ rfl,elementarySchwartz_withSeminorms.isVonNBounded_iff_seminorm_bounded.mpr fun i ↦ ?_⟩
  refine ⟨(ENNReal.ofReal (hf i).choose).toReal + 1,by positivity,?_⟩
  rintro _ ⟨y,rfl⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ((hf i).choose_spec y)).trans_lt (lt_add_one _)

private def elementaryJet (i : ElementarySchwartzIndex m₂ n₂ r₂)
    (u : EuclideanSpace ℝ (Fin m₂) × EuclideanSpace ℝ (Fin n₂)) (a : Fin r₂ → ℤ) (b : F₂) : SY →ₗ[ℂ] ℂ where
  toFun t := sliceWeight i (elementaryCover u a b) * elementaryPartial t.val i.2.1 i.2.2.1 u a b
  map_add' s t := by
    change _ * elementaryPartial (s.val+t.val) _ _ _ _ _ = _
    rw [elementaryPartial_add s.property.1 t.property.1,mul_add]
  map_smul' c s := by
    change _ * elementaryPartial (c • s.val) _ _ _ _ _ = _
    rw [elementaryPartial_smul c s.property.1]
    simp only [RingHom.id_apply,smul_eq_mul]
    ring

private def elementaryDelta (x : X) : StrongDual ℂ SX := (elementarySchwartz_eval x).choose

private theorem elementaryDelta_apply (x : X) (s : SX) : elementaryDelta x s = s x :=
  (elementarySchwartz_eval x).choose_spec s

private theorem elementaryDelta_dense :
    DenseRange (Submodule.span ℂ (range (elementaryDelta (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁)))).subtypeL := by
  let : T2Space SX := elementarySchwartz_t2
  let D := StrongDual ℂ SX
  let V := Submodule.span ℂ (range (elementaryDelta (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁)))
  let : Module ℝ D := Module.restrictScalars ℝ ℂ D
  let : IsScalarTower ℝ ℂ D := IsScalarTower.restrictScalars ℝ ℂ D
  let : PolynormableSpace ℂ D := uniformConvergenceCLM_polynormable (F := ℂ) _ (fun _ h ↦ h)
    (by rw [sUnion_isVonNBounded_eq_univ,Submodule.span_univ]; simp)
  let : LocallyConvexSpace ℝ D := (PolynormableSpace.withSeminorms ℂ D).toLocallyConvexSpace
  intro L
  rw [show range V.subtypeL = (V : Set D) from Subtype.range_coe]
  by_contra hn
  obtain ⟨φ,hne,hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem V.topologicalClosure V.isClosed_topologicalClosure hn
  obtain ⟨e,he⟩ := elementarySchwartz_reflexive (m := m₁) (n := n₁) (r := r₁) (F := F₁)
  obtain ⟨s,rfl⟩ := e.surjective φ
  have hs : s = 0 := by
    apply Subtype.ext
    funext x
    exact (elementaryDelta_apply x s).symm.trans ((he s (elementaryDelta x)).symm.trans
      (hzero _ (V.le_topologicalClosure (Submodule.subset_span (mem_range_self x)))))
  exact hne (by rw [hs,map_zero]; rfl)

/-- The weighted rows of a product test let a distribution on the first factor act on
its slices, producing a Schwartz test on the second factor. -/
private theorem elementary_kernel_operator (e : X × Y ≃ₜ+ Z) (s : SZ) :
    ∃ T : StrongDual ℂ SX →L[ℂ] SY, ∀ x y, T (elementaryDelta x) y = s (e (x,y)) := by
  classical
  let flip : Y × X ≃ₜ+ Z := (show Y × X ≃ₜ+ X × Y from ⟨AddEquiv.prodComm,continuous_swap,continuous_swap⟩).trans e
  have hf (y : Y) (x : X) : flip (y,x) = e (x,y) := rfl
  let zeroX : ElementarySchwartzIndex m₁ n₁ r₁ := (0,0,0,0)
  let zeroY : ElementarySchwartzIndex m₂ n₂ r₂ := (0,0,0,0)
  obtain ⟨row,hrow,_⟩ := bounded_weighted_rows e s zeroY
  obtain ⟨col,hcol,_⟩ := bounded_weighted_rows flip s zeroX
  have hr (y : Y) (x : X) : row y x = s (e (x,y)) := by simpa [sliceWeight,elementarySchwartzMonomial,zeroY] using hrow y x
  have hc (x : X) (y : Y) : col x y = s (e (x,y)) := by simpa [sliceWeight,elementarySchwartzMonomial,zeroX,hf] using hcol x y
  let VX₂ := EuclideanSpace ℝ (Fin m₂) × EuclideanSpace ℝ (Fin n₂)
  let U := VX₂ × (Fin r₂ → ℤ) × F₂
  let jet (i : ElementarySchwartzIndex m₂ n₂ r₂) (u : U) := elementaryJet i u.1 u.2.1 u.2.2
  have hjet (i : ElementarySchwartzIndex m₂ n₂ r₂) :
      ∃ B : U → SX, IsVonNBounded ℂ (range B) ∧ ∀ u x, B u x = jet i u (col x) := by
    obtain ⟨t,ht⟩ := slice_partial flip s i.2.1 i.2.2.1
    obtain ⟨S,hS,hB⟩ := bounded_weighted_rows e t i
    let y (u : U) : Y := elementaryCover u.1 u.2.1 u.2.2
    refine ⟨fun u ↦ S (y u),hB.subset (range_comp_subset_range _ _),fun u x ↦ ?_⟩
    rw [hS]
    change _ = _ * elementaryPartial (col x).val _ _ _ _ _
    rw [show (col x).val = fun y ↦ s (flip (y,x)) from funext (hc x),ht,hf]
  choose B hB hjet using hjet
  let V := Submodule.span ℂ (range (elementaryDelta (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁)))
  have hliftAux (L : StrongDual ℂ SX) (hL : L ∈ V) : ∃ t : SY, (∀ y, t y = L (row y)) ∧ ∀ i u, jet i u t = L (B i u) := by
    induction hL using Submodule.span_induction with
    | mem l h =>
      obtain ⟨x,rfl⟩ := h
      exact ⟨col x,fun y ↦ (hc x y).trans ((hr y x).symm.trans (elementaryDelta_apply x _).symm),
        fun i u ↦ (hjet i u x).symm.trans (elementaryDelta_apply x _).symm⟩
    | zero => exact ⟨0,fun _ ↦ rfl,fun i u ↦ (jet i u).map_zero⟩
    | add l k _ _ hl hk =>
      obtain ⟨t,ht,hj⟩ := hl
      obtain ⟨w,hw,hk⟩ := hk
      exact ⟨t+w,fun y ↦ congrArg₂ (·+·) (ht y) (hw y),
        fun i u ↦ ((jet i u).map_add _ _).trans (congrArg₂ (·+·) (hj i u) (hk i u))⟩
    | smul c l _ hl =>
      obtain ⟨t,ht,hj⟩ := hl
      exact ⟨c • t,fun y ↦ congrArg (c • ·) (ht y),
        fun i u ↦ ((jet i u).map_smul c _).trans (congrArg (c • ·) (hj i u))⟩
  let hlift (L : V) := hliftAux L.val L.property
  let T : V →ₗ[ℂ] SY :=
    { toFun := fun L ↦ (hlift L).choose
      map_add' := fun L M ↦ Subtype.ext (funext fun y ↦ ((hlift (L+M)).choose_spec.1 y).trans
        (congrArg₂ (·+·) ((hlift L).choose_spec.1 y) ((hlift M).choose_spec.1 y)).symm)
      map_smul' := fun c L ↦ Subtype.ext (funext fun y ↦ ((hlift (c•L)).choose_spec.1 y).trans
        (congrArg (c • ·) ((hlift L).choose_spec.1 y)).symm) }
  have hcont : Continuous T := by
    apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
    intro i
    apply Seminorm.continuous' (r := 1)
    have h := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) (hB i)
      (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)
    filter_upwards [V.subtypeL.continuous.continuousAt.preimage_mem_nhds (show _ ∈ 𝓝 (V.subtypeL 0) from h)] with L hL
    apply ((elementarySchwartzSeminorm i).comp T).mem_closedBall_zero.mpr
    change (elementarySchwartzBound (T L).val i).toReal ≤ 1
    apply (ENNReal.toReal_mono (b := 1) (by simp) _).trans_eq ENNReal.toReal_one
    refine iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    have h := (hlift L).choose_spec.2 i (u,a,b)
    have hb := mem_closedBall_zero_iff.mp (hL (mem_range_self (⟨u,a,b⟩ : U)))
    change ‖L.val (B i (u,a,b))‖ ≤ 1 at hb
    rw [← h] at hb
    change (‖jet i (u,a,b) (T L)‖₊ : ℝ≥0∞) ≤ 1
    rw [← ENNReal.ofReal_coe_nnreal, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hb
  let : CompleteSpace SY := elementarySchwartz_isFrechet.choose_spec.2.2
  let : T2Space SY := elementarySchwartz_t2
  let : IsUniformAddGroup V := V.toAddSubgroup.isUniformAddGroup
  let S : V →L[ℂ] SY := ⟨T,hcont⟩
  refine ⟨S.extend V.subtypeL,fun x y ↦ ?_⟩
  let v : V := ⟨elementaryDelta x,Submodule.subset_span (mem_range_self x)⟩
  change S.extend V.subtypeL (V.subtypeL v) y = _
  rw [S.extend_eq elementaryDelta_dense isUniformEmbedding_subtype_val.isUniformInducing]
  exact ((hlift v).choose_spec.1 y).trans ((elementaryDelta_apply x _).trans (hr y x))

/-- The two projective tensor completions obtained by a change of first factor are canonically equivalent. -/
private theorem projective_change_first {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [UniformSpace C] [IsUniformAddGroup C] [PolynormableSpace ℂ C] [T2Space C]
    (e : A ≃L[ℂ] B) :
    ∃ U : Completion (ProjectiveTensor A C) ≃L[ℂ] Completion (ProjectiveTensor B C), ∀ x y,
      U (Completion.coe' (α := ProjectiveTensor A C) (x ⊗ₜ[ℂ] y)) =
        Completion.coe' (α := ProjectiveTensor B C) (e x ⊗ₜ[ℂ] y) := by
  let idC := ContinuousLinearMap.id ℂ C
  let T : ProjectiveTensor A C →L[ℂ] ProjectiveTensor B C :=
    ⟨projectiveTensorMap e.toLinearMap idC.toLinearMap,projectiveTensorMap_continuous e.toContinuousLinearMap idC⟩
  let S : ProjectiveTensor B C →L[ℂ] ProjectiveTensor A C :=
    ⟨projectiveTensorMap e.symm.toLinearMap idC.toLinearMap,projectiveTensorMap_continuous e.symm.toContinuousLinearMap idC⟩
  have hT : LeftInverse S T := fun t ↦ DFunLike.congr_fun (show S.toLinearMap.comp T.toLinearMap = LinearMap.id from
    TensorProduct.ext' (fun x y ↦ by change e.symm (e x) ⊗ₜ[ℂ] y = _; rw [e.symm_apply_apply]; rfl)) t
  have hS : LeftInverse T S := fun t ↦ DFunLike.congr_fun (show T.toLinearMap.comp S.toLinearMap = LinearMap.id from
    TensorProduct.ext' (fun x y ↦ by change e (e.symm x) ⊗ₜ[ℂ] y = _; rw [e.apply_symm_apply]; rfl)) t
  refine ⟨ContinuousLinearEquiv.equivOfInverse T.completion S.completion (fun z ↦ Completion.induction_on z
    (isClosed_eq (S.completion.continuous.comp T.completion.continuous) continuous_id) (fun t ↦ ?_))
    (fun z ↦ Completion.induction_on z (isClosed_eq (T.completion.continuous.comp S.completion.continuous) continuous_id) (fun t ↦ ?_)),
    fun x y ↦ T.completion_apply_coe (show ProjectiveTensor A C from x ⊗ₜ[ℂ] y)⟩
  · change S.completion (T.completion _) = _
    rw [T.completion_apply_coe,S.completion_apply_coe,hT t]
  · change T.completion (S.completion _) = _
    rw [S.completion_apply_coe,T.completion_apply_coe,hS t]

private theorem completed_projective_frechet {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B] [PolynormableSpace ℂ B] [T2Space B]
    [TopologicalSpace.MetrizableSpace A] [TopologicalSpace.MetrizableSpace B] :
    IsFrechetTVS (Completion (ProjectiveTensor A B)) := by
  let T := ProjectiveTensor A B
  obtain ⟨U,hU⟩ := (𝓝 (0:A)).exists_antitone_basis
  obtain ⟨V,hV⟩ := (𝓝 (0:B)).exists_antitone_basis
  let : (𝓝 (0:T)).IsCountablyGenerated := (projectiveTensor_zero_basis hU.1 hV.1).isCountablyGenerated
  let : (uniformity T).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let : T2Space T := projectiveTensor_t2
  let : MetricSpace T := UniformSpace.metricSpace T
  let : PolynormableSpace ℂ (Completion T) := polynormableSpace_completion
  refine ⟨inferInstance,inferInstance,inferInstance,?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

private theorem projective_extension_of_separate {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [UniformSpace C] [IsUniformAddGroup C] [ContinuousSMul ℂ C]
    [PolynormableSpace ℂ C] [T2Space C] [CompleteSpace C]
    (hA : IsFrechetTVS A) (hB : IsFrechetTVS B) (M : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (hl : ∀ x, Continuous (M x)) (hr : ∀ y, Continuous (M.flip y)) :
    ∃ T : Completion (ProjectiveTensor A B) →L[ℂ] C, ∀ x y,
      T (Completion.coe' (α := ProjectiveTensor A B) (x ⊗ₜ[ℂ] y)) = M x y := by
  let L : InductiveTensor A B →ₗ[ℂ] C := TensorProduct.lift M
  let D : InductiveTensor A B →L[ℂ] C := ⟨L,(continuous_inductiveTensor_iff L).mpr ⟨hl,hr⟩⟩
  obtain ⟨e,he⟩ := stageTensor_change hA hB
  refine ⟨D.fromCompletion.comp e.symm.toContinuousLinearMap,fun x y ↦ ?_⟩
  change D.fromCompletion (e.symm _) = _
  rw [←he,e.symm_apply_apply]
  exact D.fromCompletion_apply_coe (show InductiveTensor A B from x ⊗ₜ[ℂ] y)

private theorem tensor_of_reflexive_nuclear {A B : Type}
    [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A] [PolynormableSpace ℂ A] [T2Space A] [CompleteSpace A]
    [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B] [PolynormableSpace ℂ B] [T2Space B] [CompleteSpace B]
    [ContinuousSMul ℂ A] [ContinuousSMul ℂ B]
    [BarrelledSpace ℂ (StrongDual ℂ A)] [CompleteSpace (StrongDual ℂ A)]
    (e : A ≃L[ℂ] StrongDual ℂ (StrongDual ℂ A)) (he : ∀ f L, e f L = L f) (hA : IsNuclearTVS.{0} A) :
    ∃ U : Completion (ProjectiveTensor A B) ≃L[ℂ] (StrongDual ℂ A →L[ℂ] B),
      ∀ (f : A) (g : B) (L : StrongDual ℂ A),
        U (Completion.coe' (α := ProjectiveTensor A B) (f ⊗ₜ[ℂ] g)) L = L f • g := by
  let D := StrongDual ℂ A
  let : PolynormableSpace ℂ D := uniformConvergenceCLM_polynormable (F := ℂ) _ (fun _ h ↦ h)
    (by rw [sUnion_isVonNBounded_eq_univ,Submodule.span_univ]; simp)
  have hn := schwartzBruhat_nuclear_of_embedding.{0} e.symm.toLinearMap e.symm.toHomeomorph.isEmbedding hA
  let : T2Space (StrongDual ℂ D) := hn.1
  let : PolynormableSpace ℂ (StrongDual ℂ D) := hn.2.1
  let u : A ≃ᵤ StrongDual ℂ D := ⟨e.toEquiv,e.toContinuousLinearMap.uniformContinuous,e.symm.toContinuousLinearMap.uniformContinuous⟩
  let : CompleteSpace (StrongDual ℂ D) := u.completeSpace_iff.mp inferInstance
  obtain ⟨U,hU⟩ := projective_change_first (C := B) e
  obtain ⟨V,hV⟩ := (completedProjectiveTensorToOperators_equiv (E := D) (F := B) hn).2
  refine ⟨U.trans V,fun f g L ↦ ?_⟩
  change V (U _) L = _
  exact (congrArg (fun z ↦ V z L) (hU f g)).trans ((congrArg (fun v : D →L[ℂ] B ↦ v L)
    (hV (e f ⊗ₜ[ℂ] g))).trans ((projectiveTensorToOperators_tmul (e f) g L).trans (congrArg (· • g) (he f L))))

private theorem elementary_product_map (e : X × Y ≃ₜ+ Z) :
    ∃ L : Completion (ProjectiveTensor SX SY) →L[ℂ] SZ, ∀ (s : SX) (t : SY) (x : X) (y : Y),
      L (Completion.coe' (α := ProjectiveTensor SX SY) (s ⊗ₜ[ℂ] t)) (e (x,y)) = s x * t y := by
  let p := (AddMonoidHom.fst X Y).comp e.symm.toAddEquiv.toAddMonoidHom
  let q := (AddMonoidHom.snd X Y).comp e.symm.toAddEquiv.toAddMonoidHom
  let hp : Continuous p := continuous_fst.comp e.symm.continuous
  let hq : Continuous q := continuous_snd.comp e.symm.continuous
  have hcoord (j : Fin m ⊕ Fin r) : ∃ (a : X →+ ℝ) (b : Y →+ ℝ), Continuous a ∧ Continuous b ∧
      ∀ z, fiberCoord z j = a (p z) + b (q z) := by
    let c := (fiberCoordHom j).comp e.toAddEquiv.toAddMonoidHom
    have hc : Continuous c := (fiberCoordHom_continuous _).comp e.continuous
    refine ⟨c.comp (AddMonoidHom.inl X Y),c.comp (AddMonoidHom.inr X Y),
      hc.comp (continuous_id.prodMk continuous_const),hc.comp (continuous_const.prodMk continuous_id),fun z ↦ ?_⟩
    change _ = c (p z,0) + c (0,q z)
    rw [←map_add,show (p z,0) + (0,q z) = e.symm z by exact Prod.ext (add_zero _) (zero_add _)]
    exact congrArg (fun z ↦ fiberCoord z j) (e.apply_symm_apply z).symm
  let hprod := elementary_graph_mem p q hp hq hcoord
  let B : SX →ₗ[ℂ] SY →ₗ[ℂ] SZ :=
    LinearMap.mk₂ ℂ (fun s t ↦ (⟨fun z ↦ s (p z) * t (q z),hprod s t⟩ : SZ))
      (fun s t v ↦ Subtype.ext (funext fun z ↦ add_mul (s (p z)) (t (p z)) (v (q z))))
      (fun c s t ↦ Subtype.ext (funext fun z ↦ mul_assoc c (s (p z)) (t (q z))))
      (fun s t v ↦ Subtype.ext (funext fun z ↦ mul_add (s (p z)) (t (q z)) (v (q z))))
      (fun c s t ↦ Subtype.ext (funext fun z ↦ mul_left_comm (s (p z)) c (t (q z))))
  let : BarrelledSpace ℂ SX := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  let : BarrelledSpace ℂ SY := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  let : ContinuousSMul ℂ SX := (withGeneratingSeminorms_spec _ _).continuousSMul
  let : ContinuousSMul ℂ SY := (withGeneratingSeminorms_spec _ _).continuousSMul
  let : T2Space SX := elementarySchwartz_t2
  let : T2Space SY := elementarySchwartz_t2
  let : T2Space SZ := elementarySchwartz_t2
  let : CompleteSpace SZ := elementarySchwartz_isFrechet.choose_spec.2.2
  let : PolynormableSpace ℂ SX := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ SY := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ SZ := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  have hl (s : SX) : Continuous (B s) := by
    apply continuous_toElementarySchwartz_of_eval
    intro z
    let h := elementarySchwartz_eval (q z)
    exact ⟨s (p z) • h.choose,fun t ↦ congrArg (s (p z) * ·) (h.choose_spec t)⟩
  have hr (t : SY) : Continuous (B.flip t) := by
    apply continuous_toElementarySchwartz_of_eval
    intro z
    let h := elementarySchwartz_eval (p z)
    exact ⟨t (q z) • h.choose,fun s ↦ (congrArg (t (q z) * ·) (h.choose_spec s)).trans (mul_comm ..)⟩
  obtain ⟨L,hL⟩ := projective_extension_of_separate elementarySchwartz_isFrechet elementarySchwartz_isFrechet B hl hr
  refine ⟨L,fun s t x y ↦ ?_⟩
  rw [hL]
  exact congrArg₂ (·*·) (congrArg (fun v : X × Y ↦ s v.1) (e.symm_apply_apply _))
    (congrArg (fun v : X × Y ↦ t v.2) (e.symm_apply_apply _))

private theorem elementary_operator_tensor :
    ∃ E : Completion (ProjectiveTensor SX SY) ≃L[ℂ] (StrongDual ℂ SX →L[ℂ] SY),
      ∀ (f : SX) (g : SY) (L : StrongDual ℂ SX),
        E (Completion.coe' (α := ProjectiveTensor SX SY) (f ⊗ₜ[ℂ] g)) L = L f • g := by
  let : T2Space SX := elementarySchwartz_t2
  let : T2Space SY := elementarySchwartz_t2
  let : PolynormableSpace ℂ SX := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ SY := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : CompleteSpace SY := elementarySchwartz_isFrechet.choose_spec.2.2
  let : CompleteSpace SX := elementarySchwartz_isFrechet.choose_spec.2.2
  let : ContinuousSMul ℂ SX := (withGeneratingSeminorms_spec _ _).continuousSMul
  let : ContinuousSMul ℂ SY := (withGeneratingSeminorms_spec _ _).continuousSMul
  let : CompleteSpace (StrongDual ℂ SX) := elementarySchwartz_strongDual_complete
  let : BarrelledSpace ℂ (StrongDual ℂ SX) := elementarySchwartz_strongDual_barrelled
  obtain ⟨e,he⟩ := elementarySchwartz_reflexive (m := m₁) (n := n₁) (r := r₁) (F := F₁)
  exact tensor_of_reflexive_nuclear (A := SX) (B := SY) e he elementarySchwartz_nuclear

private theorem elementary_kernel_value (e : X × Y ≃ₜ+ Z)
    (L : Completion (ProjectiveTensor SX SY) →L[ℂ] SZ)
    (hL : ∀ (s : SX) (t : SY) (x : X) (y : Y), L (Completion.coe' (α := ProjectiveTensor SX SY) (s ⊗ₜ[ℂ] t)) (e (x,y)) = s x * t y)
    (A : Completion (ProjectiveTensor SX SY) ≃L[ℂ] (StrongDual ℂ SX →L[ℂ] SY))
    (hA : ∀ (s : SX) (t : SY) (l : StrongDual ℂ SX), A (Completion.coe' (α := ProjectiveTensor SX SY) (s ⊗ₜ[ℂ] t)) l = l s • t)
    (z : Completion (ProjectiveTensor SX SY)) (x : X) (y : Y) : L z (e (x,y)) = A z (elementaryDelta x) y := by
  let P := ProjectiveTensor SX SY
  let ev := (elementarySchwartz_eval (e (x,y))).choose
  let δ := (elementarySchwartz_eval y).choose
  let left := ev.comp L
  let right := δ.comp ((ContinuousLinearMap.applyₗ SY (RingHom.id ℂ) (elementaryDelta x)).comp A.toContinuousLinearMap)
  have h : left.toLinearMap.comp (Completion.toComplL : P →L[ℂ] _).toLinearMap =
      right.toLinearMap.comp (Completion.toComplL : P →L[ℂ] _).toLinearMap := by
    apply TensorProduct.ext'
    intro s t
    have h := (elementarySchwartz_eval (e (x,y))).choose_spec (L (Completion.coe' (α := P) (s ⊗ₜ[ℂ] t)))
    have hv := hA s t (elementaryDelta x)
    have hv' : (A (Completion.coe' (α := P) (s ⊗ₜ[ℂ] t)) (elementaryDelta x)) y = s x * t y := by
      rw [hv,elementaryDelta_apply]
      rfl
    exact h.trans ((hL s t x y).trans (hv'.symm.trans ((elementarySchwartz_eval y).choose_spec _).symm))
  have hz : left z = right z := Completion.induction_on z (isClosed_eq left.continuous right.continuous)
    (fun t ↦ DFunLike.congr_fun h t)
  exact ((elementarySchwartz_eval (e (x,y))).choose_spec _).symm.trans (hz.trans ((elementarySchwartz_eval y).choose_spec _))

private theorem elementary_kernel_bijective {T : Type*} [AddCommGroup T] [Module ℂ T] [TopologicalSpace T]
    (e : X × Y ≃ₜ+ Z) (L : T →L[ℂ] SZ) (A : T ≃L[ℂ] (StrongDual ℂ SX →L[ℂ] SY))
    (hvalue : ∀ z x y, L z (e (x,y)) = A z (elementaryDelta x) y) : Bijective L := by
  let D := StrongDual ℂ SX
  let : T2Space SY := elementarySchwartz_t2
  have hinj : Injective L := by
    intro z w h
    apply A.injective
    let a := A z - A w
    have hz : Submodule.span ℂ (range (elementaryDelta (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁))) ≤ a.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,rfl⟩
      apply sub_eq_zero.mpr
      exact Subtype.ext (funext fun y ↦ (hvalue z x y).symm.trans ((congrArg (fun f : SZ ↦ f (e (x,y))) h).trans (hvalue w x y)))
    apply ContinuousLinearMap.ext
    intro x
    apply sub_eq_zero.mp
    apply a.isClosed_ker.closure_subset_iff.mpr (fun _ h ↦ hz h)
    exact (show Dense (Submodule.span ℂ (range (elementaryDelta (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁))) : Set D) by
      simpa only [DenseRange,show range (Submodule.span ℂ (range (elementaryDelta (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁)))).subtypeL = _ from Subtype.range_coe] using elementaryDelta_dense (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁)) x
  have hsur : Surjective L := by
    intro f
    obtain ⟨T,hT⟩ := elementary_kernel_operator e f
    refine ⟨A.symm T,Subtype.ext (funext fun g ↦ ?_)⟩
    let x := (e.symm g).1
    let y := (e.symm g).2
    have hg : e (x,y) = g := e.apply_symm_apply g
    exact (congrArg (fun w : Z ↦ L (A.symm T) w) hg).symm.trans ((hvalue _ x y).trans
      ((congrArg (fun B : D →L[ℂ] SY ↦ B (elementaryDelta x) y) (A.apply_symm_apply T)).trans
      ((hT x y).trans (congrArg (fun w : Z ↦ f w) hg))))
  exact ⟨hinj,hsur⟩

private theorem frechet_product_equiv_of_bijective {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [UniformSpace A] [IsUniformAddGroup A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [UniformSpace B] [IsUniformAddGroup B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C]
    (hA : IsFrechetTVS A) (hB : IsFrechetTVS B) (hC : IsFrechetTVS C)
    (L : Completion (ProjectiveTensor A B) →L[ℂ] C) (hL : Bijective L) :
    ∃ e : Completion (InductiveTensor A B) ≃L[ℂ] C, ∀ x y,
      e (Completion.coe' (α := InductiveTensor A B) (x ⊗ₜ[ℂ] y)) =
        L (Completion.coe' (α := ProjectiveTensor A B) (x ⊗ₜ[ℂ] y)) := by
  let : TopologicalSpace.MetrizableSpace A := hA.choose_spec.2.1
  let : TopologicalSpace.MetrizableSpace B := hB.choose_spec.2.1
  let P := ProjectiveTensor A B
  let : PolynormableSpace ℂ (Completion P) := polynormableSpace_completion
  let : ContinuousSMul ℂ (Completion P) := PolynormableSpace.continuousSMul ℂ _
  have hq := quotientMap_of_LF_surjection (isLFSpace_of_isFrechetTVS (completed_projective_frechet (A := A) (B := B)))
    (isLFSpace_of_isFrechetTVS hC) L ⟨L,fun _ ↦ rfl⟩ hL.surjective
  obtain ⟨e,he⟩ := stageTensor_change hA hB
  exact ⟨e.trans (ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective L.toLinearMap hL)
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq,hL.injective⟩)),fun x y ↦ congrArg L (he x y)⟩

/-- A product chart identifies the elementary product test space with the completed
inductive tensor of its factors. Point evaluation identifies its action on pure tensors. -/
private theorem elementary_kernel_equiv (e : X × Y ≃ₜ+ Z) :
    ∃ L : Completion (InductiveTensor SX SY) ≃L[ℂ] SZ, ∀ (s : SX) (t : SY) (x : X) (y : Y),
      L (Completion.coe' (α := InductiveTensor SX SY) (s ⊗ₜ[ℂ] t)) (e (x,y)) = s x * t y := by
  let : T2Space SX := elementarySchwartz_t2
  let : T2Space SY := elementarySchwartz_t2
  let : T2Space SZ := elementarySchwartz_t2
  let : PolynormableSpace ℂ SX := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ SY := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ SZ := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  refine (elementary_product_map e).elim fun L hL ↦ ?_
  refine (elementary_operator_tensor (m₁ := m₁) (n₁ := n₁) (r₁ := r₁) (F₁ := F₁)
    (m₂ := m₂) (n₂ := n₂) (r₂ := r₂) (F₂ := F₂)).elim fun A hA ↦ ?_
  have hb := elementary_kernel_bijective e L A (elementary_kernel_value e L hL A hA)
  refine (frechet_product_equiv_of_bijective (A := SX) (B := SY) (C := SZ) elementarySchwartz_isFrechet elementarySchwartz_isFrechet
    elementarySchwartz_isFrechet L hb).elim fun U hU ↦ ?_
  exact ⟨U,fun s t x y ↦ (congrArg (fun z : SZ ↦ z (e (x,y))) (hU s t)).trans (hL s t x y)⟩

end ElementarySlices

/-- Glue stage maps on an exhaustive directed family of linear images by taking the union
of their graphs. Injectivity in each stage makes the union a graph. -/
private theorem directed_stage_linear_map {I E F : Type*} [Nonempty I] [Preorder I] [IsDirectedOrder I]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    {X : I → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (u : ∀ i, X i →ₗ[ℂ] E) (v : ∀ i, X i →ₗ[ℂ] F) (hinj : ∀ i, Injective (u i))
    (hex : ∀ x, ∃ i t, u i t = x)
    (hm : ∀ i j, i ≤ j → ∀ t, ∃ s, u j s = u i t ∧ v j s = v i t) :
    ∃ L : E →ₗ[ℂ] F, ∀ i t, L (u i t) = v i t := by
  let R (i : I) := ((u i).prod (v i)).range
  have hmono : Monotone R := by
    rintro i j hij _ ⟨t,rfl⟩
    obtain ⟨s,hs,hs'⟩ := hm i j hij t
    exact ⟨s,Prod.ext hs hs'⟩
  let M := ⨆ i, R i
  let p := (LinearMap.fst ℂ E F).comp M.subtype
  let q := (LinearMap.snd ℂ E F).comp M.subtype
  have hi : Injective p := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    rintro ⟨⟨x,y⟩,h⟩ hx
    obtain ⟨i,t,ht⟩ := (Submodule.mem_iSup_of_directed R hmono.directed_le).mp h
    have hx' : u i t = 0 := (congrArg Prod.fst ht).trans hx
    have ht' : t = 0 := hinj i (hx'.trans (map_zero _).symm)
    apply Subtype.ext
    change (x,y) = (0,0)
    exact ht.symm.trans (ht' ▸ map_zero _)
  have hs : Surjective p := by
    intro x
    obtain ⟨i,t,rfl⟩ := hex x
    exact ⟨⟨_,(le_iSup R i) (show (u i t,v i t) ∈ R i from ⟨t,rfl⟩)⟩,rfl⟩
  let e := LinearEquiv.ofBijective p ⟨hi,hs⟩
  refine ⟨q.comp e.symm.toLinearMap,fun i t ↦ ?_⟩
  let z : M := ⟨(u i t,v i t),(le_iSup R i) (show (u i t,v i t) ∈ R i from ⟨t,rfl⟩)⟩
  exact congrArg q (e.symm_apply_apply z)

/-- Compatible lifts along an exhaustive directed union produce a continuous inverse.
The continuity criterion and the determining family for the inverse are supplied separately. -/
private theorem kernel_equiv_of_stage_lifts {I Z W : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    {T : I → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module ℂ (T i)] [∀ i, TopologicalSpace (T i)]
    (K : Z →L[ℂ] W) (v : ∀ i, T i →L[ℂ] Z) (u : ∀ i, T i →L[ℂ] W) (hu : ∀ i, K.comp (v i) = u i)
    (hi : ∀ i, Injective (u i)) (hex : ∀ x, ∃ i t, u i t = x)
    (hm : ∀ i j, i ≤ j → ∀ t, ∃ s, v j s = v i t)
    (hc : ∀ J : W →ₗ[ℂ] Z, (∀ i t, J (u i t) = v i t) → Continuous J)
    (hdet : ∀ J : Z →L[ℂ] Z, (∀ i t, J (v i t) = v i t) → J = ContinuousLinearMap.id ℂ Z) :
    ∃ E : Z ≃L[ℂ] W, ∀ z, E z = K z := by
  have hd (i j : I) (hij : i ≤ j) (t : T i) : ∃ s, u j s = u i t ∧ v j s = v i t := by
    obtain ⟨s,hs⟩ := hm i j hij t
    exact ⟨s,(DFunLike.congr_fun (hu j) s).symm.trans ((congrArg K hs).trans (DFunLike.congr_fun (hu i) t)),hs⟩
  obtain ⟨J,hJ⟩ := directed_stage_linear_map (fun i ↦ (u i).toLinearMap) (fun i ↦ (v i).toLinearMap) hi hex hd
  let Q : W →L[ℂ] Z := ⟨J,hc J hJ⟩
  have hleft := hdet (Q.comp K) fun i t ↦ (congrArg Q (DFunLike.congr_fun (hu i) t)).trans (hJ i t)
  refine ⟨ContinuousLinearEquiv.equivOfInverse K Q (fun z ↦ DFunLike.congr_fun hleft z) ?_,fun _ ↦ rfl⟩
  intro w
  obtain ⟨i,t,rfl⟩ := hex w
  exact (congrArg K (hJ i t)).trans (DFunLike.congr_fun (hu i) t)

private theorem continuous_out_of_schwartzBruhat {A : Type*} [CommGroup A] [TopologicalSpace A]
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (L : SchwartzBruhat A →ₗ[ℂ] E)
    (h : ∀ (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient),
      Continuous (L ∘ schwartzBruhatStageCLM a e)) : Continuous L := by
  let P : SeminormFamily ℂ (SchwartzBruhat A) {q : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  apply (PolynormableSpace.withSeminorms ℂ E).continuous_of_continuous_comp
  intro p
  exact hP.continuous_seminorm ⟨p.val.comp L,fun a e ↦ p.property.comp (h a e)⟩

/-- Two continuous linear maps on a completed inductive tensor agree if they agree on
the images of all pure tensors. -/
private theorem completed_tensor_ext {X Y V : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [T2Space V]
    {S T : Completion (InductiveTensor X Y) →L[ℂ] V}
    (h : ∀ (x : X) (y : Y), S (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)) =
      T (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y))) : S = T := by
  let j : InductiveTensor X Y →L[ℂ] Completion (InductiveTensor X Y) := Completion.toComplL
  have he : S.toLinearMap.comp j.toLinearMap = T.toLinearMap.comp j.toLinearMap := TensorProduct.ext' h
  exact DFunLike.ext _ _ fun z ↦ Completion.induction_on z (isClosed_eq S.continuous T.continuous)
    (fun t ↦ DFunLike.congr_fun he t)

section ProductStages

variable {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H]

private theorem quotient_locallyEuclidean_of_good (k : Subgroup G) (hk : IsBruhatGoodSubgroup k) :
    IsLocallyEuclidean (G ⧸ k) := by
  let : T1Space (G ⧸ k) := QuotientGroup.t1Space_iff.mpr hk.1
  obtain ⟨e,_⟩ := lcaQuotientDual_equiv_annihilator k hk.1
  exact isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
    (isCompactlyGeneratedGroup_of_continuousMulEquiv e.symm hk.2.2)

private theorem prod_bruhat_good (k : Subgroup G) (j : Subgroup H)
    (hk : IsBruhatGoodSubgroup k) (hj : IsBruhatGoodSubgroup j) :
    IsBruhatGoodSubgroup (k.prod j) := by
  let : T1Space (G ⧸ k) := QuotientGroup.t1Space_iff.mpr hk.1
  let : T1Space (H ⧸ j) := QuotientGroup.t1Space_iff.mpr hj.1
  have hc : IsCompact (k.prod j : Set (G × H)) :=
    (isCompact_of_bruhatGoodSubgroup k hk).prod (isCompact_of_bruhatGoodSubgroup j hj)
  let : T1Space ((G × H) ⧸ k.prod j) := QuotientGroup.t1Space_iff.mpr hc.isClosed
  obtain ⟨W,hW,hW'⟩ := exists_nhds_one_of_isLocallyEuclidean (quotient_locallyEuclidean_of_good k hk)
  obtain ⟨V,hV,hV'⟩ := exists_nhds_one_of_isLocallyEuclidean (quotient_locallyEuclidean_of_good j hj)
  let e := QuotientGroup.prodMulEquiv k j
  have hcont : Continuous e := (QuotientGroup.isQuotientMap_mk (k.prod j)).continuous_iff.mpr
    ((QuotientGroup.continuous_mk.comp continuous_fst).prodMk (QuotientGroup.continuous_mk.comp continuous_snd))
  have hN : e ⁻¹' (W ×ˢ V) ∈ 𝓝 1 := hcont.continuousAt.preimage_mem_nhds
    (by rw [map_one]; exact prod_mem_nhds hW hV)
  have hloc := isLocallyEuclidean_of_noSmallCyclicSubgroups hN (fun x hx ↦ by
    apply e.injective
    rw [map_one]
    exact Prod.ext (hW' _ fun n ↦ by simpa only [mem_preimage,map_pow,Prod.pow_fst] using (hx n).1)
      (hV' _ fun n ↦ by simpa only [mem_preimage,map_pow,Prod.pow_snd] using (hx n).2))
  obtain ⟨v,_⟩ := lcaQuotientDual_equiv_annihilator (k.prod j) hc.isClosed
  exact ⟨hc.isClosed,isOpen_lcaAnnihilator _ hc,isCompactlyGeneratedGroup_of_continuousMulEquiv v
    (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean hloc)⟩

private def rectangularStructuralPair (u : BruhatStructuralPair G) (v : BruhatStructuralPair H) : BruhatStructuralPair (G × H) := by
  let i := u.val.1
  let j := v.val.1
  let K := OrderDual.ofDual u.val.2
  let L := OrderDual.ofDual v.val.2
  refine ⟨(i.prod j,OrderDual.toDual (K.prod L)),u.property.1.prod v.property.1,?_,
    prod_bruhat_good K L u.property.2.2.1 v.property.2.2.1,
    fun x hx ↦ ⟨u.property.2.2.2 hx.1,v.property.2.2.2 hx.2⟩⟩
  have hi : IsCompactlyGeneratedGroup i := u.property.2.1
  have hj : IsCompactlyGeneratedGroup j := v.property.2.1
  obtain ⟨C,hC,hCc,hCg⟩ := hi
  obtain ⟨D,hD,hDc,hDg⟩ := hj
  have hprod : IsCompactlyGeneratedGroup (i × j) :=
    ⟨C ×ˢ D, prod_mem_nhds hC hD, hCc.prod hDc, by rw [Subgroup.closure_prod (mem_of_mem_nhds hC) (mem_of_mem_nhds hD),hCg,hDg]; exact Subgroup.top_prod_top⟩
  let equiv : i.prod j ≃ₜ* i × j := ⟨Subgroup.prodEquiv i j,
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _),
    (continuous_fst.subtype_val.prodMk continuous_snd.subtype_val).subtype_mk _⟩
  exact isCompactlyGeneratedGroup_of_continuousMulEquiv equiv.symm hprod

private theorem rectangular_quotient (a : BruhatStructuralPair G) (b : BruhatStructuralPair H) :
    let c := rectangularStructuralPair a b
    ∃ v : c.quotient ≃ₜ* a.quotient × b.quotient,
      ∀ (x : a.val.1) (y : b.val.1), v (QuotientGroup.mk (⟨(x.val,y.val),x.property,y.property⟩ : c.val.1)) =
        (QuotientGroup.mk x,QuotientGroup.mk y) := by
  let c := rectangularStructuralPair a b
  let equiv : c.val.1 ≃ₜ* a.val.1 × b.val.1 := ⟨Subgroup.prodEquiv _ _,
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _),
    (continuous_fst.subtype_val.prodMk continuous_snd.subtype_val).subtype_mk _⟩
  let p := QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)
  let q := QuotientGroup.mk' ((OrderDual.ofDual b.val.2).comap b.val.1.subtype)
  let t := (p.prodMap q).comp equiv.toMonoidHom
  have ht : IsOpenQuotientMap t := (QuotientGroup.isOpenQuotientMap_mk.prodMap QuotientGroup.isOpenQuotientMap_mk).comp equiv.toHomeomorph.isOpenQuotientMap
  let K := (OrderDual.ofDual c.val.2).comap c.val.1.subtype
  have hker : K = t.ker := by
    ext x
    change (x.val.1 ∈ OrderDual.ofDual a.val.2 ∧ x.val.2 ∈ OrderDual.ofDual b.val.2) ↔ (p (equiv x).1,q (equiv x).2) = 1
    rw [Prod.ext_iff]
    exact and_congr (a.quotient_mk_eq_one (equiv x).1).symm (b.quotient_mk_eq_one (equiv x).2).symm
  let E := (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective t ht.surjective)
  let v := E.toContinuousMulEquiv fun s ↦ by
    rw [← (QuotientGroup.isQuotientMap_mk _).isOpen_preimage]
    exact ht.isQuotientMap.isOpen_preimage
  exact ⟨v,fun _ _ ↦ rfl⟩

end ProductStages
private theorem kernel_extension {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [UniformSpace C] [IsUniformAddGroup C] [ContinuousSMul ℂ C] [T2Space C]
    [CompleteSpace C] [PolynormableSpace ℂ C] (M : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (ha : ∀ a, Continuous (M a)) (hb : ∀ b, Continuous (M.flip b)) :
    ∃ T : Completion (InductiveTensor A B) →L[ℂ] C, ∀ a b,
      T (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b)) = M a b := by
  let t : InductiveTensor A B →ₗ[ℂ] C := TensorProduct.lift M
  let L : InductiveTensor A B →L[ℂ] C := ⟨t,(continuous_inductiveTensor_iff t).mpr ⟨ha,hb⟩⟩
  exact ⟨L.fromCompletion,fun a b ↦ L.fromCompletion_apply_coe (show InductiveTensor A B from a ⊗ₜ[ℂ] b)⟩

private theorem tensor_slices_continuous {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A] [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [PolynormableSpace ℂ C] [T2Space C]
    (T : Completion (InductiveTensor A B) →L[ℂ] C) :
    let v := fun (a : A) (b : B) ↦ T (Completion.coe' (α := InductiveTensor A B) (a ⊗ₜ[ℂ] b))
    (∀ a, Continuous (v a)) ∧ (∀ b, Continuous (fun a ↦ v a b)) := by
  let L := T.comp (Completion.toComplL : InductiveTensor A B →L[ℂ] _)
  exact (continuous_inductiveTensor_iff L.toLinearMap).mp L.continuous

private def HasProductStages (G H : Type*) [CommGroup G] [TopologicalSpace G] [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] : Prop :=
  ∀ (a : BruhatStructuralPair G) (d : ElementaryLCAPresentation a.quotient) (b : BruhatStructuralPair H)
    (l : ElementaryLCAPresentation b.quotient),
    ∃ v : SchwartzBruhatStage d → SchwartzBruhatStage l → SchwartzBruhat (G × H),
      (∀ s, Continuous (v s)) ∧ (∀ t, Continuous (fun s ↦ v s t)) ∧
        ∀ s t x y, v s t (x,y) = schwartzBruhatStageCLM a d s x * schwartzBruhatStageCLM b l t y

private theorem test_from_stage {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A] (v : SchwartzBruhat A) :
    ∃ (a : BruhatStructuralPair A) (d : ElementaryLCAPresentation a.quotient) (s : SchwartzBruhatStage d),
      schwartzBruhatStageCLM a d s = v := by
  refine ((mem_schwartzBruhatSubmodule_iff (G := A) v.val).mp v.property).elim fun a h ↦ h.elim fun d h ↦ h.elim fun s h ↦ ?_
  exact ⟨a,d,s,Subtype.ext h⟩

private theorem test_from_chosen_stage {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A]
    (d : ∀ a : BruhatStructuralPair A, ElementaryLCAPresentation a.quotient) (f : SchwartzBruhat A) :
    ∃ a s, schwartzBruhatStageCLM a (d a) s = f := by
  refine (test_from_stage (A := A) f).elim fun a h ↦ h.elim fun l h ↦ h.elim fun s hs ↦ ?_
  refine (schwartzBruhatStage_transition (le_refl a) l (d a)).elim fun P hP ↦ ?_
  exact ⟨a,P s,(Subtype.ext (hP.1 s)).trans hs⟩

private theorem completed_tensor_map_exists {A B X Y : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]
    (i : A →L[ℂ] X) (j : B →L[ℂ] Y) :
    ∃ v : Completion (InductiveTensor A B) →L[ℂ] Completion (InductiveTensor X Y), ∀ s t,
      v (Completion.coe' (α := InductiveTensor A B) (s ⊗ₜ[ℂ] t)) =
        Completion.coe' (α := InductiveTensor X Y) (i s ⊗ₜ[ℂ] j t) :=
  ⟨completedInductiveMap i j,completedInductiveMap_pure i j⟩

private theorem inclusion_tensor_range {A B C D X Y Z : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup C] [Module ℂ C] [TopologicalSpace C] [PolynormableSpace ℂ C] [T2Space C]
    [AddCommGroup D] [Module ℂ D] [TopologicalSpace D] [PolynormableSpace ℂ D] [T2Space D]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (p : X → Y → Z) (i : A → X) (j : B → Y) (k : C → X) (l : D → Y)
    (v : Completion (InductiveTensor A B) →L[ℂ] Z) (w : Completion (InductiveTensor C D) →L[ℂ] Z)
    (hv : ∀ s t, v (Completion.coe' (α := InductiveTensor A B) (s ⊗ₜ[ℂ] t)) = p (i s) (j t))
    (hw : ∀ s t, w (Completion.coe' (α := InductiveTensor C D) (s ⊗ₜ[ℂ] t)) = p (k s) (l t))
    (P : A →L[ℂ] C) (Q : B →L[ℂ] D) (hP : ∀ s, k (P s) = i s) (hQ : ∀ t, l (Q t) = j t)
    (z : Completion (InductiveTensor A B)) : ∃ t, w t = v z := by
  let J := completedInductiveMap P Q
  have h : w.comp J = v := completed_tensor_ext (X := A) (Y := B) fun s t ↦
    (congrArg w (completedInductiveMap_pure P Q s t)).trans ((hw _ _).trans
      ((congrArg₂ p (hP s) (hQ t)).trans (hv _ _).symm))
  exact ⟨J z,DFunLike.congr_fun h z⟩

private theorem stage_continuous_of_le {A Z : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] [TopologicalSpace Z]
    (J : SchwartzBruhat A → Z) {a b : BruhatStructuralPair A} (hab : a ≤ b)
    (d : ElementaryLCAPresentation a.quotient) (m : ElementaryLCAPresentation b.quotient)
    (h : Continuous (J ∘ schwartzBruhatStageCLM b m)) : Continuous (J ∘ schwartzBruhatStageCLM a d) := by
  refine (schwartzBruhatStage_transition hab d m).elim fun P hP ↦ ?_
  exact (h.comp P.continuous).congr fun t ↦ congrArg J (Subtype.ext (hP.1 t))

private theorem completion_t2 (X : Type*) [UniformSpace X] : T2Space (Completion X) :=
  inferInstance

universe uι vι

/-- Use the universal mapping property of the completed tensor to apply a gluing
criterion for a kernel. The stage inclusions may come from any two test spaces. -/
private theorem product_kernel_from_stages {X : Type uι} {Y : Type vι} {W : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]
    [AddCommGroup W] [Module ℂ W] [UniformSpace W] [IsUniformAddGroup W] [ContinuousSMul ℂ W]
    [PolynormableSpace ℂ W] [T2Space W] [CompleteSpace W]
    (good : X → Y → W → Prop) (M : X →ₗ[ℂ] Y →ₗ[ℂ] W)
    (hm : ∀ x y, good x y (M x y)) (ha : ∀ x, Continuous (M x)) (hb : ∀ y, Continuous (M.flip y))
    (glue : ∀ {Z : Type (max uι vι)} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
        [PolynormableSpace ℂ Z] (pure : X → Y → Z),
      (∀ J : Z →L[ℂ] Z, (∀ x y, J (pure x y) = pure x y) → J = ContinuousLinearMap.id ℂ Z) →
      (∀ {A B : Type} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
        [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
        (i : A →L[ℂ] X) (j : B →L[ℂ] Y), ∃ v : Completion (InductiveTensor A B) →L[ℂ] Z,
           ∀ s t, v (Completion.coe' (α := InductiveTensor A B) (s ⊗ₜ[ℂ] t)) = pure (i s) (j t)) →
      ∀ K : Z →L[ℂ] W, (∀ x y, good x y (K (pure x y))) →
        ∃ E : Z ≃L[ℂ] W, ∀ x y, good x y (E (pure x y))) :
    ∃ E : Completion (InductiveTensor X Y) ≃L[ℂ] W,
      ∀ x y, good x y (E (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y))) := by
  let Z := Completion (InductiveTensor X Y)
  let : T2Space Z := completion_t2 (InductiveTensor X Y)
  let : PolynormableSpace ℂ Z := polynormableSpace_completion
  let pure (x : X) (y : Y) : Z := Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)
  obtain ⟨K,hK⟩ := kernel_extension M ha hb
  apply glue pure (fun J h ↦ completed_tensor_ext (S := J) (T := ContinuousLinearMap.id ℂ Z) h)
    (fun i j ↦ completed_tensor_map_exists i j) K
  exact fun x y ↦ (hK x y).symm ▸ hm x y

section RectangularKernels

variable {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H]

private theorem rectangular_chart (a : BruhatStructuralPair G) (b : BruhatStructuralPair H)
    (d : ElementaryLCAPresentation a.quotient) (l : ElementaryLCAPresentation b.quotient)
    (m : ElementaryLCAPresentation (rectangularStructuralPair a b).quotient) :
    let X := ElementaryLieGroup d.realDim d.torusDim d.latticeRank d.finiteFactor
    let Y := ElementaryLieGroup l.realDim l.torusDim l.latticeRank l.finiteFactor
    let Z := ElementaryLieGroup m.realDim m.torusDim m.latticeRank m.finiteFactor
    let c := rectangularStructuralPair a b
    ∃ B : X × Y ≃ₜ+ Z, ∀ (x : a.val.1) (y : b.val.1),
      B ((d.equiv (QuotientGroup.mk x)).toAdd,(l.equiv (QuotientGroup.mk y)).toAdd) =
        (m.equiv (QuotientGroup.mk (⟨(x.val,y.val),x.property,y.property⟩ : c.val.1))).toAdd := by
  intro X Y Z c
  refine (rectangular_quotient a b).elim fun v hv ↦ ?_
  let A := ((d.equiv.symm.toMulEquiv.prodCongr l.equiv.symm.toMulEquiv).trans v.symm.toMulEquiv).trans m.equiv.toMulEquiv
  let B : X × Y ≃ₜ+ Z := ⟨{ A.toEquiv with map_add' := A.map_mul },
    m.equiv.continuous.comp (v.symm.continuous.comp (d.equiv.symm.continuous.prodMap l.equiv.symm.continuous)),
    (d.equiv.continuous.prodMap l.equiv.continuous).comp (v.continuous.comp m.equiv.symm.continuous)⟩
  refine ⟨B,fun x y ↦ ?_⟩
  change (m.equiv (v.symm (d.equiv.symm (d.equiv _),l.equiv.symm (l.equiv _)))).toAdd = _
  rw [d.equiv.symm_apply_apply,l.equiv.symm_apply_apply,← hv x y,v.symm_apply_apply]

private theorem stage_value_on (a : BruhatStructuralPair G) (d : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage d) (x : a.val.1) :
    schwartzBruhatStageCLM a d s x.val = s (d.equiv (QuotientGroup.mk x)).toAdd :=
  (schwartzBruhatStageRealization_apply a d s x.val).trans (dite_eq_left x.property)

private theorem stage_value_off (a : BruhatStructuralPair G) (d : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage d) (x : G) (hx : x ∉ a.val.1) : schwartzBruhatStageCLM a d s x = 0 :=
  (schwartzBruhatStageRealization_apply a d s x).trans (dite_eq_right hx)

private theorem rectangular_stage_values (a : BruhatStructuralPair G) (b : BruhatStructuralPair H)
    (d : ElementaryLCAPresentation a.quotient) (l : ElementaryLCAPresentation b.quotient)
    (m : ElementaryLCAPresentation (rectangularStructuralPair a b).quotient)
    (s : SchwartzBruhatStage d) (t : SchwartzBruhatStage l) (w : SchwartzBruhatStage m)
    (h : ∀ (x : a.val.1) (y : b.val.1), w (m.equiv (QuotientGroup.mk
      (⟨(x.val,y.val),x.property,y.property⟩ : (rectangularStructuralPair a b).val.1))).toAdd =
        s (d.equiv (QuotientGroup.mk x)).toAdd * t (l.equiv (QuotientGroup.mk y)).toAdd)
    (x : G) (y : H) :
    schwartzBruhatStageCLM (rectangularStructuralPair a b) m w (x,y) =
      schwartzBruhatStageCLM a d s x * schwartzBruhatStageCLM b l t y := by
  let c := rectangularStructuralPair a b
  by_cases hx : x ∈ a.val.1
  · by_cases hy : y ∈ b.val.1
    · let u : a.val.1 := ⟨x,hx⟩
      let v : b.val.1 := ⟨y,hy⟩
      let z : c.val.1 := ⟨(x,y),hx,hy⟩
      exact (stage_value_on c m w z).trans ((h u v).trans
        (congrArg₂ (· * ·) (stage_value_on a d s u).symm (stage_value_on b l t v).symm))
    · exact (stage_value_off c m w (x,y) (fun hz ↦ hy hz.2)).trans
        ((congrArg (schwartzBruhatStageCLM a d s x * ·) (stage_value_off b l t y hy)).trans (mul_zero _)).symm
  · exact (stage_value_off c m w (x,y) (fun hz ↦ hx hz.1)).trans
      ((congrArg (· * schwartzBruhatStageCLM b l t y) (stage_value_off a d s x hx)).trans (zero_mul _)).symm

/-- Transport the elementary kernel equivalence through a rectangular quotient and
extension by zero. -/
private theorem rectangular_stage_kernel (a : BruhatStructuralPair G) (b : BruhatStructuralPair H)
    (d : ElementaryLCAPresentation a.quotient) (l : ElementaryLCAPresentation b.quotient)
    (m : ElementaryLCAPresentation (rectangularStructuralPair a b).quotient) :
    let c := rectangularStructuralPair a b
    ∃ E : Completion (InductiveTensor (SchwartzBruhatStage d) (SchwartzBruhatStage l)) ≃L[ℂ] SchwartzBruhatStage m,
      ∀ (s : SchwartzBruhatStage d) (t : SchwartzBruhatStage l) (x : G) (y : H),
        schwartzBruhatStageCLM c m (E (Completion.coe' (α := InductiveTensor (SchwartzBruhatStage d) (SchwartzBruhatStage l)) (s ⊗ₜ[ℂ] t))) (x,y) =
        schwartzBruhatStageCLM a d s x * schwartzBruhatStageCLM b l t y := by
  refine (rectangular_chart a b d l m).elim fun B hB ↦ ?_
  refine (elementary_kernel_equiv B).elim fun E hE ↦ ?_
  refine ⟨E,fun s t x y ↦ rectangular_stage_values a b d l m s t _ (fun u v ↦ ?_) x y⟩
  let w := E (Completion.coe' (α := InductiveTensor (SchwartzBruhatStage d) (SchwartzBruhatStage l)) (s ⊗ₜ[ℂ] t))
  exact (congrArg (fun z ↦ w z) (hB u v)).symm.trans (hE s t _ _)

private theorem exists_rectangular_bound (c : BruhatStructuralPair (G × H)) :
    ∃ a b, c ≤ rectangularStructuralPair a b :=
  (exists_rectangular_stage_bounds c).elim fun a h ↦ h.elim fun b hb ↦ ⟨a,b,hb.1,hb.2⟩

variable [scG : SecondCountableTopology G] [scH : SecondCountableTopology H]
include scG scH
local notation "SG" => SchwartzBruhat G
local notation "SH" => SchwartzBruhat H
local notation "SW" => SchwartzBruhat (G × H)
local notation "I₀" => InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)
local notation "Z₀" => Completion (InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))

private theorem kernel_bilinear (hs : HasProductStages G H) :
    ∃ B : SG →ₗ[ℂ] SH →ₗ[ℂ] SW, ∀ f g x y, B f g (x,y) = f x * g y := by
  have mem (f : SG) (g : SH) : (fun z : G × H ↦ f z.1 * g z.2) ∈ schwartzBruhatSubmodule (G × H) := by
    refine (test_from_stage (A := G) f).elim fun a h ↦ h.elim fun d h ↦ h.elim fun s hf ↦ ?_
    refine (test_from_stage (A := H) g).elim fun b h ↦ h.elim fun l h ↦ h.elim fun t hg ↦ ?_
    obtain ⟨v,_,_,hv⟩ := hs a d b l
    have h : (v s t).val = fun z : G × H ↦ f z.1 * g z.2 := funext fun ⟨x,y⟩ ↦
      (hv s t x y).trans (congrArg₂ (· * ·) (congrArg (fun u : SG ↦ u x) hf) (congrArg (fun u : SH ↦ u y) hg))
    exact h ▸ (v s t).property
  refine ⟨LinearMap.mk₂ ℂ (fun f g ↦ (⟨_,mem f g⟩ : SW)) ?_ ?_ ?_ ?_,fun _ _ _ _ ↦ rfl⟩
  · exact fun f g t ↦ Subtype.ext (funext fun z ↦ add_mul (f z.1) (g z.1) (t z.2))
  · exact fun c s t ↦ Subtype.ext (funext fun z ↦ mul_assoc c (s z.1) (t z.2))
  · exact fun s t v ↦ Subtype.ext (funext fun z ↦ mul_add (s z.1) (t z.2) (v z.2))
  · exact fun c s t ↦ Subtype.ext (funext fun z ↦ mul_left_comm (s z.1) c (t z.2))

private theorem kernel_stage_slices (hs : HasProductStages G H) (B : SG →ₗ[ℂ] SH →ₗ[ℂ] SW)
    (hB : ∀ f g x y, B f g (x,y) = f x * g y)
    (a : BruhatStructuralPair G) (d : ElementaryLCAPresentation a.quotient)
    (b : BruhatStructuralPair H) (l : ElementaryLCAPresentation b.quotient) :
    (∀ s, Continuous ((B (schwartzBruhatStageCLM a d s)) ∘ schwartzBruhatStageCLM b l)) ∧
      (∀ t, Continuous ((B.flip (schwartzBruhatStageCLM b l t)) ∘ schwartzBruhatStageCLM a d)) := by
  refine (hs a d b l).elim fun v h ↦ ?_
  have he (s : SchwartzBruhatStage d) (t : SchwartzBruhatStage l) : v s t = B (schwartzBruhatStageCLM a d s) (schwartzBruhatStageCLM b l t) :=
    Subtype.ext (funext fun ⟨x,y⟩ ↦ (h.2.2 s t x y).trans (hB (schwartzBruhatStageCLM a d s) (schwartzBruhatStageCLM b l t) x y).symm)
  exact ⟨fun s ↦ (h.1 s).congr (he s),fun t ↦ (h.2.1 t).congr (fun s ↦ he s t)⟩

private theorem kernel_separate (hs : HasProductStages G H) (B : SG →ₗ[ℂ] SH →ₗ[ℂ] SW)
    (hB : ∀ f g x y, B f g (x,y) = f x * g y) :
    (∀ f, Continuous (B f)) ∧ (∀ g, Continuous (B.flip g)) := by
  let : PolynormableSpace ℂ SW := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  constructor
  · intro f
    refine (test_from_stage (A := G) f).elim fun a h ↦ h.elim fun d h ↦ h.elim fun s hf ↦ ?_
    have hc := continuous_out_of_schwartzBruhat (A := H) (E := SW) (B (schwartzBruhatStageCLM a d s))
      (fun b l ↦ (kernel_stage_slices hs B hB a d b l).1 s)
    exact (congrArg (fun v : SG ↦ Continuous (B v)) hf).mp hc
  · intro g
    refine (test_from_stage (A := H) g).elim fun b h ↦ h.elim fun l h ↦ h.elim fun t hg ↦ ?_
    have hc := continuous_out_of_schwartzBruhat (A := G) (E := SW) (B.flip (schwartzBruhatStageCLM b l t))
      (fun a d ↦ (kernel_stage_slices hs B hB a d b l).2 t)
    exact (congrArg (fun v : SH ↦ Continuous (B.flip v)) hg).mp hc

private theorem rectangular_stage_continuity {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [PolynormableSpace ℂ Z]
    (J : SW →ₗ[ℂ] Z) (hc : ∀ (a : BruhatStructuralPair G) (b : BruhatStructuralPair H),
      let w := rectangularStructuralPair a b
      ∃ m : ElementaryLCAPresentation w.quotient, Continuous (J ∘ schwartzBruhatStageCLM w m)) :
    Continuous J := by
  refine continuous_out_of_schwartzBruhat (A := G × H) (E := Z) J fun c d ↦ ?_
  refine (exists_rectangular_bound (G := G) (H := H) c).elim fun a h ↦ h.elim fun b hcw ↦ ?_
  refine (hc a b).elim fun m hm ↦ ?_
  exact stage_continuous_of_le J hcw d m hm

private theorem rectangular_stage_exhausts
    (m : ∀ (a : BruhatStructuralPair G) (b : BruhatStructuralPair H), ElementaryLCAPresentation (rectangularStructuralPair a b).quotient)
    (s : SW) : ∃ a b t, schwartzBruhatStageCLM (rectangularStructuralPair a b) (m a b) t = s := by
  refine (test_from_stage (A := G × H) s).elim fun c h ↦ h.elim fun l h ↦ h.elim fun t ht ↦ ?_
  refine (exists_rectangular_bound (G := G) (H := H) c).elim fun a h ↦ h.elim fun b hcw ↦ ?_
  refine (schwartzBruhatStage_transition hcw l (m a b)).elim fun P hP ↦ ?_
  exact ⟨a,b,P t,(Subtype.ext (hP.1 t)).trans ht⟩

private theorem rectangular_product_stages : HasProductStages G H := by
  intro a d b l
  let w := rectangularStructuralPair a b
  let m := w.elementary.some
  refine (rectangular_stage_kernel a b d l m).elim fun e he ↦ ?_
  let T := (schwartzBruhatStageCLM w m).comp e.toContinuousLinearMap
  let A := SchwartzBruhatStage d
  let B := SchwartzBruhatStage l
  let : T2Space A := elementarySchwartz_t2
  let : T2Space B := elementarySchwartz_t2
  let : PolynormableSpace ℂ A := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ B := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : T2Space SW := schwartzBruhat_t2
  let : PolynormableSpace ℂ SW := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  have h := tensor_slices_continuous (A := A) (B := B) (C := SW) T
  exact ⟨_,h.1,h.2,he⟩
/-- A compatible family of rectangular kernel inverses defines a continuous inverse
on the directed union of product stages. -/
private theorem glue_on_rectangles {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [PolynormableSpace ℂ Z] (pure : SG → SH → Z)
    (det : ∀ J : Z →L[ℂ] Z, (∀ f g, J (pure f g) = pure f g) → J = ContinuousLinearMap.id ℂ Z)
    (K : Z →L[ℂ] SW)
    (d : ∀ a : BruhatStructuralPair G, ElementaryLCAPresentation a.quotient)
    (l : ∀ b : BruhatStructuralPair H, ElementaryLCAPresentation b.quotient)
    (m : ∀ i : BruhatStructuralPair G × BruhatStructuralPair H, ElementaryLCAPresentation (rectangularStructuralPair i.1 i.2).quotient)
    {T : BruhatStructuralPair G × BruhatStructuralPair H → Type*}
    [∀ i, AddCommGroup (T i)] [∀ i, Module ℂ (T i)] [∀ i, TopologicalSpace (T i)]
    (v : ∀ i, T i →L[ℂ] Z) (e : ∀ i, T i ≃L[ℂ] SchwartzBruhatStage (m i))
    (hu : ∀ i, K.comp (v i) = (schwartzBruhatStageCLM (rectangularStructuralPair i.1 i.2) (m i)).comp (e i).toContinuousLinearMap)
    (hm : ∀ i j, i ≤ j → ∀ z : T i, ∃ w, v j w = v i z)
    (hp : ∀ (i : BruhatStructuralPair G × BruhatStructuralPair H) (s : SchwartzBruhatStage (d i.1)) (t : SchwartzBruhatStage (l i.2)),
      ∃ z, v i z = pure (schwartzBruhatStageCLM i.1 (d i.1) s) (schwartzBruhatStageCLM i.2 (l i.2) t)) :
    ∃ E : Z ≃L[ℂ] SW, ∀ z, E z = K z := by
  let I := BruhatStructuralPair G × BruhatStructuralPair H
  let : IsDirectedOrder (BruhatStructuralPair G) := (bruhatStructuralPair_filtered (G := G)).2
  let : IsDirectedOrder (BruhatStructuralPair H) := (bruhatStructuralPair_filtered (G := H)).2
  let : Nonempty (BruhatStructuralPair G) := (bruhatStructuralPair_filtered (G := G)).1
  let : Nonempty (BruhatStructuralPair H) := (bruhatStructuralPair_filtered (G := H)).1
  let : IsDirectedOrder I := ⟨fun i j ↦ by
    obtain ⟨a,h₁,h₂⟩ := exists_ge_ge i.1 j.1
    obtain ⟨b,h₃,h₄⟩ := exists_ge_ge i.2 j.2
    exact ⟨(a,b),⟨h₁,h₃⟩,⟨h₂,h₄⟩⟩⟩
  let c (i : I) := schwartzBruhatStageCLM (rectangularStructuralPair i.1 i.2) (m i)
  let u (i : I) := (c i).comp (e i).toContinuousLinearMap
  have hi (i : I) : Injective (u i) :=
    (schwartzBruhatStageInclusion_injective (rectangularStructuralPair i.1 i.2) (m i)).comp (e i).injective
  refine kernel_equiv_of_stage_lifts (I := I) (T := T) K v u hu hi ?_ hm ?_ ?_
  · intro s
    refine (rectangular_stage_exhausts (G := G) (H := H) (fun a b ↦ m (a,b)) s).elim
      fun a h ↦ h.elim fun b h ↦ h.elim fun t ht ↦ ?_
    let i : I := (a,b)
    exact ⟨i,(e i).symm t,(congrArg (c i) ((e i).apply_symm_apply t)).trans ht⟩
  · intro J hJ
    apply rectangular_stage_continuity (G := G) (H := H) J
    intro a b
    let i : I := (a,b)
    refine ⟨m i,((v i).continuous.comp (e i).symm.continuous).congr fun t ↦ ?_⟩
    exact (hJ i ((e i).symm t)).symm.trans (congrArg J (congrArg (c i) ((e i).apply_symm_apply t)))
  · intro J hJ
    apply det J
    intro s t
    refine (test_from_chosen_stage d s).elim fun a h ↦ h.elim fun s' hs ↦ ?_
    refine (test_from_chosen_stage l t).elim fun b h ↦ h.elim fun t' ht ↦ ?_
    refine (hp (a,b) s' t').elim fun z hz ↦ ?_
    have ht' := hz.trans (congrArg₂ pure hs ht)
    exact (congrArg J ht'.symm).trans ((hJ (a,b) z).trans ht')
private theorem rectangular_kernel_glue {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    [PolynormableSpace ℂ Z] (pure : SG → SH → Z)
    (det : ∀ J : Z →L[ℂ] Z, (∀ f g, J (pure f g) = pure f g) → J = ContinuousLinearMap.id ℂ Z)
    (maps : ∀ (a : BruhatStructuralPair G) (d : ElementaryLCAPresentation a.quotient)
        (b : BruhatStructuralPair H) (l : ElementaryLCAPresentation b.quotient),
      ∃ v : Completion (InductiveTensor (SchwartzBruhatStage d) (SchwartzBruhatStage l)) →L[ℂ] Z, ∀ s t,
        v (Completion.coe' (α := InductiveTensor (SchwartzBruhatStage d) (SchwartzBruhatStage l)) (s ⊗ₜ[ℂ] t)) =
          pure (schwartzBruhatStageCLM a d s) (schwartzBruhatStageCLM b l t))
    (K : Z →L[ℂ] SW) (hK : ∀ f g x y, K (pure f g) (x,y) = f x * g y) :
    ∃ E : Z ≃L[ℂ] SW, ∀ f g x y, E (pure f g) (x,y) = f x * g y := by
  let I := BruhatStructuralPair G × BruhatStructuralPair H
  let d (a : BruhatStructuralPair G) := a.elementary.some
  let l (b : BruhatStructuralPair H) := b.elementary.some
  let w (i : I) := rectangularStructuralPair i.1 i.2
  let m (i : I) := (w i).elementary.some
  let A (a : BruhatStructuralPair G) := SchwartzBruhatStage (d a)
  let B (b : BruhatStructuralPair H) := SchwartzBruhatStage (l b)
  let T (i : I) := Completion (InductiveTensor (A i.1) (B i.2))
  let : T2Space SW := schwartzBruhat_t2
  let : ∀ a, T2Space (A a) := fun _ ↦ elementarySchwartz_t2
  let : ∀ b, T2Space (B b) := fun _ ↦ elementarySchwartz_t2
  let : ∀ a, PolynormableSpace ℂ (A a) := fun _ ↦ (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : ∀ b, PolynormableSpace ℂ (B b) := fun _ ↦ (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let f (a : BruhatStructuralPair G) := schwartzBruhatStageCLM a (d a)
  let g (b : BruhatStructuralPair H) := schwartzBruhatStageCLM b (l b)
  let c (i : I) := schwartzBruhatStageCLM (w i) (m i)
  let v (i : I) : T i →L[ℂ] Z := (maps i.1 (d i.1) i.2 (l i.2)).choose
  have hv (i : I) := (maps i.1 (d i.1) i.2 (l i.2)).choose_spec
  let e (i : I) := (rectangular_stage_kernel i.1 i.2 (d i.1) (l i.2) (m i)).choose
  have he (i : I) := (rectangular_stage_kernel i.1 i.2 (d i.1) (l i.2) (m i)).choose_spec
  let u (i : I) := (c i).comp (e i).toContinuousLinearMap
  have hu (i : I) : K.comp (v i) = u i := by
    refine completed_tensor_ext (X := A i.1) (Y := B i.2) fun s t ↦ Subtype.ext (funext fun ⟨x,y⟩ ↦ ?_)
    exact (congrArg (fun z : Z ↦ K z (x,y)) (hv i s t)).trans ((hK _ _ x y).trans (he i s t x y).symm)
  refine (glue_on_rectangles (Z := Z) (T := T) pure det K d l m v e hu ?_ ?_).elim
    fun E hE ↦ ⟨E,fun s t x y ↦ (congrArg (fun w : SW ↦ w (x,y)) (hE _)).trans (hK s t x y)⟩
  · intro i j hij z
    refine (schwartzBruhatStage_transition hij.1 (d i.1) (d j.1)).elim fun P hP ↦ ?_
    refine (schwartzBruhatStage_transition hij.2 (l i.2) (l j.2)).elim fun Q hQ ↦ ?_
    exact inclusion_tensor_range (A := A i.1) (B := B i.2) (C := A j.1) (D := B j.2)
      pure (f i.1) (g i.2) (f j.1) (g j.2) (v i) (v j) (hv i) (hv j) P Q
      (fun t ↦ Subtype.ext (hP.1 t)) (fun t ↦ Subtype.ext (hQ.1 t)) z
  · intro i s t
    exact ⟨Completion.coe' (α := InductiveTensor (A i.1) (B i.2)) (s ⊗ₜ[ℂ] t),hv i s t⟩

private theorem global_product_kernel :
    ∃ E : Z₀ ≃L[ℂ] SW, ∀ (f : SG) (g : SH) (x : G) (y : H),
      E (Completion.coe' (α := I₀) (f ⊗ₜ[ℂ] g)) (x,y) = f x * g y := by
  let : T2Space SG := schwartzBruhat_t2 (G := G)
  let : T2Space SH := schwartzBruhat_t2 (G := H)
  let : T2Space SW := schwartzBruhat_t2 (G := G × H)
  let : CompleteSpace SW := schwartzBruhat_complete (G := G × H)
  let : PolynormableSpace ℂ SG := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ SH := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ SW := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : ContinuousSMul ℂ SW := PolynormableSpace.continuousSMul ℂ SW
  let hs := rectangular_product_stages (G := G) (H := H)
  refine (kernel_bilinear hs).elim fun M hM ↦ ?_
  have hc := kernel_separate hs M hM
  let good (f : SG) (g : SH) (w : SW) := ∀ x y, w (x,y) = f x * g y
  apply product_kernel_from_stages (X := SG) (Y := SH) (W := SW) good M hM hc.1 hc.2
  intro Z _ _ _ _ _ pure hdet hmaps K hK
  refine rectangular_kernel_glue (G := G) (H := H) (Z := Z) pure hdet ?_ K hK
  intro a d b l
  let : T2Space (SchwartzBruhatStage d) := elementarySchwartz_t2
  let : T2Space (SchwartzBruhatStage l) := elementarySchwartz_t2
  exact hmaps (schwartzBruhatStageCLM a d) (schwartzBruhatStageCLM b l)

end RectangularKernels

end DistributionKernels

section Supports

open UniformSpace

local instance sec1cContinuousSMulSeminorms {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}
    (p : SeminormFamily ℂ X ι) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H]
  [hTopH : IsTopologicalGroup H] [hT2H : T2Space H] [hLCH : LocallyCompactSpace H]

include hTop hT2 hLC

include hTopH hT2H hLCH in
/-- Paper: Lemma D.1.8.1(1), p. 778. Multiplication of functions on the factors
gives a continuous linear isomorphism from the completed inductive tensor product
onto the Schwartz–Bruhat space of the product. -/
theorem schwartzBruhat_kernel_equiv [SecondCountableTopology G] [SecondCountableTopology H] :
    ∃ e : Completion (InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)) ≃L[ℂ]
        SchwartzBruhat (G × H),
      ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (x : G) (y : H),
        e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
          (f ⊗ₜ[ℂ] g)) (x, y) = f x * g y := by
  exact global_product_kernel (G := G) (H := H)

section DualKernelStages

omit hTop hT2 hLC
open TopologicalSpace Bornology

section Pullback

variable {m n r m' n' r' : ℕ} {F F' : Type}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']

omit [DiscreteTopology F] [Finite F] in
/-- The ambient noncompact coordinates descend through an open surjection with compact kernel.
Consequently their monomials are polynomial weights in the quotient coordinates. -/
private lemma stage_pullback_weight
    (H : AddSubgroup (ElementaryLieGroup m n r F))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hφ : IsOpenQuotientMap φ)
    (hK : IsCompact (φ.ker : Set H)) (α : Fin m → ℕ) (δ : Fin r → ℕ) :
    ∃ p : MvPolynomial (Fin m' ⊕ Fin r') ℂ, ∀ w : H,
      MvPolynomial.eval (Sum.elim (fun i ↦ ((φ w).1 i : ℂ)) (fun j ↦ ((φ w).2.2.1 j : ℂ))) p =
        (∏ i, (w.val.1 i : ℂ) ^ α i) * ∏ j, (w.val.2.2.1 j : ℂ) ^ δ j := by
  let coord (j : Fin m ⊕ Fin r) : H →+ ℝ := Sum.elim
    (fun i : Fin m ↦ ⟨⟨fun w : H ↦ w.val.1 i, rfl⟩, fun _ _ ↦ rfl⟩)
    (fun i : Fin r ↦ (Int.castAddHom ℝ).comp
      ⟨⟨fun w : H ↦ w.val.2.2.1 i, rfl⟩, fun _ _ ↦ rfl⟩) j
  have hc (j) : Continuous (coord j) := by
    cases j with
    | inl i => exact (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val.fst
    | inr i =>
      exact (continuous_of_discreteTopology (f := Int.castAddHom ℝ)).comp
        ((continuous_apply i).comp continuous_subtype_val.snd.snd.fst)
  let : CompactSpace φ.ker := isCompact_iff_compactSpace.mp hK
  have hk (j) : φ.ker ≤ (coord j).ker := fun w hw ↦
    compact_hom_real_zero ((coord j).comp φ.ker.subtype) ((hc j).comp continuous_subtype_val) ⟨w,hw⟩
  let l (j) := φ.liftOfRightInverseAux (Function.surjInv hφ.surjective)
    (Function.rightInverse_surjInv _) (coord j) (hk j)
  have he (j) (w : H) : l j (φ w) = coord j w := φ.liftOfRightInverseAux_comp_apply _ _ _ _ _
  have hl (j) : Continuous (l j) := hφ.isQuotientMap.continuous_iff.mpr
    ((hc j).congr fun w ↦ (he j w).symm)
  choose P hP using fun j ↦ elementary_real_hom_polynomial (l j) (hl j)
  refine ⟨(∏ i, P (.inl i) ^ α i) * ∏ j, P (.inr j) ^ δ j, fun w ↦ ?_⟩
  simp only [map_mul, map_prod, map_pow, hP, he]
  change _ * (∏ j, ((w.val.2.2.1 j : ℝ) : ℂ) ^ δ j) = _
  simp only [Complex.ofReal_intCast]
  rfl

omit [Finite F] in
/-- On a discrete fibre an open-subgroup cutoff either vanishes identically or
its quotient coordinate lifts to an affine map with fibre-independent linear part. -/
private lemma stage_pullback_charts
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hc : Continuous φ) :
    ∃ L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')),
      ∀ a b, (∀ x, elementaryCover x a b ∉ H) ∨
        ∃ y a' b', ∀ x, ∃ hw : elementaryCover x a b ∈ H,
          φ ⟨_, hw⟩ = elementaryCover (L x + y) a' b' := by
  let q := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  have hq := (elementaryCoverZeroHom_continuous_isOpenMap (m := m) (n := n) (r := r) (F := F)).1
  have hmem (x) : q x ∈ H := by
    have he := ((show IsClopen (H : Set (ElementaryLieGroup m n r F)) from ⟨H.isClosed_of_isOpen hH, hH⟩).preimage hq).eq_univ
      (show (q ⁻¹' (H : Set _)).Nonempty from ⟨0, by simp [q]⟩)
    exact eq_univ_iff_forall.mp he x
  let A := φ.comp (q.codRestrict H hmem)
  have hA : Continuous A := hc.comp (hq.subtype_mk _)
  let R := (AddMonoidHom.fst _ _).comp A
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp A)
  choose l hl using fun i : Fin n' ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hA.snd.fst)
  let L := (R.toRealLinearMap hA.fst).prod
    ((EuclideanSpace.equiv (Fin n') ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi l))
  refine ⟨L, fun a b ↦ ?_⟩
  have hshift (x) : q x + elementaryCover 0 a b = elementaryCover x a b := by
    simp [q, elementaryCoverZeroHom, elementaryCover, Pi.zero_def]
  by_cases hb : elementaryCover 0 a b ∈ H
  · right
    let c := φ ⟨_, hb⟩
    obtain ⟨t, ht⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
    refine ⟨(c.1, t), c.2.2.1, c.2.2.2, fun x ↦ ⟨(hshift x) ▸ H.add_mem (hmem x) hb, ?_⟩⟩
    have hs : (⟨elementaryCover x a b, (hshift x) ▸ H.add_mem (hmem x) hb⟩ : H) = q.codRestrict H hmem x + ⟨_,hb⟩ :=
      Subtype.ext (hshift x).symm
    rw [hs, map_add]
    change A x + c = _
    symm
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      have hti := congrArg (fun y : ElementaryLieGroup m' n' r' F' ↦ y.2.1 i) ht
      change ((l i x + t i : ℝ) : AddCircle (1 : ℝ)) = (A x).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hl i x]
      exact congrArg ((A x).2.1 i + ·) hti
    · have h := hA.snd.snd.isConst_of_preconnectedSpace x 0
      rw [map_zero A] at h
      change c.2.2 = (A x).2.2 + c.2.2
      rw [h]
      exact (zero_add _).symm
  · left
    intro x
    rwa [← hshift, H.add_mem_cancel_left (hmem x)]

omit [Finite F] in
/-- A Schwartz function pulled back by a quotient with compact kernel and extended by zero
from an open subgroup is still Schwartz. -/
private lemma stage_pullback_elementary
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hφ : IsOpenQuotientMap φ)
    (hK : IsCompact (φ.ker : Set H)) (s : ElementarySchwartz m' n' r' F')
    (g : ElementaryLieGroup m n r F → ℂ) (hon : ∀ w : H, g w.val = s (φ w))
    (hoff : ∀ w ∉ H, g w = 0) : g ∈ elementarySchwartzSubmodule m n r F := by
  classical
  obtain ⟨L, hL⟩ := stage_pullback_charts H hH φ hφ.continuous
  refine ⟨fun a b ↦ ?_, fun i ↦ ?_⟩
  · rcases hL a b with h | ⟨y, a', b', h⟩
    · simpa only [funext (fun x ↦ hoff _ (h x))] using (contDiff_const (c := (0 : ℂ)))
    · have he (x) : g (elementaryCover x a b) = s (elementaryCover (L x + y) a' b') := by
        obtain ⟨hw, hp⟩ := h x
        exact (hon ⟨_, hw⟩).trans (congrArg s.val hp)
      rw [funext he]
      exact (s.property.1 a' b').comp (L.contDiff.add contDiff_const)
  obtain ⟨p, hp⟩ := stage_pullback_weight H φ hφ hK i.1 i.2.2.2
  obtain ⟨T, c, hT⟩ := elementaryPartial_comp_lift (r := r') (r' := r) (F := F') (F' := F)
    L i.2.1 i.2.2.1
  let M (v : (Fin m' → ℕ) × (Fin n' → ℕ)) := ∑ d ∈ p.support, ‖p.coeff d‖ *
    elementarySchwartzSeminorm (fun k ↦ d (Sum.inl k), v.1, v.2, fun j ↦ d (Sum.inr j)) s
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ∑ v ∈ T, ‖c v‖ * M v))
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rcases hL a b with h | ⟨y, a', b', h⟩
  · simp [elementaryPartial, funext (fun u ↦ hoff _ (h u))]
  have he (x) : g (elementaryCover x a b) = s (elementaryCover (L x + y) a' b') := by
    obtain ⟨hw, hp⟩ := h x
    exact (hon ⟨_, hw⟩).trans (congrArg s.val hp)
  have hpart := hT s g y a b a' b' (s.property.1 a' b') he x
  obtain ⟨hw, hφw⟩ := h x
  have hwgt := hp ⟨_, hw⟩
  rw [hφw] at hwgt
  let vcoord := Sum.elim (fun k : Fin m' ↦ ((L x + y).1 k : ℂ)) (fun j : Fin r' ↦ (a' j : ℂ))
  change MvPolynomial.eval vcoord p =
    (∏ k, (x.1 k : ℂ) ^ i.1 k) * ∏ j, (a j : ℂ) ^ i.2.2.2 j at hwgt
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  change ‖_ * elementaryPartial g i.2.1 i.2.2.1 x a b‖ ≤ _
  rw [← hwgt, hpart, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ ?_)
  rw [norm_mul, norm_smul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left
    (elementarySchwartz_polynomial_weight_le_monomial_sum p s v.1 v.2 (L x + y) a' b') (norm_nonneg _)

omit [Finite F] in
/-- Two open coordinate maps from a common group produce the elementary representative, with
zero extension off the range of the larger-stage coordinate map. -/
private lemma stage_pullback_common {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    (p : A →+ ElementaryLieGroup m n r F) (pc : Continuous p) (po : IsOpenMap p)
    (q : A →+ ElementaryLieGroup m' n' r' F') (hq : IsOpenQuotientMap q)
    (hk : p.ker ≤ q.ker) (hK : IsCompact (q.ker : Set A)) (s : ElementarySchwartz m' n' r' F') :
    ∃ t : ElementarySchwartz m n r F, (∀ x, t (p x) = s (q x)) ∧ ∀ w ∉ p.range, t w = 0 := by
  classical
  let H := p.range
  have hH : IsOpen (H : Set (ElementaryLieGroup m n r F)) := by
    rw [AddMonoidHom.coe_range, ← image_univ]
    exact po _ isOpen_univ
  let j := p.rangeRestrict
  have hj : IsOpenQuotientMap j := by
    refine ⟨p.rangeRestrict_surjective, pc.subtype_mk _, ?_⟩
    intro U hU
    have he : j '' U = Subtype.val ⁻¹' (p '' U) := Set.ext fun w ↦
      ⟨fun ⟨x,hx,h⟩ ↦ ⟨x,hx,congrArg Subtype.val h⟩, fun ⟨x,hx,h⟩ ↦ ⟨x,hx,Subtype.ext h⟩⟩
    exact he ▸ (po _ hU).preimage continuous_subtype_val
  have hker : j.ker ≤ q.ker := fun x hx ↦ hk (congrArg Subtype.val (show j x = 0 from hx))
  let φ := j.liftOfRightInverseAux (Function.surjInv hj.surjective) (Function.rightInverse_surjInv _) q hker
  have he (x) : φ (j x) = q x := j.liftOfRightInverseAux_comp_apply _ _ _ _ x
  have hφ : IsOpenQuotientMap φ := by
    refine ⟨fun y ↦ (hq.surjective y).elim fun x hx ↦ ⟨j x, (he x).trans hx⟩,
      hj.isQuotientMap.continuous_iff.mpr (hq.continuous.congr (fun x ↦ (he x).symm)), ?_⟩
    intro U hU
    rw [← image_preimage_eq U hj.surjective, ← image_comp, show φ ∘ j = q from funext he]
    exact hq.isOpenMap _ (hU.preimage hj.continuous)
  have hKφ : IsCompact (φ.ker : Set H) := by
    have hEq : j ⁻¹' (φ.ker : Set H) = (q.ker : Set A) := Set.ext fun x ↦ by
      change φ (j x) = 0 ↔ q x = 0
      rw [he]
    rw [← image_preimage_eq (φ.ker : Set H) hj.surjective, hEq]
    exact hK.image hj.continuous
  let g (w : ElementaryLieGroup m n r F) := if hw : w ∈ H then s (φ ⟨_,hw⟩) else 0
  have hon (w : H) : g w = s (φ w) := dite_eq_left w.property
  have hoff (w) (hw : w ∉ H) : g w = 0 := dite_eq_right hw
  exact ⟨⟨g, stage_pullback_elementary H hH φ hφ hKφ s g hon hoff⟩,
    fun x ↦ (hon (j x)).trans (congrArg s.val (he x)), hoff⟩

end Pullback

section Stages
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
/-- Range inclusion, constructed in elementary coordinates, without using a transition map. -/
private lemma kernelStage_realization_mono {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient)
    (s : SchwartzBruhatStage e) : ∃ t : SchwartzBruhatStage d,
      schwartzBruhatStageRealization b d t = schwartzBruhatStageRealization a e s := by
  classical
  let inc := Subgroup.inclusion h.1
  let π := d.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
  let p := MonoidHom.toAdditive (π.comp inc)
  let q := MonoidHom.toAdditive (e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _))
  have pc : Continuous p := d.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
    (show Continuous inc from continuous_subtype_val.subtype_mk _))
  have po : IsOpenMap p := d.equiv.toHomeomorph.isOpenMap.comp
    ((QuotientGroup.isOpenMap_coe (N := (OrderDual.ofDual b.val.2).comap b.val.1.subtype)).comp
      (a.property.1.isOpenMap_inclusion h.1))
  have hq : IsOpenQuotientMap q := by
    refine ⟨fun w ↦ (e.equiv.surjective (Multiplicative.ofAdd w)).elim fun t ht ↦
      (QuotientGroup.mk_surjective t).elim fun x hx ↦ ⟨Additive.ofMul x, (congrArg e.equiv hx).trans ht⟩,
      e.equiv.continuous.comp (QuotientGroup.continuous_mk
        (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype)),
      e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe
        (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))⟩
  have hkle : OrderDual.ofDual b.val.2 ≤ OrderDual.ofDual a.val.2 := h.2
  have hker (x : Additive a.val.1) : x ∈ q.ker ↔ (Additive.toMul x).val ∈ OrderDual.ofDual a.val.2 := by
    change e.equiv (QuotientGroup.mk (Additive.toMul x)) = 1 ↔ _
    rw [← map_one e.equiv, e.equiv.injective.eq_iff, a.quotient_mk_eq_one]
  have hk : p.ker ≤ q.ker := by
    intro x hx
    apply (hker x).2
    apply hkle
    apply (b.quotient_mk_eq_one (inc (Additive.toMul x))).mp
    apply d.equiv.injective
    exact (show d.equiv (QuotientGroup.mk (inc (Additive.toMul x))) = 1 from hx).trans (map_one d.equiv).symm
  have hK : IsCompact (q.ker : Set (Additive a.val.1)) := by
    have heq : (q.ker : Set (Additive a.val.1)) =
        Subtype.val ⁻¹' ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G) := Set.ext hker
    rw [heq]
    exact (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage
      (compact_bruhat_kernel a)
  obtain ⟨t, hon, hoff⟩ := stage_pullback_common p pc po q hq hk hK s
  refine ⟨t, funext fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases ha : x ∈ a.val.1
  · rw [dite_eq_left ha, dite_eq_left (h.1 ha)]
    exact hon (Additive.ofMul ⟨x, ha⟩)
  rw [dite_eq_right ha]
  split_ifs with hb
  · let z : b.val.1 := ⟨x,hb⟩
    apply hoff
    rintro ⟨w, hw⟩
    change π (inc (Additive.toMul w)) = π z at hw
    have hkz : π (z / inc (Additive.toMul w)) = 1 := by rw [map_div, hw, div_self']
    have hk' := (b.quotient_mk_eq_one (z / inc (Additive.toMul w))).mp
      (d.equiv.injective (hkz.trans (map_one d.equiv).symm))
    apply ha
    have he := a.val.1.mul_mem (a.property.2.2.2 (hkle hk')) (Additive.toMul w).property
    change x / (Additive.toMul w).val * (Additive.toMul w).val ∈ a.val.1 at he
    simpa only [div_mul_cancel] using he
  · rfl

/-- The forward lift is continuous: both stages map continuously into the pointwise
range of the second, so Fréchet factorization applies to the constant second stage. -/
private lemma kernelStage_transitionMap {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage d,
      ∀ s, schwartzBruhatStageRealization b d (j s) = schwartzBruhatStageRealization a e s := by
  let A := schwartzBruhatStageRealization a e
  let B := schwartzBruhatStageRealization b d
  have hcA : Continuous A := continuous_pi (continuous_schwartzBruhatStage_eval a e)
  have hcB : Continuous B := continuous_pi (continuous_schwartzBruhatStage_eval b d)
  let i : SchwartzBruhatStage d →L[ℂ] B.range := ⟨B.rangeRestrict, hcB.subtype_mk _⟩
  let u : SchwartzBruhatStage e →L[ℂ] B.range :=
    ⟨A.codRestrict _ (kernelStage_realization_mono h e d), hcA.subtype_mk _⟩
  have hi : Function.Injective i := fun _ _ hz ↦
    schwartzBruhatStageInclusion_injective b d (Subtype.ext (congrArg (fun z : B.range ↦ z.val) hz))
  obtain ⟨_, j, hj⟩ := frechet_factorization (X := fun _ ↦ SchwartzBruhatStage d)
    (fun _ ↦ elementarySchwartz_isFrechet) (fun _ ↦ i) (fun _ ↦ hi) (fun _ ↦ Subset.rfl)
    (fun z ↦ ⟨0, z.property.elim fun t ht ↦ ⟨t, Subtype.ext ht⟩⟩) elementarySchwartz_isFrechet u
  exact ⟨j, fun s ↦ congrArg Subtype.val (DFunLike.congr_fun hj s)⟩

omit [T2Space G] [LocallyCompactSpace G] in
/-- Inside the larger stage, support and invariance are closed pointwise equations.
Descent identifies their common solution space with the range of the transition. -/
private lemma stage_clm_closed_range {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient)
    (j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage d)
    (hj : ∀ s, schwartzBruhatStageRealization b d (j s) = schwartzBruhatStageRealization a e s) :
    IsClosed (range j) := by
  classical
  let B := schwartzBruhatStageRealization b d
  let S := ⋂ x ∉ a.val.1, {t : SchwartzBruhatStage d | B t x = 0}
  let T := ⋂ (k : (OrderDual.ofDual a.val.2 : Subgroup G)), ⋂ x, {t : SchwartzBruhatStage d | B t (k.val*x) = B t x}
  have hEq : range j = S ∩ T := by
    ext t
    simp only [S, T, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    refine ⟨?_, fun ⟨hs,ht⟩ ↦ ?_⟩
    · rintro ⟨s,rfl⟩
      rw [show B (j s) = _ from hj s]
      exact ⟨fun x hx ↦ by rw [schwartzBruhatStageRealization_apply, dite_eq_right hx],
        fun k x ↦ stage_realization_mul_kernel a e s k.property x⟩
    · obtain ⟨s,he⟩ := schwartzBruhatStage_descend_of_invariant h e d t (B t) rfl hs
        (fun k hk ↦ ht ⟨k,hk⟩)
      exact ⟨s, schwartzBruhatStageInclusion_injective b d (Subtype.ext ((hj s).trans he))⟩
  rw [hEq]
  exact (isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ isClosed_eq
    (continuous_schwartzBruhatStage_eval b d x) continuous_const).inter
    (isClosed_iInter fun k ↦ isClosed_iInter fun x ↦ isClosed_eq
      (continuous_schwartzBruhatStage_eval b d (k.val*x)) (continuous_schwartzBruhatStage_eval b d x))

/-- An injective continuous linear map between Fréchet spaces with closed range is a closed
embedding: apply open mapping to its corestriction onto that complete subspace. -/
private lemma stage_frechet_closed_embedding {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsFrechetTVS X) (hY : IsFrechetTVS Y) (j : X →L[ℂ] Y) (hi : Function.Injective j)
    (hc : IsClosed (range j)) : IsClosedEmbedding j := by
  obtain ⟨hTX, hPX, hMX, hCX⟩ := hX
  obtain ⟨hTY, hPY, hMY, hCY⟩ := hY
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hCX
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Y := hCY
  let Z := j.range
  have hZ : IsClosed (Z : Set Y) := hc
  have : CompleteSpace Z := completeSpace_coe_iff_isComplete.mpr hZ.isComplete
  have : IsUniformAddGroup Z := Z.toAddSubgroup.isUniformAddGroup
  have : FirstCountableTopology Z := inferInstanceAs (FirstCountableTopology (Z : Set Y))
  have : (uniformity Z).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero Z]
    infer_instance
  have : BaireSpace Z := by
    let := UniformSpace.metricSpace Z
    infer_instance
  let p : X →L[ℂ] Z := j.rangeRestrict
  have hs : Function.Surjective p := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
  have hop := isOpenMap_of_not_isMeagre_range p (hs.range_eq ▸ not_isMeagre_of_isOpen isOpen_univ univ_nonempty)
  let eqv := Equiv.ofBijective p ⟨fun _ _ h ↦ hi (congrArg (fun z : Z ↦ z.val) h), hs⟩
  let homeo : X ≃ₜ Z := ⟨eqv, p.continuous, eqv.continuous_symm_iff.mpr hop⟩
  exact hZ.isClosedEmbedding_subtypeVal.comp homeo.isClosedEmbedding

/-- Paper: Lemma D.1.5.4, p. 762. Pullback and extension by zero give a closed
embedding between the elementary stages. -/
private lemma kernelStage_transition {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (e' : ElementaryLCAPresentation b.quotient) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e',
      (∀ f, schwartzBruhatStageRealization b e' (j f) = schwartzBruhatStageRealization a e f) ∧
        IsClosedEmbedding j := by
  obtain ⟨j,hj⟩ := kernelStage_transitionMap h e e'
  refine ⟨j,hj, stage_frechet_closed_embedding elementarySchwartz_isFrechet elementarySchwartz_isFrechet
    j (fun x y hxy ↦ ?_) (stage_clm_closed_range h e e' j hj)⟩
  apply schwartzBruhatStageInclusion_injective a e
  exact Subtype.ext ((hj x).symm.trans ((congrArg (schwartzBruhatStageRealization b e') hxy).trans (hj y)))


/-- Recover an open subgroup of the dual by separating in its quotient and writing every
separating bidual character as evaluation. -/
private lemma stage_ann_dualAnn {D : Subgroup (PontryaginDual G)} (hD : IsOpen (D : Set (PontryaginDual G))) :
    lcaAnnihilator (lcaDualAnnihilator D) = D := by
  obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
  ext χ
  constructor
  · intro hχ
    rw [← lcaDualAnnihilator_annihilator D (D.isClosed_of_isOpen hD), mem_lcaDualAnnihilator_iff]
    intro η
    obtain ⟨x, hx⟩ := e.surjective η.val
    have hη (ψ) : η.val ψ = ψ x := (hx ▸ he x ψ)
    rw [hη]
    exact (mem_lcaAnnihilator_iff _ _).mp hχ ⟨x, (mem_lcaDualAnnihilator_iff _ _).mpr fun ψ ↦
      (hη ψ.val).symm.trans ((mem_lcaAnnihilator_iff _ _).mp η.property ψ)⟩
  · intro hχ
    exact (mem_lcaAnnihilator_iff _ _).mpr fun x ↦ (mem_lcaDualAnnihilator_iff _ _).mp x.property ⟨χ,hχ⟩

/-- Compact exhaustion followed by taking successive upper bounds gives a cofinal sequence
of compactly generated open subgroups. -/
private lemma stage_cofinal_open_chain [SecondCountableTopology G] :
    ∃ H : ℕ → OpenCompactlyGeneratedSubgroups G, Monotone H ∧ ∀ J, ∃ n, J ≤ H n := by
  classical
  let C := CompactExhaustion.choice G
  choose B hB using fun n ↦ exists_openCompactlyGeneratedSubgroup_contains (C.isCompact n)
  choose upper hleft hright using (openCompactlyGeneratedSubgroups_colimit (G := G)).1.directed
  let chain : ℕ → OpenCompactlyGeneratedSubgroups G := Nat.rec (B 0) fun n prev ↦ upper prev (B (n+1))
  have hdom (n : ℕ) : B n ≤ chain n := by cases n <;> first | exact le_rfl | exact hright _ _
  refine ⟨chain, monotone_nat_of_le_succ fun n ↦ hleft _ _, fun J ↦ ?_⟩
  obtain ⟨D, _, hDc, hDgen⟩ := J.property.2
  obtain ⟨n, hn⟩ := C.exists_superset_of_isCompact (hDc.image continuous_subtype_val)
  have hD : D ⊆ ((B n).val.comap J.val.subtype : Set J.val) :=
    fun x hx ↦ hB n (hn ⟨x,hx,rfl⟩)
  have htop : ⊤ ≤ (B n).val.comap J.val.subtype := hDgen ▸ (Subgroup.closure_le _).mpr hD
  exact ⟨n, (show J ≤ B n from fun x hx ↦ htop (Subgroup.mem_top ⟨x,hx⟩)).trans (hdom n)⟩

/-- Exhaust the group and its dual simultaneously. Taking annihilators reverses the latter
chain, and shifting the former puts even the first compact kernel in every open subgroup. -/
private lemma kernelStage_cofinal_pairs [SecondCountableTopology G] :
    ∃ a : ℕ → BruhatStructuralPair G, Monotone a ∧ ∀ b, ∃ n, b ≤ a n := by
  let : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual G) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap G Circle).secondCountableTopology
  obtain ⟨H, hm, hcof⟩ := stage_cofinal_open_chain (G := G)
  obtain ⟨D, dm, dcof⟩ := stage_cofinal_open_chain (G := PontryaginDual G)
  let K (n : ℕ) := lcaDualAnnihilator (D n).val
  have hc n : IsCompact (K n : Set G) := isCompact_lcaDualAnnihilator _ (D n).property.1
  have hg n : IsBruhatGoodSubgroup (K n) :=
    ⟨(hc n).isClosed, (stage_ann_dualAnn (D n).property.1).symm ▸ (D n).property⟩
  have anti {A B : Subgroup (PontryaginDual G)} (h : A ≤ B) : lcaDualAnnihilator B ≤ lcaDualAnnihilator A :=
    fun x hx ↦ (mem_lcaDualAnnihilator_iff _ _).mpr fun χ ↦ (mem_lcaDualAnnihilator_iff _ _).mp hx ⟨χ.val,h χ.property⟩
  have hK : Antitone K := fun _ _ h ↦ anti (dm h)
  obtain ⟨J,hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains (hc 0)
  obtain ⟨m,hmJ⟩ := hcof J
  let a (n : ℕ) : BruhatStructuralPair G := ⟨((H (m+n)).val, OrderDual.toDual (K n)),
    (H (m+n)).property.1, (H (m+n)).property.2, hg n,
    (hK (Nat.zero_le n)).trans (hJ.trans (hmJ.trans (hm (Nat.le_add_right m n))))⟩
  refine ⟨a, fun i j h ↦ ⟨hm (Nat.add_le_add_left h m), hK h⟩, fun b ↦ ?_⟩
  let Kb := OrderDual.ofDual b.val.2
  obtain ⟨i,hi⟩ := hcof ⟨b.val.1,b.property.1,b.property.2.1⟩
  obtain ⟨j,hj⟩ := dcof ⟨lcaAnnihilator Kb, b.property.2.2.1.2⟩
  refine ⟨max i j, hi.trans (hm ((le_max_left i j).trans (Nat.le_add_left _ _))), ?_⟩
  change K (max i j) ≤ Kb
  rw [← lcaDualAnnihilator_annihilator Kb b.property.2.2.1.1]
  exact anti (hj.trans (dm (le_max_right i j)))

/-- Cofinality gives precisely the generating topology and the exhaustive union. -/
private lemma kernelStage_is_limit (a : ℕ → BruhatStructuralPair G) (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
    (hcof : ∀ b, ∃ n, b ≤ a n)
    (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1)))
    (hj : ∀ n x, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n x) =
      schwartzBruhatStageRealization (a n) (e n) x) :
    IsInjectiveLCLimit j (fun n ↦ schwartzBruhatStageCLM (a n) (e n)) := by
  refine ⟨fun n ↦ schwartzBruhatStageInclusion_injective _ _,
    fun n ↦ ContinuousLinearMap.ext (fun x ↦ Subtype.ext (hj n x)), ?_, ?_⟩
  · let R (n : ℕ) := (schwartzBruhatStageRealization (a n) (e n)).range
    have hR : Monotone R := monotone_nat_of_le_succ fun n _ ⟨s, hs⟩ ↦ ⟨j n s, (hj n s).trans hs⟩
    have hle : schwartzBruhatSubmodule G ≤ ⨆ n, R n := by
      refine iSup_le fun b ↦ iSup_le fun d ↦ ?_
      obtain ⟨n, hn⟩ := hcof b
      refine le_trans ?_ (le_iSup R n)
      rintro _ ⟨s,rfl⟩
      exact kernelStage_realization_mono hn d (e n) s
    intro f
    have hf : f.val ∈ ⨆ n, R n := hle f.property
    exact ((Submodule.mem_iSup_of_directed R hR.directed_le).mp hf).elim fun n hn ↦
      hn.elim fun s hs ↦ ⟨n,s,Subtype.ext hs⟩
  · apply congrArg (fun P : Seminorm ℂ (schwartzBruhatSubmodule G) → Prop ↦
      (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype P → Seminorm ℂ _)).topology)
    funext p
    apply propext
    refine ⟨fun h n ↦ h (a n) (e n), fun h b d ↦ ?_⟩
    exact (hcof b).elim fun n hn ↦ (kernelStage_transitionMap hn d (e n)).elim fun t ht ↦
      ((h n).comp t.continuous).congr fun x ↦ congrArg p (Subtype.ext (ht x))

/-- Paper: Lemma D.1.5.6, p. 763. A strict inductive presentation by a countable
cofinal family of stages, with exhaustive union and the prescribed seminorm topology. -/
private lemma kernelStage_exists_strict_limit [SecondCountableTopology G] :
    ∃ (a : ℕ → BruhatStructuralPair G) (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
      (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1))),
      Monotone a ∧ (∀ b, ∃ n, b ≤ a n) ∧
      (∀ n f, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n f) =
        schwartzBruhatStageRealization (a n) (e n) f) ∧
      (∀ n, IsClosedEmbedding (j n)) ∧
      IsInjectiveLCLimit j (fun n ↦ schwartzBruhatStageCLM (a n) (e n)) := by
  have hs := kernelStage_cofinal_pairs (G := G)
  let a := hs.choose
  let e (n : ℕ) := (a n).elementary.some
  have step (n : ℕ) := kernelStage_transition (hs.choose_spec.1 (Nat.le_succ n)) (e n) (e (n+1))
  let j (n : ℕ) := (step n).choose
  have hj (n : ℕ) := (step n).choose_spec.1
  exact ⟨a, e, j, hs.choose_spec.1, hs.choose_spec.2, hj, fun n ↦ (step n).choose_spec.2,
    kernelStage_is_limit a e hs.choose_spec.2 j hj⟩

end Stages

section KernelStages
universe v
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G]

omit [SecondCountableTopology G] in
private theorem kernel_barrelled : BarrelledSpace ℂ (SchwartzBruhat G) := by
  refine ⟨fun p hp ↦ schwartzBruhat_continuous_seminorm p ?_⟩
  intro a e
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  exact (p.comp (schwartzBruhatStageInclusion a e)).continuous_of_lowerSemicontinuous
    (hp.comp (continuous_schwartzBruhatStageInclusion a e))

/-- A strict cofinal presentation by elementary Schwartz stages gives completeness
and nuclearity on both sides of strong duality. -/
private theorem kernel_stage_properties
    (a : ℕ → BruhatStructuralPair G) (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
    (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n+1)))
    (hj : ∀ n, IsClosedEmbedding (j n))
    (hlim : IsInjectiveLCLimit j (fun n ↦ schwartzBruhatStageCLM (a n) (e n))) :
    CompleteSpace (SchwartzBruhat G) ∧ CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) ∧
    IsNuclearTVS.{v} (SchwartzBruhat G) ∧ IsNuclearTVS.{v} (StrongDual ℂ (SchwartzBruhat G)) := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  let : ∀ n, T2Space (SchwartzBruhatStage (e n)) := fun _ ↦ elementarySchwartz_t2
  let : ∀ n, CompleteSpace (StrongDual ℂ (SchwartzBruhatStage (e n))) :=
    fun _ ↦ elementarySchwartz_strongDual_complete
  let i n := schwartzBruhatStageCLM (a n) (e n)
  let res : StrongDual ℂ (SchwartzBruhat G) →L[ℂ] ((n : ℕ) → StrongDual ℂ (SchwartzBruhatStage (e n))) :=
    ContinuousLinearMap.pi fun n ↦ ContinuousLinearMap.precomp ℂ (i n)
  have hr : IsClosedEmbedding res := strongDual_closedEmbedding_of_strict_limit hlim hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hC := (strictLCLimit_complete_nonmetrizable (fun n ↦ (elementarySchwartz_isFrechet
        (m := (e n).realDim) (n := (e n).torusDim) (r := (e n).latticeRank) (F := (e n).finiteFactor)).choose_spec.2.2)
        hlim (fun n ↦ (hj n).isEmbedding)).1
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at hC
  · exact (completeSpace_iff_isComplete_range (AddMonoidHom.isUniformInducing_of_isInducing
      (f := res.toLinearMap.toAddMonoidHom) hr.isInducing)).mpr hr.isClosed_range.isComplete
  · exact nuclear_of_injective_frechet_sequence (fun _ ↦ elementarySchwartz_isFrechet)
      (fun _ ↦ elementarySchwartz_nuclear) j i hlim (fun n ↦ (hj n).isEmbedding)
  · exact schwartzBruhat_nuclear_of_embedding res.toLinearMap hr.isEmbedding
      (isNuclearTVS_pi fun n ↦ (isNuclearTVS_strongDual_iff elementarySchwartz_isFrechet).mpr elementarySchwartz_nuclear)

/-- Analytic properties of the countable strict elementary presentation. -/
private theorem kernel_space_properties :
    CompleteSpace (SchwartzBruhat G) ∧ CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) ∧
    IsNuclearTVS.{0} (SchwartzBruhat G) ∧ IsNuclearTVS.{0} (StrongDual ℂ (SchwartzBruhat G)) := by
  refine (kernelStage_exists_strict_limit (G := G)).elim fun a ha ↦ ha.elim fun d hd ↦ hd.elim fun j hj ↦ ?_
  exact kernel_stage_properties a d j hj.2.2.2.1 hj.2.2.2.2

end KernelStages

end DualKernelStages

/-- Paper: Lemma D.1.8.1(2), p. 778. The completed projective tensor product
of the strong duals is the strong dual on the product. On pure tensors
the identification multiplies the two evaluations. -/
theorem schwartzBruhat_strongDual_kernel_equiv [SecondCountableTopology G]
    [SecondCountableTopology H]
    (e : Completion (InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)) ≃L[ℂ]
      SchwartzBruhat (G × H))
    (he : ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (x : G) (y : H),
      e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
        (f ⊗ₜ[ℂ] g)) (x, y) = f x * g y) :
    ∃ E : Completion (ProjectiveTensor (StrongDual ℂ (SchwartzBruhat G))
          (StrongDual ℂ (SchwartzBruhat H))) ≃L[ℂ] StrongDual ℂ (SchwartzBruhat (G × H)),
      ∀ (S : StrongDual ℂ (SchwartzBruhat G)) (T : StrongDual ℂ (SchwartzBruhat H))
        (f : SchwartzBruhat G) (g : SchwartzBruhat H),
        E (Completion.coe' (α := ProjectiveTensor (StrongDual ℂ (SchwartzBruhat G))
          (StrongDual ℂ (SchwartzBruhat H))) (S ⊗ₜ[ℂ] T))
          (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
            (f ⊗ₜ[ℂ] g))) = S f * T g := by
  -- The evaluation formula is on images under `e`; it does not need their pointwise description.
  clear he
  let X := SchwartzBruhat G
  let Y := SchwartzBruhat H
  let Z := SchwartzBruhat (G × H)
  have hG := kernel_space_properties (G := G)
  have hH := kernel_space_properties (G := H)
  have hZ := kernel_space_properties (G := G × H)
  let : T2Space X := schwartzBruhat_t2 (G := G)
  let : T2Space Y := schwartzBruhat_t2 (G := H)
  let : T2Space Z := schwartzBruhat_t2 (G := G × H)
  let : BarrelledSpace ℂ X := kernel_barrelled (G := G)
  let : CompleteSpace X := hG.1
  let : CompleteSpace (StrongDual ℂ X) := hG.2.1
  let : CompleteSpace (StrongDual ℂ Y) := hH.2.1
  let : CompleteSpace Z := hZ.1
  let : PolynormableSpace ℂ (StrongDual ℂ Y) := hH.2.2.2.2.1
  with_reducible
    refine dualKernel_of_bounded_rectangles (X := X) (Y := Y) (Z := Z) hG.2.2.2 (fun B hB ↦ ?_) e
  -- In the complete nuclear product space, bounded sets have compact closure. Transport
  -- this compactness back to the tensor product, where we can work in a single pair of stages.
  have hcZ : IsCompact (closure (e '' B)) :=
    isCompact_closure_of_isNuclearTVS Z hZ.2.2.1 (hB.image e.toContinuousLinearMap)
  have hcB : IsCompact (closure B) :=
    e.toHomeomorph.isInducing.isCompact_iff.mpr (by rwa [e.toHomeomorph.image_closure])
  refine (kernelStage_exists_strict_limit (G := G)).elim fun a h ↦ h.elim fun d h ↦ h.elim fun j hj ↦ ?_
  refine (kernelStage_exists_strict_limit (G := H)).elim fun b h ↦ h.elim fun f h ↦ h.elim fun k hk ↦ ?_
  with_reducible
    exact completedInductiveTensor_bounded_rectangle
      (i := fun n ↦ schwartzBruhatStageCLM (a n) (d n))
      (l := fun n ↦ schwartzBruhatStageCLM (b n) (f n)) hj.2.2.2.2 hk.2.2.2.2
      (fun n ↦ (hj.2.2.2.1 n).isEmbedding) (fun n ↦ (hk.2.2.2.1 n).isEmbedding)
      (fun _ ↦ elementarySchwartz_isFrechet) (fun _ ↦ elementarySchwartz_isFrechet)
      (fun _ ↦ elementarySchwartz_nuclear) hcB

-- TODO(paper-gap): The proof after (D.1.8.3) cites part (1) for the strong-dual
-- tensor identification at the Fréchet stages. That step uses the nuclear Fréchet result.

/-- Paper: Definition D.1.8.2(1), p. 779. The vanishing locus is the union of
open sets on which the distribution kills all Schwartz–Bruhat tests supported there. -/
def schwartzBruhatVanishingLocus (T : StrongDual ℂ (SchwartzBruhat G)) : Set G :=
  ⋃₀ {U | IsOpen U ∧ ∀ f : SchwartzBruhat G, tsupport (f : G → ℂ) ⊆ U → T f = 0}

/-- Paper: Definition D.1.8.2(2), p. 779. The support is the complement of the
vanishing locus. -/
def schwartzBruhatDistributionSupport (T : StrongDual ℂ (SchwartzBruhat G)) : Set G :=
  (schwartzBruhatVanishingLocus T)ᶜ

section ElementaryTests

omit hTop hT2 hLC

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- Embed the real and torus factors in a vector space and localize a bump on one discrete fiber. -/
private theorem elementarySchwartz_exists_test {U : Set (ElementaryLieGroup m n r F)}
    (hU : IsOpen U) (x : ElementaryLieGroup m n r F) (hx : x ∈ U) :
    ∃ f : ElementarySchwartz m n r F, tsupport f.val ⊆ U ∧ f x = 1 := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let T := Fin n → AddCircle (1 : ℝ)
  let W := Fin n → ℂ
  let emb (p : E × T) : E × W := (p.1, fun j ↦ (AddCircle.toCircle (p.2 j) : ℂ))
  have ht : IsClosedEmbedding (fun t : AddCircle (1 : ℝ) ↦ (AddCircle.toCircle t : ℂ)) :=
    ((continuous_subtype_val.comp AddCircle.continuous_toCircle).isClosedEmbedding
      (Subtype.val_injective.comp (AddCircle.injective_toCircle one_ne_zero)))
  have he : IsClosedEmbedding emb := IsClosedEmbedding.id.prodMap (IsClosedEmbedding.piMap fun _ ↦ ht)
  let inc (p : E × T) : ElementaryLieGroup m n r F := (p.1,p.2,x.2.2.1,x.2.2.2)
  have hi : Continuous inc := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let t : E × T := (x.1,x.2.1)
  have hn : inc ⁻¹' U ∈ 𝓝 t := (hU.preimage hi).mem_nhds hx
  rw [he.isInducing.nhds_eq_comap] at hn
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hn
  obtain ⟨g,hg,hgc,hgs,-,hgx⟩ := exists_contDiff_tsupport_subset (n := ⊤) hV
  let f (y : ElementaryLieGroup m n r F) : ℂ :=
    if y.2.2 = x.2.2 then g (emb (y.1,y.2.1)) else 0
  let K := inc '' (emb ⁻¹' tsupport g)
  have hK : IsCompact K := (he.isCompact_preimage hgc).image hi
  have hS : tsupport f ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_cases hz : y.2.2 = x.2.2
    · refine ⟨(y.1,y.2.1), subset_tsupport g (fun h ↦ hy (by simp [f,hz,h])), ?_⟩
      exact Prod.ext rfl (Prod.ext rfl hz.symm)
    · exact (hy (by simp [f,hz])).elim
  have hsm (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (fun w ↦ f (elementaryCover w a b)) := by
    by_cases hz : (a,b) = x.2.2
    · change ContDiff ℝ ∞ (fun w ↦ if (a,b) = x.2.2 then _ else _)
      simp only [hz, ite_true]
      apply Complex.ofRealCLM.contDiff.comp
      apply hgs.comp
      apply ContDiff.prodMk contDiff_fst
      apply contDiff_pi.mpr
      intro j
      simp only [elementaryCover, AddCircle.toCircle_apply_mk,Circle.coe_exp]
      apply ContDiff.cexp
      apply ContDiff.mul _ contDiff_const
      apply Complex.ofRealCLM.contDiff.comp
      apply ContDiff.mul contDiff_const
      exact ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin n ↦ ℝ) j).contDiff).comp contDiff_snd
    · simpa only [f,elementaryCover,hz,ite_false] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E × EuclideanSpace ℝ (Fin n) ↦ (0 : ℂ)))
  refine ⟨⟨f, elementarySchwartz_of_compactSupport hsm (hK.of_isClosed_subset isClosed_closure hS)⟩,
    hS.trans ?_, ?_⟩
  · rintro _ ⟨p,hp,rfl⟩
    exact hVU (hg hp)
  · change f x = 1
    simpa [f,t] using congrArg Complex.ofReal hgx

end ElementaryTests

/-- Choose a structural quotient with a neighborhood whose entire lifted fiber lies in the given open set. -/
private theorem exists_stage_open_over {U : Set G} (hU : IsOpen U) {x : G} (hx : x ∈ U) :
    ∃ (a : BruhatStructuralPair G) (y : a.val.1) (V : Set a.quotient), y.val = x ∧
      IsOpen V ∧ QuotientGroup.mk y ∈ V ∧ ∀ t : a.val.1, QuotientGroup.mk t ∈ V → t.val ∈ U := by
  have hN : (fun z : G ↦ x*z) ⁻¹' U ∈ 𝓝 1 :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  obtain ⟨W, hW, h1, hWW⟩ := exists_open_nhds_one_split hN
  obtain ⟨H,hH⟩ := exists_lcaDualAnnihilator_subset_nhds (hW.mem_nhds h1)
  let k := lcaDualAnnihilator H.val
  have hγ := lca_dualSubgroup_quotient H
  have hkc : IsCompact (k : Set G) := by
    change IsCompact (lcaDualAnnihilator H.val : Set G)
    rw [← hγ.choose_spec.2.2.1]
    exact hγ.choose_spec.2.2.2
  have hk : IsBruhatGoodSubgroup k := by
    refine ⟨hkc.isClosed, ?_⟩
    change IsOpen (lcaAnnihilator (lcaDualAnnihilator H.val) : Set (PontryaginDual G)) ∧ _
    rw [lcaAnnihilator_dualAnnihilator_of_open H.val H.property.1]
    exact H.property
  obtain ⟨a, hak, hxa⟩ := exists_bruhatStructuralPair_mem k hk x
  let y : a.val.1 := ⟨x,hxa⟩
  let B : Set a.val.1 := (fun z : a.val.1 ↦ x⁻¹ * z.val) ⁻¹' W
  let V : Set a.quotient := QuotientGroup.mk '' B
  have hB : IsOpen B := hW.preimage (continuous_const.mul continuous_subtype_val)
  refine ⟨a, y, V, rfl, QuotientGroup.isOpenMap_coe B hB, mem_image_of_mem _ (show y ∈ B by simpa [B,y] using h1), ?_⟩
  intro t ht
  obtain ⟨v,hv,he⟩ := ht
  have hker := QuotientGroup.eq.mp he
  have ht' : v.val⁻¹ * t.val ∈ k := by
    rw [← hak]
    exact hker
  simpa only [Set.mem_preimage, inv_mul_cancel_left, mul_inv_cancel_left, ← mul_assoc, mul_inv_cancel, one_mul]
    using hWW (x⁻¹ * v.val) hv _ (hH ht')

/-- Lift an elementary test supported in a small quotient neighborhood and extend it by zero. -/
private theorem schwartzBruhat_exists_test {U : Set G} (hU : IsOpen U) {x : G} (hx : x ∈ U) :
    ∃ f : SchwartzBruhat G, tsupport f.val ⊆ U ∧ f x = 1 := by
  classical
  obtain ⟨a, y, V, hyx, hV, hyV, hVU⟩ := exists_stage_open_over (U := U) (x := x) hU hx
  let e := Classical.choice a.elementary
  let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let h : a.quotient ≃ₜ E := e.equiv.toHomeomorph.trans ⟨Multiplicative.toAdd, continuous_toAdd, continuous_ofAdd⟩
  let q : a.val.1 → a.quotient := QuotientGroup.mk
  have hV' : IsOpen (h.symm ⁻¹' V) := hV.preimage h.symm.continuous
  have hyV' : h (q y) ∈ h.symm ⁻¹' V := by simpa only [mem_preimage, h.symm_apply_apply] using hyV
  obtain ⟨s, hs, hsy⟩ := elementarySchwartz_exists_test hV' _ hyV'
  let f : SchwartzBruhat G := schwartzBruhatStageInclusion a e s
  let L : Set G := Subtype.val '' ((h ∘ q) ⁻¹' tsupport s.val)
  have hc : IsClosed L := (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isClosedMap _
    (isClosed_tsupport s.val |>.preimage (h.continuous.comp QuotientGroup.continuous_mk))
  refine ⟨f, (closure_minimal (t := L) ?_ hc).trans ?_, ?_⟩
  · intro z hz
    change schwartzBruhatStageRealization a e s z ≠ 0 at hz
    rw [schwartzBruhatStageRealization_apply] at hz
    split_ifs at hz with hzJ
    · exact ⟨⟨z,hzJ⟩, subset_tsupport s.val hz, rfl⟩
    · exact (hz rfl).elim
  · rintro _ ⟨t,ht,rfl⟩
    have hmem := hs ht
    exact hVU t (by simpa only [mem_preimage,Function.comp_apply,h.symm_apply_apply] using hmem)
  · rw [← hyx]
    change schwartzBruhatStageRealization a e s (y : G) = 1
    rw [schwartzBruhatStageRealization_apply,dite_eq_left y.property]
    exact hsy

/-- Paper: Definition D.1.8.2, p. 779. Point evaluation vanishes precisely off
the evaluation point and has singleton support.
Deviation: Sanity check on both the vanishing locus and the support. -/
theorem schwartzBruhat_dirac_support (x : G) :
    ∃ δ : StrongDual ℂ (SchwartzBruhat G),
      (∀ f, δ f = f x) ∧
      schwartzBruhatVanishingLocus δ = {x}ᶜ ∧ schwartzBruhatDistributionSupport δ = {x} :=
by
  classical
  let ev : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp ev
  let idx : {p : Seminorm ℂ (schwartzBruhatSubmodule G) // ∀ a e, Continuous (p ∘ schwartzBruhatStageInclusion a e)} :=
    ⟨p, fun a e ↦ by
      change Continuous ((normSeminorm ℂ ℂ).comp (ev.comp (schwartzBruhatStageInclusion a e)))
      apply Seminorm.continuous_of_le (elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0))
      intro f
      change ‖schwartzBruhatStageRealization a e f x‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f
      rw [schwartzBruhatStageRealization_apply]
      split_ifs
      · change (‖f _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
        apply ENNReal.toReal_mono (f.property.2 _).ne
        rw [elementarySchwartzBound_zero]
        exact le_iSup (fun y ↦ (‖f y‖₊ : ENNReal)) _
      · exact norm_zero.trans_le (apply_nonneg _ _)⟩
  let δ : StrongDual ℂ (SchwartzBruhat G) := ⟨ev,
    (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp ev
      fun _ ↦ (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm idx⟩
  have hδ : schwartzBruhatVanishingLocus δ = {x}ᶜ := by
    ext y
    constructor
    · rintro ⟨U, ⟨hU,hkill⟩,hy⟩ rfl
      obtain ⟨f,hf,hfx⟩ := schwartzBruhat_exists_test hU hy
      exact one_ne_zero (α := ℂ) (hfx.symm.trans (hkill f hf))
    · intro hy
      refine ⟨{x}ᶜ, ⟨isClosed_singleton.isOpen_compl, ?_⟩, hy⟩
      intro f hf
      change f x = 0
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hf h (mem_singleton x))
  exact ⟨δ, fun _ ↦ rfl, hδ, by rw [schwartzBruhatDistributionSupport, hδ, compl_compl]⟩

section TensorSupports

omit hTop hT2 hLC

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Compact support descends from a realization to its elementary test. -/
private theorem stage_compact_of_realization (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) (h : HasCompactSupport (schwartzBruhatStageRealization a e s)) :
    HasCompactSupport s.val := by
  let R := schwartzBruhatStageRealization a e s
  let ψ (x : a.val.1) := (e.equiv (QuotientGroup.mk x)).toAdd
  have hψ : Continuous ψ := continuous_toAdd.comp (e.equiv.continuous.comp QuotientGroup.continuous_mk)
  have hc : IsCompact (Subtype.val ⁻¹' tsupport R : Set a.val.1) :=
    (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage h
  apply HasCompactSupport.intro (hc.image hψ)
  intro y hy
  obtain ⟨x,hx⟩ := QuotientGroup.mk_surjective (e.equiv.symm (Multiplicative.ofAdd y))
  have hxy : ψ x = y := congrArg Multiplicative.toAdd ((congrArg e.equiv hx).trans (e.equiv.apply_symm_apply _))
  have hx' : x.val ∉ tsupport R := fun hh ↦ hy ⟨x,hh,hxy⟩
  have he := schwartzBruhatStageRealization_apply a e s x.val
  rw [dite_eq_left x.property] at he
  exact hxy ▸ he.symm.trans (image_eq_zero_of_notMem_tsupport hx')

/-- Multiplication by a compactly supported elementary test is continuous by point evaluation. -/
private theorem elementarySchwartz_compactMultiplier {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (u : ElementarySchwartz m n r F) (hu : HasCompactSupport u.val) :
    ∃ M : ElementarySchwartz m n r F →L[ℂ] ElementarySchwartz m n r F, ∀ f x, M f x = u x * f x := by
  let E := ElementarySchwartz m n r F
  let M : E →ₗ[ℂ] E :=
    { toFun := fun f ↦ ⟨fun x ↦ u x * f x, elementarySchwartz_of_compactSupport
        (fun a b ↦ (u.property.1 a b).mul (f.property.1 a b)) (hu.mul_right (f' := f.val))⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ mul_add (u x) (f x) (g x))
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ mul_left_comm (u x) c (f x)) }
  let : BarrelledSpace ℂ E := elementarySchwartz_barrelled
  let : ContinuousSMul ℂ E := elementarySchwartz_withSeminorms.continuousSMul
  have hM : Continuous M := by
    apply continuous_toElementarySchwartz_of_eval
    intro x
    let ev : E →L[ℂ] ℂ := ⟨(LinearMap.proj x).comp (elementarySchwartzSubmodule m n r F).subtype,
      elementarySchwartz_continuousEval.comp (continuous_id.prodMk continuous_const)⟩
    exact ⟨u x • ev,fun _ ↦ rfl⟩
  exact ⟨⟨M,hM⟩,fun _ _ ↦ rfl⟩

private theorem stageRealization_mul (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (u v w : SchwartzBruhatStage e) (h : ∀ y, w y = u y * v y) (x : G) :
    schwartzBruhatStageRealization a e w x = schwartzBruhatStageRealization a e u x * schwartzBruhatStageRealization a e v x := by
  simp only [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact h _
  · exact (zero_mul _).symm

private theorem schwartzBruhat_compactMultiplier_pair (u : SchwartzBruhat G) (hu : HasCompactSupport u.val)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (c : BruhatStructuralPair G) (t : ElementaryLCAPresentation c.quotient)
    (v : SchwartzBruhatStage t) (hv : schwartzBruhatStageRealization c t v = u.val)
    (i : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage t)
    (hi : ∀ f, schwartzBruhatStageRealization c t (i f) = schwartzBruhatStageRealization a e f) :
    ∃ A : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G, ∀ f x, A f x = u x * schwartzBruhatStageRealization a e f x := by
  have hcomp := stage_compact_of_realization c t v (hv.symm ▸ hu)
  let M := (elementarySchwartz_compactMultiplier v hcomp).choose
  have hM := (elementarySchwartz_compactMultiplier v hcomp).choose_spec
  let k : SchwartzBruhatStage t →L[ℂ] SchwartzBruhat G := ⟨schwartzBruhatStageInclusion c t,
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property c t⟩
  refine ⟨k.comp (M.comp i), fun f x ↦ ?_⟩
  change schwartzBruhatStageRealization c t (M (i f)) x = _
  exact (stageRealization_mul c t v (i f) (M (i f)) (hM (i f)) x).trans
    (congrArg₂ (·*·) (congrFun hv x) (congrFun (hi f) x))

/-- A common structural stage realizes the product with a fixed compactly supported test. -/
private theorem schwartzBruhat_compactMultiplier_stage (u : SchwartzBruhat G) (hu : HasCompactSupport u.val)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    ∃ A : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G, ∀ f x, A f x = u x * schwartzBruhatStageRealization a e f x := by
  classical
  refine ((mem_schwartzBruhatSubmodule_iff u.val).mp u.property).elim fun b hb ↦ hb.elim fun d hd ↦ hd.elim fun v hv ↦ ?_
  let : IsDirectedOrder (BruhatStructuralPair G) := bruhatStructuralPair_filtered.2
  refine (exists_ge_ge a b).elim fun c hc ↦ ?_
  let t := Classical.choice c.elementary
  refine (schwartzBruhatStage_transition hc.1 e t).elim fun i hi ↦ ?_
  refine (schwartzBruhatStage_transition hc.2 d t).elim fun j hj ↦ ?_
  exact schwartzBruhat_compactMultiplier_pair u hu a e c t (j v) ((hj.1 v).trans hv) i hi.1

/-- Compactly supported Schwartz functions act continuously by multiplication on all stages. -/
private theorem schwartzBruhat_compactMultiplier (u : SchwartzBruhat G) (hu : HasCompactSupport u.val) :
    ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f x, M f x = u x * f x := by
  classical
  choose A hA using schwartzBruhat_compactMultiplier_stage u hu
  have hmem (f : SchwartzBruhat G) : u.val * f.val ∈ schwartzBruhatSubmodule G := by
    obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
    have h : (A a e s).val = u.val * f.val := funext fun x ↦ (hA a e s x).trans (congrArg (u x * ·) (congrFun hs x))
    exact h ▸ (A a e s).property
  let M : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G :=
    { toFun := fun f ↦ ⟨u.val * f.val,hmem f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ mul_add (u x) (f x) (g x))
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ mul_left_comm (u x) c (f x)) }
  have hM : Continuous M := by
    let P : SeminormFamily ℂ (SchwartzBruhat G) {q : Seminorm ℂ (SchwartzBruhat G) //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
    have hP : WithSeminorms P := ⟨rfl⟩
    refine hP.continuous_of_continuous_comp M fun p ↦ hP.continuous_seminorm ⟨p.val.comp M,fun a e ↦ ?_⟩
    exact ((hP.continuous_seminorm p).comp (A a e).continuous).congr fun s ↦
      congrArg p.val (Subtype.ext (funext (hA a e s)))
  exact ⟨⟨M,hM⟩,fun _ _ ↦ rfl⟩

/-- Smooth postcomposition by a function vanishing at zero preserves the Schwartz–Bruhat
property of a compactly supported test function. -/
theorem compact_schwartzBruhat_comp {f : SchwartzBruhat G} (hc : HasCompactSupport f.val)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (h0 : φ 0 = 0) :
    ∃ u : SchwartzBruhat G, u.val = φ ∘ f.val := by
  obtain ⟨a,e,s,hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  have hsc := stage_compact_of_realization a e s (hs.symm ▸ hc)
  let v : SchwartzBruhatStage e := ⟨φ ∘ s.val, elementarySchwartz_of_compactSupport
    (fun j b ↦ hφ.comp (s.property.1 j b)) (hsc.comp_left h0)⟩
  refine ⟨schwartzBruhatStageInclusion a e v,funext fun x ↦ ?_⟩
  change schwartzBruhatStageRealization a e v x = φ (f x)
  rw [← congrFun hs x,schwartzBruhatStageRealization_apply,schwartzBruhatStageRealization_apply]
  split_ifs
  · rfl
  · exact h0.symm

/-- Every open neighborhood contains the support of a compactly supported Schwartz–Bruhat
test function equal to one near the given point. -/
theorem schwartzBruhat_exists_local_unit {x : G} {U : Set G} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ u : SchwartzBruhat G, HasCompactSupport u.val ∧ tsupport u.val ⊆ U ∧ u.val =ᶠ[𝓝 x] 1 := by
  obtain ⟨K,hK,hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨f,hf,hfx⟩ := schwartzBruhat_exists_test (hU.inter isOpen_interior) ⟨hx,mem_interior_iff_mem_nhds.mpr hxK⟩
  have hcf : HasCompactSupport f.val := hK.of_isClosed_subset isClosed_closure
    (hf.trans (inter_subset_right.trans interior_subset))
  let g : ContDiffBump (1 : ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have h0 : g 0 = 0 := g.zero_of_le_dist (by norm_num [g])
  let φ (z : ℂ) : ℂ := g z
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp g.contDiff
  have hφ0 : φ 0 = 0 := by simp [φ,h0]
  obtain ⟨u,hu⟩ := compact_schwartzBruhat_comp hcf hφ hφ0
  have hsubset : tsupport u.val ⊆ tsupport f.val := by
    rw [hu]
    exact tsupport_comp_subset hφ0 _
  obtain ⟨b,hb⟩ := schwartzBruhat_boundedContinuous f
  have hc : Tendsto f.val (𝓝 x) (𝓝 1) := (b.continuous.congr hb).tendsto' _ _ hfx
  refine ⟨u, hcf.of_isClosed_subset isClosed_closure hsubset, hsubset.trans (hf.trans inter_subset_left), ?_⟩
  filter_upwards [hc.eventually g.eventuallyEq_one] with y hy
  change u.val y = 1
  simp only [hu,Function.comp_apply,φ,show g (f y) = 1 from hy,Complex.ofReal_one]

/-- A continuous functional on a completed inductive tensor is determined by pure tensors. -/
private theorem completedTensor_ext_zero {X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) (L : Z →L[ℂ] ℂ)
    (h : ∀ (x : X) (y : Y), L (e (Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y))) = 0) :
    ∀ z, L z = 0 := by
  let j : InductiveTensor X Y →L[ℂ] Completion (InductiveTensor X Y) := Completion.toComplL
  let A : X ⊗[ℂ] Y →ₗ[ℂ] ℂ := L.toLinearMap.comp (e.toLinearEquiv.toLinearMap.comp j.toLinearMap)
  have hz : A = 0 := TensorProduct.ext' h
  intro z
  exact Completion.induction_on (p := fun u ↦ L (e u) = 0) (e.symm z)
    (isClosed_eq (L.continuous.comp e.continuous) continuous_const) (fun u ↦ LinearMap.congr_fun hz u)
    |> fun h ↦ (congrArg L (e.apply_symm_apply z)).symm.trans h

private def completedTensor_right {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) (f : X) : Y →L[ℂ] Z :=
  let j : InductiveTensor X Y →L[ℂ] Completion (InductiveTensor X Y) := Completion.toComplL
  let hsp := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) // (∀ x : X, Continuous (fun y : Y ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : Y, Continuous (fun x : X ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  e.toContinuousLinearMap.comp (j.comp ⟨TensorProduct.mk ℂ X Y f,
    hsp.continuous_of_continuous_comp (TensorProduct.mk ℂ X Y f) fun p ↦ p.property.1 f⟩)

private theorem completedTensor_right_apply {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] Z) (f : X) (g : Y) :
    completedTensor_right (X := X) (Y := Y) e f g = e (Completion.coe' (α := InductiveTensor X Y) (f ⊗ₜ[ℂ] g)) := rfl

variable {G H I J : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] [SecondCountableTopology H]
  [CommGroup I] [TopologicalSpace I] [IsTopologicalGroup I] [T2Space I]
  [LocallyCompactSpace I] [SecondCountableTopology I]
  [CommGroup J] [TopologicalSpace J] [IsTopologicalGroup J] [T2Space J]
  [LocallyCompactSpace J] [SecondCountableTopology J]

private theorem schwartzBruhat_product_tests :
    ∃ b : SchwartzBruhat G → SchwartzBruhat H →L[ℂ] SchwartzBruhat (G × H),
      (∀ f g x y, b f g (x,y) = f x * g y) ∧
      ∀ L : SchwartzBruhat (G × H) →L[ℂ] ℂ, (∀ f g, L (b f g) = 0) → ∀ s, L s = 0 := by
  refine (schwartzBruhat_kernel_equiv (G := G) (H := H)).elim fun e he ↦ ?_
  let b := completedTensor_right (X := SchwartzBruhat G) (Y := SchwartzBruhat H) e
  have hb (f : SchwartzBruhat G) (g : SchwartzBruhat H) := completedTensor_right_apply e f g
  refine ⟨b,fun f g x y ↦ (congrArg (fun w : SchwartzBruhat (G × H) ↦ w (x,y)) (hb f g)).trans (he f g x y),?_⟩
  exact fun L h ↦ completedTensor_ext_zero (X := SchwartzBruhat G) (Y := SchwartzBruhat H) e L
    (fun f g ↦ (congrArg L (hb f g)).symm.trans (h f g))

/-- Iterating the binary kernel isomorphism gives products determining every continuous functional. -/
private theorem schwartzBruhat_fourfold_tests :
    ∃ b : SchwartzBruhat G → SchwartzBruhat H → SchwartzBruhat I → SchwartzBruhat J →
        SchwartzBruhat (G × H × I × J),
      (∀ f g s t x, b f g s t x = f x.1 * g x.2.1 * s x.2.2.1 * t x.2.2.2) ∧
      ∀ L : SchwartzBruhat (G × H × I × J) →L[ℂ] ℂ,
        (∀ f g s t, L (b f g s t) = 0) → ∀ u, L u = 0 := by
  refine (schwartzBruhat_product_tests (G := G) (H := H × I × J)).elim fun A hA ↦ ?_
  refine (schwartzBruhat_product_tests (G := H) (H := I × J)).elim fun B hB ↦ ?_
  refine (schwartzBruhat_product_tests (G := I) (H := J)).elim fun C hC ↦ ?_
  refine ⟨fun f g s t ↦ A f (B g (C s t)),fun f g s t x ↦ ?_,fun L h ↦ ?_⟩
  · rcases x with ⟨x,y,z,w⟩
    refine (hA.1 f (B g (C s t)) x _).trans ?_
    rw [hB.1,hC.1,mul_assoc,mul_assoc]
  · exact hA.2 L fun f ↦ hB.2 (L.comp (A f)) fun g ↦ hC.2 ((L.comp (A f)).comp (B g)) (h f g)

private theorem tsupport_fourfold {X Y Z A : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace A] {f : X → ℂ} {g : Y → ℂ} {h : Z → ℂ} {k : A → ℂ}
    {s : X × Y × Z × A → ℂ} (hs : ∀ x, s x = f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2) :
    tsupport s ⊆ tsupport f ×ˢ (tsupport g ×ˢ (tsupport h ×ˢ tsupport k)) := by
  apply closure_minimal _ ((isClosed_tsupport f).prod ((isClosed_tsupport g).prod ((isClosed_tsupport h).prod (isClosed_tsupport k))))
  intro x hx
  have hn : f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2 ≠ 0 := hs x ▸ hx
  rcases mul_ne_zero_iff.mp hn with ⟨h₃,h₄⟩
  rcases mul_ne_zero_iff.mp h₃ with ⟨h₂,h₃⟩
  rcases mul_ne_zero_iff.mp h₂ with ⟨h₁,h₂⟩
  exact ⟨subset_tsupport _ h₁,subset_tsupport _ h₂,subset_tsupport _ h₃,subset_tsupport _ h₄⟩

private theorem distribution_support_test (T : StrongDual ℂ (SchwartzBruhat G)) {x : G}
    (hx : x ∈ schwartzBruhatDistributionSupport T) {U : Set G} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ f : SchwartzBruhat G, tsupport f.val ⊆ U ∧ T f ≠ 0 := by
  by_contra! h
  exact hx ⟨U,⟨hU,h⟩,hxU⟩

variable (d₁ : StrongDual ℂ (SchwartzBruhat G)) (d₂ : StrongDual ℂ (SchwartzBruhat H))
  (d₃ : StrongDual ℂ (SchwartzBruhat I)) (d₄ : StrongDual ℂ (SchwartzBruhat J))
  (d : StrongDual ℂ (SchwartzBruhat (G × H × I × J)))
variable (b : SchwartzBruhat G → SchwartzBruhat H → SchwartzBruhat I → SchwartzBruhat J →
    SchwartzBruhat (G × H × I × J))
  (hb : ∀ f g s t (x : G × H × I × J), b f g s t x = f x.1 * g x.2.1 * s x.2.2.1 * t x.2.2.2)
  (hd : ∀ f g s t, d (b f g s t) = d₁ f * d₂ g * d₃ s * d₄ t)
  (hext : ∀ L : SchwartzBruhat (G × H × I × J) →L[ℂ] ℂ, (∀ f g s t, L (b f g s t) = 0) → ∀ u, L u = 0)

include hb hd in
/-- A rectangle around four support points contains a product of tests with nonzero pairing. -/
private theorem fourfold_product_subset_support :
    schwartzBruhatDistributionSupport d₁ ×ˢ (schwartzBruhatDistributionSupport d₂ ×ˢ
        (schwartzBruhatDistributionSupport d₃ ×ˢ schwartzBruhatDistributionSupport d₄)) ⊆
      schwartzBruhatDistributionSupport d := by
  rintro ⟨x,y,z,w⟩ ⟨hx,hy,hz,hw⟩ ⟨U,⟨hU,hkill⟩,hmem⟩
  obtain ⟨V₁,W,h₁,hx₁,hW,hW₀,hsub⟩ := mem_nhds_prod_iff'.mp (hU.mem_nhds hmem)
  obtain ⟨V₂,W',h₂,hy₂,hW',hW₀',hsub'⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hW₀)
  obtain ⟨V₃,V₄,h₃,hz₃,h₄,hw₄,hsub''⟩ := mem_nhds_prod_iff'.mp (hW'.mem_nhds hW₀')
  obtain ⟨f,hf,hnf⟩ := distribution_support_test d₁ hx h₁ hx₁
  obtain ⟨g,hg,hng⟩ := distribution_support_test d₂ hy h₂ hy₂
  obtain ⟨s,hs,hns⟩ := distribution_support_test d₃ hz h₃ hz₃
  obtain ⟨t,ht,hnt⟩ := distribution_support_test d₄ hw h₄ hw₄
  have hsup := tsupport_fourfold (hb f g s t)
  have h0 := hkill (b f g s t) (fun v hv ↦ hsub ⟨hf (hsup hv).1,hsub' ⟨hg (hsup hv).2.1,
    hsub'' ⟨hs (hsup hv).2.2.1,ht (hsup hv).2.2.2⟩⟩⟩)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hnf hng) hns) hnt ((hd f g s t).symm.trans h0)

private theorem tsupport_of_mul_left {X : Type*} [TopologicalSpace X] {u v w : X → ℂ}
    (h : ∀ x, w x = u x * v x) : tsupport w ⊆ tsupport u :=
  closure_mono fun x hx hx₀ ↦ hx ((h x).trans (by rw [hx₀,zero_mul]))

private theorem fourfold_mul_reorder (a b c d e f g h : ℂ) :
    (a*b*c*d)*(e*f*g*h) = (a*e)*(b*f)*(c*g)*(d*h) := by ring

include hb hext in
/-- Localizing each factor by a cutoff transfers vanishing from pure products to all nearby tests. -/
private theorem fourfold_vanish_on_rectangle {p : G × H × I × J}
    {U₁ : Set G} {U₂ : Set H} {U₃ : Set I} {U₄ : Set J}
    (h₁ : IsOpen U₁) (h₂ : IsOpen U₂) (h₃ : IsOpen U₃) (h₄ : IsOpen U₄)
    (hp : p ∈ U₁ ×ˢ (U₂ ×ˢ (U₃ ×ˢ U₄)))
    (hkill : ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (s : SchwartzBruhat I) (t : SchwartzBruhat J), tsupport (f : G → ℂ) ⊆ U₁ → tsupport (g : H → ℂ) ⊆ U₂ →
        tsupport (s : I → ℂ) ⊆ U₃ → tsupport (t : J → ℂ) ⊆ U₄ → d (b f g s t) = 0) :
    p ∈ schwartzBruhatVanishingLocus d := by
  obtain ⟨v₁,hc₁,hv₁,he₁⟩ := schwartzBruhat_exists_local_unit h₁ hp.1
  obtain ⟨v₂,hc₂,hv₂,he₂⟩ := schwartzBruhat_exists_local_unit h₂ hp.2.1
  obtain ⟨v₃,hc₃,hv₃,he₃⟩ := schwartzBruhat_exists_local_unit h₃ hp.2.2.1
  obtain ⟨v₄,hc₄,hv₄,he₄⟩ := schwartzBruhat_exists_local_unit h₄ hp.2.2.2
  let v := b v₁ v₂ v₃ v₄
  have hvc : HasCompactSupport v.val := (hc₁.prod (hc₂.prod (hc₃.prod hc₄))).of_isClosed_subset
    isClosed_closure (tsupport_fourfold (hb v₁ v₂ v₃ v₄))
  let M := (schwartzBruhat_compactMultiplier v hvc).choose
  have hM := (schwartzBruhat_compactMultiplier v hvc).choose_spec
  have hkill' : ∀ f g s t, d (M (b f g s t)) = 0 := by
    intro f g s t
    let M₁ := schwartzBruhat_compactMultiplier v₁ hc₁
    let M₂ := schwartzBruhat_compactMultiplier v₂ hc₂
    let M₃ := schwartzBruhat_compactMultiplier v₃ hc₃
    let M₄ := schwartzBruhat_compactMultiplier v₄ hc₄
    have hEq : M (b f g s t) = b (M₁.choose f) (M₂.choose g) (M₃.choose s) (M₄.choose t) := by
      apply Subtype.ext
      funext x
      change M (b f g s t) x = _
      refine ((hM _ x).trans (congrArg₂ (·*·) (hb v₁ v₂ v₃ v₄ x) (hb f g s t x))).trans ?_
      refine (fourfold_mul_reorder ..).trans (Eq.trans ?_ (hb _ _ _ _ x).symm)
      exact congrArg₂ (·*·) (congrArg₂ (·*·) (congrArg₂ (·*·)
        (M₁.choose_spec f x.1).symm (M₂.choose_spec g x.2.1).symm)
        (M₃.choose_spec s x.2.2.1).symm) (M₄.choose_spec t x.2.2.2).symm
    apply (congrArg d hEq).trans
    exact hkill (M₁.choose f) (M₂.choose g) (M₃.choose s) (M₄.choose t) ((tsupport_of_mul_left (M₁.choose_spec f)).trans hv₁)
      ((tsupport_of_mul_left (M₂.choose_spec g)).trans hv₂)
      ((tsupport_of_mul_left (M₃.choose_spec s)).trans hv₃)
      ((tsupport_of_mul_left (M₄.choose_spec t)).trans hv₄)
  have hall := hext (d.comp M) hkill'
  have hone : v.val =ᶠ[𝓝 p] 1 := by
    filter_upwards [continuous_fst.continuousAt.eventually he₁,
      (continuous_fst.comp continuous_snd).continuousAt.eventually he₂,
      (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually he₃,
      (continuous_snd.comp (continuous_snd.comp continuous_snd)).continuousAt.eventually he₄] with x h₁ h₂ h₃ h₄
    change b v₁ v₂ v₃ v₄ x = 1
    change v₁ x.1 = 1 at h₁
    change v₂ x.2.1 = 1 at h₂
    change v₃ x.2.2.1 = 1 at h₃
    change v₄ x.2.2.2 = 1 at h₄
    simp only [hb,h₁,h₂,h₃,h₄,one_mul]
  obtain ⟨W,hW,hWo,hpW⟩ := mem_nhds_iff.mp hone
  refine ⟨W,⟨hWo,fun f hf ↦ ?_⟩,hpW⟩
  have he : M f = f := by
    apply Subtype.ext
    funext x
    change M f x = f x
    rw [hM]
    by_cases hx : x ∈ tsupport f.val
    · rw [show v x = 1 from hW (hf hx),one_mul]
    · rw [show f x = 0 from image_eq_zero_of_notMem_tsupport hx,mul_zero]
  exact (congrArg d he).symm.trans (hall f)

private theorem fourfold_mul_zero_d {a b c d : ℂ} (h : d = 0) : a*b*c*d = 0 := by simp [h]

private theorem fourfold_mul_zero_c {a b c d : ℂ} (h : c = 0) : a*b*c*d = 0 := by simp [h]

private theorem fourfold_mul_zero_b {a b c d : ℂ} (h : b = 0) : a*b*c*d = 0 := by simp [h]

private theorem fourfold_mul_zero_a {a b c d : ℂ} (h : a = 0) : a*b*c*d = 0 := by simp [h]


include hb hd hext in
private theorem fourfold_support_subset_product :
    schwartzBruhatDistributionSupport d ⊆ (schwartzBruhatDistributionSupport d₁ ×ˢ
      (schwartzBruhatDistributionSupport d₂ ×ˢ (schwartzBruhatDistributionSupport d₃ ×ˢ
        schwartzBruhatDistributionSupport d₄))) := by
  intro p hp
  have hv {U₁ U₂ U₃ U₄} (h₁ : IsOpen U₁) (h₂ : IsOpen U₂) (h₃ : IsOpen U₃) (h₄ : IsOpen U₄)
      (h : p ∈ U₁ ×ˢ (U₂ ×ˢ (U₃ ×ˢ U₄))) :
      ¬ (∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (s : SchwartzBruhat I) (t : SchwartzBruhat J), tsupport (f : G → ℂ) ⊆ U₁ → tsupport (g : H → ℂ) ⊆ U₂ →
        tsupport (s : I → ℂ) ⊆ U₃ → tsupport (t : J → ℂ) ⊆ U₄ → d (b f g s t) = 0) :=
    fun hkill ↦ hp (fourfold_vanish_on_rectangle d b hb hext h₁ h₂ h₃ h₄ h hkill)
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv hU isOpen_univ isOpen_univ isOpen_univ ⟨hx,trivial,trivial,trivial⟩
      fun f g s t hf _ _ _ ↦ (hd f g s t).trans (fourfold_mul_zero_a (hkill f hf))
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv isOpen_univ hU isOpen_univ isOpen_univ ⟨trivial,hx,trivial,trivial⟩
      fun f g s t _ hg _ _ ↦ (hd f g s t).trans (fourfold_mul_zero_b (hkill g hg))
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv isOpen_univ isOpen_univ hU isOpen_univ ⟨trivial,trivial,hx,trivial⟩
      fun f g s t _ _ hs _ ↦ (hd f g s t).trans (fourfold_mul_zero_c (hkill s hs))
  · rintro ⟨U,⟨hU,hkill⟩,hx⟩
    exact hv isOpen_univ isOpen_univ isOpen_univ hU ⟨trivial,trivial,trivial,hx⟩
      fun f g s t _ _ _ ht ↦ (hd f g s t).trans (fourfold_mul_zero_d (hkill t ht))

private theorem distribution_eval_of_pointwise {X : Type*} [CommGroup X] [TopologicalSpace X]
    (T : StrongDual ℂ (SchwartzBruhat X)) (v : SchwartzBruhat X) {u : X → ℂ} {c : ℂ}
    (hv : ∀ x, v x = u x) (h : ∃ w : SchwartzBruhat X, (∀ x, w x = u x) ∧ T w = c) :
    T v = c :=
  h.elim fun _w hw ↦ (congrArg T (Subtype.ext (funext fun x ↦ (hv x).trans (hw.1 x).symm))).trans hw.2

private theorem fourfold_distribution_support
    (h : ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (s : SchwartzBruhat I) (t : SchwartzBruhat J),
      ∃ v : SchwartzBruhat (G × H × I × J),
        (∀ x, v x = f x.1 * g x.2.1 * s x.2.2.1 * t x.2.2.2) ∧
          d v = d₁ f * d₂ g * d₃ s * d₄ t) :
    schwartzBruhatDistributionSupport d = (schwartzBruhatDistributionSupport d₁ ×ˢ
      (schwartzBruhatDistributionSupport d₂ ×ˢ (schwartzBruhatDistributionSupport d₃ ×ˢ
        schwartzBruhatDistributionSupport d₄))) := by
  refine (schwartzBruhat_fourfold_tests (G := G) (H := H) (I := I) (J := J)).elim fun B hB ↦ ?_
  have hpair (f g s t) : d (B f g s t) = d₁ f * d₂ g * d₃ s * d₄ t :=
    distribution_eval_of_pointwise d (B f g s t) (hB.1 f g s t) (h f g s t)
  exact Subset.antisymm (fourfold_support_subset_product d₁ d₂ d₃ d₄ d B hB.1 hpair hB.2)
    (fourfold_product_subset_support d₁ d₂ d₃ d₄ d B hB.1 hpair)

end TensorSupports

omit hTop hT2 hLC in
/-- Paper: Proposition D.1.8.3, p. 779. The support of a tensor product of four
tempered distributions on the elementary factors is the product of their supports.
Deviation: The tensor distribution is characterized by its pairings with pure tensors. -/
theorem elementary_schwartzBruhat_tensor_support
    (m n r : ℕ) {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    let R := Multiplicative (EuclideanSpace ℝ (Fin m))
    let T := Multiplicative (Fin n → AddCircle (1 : ℝ))
    let Z := Multiplicative (Fin r → ℤ)
    let A := Multiplicative F
    ∀ (d₁ : StrongDual ℂ (SchwartzBruhat R)) (d₂ : StrongDual ℂ (SchwartzBruhat T))
      (d₃ : StrongDual ℂ (SchwartzBruhat Z)) (d₄ : StrongDual ℂ (SchwartzBruhat A))
      (d : StrongDual ℂ (SchwartzBruhat (R × T × Z × A))),
      (∀ (f₁ : SchwartzBruhat R) (f₂ : SchwartzBruhat T) (f₃ : SchwartzBruhat Z)
        (f₄ : SchwartzBruhat A), ∃ f : SchwartzBruhat (R × T × Z × A),
        (∀ x, f x = f₁ x.1 * f₂ x.2.1 * f₃ x.2.2.1 * f₄ x.2.2.2) ∧
        d f = d₁ f₁ * d₂ f₂ * d₃ f₃ * d₄ f₄) →
      schwartzBruhatDistributionSupport d =
        schwartzBruhatDistributionSupport d₁ ×ˢ (schwartzBruhatDistributionSupport d₂ ×ˢ
          (schwartzBruhatDistributionSupport d₃ ×ˢ schwartzBruhatDistributionSupport d₄)) :=
  by
    intro R T Z A d₁ d₂ d₃ d₄ d h
    exact fourfold_distribution_support (G := R) (H := T) (I := Z) (J := A) d₁ d₂ d₃ d₄ d h

open Classical in
/-- Compose the inverse elementary identification with the canonical stage inclusion. -/
private theorem schwartzBruhatStageLift_of_equiv (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (I : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhat a.quotient)
    (hI : ∀ f (x : a.quotient), I f x = f (e.equiv x).toAdd) :
    ∃ j : SchwartzBruhat a.quotient →L[ℂ] SchwartzBruhat G, ∀ (f : SchwartzBruhat a.quotient) (x : G),
      j f x = if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x,hx⟩ : a.quotient) else 0 := by
  classical
  let j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G := ⟨schwartzBruhatStageInclusion a e,
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property a e⟩
  refine ⟨j.comp I.symm.toContinuousLinearMap, fun f x ↦ ?_⟩
  change schwartzBruhatStageRealization a e (I.symm f) x = _
  refine (schwartzBruhatStageRealization_apply a e (I.symm f) x).trans ?_
  apply congrArg (fun u : x ∈ a.val.1 → ℂ ↦ dite (x ∈ a.val.1) u (fun _ ↦ 0))
  funext hx
  let y : a.quotient := QuotientGroup.mk (⟨x,hx⟩ : a.val.1)
  have he : I (I.symm f) y = f y :=
    congrArg (fun z : SchwartzBruhat a.quotient ↦ z y) (I.apply_symm_apply f)
  exact (hI (I.symm f) y).symm.trans he

open Classical in
/-- Pull back a Schwartz function on the structural quotient and extend it by zero. -/
private theorem schwartzBruhatStageLift (a : BruhatStructuralPair G) :
    ∃ j : SchwartzBruhat a.quotient →L[ℂ] SchwartzBruhat G, ∀ (f : SchwartzBruhat a.quotient) (x : G),
      j f x = if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x,hx⟩ : a.quotient) else 0 := by
  classical
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.mpr (a.property.2.2.1.1.preimage continuous_subtype_val)
  let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let e := Classical.choice a.elementary
  exact (elementarySchwartz_equiv_schwartzBruhat e).elim fun I hI ↦ schwartzBruhatStageLift_of_equiv a e I hI

open Classical in
/-- The closed subgroup contains the support of the lift over the closed support downstairs. -/
private theorem schwartzBruhatStageLift_tsupport (a : BruhatStructuralPair G) (f : SchwartzBruhat a.quotient)
    (g : SchwartzBruhat G) (hg : ∀ x : G, g x =
      if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x,hx⟩) else 0)
    {V : Set a.quotient} {U : Set G} (hf : tsupport f.val ⊆ V)
    (hU : ∀ t : a.val.1, QuotientGroup.mk t ∈ V → t.val ∈ U) : tsupport g.val ⊆ U := by
  let q : a.val.1 → a.quotient := QuotientGroup.mk
  let L : Set G := Subtype.val '' (q ⁻¹' tsupport f.val)
  have hL : IsClosed L := (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isClosedMap _
    ((isClosed_tsupport f.val).preimage QuotientGroup.continuous_mk)
  refine (closure_minimal (t := L) ?_ hL).trans ?_
  · intro z hz
    change g z ≠ 0 at hz
    rw [hg] at hz
    split_ifs at hz with h
    · exact ⟨⟨z,h⟩, subset_tsupport f.val hz, rfl⟩
    · exact (hz rfl).elim
  · rintro _ ⟨t, ht, rfl⟩
    exact hU t (hf ht)

open Classical in
/-- Paper: Lemma D.1.8.4, p. 780. Pullback and extension by zero are continuous
on a structural quotient and induce restriction of a tempered distribution.
The vanishing locus of the original distribution is covered by the lifted
vanishing loci of these restrictions. -/
theorem schwartzBruhatVanishingLocus_subset_stages (T : StrongDual ℂ (SchwartzBruhat G)) :
    ∃ j : ∀ a : BruhatStructuralPair G, SchwartzBruhat a.quotient →L[ℂ] SchwartzBruhat G,
      (∀ (a : BruhatStructuralPair G) (f : SchwartzBruhat a.quotient) (x : G),
        j a f x = if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x, hx⟩) else 0) ∧
      schwartzBruhatVanishingLocus T ⊆
        ⋃ a : BruhatStructuralPair G,
          Subtype.val '' (QuotientGroup.mk ⁻¹' schwartzBruhatVanishingLocus (T.comp (j a))) :=
by
  classical
  let j (a : BruhatStructuralPair G) := (schwartzBruhatStageLift a).choose
  have hj (a : BruhatStructuralPair G) := (schwartzBruhatStageLift a).choose_spec
  refine ⟨j, hj, ?_⟩
  rintro x ⟨U, ⟨hU, hT⟩, hx⟩
  refine (exists_stage_open_over (G := G) (U := U) (x := x) hU hx).elim fun a ha ↦
    ha.elim fun y hy ↦ hy.elim fun V h ↦ ?_
  have hkill (f : SchwartzBruhat a.quotient) (hf : tsupport f.val ⊆ V) : T (j a f) = 0 :=
    hT (j a f) (schwartzBruhatStageLift_tsupport a f (j a f) (hj a f) hf h.2.2.2)
  exact mem_iUnion.mpr ⟨a, y, ⟨V, ⟨h.2.1, hkill⟩, h.2.2.1⟩, h.1⟩

end Supports

section ElementaryTranslations

open scoped BoundedContinuousFunction

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

omit [TopologicalSpace F] [DiscreteTopology F] [Finite F] in
private theorem elementaryPartial_translate (g : ElementaryLieGroup m n r F) (v) (hv : elementaryCover v g.2.2.1 g.2.2.2 = g)
    (f : ElementaryLieGroup m n r F → ℂ) (β γ) (u) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (fun x ↦ f (g + x)) β γ u a b =
      elementaryPartial f β γ (u + v) (a + g.2.2.1) (b + g.2.2.2) := by
  have h (w) : g + elementaryCover w a b =
      elementaryCover (w+v) (a+g.2.2.1) (b+g.2.2.2) := by
    rw [add_comm, ← hv]
    exact elementaryCover_add ..
  simp only [elementaryPartial, h]
  rw [iteratedFDeriv_comp_add_right (f := fun w ↦ f (elementaryCover w (a+g.2.2.1) (b+g.2.2.2))) _ v u]

private def elementaryLatticeVector (a : Fin r → ℤ) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun k ↦ (a k : ℝ))

private theorem elementaryMonomial_translate_le {k : ℕ} (x t : EuclideanSpace ℝ (Fin k)) (α : Fin k → ℕ) {M : ℝ}
    (hM : ‖t‖ ≤ M) :
    ‖∏ j, (x j : ℂ) ^ α j‖ ≤ (1 + M) ^ (∑ j, α j) * (1 + ‖x + t‖ ^ (∑ j, α j)) := by
  let R := max 1 ‖x+t‖
  have hR : 1 ≤ R := le_max_left ..
  have hM0 := (norm_nonneg t).trans hM
  have h (j : Fin k) : ‖(x j : ℂ)‖ ≤ (1 + M) * R := by
    rw [Complex.norm_real]
    have hx : ‖x‖ ≤ ‖x+t‖ + ‖t‖ := by simpa using norm_sub_le (x+t) t
    calc
      ‖x j‖ ≤ ‖x‖ := PiLp.norm_apply_le x j
      _ ≤ R + M := hx.trans (add_le_add (le_max_right ..) hM)
      _ ≤ (1 + M) * R := by nlinarith [mul_le_mul_of_nonneg_left hR hM0]
  have hpow (d : ℕ) : R ^ d ≤ 1 + ‖x+t‖ ^ d := by
    dsimp [R]
    rcases le_total 1 ‖x+t‖ with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
  rw [norm_prod]
  calc
    _ ≤ ∏ j, ((1 + M) * R) ^ α j := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      (fun j _ ↦ by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (h j) (α j))
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpow _) (by positivity)

/-- On bounded sets of translating parameters, each translated seminorm is dominated
by a single continuous seminorm of the original function. -/
private theorem elementarySchwartzBound_translate_le (i : ElementarySchwartzIndex m n r) (M : ℝ) (hM : 0 ≤ M) :
    ∃ p : Seminorm ℂ (ElementarySchwartz m n r F), Continuous p ∧
      ∀ (g : ElementaryLieGroup m n r F) (f : ElementarySchwartz m n r F),
        ‖g.1‖ ≤ M → ‖elementaryLatticeVector g.2.2.1‖ ≤ M →
        elementarySchwartzBound (fun x ↦ f (g+x)) i ≤ ENNReal.ofReal (p f) := by
  obtain ⟨P, hP, hval⟩ := elementarySchwartz_withSeminorms_P1 (m := m) (n := n) (r := r) (F := F)
  let d := ∑ j, i.1 j
  let l := ∑ j, i.2.2.2 j
  let C : ℝ≥0 := ⟨(1+M)^d * (1+M)^l, by positivity⟩
  let q := P (d, l, i.2.1, i.2.2.1)
  refine ⟨C • q, (hP.continuous_seminorm _).const_smul (C : ℝ), fun g f hx ha ↦ ?_⟩
  obtain ⟨t, ht⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
  let v := (g.1,t)
  refine iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have hL : elementaryLatticeVector a + elementaryLatticeVector g.2.2.1 = elementaryLatticeVector (a+g.2.2.1) := by
    ext k
    change (a k : ℝ) + (g.2.2.1 k : ℝ) = ((a k + g.2.2.1 k : ℤ) : ℝ)
    exact (Int.cast_add ..).symm
  let D := ‖elementaryPartial f i.2.1 i.2.2.1 (u+v) (a+g.2.2.1) (b+g.2.2.2)‖
  let X := (1 + ‖u.1+g.1‖^d)
  let Z := (1 + ‖elementaryLatticeVector (a+g.2.2.1)‖^l)
  have hf : X * Z * D ≤ q f := by
    apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg q f)).mp
    rw [show ENNReal.ofReal (q f) = _ from hval _ f]
    exact le_iSup_of_le (u+v) (le_iSup_of_le (a+g.2.2.1) (le_iSup_of_le (b+g.2.2.2) le_rfl))
  have h₁ : ‖∏ k, (u.1 k : ℂ) ^ i.1 k‖ ≤ (1+M)^d * X := elementaryMonomial_translate_le u.1 g.1 i.1 hx
  have h₂ : ‖∏ k, (a k : ℂ) ^ i.2.2.2 k‖ ≤ (1+M)^l * Z := by
    have h := elementaryMonomial_translate_le (elementaryLatticeVector a) (elementaryLatticeVector g.2.2.1) i.2.2.2 ha
    rw [hL] at h
    simpa only [Z, l, elementaryLatticeVector, PiLp.toLp_apply, Complex.ofReal_intCast] using h
  rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _), coe_nnNorm,
    norm_mul, norm_mul, elementaryPartial_translate g v ht]
  calc
    _ ≤ ((1+M)^d * X) * ((1+M)^l * Z) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ (norm_nonneg _) (by dsimp [X]; positivity)) (norm_nonneg _)
    _ = (C : ℝ) * (X * Z * D) := by change _ = ((1+M)^d * (1+M)^l) * _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf C.property

end ElementaryTranslations

section Translations

variable {H E : Type*} [Group H] [TopologicalSpace H] [hTopH : IsTopologicalGroup H]

open scoped ComplexOrder in
include hTopH in
/-- Paper: Lemma D.1.9.1, p. 780. A linear group action on a strict inductive
limit of barrelled spaces is continuous if it jointly acts at each stage through
the corresponding subsystem of open subgroups.
Deviation: Stages are identified with their images with the subspace topology.
Linearity is explicit, as in the proof's representation by linear operators. -/
theorem continuous_action_strict_inductive_limit [T2Space H] [LocallyCompactSpace H]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E] [PolynormableSpace ℂ E]
    (K : ℕ → OpenSubgroup H) (hK : Monotone K) (hK' : ∀ h : H, ∃ n, h ∈ K n)
    (S : ℕ → Submodule ℂ E) (hS : Monotone S) (hS' : ∀ x : E, ∃ n, x ∈ S n)
    (hFinal : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun n ↦ (S n).subtype))
    (hBarrelled : ∀ n, BarrelledSpace ℂ (S n))
    (ρ : H →* (E ≃ₗ[ℂ] E))
    (hPreserve : ∀ n (k : K n) (x : S n), ρ k.val x.val ∈ S n)
    (hContinuous : ∀ n, Continuous (fun p : K n × S n ↦ ρ p.1.val p.2.val)) :
    Continuous (fun p : H × E ↦ ρ p.1 p.2) := by
  -- The compact-open argument only needs the stage actions to be continuous into E.
  clear hBarrelled hPreserve
  let : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).isTopologicalAddGroup
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : LocallyConvexSpace ℂ E := .ofBasisZero ℂ E _ _ (LocallyConvexSpace.convex_basis_zero ℝ E)
    (fun _ hs ↦ convex_of_nonneg_surjective_algebraMap ℂ
      (fun _ hz ↦ RCLike.nonneg_iff_exists_ofReal.mp hz) hs.2)
  let : ContinuousSMul ℝ C(H, E) := IsScalarTower.continuousSMul ℂ
  have hStage (n : ℕ) : Continuous (fun p : H × S n ↦ ρ p.1 p.2.val) := by
    rw [continuous_iff_continuousAt]
    intro ⟨h, x⟩
    obtain ⟨m, hm⟩ := hK' h
    let l := max m n
    have hh : h ∈ K l := hK (le_max_left m n) hm
    let inc : S n →L[ℂ] S l := (S n).subtypeL.codRestrict (S l)
      (fun y ↦ hS (le_max_right m n) y.property)
    have he := (K l).isOpen.isOpenEmbedding_subtypeVal.prodMap
      (IsOpenEmbedding.id (X := S n))
    apply (he.continuousAt_iff (x := (⟨h, hh⟩, x))).mp
    exact ((hContinuous l).comp (continuous_fst.prodMk (inc.continuous.comp continuous_snd))).continuousAt
  have hOrbit (x : E) : Continuous (fun h ↦ ρ h x) := by
    obtain ⟨n, hx⟩ := hS' x
    exact (hStage n).comp (continuous_id.prodMk (continuous_const (y := (⟨x, hx⟩ : S n))))
  let A : E →ₗ[ℂ] C(H, E) :=
    { toFun := fun x ↦ ⟨fun h ↦ ρ h x, hOrbit x⟩
      map_add' := fun x y ↦ ContinuousMap.ext fun h ↦ map_add (ρ h) x y
      map_smul' := fun c x ↦ ContinuousMap.ext fun h ↦ (ρ h).map_smul c x }
  have hP : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ E // ∀ n, Continuous (p ∘ (S n).subtype)} → _) := ⟨hFinal⟩
  have hA : Continuous A := by
    refine (PolynormableSpace.withSeminorms ℂ C(H, E)).continuous_of_continuous_comp A fun p ↦ ?_
    refine hP.continuous_seminorm ⟨p.val.comp A, fun n ↦ p.property.comp ?_⟩
    exact ContinuousMap.continuous_of_continuous_uncurry _ ((hStage n).comp continuous_swap)
  exact continuous_eval.comp ((hA.comp continuous_snd).prodMk continuous_fst)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

omit hTop hT2 hLC in
/-- Paper: Proposition D.1.9.2, p. 781. On an elementary group, shifting the argument
by addition preserves the Schwartz space and is jointly continuous for the weighted
derivative seminorm topology. -/
theorem elementarySchwartz_translate_jointly {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    ∃ T : C(ElementaryLieGroup m n r F × ElementarySchwartz m n r F,
        ElementarySchwartz m n r F),
      ∀ g f x, T (g, f) x = f (g + x) := by
  let E := ElementarySchwartz m n r F
  let X := ElementaryLieGroup m n r F
  let size (g : X) := max ‖g.1‖ ‖elementaryLatticeVector g.2.2.1‖
  have hsize : Continuous size := continuous_fst.norm.max
    ((continuous_of_discreteTopology (f := fun a ↦ ‖elementaryLatticeVector (r := r) a‖)).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hmem (g : X) (f : E) : (fun x ↦ f (g+x)) ∈ elementarySchwartzSubmodule m n r F := by
    constructor
    · intro a b
      obtain ⟨v, hv⟩ := elementaryCover_surjective g.2.2.1 g.2.2.2 g.1 g.2.1
      change elementaryCover (g.1,v) g.2.2.1 g.2.2.2 = g at hv
      have heq (u) : g + elementaryCover u a b =
          elementaryCover (u+(g.1,v)) (a+g.2.2.1) (b+g.2.2.2) := by
        exact (add_comm ..).trans ((congrArg (elementaryCover u a b + ·) hv.symm).trans (elementaryCover_add ..))
      simp only [heq]
      exact (f.property.1 (a+g.2.2.1) (b+g.2.2.2)).comp (contDiff_id.add contDiff_const)
    · intro i
      obtain ⟨p, _, hp⟩ := elementarySchwartzBound_translate_le (F := F) i (size g) ((norm_nonneg _).trans (le_max_left ..))
      exact (hp g f (le_max_left ..) (le_max_right ..)).trans_lt ENNReal.ofReal_lt_top
  let T (z : X × E) : E := ⟨_, hmem z.1 z.2⟩
  refine ⟨⟨T, ?_⟩, fun _ _ _ ↦ rfl⟩
  let : TopologicalSpace.MetrizableSpace E := elementarySchwartz_isFrechet.choose_spec.2.1
  change Continuous T
  rw [CompactlyCoherentSpace.isCoherentWith.continuous_iff]
  intro K hK
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hsize.comp continuous_fst).continuousOn
  let M' := max 0 M
  have hbound : Bornology.IsVonNBounded ℂ (T '' K) := by
    apply elementarySchwartz_withSeminorms.isVonNBounded_iff_seminorm_bddAbove.mpr
    intro i
    obtain ⟨p, hp, h⟩ := elementarySchwartzBound_translate_le (F := F) i M' (le_max_left ..)
    obtain ⟨R, hR⟩ := hK.bddAbove_image (hp.comp continuous_snd).continuousOn
    refine ⟨R, ?_⟩
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hg : size z.1 ≤ M' := (hM (mem_image_of_mem _ hz)).trans (le_max_right ..)
    have hb := h z.1 z.2 ((le_max_left ..).trans hg) ((le_max_right ..).trans hg)
    exact (ENNReal.toReal_le_of_le_ofReal (apply_nonneg p _) hb).trans (hR (mem_image_of_mem _ hz))
  -- On the compact closure of these translates, pointwise convergence detects the topology.
  let S := closure (T '' K)
  have hS : IsCompact S := elementarySchwartz_isCompact_of_isClosed_isVonNBounded isClosed_closure hbound.closure
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let ev (f : S) : X → ℂ := f.val.val
  have hEval : Continuous ev := continuous_pi fun x ↦ elementarySchwartz_continuousEval.comp
    (continuous_subtype_val.prodMk (continuous_const (y := x)))
  have he := hEval.isClosedEmbedding (show Function.Injective ev from fun _ _ h ↦ Subtype.ext (Subtype.ext h))
  let lift (z : K) : S := ⟨T z.val, subset_closure (mem_image_of_mem _ z.property)⟩
  have hc : Continuous lift := he.isEmbedding.continuous_iff.mpr (continuous_pi fun x ↦
    elementarySchwartz_continuousEval.comp ((continuous_snd.comp continuous_subtype_val).prodMk
      ((continuous_fst.comp continuous_subtype_val).add continuous_const)))
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hc)

/-- A stage can be enlarged to contain any prescribed translating element. -/
private theorem exists_bruhatStructuralPair_le_mem (a : BruhatStructuralPair G) (g : G) :
    ∃ b : BruhatStructuralPair G, a ≤ b ∧ g ∈ b.val.1 := by
  let I := OpenCompactlyGeneratedSubgroups G
  have hGroups := openCompactlyGeneratedSubgroups_colimit (G := G)
  let : IsDirectedOrder I := hGroups.1
  obtain ⟨J, hgJ⟩ := hGroups.2.1 g
  let aGroup : I := ⟨a.val.1, a.property.1, a.property.2.1⟩
  obtain ⟨H, haH, hJH⟩ := exists_ge_ge aGroup J
  let b : BruhatStructuralPair G := ⟨(H.val, a.val.2), H.property.1, H.property.2,
    a.property.2.2.1, a.property.2.2.2.trans haH⟩
  exact ⟨b, ⟨haH, le_rfl⟩, hJH hgJ⟩

/-- Paper: Proposition D.1.9.2, p. 781. A left translate of a Schwartz–Bruhat
function is again Schwartz–Bruhat. -/
theorem schwartzBruhat_translate_mem (g : G) (f : SchwartzBruhat G) :
    (fun x ↦ f (g⁻¹ * x)) ∈ schwartzBruhatSubmodule G := by
  classical
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff (fun x ↦ f x)).mp f.property
  obtain ⟨b, hab, hg⟩ := exists_bruhatStructuralPair_le_mem a g
  obtain ⟨e'⟩ := b.elementary
  obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition hab e e'
  obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly
    (m := e'.realDim) (n := e'.torusDim) (r := e'.latticeRank) (F := e'.finiteFactor)
  let h : b.val.1 := ⟨g, hg⟩
  let q (y : b.val.1) := (e'.equiv (QuotientGroup.mk y : b.quotient)).toAdd
  apply (mem_schwartzBruhatSubmodule_iff _).mpr
  refine ⟨b, e', T (q h⁻¹, j s), funext fun x ↦ ?_⟩
  rw [← congrFun hs (g⁻¹ * x), ← congrFun (hj s) (g⁻¹ * x)]
  have hmem := b.val.1.mul_mem_cancel_left (x := g⁻¹) (y := x) (b.val.1.inv_mem hg)
  by_cases hx : x ∈ b.val.1
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_left hx, dite_eq_left (hmem.mpr hx), hT]
    apply congrArg (fun y ↦ j s y)
    change q h⁻¹ + q ⟨x, hx⟩ = q (h⁻¹ * ⟨x, hx⟩)
    unfold q
    rw [QuotientGroup.mk_mul, map_mul]
    rfl
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_right hx, dite_eq_right (hmem.not.mpr hx)]

/-- Paper: Proposition D.1.9.2, p. 781. The left translation by g evaluates
the original function at g⁻¹x. -/
def schwartzBruhatTranslate (g : G) (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨fun x ↦ f (g⁻¹ * x), schwartzBruhat_translate_mem g f⟩

/-- Paper: Proposition D.1.9.2, p. 781. Translating a test function by g and
evaluating at gx recovers its original value at x.
Deviation: Sanity check on the direction of left translation. -/
theorem schwartzBruhatTranslate_apply_mul (g x : G) (f : SchwartzBruhat G) :
    schwartzBruhatTranslate g f (g * x) = f x := by
  change f.val (g⁻¹ * (g * x)) = f.val x
  rw [inv_mul_cancel_left]

omit hTop hT2 hLC in
/-- The inclusion of a structural stage is continuous for the generating seminorms. -/
private theorem continuous_schwartzBruhatStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Continuous (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
      schwartzBruhatStageInclusion a e) :=
  (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ fun p ↦ p.property a e

/-- The quotient action gives translation by elements of the stage's own open subgroup. -/
private theorem continuous_schwartzBruhatTranslate_on_subgroup (b : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation b.quotient) :
    Continuous (fun p : b.val.1 × SchwartzBruhatStage e ↦
      schwartzBruhatTranslate p.1.val (schwartzBruhatStageInclusion b e p.2)) := by
  classical
  obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly
    (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  let q (h : b.val.1) := (e.equiv (QuotientGroup.mk h : b.quotient)).toAdd
  have hq : Continuous q := continuous_toAdd.comp
    (e.equiv.continuous.comp QuotientGroup.continuous_mk)
  have hCont : Continuous (fun p : b.val.1 × SchwartzBruhatStage e ↦
      (show SchwartzBruhat G from schwartzBruhatStageInclusion b e (T (q p.1⁻¹, p.2)))) :=
    (continuous_schwartzBruhatStageInclusion b e).comp
      (T.continuous.comp ((hq.comp continuous_fst.inv).prodMk continuous_snd))
  refine hCont.congr fun ⟨h, s⟩ ↦ ?_
  refine Subtype.ext (funext fun x ↦ ?_)
  change schwartzBruhatStageRealization b e (T (q h⁻¹, s)) x =
    schwartzBruhatStageRealization b e s ((h : G)⁻¹ * x)
  have hmem := b.val.1.mul_mem_cancel_left (x := (h : G)⁻¹) (y := x)
    (b.val.1.inv_mem h.property)
  by_cases hx : x ∈ b.val.1
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_left hx, dite_eq_left (hmem.mpr hx), hT]
    apply congrArg (fun y ↦ s y)
    change q h⁻¹ + q ⟨x, hx⟩ = q (h⁻¹ * ⟨x, hx⟩)
    unfold q
    rw [QuotientGroup.mk_mul, map_mul]
    rfl
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_right hx, dite_eq_right (hmem.not.mpr hx)]

/-- Translation is jointly continuous when the function varies in a fixed structural stage.
Locally the translating element and the function are handled in one larger stage. -/
private theorem continuous_schwartzBruhatTranslate_stage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    Continuous (fun p : G × SchwartzBruhatStage e ↦
      schwartzBruhatTranslate p.1 (schwartzBruhatStageInclusion a e p.2)) := by
  rw [continuous_iff_continuousAt]
  intro ⟨g, f⟩
  obtain ⟨b, hab, hgb⟩ := exists_bruhatStructuralPair_le_mem a g
  obtain ⟨e'⟩ := b.elementary
  obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (a := a) (b := b) hab e e'
  have hOpen : IsOpenEmbedding (Prod.map (Subtype.val : b.val.1 → G)
      (id : SchwartzBruhatStage e → SchwartzBruhatStage e)) :=
    b.property.1.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
  apply (hOpen.continuousAt_iff (x := (⟨g, hgb⟩, f))).mp
  have hCont : Continuous (fun p : b.val.1 × SchwartzBruhatStage e ↦
      schwartzBruhatTranslate p.1.val (schwartzBruhatStageInclusion b e' (j p.2))) :=
    (continuous_schwartzBruhatTranslate_on_subgroup b e').comp
      (continuous_fst.prodMk (j.continuous.comp continuous_snd))
  refine (hCont.congr fun p ↦ ?_).continuousAt
  exact congrArg (schwartzBruhatTranslate p.1.val) (Subtype.ext (hj p.2))

open scoped ComplexOrder in
/-- Paper: Proposition D.1.9.2, p. 781. For a second-countable group, left
translation is jointly continuous in the group element and Schwartz–Bruhat function. -/
theorem schwartzBruhatTranslate_continuous [SecondCountableTopology G] :
    Continuous (fun p : G × SchwartzBruhat G ↦ schwartzBruhatTranslate p.1 p.2) := by
  let E := SchwartzBruhat G
  let : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : LocallyConvexSpace ℂ E := .ofBasisZero ℂ E _ _ (LocallyConvexSpace.convex_basis_zero ℝ E)
    (fun _ hs ↦ convex_of_nonneg_surjective_algebraMap ℂ
      (fun _ hz ↦ RCLike.nonneg_iff_exists_ofReal.mp hz) hs.2)
  let : ContinuousSMul ℝ C(G, E) := IsScalarTower.continuousSMul ℂ
  have hOrbit (f : E) : Continuous (fun g ↦ schwartzBruhatTranslate g f) := by
    obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
    have hf : (show E from schwartzBruhatStageInclusion a e s) = f := Subtype.ext hs
    rw [← hf]
    exact (continuous_schwartzBruhatTranslate_stage a e).comp (continuous_id.prodMk continuous_const)
  let A : E →ₗ[ℂ] C(G, E) :=
    { toFun := fun f ↦ ⟨fun g ↦ schwartzBruhatTranslate g f, hOrbit f⟩
      map_add' := fun f s ↦ ContinuousMap.ext fun g ↦ Subtype.ext rfl
      map_smul' := fun c f ↦ ContinuousMap.ext fun g ↦ Subtype.ext rfl }
  -- The linear map into the compact-open space is continuous on each stage.
  -- Its seminorm pullbacks are therefore among the defining seminorms of E.
  have hA : Continuous A := by
    let P : SeminormFamily ℂ E {q : Seminorm ℂ E //
        ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
          Continuous (q ∘ schwartzBruhatStageInclusion a e)} := Subtype.val
    have hP : WithSeminorms P := ⟨rfl⟩
    refine (PolynormableSpace.withSeminorms ℂ C(G, E)).continuous_of_continuous_comp A fun p ↦ ?_
    refine hP.continuous_seminorm ⟨p.val.comp A, ?_⟩
    intro a e
    have hStage : Continuous (fun s : SchwartzBruhatStage e ↦ A (schwartzBruhatStageInclusion a e s)) :=
      ContinuousMap.continuous_of_continuous_uncurry _ <|
        (continuous_schwartzBruhatTranslate_stage a e).comp continuous_swap
    exact p.property.comp hStage
  exact continuous_eval.comp ((hA.comp continuous_snd).prodMk continuous_fst)

/-- Paper: Proposition D.1.9.2, p. 781. Translations by a compact set of group
elements send one common zero-neighborhood into any prescribed zero-neighborhood. -/
theorem schwartzBruhatTranslate_equicontinuous [SecondCountableTopology G]
    (K : Set G) (hK : IsCompact K) {U : Set (SchwartzBruhat G)} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : SchwartzBruhat G),
      ∀ g ∈ K, ∀ f ∈ V, schwartzBruhatTranslate g f ∈ U := by
  have h : ∀ᶠ f in 𝓝 (0 : SchwartzBruhat G), ∀ g ∈ K, schwartzBruhatTranslate g f ∈ U := by
    apply hK.eventually_forall_of_forall_eventually
    intro g _
    have hc := (schwartzBruhatTranslate_continuous (G := G)).comp continuous_swap
    exact (hc.continuousAt (x := (0, g))).preimage_mem_nhds hU
  exact ⟨_, h, fun g hg f hf ↦ hf g hg⟩

-- TODO(paper-gap): D.1.9.3 omits additivity of the action. The proof uses
-- distributivity over sums, and the statement fails for actions by arbitrary homeomorphisms.

omit hTop hT2 hLC in
include hTopH in
/-- Paper: Lemma D.1.9.3, p. 781. A complex linear action on the completion
is jointly continuous if each operator is continuous and the invariant original
space has a jointly continuous action.
Deviation: The linear action needed for the addition identities in the proof is explicit. -/
theorem continuous_action_completion [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E]
    (ρ : H →* (UniformSpace.Completion E ≃ₗ[ℂ] UniformSpace.Completion E))
    (hEach : ∀ h : H, Continuous (ρ h))
    (τ : H →* (E ≃ₗ[ℂ] E))
    (hτ : ∀ h (x : E), ρ h (x : UniformSpace.Completion E) = (τ h x : UniformSpace.Completion E))
    (hJoint : Continuous (fun p : H × E ↦ τ p.1 p.2)) :
    Continuous (fun p : H × UniformSpace.Completion E ↦ ρ p.1 p.2) := by
  let C := UniformSpace.Completion E
  let i : E →+ C := UniformSpace.Completion.toCompl
  have hd : IsDenseInducing i := UniformSpace.Completion.isDenseInducing_coe
  -- A closed target neighborhood lets us pass each estimate to the closure in C.
  have hZero (h : H) {U : Set C} (hU : U ∈ 𝓝 0) :
      ∃ N ∈ 𝓝 h, ∃ V ∈ 𝓝 (0 : C), ∀ k ∈ N, MapsTo (ρ k) V U := by
    obtain ⟨W, ⟨hW, hcW⟩, hWU⟩ := (closed_nhds_basis (0 : C)).mem_iff.mp hU
    have hc := hd.continuous.comp hJoint
    have hpre := (hc.continuousAt (x := (h, 0))).preimage_mem_nhds
      (show W ∈ 𝓝 (i (τ h 0)) by simpa using hW)
    obtain ⟨N, hN, B, hB, hNB⟩ := mem_nhds_prod_iff.mp hpre
    refine ⟨N, hN, closure (i '' B), ?_, fun k hk ↦ ?_⟩
    · simpa only [map_zero] using hd.closure_image_mem_nhds hB
    · apply Subset.trans _ (preimage_mono hWU)
      apply closure_minimal _ (hcW.preimage (hEach k))
      rintro _ ⟨y, hy, rfl⟩
      change ρ k (y : C) ∈ W
      rw [hτ]
      exact hNB (a := (k, y)) ⟨hk, hy⟩
  rw [continuous_iff_continuousAt]
  intro ⟨h, x⟩ U hU
  have hsum : Continuous (fun p : C × C × C ↦ p.1 + p.2.1 - p.2.2 + ρ h x) :=
    ((continuous_fst.add (continuous_fst.comp continuous_snd)).sub
      (continuous_snd.comp continuous_snd)).add continuous_const
  have hu : (fun p : C × C × C ↦ p.1 + p.2.1 - p.2.2 + ρ h x) ⁻¹' U ∈
      𝓝 ((0 : C), (0 : C), (0 : C)) := by
    apply hsum.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨A, hA, BC, hBC, hrect⟩ := mem_nhds_prod_iff.mp hu
  obtain ⟨B, hB, D, hD, hrect'⟩ := mem_nhds_prod_iff.mp hBC
  obtain ⟨N, hN, V, hV, hNV⟩ := hZero h (inter_mem hA hD)
  -- Approximate x by an original vector c, retaining a neighborhood around x - c.
  have hnear : {z : C | x - z ∈ interior V} ∈ 𝓝 x := by
    apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
    simpa using interior_mem_nhds.mpr hV
  obtain ⟨_, hz, c, rfl⟩ := mem_closure_iff_nhds.mp (hd.dense x) _ hnear
  have hc : Continuous (fun k ↦ ρ k (i c)) := by
    exact (hd.continuous.comp (hJoint.comp (continuous_id.prodMk continuous_const))).congr
      (fun k ↦ (hτ k c).symm)
  have horbit : ∀ᶠ k in 𝓝 h, ρ k (i c) - ρ h (i c) ∈ B :=
    (hc.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hB)
  have hrem : ∀ᶠ z in 𝓝 x, z - i c ∈ V :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
  change ∀ᶠ p : H × C in 𝓝 (h, x), ρ p.1 p.2 ∈ U
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (inter_mem hN horbit),
    continuous_snd.continuousAt.preimage_mem_nhds hrem] with p hp hp'
  have h₁ := (hNV p.1 hp.1 hp').1
  have h₃ := (hNV h (mem_of_mem_nhds hN) (interior_subset hz)).2
  have h := hrect (a := (ρ p.1 (p.2 - i c), ρ p.1 (i c) - ρ h (i c), ρ h (x - i c)))
    ⟨h₁, hrect' ⟨hp.2, h₃⟩⟩
  simpa only [mem_preimage, map_sub, sub_add_sub_cancel, sub_sub_sub_cancel_right, sub_add_cancel]
    using h

open scoped ComplexOrder in
omit hTop hT2 hLC in
include hTopH in
/-- Paper: Lemma D.1.9.4, p. 782. The diagonal action induced by continuous
linear actions on both factors is jointly continuous on their projective tensor product. -/
theorem continuous_action_projectiveTensor
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [T2Space E] [T2Space F] [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (ρ : H →* (E ≃ₗ[ℂ] E)) (τ : H →* (F ≃ₗ[ℂ] F))
    (hρ : Continuous (fun p : H × E ↦ ρ p.1 p.2))
    (hτ : Continuous (fun p : H × F ↦ τ p.1 p.2)) :
    Continuous (fun p : H × ProjectiveTensor E F ↦
      (show ProjectiveTensor E F from
        TensorProduct.map (ρ p.1).toLinearMap (τ p.1).toLinearMap p.2)) := by
  let P := ProjectiveTensor E F
  let A (h : H) : P →ₗ[ℂ] P := TensorProduct.map (ρ h).toLinearMap (τ h).toLinearMap
  let tmul : E × F → P := fun z ↦ z.1 ⊗ₜ[ℂ] z.2
  have htZero : tmul (0, 0) = 0 := TensorProduct.zero_tmul E (0 : F)
  have ht : Continuous tmul :=
    (continuous_projectiveTensor_iff (G := P) (LinearMap.id : P →ₗ[ℂ] P)).mp continuous_id
  have horbit (z : P) : Continuous (fun h ↦ A h z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      exact ht.comp ((hρ.comp (continuous_id.prodMk continuous_const)).prodMk
        (hτ.comp (continuous_id.prodMk continuous_const)))
    | add x y hx hy => exact (hx.add hy).congr fun h ↦ ((A h).map_add x y).symm
  have hzero (h : H) : Tendsto (fun p : H × P ↦ A p.1 p.2) (𝓝 (h, 0)) (𝓝 0) := by
    apply (PolynormableSpace.hasBasis_zero_ball ℂ P).tendsto_right_iff.mpr
    intro q hq
    have hball := q.ball_mem_nhds hq one_pos
    have ht0 := ht.continuousAt (x := ((0 : E), (0 : F)))
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (ht0.preimage_mem_nhds
      (by simpa only [htZero] using hball))
    obtain ⟨N, hN, B, hB, hNB⟩ := mem_nhds_prod_iff.mp ((hρ.continuousAt (x := (h, 0))).preimage_mem_nhds
      (show U ∈ 𝓝 (ρ h 0) by simpa using hU))
    obtain ⟨M, hM, D, hD, hMD⟩ := mem_nhds_prod_iff.mp ((hτ.continuousAt (x := (h, 0))).preimage_mem_nhds
      (show V ∈ 𝓝 (τ h 0) by simpa using hV))
    let W := absConvexHull ℂ (image2 (TensorProduct.tmul ℂ) B D)
    have hW : W ∈ 𝓝 (0 : P) :=
      (projectiveTensor_zero_basis (𝓝 (0 : E)).basis_sets (𝓝 (0 : F)).basis_sets).mem_of_mem
        (i := (B, D)) ⟨hB, hD⟩
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (inter_mem hN hM),
      continuous_snd.continuousAt.preimage_mem_nhds hW] with p hp hpW
    let s := q.comp (A p.1)
    suffices W ⊆ s.ball 0 1 by
      exact q.mem_ball_zero.mpr (s.mem_ball_zero.mp (this hpW))
    apply absConvexHull_min _ ⟨s.balanced_ball_zero 1,
      convex_RCLike_iff_convex_real.mpr (s.convex_ball 0 1)⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    apply s.mem_ball_zero.mpr
    exact q.mem_ball_zero.mp (hUV (a := (ρ p.1 x, τ p.1 y))
      ⟨hNB (a := (p.1, x)) ⟨hp.1, hx⟩, hMD (a := (p.1, y)) ⟨hp.2, hy⟩⟩)
  rw [continuous_iff_continuousAt]
  intro ⟨h, z⟩
  have hd : Continuous (fun p : H × P ↦ (p.1, p.2 - z)) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hlim := (hzero h).comp (hd.tendsto' (h, z) (h, 0) (by simp))
  have hc := hlim.add (((horbit z).comp continuous_fst).tendsto (h, z))
  change Tendsto (fun p : H × P ↦ A p.1 p.2) (𝓝 (h, z)) (𝓝 (A h z))
  simpa only [Function.comp_def, map_sub, sub_add_cancel, zero_add] using hc

end Translations

end RiemannMasullo
