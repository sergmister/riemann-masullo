module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Pi

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Data.Pi.Interval
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1d
import all RiemannMasullo.Ch02_AdelicTheta.Sec1

/-! # Structure Theorem IV: local within global

Masullo, §6.1, pp. 287–295. The finite sets index finite places. The
archimedean places are included in every S-adelic ring.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped CompactlySupported MonoidAlgebra NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Places" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "L(" w ")" => (HeightOneSpectrum.adicCompletion (R := 𝓞 F) F w)
local notation "ℬᵥ(" w ")" => (SchwartzBruhat (Multiplicative (L(w))))
local notation "O(" w ")" => (HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F w)
local notation "U(" w ")" =>
  (Submonoid.units (Subsemiring.toSubmonoid (Subring.toSubsemiring (ValuationSubring.toSubring (O(w))))))

-- TODO(paper-gap): Proposition 6.1.1.1, (6.1.1.1)–(6.1.1.2), multiplies
-- inverses of test-space endomorphisms to obtain transitions between distinct
-- quotients. On the target coinvariants every basis lift acts as the identity,
-- so the differences have no inverse. Already over ℚ, with S = {∞} and
-- S' = {∞, p}, the proposed geometric series does not converge in the target
-- quotient on a nonzero transition class. The global series has the same defect.

section Ranges

private theorem mem_ker_adeleProjection_units_iff (T : Finset (HeightOneSpectrum (𝓞 F)))
    (g : IdeleGroup (𝓞 F) F) :
    g ∈ (Units.map (adeleProjection F T).toMonoidHom).ker ↔
      g.val.1 = 1 ∧ ∀ w : T, g.val.2 w.val = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp only [Units.coe_map, Units.val_one]
  rw [Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w ↦ congrFun h2 w⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext fun w ↦ h2 w⟩

variable (F S) in
/-- Paper: (6.1.2.2), p. 288.
The complementary integral ideles are the ideles integral and invertible outside S
whose S-adelic projection is the identity.
Deviation: In (6.1.2.2) the ambient outside multiplicative factors form a restricted
product. The full product of integer units embeds in the ideles. -/
def outsideIntegralIdeleUnits : Subgroup (IdeleGroup (𝓞 F) F) :=
  (integralIdeleInsertion F S).range ⊓ (Units.map (adeleProjection F S).toMonoidHom).ker

/-- Paper: (6.1.2.2), p. 288.
An idele belongs to the complementary group exactly when its archimedean and S coordinates
are one and its other coordinates are local integer units. -/
theorem mem_outsideIntegralIdeleUnits_iff (g : IdeleGroup (𝓞 F) F) :
    g ∈ outsideIntegralIdeleUnits F S ↔
      g.val.1 = 1 ∧ (∀ w ∈ S, g.val.2 w = 1) ∧
        ∀ w ∉ S, g.val.2 w ∈ O(w) ∧ (g⁻¹).val.2 w ∈ O(w) := by
  unfold outsideIntegralIdeleUnits
  rw [Subgroup.mem_inf, mem_ker_adeleProjection_units_iff,
    show g ∈ (integralIdeleInsertion F S).range ↔ g ∈ Set.range (integralIdeleInsertion F S) from
      Iff.rfl,
    mem_range_integralIdeleInsertion]
  constructor
  · rintro ⟨h2, h1, h3⟩
    exact ⟨h1, fun w hw ↦ h3 ⟨w, hw⟩, h2⟩
  · rintro ⟨h1, h3, h2⟩
    exact ⟨h2, h1, fun w ↦ h3 w.1 w.2⟩

variable (F S T) in
/-- Paper: (6.1.2.1), p. 288.
Projecting the complementary integral ideles to T inserts the integer units at T minus S.
Deviation: The insertion lands in the T-ideles, as required by Theorem 6.1.2.1(1). -/
def relativeIntegralIdeleUnits : Subgroup (SAdeleRing F T)ˣ :=
  (outsideIntegralIdeleUnits F S).map (Units.map (adeleProjection F T).toMonoidHom)

/-- Paper: (6.1.2.1), p. 288.
The relative group has identity coordinates on the archimedean factor and S, and
arbitrary integer-unit coordinates on T minus S. -/
theorem mem_relativeIntegralIdeleUnits_iff (g : (SAdeleRing F T)ˣ) :
    g ∈ relativeIntegralIdeleUnits F S T ↔
      g.val.1 = 1 ∧ (∀ w : T, w.val ∈ S → g.val.2 w = 1) ∧
        ∀ w : T, w.val ∉ S → g.val.2 w ∈ O(w.val) ∧ (g⁻¹).val.2 w ∈ O(w.val) := by
  classical
  unfold relativeIntegralIdeleUnits
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (mem_outsideIntegralIdeleUnits_iff h).1 hh
    refine ⟨h1, fun w hw ↦ h2 w.val hw, fun w hw ↦ h3 w.val hw⟩
  · rintro ⟨h1, h2, h3⟩
    let e (x : (w : T) → HeightOneSpectrum.adicCompletion F w.val) :
        RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) ↦ HeightOneSpectrum.adicCompletion F w)
          (fun w ↦ HeightOneSpectrum.adicCompletionIntegers F w) Filter.cofinite :=
      RestrictedProduct.mk
        (fun w : HeightOneSpectrum (𝓞 F) ↦ if hw : w ∈ T then x ⟨w, hw⟩ else 1)
        (by
          filter_upwards [T.eventually_cofinite_notMem] with w hw
          simp only [hw, dite_false]
          exact one_mem _)
    have he (x) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∈ T) : e x w = x ⟨w, hw⟩ := by
      exact dif_pos hw
    have he' (x) (w : HeightOneSpectrum (𝓞 F)) (hw : w ∉ T) : e x w = 1 := by
      exact dif_neg hw
    have hmul : ∀ w : T, g.val.2 w * (g⁻¹).val.2 w = 1 := fun w ↦
      congrFun (congrArg Prod.snd g.val_inv) w
    have hmul' : ∀ w : T, (g⁻¹).val.2 w * g.val.2 w = 1 := fun w ↦
      congrFun (congrArg Prod.snd g.inv_val) w
    have hm1 : e g.val.2 * e (g⁻¹).val.2 = 1 := Subtype.ext (funext fun w ↦ by
      by_cases hw : w ∈ T
      · change e _ w * e _ w = 1
        rw [he _ _ hw, he _ _ hw]; exact hmul ⟨w, hw⟩
      · change e _ w * e _ w = 1
        rw [he' _ _ hw, he' _ _ hw]; exact mul_one _)
    have hm2 : e (g⁻¹).val.2 * e g.val.2 = 1 := Subtype.ext (funext fun w ↦ by
      by_cases hw : w ∈ T
      · change e _ w * e _ w = 1
        rw [he _ _ hw, he _ _ hw]; exact hmul' ⟨w, hw⟩
      · change e _ w * e _ w = 1
        rw [he' _ _ hw, he' _ _ hw]; exact mul_one _)
    let h : IdeleGroup (𝓞 F) F :=
      ⟨(1, e g.val.2), (1, e (g⁻¹).val.2), Prod.ext (mul_one 1) hm1, Prod.ext (mul_one 1) hm2⟩
    refine ⟨h, ?_, ?_⟩
    · rw [mem_outsideIntegralIdeleUnits_iff]
      refine ⟨rfl, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hT : w ∈ T
        · exact (he _ _ hT).trans (h2 ⟨w, hT⟩ hw)
        · exact he' _ _ hT
      · by_cases hT : w ∈ T
        · exact ⟨(he _ _ hT).symm ▸ (h3 ⟨w, hT⟩ hw).1, (he _ _ hT).symm ▸ (h3 ⟨w, hT⟩ hw).2⟩
        · exact ⟨(he' _ _ hT).symm ▸ one_mem _, (he' _ _ hT).symm ▸ one_mem _⟩
    · refine Units.ext (Prod.ext h1.symm (funext fun w ↦ ?_))
      exact he _ _ w.2

open scoped RestrictedProduct in
/-- The local integer rings form a compact subset of the finite adeles. -/
private theorem outsideIntegralIdeleUnits_isCompact_integral :
    IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} := by
  let K := fun v : Places ↦ v.adicCompletion F
  let O := fun v : Places ↦ (v.adicCompletionIntegers F : Set (K v))
  have (v : Places) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let j : (∀ v : Places, v.adicCompletionIntegers F) → Πʳ v, [K v, O v]_[Filter.principal Set.univ] :=
    fun x ↦ ⟨fun v ↦ x v, Filter.Eventually.of_forall fun v ↦ (x v).property⟩
  let i := RestrictedProduct.inclusion K O
    (show Filter.cofinite ≤ Filter.principal (Set.univ : Set Places) by simp)
  have hj : Continuous j := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun v ↦ continuous_subtype_val.comp (continuous_apply v))
  have hc := isCompact_range ((RestrictedProduct.continuous_inclusion _).comp hj :
    Continuous (i ∘ j))
  have h : Set.range (i ∘ j) =
      {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
    apply Set.ext
    intro a
    exact ⟨fun ⟨x, hx⟩ v ↦ hx ▸ (x v).property,
      fun ha ↦ ⟨fun v ↦ ⟨a v, ha v⟩, rfl⟩⟩
  rwa [← h]

/-- Paper: (6.1.2.2), p. 288.
The group of integral idelic units outside S is compact in the global ideles. -/
theorem outsideIntegralIdeleUnits_isCompact :
    IsCompact (outsideIntegralIdeleUnits F S : Set (IdeleGroup (𝓞 F) F)) := by
  classical
  let K : Submonoid (AdeleRing (𝓞 F) F) :=
    { carrier := {a | a.1 = 1 ∧ (∀ w ∈ S, a.2 w = 1) ∧ ∀ w, a.2 w ∈ O(w)}
      mul_mem' := fun {a b} ha hb ↦ ⟨by rw [Prod.fst_mul, ha.1, hb.1, one_mul],
        fun w hw ↦ by
          change a.2 w * b.2 w = 1
          rw [ha.2.1 w hw, hb.2.1 w hw, one_mul],
        fun w ↦ by
          change a.2 w * b.2 w ∈ O(w)
          exact mul_mem (ha.2.2 w) (hb.2.2 w)⟩
      one_mem' := ⟨rfl, fun _ _ ↦ rfl, fun w ↦ one_mem (O(w))⟩ }
  have hK : IsCompact (K : Set (AdeleRing (𝓞 F) F)) := by
    have hcl : IsClosed {a : FiniteAdeleRing (𝓞 F) F | ∀ w ∈ S, a w = 1} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun w ↦ isClosed_iInter fun _ ↦
        isClosed_eq (RestrictedProduct.continuous_eval w) continuous_const
    have h1 := (isCompact_singleton (x := (1 : InfiniteAdeleRing F))).prod
      (outsideIntegralIdeleUnits_isCompact_integral.inter_right hcl)
    have he : (K : Set (AdeleRing (𝓞 F) F)) = ({1} : Set (InfiniteAdeleRing F)) ×ˢ
        ({a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} ∩
          {a : FiniteAdeleRing (𝓞 F) F | ∀ w ∈ S, a w = 1}) := by
      ext a
      change (a.1 = 1 ∧ (∀ w ∈ S, a.2 w = 1) ∧ ∀ w, a.2 w ∈ O(w)) ↔
        a.1 = 1 ∧ ((∀ v, a.2 v ∈ O(v)) ∧ ∀ w ∈ S, a.2 w = 1)
      tauto
    exact he ▸ h1
  have hinv (g : IdeleGroup (𝓞 F) F) : (g⁻¹).val * g.val = 1 := Units.inv_mul g
  have heq : (outsideIntegralIdeleUnits F S : Set (IdeleGroup (𝓞 F) F)) = K.units := by
    ext g
    rw [SetLike.mem_coe, mem_outsideIntegralIdeleUnits_iff, SetLike.mem_coe,
      Submonoid.mem_units_iff]
    have h1 := congrArg Prod.fst (hinv g)
    have h2 := fun w ↦ congrFun (congrArg (fun a : AdeleRing (𝓞 F) F ↦ ⇑a.2) (hinv g)) w
    change (g⁻¹).val.1 * g.val.1 = 1 at h1
    change ∀ w, (g⁻¹).val.2 w * g.val.2 w = 1 at h2
    constructor
    · rintro ⟨ha, hS, hO⟩
      refine ⟨⟨ha, hS, fun w ↦ ?_⟩, ⟨?_, fun w hw ↦ ?_, fun w ↦ ?_⟩⟩
      · by_cases hw : w ∈ S
        · rw [hS w hw]; exact one_mem _
        · exact (hO w hw).1
      · rwa [ha, mul_one] at h1
      · have := h2 w
        rwa [hS w hw, mul_one] at this
      · by_cases hw : w ∈ S
        · have := h2 w
          rw [hS w hw, mul_one] at this
          change (g⁻¹).val.2 w ∈ O(w)
          rw [this]; exact one_mem _
        · exact (hO w hw).2
    · rintro ⟨⟨ha, hS, hO⟩, ⟨_, _, hO'⟩⟩
      exact ⟨ha, hS, fun w _ ↦ ⟨hO w, hO' w⟩⟩
  rw [heq]
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous
      (f := fun a : FiniteAdeleRing (𝓞 F) F ↦ (⇑a : ∀ v : Places, v.adicCompletion F))
      (fun _ _ h ↦ Subtype.ext h) (continuous_pi fun v ↦ RestrictedProduct.continuous_eval v)
  have : T2Space (InfiniteAdeleRing F) :=
    inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  have : T2Space (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  exact Submonoid.units_isCompact hK

/-- Paper: (6.1.2.1), p. 288.
The group of integer units inserted at the additional finite places is compact in the T-ideles. -/
theorem relativeIntegralIdeleUnits_isCompact :
    IsCompact (relativeIntegralIdeleUnits F S T : Set (SAdeleRing F T)ˣ) := by
  classical
  let H (v : T) : Set (L(v.val))ˣ := if v.val ∈ S then {1} else U(v.val)
  have hc (v : T) : IsCompact (H v) := by
    by_cases hv : v.val ∈ S
    · simpa only [H, ite_eq_left hv] using (isCompact_singleton (x := (1 : (L(v.val))ˣ)))
    · have hO : IsCompact (O(v.val) : Set (L(v.val))) :=
        isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val)
      simpa only [H, ite_eq_right hv] using Submonoid.units_isCompact hO
  have memH (v : T) (u : (L(v.val))ˣ) : u ∈ H v ↔
      (v.val ∈ S → u.val = 1) ∧
        (v.val ∉ S → u.val ∈ O(v.val) ∧ (u⁻¹).val ∈ O(v.val)) := by
    by_cases hv : v.val ∈ S
    · simp only [H, ite_eq_left hv, Set.mem_singleton_iff]
      exact ⟨fun h ↦ ⟨fun _ ↦ congrArg Units.val h, fun hn ↦ (hn hv).elim⟩, fun h ↦ Units.ext (h.1 hv)⟩
    · simp only [H, ite_eq_right hv]
      exact ⟨fun h ↦ ⟨fun hs ↦ (hv hs).elim, fun _ ↦ h⟩, fun h ↦ h.2 hv⟩
  let p := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((v : T) → L(v.val))
  let q := ContinuousMulEquiv.piUnits (M := fun v : T ↦ L(v.val))
  let e := p.toHomeomorph.trans ((Homeomorph.refl _).prodCongr q.toHomeomorph)
  have he : (relativeIntegralIdeleUnits F S T : Set (SAdeleRing F T)ˣ) =
      e ⁻¹' (({1} : Set (InfiniteAdeleRing F)ˣ) ×ˢ Set.univ.pi H) := by
    ext g
    refine (mem_relativeIntegralIdeleUnits_iff (F := F) (S := S) (T := T) g).trans ?_
    change _ ↔ (p g).1 ∈ ({1} : Set (InfiniteAdeleRing F)ˣ) ∧ q (p g).2 ∈ Set.univ.pi H
    rw [Set.mem_singleton_iff, Units.ext_iff, Set.mem_univ_pi]
    refine and_congr_right fun _ ↦ ?_
    simp_rw [memH]
    exact ⟨fun ⟨hs, hd⟩ v ↦ ⟨hs v, hd v⟩, fun h ↦ ⟨fun v ↦ (h v).1, fun v ↦ (h v).2⟩⟩
  exact (congrArg IsCompact he).mpr (e.isCompact_preimage.mpr
    (isCompact_singleton.prod (isCompact_univ_pi hc)))

-- TODO(paper-gap): The proof of Theorem 6.1.2.1 applies its invariant-space
-- tensor identification to the full test space and has mismatched indices
-- in (6.1.2.21). The argument on pp. 294–295 assumes convergent Cauchy nets
-- have bounded tails in the strict LF topology. Equation (5.1.1.3) defines the
-- two theta spaces as quotients by the theta kernels. Remark 5.2.3.4 concerns
-- the separate comparison with closures of principal translation differences.

/-- Paper: Theorem 6.1.2.1(1), p. 288.
When the S-integers have trivial Picard group, the range of the transition is the fixed
subspace for the relative integral units in the T-local theta quotient of (5.1.1.3). -/
theorem sLocalThetaTransition_range_eq_invariants (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    Set.range (sLocalThetaTransition (F := F) hST.le) =
      {x : Θₛ(T) | ∀ g : relativeIntegralIdeleUnits F S T,
        ρ (QuotientGroup.mk g.val) x = x} := by sorry

private theorem sLocalThetaToGlobal_range_eq_invariants_intertwine
    (g : IdeleGroup (𝓞 F) F) (hg : g ∈ (integralIdeleInsertion F T).range) (y : Θₛ(T)) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    let ρT := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    sLocalThetaToGlobal F T
        (ρT (QuotientGroup.mk (Units.map (adeleProjection F T).toMonoidHom g)) y) =
      ρ (QuotientGroup.mk g) (sLocalThetaToGlobal F T y) := by
  obtain ⟨u, rfl⟩ := hg
  refine Submodule.Quotient.induction_on (LinearMap.ker (sLocalAdelicTheta F T)) y ?_
  intro f
  let g := integralIdeleInsertion F T u
  have hT := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2
    (Units.map (adeleProjection F T).toMonoidHom g) f
  have hF := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 g
    (sAdeleSchwartzToGlobal F T f)
  have h₁ := congrArg (sLocalThetaToGlobal F T) hT
  have h₂ := sLocalThetaToGlobal_equivariant (F := F) (S := T) u f
  have h₃ := congrArg ((existsUnique_globalThetaAction (F := F)).exists.choose (QuotientGroup.mk g))
    (sLocalThetaToGlobal_mk (F := F) (S := T) f)
  with_reducible exact h₁.trans (h₂.trans (h₃.trans hF).symm)

private theorem sLocalThetaToGlobal_range_eq_invariants_one {G V : Type*} [Group G]
    {N : Subgroup G} [N.Normal] [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (ρ : G ⧸ N →* (V →L[ℂ] V)) {g : G} (hg : g = 1) (v : V) :
    ρ (QuotientGroup.mk g) v = v := by
  subst g
  rw [QuotientGroup.mk_one, map_one]
  rfl

private theorem sLocalThetaToGlobal_range_eq_invariants_comp_apply
    (hST : S ⊆ T) (y : Θₛ(S)) :
    sLocalThetaToGlobal F T (sLocalThetaTransition hST y) = sLocalThetaToGlobal F S y :=
  LinearMap.congr_fun (sLocalThetaToGlobal_comp (F := F) hST) y

private theorem sLocalThetaToGlobal_range_eq_invariants_stage (x : Θ𝔽) :
    ∃ (T : Finset Places), S ⊆ T ∧ ∃ z : Θₛ(T), sLocalThetaToGlobal F T z = x := by
  have he := sLocalThetaToGlobal_exhaustive (F := F) x
  rcases he with ⟨U, y, hy⟩
  classical
  have hUT : U ⊆ S ∪ U := Finset.subset_union_right
  have hz := sLocalThetaToGlobal_range_eq_invariants_comp_apply (F := F) hUT y
  with_reducible exact ⟨S ∪ U, Finset.subset_union_left, sLocalThetaTransition (F := F) hUT y,
    hz.trans hy⟩

/-- Paper: Theorem 6.1.2.1(2), p. 288.
When the S-integers have trivial Picard group, the range of the global insertion is the fixed
subspace for the complementary integral units in the global theta quotient of (5.1.1.3). -/
theorem sLocalThetaToGlobal_range_eq_invariants
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F))) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    Set.range (sLocalThetaToGlobal F S) =
      {x : Θ𝔽 | ∀ g : outsideIntegralIdeleUnits F S, ρ (QuotientGroup.mk g.val) x = x} := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩ g
    -- On the S-stage the projection of every complementary unit is one.
    have h := sLocalThetaToGlobal_range_eq_invariants_intertwine (F := F) (T := S)
      g.val g.property.1 y
    have hp : Units.map (adeleProjection F S).toMonoidHom g.val = 1 := g.property.2
    have hid := sLocalThetaToGlobal_range_eq_invariants_one
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose hp y
    have h₂ := congrArg (sLocalThetaToGlobal F S) hid
    with_reducible exact h.symm.trans h₂
  · intro hx
    -- Take a finite stage containing S and representing the fixed global class.
    have he := sLocalThetaToGlobal_range_eq_invariants_stage (F := F) (S := S) x
    rcases he with ⟨T, hST, z, hz⟩
    by_cases heq : T = S
    · have hy : x ∈ Set.range (sLocalThetaToGlobal F T) := ⟨z, hz⟩
      exact (congrArg (fun V ↦ x ∈ Set.range (sLocalThetaToGlobal F V)) heq).mp hy
    · have hlt : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hST, Ne.symm heq⟩
      -- Lift each relative unit to a complementary unit and use injectivity at T.
      have hfixed : ∀ k : relativeIntegralIdeleUnits F S T,
          (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
            (QuotientGroup.mk k.val) z = z := by
        rintro ⟨k, g, hg, rfl⟩
        apply (sLocalThetaToGlobal_isEmbedding (F := F) (S := T)).injective
        have hgT : g ∈ (integralIdeleInsertion F T).range :=
          (integralIdeleInsertion_exhaustive F).1 hST hg.1
        have hi := sLocalThetaToGlobal_range_eq_invariants_intertwine (F := F) (T := T) g hgT z
        have ha := congrArg
          ((existsUnique_globalThetaAction (F := F)).exists.choose (QuotientGroup.mk g)) hz
        have hgx := hx ⟨g, hg⟩
        with_reducible exact hi.trans (ha.trans (hgx.trans hz.symm))
      have hr := Set.ext_iff.mp (sLocalThetaTransition_range_eq_invariants (F := F) hlt _hPic) z
      have hmem := hr.mpr (Set.mem_ofPred.mpr hfixed)
      rcases hmem with ⟨w, hw⟩
      have h := sLocalThetaToGlobal_range_eq_invariants_comp_apply (F := F) hlt.le w
      have h' := congrArg (sLocalThetaToGlobal F T) hw
      with_reducible exact Set.mem_range.mpr ⟨w, h.symm.trans (h'.trans hz)⟩

end Ranges

section UnitRepresentation

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "translate" => fun (g : Rˣ) ↦
  ((LinearMap.funLeft ℂ ℂ (fun x : Multiplicative R ↦
    Multiplicative.ofAdd ((g⁻¹ : Rˣ).val * x.toAdd))).comp
    (schwartzBruhatSubmodule (Multiplicative R)).subtype).codRestrict
      (schwartzBruhatSubmodule (Multiplicative R)) (schwartzBruhat_unitTranslate_mem g)

/-- Paper: Remark 6.1.2.3, p. 289.
The identity unit acts by the identity on the additive Schwartz–Bruhat space. -/
theorem schwartzBruhatUnitRepresentation_map_one :
    translate (1 : Rˣ) = (1 : Module.End ℂ ℬ(R)) := by
  refine LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ ?_)
  simp
  rfl

/-- Paper: Remark 6.1.2.3, p. 289.
Pullback by the inverse of a product agrees with the composition of the two translations. -/
theorem schwartzBruhatUnitRepresentation_map_mul (g h : Rˣ) :
    translate (g * h) = (translate g : Module.End ℂ ℬ(R)) * translate h := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change f.val (Multiplicative.ofAdd (((g * h)⁻¹ : Rˣ).val * x.toAdd)) =
    f.val (Multiplicative.ofAdd ((h⁻¹ : Rˣ).val * ((g⁻¹ : Rˣ).val * x.toAdd)))
  rw [mul_inv_rev, Units.val_mul, mul_assoc]

/-- Paper: Remark 6.1.2.3, p. 289.
The inverse-multiplication pullback action on additive Schwartz–Bruhat functions,
bundled as a complex linear representation of the unit group. -/
def schwartzBruhatUnitRepresentation : Representation ℂ Rˣ ℬ(R) where
  toFun := translate
  map_one' := schwartzBruhatUnitRepresentation_map_one
  map_mul' := schwartzBruhatUnitRepresentation_map_mul

/-- Paper: Remark 6.1.2.3, p. 289.
The bundled representation acts by the existing left-translation operator. -/
theorem schwartzBruhatUnitRepresentation_apply (g : Rˣ) (f : ℬ(R)) :
    schwartzBruhatUnitRepresentation (R := R) g f = schwartzBruhatUnitTranslate g f := by
  rfl

end UnitRepresentation

local notation "ρ(" w ")" =>
  (schwartzBruhatUnitRepresentation (R := L(w))).comp
    (Subgroup.subtype (U(w)))

section Laurent

open scoped ENNReal in
/-- Point evaluation is continuous in the Schwartz–Bruhat topology since its
norm is bounded on each stage by the zeroth Schwartz seminorm. -/
private theorem schwartzBruhat_eval_continuous {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ℝ≥0∞).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f z‖₊ : ℝ≥0∞)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

private theorem unitInvariants_isClosed {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (H : Subgroup Rˣ) :
    IsClosed (SetLike.coe (Representation.invariants
      ((schwartzBruhatUnitRepresentation (R := R)).comp H.subtype)) : Set ℬ(R)) := by
  have : (SetLike.coe (Representation.invariants
      ((schwartzBruhatUnitRepresentation (R := R)).comp H.subtype)) : Set ℬ(R)) =
      ⋂ g : H, ⋂ x : R, {f | f (Multiplicative.ofAdd (((g⁻¹ : H) : Rˣ).val * x)) =
        f (Multiplicative.ofAdd x)} := by
    ext f
    simp only [SetLike.mem_coe, Representation.mem_invariants, Set.mem_iInter, Set.mem_setOf_eq]
    refine forall_congr' fun g ↦ ?_
    constructor
    · intro h x
      exact congrArg (fun φ : ℬ(R) ↦ φ.val (Multiplicative.ofAdd x)) h
    · intro h
      exact Subtype.ext (funext fun x ↦ h x.toAdd)
  rw [this]
  exact isClosed_iInter fun g ↦ isClosed_iInter fun x ↦
    isClosed_eq (schwartzBruhat_eval_continuous (Multiplicative.ofAdd _))
      (schwartzBruhat_eval_continuous (Multiplicative.ofAdd _))

open Classical in
/-- Paper: Lemma 6.1.2.2(1), p. 288.
The monomial of exponent n corresponds to the indicator of the integral ball
scaled by the n-th power of the uniformizer. -/
def finitePlaceBallIndicator (w : Places) (π : (L(w))ˣ) (n : ℤ)
    (x : L(w)) : ℂ :=
  (O(w) : Set L(w)).indicator (fun _ ↦ (1 : ℂ)) ((π ^ (-n)).val * x)

/-- Paper: Lemma 6.1.2.2(1), p. 288.
The translated ball contains the m-th uniformizer power exactly when m is at least its
defining exponent n. -/
theorem finitePlaceBallIndicator_at_power (w : Places) (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val)
    (m n : ℤ) :
    finitePlaceBallIndicator w π n (π ^ m).val = (if n ≤ m then 1 else 0) := by
  have hv : Valued.v (π.val) = (WithZero.exp (-1 : ℤ)) := _hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (w.valuedAdicCompletion_surjective F)))
  have h1 : (π ^ (-n)).val * (π ^ m).val = ((π ^ (m - n)).val) := by
    rw [← Units.val_mul, ← zpow_add]; congr 2; ring
  have h2 : Valued.v ((π ^ (m - n)).val) = WithZero.exp (-(m - n)) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, ← WithZero.exp_zsmul]; simp
  unfold finitePlaceBallIndicator
  rw [h1]
  by_cases h : n ≤ m
  · rw [if_pos h, Set.indicator_of_mem]
    show _ ∈ O(w)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · rw [if_neg h, Set.indicator_of_notMem]
    show _ ∉ O(w)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2]
    rw [not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega


/-- Paper: Lemma 6.1.2.2(1)(1), p. 288.
The integer-unit invariants form a free Laurent module on the integer-ball indicator.
Deviation: A complex linear equivalence spells out the Laurent action by the generator
and the image of the free generator, without installing an extra module instance. -/
theorem finitePlaceSchwartz_invariants_laurent_free (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : LaurentPolynomial ℂ ≃ₗ[ℂ] (Representation.invariants (ρ(w))),
      (∀ x, (e 1).val (Multiplicative.ofAdd x) = finitePlaceBallIndicator w π 0 x) ∧
      ∀ P, (e (LaurentPolynomial.T 1 * P)).val =
        schwartzBruhatUnitTranslate π (e P).val := by sorry

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
The integer-unit invariants are closed in the local Schwartz–Bruhat space. -/
theorem finitePlaceSchwartz_invariants_isClosed (w : Places) :
    IsClosed (SetLike.coe (Representation.invariants (V := ℬᵥ(w)) (ρ(w))) : Set ℬᵥ(w)) :=
  unitInvariants_isClosed _

/-- Paper: Lemma 6.1.2.2(1)(2), p. 288.
With the finest locally convex topology on Laurent polynomials, the monomial-to-ball
correspondence is a linear homeomorphism onto the unit invariants. -/
theorem finitePlaceSchwartz_invariants_laurent_equiv (w : Places)
    (π : (L(w))ˣ)
    (_hπ : Valuation.IsUniformizer
      (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    ∃ e : FinestLocallyConvex (LaurentPolynomial ℂ) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ n x, (e (LaurentPolynomial.T n)).val (Multiplicative.ofAdd x) =
        finitePlaceBallIndicator w π n x := by sorry

end Laurent

section RelativeLaurent

-- TODO(paper-gap): Lemma 6.1.2.2(2), (6.1.2.5), specifies the projective
-- topology, but §2.1.4.2 uses the inductive topology on this algebraic tensor.
-- For ℚ with one new prime the invariant space is a locally convex direct sum
-- of copies of the real Schwartz space. The canonical tensor pairing into
-- this sum is separately continuous and is not jointly continuous.
-- TODO(paper-gap): After (6.1.2.9) the kernel is the image of the outside unit
-- group itself. Its intersection with the principal ideles is trivial by the
-- archimedean coordinate. The extra quotient by the S-units is unjustified.
-- TODO(paper-gap): The restriction used on p. 291 need not be compactly
-- supported on the multiplicative group, as the restriction of 1_{ℤₚ} shows.

section LaurentProof

/- The forward map adjoins a compact open ball at each new place. For the inverse,
restrict a test function to the slices at tuples of uniformizer powers. On any
one elementary stage these slices vanish below a lower bound and stabilize in
each coordinate above an upper bound. Thus on that stage it suffices to invert
the incidence matrix of a finite box of exponents. The resulting continuous
maps agree because the samples determine a Laurent tensor uniquely. -/

open Filter Topology
open scoped ENNReal TensorProduct

private theorem laurent_compactGen_prod {A B : Type*} [CommGroup A] [TopologicalSpace A]
    [CommGroup B] [TopologicalSpace B] (ha : IsCompactlyGeneratedGroup A)
    (hb : IsCompactlyGeneratedGroup B) : IsCompactlyGeneratedGroup (A × B) := by
  obtain ⟨U, hu, huc, hgen⟩ := ha
  obtain ⟨V, hv, hvc, hgen'⟩ := hb
  refine ⟨U ×ˢ V, prod_mem_nhds hu hv, huc.prod hvc, eq_top_iff.mpr ?_⟩
  let K := Subgroup.closure (U ×ˢ V)
  have h1 : ⊤ ≤ K.comap (MonoidHom.inl A B) := by
    rw [← hgen, Subgroup.closure_le]
    exact fun x hx ↦ Subgroup.subset_closure ⟨hx, mem_of_mem_nhds hv⟩
  have h2 : ⊤ ≤ K.comap (MonoidHom.inr A B) := by
    rw [← hgen', Subgroup.closure_le]
    exact fun x hx ↦ Subgroup.subset_closure ⟨mem_of_mem_nhds hu, hx⟩
  rintro ⟨x,y⟩ -
  have h := K.mul_mem (h1 (Subgroup.mem_top x)) (h2 (Subgroup.mem_top y))
  simpa only [MonoidHom.inl_apply, MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one, one_mul] using h

private theorem laurent_prod_ann {A B C : Type*} [CommGroup A] [TopologicalSpace A]
    [CommGroup B] [TopologicalSpace B] [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [T2Space A] [T2Space B] [T2Space C] [LocallyCompactSpace A] [LocallyCompactSpace B] [LocallyCompactSpace C]
    (d : C ≃ₜ* A × B) (K : Subgroup A) (U : Subgroup B) :
    Nonempty ((lcaAnnihilator K × lcaAnnihilator U) ≃ₜ*
      lcaAnnihilator ((K.prod U).comap d.toMulEquiv.toMonoidHom)) := by
  let j : C →ₜ* A × B := ContinuousMonoidHom.toContinuousMonoidHom d
  let j' : A × B →ₜ* C := ContinuousMonoidHom.toContinuousMonoidHom d.symm
  let p := (ContinuousMonoidHom.fst A B).comp j
  let q := (ContinuousMonoidHom.snd A B).comp j
  let u := j'.comp (ContinuousMonoidHom.inl A B)
  let v := j'.comp (ContinuousMonoidHom.inr A B)
  let H := (K.prod U).comap d.toMulEquiv.toMonoidHom
  let make (z : lcaAnnihilator K × lcaAnnihilator U) : PontryaginDual C :=
    (PontryaginDual.map p z.1.val) * (PontryaginDual.map q z.2.val)
  have hm (z) : make z ∈ lcaAnnihilator H := by
    refine (mem_lcaAnnihilator_iff H _).mpr fun x ↦ ?_
    change z.1.val (d x.val).1 * z.2.val (d x.val).2 = 1
    exact (congrArg₂ (· * ·) ((mem_lcaAnnihilator_iff _ _).1 z.1.property ⟨_, x.property.1⟩)
      ((mem_lcaAnnihilator_iff _ _).1 z.2.property ⟨_, x.property.2⟩)).trans (one_mul 1)
  have hu (χ : lcaAnnihilator H) : PontryaginDual.map u χ.val ∈ lcaAnnihilator K := by
    refine (mem_lcaAnnihilator_iff K _).mpr fun x ↦ (mem_lcaAnnihilator_iff H _).1 χ.property
      ⟨d.symm (x.val,1), ?_⟩
    change d (d.symm _) ∈ K.prod U
    rw [d.apply_symm_apply]; exact ⟨x.property, U.one_mem⟩
  have hv (χ : lcaAnnihilator H) : PontryaginDual.map v χ.val ∈ lcaAnnihilator U := by
    refine (mem_lcaAnnihilator_iff U _).mpr fun x ↦ (mem_lcaAnnihilator_iff H _).1 χ.property
      ⟨d.symm (1,x.val), ?_⟩
    change d (d.symm _) ∈ K.prod U
    rw [d.apply_symm_apply]; exact ⟨K.one_mem, x.property⟩
  refine ⟨{ toFun := fun z ↦ ⟨make z, hm z⟩
            invFun := fun χ ↦ (⟨_, hu χ⟩, ⟨_, hv χ⟩)
            map_mul' := ?_, left_inv := ?_, right_inv := ?_,
            continuous_toFun := ?_, continuous_invFun := ?_ }⟩
  · intro z
    refine Prod.ext (Subtype.ext (PontryaginDual.ext fun a ↦ ?_))
      (Subtype.ext (PontryaginDual.ext fun b ↦ ?_))
    · change z.1.val (d (d.symm (a,1))).1 * z.2.val (d (d.symm (a,1))).2 = z.1.val a
      rw [d.apply_symm_apply, map_one, mul_one]
    · change z.1.val (d (d.symm (1,b))).1 * z.2.val (d (d.symm (1,b))).2 = z.2.val b
      rw [d.apply_symm_apply, map_one, one_mul]
  · intro χ
    refine Subtype.ext (PontryaginDual.ext fun x ↦ ?_)
    change χ.val (d.symm ((d x).1,1)) * χ.val (d.symm (1,(d x).2)) = χ.val x
    rw [← map_mul, ← map_mul]; simp
  · intro x y
    refine Subtype.ext (PontryaginDual.ext fun a ↦ ?_)
    change (x.1.val _ * y.1.val _) * (x.2.val _ * y.2.val _) = _
    change _ = (x.1.val _ * x.2.val _) * (y.1.val _ * y.2.val _)
    ac_rfl
  · exact (((PontryaginDual.map p).continuous.comp (continuous_subtype_val.comp continuous_fst)).mul
      ((PontryaginDual.map q).continuous.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · exact (((PontryaginDual.map u).continuous.comp continuous_subtype_val).subtype_mk _).prodMk
      (((PontryaginDual.map v).continuous.comp continuous_subtype_val).subtype_mk _)
private theorem laurent_stage_mask {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    (hr : r ↔ p ∧ q) (f : r → ℂ) (g : p → ℂ) (h : ∀ t, f t = g ((hr.mp t).1)) :
    (if t : r then f t else 0) = if q then (if t : p then g t else 0) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

open Classical in
/-- Adjoining the same compact open subgroup to the support and period groups leaves the
elementary quotient unchanged. Its stage map extends by the subgroup indicator. -/
private theorem laurent_insert_stage {A B C : Type*} [CommGroup A] [TopologicalSpace A]
    [CommGroup B] [TopologicalSpace B] [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [T2Space A] [T2Space B] [T2Space C] [LocallyCompactSpace A] [LocallyCompactSpace B]
    [LocallyCompactSpace C]
    (d : C ≃ₜ* A × B) (U : Subgroup B) (ho : IsOpen (U : Set B)) (hc : IsCompact (U : Set B))
    (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient) :
    ∃ (b : BruhatStructuralPair C) (e' : ElementaryLCAPresentation b.quotient)
      (j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e'), ∀ f x,
      schwartzBruhatStageRealization b e' (j f) x =
        if (d x).2 ∈ U then schwartzBruhatStageRealization a e f (d x).1 else 0 := by
  let J := a.val.1
  let K := OrderDual.ofDual a.val.2
  let J' := (J.prod U).comap d.toMulEquiv.toMonoidHom
  let K' := (K.prod U).comap d.toMulEquiv.toMonoidHom
  let dj : J' ≃ₜ* J × U :=
    { toFun := fun x ↦ (⟨(d x.val).1, x.property.1⟩, ⟨(d x.val).2, x.property.2⟩)
      invFun := fun z ↦ ⟨d.symm (z.1.val,z.2.val), by
        change d (d.symm _) ∈ J.prod U; rw [d.apply_symm_apply]; exact ⟨z.1.property,z.2.property⟩⟩
      map_mul' := fun x y ↦ Prod.ext (Subtype.ext (congrArg Prod.fst (map_mul d x.val y.val)))
        (Subtype.ext (congrArg Prod.snd (map_mul d x.val y.val)))
      left_inv := fun x ↦ Subtype.ext (d.symm_apply_apply x.val)
      right_inv := fun z ↦ Prod.ext (Subtype.ext (congrArg Prod.fst (d.apply_symm_apply _)))
        (Subtype.ext (congrArg Prod.snd (d.apply_symm_apply _)))
      continuous_toFun := ((d.continuous.comp continuous_subtype_val).fst.subtype_mk _).prodMk
        ((d.continuous.comp continuous_subtype_val).snd.subtype_mk _)
      continuous_invFun := (d.symm.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk (fun z ↦ by
          change d (d.symm (z.1.val,z.2.val)) ∈ J.prod U
          rw [d.apply_symm_apply]; exact ⟨z.1.property,z.2.property⟩) }
  let : CompactSpace U := isCompact_iff_compactSpace.mp hc
  let : CompactSpace (lcaAnnihilator U) := isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator U ho)
  have hc' : IsCompact (K' : Set C) := d.toHomeomorph.isCompact_preimage.mpr
    ((IsBruhatGoodSubgroup.isCompact a.property.2.2.1).prod hc)
  let b : BruhatStructuralPair C := ⟨(J',OrderDual.toDual K'), (a.property.1.prod ho).preimage d.continuous,
    isCompactlyGeneratedGroup_of_continuousMulEquiv dj.symm
      (laurent_compactGen_prod a.property.2.1 isCompactlyGeneratedGroup_of_compact),
    ⟨hc'.isClosed, isOpen_lcaAnnihilator K' hc', isCompactlyGeneratedGroup_of_continuousMulEquiv
      (laurent_prod_ann d K U).some (laurent_compactGen_prod a.property.2.2.1.2.2 isCompactlyGeneratedGroup_of_compact)⟩,
    fun _ hx ↦ ⟨a.property.2.2.2 hx.1,hx.2⟩⟩
  let p := (MonoidHom.fst J U).comp dj.toMulEquiv.toMonoidHom
  let i := dj.symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inl J U)
  let N := K.comap J.subtype
  let N' := K'.comap J'.subtype
  have hp : N' ≤ N.comap p := fun x hx ↦ hx.1
  have hi : N ≤ N'.comap i := by
    intro x hx
    change d (d.symm (x.val,1)) ∈ K.prod U
    rw [d.apply_symm_apply]; exact ⟨hx,U.one_mem⟩
  let p' := QuotientGroup.map N' N p hp
  let i' := QuotientGroup.map N N' i hi
  let dq : b.quotient ≃ₜ* a.quotient := by
    refine { p' with
              invFun := i'
              left_inv := ?_, right_inv := ?_,
              continuous_toFun := (QuotientGroup.isQuotientMap_mk N').continuous_iff.mpr
                (QuotientGroup.continuous_mk.comp (continuous_fst.comp dj.continuous))
              continuous_invFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
                (QuotientGroup.continuous_mk.comp (dj.symm.continuous.comp (continuous_id.prodMk continuous_const))) }
    · intro z; induction z using QuotientGroup.induction_on with | H x => ?_
      change (QuotientGroup.mk (i (p x)) : J' ⧸ N') = QuotientGroup.mk x
      apply QuotientGroup.eq.mpr
      change d ((d.symm ((d x.val).1,1))⁻¹ * x.val) ∈ K.prod U
      rw [map_mul, map_inv, d.apply_symm_apply]
      change (d x.val).1⁻¹ * (d x.val).1 ∈ K ∧ (1:B)⁻¹ * (d x.val).2 ∈ U
      rw [inv_mul_cancel, inv_one, one_mul]; exact ⟨K.one_mem,x.property.2⟩
    · intro z; induction z using QuotientGroup.induction_on with | H x => ?_
      change (QuotientGroup.mk (p (i x)) : J ⧸ N) = QuotientGroup.mk x
      exact congrArg QuotientGroup.mk (Subtype.ext (congrArg Prod.fst (d.apply_symm_apply (x.val,1))))
  let e' : ElementaryLCAPresentation b.quotient := { e with equiv := dq.trans e.equiv }
  refine ⟨b,e',ContinuousLinearMap.id ℂ _, fun f x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  exact laurent_stage_mask (show x ∈ b.val.1 ↔ (d x).1 ∈ a.val.1 ∧ (d x).2 ∈ U from Iff.rfl)
    _ _ (fun _ ↦ rfl)

private theorem laurent_cont_of_stages {A : Type*} [CommGroup A] [TopologicalSpace A]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [PolynormableSpace ℂ V]
    (L : SchwartzBruhat A →ₗ[ℂ] V) (h : ∀ a e,
      Continuous (L ∘ (schwartzBruhatStageInclusion a e : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat A))) :
    Continuous L := by
  apply (PolynormableSpace.withSeminorms ℂ V).continuous_of_continuous_comp L
  intro q
  let p := q.1.comp L
  have hp (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := q.2.comp (h a e)
  exact (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p,hp⟩

private theorem laurent_stage_cont {A : Type*} [CommGroup A] [TopologicalSpace A]
    (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient) :
    Continuous (fun f : SchwartzBruhatStage e ↦ (show SchwartzBruhat A from schwartzBruhatStageInclusion a e f)) := by
  apply (withGeneratingSeminorms_spec _ Subtype.val).continuous_of_continuous_comp
    (schwartzBruhatStageInclusion a e : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat A)
  rintro ⟨q,hq⟩
  exact hq a e

private theorem laurent_realize_clm {A C : Type*} [CommGroup A] [TopologicalSpace A]
    [CommGroup C] [TopologicalSpace C] (M : (A → ℂ) →ₗ[ℂ] (C → ℂ))
    (hs : ∀ (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient),
      ∃ (b : BruhatStructuralPair C) (e' : ElementaryLCAPresentation b.quotient)
        (j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e'), ∀ f,
          M (schwartzBruhatStageRealization a e f) = schwartzBruhatStageRealization b e' (j f)) :
    ∃ L : SchwartzBruhat A →L[ℂ] SchwartzBruhat C, ∀ f, (L f).val = M f.val := by
  have h : schwartzBruhatSubmodule A ≤ (schwartzBruhatSubmodule C).comap M := by
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨f,rfl⟩
    with_reducible refine (hs a e).elim fun b hb ↦ hb.elim fun e' he ↦ he.elim fun j hj ↦ ?_
    change M _ ∈ schwartzBruhatSubmodule C
    rw [hj]
    exact (schwartzBruhatStageInclusion b e' (j f)).property
  let L : SchwartzBruhat A →ₗ[ℂ] SchwartzBruhat C :=
    (M.comp (schwartzBruhatSubmodule A).subtype).codRestrict _ (fun f ↦ h f.property)
  refine ⟨⟨L, ?_⟩, fun f ↦ rfl⟩
  refine laurent_cont_of_stages L fun a e ↦ ?_
  with_reducible refine (hs a e).elim fun b hb ↦ hb.elim fun e' he ↦ he.elim fun j hj ↦ ?_
  have hh (s : SchwartzBruhatStage e) :
      (show SchwartzBruhat C from schwartzBruhatStageInclusion b e' (j s)) =
        L (schwartzBruhatStageInclusion a e s) := Subtype.ext (hj s).symm
  exact ((laurent_stage_cont b e').comp j.continuous).congr hh

open Classical in
private theorem laurent_insert_clm {A B C : Type*} [CommGroup A] [TopologicalSpace A]
    [CommGroup B] [TopologicalSpace B] [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]
    [T2Space A] [T2Space B] [T2Space C] [LocallyCompactSpace A] [LocallyCompactSpace B]
    [LocallyCompactSpace C]
    (d : C ≃ₜ* A × B) (U : Subgroup B) (ho : IsOpen (U : Set B)) (hc : IsCompact (U : Set B)) :
    ∃ L : SchwartzBruhat A →L[ℂ] SchwartzBruhat C, ∀ f x,
      L f x = if (d x).2 ∈ U then f (d x).1 else 0 := by
  let M : (A → ℂ) →ₗ[ℂ] (C → ℂ) := LinearMap.pi fun x ↦
    if (d x).2 ∈ U then LinearMap.proj (d x).1 else 0
  have hM (f : A → ℂ) (x : C) : M f x = if (d x).2 ∈ U then f (d x).1 else 0 := by
    dsimp only [M,LinearMap.pi_apply]; split <;> rfl
  have hs (a : BruhatStructuralPair A) (e : ElementaryLCAPresentation a.quotient) :
      ∃ (b : BruhatStructuralPair C) (e' : ElementaryLCAPresentation b.quotient)
        (j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e'), ∀ f,
          M (schwartzBruhatStageRealization a e f) = schwartzBruhatStageRealization b e' (j f) := by
    with_reducible refine (laurent_insert_stage d U ho hc a e).elim fun b hb ↦ hb.elim fun e' he ↦ he.elim fun j h ↦ ?_
    exact ⟨b,e',j,fun f ↦ funext fun x ↦ (hM _ _).trans (h f x).symm⟩
  with_reducible refine (laurent_realize_clm M hs).elim fun L hL ↦ ?_
  exact ⟨L, fun f x ↦ (congrFun (hL f) x).trans (hM f.val x)⟩
open Classical in
private theorem laurent_split (hST : S ⊆ T) : ∃ d : Multiplicative (SAdeleRing F T) ≃ₜ*
    Multiplicative (SAdeleRing F S) × Multiplicative (FinitePlaceProduct F (T \ S)),
    ∀ x : SAdeleRing F T, d (Multiplicative.ofAdd x) =
      (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩),
        Multiplicative.ofAdd (fun w : ↥(T \ S) ↦ x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)) := by
  let split (x : SAdeleRing F T) : SAdeleRing F S × FinitePlaceProduct F (T \ S) :=
    ((x.1, fun w ↦ x.2 ⟨w.val, hST w.property⟩),
      fun w ↦ x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)
  let join (y : SAdeleRing F S × FinitePlaceProduct F (T \ S)) : SAdeleRing F T :=
    (y.1.1, fun w ↦ if h : w.val ∈ S then y.1.2 ⟨w.val, h⟩
      else y.2 ⟨w.val, Finset.mem_sdiff.mpr ⟨w.property, h⟩⟩)
  refine ⟨{ toFun := split, invFun := join, map_mul' := fun _ _ ↦ rfl,
            left_inv := ?_, right_inv := ?_, continuous_toFun := ?_, continuous_invFun := ?_ }, fun _ ↦ rfl⟩
  · intro x
    change join (split x.toAdd) = x.toAdd
    refine Prod.ext (by rfl) ?_
    funext w
    change (if h : w.val ∈ S then _ else _) = _
    split <;> rfl
  · rintro ⟨x, y⟩
    refine Prod.ext (Prod.ext rfl (funext fun w ↦ ?_)) (funext fun w ↦ ?_)
    · exact dite_eq_left w.property
    · exact dite_eq_right (Finset.mem_sdiff.mp w.property).2
  · exact (continuous_fst.prodMk (continuous_pi fun w ↦ (continuous_apply _).comp continuous_snd)).prodMk
      (continuous_pi fun w ↦ (continuous_apply _).comp continuous_snd)
  · refine (continuous_fst.comp continuous_fst).prodMk (continuous_pi fun w ↦ ?_)
    by_cases hw : w.val ∈ S
    · simp only [dite_eq_left hw]
      exact (continuous_apply (⟨w.val, hw⟩ : S)).comp (continuous_snd.comp continuous_fst)
    · simp only [dite_eq_right hw]
      exact (continuous_apply (⟨w.val, Finset.mem_sdiff.mpr ⟨w.property, hw⟩⟩ : ↥(T \ S))).comp continuous_snd


open Classical in
private theorem laurent_ballGroup (D : Finset Places) (π : ∀ w : D, (L(w.val))ˣ) (a : D → ℤ) :
    ∃ U : Subgroup (Multiplicative (FinitePlaceProduct F D)), IsOpen (U : Set (Multiplicative (FinitePlaceProduct F D))) ∧ IsCompact (U : Set (Multiplicative (FinitePlaceProduct F D))) ∧
      ∀ x : FinitePlaceProduct F D, (if Multiplicative.ofAdd x ∈ U then 1 else 0 : ℂ) =
        ∏ w : D, finitePlaceBallIndicator w.val (π w) (a w) (x w) := by
  let c (w : D) := (π w ^ (-a w)).val
  let H (w : D) := O(w.val).toAddSubgroup.comap (AddMonoidHom.mulLeft (c w))
  let h (w : D) := Homeomorph.mulLeft₀ (c w) (π w ^ (-a w)).ne_zero
  have ho (w : D) : IsOpen (H w : Set L(w.val)) := (Valued.isOpen_valuationSubring _).preimage (h w).continuous
  have hc (w : D) : IsCompact (H w : Set L(w.val)) := (h w).isCompact_preimage.mpr
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w.val))
  let U := (AddSubgroup.pi Set.univ H).toSubgroup
  refine ⟨U, isOpen_set_pi finite_univ (fun w _ ↦ ho w), isCompact_univ_pi hc, fun x ↦ ?_⟩
  have hmem : Multiplicative.ofAdd x ∈ U ↔ ∀ w, c w * x w ∈ O(w.val) := by
    change (∀ w ∈ Set.univ, x w ∈ H w) ↔ _
    simp only [mem_univ, forall_const]; rfl
  by_cases h : Multiplicative.ofAdd x ∈ U
  · rw [ite_eq_left h]
    symm; apply Finset.prod_eq_one
    intro w _
    exact Set.indicator_of_mem (hmem.mp h w) _
  · rw [ite_eq_right h]
    obtain ⟨w,hw⟩ := not_forall.mp (mt hmem.mpr h)
    exact (Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _ :
      finitePlaceBallIndicator w.val (π w) (a w) (x w) = 0)).symm

open Classical in
private theorem laurent_insert_ball (hST : S ⊆ T) (π : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (a : ↥(T \ S) → ℤ) :
    ∃ L : ℬ(SAdeleRing F S) →L[ℂ] ℬ(SAdeleRing F T), ∀ (f : ℬ(SAdeleRing F S)) (x : SAdeleRing F T),
      L f (Multiplicative.ofAdd x) =
        f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩)) *
          ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w)
            (x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) := by
  let (w : Places) : ProperSpace (L(w)) := properSpace_adicCompletion w
  let : LocallyCompactSpace (InfiniteAdeleRing F) := InfiniteAdeleRing.locallyCompactSpace F
  let (U : Finset Places) : LocallyCompactSpace (Multiplicative (SAdeleRing F U)) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FinitePlaceProduct F U))
  let : LocallyCompactSpace (Multiplicative (FinitePlaceProduct F (T \ S))) :=
    inferInstanceAs (LocallyCompactSpace (FinitePlaceProduct F (T \ S)))
  let : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let (U : Finset Places) : T2Space (Multiplicative (SAdeleRing F U)) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing F × FinitePlaceProduct F U))
  let : T2Space (Multiplicative (FinitePlaceProduct F (T \ S))) :=
    inferInstanceAs (T2Space (FinitePlaceProduct F (T \ S)))
  with_reducible refine (laurent_split (F := F) hST).elim fun d hd ↦ ?_
  with_reducible refine (laurent_ballGroup (T \ S) π a).elim fun U h ↦ ?_
  with_reducible refine (laurent_insert_clm d U h.1 h.2.1).elim fun L hL ↦ ?_
  refine ⟨L, fun f x ↦ ?_⟩
  rw [hL, hd, ← h.2.2]
  split <;> simp

private theorem laurent_assemble {I X Y : Type*} [AddMonoid I]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]
    (L : I → X →L[ℂ] Y) :
    ∃ A : InductiveTensor X (FinestLocallyConvex (AddMonoidAlgebra ℂ I)) →L[ℂ] Y,
      ∀ (x : X) (i : I), A (x ⊗ₜ[ℂ] AddMonoidAlgebra.single i 1) = L i x := by
  classical
  let P := FinestLocallyConvex (AddMonoidAlgebra ℂ I)
  let T := InductiveTensor X P
  let b : Module.Basis I ℂ P := AddMonoidAlgebra.basis I ℂ
  let M := b.constr ℂ fun i ↦ (L i).toLinearMap
  let A : T →ₗ[ℂ] Y := TensorProduct.lift M.flip
  have hA (x : X) (p : P) : A (x ⊗ₜ[ℂ] p) = M p x := rfl
  have h (i : I) : M (b i) = (L i).toLinearMap := b.constr_basis ℂ _ i
  have : T2Space P := finestLocallyConvex_t2 _
  refine ⟨⟨A, (continuous_inductiveTensor_iff (E := X) (F := P) A).mpr ⟨?_, ?_⟩⟩,
    fun x i ↦ (hA x (b i)).trans (LinearMap.congr_fun (h i) x)⟩
  · intro x
    exact continuous_of_finestLocallyConvex _ (M.flip x)
  · intro p
    rw [← b.linearCombination_repr p, Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [hA,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,h]
    let := PolynormableSpace.isTopologicalAddGroup ℂ Y
    let := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
    exact continuous_finsetSum _ fun i _ ↦ (L i).continuous.const_smul _

private theorem laurent_ball_invariant (w : Places) (π : (L(w))ˣ) (a : ℤ) (x t u : L(w))
    (htu : t*u = 1) (ht : t ∈ O(w)) (hu : u ∈ O(w)) :
    finitePlaceBallIndicator w π a (t*x) = finitePlaceBallIndicator w π a x := by
  classical
  let v := (π ^ (-a)).val * x
  have he : (π ^ (-a)).val * (t*x) = t*v := by dsimp [v]; ring
  have h : t*v ∈ O(w) ↔ v ∈ O(w) := by
    refine ⟨fun hv ↦ ?_, fun hv ↦ mul_mem ht hv⟩
    have h' : (t*v)*u ∈ O(w) := mul_mem hv hu
    rwa [mul_right_comm, htu, one_mul] at h'
  unfold finitePlaceBallIndicator
  rw [he]; by_cases hv : v ∈ O(w)
  · exact (Set.indicator_of_mem (h.mpr hv) _).trans (Set.indicator_of_mem hv (fun _ ↦ (1 : ℂ))).symm
  · exact (Set.indicator_of_notMem (mt h.mp hv) _).trans (Set.indicator_of_notMem hv _).symm

open Classical in
private theorem laurent_ball_fixed (hST : S ⊆ T) (π : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (a : ↥(T \ S) → ℤ) (f : ℬ(SAdeleRing F S)) (z : ℬ(SAdeleRing F T))
    (hz : ∀ (x : SAdeleRing F T), z (Multiplicative.ofAdd x) =
        f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩)) *
          ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w)
            (x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)) :
    z ∈ Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
          (relativeIntegralIdeleUnits F S T).subtype) := by
  intro g
  apply Subtype.ext
  funext x
  change z (Multiplicative.ofAdd ((g.val⁻¹).val * x.toAdd)) = z (Multiplicative.ofAdd x.toAdd)
  rw [hz, hz]
  have hg := (mem_relativeIntegralIdeleUnits_iff (S := S) (g.val⁻¹)).mp (Subgroup.inv_mem _ g.property)
  congr 1
  · apply congrArg f
    apply Multiplicative.ext
    refine Prod.ext ?_ (funext fun w ↦ ?_)
    · change (g.val⁻¹).val.1 * _ = _; rw [hg.1,one_mul]; rfl
    · change (g.val⁻¹).val.2 ⟨w.val, hST w.property⟩ * _ = _
      rw [hg.2.1 _ w.property,one_mul]; rfl
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    let v : T := ⟨w.val,(Finset.mem_sdiff.mp w.property).1⟩
    have h := hg.2.2 v (Finset.mem_sdiff.mp w.property).2
    exact laurent_ball_invariant w.val (π w) (a w) _ _ _
      (congrFun (congrArg Prod.snd (g.val⁻¹).val_inv) v) h.1 h.2

private theorem laurent_schwartz_t2 (G : Type*) [CommGroup G] [TopologicalSpace G] : T2Space (SchwartzBruhat G) :=
  T2Space.of_injective_continuous (f := fun f : SchwartzBruhat G ↦ f.val) Subtype.val_injective
    (continuous_pi fun x ↦ schwartzBruhat_eval_continuous x)

open Classical in
private theorem laurent_forward (hST : S ⊆ T)
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ) :
    ∃ e : InductiveTensor ℬ(SAdeleRing F S)
        (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) →L[ℂ]
        (Representation.invariants <| (schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
          (relativeIntegralIdeleUnits F S T).subtype),
      ∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
        (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩)) *
            ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w)
              (x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) := by
  let H := Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
      (relativeIntegralIdeleUnits F S T).subtype)
  have h (a : ↥(T \ S) → ℤ) := laurent_insert_ball (F := F) hST π a
  let L (a : ↥(T \ S) → ℤ) : ℬ(SAdeleRing F S) →L[ℂ] H := (h a).choose.codRestrict H
    (fun f ↦ laurent_ball_fixed hST π a f _ ((h a).choose_spec f))
  let (D : Finset Places) : T2Space ℬ(SAdeleRing F D) := laurent_schwartz_t2 _
  with_reducible refine (laurent_assemble L).elim fun e he ↦ ?_
  with_reducible refine ⟨e, ?_⟩
  intro f a x
  with_reducible refine (congrArg (fun z : H ↦ z.val (Multiplicative.ofAdd x)) (he f a)).trans ?_
  change (h a).choose f (Multiplicative.ofAdd x) = _
  exact (h a).choose_spec f x

/-- Charts for an open homomorphism on the connected components that meet its image.
Unlike the open quotient charts, the homomorphism need not be surjective. -/
private theorem laurent_chart {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hc : Continuous φ) (ho : IsOpenMap φ) :
    ∃ L : (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')) →L[ℝ]
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      ∀ a b, elementaryCover 0 a b ∈ φ.range → ∃ y a' b', ∀ x, ∃ w : H, w.val = elementaryCover (L x + y) a' b' ∧
        φ w = elementaryCover x a b := by
  let q := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  have hq := elementaryCoverZeroHom_continuous_isOpenMap (m := m) (n := n) (r := r) (F := F)
  have hmem (x) : q x ∈ H := by
    have he := ((show IsClopen (H : Set (ElementaryLieGroup m n r F)) from ⟨H.isClosed_of_isOpen hH, hH⟩).preimage hq.1).eq_univ
      (show (q ⁻¹' (H : Set (ElementaryLieGroup m n r F))).Nonempty from ⟨0, by simp [q]⟩)
    exact eq_univ_iff_forall.mp he x
  let j := q.codRestrict H hmem
  have hj : Continuous j := hq.1.subtype_mk _
  have hjOpen : IsOpenMap j := by
    intro U hU
    rw [show j '' U = Subtype.val ⁻¹' (q '' U) from Set.ext fun w ↦
      ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, hx, congrArg Subtype.val h⟩,
        fun ⟨x, hx, h⟩ ↦ ⟨x, hx, Subtype.ext h⟩⟩]
    exact (hq.2 U hU).preimage continuous_subtype_val
  obtain ⟨L, hL⟩ := elementary_linear_section (φ.comp j) (hc.comp hj) (ho.comp hjOpen)
  refine ⟨L, fun a b hs ↦ ?_⟩
  obtain ⟨w, hw⟩ := hs
  obtain ⟨t, ht⟩ := elementaryCover_surjective w.val.2.2.1 w.val.2.2.2 w.val.1 w.val.2.1
  refine ⟨(w.val.1, t), w.val.2.2.1, w.val.2.2.2, fun x ↦ ⟨j (L x) + w, ?_, ?_⟩⟩
  · change q (L x) + w.val = _
    conv_lhs => rw [← show elementaryCover (w.val.1,t) w.val.2.2.1 w.val.2.2.2 = w.val from ht]
    refine Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_add _ _ _).symm) (zero_add _))
  · rw [map_add, show φ (j (L x)) = _ from hL x, hw]
    simp [elementaryCover, Pi.zero_def]
/-- Descend a Schwartz function along an open homomorphism, extending by zero outside
the image. The components outside the image have all Schwartz bounds equal to zero. -/
private theorem laurent_open_quotient {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    (H : AddSubgroup (ElementaryLieGroup m n r F)) (hH : IsOpen (H : Set (ElementaryLieGroup m n r F)))
    (φ : H →+ ElementaryLieGroup m' n' r' F') (hc : Continuous φ) (ho : IsOpenMap φ)
    (s : ElementarySchwartz m n r F)
    (g : ElementaryLieGroup m' n' r' F' → ℂ) (hg : ∀ w : H, s w.val = g (φ w))
    (hz : ∀ y ∉ φ.range, g y = 0) :
    g ∈ elementarySchwartzSubmodule m' n' r' F' := by
  classical
  obtain ⟨L, hL⟩ := laurent_chart H hH φ hc ho
  have hoff (a b) (h : elementaryCover 0 a b ∉ φ.range) :
      (fun x ↦ g (elementaryCover x a b)) = 0 := by
    funext x
    apply hz
    let H' : OpenSubgroup (Multiplicative (ElementaryLieGroup m' n' r' F')) :=
      ⟨φ.range.toSubgroup, show IsOpen (φ.range : Set (ElementaryLieGroup m' n' r' F')) by rw [AddMonoidHom.coe_range, ← image_univ]; exact ho _ isOpen_univ⟩
    exact fun hy ↦ h ((elementary_open_mask H' (elementaryCover x a b)).mp hy)
  have hfiber (a b) (h : elementaryCover 0 a b ∈ φ.range) : ∃ y a' b', ∀ x, g (elementaryCover x a b) = s (elementaryCover (L x + y) a' b') := by
    obtain ⟨y, a', b', h⟩ := hL a b h
    refine ⟨y, a', b', fun x ↦ ?_⟩
    obtain ⟨w, hw, hp⟩ := h x
    rw [← hp, ← hw, hg]
  refine ⟨fun a b ↦ ?_, fun i ↦ ?_⟩
  · by_cases h : elementaryCover 0 a b ∈ φ.range
    · obtain ⟨y, a', b', h'⟩ := hfiber a b h
      rw [funext h']
      exact (s.property.1 a' b').comp (L.contDiff.add contDiff_const)
    · rw [hoff a b h]; exact contDiff_const
  obtain ⟨p, hp⟩ := elementary_open_quotient_weight H hH φ hc i.1 i.2.2.2
  obtain ⟨T, c, hT⟩ := elementaryPartial_comp_lift (r := r) (r' := r') (F := F) (F' := F') L i.2.1 i.2.2.1
  let M (v : (Fin m → ℕ) × (Fin n → ℕ)) := ∑ d ∈ p.support, ‖p.coeff d‖ *
    elementarySchwartzSeminorm (fun k ↦ d (Sum.inl k), v.1, v.2, fun j ↦ d (Sum.inr j)) s
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ∑ v ∈ T, ‖c v‖ * M v))
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  by_cases h : elementaryCover 0 a b ∈ φ.range
  swap
  · simp [elementaryPartial, hoff a b h]
  obtain ⟨y, a', b', h⟩ := hL a b h
  have hfun (u) : g (elementaryCover u a b) = s (elementaryCover (L u + y) a' b') := by
    obtain ⟨w, hw, hp⟩ := h u
    rw [← hp, ← hw, hg]
  have hpart := hT s g y a b a' b' (s.property.1 a' b') hfun x
  obtain ⟨w, hw, hφ⟩ := h x
  have hwgt := hp w
  rw [hw,hφ] at hwgt
  let vcoord := Sum.elim (fun k : Fin m ↦ ((L x + y).1 k : ℂ)) (fun j : Fin r ↦ (a' j : ℂ))
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

/-- Test elementary Schwartz membership on a common source with open maps into the two
elementary groups, allowing extension by zero off the second image. -/
private theorem laurent_common {m n r m' n' r' : ℕ} {F F' : Type}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']
    {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    (p : A →+ ElementaryLieGroup m n r F) (pc : Continuous p) (po : IsOpenMap p)
    (q : A →+ ElementaryLieGroup m' n' r' F') (qc : Continuous q) (qo : IsOpenMap q)
    (hk : p.ker ≤ q.ker)
    (s : ElementarySchwartz m n r F) (g : ElementaryLieGroup m' n' r' F' → ℂ)
    (hg : ∀ x, s (p x) = g (q x)) (hz : ∀ y ∉ q.range, g y = 0) : g ∈ elementarySchwartzSubmodule m' n' r' F' := by
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
  have hφ (x) : φ (j x) = q x := j.liftOfRightInverseAux_comp_apply _ _ _ _ x
  have hφc : Continuous φ := hj.isQuotientMap.continuous_iff.mpr (qc.congr (fun x ↦ (hφ x).symm))
  have hφo : IsOpenMap φ := by
    intro U hU
    rw [← image_preimage_eq U hj.surjective, ← image_comp, show φ ∘ j = q from funext hφ]
    exact qo _ (hU.preimage hj.continuous)
  refine laurent_open_quotient H hH φ hφc hφo s g ?_ (fun y hy ↦ hz y ?_)
  · intro w
    obtain ⟨x,rfl⟩ := hj.surjective w
    rw [hφ]; exact hg x
  · rintro ⟨x,rfl⟩; exact hy ⟨j x,hφ x⟩


private theorem laurent_slice_good {A B : Type*} [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [LocallyCompactSpace A] [LocallyCompactSpace B] (K : Subgroup (A × B)) (hk : IsBruhatGoodSubgroup K)
:
    IsBruhatGoodSubgroup (K.comap (MonoidHom.inl A B)) := by
  let i := ContinuousMonoidHom.inl A B
  let N := K.comap i.toMonoidHom
  have hc : IsCompact (N : Set A) := by
    have h := (hk.isCompact.inter_right ((isClosed_singleton (X := B) (x := (1:B))).preimage (continuous_snd : Continuous (Prod.snd : A × B → B)))).image continuous_fst
    convert h using 1
    ext x
    exact ⟨fun hx ↦ ⟨(x,1),⟨hx,rfl⟩,rfl⟩, fun ⟨(v,w),⟨hv,(hw : w = 1)⟩,(h : v = x)⟩ ↦ by subst x; subst w; exact hv⟩
  have : IsClosed (N : Set A) := hc.isClosed
  have : IsClosed (K : Set (A × B)) := hk.1
  change IsBruhatGoodSubgroup N
  rw [good_iff_quotient _ hc]
  let j := inducedQuotientHom i K
  have hj : Injective j := (QuotientGroup.injective_lift_iff (K.comap i.toMonoidHom) ((QuotientGroup.mk' K).comp i.toMonoidHom) (fun x hx ↦ (QuotientGroup.eq_one_iff _).mpr hx)).mpr (by
    ext x; exact (QuotientGroup.eq_one_iff (N := K) (i x)).symm)
  obtain ⟨W,hW,hpow⟩ := exists_nhds_one_of_isLocallyEuclidean ((good_iff_quotient K hk.isCompact).mp hk)
  exact isLocallyEuclidean_of_noSmallCyclicSubgroups
    (show j ⁻¹' W ∈ 𝓝 1 from j.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (j 1); rwa [map_one]))
    (fun x hx ↦ hj ((hpow (j x) (fun n ↦ map_pow j x n ▸ hx n)).trans (map_one j).symm))

private theorem laurent_stage_slice_open {A B : Type*} [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [LocallyCompactSpace A] [LocallyCompactSpace B] (a : BruhatStructuralPair (A × B))
    (U : OpenSubgroup B) (hu : ∀ u ∈ U, ((1:A),u) ∈ OrderDual.ofDual a.val.2) :
    let X := a.val.1.comap (MonoidHom.inl A B)
    IsOpenMap (fun x : X ↦ (QuotientGroup.mk (⟨(x.val,1),x.property⟩ : a.val.1) : a.quotient)) := by
  intro X V hV
  let W := (Subtype.val '' V) ×ˢ (U : Set B)
  have hoX : IsOpen (X : Set A) := a.property.1.preimage (continuous_id.prodMk continuous_const)
  have hW : IsOpen W := (hoX.isOpenMap_subtype_val _ hV).prod U.isOpen
  let q : a.val.1 → a.quotient := QuotientGroup.mk
  have he : (fun x : X ↦ q ⟨(x.val,1),x.property⟩) '' V = q '' (Subtype.val ⁻¹' W) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩; exact ⟨⟨(x.val,1),x.property⟩,⟨⟨x,hx,rfl⟩,U.one_mem⟩,rfl⟩
    · rintro ⟨⟨⟨x,y⟩,hxy⟩,⟨⟨v,hv,rfl⟩,hy⟩,rfl⟩
      refine ⟨v,hv,QuotientGroup.eq.mpr ?_⟩
      change ((v.val,1)⁻¹ * (v.val,y)) ∈ OrderDual.ofDual a.val.2
      simpa using hu y hy
  rw [he]; exact QuotientGroup.isOpenMap_coe _ (hW.preimage continuous_subtype_val)

private theorem laurent_slice_pair {A B : Type*} [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [LocallyCompactSpace A] [LocallyCompactSpace B] (a : BruhatStructuralPair (A × B))
    : ∃ b : BruhatStructuralPair A, b.val.1 = a.val.1.map (MonoidHom.fst A B) ∧
      OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).comap (MonoidHom.inl A B) := by
  let J := a.val.1
  let J' := J.map (MonoidHom.fst A B)
  let p := (MonoidHom.fst A B).comp J.subtype
  have hP : p.range = J' := by ext y; exact ⟨fun ⟨x,hx⟩ ↦ ⟨x.val,x.property,hx⟩,fun ⟨x,hx,hxy⟩ ↦ ⟨⟨x,hx⟩,hxy⟩⟩
  have hop : IsOpenMap p := isOpenMap_fst.comp a.property.1.isOpenMap_subtype_val
  have ho : IsOpen (J' : Set A) := isOpenMap_fst _ a.property.1
  have hp' : IsOpenMap p.rangeRestrict := by
    intro V hV
    have he : p.rangeRestrict '' V = Subtype.val ⁻¹' (p '' V) := by
      ext y; exact ⟨fun ⟨x,hx,h⟩ ↦ ⟨x,hx,congrArg Subtype.val h⟩,fun ⟨x,hx,h⟩ ↦ ⟨x,hx,Subtype.ext h⟩⟩
    rw [he]; exact (hop V hV).preimage continuous_subtype_val
  have hc : IsCompactlyGeneratedGroup J' := hP ▸ isCompactlyGeneratedGroup_of_surjective p.rangeRestrict
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _) hp' p.rangeRestrict_surjective a.property.2.1
  exact ⟨⟨(J',_), ho,hc,laurent_slice_good _ a.property.2.2.1,fun x hx ↦ ⟨(x,1),a.property.2.2.2 hx,rfl⟩⟩,rfl,rfl⟩

/-- A slice through a point of the support group descends to the old elementary
quotient after translation. The period subgroup in the new variables makes the map open. -/
private theorem laurent_shifted_stage_slice {A B : Type*} [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [LocallyCompactSpace A] [LocallyCompactSpace B] (a : BruhatStructuralPair (A × B))
    (e : ElementaryLCAPresentation a.quotient) (b : BruhatStructuralPair A)
    (c : ElementaryLCAPresentation b.quotient)
    (hb : b.val.1 = a.val.1.map (MonoidHom.fst A B))
    (hk : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).comap (MonoidHom.inl A B))
    (U : OpenSubgroup B) (hu : ∀ u ∈ U, ((1:A),u) ∈ OrderDual.ofDual a.val.2)
    (s : SchwartzBruhatStage e) (z : a.val.1) :
    ∃ v : SchwartzBruhatStage c, ∀ x : b.val.1,
      v (c.equiv (QuotientGroup.mk x)).toAdd = schwartzBruhatStageRealization a e s (z.val * (x.val,1)) := by
  classical
  let X := a.val.1.comap (MonoidHom.inl A B)
  let i : X →* a.val.1 := ((MonoidHom.inl A B).comp X.subtype).codRestrict a.val.1 (fun x ↦ x.property)
  have hX : X ≤ b.val.1 := by rw [hb]; exact fun x hx ↦ ⟨(x,1),hx,rfl⟩
  let j := Subgroup.inclusion hX
  let p := MonoidHom.toAdditive ((e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).comp i)
  let q := MonoidHom.toAdditive ((c.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).comp j)
  have pc : Continuous p := e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
    ((continuous_subtype_val.prodMk continuous_const).subtype_mk _))
  have po : IsOpenMap p := e.equiv.toHomeomorph.isOpenMap.comp (laurent_stage_slice_open a U hu)
  have qc : Continuous q := c.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
    (continuous_subtype_val.subtype_mk _))
  have qo : IsOpenMap q := c.equiv.toHomeomorph.isOpenMap.comp ((QuotientGroup.isOpenMap_coe (N := (OrderDual.ofDual b.val.2).comap b.val.1.subtype)).comp
    ((show IsOpen (X : Set A) from a.property.1.preimage (continuous_id.prodMk continuous_const)).isOpenMap_inclusion hX))
  let f (x : A) := schwartzBruhatStageRealization a e s (z.val * (x,1))
  have hInv (k : A) (h : k ∈ OrderDual.ofDual b.val.2) (x : A) : f (k*x) = f x := by
    rw [hk] at h
    have h' := stage_realization_mul_kernel a e s h (z.val * (x,1))
    have he : z.val * (k*x,1) = (k,1) * (z.val * (x,1)) := by ext <;> simp [mul_left_comm]
    exact (congrArg (schwartzBruhatStageRealization a e s) he).trans h'
  let lift : b.quotient → ℂ := Quotient.lift (fun x : b.val.1 ↦ f x.val) (by
    intro x y h
    have h' := QuotientGroup.eq.mp (show (QuotientGroup.mk x : b.quotient) = QuotientGroup.mk y from Quotient.sound h)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_right_comm, inv_mul_cancel, one_mul]
      using (hInv (x⁻¹*y).val h' x.val).symm)
  let g := fun w ↦ lift (c.equiv.symm (Multiplicative.ofAdd w))
  have hg (x : b.val.1) : g (c.equiv (QuotientGroup.mk x)).toAdd = f x.val := by
    change lift (c.equiv.symm (c.equiv _)) = _; rw [c.equiv.symm_apply_apply]; rfl
  with_reducible refine (elementarySchwartz_translate_jointly (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)).elim fun M hM ↦ ?_
  let s' := M ((e.equiv (QuotientGroup.mk z)).toAdd,s)
  refine ⟨⟨g,laurent_common p pc po q qc qo ?_ s' g ?_ ?_⟩, hg⟩
  · intro x hx
    change c.equiv (QuotientGroup.mk (j (Additive.toMul x))) = 1
    refine (congrArg c.equiv ((b.quotient_mk_eq_one _).mpr ?_)).trans (map_one _)
    rw [hk]
    apply (a.quotient_mk_eq_one (i (Additive.toMul x))).mp
    exact e.equiv.injective ((show e.equiv (QuotientGroup.mk _) = 1 from hx).trans (map_one _).symm)
  · intro x
    refine (hM _ _ _).trans (Eq.trans ?_ (hg (j x.toMul)).symm)
    change s ((e.equiv (QuotientGroup.mk z)).toAdd + (e.equiv (QuotientGroup.mk (i x.toMul))).toAdd) = f _
    change _ = schwartzBruhatStageRealization a e s (z * i x.toMul).val
    rw [schwartzBruhatStageRealization_apply, dite_eq_left (z * i x.toMul).property]
    change _ = s (e.equiv (QuotientGroup.mk (z * i x.toMul))).toAdd
    exact congrArg (fun u ↦ s (Multiplicative.toAdd u)) ((congrArg e.equiv (QuotientGroup.mk_mul _ z (i x.toMul))).trans (map_mul e.equiv _ _)).symm
  · intro y hy
    obtain ⟨t,ht⟩ := c.equiv.surjective (Multiplicative.ofAdd y)
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective t
    have hval := congrArg Multiplicative.toAdd ht
    change (c.equiv (QuotientGroup.mk x)).toAdd = y at hval
    subst y
    rw [hg]
    unfold f; rw [schwartzBruhatStageRealization_apply]; apply dite_eq_right
    intro h
    have hx : (x.val,1) ∈ a.val.1 := (a.val.1.mul_mem_cancel_left z.property).mp h
    exact hy ⟨Additive.ofMul (⟨x.val,hx⟩ : X),rfl⟩

private theorem laurent_stage_slice_mem {A B : Type*} [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [LocallyCompactSpace A] [LocallyCompactSpace B] (a : BruhatStructuralPair (A × B))
    (e : ElementaryLCAPresentation a.quotient) (b : BruhatStructuralPair A)
    (c : ElementaryLCAPresentation b.quotient) (hb : b.val.1 = a.val.1.map (MonoidHom.fst A B))
    (hk : OrderDual.ofDual b.val.2 = (OrderDual.ofDual a.val.2).comap (MonoidHom.inl A B))
    (U : OpenSubgroup B) (hu : ∀ u ∈ U, ((1:A),u) ∈ OrderDual.ofDual a.val.2)
    (s : SchwartzBruhatStage e) (y : B) : ∃ v : SchwartzBruhatStage c, ∀ x : A,
      schwartzBruhatStageRealization b c v x = schwartzBruhatStageRealization a e s (x,y) := by
  classical
  by_cases h : ∃ x : A, (x,y) ∈ a.val.1
  · obtain ⟨t,ht⟩ := h
    let z : a.val.1 := ⟨(t,y),ht⟩
    let t' : b.val.1 := ⟨t,hb ▸ (show t ∈ a.val.1.map (MonoidHom.fst A B) from ⟨(t,y),ht,rfl⟩)⟩
    with_reducible refine (laurent_shifted_stage_slice a e b c hb hk U hu s z).elim fun v hv ↦ ?_
    with_reducible refine (elementarySchwartz_translate_jointly (m := c.realDim) (n := c.torusDim) (r := c.latticeRank) (F := c.finiteFactor)).elim fun M hM ↦ ?_
    refine ⟨M ((c.equiv (QuotientGroup.mk t'⁻¹)).toAdd,v),fun x ↦ ?_⟩
    rw [schwartzBruhatStageRealization_apply b]
    by_cases hx : x ∈ b.val.1
    · rw [dite_eq_left hx,hM]
      let u : b.val.1 := ⟨x,hx⟩
      change v ((c.equiv (QuotientGroup.mk t'⁻¹) * c.equiv (QuotientGroup.mk u)).toAdd) = _
      refine Eq.trans (congrArg (fun u ↦ v (Multiplicative.toAdd u)) ((congrArg c.equiv (QuotientGroup.mk_mul _ t'⁻¹ u)).trans (map_mul c.equiv _ _)).symm) ((hv _).trans ?_)
      apply congrArg (schwartzBruhatStageRealization a e s)
      exact Prod.ext (mul_inv_cancel_left t x) (mul_one y)
    · have hxy : (x,y) ∉ a.val.1 := fun hxy ↦ hx (hb ▸ ⟨(x,y),hxy,rfl⟩)
      rw [dite_eq_right hx,schwartzBruhatStageRealization_apply,dite_eq_right hxy]
  · refine ⟨0,fun x ↦ ?_⟩
    rw [map_zero,Pi.zero_apply,schwartzBruhatStageRealization_apply,dite_eq_right (fun hxy ↦ h ⟨x,hxy⟩)]

/-- Slicing at a fixed new coordinate is a continuous linear map from the elementary
stage to the old Schwartz–Bruhat space. -/
private theorem laurent_stage_slice_clm {A B : Type*} [CommGroup A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup A] [IsTopologicalGroup B] [T2Space A] [T2Space B]
    [LocallyCompactSpace A] [LocallyCompactSpace B] (a : BruhatStructuralPair (A × B))
    (e : ElementaryLCAPresentation a.quotient) (U : OpenSubgroup B)
    (hu : ∀ u ∈ U, ((1:A),u) ∈ OrderDual.ofDual a.val.2) (y : B) :
    ∃ L : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat A, ∀ f x,
      L f x = schwartzBruhatStageRealization a e f (x,y) := by
  classical
  with_reducible refine (laurent_slice_pair a).elim fun b hbhk ↦ ?_
  obtain ⟨hb,hk⟩ := hbhk
  let c := b.elementary.some
  let h (f : SchwartzBruhatStage e) := laurent_stage_slice_mem a e b c hb hk U hu f y
  let j (f : SchwartzBruhatStage e) := (h f).choose
  have hj (f) (x) := (h f).choose_spec x
  have hinj : Injective (schwartzBruhatStageRealization b c) := fun s t he ↦
    schwartzBruhatStageInclusion_injective b c (Subtype.ext he)
  let J : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhatStage c :=
    { toFun := j
      map_add' := fun f g ↦ hinj (funext fun x ↦ ((hj (f+g) x).trans (congrFun ((schwartzBruhatStageRealization a e).map_add f g) (x,y))).trans
        ((congrArg₂ (· + ·) (hj f x) (hj g x)).symm.trans (congrFun ((schwartzBruhatStageRealization b c).map_add _ _) x).symm))
      map_smul' := fun z f ↦ hinj (funext fun x ↦ ((hj (z • f) x).trans (congrFun ((schwartzBruhatStageRealization a e).map_smul z f) (x,y))).trans
        ((congrArg (z • ·) (hj f x)).symm.trans (congrFun ((schwartzBruhatStageRealization b c).map_smul z _) x).symm)) }
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  have hcont : Continuous J := by
    apply continuous_toElementarySchwartz_of_eval J
    intro x
    obtain ⟨u,hu'⟩ := QuotientGroup.mk_surjective (c.equiv.symm (Multiplicative.ofAdd x))
    let L := (LinearMap.proj (u.val,y)).comp (schwartzBruhatStageRealization a e)
    refine ⟨⟨L,continuous_schwartzBruhatStage_eval a e (u.val,y)⟩,fun f ↦ ?_⟩
    have hh := hj f u.val
    have hh' := (schwartzBruhatStageRealization_apply b c (j f) u.val).trans (dite_eq_left u.property)
    replace hh := hh'.symm.trans hh
    exact hh.symm.trans (congrArg (j f) (congrArg Multiplicative.toAdd ((congrArg c.equiv hu').trans (c.equiv.apply_symm_apply _))))
  exact ⟨(⟨schwartzBruhatStageInclusion b c, continuous_schwartzBruhatStageInclusion b c⟩ :
    SchwartzBruhatStage c →L[ℂ] SchwartzBruhat A).comp ⟨J,hcont⟩,fun f x ↦ hj f x⟩

open Classical in
private theorem laurent_step_injective {I V : Type*} [PartialOrder I] [AddCommGroup V]
    (b : I →₀ V) (h : ∀ m : I, (∑ i ∈ b.support, if i ≤ m then b i else 0) = 0) : b = 0 := by
  classical
  by_contra hn
  obtain ⟨i,hi⟩ := Finset.exists_minimal (Finsupp.support_nonempty_iff.mpr hn)
  have hh := h i
  rw [Finset.sum_eq_single i (fun j hj hji ↦ ite_eq_right fun h ↦ hji (hi.eq_of_le hj h))
    (fun h ↦ False.elim (h hi.1)), ite_eq_left le_rfl] at hh
  exact (Finsupp.mem_support_iff.mp hi.1) hh

open Classical in
private theorem laurent_interp {I : Type*} [PartialOrder I] [Fintype I] :
    ∃ c : I → I → ℂ, ∀ j m : I, (∑ i, if i ≤ m then c j i else 0) = if m = j then 1 else 0 := by
  let L : (I → ℂ) →ₗ[ℂ] (I → ℂ) := LinearMap.pi fun m ↦ ∑ i : I,
    if i ≤ m then LinearMap.proj i else 0
  have hL (u : I → ℂ) (m : I) : L u m = ∑ i : I, if i ≤ m then u i else 0 := by
    change (∑ i : I, if i ≤ m then LinearMap.proj i else (0 : (I → ℂ) →ₗ[ℂ] ℂ)) u = _
    rw [LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; split <;> rfl
  have hi : Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro u hu
    let b := Finsupp.equivFunOnFinite.symm u
    have : b = 0 := laurent_step_injective b (fun m ↦ by
      have h := congrFun hu m
      rw [hL] at h
      refine Eq.trans (Finset.sum_subset (f := fun i ↦ if i ≤ m then b i else 0) (Finset.subset_univ b.support) ?_) ?_
      · intro i _ hn
        simp [Finsupp.notMem_support_iff.mp hn]
      · exact h)
    exact congrArg Finsupp.toFun this
  have hs := LinearMap.surjective_of_injective hi
  choose c hc using fun j : I ↦ hs (fun m ↦ if m = j then (1 : ℂ) else 0)
  exact ⟨c,fun j m ↦ (hL _ _).symm.trans (congrFun (hc j) m)⟩
open Classical TensorProduct in
private theorem laurent_tensor_step_injective {I V W : Type*} [PartialOrder I] [AddMonoid I]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (j : V →ₗ[ℂ] W) (hj : Injective j)
    (Q : (V ⊗[ℂ] AddMonoidAlgebra ℂ I) →ₗ[ℂ] (I → W))
    (hQ : ∀ v i m, Q (v ⊗ₜ[ℂ] AddMonoidAlgebra.single i 1) m = if i ≤ m then j v else 0) : Injective Q := by
  apply (injective_iff_map_eq_zero Q).mpr
  intro t ht
  let c := TensorProduct.equivFinsuppOfBasisRight (M := V) (AddMonoidAlgebra.basis I ℂ)
  obtain ⟨b,rfl⟩ := c.symm.surjective t
  suffices b = 0 by rw [this,map_zero]
  apply laurent_step_injective
  intro m
  apply hj
  rw [map_zero,map_sum]
  have hh := congrFun ht m
  change Q ((TensorProduct.equivFinsuppOfBasisRight _).symm b) m = 0 at hh
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,Finsupp.sum,map_sum,Finset.sum_apply] at hh
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) hh
  change j (if i ≤ m then b i else 0) = Q (b i ⊗ₜ[ℂ] AddMonoidAlgebra.single i 1) m
  rw [hQ]; split <;> simp

open Classical TensorProduct in
private theorem laurent_tensor_ext {I V W : Type*} [AddMonoid I]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {L L' : (V ⊗[ℂ] AddMonoidAlgebra ℂ I) →ₗ[ℂ] W}
    (h : ∀ v i, L (v ⊗ₜ[ℂ] AddMonoidAlgebra.single i 1) = L' (v ⊗ₜ[ℂ] AddMonoidAlgebra.single i 1)) : L = L' := by
  let c := TensorProduct.equivFinsuppOfBasisRight (M := V) (AddMonoidAlgebra.basis I ℂ)
  refine LinearMap.ext fun t ↦ ?_
  obtain ⟨b,rfl⟩ := c.symm.surjective t
  change L ((TensorProduct.equivFinsuppOfBasisRight _).symm b) = _
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,Finsupp.sum,map_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ h _ i

open Classical in
/-- On the finite exponent box, express each point indicator in the basis of upper-set
indicators. The same coefficients interpolate the samples outside the box by stabilization. -/
private theorem laurent_grid_lift {I E T V W : Type*} [SemilatticeInf I] [LocallyFiniteOrder I]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup T] [Module ℂ T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul ℂ T]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [AddCommGroup W] [Module ℂ W]
    (j : V →ₗ[ℂ] W) (B : I → V →L[ℂ] T) (Q : T →ₗ[ℂ] (I → W))
    (hQ : ∀ i v m, Q (B i v) m = if i ≤ m then j v else 0)
    (s : I → E →L[ℂ] V) (l u : I) (hlu : l ≤ u)
    (h0 : ∀ m, ¬ l ≤ m → ∀ f, s m f = 0)
    (hu : ∀ m, l ≤ m → ∀ f, s (m ⊓ u) f = s m f) :
    ∃ H : E →L[ℂ] T, ∀ f m, Q (H f) m = j (s m f) := by
  let K := Set.Icc l u
  let : Fintype K := inferInstanceAs (Fintype (Set.Icc l u))
  obtain ⟨c,hc⟩ := laurent_interp (I := K)
  let H : E →L[ℂ] T := ∑ k : K, ∑ i : K, c k i • (B i.val).comp (s k.val)
  refine ⟨H, fun f m ↦ ?_⟩
  have h (k : K) : (∑ i : K, c k i • Q (B i.val (s k.val f)) m) =
      (∑ i : K, if i.val ≤ m then c k i else 0) • j (s k.val f) := by
    rw [Finset.sum_smul]; apply Finset.sum_congr rfl
    intro i _; rw [hQ]; split <;> simp
  simp only [H,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,h]
  by_cases hm : l ≤ m
  · let t : K := ⟨m ⊓ u,le_inf hm hlu,inf_le_right⟩
    have he (k : K) : (∑ i : K, if i.val ≤ m then c k i else 0) = if t = k then 1 else 0 := by
      refine Eq.trans (Finset.sum_congr rfl (g := fun i : K ↦ if i ≤ t then c k i else 0) fun i _ ↦ if_congr ?_ rfl rfl) ?_
      · exact (le_inf_iff.trans (and_iff_left i.property.2)).symm
      · by_cases htk : t = k <;> simpa only [htk,ite_true,ite_false] using hc k t
    simp only [he,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact congrArg j (hu m hm f)
  · have he (i : K) : ¬ i.val ≤ m := fun hi ↦ hm (i.property.1.trans hi)
    simp [he,h0 m hm]

/-- If samples can be lifted continuously on each stage, injectivity of the sampling map
on the target makes the lifts compatible and gives a continuous lift on the whole space. -/
private theorem laurent_glue {G V W : Type*} [CommGroup G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [PolynormableSpace ℂ V] [AddCommGroup W] [Module ℂ W]
    (Q : V →ₗ[ℂ] W) (hi : Injective Q) (P : (G → ℂ) →ₗ[ℂ] W)
    (h : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
       ∃ H : SchwartzBruhatStage e →L[ℂ] V, ∀ s, Q (H s) = P (schwartzBruhatStageRealization a e s)) :
    ∃ H : SchwartzBruhat G →L[ℂ] V, ∀ f, Q (H f) = P f.val := by
  let c := LinearEquiv.ofInjective Q hi
  have hr : schwartzBruhatSubmodule G ≤ Q.range.comap P := by
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s,rfl⟩
    exact ⟨(h a e).choose s,(h a e).choose_spec s⟩
  let M : SchwartzBruhat G →ₗ[ℂ] V := c.symm.toLinearMap.comp
    ((P.comp (schwartzBruhatSubmodule G).subtype).codRestrict _ fun f ↦ hr f.property)
  have hM (f : SchwartzBruhat G) : Q (M f) = P f.val := congrArg Subtype.val (c.apply_symm_apply _)
  refine ⟨⟨M, laurent_cont_of_stages M (fun a e ↦ ?_)⟩,hM⟩
  exact (h a e).choose.continuous.congr fun s ↦ hi (((h a e).choose_spec s).trans (hM (schwartzBruhatStageInclusion a e s)).symm)

open Classical in
private theorem laurent_recover_equiv {G V X W : Type*} [CommGroup G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [PolynormableSpace ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (L : V →L[ℂ] X) (i : X →L[ℂ] SchwartzBruhat G) (P : (G → ℂ) →ₗ[ℂ] W)
    (Q : V →ₗ[ℂ] W) (hi : Injective Q) (hQ : ∀ t, Q t = P (i (L t)).val)
    (hsep : ∀ x : X, P (i x).val = 0 → x = 0)
    (h : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
       ∃ H : SchwartzBruhatStage e →L[ℂ] V, ∀ s, Q (H s) = P (schwartzBruhatStageRealization a e s)) :
    ∃ E : V ≃L[ℂ] X, ∀ t, E t = L t := by
  with_reducible refine (laurent_glue Q hi P h).elim fun H hH ↦ ?_
  let J := H.comp i
  have left (v : V) : J (L v) = v := hi ((hH _).trans (hQ v).symm)
  have right (x : X) : L (J x) = x := by
    apply sub_eq_zero.mp; apply hsep
    have he := (hQ (J x)).symm.trans (hH (i x))
    rw [map_sub]; change P ((i (L (J x))).val - (i x).val) = 0
    rwa [map_sub,sub_eq_zero]
  exact ⟨⟨LinearEquiv.ofLinearMap L.toLinearMap J.toLinearMap (LinearMap.ext right) (LinearMap.ext left),L.continuous,J.continuous⟩,fun _ ↦ rfl⟩

private theorem laurent_pow_zero (w : Places) (π : (L(w))ˣ)
    (hπ : Valuation.IsUniformizer (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val) :
    Tendsto (fun n : ℕ ↦ π.val ^ n) atTop (𝓝 0) := by
  apply Valued.tendsto_zero_pow_of_le_exp_neg_one
  exact (hπ.trans (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (w.valuedAdicCompletion_surjective F)))).le

private theorem laurent_lower {K : Type*} [NormedField K] (p : Kˣ)
    (hp : Tendsto (fun n : ℕ ↦ p.val ^ n) atTop (𝓝 0)) {s : Set K} (hs : IsCompact s) :
    ∃ l : ℤ, ∀ m : ℤ, (p ^ m).val ∈ s → l ≤ m := by
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs.isBounded
  have hn := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hp
  have hpos : 0 < ‖p.val‖ := norm_pos_iff.mpr p.ne_zero
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hpos).mpr hn)).eventually_gt_atTop r)
  refine ⟨-(N : ℤ),fun m hm ↦ ?_⟩
  by_contra! hh
  let n := (-m).toNat
  have he : m = -(n : ℤ) := by dsimp [n]; omega
  have hnN : n ≥ N := by omega
  have hle := Metric.mem_closedBall.mp (hr hm)
  rw [dist_zero_right, Units.val_zpow_eq_zpow_val,he,zpow_neg,zpow_natCast,norm_inv,norm_pow,← inv_pow] at hle
  exact (hN n hnN).not_ge hle

open Classical in
private theorem laurent_clip {D : Finset Places} (π : ∀ w : D, (L(w.val))ˣ)
    (hπ : ∀ w : D, Valuation.IsUniformizer (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val)
    (U : OpenSubgroup (Multiplicative (FinitePlaceProduct F D))) :
    ∃ r : D → ℤ, ∀ u : D → ℤ, r ≤ u → ∀ m : D → ℤ,
      Multiplicative.ofAdd (fun w ↦ (π w ^ ((m ⊓ u) w)).val - (π w ^ m w).val) ∈ U := by
  let H := U.toSubgroup.toAddSubgroup'
  have h (w : D) : Tendsto (fun n : ℕ ↦ Pi.single (M := fun v : D ↦ L(v.val)) w ((π w).val ^ n)) atTop (𝓝 (0 : FinitePlaceProduct F D)) := by
    have hc : Continuous (Pi.single (M := fun v : D ↦ L(v.val)) w) := continuous_single (A := fun w : D ↦ L(w.val)) w
    have hh := (hc.tendsto 0).comp (laurent_pow_zero _ (π w) (hπ w))
    rw [Pi.single_zero] at hh
    exact hh
  choose N hN using fun w : D ↦ eventually_atTop.mp ((h w) (show (H : Set _) ∈ 𝓝 (0 : FinitePlaceProduct F D) from U.mem_nhds_one))
  refine ⟨fun w ↦ N w, fun u hu m ↦ ?_⟩
  let x : FinitePlaceProduct F D := fun w ↦ (π w ^ ((m ⊓ u) w)).val - (π w ^ m w).val
  change x ∈ H
  rw [← Finset.univ_sum_single x]
  apply H.sum_mem; intro w _
  change Pi.single w ((π w ^ (min (m w) (u w))).val - (π w ^ m w).val) ∈ H
  by_cases hw : m w ≤ u w
  · simp [min_eq_left hw]
  · rw [min_eq_right (le_of_not_ge hw),Pi.single_sub]
    have hm (k : ℤ) (hk : (N w : ℤ) ≤ k) : Pi.single w ((π w ^ k).val) ∈ H := by
      lift k to ℕ using (by omega) with k
      simpa using hN w k (by exact_mod_cast hk)
    exact H.sub_mem (hm _ (hu w)) (hm _ ((hu w).trans (le_of_not_ge hw)))

/-- Bound the projection of the support subgroup by compact generation. An open period
subgroup in the new variables then gives a uniform upper cutoff for all power samples. -/
private theorem laurent_stage_bounds {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] (D : Finset Places)
    (π : ∀ w : D, (L(w.val))ˣ) (hπ : ∀ w : D, Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val)
    (a : BruhatStructuralPair (A × Multiplicative (FinitePlaceProduct F D)))
    (e : ElementaryLCAPresentation a.quotient) :
    ∃ (U : OpenSubgroup (Multiplicative (FinitePlaceProduct F D))) (l u : D → ℤ),
      l ≤ u ∧ (∀ y ∈ U, ((1:A),y) ∈ OrderDual.ofDual a.val.2) ∧
      ∀ (s : SchwartzBruhatStage e) (m : D → ℤ) (x : A),
        (¬ l ≤ m → schwartzBruhatStageRealization a e s (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val)) = 0) ∧
        schwartzBruhatStageRealization a e s (x,Multiplicative.ofAdd (fun w ↦ (π w ^ ((m ⊓ u) w)).val)) =
          schwartzBruhatStageRealization a e s (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val)) := by
  classical
  let B := Multiplicative (FinitePlaceProduct F D)
  let : T2Space B := inferInstanceAs (T2Space (FinitePlaceProduct F D))
  let (w : D) : ProperSpace (L(w.val)) := properSpace_adicCompletion w.val
  let : LocallyCompactSpace B := inferInstanceAs (LocallyCompactSpace (FinitePlaceProduct F D))
  with_reducible refine (stage_kernel_contains_small_powers a e).elim fun W hh ↦ ?_
  have hW := hh.1
  have hk := hh.2
  have hpre : (fun y : B ↦ ((1:A),y)) ⁻¹' W ∈ 𝓝 1 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hW
  with_reducible refine (finitePlaceProduct_smallSubgroups F D hpre).elim fun V hv ↦ ?_
  obtain ⟨hV,hVW⟩ := hv
  let U : OpenSubgroup B := ⟨V,hV⟩
  have hu (y : B) (hy : y ∈ U) : ((1:A),y) ∈ OrderDual.ofDual a.val.2 :=
    hk _ fun k ↦ by simpa using hVW (V.pow_mem hy k)
  with_reducible refine (laurent_clip π hπ U).elim fun r hr ↦ ?_
  have hcg := a.property.2.1
  unfold IsCompactlyGeneratedGroup at hcg
  with_reducible refine hcg.elim fun C hCgen ↦ ?_
  have hCc := hCgen.2.1
  have hC := hCgen.2.2
  let p : a.val.1 →* B := (MonoidHom.snd A B).comp a.val.1.subtype
  with_reducible refine (finitePlaceProduct_mem_compactSubgroup F D (hCc.image (continuous_snd.comp continuous_subtype_val) : IsCompact (p '' C))).elim fun H hhH ↦ ?_
  have hH := hhH.1
  have hCH := hhH.2
  have hb : ⊤ ≤ H.comap p := hC ▸ ((H.comap p).closure_le.mpr (fun z hz ↦ hCH (mem_image_of_mem p hz)))
  have hc (w : D) : IsCompact ((fun y : B ↦ y.toAdd w) '' (H : Set B)) := hH.image ((continuous_apply w).comp continuous_toAdd)
  choose l hl using fun w : D ↦ laurent_lower (π w) (laurent_pow_zero w.val (π w) (hπ w)) (hc w)
  let u := l ⊔ r
  refine ⟨U,l,u,le_sup_left,hu,fun s m x ↦ ⟨fun hm ↦ ?_,?_⟩⟩
  · rw [schwartzBruhatStageRealization_apply]; apply dite_eq_right
    intro hx; apply hm
    have hp := hb (Subgroup.mem_top (x := (⟨_,hx⟩ : a.val.1)))
    exact fun w ↦ hl w _ ⟨_,hp,rfl⟩
  · have hk' := hu _ (hr u le_sup_right m)
    have he := stage_realization_mul_kernel a e s hk' (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val))
    refine Eq.trans (congrArg (schwartzBruhatStageRealization a e s) (Prod.ext (one_mul x).symm ?_)) he
    exact funext fun w ↦ (sub_add_cancel _ _).symm

private theorem laurent_orbit (w : Places) (π : (L(w))ˣ)
    (hπ : Valuation.IsUniformizer (Valued.v : Valuation (L(w)) (WithZero (Multiplicative ℤ))) π.val)
    {y : L(w)} (hy : y ≠ 0) : ∃ (u : (L(w))ˣ) (m : ℤ), u.val ∈ O(w) ∧ (u⁻¹).val ∈ O(w) ∧
      y = u.val * (π ^ m).val := by
  let v : Valuation (L(w)) (WithZero (Multiplicative ℤ)) := Valued.v
  have hp : v π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective (w.valuedAdicCompletion_surjective F)))
  let m := -(v y).log
  have hpow : v (π ^ m).val = v y := by
    rw [Units.val_zpow_eq_zpow_val,map_zpow₀,hp,← WithZero.exp_zsmul]
    simpa [m] using WithZero.exp_log ((map_ne_zero v).mpr hy)
  let u := Units.mk0 y hy / π ^ m
  have hv : v u.val = 1 := by rw [show u.val = y / (π ^ m).val from Units.val_div_eq_div_val _ _,map_div₀,hpow,div_self ((map_ne_zero v).mpr hy)]
  refine ⟨u,m,(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hv.le,?_,?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; rw [Units.val_inv_eq_inv_val,map_inv₀,show Valued.v u.val = 1 from hv,inv_one]
  · exact (congrArg Units.val (div_mul_cancel (Units.mk0 y hy) (π ^ m))).symm

open Classical in
private theorem laurent_units_extend {S T : Finset Places} (u : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (hu : ∀ w, (u w).val ∈ O(w.val) ∧ ((u w)⁻¹).val ∈ O(w.val)) :
    ∃ g : relativeIntegralIdeleUnits F S T, g.val.val.1 = 1 ∧
      (∀ w : T, w.val ∈ S → g.val.val.2 w = 1) ∧
      ∀ w : ↥(T \ S), g.val.val.2 ⟨w.val,(Finset.mem_sdiff.mp w.property).1⟩ = (u w).val := by
  let t (w : T) : (L(w.val))ˣ := if h : w.val ∈ S then 1 else u ⟨w.val,Finset.mem_sdiff.mpr ⟨w.property,h⟩⟩
  let g : (SAdeleRing F T)ˣ := ⟨(1,fun w ↦ (t w).val),(1,fun w ↦ ((t w)⁻¹).val),
    Prod.ext (one_mul _) (funext fun w ↦ (t w).val_inv),Prod.ext (one_mul _) (funext fun w ↦ (t w).inv_val)⟩
  have hone (w : T) (hw : w.val ∈ S) : g.val.2 w = 1 := congrArg Units.val (dite_eq_left (α := (L(w.val))ˣ) hw : t w = 1)
  have hnew (w : T) (hw : w.val ∉ S) : t w = u ⟨w.val,Finset.mem_sdiff.mpr ⟨w.property,hw⟩⟩ := dite_eq_right hw
  have hmem := (mem_relativeIntegralIdeleUnits_iff (S := S) g).mpr ⟨rfl,hone,fun w hw ↦ by
    change (t w).val ∈ _ ∧ ((t w)⁻¹).val ∈ _
    rw [hnew w hw]; exact hu ⟨w.val,Finset.mem_sdiff.mpr ⟨w.property,hw⟩⟩⟩
  exact ⟨⟨g,hmem⟩,rfl,hone,fun w ↦ congrArg Units.val (hnew _ (Finset.mem_sdiff.mp w.property).2)⟩

open Classical in
/-- Integral units move every tuple of nonzero new coordinates to a tuple of uniformizer
powers. Continuity recovers the slices where one or more coordinates vanish. -/
private theorem laurent_sample_separates {S T : Finset Places} (hST : S ⊆ T)
    (d : Multiplicative (SAdeleRing F T) ≃ₜ* Multiplicative (SAdeleRing F S) × Multiplicative (FinitePlaceProduct F (T \ S)))
    (hd : ∀ x : SAdeleRing F T, d (Multiplicative.ofAdd x) =
      (Multiplicative.ofAdd (x.1,fun w : S ↦ x.2 ⟨w.val,hST w.property⟩),
       Multiplicative.ofAdd (fun w : ↥(T \ S) ↦ x.2 ⟨w.val,(Finset.mem_sdiff.mp w.property).1⟩)))
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ) (hπ : ∀ w : ↥(T \ S), Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F T)))
    (hf : f ∈ Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
      (relativeIntegralIdeleUnits F S T).subtype))
    (hs : ∀ x : Multiplicative (SAdeleRing F S), ∀ m : ↥(T \ S) → ℤ,
      f (d.symm (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val))) = 0) : f = 0 := by
  let D := T \ S
  have hnon (x : Multiplicative (SAdeleRing F S)) (y : FinitePlaceProduct F D) (hy : ∀ w, y w ≠ 0) :
      f (d.symm (x,Multiplicative.ofAdd y)) = 0 := by
    choose u m hu1 hu2 he using fun w : D ↦ laurent_orbit w.val (π w) (hπ w) (hy w)
    with_reducible refine (laurent_units_extend u (fun w ↦ ⟨hu1 w,hu2 w⟩)).elim fun g hh ↦ ?_
    let z := d.symm (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val))
    have hz := (hd z.toAdd).symm.trans (d.apply_symm_apply _)
    let v : Multiplicative (SAdeleRing F T) := Multiplicative.ofAdd (g.val.val * z.toAdd)
    have hv : d v = (x,Multiplicative.ofAdd y) := by
      refine (hd v.toAdd).trans (Prod.ext ?_ ?_)
      · have hz1 := congrArg Prod.fst hz
        refine Eq.trans ?_ hz1
        apply Multiplicative.ext; apply Prod.ext
        · exact (congrArg (· * z.toAdd.1) hh.1).trans (one_mul _)
        · exact funext fun w ↦ (congrArg (· * _) (hh.2.1 ⟨w.val,hST w.property⟩ w.property)).trans (one_mul _)
      · refine funext fun w ↦ ?_
        refine Eq.trans (congrArg₂ (· * ·) (hh.2.2 w) (congrFun (congrArg (fun p ↦ p.2.toAdd) hz) w)) (he w).symm
    have hg := congrArg (fun k : SchwartzBruhat (Multiplicative (SAdeleRing F T)) ↦ k z) (hf g⁻¹)
    change f (Multiplicative.ofAdd ((g.val⁻¹)⁻¹.val * z.toAdd)) = f z at hg
    rw [inv_inv] at hg
    exact (congrArg f ((congrArg d.symm hv).symm.trans (d.symm_apply_apply _))).trans (hg.trans (hs x m))
  apply Subtype.ext; funext z
  let x := (d z).1
  let y := (d z).2.toAdd
  let yn (n : ℕ) : FinitePlaceProduct F D := fun w ↦ if y w = 0 then (π w).val ^ n else y w
  have hlim : Tendsto yn atTop (𝓝 y) := by
    apply tendsto_pi_nhds.mpr; intro w
    by_cases hw : y w = 0
    · simpa only [yn,hw,ite_true] using laurent_pow_zero w.val (π w) (hπ w)
    · simpa only [yn,hw,ite_false] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ y w) atTop (𝓝 (y w)))
  have hn (n : ℕ) : ∀ w, yn n w ≠ 0 := fun w ↦ by dsimp only [yn]; split <;> simp_all only [ne_eq,pow_ne_zero,Units.ne_zero,not_false_eq_true]
  have hc : Continuous (fun v : FinitePlaceProduct F D ↦ f (d.symm (x,Multiplicative.ofAdd v))) :=
    (schwartzBruhat_continuous f).comp (d.symm.continuous.comp (continuous_const.prodMk continuous_ofAdd))
  have hzero := tendsto_nhds_unique ((hc.tendsto y).comp hlim) (tendsto_const_nhds.congr (fun n ↦ (hnon x (yn n) (hn n)).symm))
  exact (congrArg f (d.symm_apply_apply z)).symm.trans hzero

open Classical in
private theorem laurent_stage_interp {A Z : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [IsTopologicalAddGroup Z] [ContinuousConstSMul ℂ Z] (D : Finset Places)
    (π : ∀ w : D, (L(w.val))ˣ) (hπ : ∀ w : D, Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val)
    (B : (D → ℤ) → SchwartzBruhat A →L[ℂ] Z) (Q : Z →ₗ[ℂ] ((D → ℤ) → A → ℂ))
    (hQ : ∀ i v m, Q (B i v) m = if i ≤ m then v.val else 0)
    (a : BruhatStructuralPair (A × Multiplicative (FinitePlaceProduct F D))) (e : ElementaryLCAPresentation a.quotient) :
    ∃ H : SchwartzBruhatStage e →L[ℂ] Z, ∀ s m x,
      Q (H s) m x = schwartzBruhatStageRealization a e s (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val)) := by
  let (w : D) : ProperSpace (L(w.val)) := properSpace_adicCompletion w.val
  let : T2Space (Multiplicative (FinitePlaceProduct F D)) := inferInstanceAs (T2Space (FinitePlaceProduct F D))
  let : LocallyCompactSpace (Multiplicative (FinitePlaceProduct F D)) := inferInstanceAs (LocallyCompactSpace (FinitePlaceProduct F D))
  with_reducible refine (laurent_stage_bounds D π hπ a e).elim fun U hU ↦ hU.elim fun l hl ↦ hl.elim fun u hu ↦ ?_
  have h (m : D → ℤ) := laurent_stage_slice_clm a e U hu.2.1 (Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val))
  let s m := (h m).choose
  have hs m := (h m).choose_spec
  let j := (schwartzBruhatSubmodule A).subtype
  have hz (m) (hm : ¬ l ≤ m) (f) : s m f = 0 := Subtype.ext (funext fun x ↦ ((hs m f x).trans ((hu.2.2 f m x).1 hm)))
  have hc (m) (_ : l ≤ m) (f) : s (m ⊓ u) f = s m f := Subtype.ext (funext fun x ↦
    ((hs _ f x).trans (hu.2.2 f m x).2).trans (hs _ f x).symm)
  have hgrid := laurent_grid_lift (V := SchwartzBruhat A) j B Q (fun i v m ↦ (hQ i v m).trans (by
    by_cases hh : i ≤ m <;> simp only [hh, ite_true, ite_false]; rfl)) s l u hu.1 hz hc
  with_reducible refine hgrid.elim fun H hH ↦ ?_
  exact ⟨H,fun f m x ↦ (congrFun (hH f m) x).trans (hs m f x)⟩

open Classical in
private theorem laurent_ball_step (D : Finset Places) (π : ∀ w : D, (L(w.val))ˣ)
    (hπ : ∀ w : D, Valuation.IsUniformizer (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val)
    (a m : D → ℤ) : (∏ w, finitePlaceBallIndicator w.val (π w) (a w) (π w ^ m w).val) = if a ≤ m then 1 else 0 := by
  by_cases h : a ≤ m
  · rw [ite_eq_left h]; exact Finset.prod_eq_one fun i _ ↦ (finitePlaceBallIndicator_at_power i.val _ (hπ i) _ _).trans (ite_eq_left (h i))
  · rw [ite_eq_right h]; obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((finitePlaceBallIndicator_at_power i.val _ (hπ i) _ _).trans (ite_eq_right hi))

private theorem laurent_tmul_clm {X I : Type*} [AddMonoid I] [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X] (i : I) :
    ∃ B : X →L[ℂ] InductiveTensor X (FinestLocallyConvex (AddMonoidAlgebra ℂ I)),
      ∀ x, B x = x ⊗ₜ[ℂ] AddMonoidAlgebra.single i 1 := by
  let P := FinestLocallyConvex (AddMonoidAlgebra ℂ I)
  let : T2Space P := finestLocallyConvex_t2 _
  let Z := InductiveTensor X P
  let v : P := AddMonoidAlgebra.single i 1
  exact ⟨⟨(TensorProduct.mk ℂ X P).flip v, ((continuous_inductiveTensor_iff (E := X) (F := P) (LinearMap.id : Z →ₗ[ℂ] Z)).mp continuous_id).2 v⟩,fun _ ↦ rfl⟩

private theorem laurent_pull_submodule {G C : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C] (d : C ≃ₜ* G)
    (V : Submodule ℂ (SchwartzBruhat C)) :
    ∃ i : V →L[ℂ] SchwartzBruhat G, ∀ f x, i f x = f.val (d.symm x) := by
  let E := schwartzBruhatPullbackEquiv d.symm
  exact ⟨E.toContinuousLinearMap.comp V.subtypeL,fun _ _ ↦ rfl⟩

open Classical in
private theorem laurent_sample_equiv {A V : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A] [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (D : Finset Places) (π : ∀ w : D, (L(w.val))ˣ) (hπ : ∀ w : D, Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val)
    (L : InductiveTensor (SchwartzBruhat A) (FinestLocallyConvex (AddMonoidAlgebra ℂ (D → ℤ))) →L[ℂ] V)
    (i : V →L[ℂ] SchwartzBruhat (A × Multiplicative (FinitePlaceProduct F D)))
    (hstep : ∀ (f : SchwartzBruhat A) (a m : D → ℤ) (x : A), i (L (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1))
        (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val)) = if a ≤ m then f x else 0)
    (hsepar : ∀ v : V, (∀ (x : A) (m : D → ℤ), i v (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val)) = 0) → v = 0) :
    ∃ E : InductiveTensor (SchwartzBruhat A) (FinestLocallyConvex (AddMonoidAlgebra ℂ (D → ℤ))) ≃L[ℂ] V, ∀ t, E t = L t := by
  let X := SchwartzBruhat A
  let I := ↥D → ℤ
  let G := A × Multiplicative (FinitePlaceProduct F D)
  let Z := InductiveTensor X (FinestLocallyConvex (AddMonoidAlgebra ℂ I))
  let : T2Space X := laurent_schwartz_t2 A
  let : T2Space (FinestLocallyConvex (AddMonoidAlgebra ℂ I)) := finestLocallyConvex_t2 _
  let : IsTopologicalAddGroup Z := PolynormableSpace.isTopologicalAddGroup ℂ Z
  let : ContinuousSMul ℂ Z := (PolynormableSpace.withSeminorms ℂ Z).continuousSMul
  let y (m : I) : Multiplicative (FinitePlaceProduct F D) := Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val)
  let P : (G → ℂ) →ₗ[ℂ] (I → A → ℂ) := LinearMap.pi fun m ↦ LinearMap.funLeft ℂ ℂ (fun x ↦ (x,y m))
  let Q : Z →ₗ[ℂ] (I → A → ℂ) := P.comp (((schwartzBruhatSubmodule G).subtype.comp i.toLinearMap).comp L.toLinearMap)
  have hQ (f : X) (a m : I) : Q (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1) m = if a ≤ m then f.val else 0 := by
    funext x
    exact (hstep f a m x).trans (by by_cases h : a ≤ m <;> simp only [h, ite_true, ite_false]; rfl)
  have hi : Injective Q := laurent_tensor_step_injective (V := X) (schwartzBruhatSubmodule A).subtype
    Subtype.val_injective Q (fun f a m ↦ (hQ f a m).trans (by
      by_cases h : a ≤ m <;> simp only [h, ite_true, ite_false]; rfl))
  have hsep (v : V) (hv : P (i v).val = 0) : v = 0 := hsepar v fun x m ↦ congrFun (congrFun hv m) x
  let b (a : I) := laurent_tmul_clm (X := X) a
  let B (a : I) := (b a).choose
  have hB (a : I) (f : X) := (b a).choose_spec f
  have hs (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      ∃ H : SchwartzBruhatStage e →L[ℂ] Z, ∀ s, Q (H s) = P (schwartzBruhatStageRealization a e s) := by
    have hh := laurent_stage_interp D π hπ B Q (fun t f m ↦ (congrArg (fun z ↦ Q z m) (hB t f)).trans (hQ f t m)) a e
    with_reducible refine hh.elim fun H hH ↦ ?_
    exact ⟨H,fun s ↦ funext fun m ↦ funext fun x ↦ hH s m x⟩
  have hEquiv := laurent_recover_equiv L i P Q hi (fun _ ↦ rfl) hsep hs
  exact hEquiv
open Classical in
private theorem laurent_sample_formula (hST : S ⊆ T)
    (d : Multiplicative (SAdeleRing F T) ≃ₜ* Multiplicative (SAdeleRing F S) × Multiplicative (FinitePlaceProduct F (T \ S)))
    (hd : ∀ x : SAdeleRing F T, d (Multiplicative.ofAdd x) =
      (Multiplicative.ofAdd (x.1,fun w : S ↦ x.2 ⟨w.val,hST w.property⟩),
       Multiplicative.ofAdd (fun w : ↥(T \ S) ↦ x.2 ⟨w.val,(Finset.mem_sdiff.mp w.property).1⟩)))
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ) (hπ : ∀ w : ↥(T \ S), Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val)
    (f : Multiplicative (SAdeleRing F S) → ℂ) (g : Multiplicative (SAdeleRing F T) → ℂ) (a : ↥(T \ S) → ℤ)
    (hg : ∀ x : SAdeleRing F T, g (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd (x.1,fun w : S ↦ x.2 ⟨w.val,hST w.property⟩)) *
      ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w) (x.2 ⟨w.val,(Finset.mem_sdiff.mp w.property).1⟩))
    (m : ↥(T \ S) → ℤ) (x : Multiplicative (SAdeleRing F S)) :
    g (d.symm (x,Multiplicative.ofAdd (fun w ↦ (π w ^ m w).val))) = if a ≤ m then f x else 0 := by
  let y := Multiplicative.ofAdd (fun w : ↥(T \ S) ↦ (π w ^ m w).val)
  let z := d.symm (x,y)
  have hz := (hd z.toAdd).symm.trans (d.apply_symm_apply _)
  have hz1 := congrArg Prod.fst hz
  have hz2 := congrArg (fun p ↦ p.2.toAdd) hz
  refine Eq.trans (hg z.toAdd) ?_
  have he := Finset.prod_congr (s₁ := Finset.univ) rfl (fun (w : ↥(T \ S)) _ ↦
    congrArg (finitePlaceBallIndicator w.val (π w) (a w)) (congrFun hz2 w))
  refine (congrArg₂ (· * ·) (congrArg f hz1) (he.trans (laurent_ball_step _ π hπ a m))).trans ?_
  by_cases h : a ≤ m <;> simp [h]

open Classical in
private theorem laurent_final (hST : S ⊆ T)
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (hπ : ∀ w : ↥(T \ S), Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val) :
    ∀ (L : InductiveTensor ℬ(SAdeleRing F S) (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) →L[ℂ]
      (Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
        (relativeIntegralIdeleUnits F S T).subtype))),
    (∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
      (L (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
        f (Multiplicative.ofAdd (x.1,fun w : S ↦ x.2 ⟨w.val,hST w.property⟩)) *
          ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w) (x.2 ⟨w.val,(Finset.mem_sdiff.mp w.property).1⟩)) →
    ∃ E : InductiveTensor ℬ(SAdeleRing F S) (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) ≃L[ℂ]
      (Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
        (relativeIntegralIdeleUnits F S T).subtype)), ∀ t, E t = L t := by
  intro L hL
  let (w : Places) : ProperSpace (L(w)) := properSpace_adicCompletion w
  let : LocallyCompactSpace (InfiniteAdeleRing F) := InfiniteAdeleRing.locallyCompactSpace F
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FinitePlaceProduct F S))
  let : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let : T2Space (Multiplicative (SAdeleRing F S)) := inferInstanceAs (T2Space (InfiniteAdeleRing F × FinitePlaceProduct F S))
  with_reducible refine (laurent_split (F := F) hST).elim fun d hd ↦ ?_
  let V := Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
      (relativeIntegralIdeleUnits F S T).subtype)
  have hh := laurent_pull_submodule d V
  with_reducible refine hh.elim fun i hEval ↦ ?_
  with_reducible refine laurent_sample_equiv (V := V) (A := Multiplicative (SAdeleRing F S)) (T \ S) π hπ L i ?_ ?_
  · intro f a m x
    with_reducible refine (hEval _ _).trans ?_
    have he := laurent_sample_formula hST d hd π hπ f.val _ a (hL f a) m x
    with_reducible refine he.trans ?_
    by_cases ham : a ≤ m <;> simp only [ham,ite_true,ite_false]
  · intro v hv
    have hf := laurent_sample_separates hST d hd π hπ v.val v.property
    have hzero : (0 : V).val = 0 := rfl
    with_reducible refine Subtype.ext ((hf ?_).trans hzero.symm)
    intro x m
    with_reducible exact (hEval v (x,Multiplicative.ofAdd (fun w : ↥(T \ S) ↦ (π w ^ m w).val))).symm.trans (hv x m)

private theorem laurent_unique {I X V Y : Type*} [AddMonoid I] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace X] [TopologicalSpace V]
    (L : InductiveTensor X (FinestLocallyConvex (AddMonoidAlgebra ℂ I)) →L[ℂ] V)
    (j : V → Y → ℂ) (hj : Injective j) (p : X → I → Y → ℂ)
    (hL : ∀ f a x, j (L (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)) x = p f a x)
    (E : InductiveTensor X (FinestLocallyConvex (AddMonoidAlgebra ℂ I)) ≃L[ℂ] V) (hE : ∀ t, E t = L t) :
    ∃! e : InductiveTensor X (FinestLocallyConvex (AddMonoidAlgebra ℂ I)) ≃L[ℂ] V,
      ∀ f a x, j (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)) x = p f a x := by
  refine ⟨E,fun f a x ↦ (congrArg (fun v ↦ j v x) (hE _)).trans (hL f a x),fun D hD ↦ ?_⟩
  apply ContinuousLinearEquiv.ext
  have hh : D.toLinearEquiv.toLinearMap = E.toLinearEquiv.toLinearMap := by
    apply laurent_tensor_ext (V := X) (I := I)
    intro f a
    exact (hj (funext fun x ↦ (hD f a x).trans (hL f a x).symm)).trans (hE _).symm
  exact funext (LinearMap.congr_fun hh)

end LaurentProof

open Classical in
/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5)–(6.1.2.6), p. 289.
The larger-stage relative unit invariants have a unique linear topological identification
with the S-local test space tensored with the multivariate Laurent polynomials.
Each pure tensor with a monomial multiplies the old test function by the indicated local balls.
Deviation: The tensor topology is inductive, following Corollary 2.1.4.2 as formalized. -/
theorem sLocalSchwartz_invariants_laurent_equiv (hST : S ⊂ T)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (π : ∀ w : ↥(T \ S), (L(w.val))ˣ)
    (_hπ : ∀ w : ↥(T \ S), Valuation.IsUniformizer
      (Valued.v : Valuation (L(w.val)) (WithZero (Multiplicative ℤ))) (π w).val) :
    ∃! e : InductiveTensor ℬ(SAdeleRing F S)
        (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) ≃L[ℂ]
        (Representation.invariants <| (schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
          (relativeIntegralIdeleUnits F S T).subtype),
      ∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
        (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST.le w.property⟩)) *
            ∏ w : ↥(T \ S), finitePlaceBallIndicator w.val (π w) (a w)
              (x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) := by
  with_reducible refine (laurent_forward (F := F) hST.le π).elim fun L hL ↦ ?_
  have he := laurent_final hST.le π _hπ L hL
  with_reducible refine he.elim fun E hE ↦ ?_
  let V := Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
      (relativeIntegralIdeleUnits F S T).subtype)
  let j := fun (v : V) (x : SAdeleRing F T) ↦ v.val (Multiplicative.ofAdd x)
  have hj : Injective j := fun v w h ↦ Subtype.ext (Subtype.ext (funext fun x ↦ congrFun h x.toAdd))
  with_reducible exact laurent_unique (I := ↥(T \ S) → ℤ) (X := ℬ(SAdeleRing F S)) (V := V) L j hj _ hL E hE



end RelativeLaurent

section Averaging

-- These Borel structures agree with the local instances in Appendix A.3.
local instance instLocalUnitMeasurableSpaceCh06Sec1 (w : Places) :
    MeasurableSpace (L(w))ˣ := borel _

local notation "μ(" w ")" => finiteLocalMultiplicativeTamagawaMeasure F w

private theorem unitsMass_ne_top (w : Places) :
    μ(w) (U(w) : Set (L(w))ˣ) ≠ ⊤ := by
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits F w, ne_eq, ENNReal.inv_eq_top,
    ENNReal.ofReal_eq_zero, not_le]
  exact Real.sqrt_pos.2
    (pow_pos (Nat.cast_pos.2 (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm w))) _)

private theorem units_isCompact (w : Places) : IsCompact (U(w) : Set (L(w))ˣ) :=
  Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w))

private theorem units_isOpen (w : Places) : IsOpen (U(w) : Set (L(w))ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

private instance unitsRestrict_isFinite (w : Places) :
    IsFiniteMeasure ((μ(w)).restrict (U(w) : Set (L(w))ˣ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (unitsMass_ne_top w).lt_top⟩

private local instance instProperSpaceCh06Sec1 (w : Places) : ProperSpace (L(w)) :=
  properSpace_adicCompletion w
private local instance instSecondCountableUnitsCh06Sec1 (w : Places) :
    SecondCountableTopology (L(w))ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance instBorelUnitsCh06Sec1 (w : Places) : BorelSpace (L(w))ˣ := ⟨rfl⟩

/-- Paper: Lemma 6.1.2.4(1), p. 291.
The span of integer-unit translation differences is closed.
Consequently the algebraic and continuous coinvariant quotients use the same relations.
Deviation: The closure equality states both conclusions on the relation submodule. -/
theorem finitePlaceSchwartz_unitRelations_closure_eq (w : Places) :
    (Representation.Coinvariants.ker (ρ(w))).topologicalClosure =
      Representation.Coinvariants.ker (ρ(w)) := by
  apply IsClosed.submodule_topologicalClosure_eq
  exact (congrArg (fun t ↦ @IsClosed ℬᵥ(w) t (Representation.Coinvariants.ker (ρ(w)) : Set ℬᵥ(w)))
    (finitePlaceSchwartz_finestTopology (F := F) w)).mpr
    (finestLocallyConvex_submodule_isClosed (E := schwartzBruhatSubmodule (Multiplicative (L(w))))
      (Representation.Coinvariants.ker (ρ(w))))

/-- Paper: (6.1.2.14), p. 292.
Averaging a local test function evaluates it along the multiplicative orbit and integrates
over the integer units against the local multiplicative Tamagawa measure. -/
def finitePlaceUnitAverage (w : Places) (f : ℬᵥ(w)) (x : L(w)) : ℂ :=
  ∫ u : (L(w))ˣ, f (Multiplicative.ofAdd (x * u.val)) ∂((μ(w)).restrict (U(w)))

/-- Paper: (6.1.2.14), p. 292.
The orbit integral at zero is the value at zero times the Tamagawa mass of the integer units. -/
theorem finitePlaceUnitAverage_zero (w : Places) (f : ℬᵥ(w)) :
    finitePlaceUnitAverage w f 0 =
      ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ) *
        f (Multiplicative.ofAdd 0) := by
  unfold finitePlaceUnitAverage
  simp only [zero_mul, integral_const]
  rw [Complex.real_smul, Measure.real, Measure.restrict_apply_univ]

/-- Paper: (6.1.2.14), p. 292.
Each integrand of the local averaging formula is integrable on the integer units. -/
theorem finitePlaceUnitAverage_integrable (w : Places) (f : ℬᵥ(w)) (x : L(w)) :
    IntegrableOn (fun u : (L(w))ˣ ↦ f (Multiplicative.ofAdd (x * u.val)))
      (U(w) : Set (L(w))ˣ) (μ(w)) := by
  have hc : Continuous (fun u : (L(w))ˣ ↦ f (Multiplicative.ofAdd (x * u.val))) :=
    (schwartzBruhat_continuous f).comp
      (continuous_ofAdd.comp (continuous_const.mul Units.continuous_val))
  obtain ⟨C, hC⟩ := (units_isCompact w).exists_bound_of_continuousOn hc.continuousOn
  exact Integrable.of_bound hc.aestronglyMeasurable C
    ((ae_restrict_iff' (units_isOpen w).measurableSet).2 (Filter.Eventually.of_forall hC))


/-- Paper: Lemma 6.1.2.4(2), p. 292.
A test function averages to zero exactly when it belongs to the span of unit
translation differences. -/
theorem finitePlaceUnitAverage_eq_zero_iff (w : Places) (f : ℬᵥ(w)) :
    (∀ x, finitePlaceUnitAverage w f x = 0) ↔
      f ∈ Representation.Coinvariants.ker (ρ(w)) := by sorry

-- TODO(paper-gap): The proof on p. 292 identifies multiplicative unit averaging
-- with additive convolution and deduces vanishing of the function from unramified
-- Mellin values. For the indicator of the integer ring at the trivial character,
-- the shell integrals in (6.1.2.17) all have the same positive mass. A nonzero
-- eigendistribution annihilates every unit difference only for unramified weight.
-- The kernel assertion follows by averaging the finite unit orbit of each test function.

private theorem finitePlaceUnitAverage_coinvariants_equiv_restrict {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (H : Subgroup G) (hH : MeasurableSet (H : Set G)) (a : G) (ha : a ∈ H) (φ : G → ℂ) :
    ∫ u in (H : Set G), φ (a * u) ∂μ = ∫ u in (H : Set G), φ u ∂μ := by
  classical
  rw [← integral_indicator hH, ← integral_indicator hH,
    ← integral_mul_left_eq_self (μ := μ) ((H : Set G).indicator φ) a]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ H <;> simp [Set.indicator, hu, H.mul_mem_cancel_left ha]

private theorem finitePlaceUnitAverage_coinvariants_equiv_translate (w : Places)
    (g : U(w)) (f : ℬᵥ(w)) (x : L(w)) :
    finitePlaceUnitAverage w ((ρ(w)) g f) x = finitePlaceUnitAverage w f x := by
  classical
  let : (μ(w)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure w
  let φ (u : (L(w))ˣ) := f (Multiplicative.ofAdd (x * u.val))
  let a : (L(w))ˣ := ↑(g⁻¹ : U(w))
  have ha : a ∈ U(w) := (g⁻¹ : U(w)).property
  have hφ (u : (L(w))ˣ) : ((ρ(w)) g f) (Multiplicative.ofAdd (x * u.val)) = φ (a * u) := by
    change f (Multiplicative.ofAdd (a.val * (x * u.val))) = f (Multiplicative.ofAdd (x * (a.val * u.val)))
    rw [mul_left_comm]
  unfold finitePlaceUnitAverage
  simp_rw [hφ]
  exact finitePlaceUnitAverage_coinvariants_equiv_restrict (μ(w)) (U(w))
    (units_isOpen w).measurableSet a ha φ

private theorem finitePlaceUnitAverage_coinvariants_equiv_lift (w : Places) (x : L(w)) :
    ∃ l : (ℬᵥ(w) ⧸ Representation.Coinvariants.ker (ρ(w))) →ₗ[ℂ] ℂ,
      ∀ f, l ((Representation.Coinvariants.ker (ρ(w))).mkQ f) = finitePlaceUnitAverage w f x := by
  let a : ℬᵥ(w) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ finitePlaceUnitAverage w f x
      map_add' := fun f g ↦ integral_add (finitePlaceUnitAverage_integrable w f x)
        (finitePlaceUnitAverage_integrable w g x)
      map_smul' := fun c f ↦ integral_smul c _ }
  refine ⟨Representation.Coinvariants.lift (ρ(w)) a (fun g ↦ LinearMap.ext fun f ↦ ?_), fun _ ↦ rfl⟩
  exact finitePlaceUnitAverage_coinvariants_equiv_translate w g f x

private theorem finitePlaceUnitAverage_coinvariants_equiv_fixed (w : Places)
    (f : Representation.invariants (ρ(w))) (x : L(w)) :
    finitePlaceUnitAverage w f.val x =
      ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ) * f.val (Multiplicative.ofAdd x) := by
  let φ (u : (L(w))ˣ) := f.val (Multiplicative.ofAdd (x * u.val))
  have hφ (u : (L(w))ˣ) (hu : u ∈ U(w)) : φ u = f.val (Multiplicative.ofAdd x) := by
    let v : U(w) := ⟨u, hu⟩
    have h : (ρ(w)) v⁻¹ f.val = f.val := f.property v⁻¹
    have he := congrArg (fun t : ℬᵥ(w) ↦ t (Multiplicative.ofAdd x)) h
    change f.val (Multiplicative.ofAdd ((u⁻¹⁻¹).val * x)) = f.val (Multiplicative.ofAdd x) at he
    simpa only [φ, inv_inv, mul_comm x] using he
  change ∫ u in (U(w) : Set (L(w))ˣ), φ u ∂μ(w) = _
  have h₁ := setIntegral_congr_fun (μ := μ(w)) (s := (U(w) : Set (L(w))ˣ))
    (f := φ) (g := fun _ ↦ f.val (Multiplicative.ofAdd x)) (units_isOpen w).measurableSet hφ
  have h₂ := setIntegral_const (μ := μ(w)) (s := (U(w) : Set (L(w))ˣ)) (f.val (Multiplicative.ofAdd x))
  exact h₁.trans (h₂.trans Complex.real_smul)

/-- The normalized sum over a finite orbit is a fixed representative of its coinvariant class. -/
private theorem finitePlaceUnitAverage_coinvariants_equiv_representative {G E : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E] (r : Representation ℂ G E) (f : E) (s : Finset E)
    (hs : ∀ y, y ∈ s ↔ ∃ u : G, r u f = y) :
    ∃ y : r.invariants, Representation.Coinvariants.mk r y.val = Representation.Coinvariants.mk r f := by
  classical
  let q := Representation.Coinvariants.mk r
  have mul_apply (a b : G) (y : E) : r (a * b) y = r a (r b y) := DFunLike.congr_fun (r.map_mul a b) y
  have perm (a : G) (y : E) (hy : y ∈ s) : r a y ∈ s := by
    obtain ⟨b, rfl⟩ := (hs y).mp hy
    exact (hs _).mpr ⟨a * b, mul_apply _ _ _⟩
  have undo (a : G) (y : E) : r a⁻¹ (r a y) = y := by rw [← mul_apply, inv_mul_cancel, map_one]; rfl
  have hsum (a : G) : r a (∑ y ∈ s, y) = ∑ y ∈ s, y := by
    rw [map_sum]
    exact Finset.sum_bij' (fun y _ ↦ r a y) (fun y _ ↦ r a⁻¹ y) (perm a) (perm a⁻¹)
      (fun y _ ↦ undo a y) (fun y _ ↦ by simp) (fun _ _ ↦ rfl)
  refine ⟨⟨(s.card : ℂ)⁻¹ • ∑ y ∈ s, y, fun a ↦ by rw [map_smul, hsum]⟩, ?_⟩
  have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
    ⟨r 1 f, (hs _).mpr ⟨1, rfl⟩⟩)
  have hq (y : E) (hy : y ∈ s) : q y = q f := by
    obtain ⟨u, rfl⟩ := (hs y).mp hy
    exact Representation.Coinvariants.mk_self_apply r u f
  change q ((s.card : ℂ)⁻¹ • ∑ y ∈ s, y) = q f
  rw [map_smul, map_sum, Finset.sum_congr rfl hq, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem finitePlaceUnitAverage_coinvariants_equiv_continuous (w : Places)
    (T : ℬᵥ(w) →ₗ[ℂ] ℬᵥ(w)) : Continuous T := by
  let E := ℬᵥ(w)
  have h := finestLocallyConvex_withSeminorms E
  let : IsTopologicalAddGroup (FinestLocallyConvex E) := h.isTopologicalAddGroup
  let T' : FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex E := T
  have hT := h.continuous_of_continuous_comp T' fun p ↦ h.continuous_seminorm (p.comp T')
  exact (congrArg (fun t ↦ @Continuous E E t t T) (finitePlaceSchwartz_finestTopology F w)).mpr hT

private theorem finitePlaceUnitAverage_coinvariants_equiv_mass (w : Places) :
    ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply ENNReal.toReal_ne_zero.mpr
  refine ⟨?_, unitsMass_ne_top w⟩
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits F w]
  exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top

private theorem finitePlaceUnitAverage_coinvariants_equiv_surj (w : Places) (f : ℬᵥ(w)) :
    ∃ y : Representation.invariants (ρ(w)), Representation.Coinvariants.mk (ρ(w)) y.val =
      Representation.Coinvariants.mk (ρ(w)) f := by
  have H := finitePlaceSchwartz_average_dilation (F := F) w f
  refine finitePlaceUnitAverage_coinvariants_equiv_representative (G := U(w)) (E := ℬᵥ(w))
    (ρ(w)) f H.choose ?_
  intro y
  change y ∈ H.choose ↔ ∃ u : U(w), schwartzBruhatUnitRepresentation (R := L(w)) u.val f = y
  simpa only [schwartzBruhatUnitRepresentation_apply] using H.choose_spec.1 y

private theorem finitePlaceUnitAverage_coinvariants_equiv_of_bijective {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (K I : Submodule ℂ E)
    (hc : ∀ T : E →ₗ[ℂ] E, Continuous T) (hq : Bijective (K.mkQ.comp I.subtype))
    (m : ℂ) (hm : m ≠ 0) : ∃ N : (E ⧸ K) ≃L[ℂ] I, ∀ y : I, N (K.mkQ y.val) = m • y := by
  let e := LinearEquiv.ofBijective (K.mkQ.comp I.subtype) hq
  let N := e.symm.trans (LinearEquiv.smulOfNeZero ℂ I m hm)
  have hN : Continuous N := by
    apply K.isQuotientMap_mkQ.continuous_iff.mpr
    exact (hc (I.subtype.comp (N.toLinearMap.comp K.mkQ))).subtype_mk fun f ↦ (N (K.mkQ f)).property
  have hN' : Continuous N.symm :=
    K.continuous_mkQ.comp ((hc (m⁻¹ • LinearMap.id)).comp continuous_subtype_val)
  refine ⟨⟨N, hN, hN'⟩, fun y ↦ ?_⟩
  change m • e.symm (e y) = m • y
  rw [e.symm_apply_apply]

/-- Pointwise averages that descend to the quotient and act by a nonzero mass on fixed vectors
identify the quotient with the fixed space, provided every class has a fixed representative. -/
private theorem finitePlaceUnitAverage_coinvariants_equiv_assemble {G E X : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (r : Representation ℂ G E)
    (hc : ∀ T : E →ₗ[ℂ] E, Continuous T) (m : ℂ) (hm : m ≠ 0)
    (v A : E → X → ℂ) (hext : ∀ f g, (∀ x, v f x = v g x) → f = g)
    (hsmul : ∀ f x, v (m • f) x = m * v f x)
    (hlift : ∀ x, ∃ l : (E ⧸ Representation.Coinvariants.ker r) →ₗ[ℂ] ℂ,
      ∀ f, l ((Representation.Coinvariants.ker r).mkQ f) = A f x)
    (hfixed : ∀ y : r.invariants, ∀ x, A y.val x = m * v y.val x)
    (hrep : ∀ f, ∃ y : r.invariants,
      Representation.Coinvariants.mk r y.val = Representation.Coinvariants.mk r f) :
    ∃ N : (E ⧸ Representation.Coinvariants.ker r) ≃L[ℂ] r.invariants,
      ∀ f x, v (N (Submodule.Quotient.mk f)).val x = A f x := by
  let I := r.invariants
  let K := Representation.Coinvariants.ker r
  have hcongr (f g : E) (h : K.mkQ f = K.mkQ g) (x : X) : A f x = A g x := by
    obtain ⟨l, hl⟩ := hlift x
    exact (hl f).symm.trans ((congrArg l h).trans (hl g))
  have hq : Bijective (K.mkQ.comp I.subtype) := by
    constructor
    · intro f g h
      refine Subtype.ext (hext _ _ fun x ↦ mul_left_cancel₀ hm ?_)
      exact (hfixed f x).symm.trans ((hcongr f.val g.val h x).trans (hfixed g x))
    · intro z
      obtain ⟨f, rfl⟩ := K.mkQ_surjective z
      exact hrep f
  obtain ⟨N, hN⟩ := finitePlaceUnitAverage_coinvariants_equiv_of_bijective K I hc hq m hm
  refine ⟨N, fun f x ↦ ?_⟩
  obtain ⟨y, hy⟩ := hrep f
  change K.mkQ y.val = K.mkQ f at hy
  change v (N (K.mkQ f)).val x = A f x
  rw [← hy, hN]
  exact (hsmul y.val x).trans ((hfixed y x).symm.trans (hcongr y.val f hy x))

/-- Paper: Lemma 6.1.2.4(2), (6.1.2.15), p. 292.
Multiplicative unit averaging induces a linear homeomorphism from the algebraic
coinvariants with their quotient topology to the integer-unit invariants. -/
theorem finitePlaceUnitAverage_coinvariants_equiv (w : Places) :
    ∃ N : (ℬᵥ(w) ⧸ Representation.Coinvariants.ker (ρ(w))) ≃L[ℂ] (Representation.invariants (ρ(w))),
      ∀ (f : ℬᵥ(w)) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finitePlaceUnitAverage w f x := by
  let v (f : ℬᵥ(w)) (x : L(w)) := f (Multiplicative.ofAdd x)
  let m : ℂ := ((μ(w) (U(w) : Set (L(w))ˣ)).toReal : ℂ)
  have extv (f g : ℬᵥ(w)) (h : ∀ x, v f x = v g x) : f = g := Subtype.ext (funext fun x ↦ h x.toAdd)
  have smulv (f : ℬᵥ(w)) (x : L(w)) : v (m • f) x = m * v f x := rfl
  have H := finitePlaceUnitAverage_coinvariants_equiv_assemble (E := ℬᵥ(w)) (G := U(w)) (X := L(w))
    (ρ(w)) (finitePlaceUnitAverage_coinvariants_equiv_continuous w)
    m (finitePlaceUnitAverage_coinvariants_equiv_mass w)
    v (finitePlaceUnitAverage w) extv smulv
  with_reducible
    exact H (finitePlaceUnitAverage_coinvariants_equiv_lift (F := F) w)
      (finitePlaceUnitAverage_coinvariants_equiv_fixed (F := F) w)
      (finitePlaceUnitAverage_coinvariants_equiv_surj (F := F) w)

/-- Paper: Lemma 6.1.2.4(2), p. 292.
Local unit averaging also defines a continuous linear map in the intrinsic
Schwartz–Bruhat topology. -/
theorem finitePlaceUnitAverage_continuous_schwartzBruhat (w : Places) :
    ∃ A : ℬᵥ(w) →L[ℂ] ℬᵥ(w),
      ∀ f x, A f (Multiplicative.ofAdd x) = finitePlaceUnitAverage w f x := by
  let K := Representation.Coinvariants.ker (ρ(w))
  let I := Representation.invariants (ρ(w))
  let N := (finitePlaceUnitAverage_coinvariants_equiv w).choose
  let A : ℬᵥ(w) →L[ℂ] ℬᵥ(w) :=
    { toLinearMap := I.subtype.comp (N.toLinearEquiv.toLinearMap.comp K.mkQ)
      cont := continuous_subtype_val.comp (N.continuous.comp K.continuous_mkQ) }
  exact ⟨A, (finitePlaceUnitAverage_coinvariants_equiv w).choose_spec⟩

private theorem finitePlaceUnitAverage_continuous_uniform_of_finest {E X : Type*}
    [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E] [TopologicalSpace X]
    (ht : t = (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (L : E →ₗ[ℂ] (X → ℂ))
    (hc : ∀ f, Continuous (L f)) (hs : ∀ f, HasCompactSupport (L f)) :
    ∃ A : E →ₗ[ℂ] C_c(X, ℂ), (∀ f x, A f x = L f x) ∧
      Continuous (fun f ↦ (A f).toBoundedContinuousFunction) := by
  let A : E →ₗ[ℂ] C_c(X, ℂ) :=
    { toFun := fun f ↦ ⟨⟨L f, hc f⟩, hs f⟩
      map_add' := fun f g ↦ CompactlySupportedContinuousMap.ext fun x ↦
        congrFun (L.map_add f g) x
      map_smul' := fun c f ↦ CompactlySupportedContinuousMap.ext fun x ↦
        congrFun (L.map_smul c f) x }
  let B : FinestLocallyConvex E →ₗ[ℂ] (BoundedContinuousFunction X ℂ) :=
    { toFun := fun f ↦ (A f).toBoundedContinuousFunction
      map_add' := fun f g ↦ BoundedContinuousFunction.ext fun x ↦
        congrFun (L.map_add f g) x
      map_smul' := fun c f ↦ BoundedContinuousFunction.ext fun x ↦
        congrFun (L.map_smul c f) x }
  exact ⟨A, fun _ _ ↦ rfl,
    (congrArg (fun t' ↦ @Continuous E (BoundedContinuousFunction X ℂ) t' _ B) ht).mpr
      (continuous_of_finestLocallyConvex E B)⟩

/-- Paper: Lemma 6.1.2.4(2), (6.1.2.13)–(6.1.2.14), p. 292.
Local unit averaging defines a linear map to compactly supported continuous functions
which is continuous for their uniform norm. -/
theorem finitePlaceUnitAverage_continuous_uniform (w : Places) :
    ∃ A : ℬᵥ(w) →ₗ[ℂ] C_c(L(w), ℂ),
      (∀ f x, A f x = finitePlaceUnitAverage w f x) ∧
        Continuous (fun f ↦ (A f).toBoundedContinuousFunction) := by
  let N := (finitePlaceUnitAverage_continuous_schwartzBruhat w).choose
  let L : ℬᵥ(w) →ₗ[ℂ] (L(w) → ℂ) :=
    { toFun := fun f x ↦ N f (Multiplicative.ofAdd x)
      map_add' := fun f g ↦ funext fun x ↦
        congrArg (fun h : ℬᵥ(w) ↦ h (Multiplicative.ofAdd x)) (N.map_add f g)
      map_smul' := fun c f ↦ funext fun x ↦
        congrArg (fun h : ℬᵥ(w) ↦ h (Multiplicative.ofAdd x)) (N.map_smul c f) }
  have hc (f : ℬᵥ(w)) : Continuous (L f) :=
    (schwartzBruhat_continuous (N f)).comp continuous_ofAdd
  have hs (f : ℬᵥ(w)) : HasCompactSupport (L f) :=
    ((mem_finitePlaceSchwartz_iff F w (L f)).mp ⟨N f, fun _ ↦ rfl⟩).2
  have h := finitePlaceUnitAverage_continuous_uniform_of_finest
    (finitePlaceSchwartz_finestTopology F w) L hc hs
  refine ⟨h.choose, fun f x ↦ (h.choose_spec.1 f x).trans ?_, h.choose_spec.2⟩
  exact (finitePlaceUnitAverage_continuous_schwartzBruhat w).choose_spec f x

local notation "K(" D ")" => FinitePlaceProduct F D
local notation "KUnits(" D ")" =>
  (Subgroup.pi Set.univ (fun w : D ↦ U(w.val))).comap
    (MulEquiv.piUnits (M := fun w : D ↦ L(w.val))).toMonoidHom
local notation "ρΠ(" D ")" =>
  (schwartzBruhatUnitRepresentation (R := K(D))).comp (KUnits(D)).subtype

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product of the local averages integrates the test function along its orbit
against the product of the restricted local multiplicative Tamagawa measures. -/
def finiteProductUnitAverage (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) : ℂ :=
  ∫ u : ∀ v : D, (L(v.val))ˣ,
    f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val))
    ∂(Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val)))

/-- Paper: Lemma 6.1.2.4(3), p. 292.
At the zero tuple, product averaging multiplies the value there by the product
of the local integer-unit masses. -/
theorem finiteProductUnitAverage_zero (D : Finset Places) (f : ℬ(K(D))) :
    finiteProductUnitAverage D f 0 =
      (∏ w : D, ((μ(w.val) (U(w.val) : Set (L(w.val))ˣ)).toReal : ℂ)) *
        f (Multiplicative.ofAdd 0) := by
  unfold finiteProductUnitAverage
  simp only [Pi.zero_apply, zero_mul, integral_const]
  rw [Measure.real, Measure.pi_univ, ENNReal.toReal_prod, Complex.real_smul, Complex.ofReal_prod]
  simp only [Measure.restrict_apply_univ]
  rfl

private local instance (w : HeightOneSpectrum (𝓞 F)) : ProperSpace (L(w)) := properSpace_adicCompletion w
private local instance (w : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (L(w))ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

/-- Paper: Lemma 6.1.2.4(3), p. 292.
The product orbit integral is integrable against the finite product of the restricted measures. -/
theorem finiteProductUnitAverage_integrable (D : Finset Places) (f : ℬ(K(D))) (x : K(D)) :
    Integrable
      (fun u : ∀ v : D, (L(v.val))ˣ ↦
        f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val)))
      (Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))) := by
  have hc : Continuous (fun u : ∀ v : D, (L(v.val))ˣ ↦
        f (Multiplicative.ofAdd (fun v ↦ x v * (u v).val))) :=
    (schwartzBruhat_continuous f).comp
      (continuous_ofAdd.comp (continuous_pi fun v ↦
        continuous_const.mul (Units.continuous_val.comp (continuous_apply v))))
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun v : D ↦ units_isCompact v.val).exists_bound_of_continuousOn
    hc.continuousOn
  refine Integrable.of_bound hc.aestronglyMeasurable C ?_
  have hae : ∀ᵐ u ∂(Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))),
      ∀ v : D, u v ∈ (U(v.val) : Set (L(v.val))ˣ) := by
    rw [ae_all_iff]
    intro v
    exact (Measure.tendsto_eval_ae_ae (μ := fun v : D ↦ (μ(v.val)).restrict (U(v.val))) (i := v)).eventually
      (ae_restrict_mem (units_isOpen v.val).measurableSet)
  filter_upwards [hae] with u hu
  exact hC u (Set.mem_univ_pi.2 hu)


/-- Paper: Lemma 6.1.2.4(3), p. 292.
The integer-unit invariants are closed in the Schwartz–Bruhat space on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductSchwartz_unitInvariants_isClosed (D : Finset Places) (_hD : D.Nonempty) :
    IsClosed ((Representation.invariants (ρΠ(D))) : Set ℬ(K(D))) :=
  unitInvariants_isClosed _

private theorem finiteProductUnitAverage_coinvariants_equiv_representative
    (D : Finset Places) (f : ℬ(K(D))) :
    ∃ y : Representation.invariants (ρΠ(D)),
      Representation.Coinvariants.mk (ρΠ(D)) y.val =
        Representation.Coinvariants.mk (ρΠ(D)) f := by
  classical
  let C : Set (K(D)) := univ.pi fun v : D ↦ (O(v.val) : Set (L(v.val)))
  have hC : IsCompact C := isCompact_univ_pi fun v : D ↦
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val)
  let : TotallyDisconnectedSpace (Multiplicative (K(D))) :=
    inferInstanceAs (TotallyDisconnectedSpace (∀ v : D, L(v.val)))
  have hf := schwartzBruhat_locallyConstant_compactSupport
    (finitePlaceProduct_compact_subset_subgroup F D) f
  have hfinite := finite_unit_dilates C hC f hf.1 hf.2
  have horbit : (range fun g : KUnits(D) ↦ (ρΠ(D)) g f).Finite := by
    refine hfinite.subset ?_
    rintro _ ⟨g, rfl⟩
    have hu (v : D) : MulEquiv.piUnits (M := fun v : D ↦ L(v.val)) g.val v ∈ U(v.val) :=
      g.property v (mem_univ v)
    exact ⟨⟨g.val, fun v _ ↦ (hu v).1, fun v _ ↦ (hu v).2⟩, rfl⟩
  exact finitePlaceUnitAverage_coinvariants_equiv_representative
    (G := KUnits(D)) (E := ℬ(K(D))) (ρΠ(D)) f horbit.toFinset fun y ↦ by
      rw [Set.Finite.mem_toFinset, Set.mem_range]

private theorem finiteProductUnitAverage_coinvariants_equiv_integral (D : Finset Places) :
    let ν := Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))
    let m : ℂ := (ν.real univ : ℝ)
    m ≠ 0 ∧
      (∀ x : K(D), ∃ l : (ℬ(K(D)) ⧸ Representation.Coinvariants.ker (ρΠ(D))) →ₗ[ℂ] ℂ,
        ∀ f, l ((Representation.Coinvariants.ker (ρΠ(D))).mkQ f) =
          finiteProductUnitAverage D f x) ∧
      (∀ (y : Representation.invariants (ρΠ(D))) (x : K(D)),
        finiteProductUnitAverage D y.val x = m * y.val (Multiplicative.ofAdd x)) := by
  classical
  let ν := Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))
  let m : ℂ := (ν.real univ : ℝ)
  let H := Subgroup.pi Set.univ fun v : D ↦ U(v.val)
  let (v : D) : (μ(v.val)).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let ambientMeasure := Measure.pi fun v : D ↦ μ(v.val)
  let e := MulEquiv.piUnits (M := fun v : D ↦ L(v.val))
  have hH : MeasurableSet (H : Set (∀ v : D, (L(v.val))ˣ)) :=
    MeasurableSet.univ_pi fun v ↦ (units_isOpen v.val).measurableSet
  have hν : ambientMeasure.restrict (H : Set (∀ v : D, (L(v.val))ˣ)) = ν :=
    Measure.restrict_pi_pi (fun v : D ↦ μ(v.val)) (fun v ↦ (U(v.val) : Set (L(v.val))ˣ))
  have hm : m ≠ 0 := by
    change ((ν univ).toReal : ℂ) ≠ 0
    rw [Measure.pi_univ, ENNReal.toReal_prod, Complex.ofReal_prod]
    simp only [Measure.restrict_apply_univ]
    exact Finset.prod_ne_zero_iff.mpr (fun v _ ↦ finitePlaceUnitAverage_coinvariants_equiv_mass v.val)
  refine ⟨hm, ?_, ?_⟩
  · intro x
    let A : ℬ(K(D)) →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ finiteProductUnitAverage D f x
        map_add' := fun f g ↦ integral_add (finiteProductUnitAverage_integrable D f x)
          (finiteProductUnitAverage_integrable D g x)
        map_smul' := fun c f ↦ integral_smul c _ }
    refine ⟨Representation.Coinvariants.lift (ρΠ(D)) A
      (fun g ↦ LinearMap.ext fun f ↦ ?_), fun _ ↦ rfl⟩
    let a := e (g⁻¹ : KUnits(D)).val
    have ha : a ∈ H := (g⁻¹ : KUnits(D)).property
    let φ (u : ∀ v : D, (L(v.val))ˣ) := f (Multiplicative.ofAdd (x * (e.symm u).val))
    have hφ (u : ∀ v : D, (L(v.val))ˣ) :
        ((ρΠ(D)) g f) (Multiplicative.ofAdd (x * (e.symm u).val)) = φ (a * u) := by
      change f (Multiplicative.ofAdd ((g.val⁻¹ : (K(D))ˣ).val * (x * (e.symm u).val))) =
        f (Multiplicative.ofAdd (x * (e.symm (a * u)).val))
      refine congrArg (fun z : K(D) ↦ f (Multiplicative.ofAdd z)) ?_
      rw [e.symm.map_mul, show e.symm a = g.val⁻¹ from e.symm_apply_apply _]
      exact mul_left_comm _ _ _
    change (∫ u, ((ρΠ(D)) g f) (Multiplicative.ofAdd (x * (e.symm u).val)) ∂ν) = ∫ u, φ u ∂ν
    simp_rw [hφ]
    rw [← hν]
    exact finitePlaceUnitAverage_coinvariants_equiv_restrict ambientMeasure H hH a ha φ
  · intro y x
    let φ (u : ∀ v : D, (L(v.val))ˣ) := y.val (Multiplicative.ofAdd (x * (e.symm u).val))
    have hφ (u : ∀ v : D, (L(v.val))ˣ) (hu : u ∈ H) :
        φ u = y.val (Multiplicative.ofAdd x) := by
      let g : KUnits(D) := ⟨e.symm u, by change e (e.symm u) ∈ H; rwa [e.apply_symm_apply]⟩
      have he := congrArg (fun f : ℬ(K(D)) ↦ f (Multiplicative.ofAdd x)) (y.property g⁻¹)
      change y.val (Multiplicative.ofAdd (((g⁻¹ : KUnits(D)).val⁻¹ : (K(D))ˣ).val * x)) =
        y.val (Multiplicative.ofAdd x) at he
      rw [Subgroup.coe_inv, inv_inv, mul_comm] at he
      exact he
    change ∫ u, φ u ∂ν = m * y.val (Multiplicative.ofAdd x)
    calc
      ∫ u, φ u ∂ν = ∫ u, y.val (Multiplicative.ofAdd x) ∂ν := by
        rw [← hν]
        exact setIntegral_congr_fun hH hφ
      _ = _ := (integral_const _).trans Complex.real_smul

/-- Paper: Lemma 6.1.2.4(3), (6.1.2.16), p. 292.
The product of the local unit averages induces a linear homeomorphism from
coinvariants with their quotient topology to invariants on the finite product.
Deviation: The place set is written directly as the finite set of additional places. -/
theorem finiteProductUnitAverage_coinvariants_equiv (D : Finset Places) (_hD : D.Nonempty) :
    ∃ N : (ℬ(K(D)) ⧸ Representation.Coinvariants.ker (ρΠ(D))) ≃L[ℂ] (Representation.invariants (ρΠ(D))),
      ∀ (f : ℬ(K(D))) x, (N (Submodule.Quotient.mk f)).val (Multiplicative.ofAdd x) =
        finiteProductUnitAverage D f x := by
  let E := ℬ(K(D))
  let v (f : E) (x : K(D)) := f (Multiplicative.ofAdd x)
  let ν := Measure.pi fun v : D ↦ (μ(v.val)).restrict (U(v.val))
  let m : ℂ := (ν.real univ : ℝ)
  have hc (T : E →ₗ[ℂ] E) : Continuous T := by
    have h := finestLocallyConvex_withSeminorms E
    let : IsTopologicalAddGroup (FinestLocallyConvex E) := h.isTopologicalAddGroup
    let T' : FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex E := T
    have hT := h.continuous_of_continuous_comp T' fun p ↦ h.continuous_seminorm (p.comp T')
    exact (congrArg (fun t ↦ @Continuous E E t t T)
      (finiteProduct_tailSchwartz_finestTopology F D ∅).1).mpr hT
  have hv (f g : E) (h : ∀ x, v f x = v g x) : f = g :=
    Subtype.ext (funext fun x ↦ h x.toAdd)
  have hsmul (f : E) (x : K(D)) : v (m • f) x = m * v f x := rfl
  have h := finiteProductUnitAverage_coinvariants_equiv_integral (F := F) D
  have result := finitePlaceUnitAverage_coinvariants_equiv_assemble (E := E)
    (G := KUnits(D)) (X := K(D)) (ρΠ(D)) hc m h.1 v (finiteProductUnitAverage D) hv hsmul
  with_reducible
    exact result h.2.1 h.2.2 (finiteProductUnitAverage_coinvariants_equiv_representative D)

end Averaging

end RiemannMasullo
