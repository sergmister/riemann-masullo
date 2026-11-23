module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.Complex
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import all RiemannMasullo.AppA_AlgebraicNT.Sec1
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Basic
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import RiemannMasullo.ForMathlib.Analysis.Fourier.FourierPhase
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.ContinuousOfBounded
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Montel
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Group.FundamentalDomain
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.InfiniteAdeleRing
import RiemannMasullo.ForMathlib.RingTheory.Trace.Defs
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
import RiemannMasullo.ForMathlib.Topology.Covering.AddCircle

/-!
# Directional derivatives and homogeneous adelic theta functions

Masullo, §§2.2.4–2.2.5, pp. 86–98.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped ContDiff Manifold NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "N₁[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "valueℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)
local notation "normℝ" => fun (g : C[F]) ↦ valueℝ (ideleClassNorm F g)
local notation "expUnit" => fun s : ℝ ↦ Homeomorph.symm (Nonneg.unitsHomeomorphPos ℝ) (Real.expOrderIso s)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

section DirectionalDerivatives

variable (γ : ℝ≥0ˣ →ₜ* 𝕀[F])

/-- Paper: Lemma 2.2.4.1, p. 87. Every idele in a continuous one-parameter
subgroup has finite component one. -/
theorem adeleOneParameter_finite_eq_one (t : ℝ≥0ˣ) : (γ t).val.2 = 1 := by
  have : ConnectedSpace ℝ≥0ˣ :=
    (Nonneg.unitsHomeomorphPos ℝ).connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp (isConnected_Ioi (a := (0 : ℝ))))
  have hVal : Continuous (fun s : ℝ≥0ˣ ↦ (γ s).val) :=
    Units.continuous_val.comp γ.continuous
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro v
  have hCoord : Continuous (fun s : ℝ≥0ˣ ↦ (γ s).val.2 v) :=
    (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp hVal)
  calc
    (γ t).val.2 v = (γ 1).val.2 v :=
      TotallyDisconnectedSpace.eq_of_continuous _ hCoord t 1
    _ = (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v := by rw [map_one]; rfl

/-- Paper: Lemma 2.2.4.1, p. 87. The norm of a continuous one-parameter
subgroup is a power of its positive real parameter, with unique real exponent.
The norm-one case has exponent zero. -/
theorem adeleOneParameter_norm_rpow :
    ∃! α : ℝ, ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α := by
  let E : ℝ ≃ₜ ℝ≥0ˣ :=
    Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hE (x : ℝ) : valueℝ (E x) = Real.exp x := rfl
  have hEadd (x y : ℝ) : E (x + y) = E x * E y :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add x y))
  have hpos (t : ℝ≥0ˣ) : 0 < valueℝ t := NNReal.coe_pos.mpr (Units.zero_lt t)
  let f : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun x ↦ Real.log (valueℝ (ideleNorm F (γ (E x))))) (by
      intro x y
      dsimp only
      rw [hEadd, map_mul, map_mul, Units.val_mul, NNReal.coe_mul,
        Real.log_mul (hpos _).ne' (hpos _).ne'])
  have hf : Continuous f := by
    change Continuous (fun x ↦ Real.log (valueℝ (ideleNorm F (γ (E x)))))
    have hNorm : Continuous (ideleNorm F) := (ideleGroup_topology F).2.2.2.2.1
    exact (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (hNorm.comp (γ.continuous.comp E.continuous)))).log
      fun x ↦ (hpos _).ne'
  have hlinear (x : ℝ) : f x = x * f 1 := by
    simpa only [smul_eq_mul, mul_one] using map_real_smul f hf x (1 : ℝ)
  have hpower (x a : ℝ) : (valueℝ (E x)) ^ a = Real.exp (x * a) := by
    rw [hE, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  have h (t : ℝ≥0ˣ) : valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ f 1 := by
    obtain ⟨x, rfl⟩ := E.surjective t
    rw [hpower, ← hlinear]
    exact (Real.exp_log (hpos _)).symm
  refine ⟨f 1, h, fun a ha ↦ ?_⟩
  have ha' := (ha (E 1)).symm.trans (h (E 1))
  simpa only [hpower, one_mul, Real.exp_eq_exp] using ha'

/-- Paper: Lemma 2.2.4.1(1)–(2), p. 87. The norm of the subgroup is either
an automorphism smooth in both directions or identically one. Smoothness is
expressed in the logarithmic coordinate on the positive reals. -/
theorem adeleOneParameter_norm_cases :
    Xor
      (∃ e : ℝ≥0ˣ ≃ₜ* ℝ≥0ˣ, (∀ t, e t = ideleNorm F (γ t)) ∧
        ContDiff ℝ (∞ : ℕ∞ω) (fun s : ℝ ↦ Real.log (valueℝ (e (expUnit s)))) ∧
        ContDiff ℝ (∞ : ℕ∞ω) (fun s : ℝ ↦ Real.log (valueℝ (e.symm (expUnit s)))))
      (∀ t : ℝ≥0ˣ, ideleNorm F (γ t) = 1) := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let n : ℝ≥0ˣ →* ℝ≥0ˣ := (ideleNorm F).comp γ.toMonoidHom
  have hE (s : ℝ) : valueℝ (E s) = Real.exp s := rfl
  have hLog (t : ℝ≥0ˣ) : Real.log (valueℝ t) = E.symm t := by
    obtain ⟨s, rfl⟩ := E.surjective t
    rw [hE, Real.log_exp, E.symm_apply_apply]
  have hZero : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hAdd (s t : ℝ) : E (s + t) = E s * E t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add s t))
  -- In logarithmic coordinates, the norm is a continuous additive map on ℝ.
  let f : ℝ →+ ℝ := AddMonoidHom.mk' (fun s ↦ E.symm (n (E s))) (by
    intro s t
    apply E.injective
    simp only [E.apply_symm_apply, hAdd, map_mul])
  have hf : Continuous f := E.symm.continuous.comp
    ((ideleGroup_topology F).2.2.2.2.1.comp (γ.continuous.comp E.continuous))
  let α := f 1
  have hNorm (s : ℝ) : n (E s) = E (α * s) := by
    apply E.symm.injective
    rw [E.symm_apply_apply]
    change f s = f 1 * s
    simpa only [smul_eq_mul, mul_one, mul_comm s (f 1)] using map_real_smul f hf s (1 : ℝ)
  by_cases hα : α = 0
  · have hn (t : ℝ≥0ˣ) : n t = 1 := by
      obtain ⟨s, rfl⟩ := E.surjective t
      rw [hNorm, hα, zero_mul, hZero]
    refine Or.inr ⟨hn, ?_⟩
    rintro ⟨e, he, -, -⟩
    have heOne (t : ℝ≥0ˣ) : e t = 1 := (he t).trans (hn t)
    exact one_ne_zero (E.injective (e.injective ((heOne (E 1)).trans (heOne (E 0)).symm)))
  · let H := (E.symm.trans (Homeomorph.mulLeft₀ α hα)).trans E
    have hH (t : ℝ≥0ˣ) : H t = n t := by
      change E (α * E.symm t) = n t
      rw [← hNorm, E.apply_symm_apply]
    let e := ContinuousMulEquiv.mk' H (by
      intro t u
      simp only [hH, map_mul])
    refine Or.inl ⟨⟨e, hH, ?_, ?_⟩, ?_⟩
    · change ContDiff ℝ (∞ : ℕ∞ω) (fun s ↦ Real.log (valueℝ (E (α * E.symm (E s)))))
      simp only [hLog, E.symm_apply_apply]
      exact contDiff_const.mul contDiff_id
    · change ContDiff ℝ (∞ : ℕ∞ω) (fun s ↦ Real.log (valueℝ (E (α⁻¹ * E.symm (E s)))))
      simp only [hLog, E.symm_apply_apply]
      exact contDiff_const.mul contDiff_id
    · intro hn
      have hOne : E α = 1 := by
        simpa only [mul_one] using (hNorm 1).symm.trans (hn (E 1))
      exact hα (E.injective (hOne.trans hZero.symm))

local notation "orbitDeriv" => fun (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (f : ℬ[F]) (x : Multiplicative 𝔸[F]) ↦
  deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd (Units.val (γ (expUnit s)) * Multiplicative.toAdd x))) 0

section Archimedean

open scoped Classical

local notation "mixed" => InfiniteAdeleRing.ringEquiv_mixedSpace F

/-- Euclidean coordinates identify the full, trivial-kernel Bruhat stage with the
classical Schwartz space. Every structural stage maps into this stage. -/
private theorem mem_schwartzBruhatSubmodule_euclidean_iff
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] {n : ℕ}
    (v : A ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n))) (g : A → ℂ) :
    g ∈ schwartzBruhatSubmodule A ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, s (v x).toAdd = g x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let P := ElementaryLieGroup n 0 0 PUnit
  let D := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit
  let : Unique D := uniqueOfSubsingleton 0
  let p : Multiplicative E ≃ₜ* Multiplicative P :=
    { toMulEquiv := (AddEquiv.prodUnique (M := E) (N := D)).symm.toMultiplicative
      continuous_toFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : E ↦ (x, (default : D))))
      continuous_invFun := (continuous_fst : Continuous (Prod.fst : E × D → E)) }
  let e : ElementaryLCAPresentation A :=
    { realDim := n, torusDim := 0, latticeRank := 0, finiteFactor := PUnit, equiv := v.trans p }
  have hA := (lca_elementary_iff (G := A)).mpr ⟨e⟩
  let i : (⊤ : Subgroup A) ≃ₜ* A :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair A := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hA.1,
    isBruhatGoodSubgroup_bot_iff.mpr hA.2, bot_le⟩
  let q₀ : A →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hq₀ : IsOpenQuotientMap q₀ :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have hinj : Injective q₀ := (MonoidHom.ker_eq_bot_iff q₀).mp (eq_bot_iff.mpr fun x hx ↦ by
    exact (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective q₀ ⟨hinj, hq₀.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hq₀.isQuotientMap.isOpen_preimage)
  let e₀ : ElementaryLCAPresentation a.quotient := { e with equiv := q.symm.trans e.equiv }
  have hreal (s : SchwartzBruhatStage e₀) (x : A) :
      schwartzBruhatStageRealization a e₀ s x = s ((v x).toAdd, 0, 0, PUnit.unit) := by
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    change s ((e₀.equiv (q x)).toAdd) = _
    change s ((e.equiv (q.symm (q x))).toAdd) = _
    rw [q.symm_apply_apply]
    rfl
  have hrange : schwartzBruhatSubmodule A = (schwartzBruhatStageRealization a e₀).range := by
    refine le_antisymm (iSup_le fun b ↦ iSup_le fun eb ↦ ?_) ?_
    · rintro _ ⟨sb, rfl⟩
      obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (show b ≤ a from ⟨le_top, le_top⟩) eb e₀
      exact ⟨j sb, hj sb⟩
    · exact le_iSup_of_le a (le_iSup (fun e ↦ (schwartzBruhatStageRealization a e).range) e₀)
  rw [hrange, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    let f : E → ℂ := fun x ↦ s (x, 0, 0, PUnit.unit)
    have hs' (y : P) : f y.1 = s y :=
      congrArg (fun z : P ↦ s z) (Prod.ext rfl (Subsingleton.elim _ _))
    have hf : (fun y : P ↦ f y.1) ∈ elementarySchwartzSubmodule n 0 0 PUnit :=
      (funext hs').symm ▸ s.property
    obtain ⟨S, hS⟩ := (elementarySchwartzSubmodule_real_iff f).mp hf
    refine ⟨S, fun x ↦ ?_⟩
    exact (congrFun hS (v x).toAdd).trans
      ((hreal s x).symm.trans (congrFun hs x))
  · rintro ⟨s, hs⟩
    let t : SchwartzBruhatStage e₀ :=
      ⟨fun y : P ↦ s y.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨s, rfl⟩⟩
    exact ⟨t, funext fun x ↦ (hreal t x).trans (hs x)⟩

omit [NumberField F] in
/-- The mixed coordinate map on infinite adeles is continuous in both directions. -/
private theorem continuous_mixedCoordinates : Continuous mixed ∧ Continuous (mixed).symm :=
  ⟨continuous_infiniteAdeleRingEquivMixedSpace F, continuous_infiniteAdeleRingEquivMixedSpace_symm F⟩

/-- In mixed real and complex coordinates, the archimedean Schwartz–Bruhat functions
are precisely the classical Schwartz functions on the underlying real vector space. -/
theorem mem_archimedeanSchwartzBruhat_iff (g : InfiniteAdeleRing F → ℂ) :
    g ∘ Multiplicative.toAdd ∈ schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F)) ↔
      ∃ G : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ, ∀ x, G (mixed x) = g x := by
  classical
  let V := mixedEmbedding.mixedSpace F
  let n := Module.finrank ℝ V
  let L : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  obtain ⟨hm, hm'⟩ := continuous_mixedCoordinates (F := F)
  let v : Multiplicative (InfiniteAdeleRing F) ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n)) :=
    { toMulEquiv := ((mixed).toAddEquiv.trans L.toLinearEquiv.toAddEquiv).toMultiplicative
      continuous_toFun := L.continuous.comp hm
      continuous_invFun := hm'.comp L.symm.continuous }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) :=
    v.toHomeomorph.isEmbedding.t2Space
  rw [mem_schwartzBruhatSubmodule_euclidean_iff v]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L s, fun x ↦ hs (Multiplicative.ofAdd x)⟩
  · rintro ⟨s, hs⟩
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm s, fun x ↦ ?_⟩
    change s (L.symm (L (mixed x.toAdd))) = g x.toAdd
    rw [L.symm_apply_apply, hs]

/-- The logarithmically parametrized archimedean component of the subgroup is
differentiable at the identity in mixed coordinates. -/
private theorem adeleOneParameter_archimedean_differentiable :
    DifferentiableAt ℝ (fun s : ℝ ↦ mixed (γ (expUnit s)).val.1) 0 := by
  have hCharacter (c : ℝ≥0ˣ →ₜ* ℂ) : DifferentiableAt ℝ (fun s ↦ c (expUnit s)) 0 := by
    obtain ⟨z, hz, _⟩ := existsUnique_complexPower c
    have hExp (s : ℝ) : c (expUnit s) = Complex.exp ((s : ℂ) * z) := by
      have h := hz (expUnit s)
      change c (expUnit s) = (↑(Real.exp s) : ℂ) ^ z at h
      refine h.trans ?_
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
        ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp]
    simp_rw [hExp]
    exact Complex.differentiableAt_exp.comp 0
      (Complex.ofRealCLM.differentiableAt.mul_const z)
  have hc (v : InfinitePlace F) :
      DifferentiableAt ℝ (fun s : ℝ ↦
        InfinitePlace.Completion.extensionEmbedding v ((γ (expUnit s)).val.1 v)) 0 := by
    let c : ℝ≥0ˣ →ₜ* ℂ :=
      { toFun := fun t ↦ InfinitePlace.Completion.extensionEmbedding v ((γ t).val.1 v)
        map_one' := by rw [map_one]; exact map_one _
        map_mul' := fun t u ↦ by rw [map_mul]; exact map_mul _ _ _
        continuous_toFun := (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
          ((continuous_apply v).comp (continuous_fst.comp (Units.continuous_val.comp γ.continuous))) }
    exact hCharacter c
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply DifferentiableAt.prodMk
  · refine differentiableAt_pi.mpr fun v ↦ ?_
    have h := Complex.reCLM.differentiableAt.comp 0 (hc v.1)
    have hReal (s : ℝ) : (InfinitePlace.Completion.extensionEmbedding v.1
        ((γ (expUnit s)).val.1 v.1)).re =
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 ((γ (expUnit s)).val.1 v.1) := by
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply v.2, Complex.ofReal_re]
    change DifferentiableAt ℝ (fun s ↦ (InfinitePlace.Completion.extensionEmbedding v.1
      ((γ (expUnit s)).val.1 v.1)).re) 0 at h
    simpa only [hReal] using h
  · exact differentiableAt_pi.mpr fun v ↦ hc v.1

/-- Differentiating a pure archimedean test function along the logarithmic
dilation gives an archimedean test function, with an actual pointwise derivative. -/
private theorem adeleDirectionalDeriv_archimedean
    (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) :
    ∃ d : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)), ∀ x : InfiniteAdeleRing F,
      HasDerivAt (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x)))
        (d (Multiplicative.ofAdd x)) 0 := by
  let V := mixedEmbedding.mixedSpace F
  obtain ⟨G, hG⟩ := (mem_archimedeanSchwartzBruhat_iff
    (fun x ↦ f (Multiplicative.ofAdd x))).mp f.property
  let curve : ℝ → V := fun s ↦ mixed (γ (expUnit s)).val.1
  let velocity : V := deriv curve 0
  have hCurve : HasDerivAt curve velocity 0 :=
    (adeleOneParameter_archimedean_differentiable γ).hasDerivAt
  have hOne : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hZero : curve 0 = 1 := by
    have hγ : γ (expUnit (0 : ℝ)) = 1 := (congrArg γ hOne).trans (map_one γ)
    exact (congrArg (fun u : 𝕀[F] ↦ mixed u.val.1) hγ).trans (map_one mixed)
  let L : V →L[ℝ] V := ContinuousLinearMap.mul ℝ V velocity
  let D : SchwartzMap V ℂ :=
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ).flip L.hasTemperateGrowth
      (SchwartzMap.fderivCLM ℝ V ℂ G)
  have hmem := (mem_archimedeanSchwartzBruhat_iff (fun x ↦ D (mixed x))).mpr ⟨D, fun _ ↦ rfl⟩
  refine ⟨⟨fun x ↦ D (mixed x.toAdd), hmem⟩, fun x ↦ ?_⟩
  have hOrbit : HasDerivAt (fun s ↦ curve s * mixed x) (L (mixed x)) 0 :=
    hCurve.mul_const (mixed x)
  have hG' : HasFDerivAt G (fderiv ℝ G (mixed x)) (curve 0 * mixed x) := by
    rw [hZero, one_mul]
    exact G.hasFDerivAt _
  have hEval : (fun s : ℝ ↦ G (curve s * mixed x)) =
      fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x)) := by
    funext s
    rw [← hG, map_mul mixed]
  rw [← hEval]
  exact hG'.comp_hasDerivAt 0 hOrbit

end Archimedean

open scoped TensorProduct in
/-- Paper: Lemma 2.2.4.2, p. 87. Differentiating the orbit curve pointwise in
the logarithmic parameter gives a Schwartz–Bruhat function. -/
theorem adeleDirectionalDeriv_mem (f : ℬ[F]) :
    orbitDeriv γ f ∈ schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by
  obtain ⟨e, he⟩ := adeleSchwartz_inductiveTensor_equiv F
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B := SchwartzBruhat (Multiplicative (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
  let E : (A ⊗[ℂ] B) ≃ₗ[ℂ] ℬ[F] := e.toLinearEquiv
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq (E.symm f)
  have hf : f = ∑ i, E (a i ⊗ₜ[ℂ] b i) := by
    calc
      f = E (E.symm f) := (E.apply_symm_apply f).symm
      _ = E (∑ i, a i ⊗ₜ[ℂ] b i) := congrArg E hab
      _ = _ := map_sum E _ _
  choose d hd using fun i ↦ adeleDirectionalDeriv_archimedean γ (a i)
  let eval (x : 𝔸[F]) : ℬ[F] →ₗ[ℂ] ℂ :=
    { toFun := fun g ↦ g (Multiplicative.ofAdd x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let g (i : Fin n) : ℬ[F] := E (a i ⊗ₜ[ℂ] b i)
  let dg (i : Fin n) : ℬ[F] := E (d i ⊗ₜ[ℂ] b i)
  have hDeriv (i : Fin n) (x : 𝔸[F]) :
      HasDerivAt (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x) (g i)) (eval x (dg i)) 0 := by
    let aOrbit (s : ℝ) := a i (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1))
    let bValue := b i (Multiplicative.ofAdd x.2)
    have hEval : (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x) (g i)) =
        fun s : ℝ ↦ aOrbit s * bValue := by
      funext s
      refine (he (a i) (b i) ((γ (expUnit s)).val * x)).trans ?_
      have hFinite : ((γ (expUnit s)).val.2 * x.2) = x.2 :=
        (congrArg (· * x.2) (adeleOneParameter_finite_eq_one γ (expUnit s))).trans (one_mul _)
      exact congrArg (fun y ↦ aOrbit s * b i (Multiplicative.ofAdd y)) hFinite
    have hValue : eval x (dg i) = d i (Multiplicative.ofAdd x.1) * bValue := he (d i) (b i) x
    exact (congrArg₂ (fun c v ↦ HasDerivAt c v (0 : ℝ)) hEval hValue).mpr
      ((hd i x.1).mul_const bValue)
  let result : ℬ[F] := ∑ i, dg i
  have hEq : orbitDeriv γ f = (result : Multiplicative 𝔸[F] → ℂ) := by
    funext x
    have hOrbit : (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x.toAdd) f) =
        fun s : ℝ ↦ ∑ i, eval ((γ (expUnit s)).val * x.toAdd) (g i) := by
      funext s
      let ev := eval ((γ (expUnit s)).val * x.toAdd)
      exact (congrArg ev hf).trans (map_sum ev g Finset.univ)
    have hValue : eval x.toAdd result = ∑ i, eval x.toAdd (dg i) :=
      map_sum (eval x.toAdd) dg Finset.univ
    change deriv (fun s : ℝ ↦ eval ((γ (expUnit s)).val * x.toAdd) f) 0 = eval x.toAdd result
    exact (congrArg (fun c ↦ deriv c 0) hOrbit).trans
      ((HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hDeriv i x.toAdd).deriv.trans hValue.symm)
  rw [hEq]
  exact result.property

/-- Paper: Lemma 2.2.4.2, p. 87. The Archimedean coordinates of a continuous
one-parameter group of ideles are differentiable in the logarithmic parameter. -/
private theorem adeleOneParameter_infinite_differentiableAt :
    DifferentiableAt ℝ
      (fun s : ℝ ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F (γ (expUnit s)).val.1) 0 := by
  classical
  have hScalar {𝕜 : Type} [RCLike 𝕜] (g : ℝ → 𝕜) (hg : Continuous g)
      (hOne : g 0 = 1) (hMul : ∀ s t, g (s + t) = g s * g t) :
      DifferentiableAt ℝ g 0 := by
    -- A nonzero interval integral expresses the subgroup curve through its primitive.
    let I : ℝ → 𝕜 := fun t ↦ ∫ u in 0..t, g u
    have hI t : HasDerivAt I (g t) t :=
      intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    obtain ⟨b, hb⟩ : ∃ b, I b ≠ 0 := by
      by_contra! hz
      exact one_ne_zero <| hOne.symm.trans <| (hI 0).deriv.symm.trans <| by
        simp [show I = 0 from funext hz]
    have hEq (s : ℝ) : g s = (I (s + b) - I s) / I b := by
      rw [eq_div_iff hb, eq_sub_iff_add_eq']
      dsimp only [I]
      rw [← intervalIntegral.integral_const_mul]
      simp only [← hMul, intervalIntegral.integral_comp_add_left, add_zero]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    rw [show g = _ from funext hEq]
    exact (((hI (0 + b)).differentiableAt.comp (0 : ℝ) (differentiableAt_id.add_const b)).sub
      (hI 0).differentiableAt).div_const (I b)
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let a : ℝ → InfiniteAdeleRing F := fun s ↦ (γ (E s)).val.1
  have hExpAdd (s t : ℝ) : E (s + t) = E s * E t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add s t))
  have ha : Continuous a :=
    continuous_fst.comp (Units.continuous_val.comp (γ.continuous.comp E.continuous))
  have haZero : a 0 = 1 := by
    have hExpZero : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
    change (γ (E 0)).val.1 = 1
    rw [hExpZero, map_one]
    rfl
  have haAdd (s t : ℝ) : a (s + t) = a s * a t := by
    show (γ (E (s + t))).val.1 = _
    rw [hExpAdd, map_mul]
    rfl
  let b (s : ℝ) (v : {v : InfinitePlace F // v.IsReal}) :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (a s v)
  let c (s : ℝ) (v : {v : InfinitePlace F // v.IsComplex}) :=
    InfinitePlace.Completion.extensionEmbedding v.1 (a s v)
  have hb : DifferentiableAt ℝ b 0 := differentiableAt_pi.mpr fun v ↦
    hScalar _ ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      ((continuous_apply v.1).comp ha)) (by
        show InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (a 0 v) = 1
        rw [haZero]
        exact map_one _) (fun s t ↦ by
        show InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (a (s + t) v) = _
        rw [haAdd]
        exact map_mul _ _ _)
  have hc : DifferentiableAt ℝ c 0 := differentiableAt_pi.mpr fun v ↦
    hScalar _ ((InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      ((continuous_apply v.1).comp ha)) (by
        show InfinitePlace.Completion.extensionEmbedding v.1 (a 0 v) = 1
        rw [haZero]
        exact map_one _) (fun s t ↦ by
        show InfinitePlace.Completion.extensionEmbedding v.1 (a (s + t) v) = _
        rw [haAdd]
        exact map_mul _ _ _)
  exact hb.prodMk hc

/-- Pulling a Schwartz–Bruhat function back along a translate of a continuous
homomorphism from a real normed vector space gives a differentiable function. -/
private theorem schwartzBruhat_differentiableAt_comp_translate
    {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Multiplicative E →ₜ* G) (f : SchwartzBruhat G) (x : G) (z : E) :
    DifferentiableAt ℝ (fun y : E ↦ f (x * i (Multiplicative.ofAdd y))) z := by
  classical
  let v : E → G := fun y ↦ x * i (Multiplicative.ofAdd y)
  let fs : schwartzBruhatSubmodule G := f
  change DifferentiableAt ℝ (fs.val ∘ v) z
  refine Submodule.iSup_induction (motive := fun g : G → ℂ ↦
    DifferentiableAt ℝ (g ∘ v) z) _
    fs.property (fun a g hg ↦ ?_) (differentiableAt_const _) (fun _ _ hg hh ↦ hg.add hh)
  refine Submodule.iSup_induction (motive := fun g : G → ℂ ↦
    DifferentiableAt ℝ (g ∘ v) z) _ hg
    (fun e g ⟨s, hs⟩ ↦ ?_) (differentiableAt_const _) (fun _ _ hg hh ↦ hg.add hh)
  subst g
  let U : OpenSubgroup G := ⟨a.val.1, a.property.1⟩
  have hi : Continuous (fun y : E ↦ i (Multiplicative.ofAdd y)) := i.continuous
  have hiMem (y : Multiplicative E) : i y ∈ U :=
    (isPreconnected_range hi).subset_isClopen U.isClopen
      ⟨1, ⟨0, map_one i⟩, U.one_mem⟩ (mem_range_self y.toAdd)
  by_cases hx : x ∈ U
  · let iU : Multiplicative E →* a.val.1 :=
      i.toMonoidHom.codRestrict a.val.1 hiMem
    let q : a.val.1 →* a.quotient := QuotientGroup.mk' _
    let c : E →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
      AddMonoidHom.toMultiplicative.symm (e.equiv.toMulEquiv.toMonoidHom.comp (q.comp iU))
    have hc : Continuous c :=
      e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp (i.continuous.subtype_mk hiMem))
    let cR := (AddMonoidHom.fst _ _).comp c
    let cT := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp c)
    let L := cR.toRealLinearMap hc.fst
    have hD (y : E) : (c y).2.2 = 0 :=
      (hc.snd.snd.isConst_of_preconnectedSpace y 0).trans (by rw [map_zero]; rfl)
    have hLift (j : Fin e.torusDim) :
        ∃ l : E →L[ℝ] ℝ, ∀ y, (l y : AddCircle (1 : ℝ)) = (c y).2.1 j := by
      let χ := (Pi.evalAddMonoidHom _ j).comp cT
      have hχ : Continuous χ := (continuous_apply j).comp hc.snd.fst
      exact exists_addCircle_coe_linearMap_eq χ hχ
    choose l hl using hLift
    let W := EuclideanSpace ℝ (Fin e.torusDim)
    let M : E →L[ℝ] W :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e.torusDim ↦ ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi l)
    let y₀ := (e.equiv (q ⟨x, hx⟩)).toAdd
    obtain ⟨w, hw⟩ := elementaryCover_surjective y₀.2.2.1 y₀.2.2.2 y₀.1 y₀.2.1
    have hCover (y : E) :
        elementaryCover (y₀.1 + L y, w + M y) y₀.2.2.1 y₀.2.2.2 = y₀ + c y := by
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · funext j
        have hwj := congrArg (fun r : ElementaryLieGroup e.realDim e.torusDim e.latticeRank
          e.finiteFactor ↦ r.2.1 j) hw
        change ((w j + l j y : ℝ) : AddCircle (1 : ℝ)) = y₀.2.1 j + (c y).2.1 j
        rw [AddCircle.coe_add, show (w j : AddCircle (1 : ℝ)) = y₀.2.1 j from hwj, hl]
      · change y₀.2.2 = y₀.2.2 + (c y).2.2
        rw [hD, add_zero]
    let ss : elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor := s
    have hs : Differentiable ℝ (fun b ↦ s (elementaryCover b y₀.2.2.1 y₀.2.2.2)) :=
      (ss.property.1 _ _).differentiable (by simp)
    have hp : Differentiable ℝ (fun y : E ↦ (y₀.1 + L y, w + M y)) :=
      (L.differentiable.const_add _).prodMk (M.differentiable.const_add _)
    convert (hs.comp hp) z using 1
    funext y
    have hyU : v y ∈ a.val.1 := U.mul_mem hx (hiMem (Multiplicative.ofAdd y))
    rw [Function.comp_apply, schwartzBruhatStageRealization_apply, dite_eq_left hyU]
    apply congrArg (fun r ↦ s r)
    rw [hCover]
    change (e.equiv (q (⟨v y, hyU⟩ : a.val.1))).toAdd =
      (e.equiv (q (⟨x, hx⟩ : a.val.1)) * e.equiv (q (iU (Multiplicative.ofAdd y)))).toAdd
    rw [← map_mul, ← map_mul]
    exact congrArg (fun j : a.val.1 ↦ (e.equiv (q j)).toAdd) (Subtype.ext rfl)
  · have hn (y : E) : v y ∉ U := fun hy ↦ hx (by
      have h := U.mul_mem hy (U.inv_mem (hiMem (Multiplicative.ofAdd y)))
      simpa [v] using h)
    convert (differentiableAt_const (x := z) (c := (0 : ℂ))) using 1
    funext y
    exact (schwartzBruhatStageRealization_apply a e s (v y)).trans (dite_eq_right (hn y))

/-- Paper: Lemma 2.2.4.2, p. 87. An adelic Schwartz–Bruhat function is
differentiable in the Archimedean coordinates at each fixed finite adele. -/
private theorem adeleSchwartz_infinite_differentiableAt (f : ℬ[F])
    (x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    DifferentiableAt ℝ (fun a : mixedEmbedding.mixedSpace F ↦
      f (Multiplicative.ofAdd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, x))) z := by
  classical
  let E := mixedEmbedding.mixedSpace F
  let eArch := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hInv : Continuous eArch.symm := continuous_infiniteAdeleRingEquivMixedSpace_symm F
  let i : E →+ 𝔸[F] := eArch.symm.toAddMonoidHom.prod (0 : E →+ _)
  have hi : Continuous i := hInv.prodMk continuous_const
  let j : Multiplicative E →ₜ* Multiplicative 𝔸[F] := ⟨i.toMultiplicative, hi⟩
  have h := schwartzBruhat_differentiableAt_comp_translate j f
    (Multiplicative.ofAdd (0, x)) z
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  exact congrArg (fun p : 𝔸[F] ↦ f (Multiplicative.ofAdd p))
    (Prod.ext (zero_add _).symm (add_zero _).symm)

/-- Paper: Lemma 2.2.4.2, p. 87. The logarithmic dilation orbit of a
Schwartz–Bruhat function has a derivative at zero. -/
private theorem adeleOrbit_differentiableAt (f : ℬ[F]) (x : Multiplicative 𝔸[F]) :
    DifferentiableAt ℝ
      (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val * x.toAdd))) 0 := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let a : ℝ → mixedEmbedding.mixedSpace F := fun s ↦ e (γ (expUnit s)).val.1 * e x.toAdd.1
  have hγ := adeleOneParameter_infinite_differentiableAt γ
  have hb : DifferentiableAt ℝ (fun s : ℝ ↦ (a s).1) 0 := differentiableAt_pi.mpr fun v ↦
    (differentiableAt_pi.mp hγ.fst v).mul_const _
  have hc : DifferentiableAt ℝ (fun s : ℝ ↦ (a s).2) 0 := differentiableAt_pi.mpr fun v ↦
    (differentiableAt_pi.mp hγ.snd v).mul_const _
  have ha : DifferentiableAt ℝ a 0 := hb.prodMk hc
  have h := (adeleSchwartz_infinite_differentiableAt f x.toAdd.2 (a 0)).comp (0 : ℝ) ha
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  let b := (γ (expUnit s)).val.1
  let c := (γ (expUnit s)).val.2
  have hArch : b * x.toAdd.1 = e.symm (a s) := by
    change _ = e.symm (e b * e x.toAdd.1)
    rw [← e.map_mul, e.symm_apply_apply]
  have hFin : c * x.toAdd.2 = x.toAdd.2 :=
    (congrArg (· * x.toAdd.2) (adeleOneParameter_finite_eq_one γ (expUnit s))).trans (one_mul _)
  exact congrArg (fun y : 𝔸[F] ↦ f (Multiplicative.ofAdd y)) (Prod.ext hArch hFin)

/-- Paper: Lemma 2.2.4.2, p. 87. Formation of the directional derivative is
complex linear on the adelic Schwartz–Bruhat space. -/
theorem adeleDirectionalDeriv_isLinear :
    IsLinearMap ℂ (fun f : ℬ[F] ↦
      (⟨orbitDeriv γ f, adeleDirectionalDeriv_mem γ f⟩ : ℬ[F])) := by
  constructor
  · intro f g
    apply Subtype.ext
    funext x
    exact deriv_add (adeleOrbit_differentiableAt γ f x) (adeleOrbit_differentiableAt γ g x)
  · intro c f
    apply Subtype.ext
    funext x
    exact deriv_fun_const_smul_field c _

/-- Paper: Equation (2.2.4.2), p. 87. The directional derivative differentiates
`f (γ(t) x)` at `t = 1` and is a complex-linear endomorphism.
Deviation: The definition uses the equivalent parameter `t = exp s` at `s = 0`,
as in (2.2.4.4). -/
def adeleDirectionalDeriv : ℬ[F] →ₗ[ℂ] ℬ[F] :=
  IsLinearMap.mk' _ (adeleDirectionalDeriv_isLinear γ)

section ArchimedeanContinuity

open scoped Classical Uniformity
open TopologicalSpace (MetrizableSpace)

local notation "mixed" => InfiniteAdeleRing.ringEquiv_mixedSpace F

/-- A purely real elementary presentation yields a Schwartz–Bruhat stage with
the full group and trivial kernel. -/
private theorem schwartzBruhat_euclidean_stage {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {m : ℕ}
    (w : G ≃ₜ* Multiplicative (ElementaryLieGroup m 0 0 PUnit.{1})) :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      ∃ J : ElementarySchwartz m 0 0 PUnit.{1} ≃L[ℂ] SchwartzBruhatStage e,
        ∀ s x, schwartzBruhatStageRealization a e (J s) x = s (w x).toAdd := by
  classical
  let p : ElementaryLCAPresentation G :=
    { realDim := m, torusDim := 0, latticeRank := 0, finiteFactor := PUnit.{1}
      equiv := w }
  have hG : IsCompactlyGeneratedGroup G ∧ IsLocallyEuclidean G :=
    (lca_elementary_iff (G := G)).mpr ⟨p⟩
  have hcg := hG.1
  have hloc := hG.2
  let t : (⊤ : Subgroup G) ≃ₜ* G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair G := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv t.symm hcg,
    isBruhatGoodSubgroup_bot_iff.mpr hloc, bot_le⟩
  let q : a.quotient ≃* G :=
    QuotientGroup.quotientKerEquivOfRightInverse a.val.1.subtype t.symm (fun _ ↦ rfl)
  have hq (x : a.val.1) : q (QuotientGroup.mk x) = x.val := rfl
  let q' : a.quotient ≃ₜ* G :=
    { q with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (continuous_subtype_val.congr fun x ↦ (hq x).symm)
      continuous_invFun := QuotientGroup.continuous_mk.comp t.symm.continuous }
  let e : ElementaryLCAPresentation a.quotient :=
    { realDim := m, torusDim := 0, latticeRank := 0, finiteFactor := PUnit.{1}
      equiv := q'.trans p.equiv }
  refine ⟨a, e, ContinuousLinearEquiv.refl ℂ _, fun s x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply, dite_eq_left (Subgroup.mem_top _)]
  rfl

omit [NumberField F] in
/-- The mixed archimedean coordinates followed by a Euclidean linear equivalence
give a purely real elementary presentation. -/
private theorem archimedeanMixedSpace_equiv
    {m : ℕ} (L : mixedEmbedding.mixedSpace F ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ w : Multiplicative (InfiniteAdeleRing F) ≃ₜ*
        Multiplicative (ElementaryLieGroup m 0 0 PUnit.{1}),
      ∀ x : InfiniteAdeleRing F, (w (Multiplicative.ofAdd x)).toAdd =
        (L (mixed x), 0, 0, 0) := by
  classical
  let G := Multiplicative (InfiniteAdeleRing F)
  let E := EuclideanSpace ℝ (Fin m)
  let P := ElementaryLieGroup m 0 0 PUnit.{1}
  let B := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit.{1}
  let : Unique B := uniqueOfSubsingleton 0
  let M := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hm := continuous_infiniteAdeleRingEquivMixedSpace F
  have hMi := continuous_infiniteAdeleRingEquivMixedSpace_symm F
  let w : G ≃* Multiplicative P :=
    AddEquiv.toMultiplicative
      (M.toAddEquiv.trans (L.toLinearEquiv.toAddEquiv.trans
        (AddEquiv.prodUnique (M := E) (N := B)).symm))
  have hw : Continuous w := (L.continuous.comp hm).prodMk continuous_const
  have hw' : Continuous w.symm := hMi.comp (L.symm.continuous.comp continuous_fst)
  exact ⟨⟨w, hw, hw'⟩, fun _ ↦ rfl⟩

/-- The purely real elementary Schwartz space has the classical Schwartz topology. -/
private theorem elementarySchwartz_euclidean_equiv (m : ℕ) :
    ∃ J : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ ≃L[ℂ] ElementarySchwartz m 0 0 PUnit.{1},
      ∀ f x, J f x = f x.1 := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let S := SchwartzMap E ℂ
  let T := ElementarySchwartz m 0 0 PUnit.{1}
  let P := ElementaryLieGroup m 0 0 PUnit.{1}
  let A : S →ₗ[ℂ] T :=
    { toFun := fun f ↦ ⟨fun x : P ↦ f x.1,
        (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hA (f : S) (x : P) : A f x = f x.1 := rfl
  have hSurj : Surjective A := by
    intro s
    have hs (x : P) : s (x.1, 0, 0, 0) = s x :=
      congrArg s (Prod.ext rfl (Subsingleton.elim _ _))
    obtain ⟨f, hf⟩ :=
      (elementarySchwartzSubmodule_real_iff (fun x : E ↦ s (x, 0, 0, 0))).mp
        (show (fun x : P ↦ s (x.1, 0, 0, 0)) ∈ elementarySchwartzSubmodule m 0 0 PUnit.{1} by
          rw [show (fun x : P ↦ s (x.1, 0, 0, 0)) = s.val from funext hs]
          exact s.property)
    refine ⟨f, Subtype.ext (funext fun x ↦ ?_)⟩
    exact (congrFun hf x.1).trans (hs x)
  let e := LinearEquiv.ofBijective A ⟨fun f g h ↦ SchwartzMap.ext fun x ↦
    congrArg (fun s : T ↦ s (x, 0, 0, 0)) h, hSurj⟩
  let : BarrelledSpace ℂ S := isFrechetTVS_barrelled (euclideanSchwartz_frechet m)
  have hc : Continuous A :=
    continuous_toElementarySchwartz_of_eval A fun x ↦
      ⟨(BoundedContinuousFunction.evalCLM ℂ x.1).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ), fun _ ↦ rfl⟩
  obtain ⟨hadd, -, hmetric, hcomplete⟩ := elementarySchwartz_isFrechet (m := m) (n := 0)
    (r := 0) (F := PUnit.{1})
  have : MetrizableSpace T := hmetric
  have : CompleteSpace T := by
    rw [← IsUniformAddGroup.rightUniformSpace_eq (G := T)]
    exact hcomplete
  have : (uniformity T).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero T]
    infer_instance
  have : CompleteSpace S := completeSpace_schwartzMap
  have ho : IsOpenMap A := by
    have h : ¬ IsMeagre (range (A : S → T)) := by
      rw [hSurj.range_eq]
      exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
    exact isOpenMap_of_not_isMeagre_range (⟨A, hc⟩ : S →L[ℂ] T) h
  exact ⟨⟨e, hc, e.toEquiv.continuous_symm_iff.mpr ho⟩, hA⟩

/-- A Euclidean stage which realizes every Schwartz–Bruhat function gives a topological
equivalence by pointwise pullback. -/
private theorem schwartzBruhat_equiv_of_stage
    {G V : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (T : SchwartzMap V ℂ ≃L[ℂ] SchwartzBruhatStage e)
    (coord : G → V)
    (hT : ∀ f x, schwartzBruhatStageRealization a e (T f) x = f (coord x))
    (hSchwartz : ∀ s : SchwartzBruhat G, ∃ f : SchwartzMap V ℂ, ∀ x, f (coord x) = s x) :
    ∃ J : SchwartzMap V ℂ ≃L[ℂ] SchwartzBruhat G, ∀ f x, J f x = f (coord x) := by
  let I : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  let A := I.comp T.toLinearEquiv.toLinearMap
  have hA (f : SchwartzMap V ℂ) (x : G) : A f x = f (coord x) := hT f x
  have hI : IsEmbedding I := schwartzBruhatStage_isEmbedding a e
  have hEmb : IsEmbedding A := hI.comp T.toHomeomorph.isEmbedding
  have hSurj : Surjective A := by
    intro s
    obtain ⟨f, hf⟩ := hSchwartz s
    exact ⟨f, Subtype.ext (funext fun x ↦ (hA f x).trans (hf x))⟩
  let B := LinearEquiv.ofBijective A ⟨hEmb.injective, hSurj⟩
  refine ⟨⟨B, hEmb.continuous, hEmb.continuous_iff.mpr ?_⟩, hA⟩
  exact continuous_id.congr fun f ↦ (B.apply_symm_apply f).symm

/-- A real linear coordinate change identifies classical Schwartz functions with
the corresponding purely real elementary stage. -/
private theorem schwartz_equiv_of_euclidean_coordinates
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ}
    (L : V ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ K : SchwartzMap V ℂ ≃L[ℂ] ElementarySchwartz m 0 0 PUnit.{1},
      ∀ f x, K f (L x, 0, 0, 0) = f x := by
  obtain ⟨K, hK⟩ := elementarySchwartz_euclidean_equiv m
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (F := ℂ)
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (F := ℂ)
  let C := ContinuousLinearEquiv.equivOfInverse P Q
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.symm_apply_apply x))
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.apply_symm_apply x))
  refine ⟨C.trans K, fun f x ↦ ?_⟩
  change K (P f) (L x, 0, 0, 0) = _
  rw [hK]
  exact congrArg f (L.symm_apply_apply x)

/-- Pullback in mixed coordinates identifies the classical and archimedean
Schwartz–Bruhat spaces as topological complex vector spaces. -/
private theorem archimedeanSchwartzBruhat_equiv :
    ∃ J : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ ≃L[ℂ]
        SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)),
      ∀ f x, J f (Multiplicative.ofAdd x) = f (mixed x) := by
  let V := mixedEmbedding.mixedSpace F
  let G := Multiplicative (InfiniteAdeleRing F)
  let m := Module.finrank ℝ V
  let E := EuclideanSpace ℝ (Fin m)
  let L : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E, m, finrank_euclideanSpace])
  refine Exists.elim (archimedeanMixedSpace_equiv (F := F) (m := m) L) fun w hw ↦ ?_
  have : IsTopologicalGroup G := inferInstanceAs (IsTopologicalGroup
    (Multiplicative (InfiniteAdeleRing F)))
  have : LocallyCompactSpace G := InfiniteAdeleRing.locallyCompactSpace F
  have : T2Space G := w.toHomeomorph.isEmbedding.t2Space
  have : SecondCountableTopology G := w.toHomeomorph.isEmbedding.secondCountableTopology
  let coord : G → V := fun x ↦ mixed x.toAdd
  refine Exists.elim (schwartzBruhat_euclidean_stage (G := G) w) fun a ha ↦ ?_
  refine Exists.elim ha fun e he ↦ ?_
  refine Exists.elim he fun J hJ ↦ ?_
  refine Exists.elim (schwartz_equiv_of_euclidean_coordinates L) fun K hK ↦ ?_
  refine schwartzBruhat_equiv_of_stage a e (K.trans J) coord (fun f x ↦ ?_) fun s ↦
      (mem_archimedeanSchwartzBruhat_iff (fun x ↦ s (Multiplicative.ofAdd x))).mp s.property
  change schwartzBruhatStageRealization a e (J (K f)) x = f (mixed x.toAdd)
  exact (hJ (K f) x).trans ((congrArg (K f) (hw x.toAdd)).trans (hK f (mixed x.toAdd)))

/-- The classical differential paired with the dilation velocity transports to a
continuous directional derivative on the Schwartz–Bruhat space. -/
private theorem schwartzBruhat_dilation_of_coordinates
    {G V : Type*} [CommGroup G] [TopologicalSpace G] [NormedCommRing V] [NormedAlgebra ℝ V]
    (J : SchwartzMap V ℂ ≃L[ℂ] SchwartzBruhat G)
    (coord : G → V) (hJ : ∀ f x, J f x = f (coord x))
    (curve : ℝ → V) (hCurve : DifferentiableAt ℝ curve 0) (hZero : curve 0 = 1)
    (orbit : ℝ → G → G) (hOrbit : ∀ s x, coord (orbit s x) = curve s * coord x) :
    ∃ D : SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ f x, D f x = deriv (fun s : ℝ ↦ f (orbit s x)) 0 := by
  let L : V →L[ℝ] V := ContinuousLinearMap.mul ℝ V (deriv curve 0)
  let P := SchwartzMap.fderivCLM ℂ V ℂ
  let Q := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ).flip L.hasTemperateGrowth
  let D : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
    { toFun := fun f ↦ Q (P f)
      map_add' := fun f g ↦ by
        change Q (P (f + g)) = _
        rw [map_add, map_add]
      map_smul' := fun c f ↦ by
        change Q (P (c • f)) = c • Q (P f)
        rw [map_smul]
        exact SchwartzMap.ext fun _ ↦ rfl
      cont := Q.continuous.comp P.continuous }
  refine ⟨J.toContinuousLinearMap.comp (D.comp J.symm.toContinuousLinearMap), fun f x ↦ ?_⟩
  let g := J.symm f
  have hg (y : G) : g (coord y) = f y := by rw [← hJ, J.apply_symm_apply]
  have hDeriv : HasDerivAt (fun s ↦ curve s * coord x) (L (coord x)) 0 :=
    hCurve.hasDerivAt.mul_const (coord x)
  have hG : HasFDerivAt g (fderiv ℝ g (coord x)) (curve 0 * coord x) := by
    rw [hZero, one_mul]
    exact g.hasFDerivAt _
  have hEval : (fun s ↦ g (curve s * coord x)) = fun s ↦ f (orbit s x) := by
    funext s
    rw [← hg, hOrbit]
  change J (D g) x = _
  rw [hJ, ← hEval]
  exact (hG.comp_hasDerivAt 0 hDeriv).deriv.symm

/-- Paper: Lemma 2.2.4.2, pp. 87–88. Differentiation of the archimedean orbit
in the logarithmic parameter is a continuous complex-linear operator on
archimedean Schwartz–Bruhat functions. -/
theorem exists_archimedeanDirectionalDeriv :
    ∃ D : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) →L[ℂ]
        SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)),
      ∀ (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) (x : InfiniteAdeleRing F),
        D f (Multiplicative.ofAdd x) =
          deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x))) 0 := by
  refine Exists.elim (archimedeanSchwartzBruhat_equiv (F := F)) fun J hJ ↦ ?_
  let V := mixedEmbedding.mixedSpace F
  let G := Multiplicative (InfiniteAdeleRing F)
  let M := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let curve : ℝ → V := fun s ↦ M (γ (expUnit s)).val.1
  have hOne : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hZero : curve 0 = 1 := by
    have hγ : γ (expUnit (0 : ℝ)) = 1 := (congrArg γ hOne).trans (map_one γ)
    exact (congrArg (fun u : 𝕀[F] ↦ M u.val.1) hγ).trans (map_one M)
  let orbit (s : ℝ) (x : G) : G :=
    Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.toAdd)
  let coord (x : G) : V := M x.toAdd
  have hOrbit (s : ℝ) (x : G) : coord (orbit s x) = curve s * coord x :=
    M.map_mul _ _
  refine Exists.elim (schwartzBruhat_dilation_of_coordinates (G := G) (V := V)
    J coord (fun f x ↦ hJ f x.toAdd) curve
    (adeleOneParameter_archimedean_differentiable γ) hZero orbit hOrbit) fun D hD ↦ ?_
  exact ⟨D, fun f x ↦ hD f (Multiplicative.ofAdd x)⟩

end ArchimedeanContinuity

/-- Tensoring a continuous endomorphism with the identity is continuous for
the inductive tensor topology. -/
private theorem continuous_inductiveTensorMap_id {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] (L : A →L[ℂ] A) :
    Continuous (inductiveTensorMap L.toLinearMap (LinearMap.id (M := B))) := by
  let T := inductiveTensorMap L.toLinearMap (LinearMap.id (M := B))
  let hS := withGeneratingSeminorms_spec (A ⊗[ℂ] B)
    (fun p : {p : Seminorm ℂ (A ⊗[ℂ] B) //
      (∀ f : A, Continuous (fun g : B ↦ p (f ⊗ₜ[ℂ] g))) ∧
      (∀ g : B, Continuous (fun f : A ↦ p (f ⊗ₜ[ℂ] g)))} ↦ p.val)
  refine hS.continuous_of_continuous_comp T fun p ↦ ?_
  exact hS.continuous_seminorm
    ⟨p.val.comp T, fun f ↦ p.property.1 (L f), fun g ↦ (p.property.2 g).comp L.continuous⟩

/-- Paper: Lemma 2.2.4.2, p. 87. Formation of the directional derivative
is continuous in the Schwartz–Bruhat topology. -/
theorem adeleDirectionalDeriv_continuous : Continuous (adeleDirectionalDeriv γ) := by
  refine Exists.elim (adeleSchwartz_inductiveTensor_equiv F) fun e he ↦ ?_
  refine Exists.elim (exists_archimedeanDirectionalDeriv γ) fun D hD ↦ ?_
  let I := ContinuousLinearMap.id ℂ (SchwartzBruhat (Multiplicative 𝔸ᶠ[F]))
  let T := inductiveTensorMap D.toLinearMap I.toLinearMap
  have hleft : (adeleDirectionalDeriv γ).comp e.toLinearEquiv.toLinearMap =
      e.toLinearEquiv.toLinearMap.comp T := by
    apply TensorProduct.ext'
    intro f g
    apply Subtype.ext
    funext y
    let x := Multiplicative.toAdd y
    have hOrbit (s : ℝ) :
        e (f ⊗ₜ[ℂ] g)
            (Multiplicative.ofAdd ((γ (expUnit s)).val * x)) =
          f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1)) *
            g (Multiplicative.ofAdd x.2) := by
      have hfinite : ((γ (expUnit s)).val * x).2 = x.2 := by
        change (γ (expUnit s)).val.2 * x.2 = x.2
        rw [adeleOneParameter_finite_eq_one γ (expUnit s), one_mul]
      exact (he f g _).trans (congrArg (fun z : 𝔸ᶠ[F] ↦
        f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1)) *
          g (Multiplicative.ofAdd z)) hfinite)
    change deriv (fun s : ℝ ↦ e (f ⊗ₜ[ℂ] g)
      (Multiplicative.ofAdd ((γ (expUnit s)).val * x))) 0 =
        e (D f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x)
    let u (s : ℝ) := f (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x.1))
    let v := g (Multiplicative.ofAdd x.2)
    exact (congrArg (fun k : ℝ → ℂ ↦ deriv k 0) (funext hOrbit)).trans
      ((deriv_mul_const_field (u := u) v).trans
        ((congrArg (· * v) (hD f x.1).symm).trans (he (D f) g x).symm))
  have hcont : Continuous T :=
    continuous_inductiveTensorMap_id (B := SchwartzBruhat (Multiplicative 𝔸ᶠ[F])) D
  refine (e.continuous.comp (hcont.comp e.symm.continuous)).congr fun f ↦ ?_
  change e (T (e.symm f)) = adeleDirectionalDeriv γ f
  have h := DFunLike.congr_fun hleft (e.symm f)
  change adeleDirectionalDeriv γ (e (e.symm f)) = e (T (e.symm f)) at h
  simpa only [e.apply_symm_apply] using h.symm

/-- Paper: Lemma 2.2.4.2, p. 87. The difference quotient in the positive real
parameter converges to the directional derivative at every adele. -/
theorem adeleDirectionalDeriv_tendsto (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (f (Multiplicative.ofAdd ((γ t).val * x)) - f (Multiplicative.ofAdd x)) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 (adeleDirectionalDeriv γ f (Multiplicative.ofAdd x))) := by
  have hOrbit := (adeleOrbit_differentiableAt γ f (Multiplicative.ofAdd x)).hasDerivAt
  have hLog := hOrbit.scomp_of_eq (1 : ℝ) (Real.hasDerivAt_log one_ne_zero) Real.log_one.symm
  rw [inv_one, one_smul] at hLog
  have hVal : Tendsto valueℝ (𝓝[≠] (1 : ℝ≥0ˣ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc := NNReal.continuous_coe.comp (Units.continuous_val (M := ℝ≥0))
      exact (hc.continuousAt (x := (1 : ℝ≥0ˣ))).continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he ↦ ht (Units.val_injective (NNReal.coe_injective he))
  refine (hLog.tendsto_slope.comp hVal).congr' (Eventually.of_forall fun t ↦ ?_)
  have hExpLog : expUnit (Real.log (valueℝ t)) = t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
  have hZero : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  simp only [Function.comp_apply, slope_def_module, Real.log_one, hExpLog, hZero,
    map_one, Units.val_one, one_mul, toAdd_ofAdd, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_sub, Complex.ofReal_one, div_eq_inv_mul]

-- TODO(paper-gap): The last sentence of the proof of Lemma 2.2.4.2 uses
-- injectivity of γ∞. Lemma 2.2.4.1 only gives factorization through the infinite ideles.
-- TODO(paper-gap): The proof of Lemma 2.2.4.3 cites “Lemma ??” for closedness
-- of the section image and invokes the unrestricted bound from Lemma 2.2.2.1(3).

/-- If a Schwartz–Bruhat function represents the pointwise logarithmic orbit derivative,
its theta series gives the derivative of the original theta series. -/
private theorem adelicTheta_tendsto_of_orbitDeriv (f d : ℬ[F])
    (hd : ∀ x : Multiplicative 𝔸[F],
      HasDerivAt (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val * x.toAdd))) (d x) 0)
    (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (adelicTheta f (classOf (γ t) * g) - adelicTheta f g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adelicTheta d g)) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  let E : ℝ → ℝ≥0ˣ := expUnit
  have hE : Continuous E :=
    (Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous
  have hZero : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hAdd (s t : ℝ) : E (s + t) = E s * E t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_add s t))
  let x (ξ : Fˣ) (s : ℝ) : 𝔸[F] := (γ (E s) * a).val * algebraMap F 𝔸[F] (ξ : F)
  let term (φ : ℬ[F]) (ξ : Fˣ) (s : ℝ) := φ (Multiplicative.ofAdd (x ξ s))
  have hDeriv (ξ : Fˣ) (s : ℝ) : HasDerivAt (term f ξ) (term d ξ s) s := by
    have h : HasDerivAt
        (fun t : ℝ ↦ f (Multiplicative.ofAdd ((γ (E t)).val * x ξ s)))
        (term d ξ s) (s - s) := by
      simpa only [sub_self, toAdd_ofAdd] using hd (Multiplicative.ofAdd (x ξ s))
    refine (h.comp_sub_const s s).congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
    change f (Multiplicative.ofAdd (x ξ t)) =
      f (Multiplicative.ofAdd ((γ (E (t - s))).val * x ξ s))
    have hMul : γ (E t) = γ (E (t - s)) * γ (E s) := by
      rw [← map_mul γ, ← hAdd, sub_add_cancel]
    simp only [x, hMul, Units.val_mul, mul_assoc]
  let p (s : ℝ) : 𝕀[F] × 𝔸[F] := (γ (E s) * a, 0)
  have hp : Continuous p :=
    ((γ.continuous.comp hE).mul continuous_const).prodMk continuous_const
  let K := p '' Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hp
  have hAbs (φ : ℬ[F]) := adelicAverage_summableUniformlyOn φ K hK
  have hUniform : TendstoUniformlyOn (fun S s ↦ ∑ ξ ∈ S, term d ξ s)
      (fun s ↦ ∑' ξ, term d ξ s) atTop (Ioo (-1 : ℝ) 1) := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hAbs d).hasSumUniformlyOn.tendstoUniformlyOn ε hε] with S hS s hs
    have hmem : p s ∈ K := mem_image_of_mem p (Ioo_subset_Icc_self hs)
    have hsum : Summable (fun ξ ↦ ‖term d ξ s‖) := by
      simpa only [term, x, p, add_zero] using (hAbs d).summable hmem
    have htail := hS (p s) hmem
    simp only [p, add_zero] at htail
    change dist (∑' ξ, ‖term d ξ s‖) (∑ ξ ∈ S, ‖term d ξ s‖) < ε at htail
    rw [dist_eq_norm, ← hsum.sum_add_tsum_subtype_compl S, add_sub_cancel_left,
      Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)] at htail
    rw [dist_eq_norm, ← hsum.of_norm.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
    exact (norm_tsum_le_tsum_norm (hsum.subtype fun ξ ↦ ξ ∉ S)).trans_lt htail
  have hSeries : HasDerivAt (fun s ↦ ∑' ξ, term f ξ s) (∑' ξ, term d ξ 0) 0 := by
    refine hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hUniform
      (Eventually.of_forall fun S s _ ↦ HasDerivAt.fun_sum fun ξ _ ↦ hDeriv ξ s) ?_ (by simp)
    intro s hs
    have hmem : p s ∈ K := mem_image_of_mem p (Ioo_subset_Icc_self hs)
    have hsum : Summable (fun ξ ↦ ‖term f ξ s‖) := by
      simpa only [term, x, p, add_zero] using (hAbs f).summable hmem
    exact hsum.of_norm.hasSum
  have hTheta (φ : ℬ[F]) (s : ℝ) :
      (∑' ξ, term φ ξ s) = adelicTheta φ (classOf (γ (E s)) * classOf a) := by
    rw [← QuotientGroup.mk_mul, adelicTheta_mk]
    simp only [term, x, mul_comm]
  have hThetaZero (φ : ℬ[F]) : (∑' ξ, term φ ξ 0) = adelicTheta φ (classOf a) := by
    rw [hTheta, ← QuotientGroup.mk_mul, hZero, map_one, one_mul]
  have hLog := hSeries.scomp_of_eq (1 : ℝ) (Real.hasDerivAt_log one_ne_zero) Real.log_one.symm
  rw [inv_one, one_smul, hThetaZero] at hLog
  have hVal : Tendsto valueℝ (𝓝[≠] (1 : ℝ≥0ˣ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc := NNReal.continuous_coe.comp (Units.continuous_val (M := ℝ≥0))
      exact (hc.continuousAt (x := (1 : ℝ≥0ˣ))).continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he ↦ ht (Units.val_injective (NNReal.coe_injective he))
  refine (hLog.tendsto_slope.comp hVal).congr' (Eventually.of_forall fun t ↦ ?_)
  have hExpLog : E (Real.log (valueℝ t)) = t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
  rw [Function.comp_apply, slope_def_module, Function.comp_apply, Function.comp_apply,
    Real.log_one, hThetaZero, hTheta, hExpLog]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    div_eq_inv_mul]

/-- Paper: Lemma 2.2.4.3, p. 88. The difference quotient of theta along the
projected one-parameter subgroup converges to theta of the directional derivative.
The limit is continuous since it is a global theta function. -/
theorem adelicTheta_directionalDeriv (f : ℬ[F]) (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (adelicTheta f (classOf (γ t) * g) - adelicTheta f g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adelicTheta (adeleDirectionalDeriv γ f) g)) := by
  exact adelicTheta_tendsto_of_orbitDeriv γ f (adeleDirectionalDeriv γ f)
    (fun x ↦ (adeleOrbit_differentiableAt γ f x).hasDerivAt) g

end DirectionalDerivatives

section PolarHyperplanes

/-- Paper: Definition 2.2.4.4, p. 91. The evaluations of a test function and
its Fourier transform at zero are complex linear. -/
theorem adelePolarValues_isLinear :
    IsLinearMap ℂ (fun f : ℬ[F] ↦ (f zeroAdele, adeleSchwartzFourier f zeroAdele)) := by
  constructor
  · intro f g
    refine Prod.ext rfl ?_
    simp only [(adeleSchwartzFourier_apply_zero _).2]
    exact integral_add (adeleSchwartzFourier_apply_zero f).1
      (adeleSchwartzFourier_apply_zero g).1
  · intro c f
    refine Prod.ext rfl ?_
    simp only [(adeleSchwartzFourier_apply_zero _).2]
    exact integral_smul c (fun x ↦ f (Multiplicative.ofAdd x))

/-- Paper: Definition 2.2.4.4, p. 91. The two polar functionals are the
coordinates of the map that evaluates a test function and its transform at zero. -/
def adelePolarValues : ℬ[F] →ₗ[ℂ] ℂ × ℂ :=
  IsLinearMap.mk' _ (adelePolarValues_isLinear (F := F))

/-- Paper: Definition 2.2.4.4, p. 91. The polar functionals give the test
function and Fourier transform values at zero. -/
theorem adelePolarValues_apply (f : ℬ[F]) :
    adelePolarValues (F := F) f = (f zeroAdele, adeleSchwartzFourier f zeroAdele) := rfl

/-- Paper: Definition 2.2.4.4, p. 91. The intersection of the global polar
hyperplanes is the common kernel of the two polar functionals. -/
def adelePolarSubspace (F : Type*) [Field F] [NumberField F] : Submodule ℂ ℬ[F] :=
  LinearMap.ker (adelePolarValues (F := F))

/-- Paper: Definition 2.2.4.4, p. 91. A function belongs to the polar
subspace exactly when both it and its Fourier transform vanish at zero. -/
theorem mem_adelePolarSubspace (f : ℬ[F]) :
    f ∈ adelePolarSubspace F ↔ f zeroAdele = 0 ∧ adeleSchwartzFourier f zeroAdele = 0 :=
  LinearMap.mem_ker.trans Prod.mk_eq_zero

open scoped ENNReal in
/-- Point evaluation is continuous in the Schwartz–Bruhat topology since its
norm is bounded on each stage by the zeroth Schwartz seminorm. -/
private theorem schwartzBruhat_continuous_eval {G : Type*} [CommGroup G] [TopologicalSpace G]
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

/-- Integration against regular Haar measure is continuous on the Schwartz–Bruhat
space, since it evaluates the Fourier transform at the trivial character. -/
private theorem schwartzBruhat_continuous_integral {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    Continuous (fun f : SchwartzBruhat G ↦ ∫ x, f x ∂μ) := by
  obtain ⟨Fourier, hFourier⟩ := schwartzBruhat_fourier_equiv μ
  refine ((schwartzBruhat_continuous_eval (1 : PontryaginDual G)).comp Fourier.continuous).congr
    fun f ↦ ?_
  exact ((hFourier f).2 1).trans (lcaFourier_one μ f (hFourier f).1)

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Definition 2.2.4.4, p. 91. Both polar functionals are continuous,
expressed as continuity of the pair of evaluations. -/
theorem adelePolarValues_continuous : Continuous (adelePolarValues (F := F)) := by
  change Continuous (fun f : ℬ[F] ↦ (f zeroAdele, adeleSchwartzFourier f zeroAdele))
  refine (schwartzBruhat_continuous_eval zeroAdele).prodMk ?_
  let G := Multiplicative 𝔸[F]
  let : MeasurableSpace 𝔸[F] := borel _
  let μ : Measure G := additiveTamagawaMeasure F
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F ×
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : BorelSpace G := ⟨rfl⟩
  have hμ := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.1.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.1.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.1.map_add_left_eq_self x.toAdd }
  let : μ.Regular := hμ.2.1
  exact (schwartzBruhat_continuous_integral (G := G) μ).congr
    fun f ↦ (adeleSchwartzFourier_apply_zero f).2.symm

variable (γ : ℝ≥0ˣ →ₜ* 𝕀[F])

/-- Paper: Lemma 2.2.4.5(1), p. 91. The common polar kernel is closed in
the Schwartz–Bruhat topology. -/
theorem adelePolarSubspace_closed : IsClosed (adelePolarSubspace F : Set ℬ[F]) := by
  exact isClosed_singleton.preimage (adelePolarValues_continuous (F := F))

local instance adelicThetaAdeleMeasurableSpace : MeasurableSpace 𝔸[F] := borel _

open scoped ENNReal in
/-- Integrating a function after adelic dilation scales its integral by the reciprocal norm. -/
private theorem adeleIntegral_dilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝔸[F] → E) (hf : Integrable f (additiveTamagawaMeasure F)) (g : 𝕀[F]) :
    Integrable (fun x ↦ f (g.val * x)) (additiveTamagawaMeasure F) ∧
      (∫ x, f (g.val * x) ∂additiveTamagawaMeasure F) =
        (valueℝ (ideleNorm F g))⁻¹ • (∫ x, f x ∂additiveTamagawaMeasure F) := by
  let μ := additiveTamagawaMeasure F
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let d := (Homeomorph.smul (α := 𝔸[F]) g).toMeasurableEquiv
  have hmap : μ.map d = (↑(ideleNorm F g⁻¹).val : ℝ≥0∞) • μ := by
    ext s hs
    rw [Measure.map_apply d.measurable hs]
    change μ ((fun x : 𝔸[F] ↦ g • x) ⁻¹' s) = (↑(ideleNorm F g⁻¹).val : ℝ≥0∞) * μ s
    rw [← inv_inv g, Set.preimage_smul_inv]
    exact adeleHaar_mul_image F μ g⁻¹ s hs
  change Integrable (f ∘ d) μ ∧ (∫ x, f (d x) ∂μ) = _
  refine ⟨(integrable_map_equiv d f).mp (hmap.symm ▸ hf.smul_measure ENNReal.coe_ne_top), ?_⟩
  rw [← integral_map_equiv d f, hmap, integral_smul_measure]
  simp only [ENNReal.coe_toReal, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  rfl

/-- Converting a derivative in the logarithmic parameter to a slope on the positive reals. -/
private theorem tendsto_unit_slope_of_log_deriv (A : ℝ≥0ˣ → ℂ) (v : ℂ)
    (h : HasDerivAt (fun s : ℝ ↦ A (expUnit s)) v 0) :
    Tendsto (fun t : ℝ≥0ˣ ↦ (A t - A 1) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 v) := by
  have hLog := h.scomp_of_eq (1 : ℝ) (Real.hasDerivAt_log one_ne_zero) Real.log_one.symm
  rw [inv_one, one_smul] at hLog
  have hVal : Tendsto valueℝ (𝓝[≠] (1 : ℝ≥0ˣ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (NNReal.continuous_coe.comp (Units.continuous_val (M := ℝ≥0))).continuousAt.continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he ↦ ht (Units.val_injective (NNReal.coe_injective he))
  refine (hLog.tendsto_slope.comp hVal).congr' (Eventually.of_forall fun t ↦ ?_)
  have hExpLog : expUnit (Real.log (valueℝ t)) = t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
  have hZero : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  simp only [Function.comp_apply, slope_def_module, Real.log_one, hExpLog, hZero,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, div_eq_inv_mul]

private theorem hasDerivAt_of_shift {f g : ℝ → ℂ} {s : ℝ} {v : ℂ} (hg : HasDerivAt g v 0)
    (h : ∀ t, f t = g (t - s)) : HasDerivAt f v s := by
  have h' : HasDerivAt g v (s - s) := by simpa only [sub_self] using hg
  exact (h'.comp_sub_const s s).congr_of_eventuallyEq (.of_forall h)

/-- The physical dilation orbit differentiates by translating the derivative to the same point. -/
private theorem adele_dilation_orbit_hasDerivAt (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (f : ℬ[F]) (x : 𝔸[F]) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit t)).val * x)))
      (adeleDirectionalDeriv γ f (Multiplicative.ofAdd ((γ (expUnit s)).val * x))) s := by
  let g (u : ℝ) := γ (expUnit u)
  let y := (g s).val * x
  let a (t : ℝ) := f (Multiplicative.ofAdd ((g t).val * y))
  have h0 : HasDerivAt a (adeleDirectionalDeriv γ f (Multiplicative.ofAdd y)) 0 :=
    (adeleOrbit_differentiableAt γ f (Multiplicative.ofAdd y)).hasDerivAt
  refine hasDerivAt_of_shift h0 (fun t ↦ ?_)
  have hE : expUnit (t - s) * expUnit s = expUnit t :=
    Units.ext (NNReal.coe_inj.mp ((Real.exp_add (t - s) s).symm.trans (congrArg Real.exp (sub_add_cancel t s))))
  have hg : g (t - s) * g s = g t := (map_mul γ _ _).symm.trans (congrArg γ hE)
  change f (Multiplicative.ofAdd ((g t).val * x)) = f (Multiplicative.ofAdd ((g (t-s)).val * ((g s).val * x)))
  exact congrArg (fun z : 𝔸[F] ↦ f (Multiplicative.ofAdd z))
    ((congrArg (fun u : 𝕀[F] ↦ u.val * x) hg.symm).trans (mul_assoc _ _ _))

open scoped Pointwise in
/-- Fubini and the fundamental theorem of calculus along each dilation orbit give the
derivative of the norm-weighted Fourier transform, at every frequency. -/
private theorem fourier_dilation_hasDerivAt (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (f : ℬ[F]) (y : 𝔸[F]) :
    HasDerivAt (fun s : ℝ ↦ (valueℝ (ideleNorm F (γ (expUnit s))))⁻¹ •
      adeleSchwartzFourier f (Multiplicative.ofAdd ((γ (expUnit s))⁻¹.val * y)))
      (adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd y)) 0 := by
  let μ := additiveTamagawaMeasure F
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let : SigmaCompactSpace 𝔸[F] := by
    let : Countable F := Countable.of_moduleFinite (R := ℚ)
    let b := RingOfIntegers.basis F
    let D := adeleFundamentalDomain F b
    let K (q : F) := algebraMap F 𝔸[F] q +ᵥ closure D
    refine SigmaCompactSpace.of_countable (range K) (countable_range K) ?_ ?_
    · rintro _ ⟨q, rfl⟩
      exact IsCompact.vadd _ (adeleFundamentalDomain_precompact F b)
    · rw [sUnion_range]
      exact eq_top_mono (iUnion_mono fun _ ↦ vadd_set_mono (subset_closure (s := D)))
        (adeleFundamentalDomain_cover F b)
  let d := adeleDirectionalDeriv γ f
  let g (s : ℝ) := γ (expUnit s)
  let c (s : ℝ) := (valueℝ (ideleNorm F (g s)))⁻¹
  have hg : Continuous g := γ.continuous.comp
    ((Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous)
  have hg0 : g 0 = 1 := (congrArg γ (show expUnit (0 : ℝ) = 1 from
    Units.ext (NNReal.coe_inj.mp Real.exp_zero))).trans (map_one γ)
  have hc : Continuous c := by
    apply Continuous.inv₀ _ (fun s ↦ (NNReal.coe_pos.mpr (Units.zero_lt (ideleNorm F (g s)))).ne')
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp
      ((ideleGroup_topology F).2.2.2.2.1.comp hg))
  let orbit (s : ℝ) (x : 𝔸[F]) := Multiplicative.ofAdd ((g s).val * x)
  have hOrbit : Continuous (uncurry orbit) := continuous_ofAdd.comp
    (((Units.continuous_val.comp hg).comp continuous_fst).mul continuous_snd)
  let k (z : 𝔸[F]) (x : 𝔸[F]) := star (adeleStandardCharacter F (x * z) : ℂ)
  have hk (z) : Continuous (k z) := by
    obtain ⟨e, he, -⟩ := additiveTamagawaMeasure_selfDual F
    have h := (continuous_subtype_val.comp ((e (Multiplicative.ofAdd z)).continuous.comp
      continuous_ofAdd)).star
    refine h.congr fun x ↦ ?_
    change star ((e (Multiplicative.ofAdd z) (Multiplicative.ofAdd x)) : ℂ) = _
    rw [he, mul_comm z x]
  have hkn (z x) : ‖k z x‖ = 1 := by simp [k]
  let A (φ : ℬ[F]) (s : ℝ) := c s •
    adeleSchwartzFourier φ (Multiplicative.ofAdd ((g s)⁻¹.val * y))
  have hA (φ : ℬ[F]) : Continuous (A φ) :=
    hc.smul ((schwartzBruhat_continuous _).comp
      (continuous_ofAdd.comp ((Units.continuous_val.comp hg.inv).mul_const y)))
  have hAi (φ : ℬ[F]) (s : ℝ) :
      Integrable (fun x ↦ φ (orbit s x) * k y x) μ ∧
      (∫ x, φ (orbit s x) * k y x ∂μ) = A φ s := by
    let z := (g s)⁻¹.val * y
    let G (x : 𝔸[F]) := φ (Multiplicative.ofAdd x) * k z x
    have hG : Integrable G μ := ((adeleSchwartzFourier_apply_zero φ).1).mono
      (((schwartzBruhat_continuous φ).comp continuous_ofAdd).mul (hk z)).aestronglyMeasurable
      (.of_forall fun x ↦ by simp only [G, norm_mul, hkn, mul_one, le_refl])
    have hEq (x : 𝔸[F]) : G ((g s).val * x) = φ (orbit s x) * k y x := by
      have hh : (g s).val * (g s)⁻¹.val = 1 := (g s).val_inv
      simp only [G, k, orbit, z, mul_mul_mul_comm (g s).val x, hh, one_mul]
    have hdil := adeleIntegral_dilation G hG (g s)
    simp only [hEq] at hdil
    exact ⟨hdil.1, hdil.2.trans (by rfl)⟩
  have hDeriv (s : ℝ) (x : 𝔸[F]) :
      HasDerivAt (fun t ↦ f (orbit t x) * k y x) (d (orbit s x) * k y x) s :=
    (adele_dilation_orbit_hasDerivAt γ f x s).mul_const _
  have hFTC (b : ℝ) : (∫ s in 0..b, A d s) = A f b - A f 0 := by
    have hd := (adeleSchwartzFourier_apply_zero d).1
    have hcont : Continuous (uncurry (fun s x ↦ d (orbit s x) * k y x)) :=
      ((schwartzBruhat_continuous d).comp hOrbit).mul ((hk y).comp continuous_snd)
    have hprod : Integrable (uncurry (fun s x ↦ d (orbit s x) * k y x))
        ((volume.restrict (uIoc 0 b)).prod μ) := by
      apply (integrable_prod_iff hcont.aestronglyMeasurable).mpr
      refine ⟨.of_forall fun s ↦ (hAi d s).1, ?_⟩
      have hBound : IntegrableOn (fun s ↦ c s • (∫ x, ‖d (Multiplicative.ofAdd x)‖ ∂μ))
          (uIoc 0 b) volume :=
        (hc.smul continuous_const).integrableOn_Icc.mono_set uIoc_subset_uIcc
      refine hBound.congr (.of_forall fun s ↦ ?_)
      simp only [uncurry_apply_pair, norm_mul, hkn, mul_one]
      exact (adeleIntegral_dilation _ hd.norm (g s)).2.symm
    calc
      _ = ∫ s in 0..b, ∫ x, d (orbit s x) * k y x ∂μ :=
        intervalIntegral.integral_congr fun s _ ↦ (hAi d s).2.symm
      _ = ∫ x, (∫ s in 0..b, d (orbit s x) * k y x) ∂μ := intervalIntegral_integral_swap hprod
      _ = ∫ x, f (orbit b x) * k y x - f (orbit 0 x) * k y x ∂μ := by
        apply integral_congr_ae
        exact .of_forall fun x ↦ intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s _ ↦ hDeriv s x) ((hcont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 b)
      _ = _ := by rw [integral_sub (hAi f b).1 (hAi f 0).1, (hAi f b).2, (hAi f 0).2]
  have h := intervalIntegral.integral_hasDerivAt_right ((hA d).intervalIntegrable 0 0)
    (hA d).aestronglyMeasurable.stronglyMeasurableAtFilter (hA d).continuousAt
  have h' : HasDerivAt (A f) (A d 0) 0 := (h.add_const (A f 0)).congr_of_eventuallyEq
    (.of_forall fun s ↦ by change A f s = (∫ t in 0..s, A d t) + A f 0; rw [hFTC, sub_add_cancel])
  have hd0 : A d 0 = adeleSchwartzFourier d (Multiplicative.ofAdd y) := by
    simp [A, c, hg0]
  exact hd0 ▸ h'

/-- The integral of a directional derivative vanishes when the original integral vanishes.
-/
private theorem adeleDirectionalDeriv_integral_eq_zero (f : ℬ[F])
    (hf : (∫ x, f (Multiplicative.ofAdd x) ∂additiveTamagawaMeasure F) = 0) :
    (∫ x, adeleDirectionalDeriv γ f (Multiplicative.ofAdd x) ∂additiveTamagawaMeasure F) = 0 := by
  have H := fourier_dilation_hasDerivAt γ f 0
  have hz := (adeleSchwartzFourier_apply_zero f).2.trans hf
  simp only [mul_zero, hz, smul_zero] at H
  exact (adeleSchwartzFourier_apply_zero _).2.symm.trans (H.unique (hasDerivAt_const 0 0))

/-- Paper: Lemma 2.2.4.5(1), p. 91. Directional differentiation preserves the
common polar kernel, so it induces a linear map on the polar quotient. -/
theorem adeleDirectionalDeriv_preserves_polarSubspace :
    adelePolarSubspace F ≤ (adelePolarSubspace F).comap (adeleDirectionalDeriv γ) := by
  intro f hf
  change adeleDirectionalDeriv γ f ∈ adelePolarSubspace F
  refine (mem_adelePolarSubspace _).mpr ⟨?_, ?_⟩
  · change deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val * 0))) 0 = 0
    simp only [mul_zero, deriv_const]
  · rw [(adeleSchwartzFourier_apply_zero _).2]
    apply adeleDirectionalDeriv_integral_eq_zero γ f
    rw [← (adeleSchwartzFourier_apply_zero _).2]
    exact ((mem_adelePolarSubspace f).mp hf).2

/-- Extend an archimedean bump at zero by the indicator of the finite integral adeles. -/
private theorem exists_positive_polar_test :
    ∃ f : ℬ[F], f zeroAdele = 1 ∧ adeleSchwartzFourier f zeroAdele ≠ 0 := by
  classical
  let V := mixedEmbedding.mixedSpace F
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let L : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  let S : SchwartzMap E ℂ := (b.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let A := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L S
  let arch (y : InfiniteAdeleRing F) := A (InfiniteAdeleRing.ringEquiv_mixedSpace F y)
  let a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨arch ∘ Multiplicative.toAdd, (mem_archimedeanSchwartzBruhat_iff arch).mpr ⟨A, fun _ ↦ rfl⟩⟩
  let S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := ∅
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S₀
  let φ := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w : S₀, (0 : SchwartzBruhat (Multiplicative (w.val.adicCompletion F)))))
  let f := sAdeleSchwartzToGlobal F S₀ φ
  have hφ (x : SAdeleRing F S₀) : φ (Multiplicative.ofAdd x) = arch x.1 := by
    simpa [φ, S₀, arch, a] using he a (fun _ ↦ 0) x
  have hf (x : 𝔸[F]) : f (Multiplicative.ofAdd x) =
      if ∀ w, w ∉ S₀ → x.2 w ∈ w.adicCompletionIntegers F then
        (b (L (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)) : ℂ) else 0 := by
    rw [sAdeleSchwartzToGlobal_apply, hφ]
    rfl
  have h0 : f zeroAdele = 1 := by
    rw [hf, ite_eq_left (fun w _ ↦ (w.adicCompletionIntegers F).zero_mem)]
    change (b (L (InfiniteAdeleRing.ringEquiv_mixedSpace F 0)) : ℂ) = 1
    rw [map_zero, map_zero, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),
      Complex.ofReal_one]
  refine ⟨f, h0, ?_⟩
  let μ := additiveTamagawaMeasure F
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  have hInt := (adeleSchwartzFourier_apply_zero f).1
  have hpos : 0 < ∫ x, (f (Multiplicative.ofAdd x)).re ∂μ :=
    integral_pos_of_integrable_nonneg_ne_zero
      (Complex.continuous_re.comp ((schwartzBruhat_continuous f).comp continuous_ofAdd))
      hInt.re (fun x ↦ by rw [hf]; split_ifs <;> simp [b.nonneg]) (x := 0) (by rw [h0]; exact one_ne_zero)
  rw [(adeleSchwartzFourier_apply_zero f).2]
  intro hz
  exact hpos.ne' ((integral_re hInt).trans (congrArg Complex.re hz))

/-- A dilation of norm two preserves the first polar value and doubles the second. -/
private theorem exists_double_polar_integral (f : ℬ[F]) :
    ∃ d : ℬ[F], adelePolarValues (F := F) d =
      (f zeroAdele, 2 * adeleSchwartzFourier f zeroAdele) := by
  let t : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let g : 𝕀[F] := canonicalIdeleNormSection F t
  let d : ℬ[F] := schwartzBruhatUnitTranslate g f
  have hscale : (valueℝ (ideleNorm F g⁻¹))⁻¹ = 2 := by
    change (((ideleNorm F g⁻¹).val : ℝ))⁻¹ = 2
    rw [map_inv, show ideleNorm F g = t from canonicalIdeleNormSection_rightInverse F t,
      Units.val_inv_eq_inv_val, NNReal.coe_inv, inv_inv]
    norm_num [t]
  refine ⟨d, Prod.ext ?_ ?_⟩
  · change f (Multiplicative.ofAdd (g⁻¹.val * 0)) = f zeroAdele
    rw [mul_zero]
  · change adeleSchwartzFourier d zeroAdele = 2 * adeleSchwartzFourier f zeroAdele
    rw [(adeleSchwartzFourier_apply_zero d).2]
    change (∫ x, f (Multiplicative.ofAdd (g⁻¹.val * x)) ∂additiveTamagawaMeasure F) = _
    rw [(adeleIntegral_dilation _ (adeleSchwartzFourier_apply_zero f).1 g⁻¹).2,
      hscale, ← (adeleSchwartzFourier_apply_zero f).2, Complex.real_smul, Complex.ofReal_ofNat]

/-- Two inputs with respective values `(1,I)` and `(1,2I)` span the polar plane. -/
private theorem surjective_of_two_polar_values {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : V →ₗ[ℂ] ℂ × ℂ) (f d : V) (I : ℂ) (hI : I ≠ 0)
    (hf : P f = (1, I)) (hd : P d = (1, 2 * I)) : Surjective P := by
  rintro ⟨u, v⟩
  refine ⟨(2 * u - v / I) • f + (v / I - u) • d, ?_⟩
  rw [map_add, map_smul, map_smul, hf, hd]
  apply Prod.ext
  · change (2 * u - v / I) * 1 + (v / I - u) * 1 = u
    ring
  · change (2 * u - v / I) * I + (v / I - u) * (2 * I) = v
    linear_combination div_mul_cancel₀ v hI

/-- Paper: Equation (2.2.4.25), p. 91. The two polar evaluations are jointly
surjective, so they identify the quotient by their common kernel with `ℂ × ℂ`. -/
theorem adelePolarValues_surjective : Surjective (adelePolarValues (F := F)) := by
  refine (exists_positive_polar_test (F := F)).elim fun f hf ↦ ?_
  refine (exists_double_polar_integral f).elim fun d hd ↦ ?_
  exact surjective_of_two_polar_values (adelePolarValues (F := F)) f d
    (adeleSchwartzFourier f zeroAdele) hf.2 (Prod.ext hf.1 rfl)
    (hd.trans (congrArg (fun z : ℂ ↦ (z, 2 * adeleSchwartzFourier f zeroAdele)) hf.1))

/-- In the evaluation coordinates, a quotient endomorphism acts by its values on representatives. -/
private theorem quotKer_conjugate_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : V →ₗ[ℂ] ℂ × ℂ) (hP : Surjective P) (D : V →ₗ[ℂ] V)
    (hD : P.ker ≤ P.ker.comap D) (A : ℂ × ℂ → ℂ × ℂ) (h : ∀ f, P (D f) = A (P f)) (z : ℂ × ℂ) :
    let T := P.quotKerEquivOfSurjective hP
    T ((P.ker.mapQ P.ker D hD) (T.symm z)) = A z := by
  obtain ⟨f, rfl⟩ := hP z
  dsimp only
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact h f

/-- Paper: Lemma 2.2.4.5(2), p. 91. In the two evaluation coordinates on
the quotient, the induced derivative has diagonal entries `0` and `-α`,
where `α` is the norm exponent of the subgroup. -/
theorem adeleDirectionalDeriv_polarQuotient_diagonal (α : ℝ)
    (hα : ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α) (z : ℂ × ℂ) :
    let T : (ℬ[F] ⧸ adelePolarSubspace F) ≃ₗ[ℂ] ℂ × ℂ :=
      (adelePolarValues (F := F)).quotKerEquivOfSurjective (adelePolarValues_surjective (F := F))
    let D : (ℬ[F] ⧸ adelePolarSubspace F) →ₗ[ℂ] ℬ[F] ⧸ adelePolarSubspace F :=
      (adelePolarSubspace F).mapQ (τ₁₂ := RingHom.id ℂ) (adelePolarSubspace F)
        (adeleDirectionalDeriv (F := F) γ) (adeleDirectionalDeriv_preserves_polarSubspace (F := F) γ)
    T.toFun (D.toFun (T.symm.toFun z)) = (0, (-α) • z.2) := by
  refine quotKer_conjugate_apply (V := ℬ[F]) (adelePolarValues (F := F))
    (adelePolarValues_surjective (F := F)) (adeleDirectionalDeriv (F := F) γ)
    (adeleDirectionalDeriv_preserves_polarSubspace (F := F) γ) (fun w ↦ (0, (-α) • w.2)) ?_ z
  intro f
  apply Prod.ext
  · change deriv (fun s : ℝ ↦ f (Multiplicative.ofAdd ((γ (expUnit s)).val * 0))) 0 = 0
    simp only [mul_zero, deriv_const]
  · let I : ℂ := adeleSchwartzFourier f zeroAdele
    have h := fourier_dilation_hasDerivAt γ f 0
    have hc (s : ℝ) : (valueℝ (ideleNorm F (γ (expUnit s))))⁻¹ = Real.exp (-(s * α)) := by
      exact (congrArg Inv.inv (hα (expUnit s))).trans
        ((congrArg Inv.inv (Real.exp_mul s α).symm).trans (Real.exp_neg _).symm)
    simp only [mul_zero, hc] at h
    have he : HasDerivAt (fun s : ℝ ↦ Real.exp (-(s * α))) (-α) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const α).neg.exp)
    exact h.unique (he.smul_const I)

/-- Paper: Lemma 2.2.4.5(3), p. 92. The difference quotient of the Fourier
transform under inverse dilation, weighted by the reciprocal norm, converges
pointwise to the Fourier transform of the directional derivative. -/
theorem adeleDirectionalDeriv_fourier_tendsto (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      ((valueℝ (ideleNorm F (γ t)))⁻¹ •
          adeleSchwartzFourier f (Multiplicative.ofAdd (((γ t)⁻¹).val * x)) -
        adeleSchwartzFourier f (Multiplicative.ofAdd x)) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd x))) := by
  simpa only [map_one, inv_one, Units.val_one, one_mul, NNReal.coe_one, one_smul] using
    tendsto_unit_slope_of_log_deriv
      (fun t ↦ (valueℝ (ideleNorm F (γ t)))⁻¹ •
        adeleSchwartzFourier f (Multiplicative.ofAdd ((γ t)⁻¹.val * x)))
      _ (fourier_dilation_hasDerivAt γ f x)

section

open InfinitePlace.Completion
open scoped Classical

private abbrev rationalArchProjection : 𝔸[ℚ] →+* ℝ :=
  (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).comp
    ((Pi.evalRingHom _ Rat.infinitePlace).comp (RingHom.fst _ _))

/-- In every archimedean embedding, adelic scalar extension is the real projection. -/
private theorem rationalAdele_arch_scalar (v : InfinitePlace F) (a : 𝔸[ℚ]) :
    extensionEmbedding v ((rationalAdeleEmbedding F a).1 v) = (rationalArchProjection a : ℂ) := by
  classical
  let e := ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let lift (x : ℝ) : 𝔸[ℚ] := (Pi.single Rat.infinitePlace (e.symm x), 0)
  have hfst (b : 𝔸[ℚ]) : (lift (rationalArchProjection b)).1 = b.1 := by
    funext w
    obtain rfl := Subsingleton.elim w Rat.infinitePlace
    change Pi.single Rat.infinitePlace (e.symm (e _)) Rat.infinitePlace = _
    simp only [Pi.single_eq_same, e.symm_apply_apply]
    rfl
  let f := rationalAdeleEmbedding F
  let j (x : ℝ) := extensionEmbedding v ((f (lift x)).1 v)
  have hj : Continuous j := (isometry_extensionEmbedding v).continuous.comp
    ((continuous_apply v).comp (continuous_fst.comp ((rationalAdeleEmbedding_spec F).1.comp
      (((continuous_single Rat.infinitePlace).comp
        (isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous).prodMk continuous_const))))
  have hreal : j = Complex.ofReal := by
    apply (Rat.denseRange_cast (𝕜 := ℝ)).equalizer hj Complex.continuous_ofReal
    funext r
    let d := algebraMap ℚ 𝔸[ℚ] r
    have hd : rationalArchProjection d = (r : ℝ) := by simp [d]
    change extensionEmbedding v ((f (lift (r : ℝ))).1 v) = ((r : ℝ) : ℂ)
    rw [← hd, rationalAdeleEmbedding_fst_eq F _ _ (hfst d), (rationalAdeleEmbedding_spec F).2.1, hd]
    change extensionEmbedding v (algebraMap F v.Completion (algebraMap ℚ F r)) = _
    simp
  have h := congrFun hreal (rationalArchProjection a)
  change extensionEmbedding v ((f (lift (rationalArchProjection a))).1 v) = _ at h
  rwa [rationalAdeleEmbedding_fst_eq F _ _ (hfst a)] at h

/-- On a single infinite summand the adelic trace character is the real trace character
of its local field. The scalar archimedean idempotent kills the finite part of the trace. -/
private theorem archCharacter_single_trace (v : InfinitePlace F) {B : Type*} [Field B]
    [Algebra ℝ B] (e : v.Completion ≃+* B)
    (hc : ∀ a, e ((rationalAdeleEmbedding F a).1 v) = algebraMap ℝ B (rationalArchProjection a))
    (x : v.Completion) :
    adeleStandardCharacter F (Pi.single v x, 0) =
      Circle.exp (2 * Real.pi * Algebra.trace ℝ B (e x)) := by
  classical
  let := (rationalAdeleEmbedding F).toAlgebra
  let p := rationalArchProjection
  let q : 𝔸[F] →+* B := e.toRingHom.comp ((Pi.evalRingHom _ v).comp (RingHom.fst _ _))
  let s : B →+ 𝔸[F] :=
    { toFun := fun z ↦ (Pi.single v (e.symm z), 0)
      map_zero' := Prod.ext (by simp) rfl
      map_add' := fun z w ↦ Prod.ext (by
        change Pi.single v (e.symm (z + w)) = _
        rw [map_add, Pi.single_add]
        rfl) (zero_add _).symm }
  have hs (a : 𝔸[F]) (z : B) : s (q a * z) = a * s z := by
    apply Prod.ext
    · funext w
      change Pi.single v (e.symm (e (a.1 v) * z)) w = a.1 w * Pi.single v (e.symm z) w
      by_cases hw : w = v
      · subst w; simp
      · simp [Pi.single_eq_of_ne hw]
    · exact (mul_zero _).symm
  have hp : Surjective p := fun z ↦
    ⟨(Pi.single Rat.infinitePlace ((ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm z), 0), by
      let E := ringEquivRealOfIsReal Rat.isReal_infinitePlace
      change E (Pi.single Rat.infinitePlace (E.symm z) Rat.infinitePlace) = z
      rw [Pi.single_eq_same, E.apply_symm_apply]⟩
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  have hqs (z : B) : q (s z) = z := by change e (Pi.single v (e.symm z) v) = z; simp
  obtain ⟨_, htr⟩ := trace_of_algebra_projection b p hp q s hqs hc hs
  let u : 𝔸[ℚ] := (1,0)
  have hu : p u = 1 := map_one (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace)
  have hsx : u • s (e x) = s (e x) := by
    change rationalAdeleEmbedding F u * s (e x) = _
    rw [← hs, show q (rationalAdeleEmbedding F u) = _ from hc u, hu, map_one, one_mul]
  let t := Algebra.trace 𝔸[ℚ] 𝔸[F] (s (e x))
  have ht : u * t = t := by
    change u • Algebra.trace 𝔸[ℚ] 𝔸[F] (s (e x)) = _
    rw [← map_smul, hsx]
  have hfin : t.2 = 0 := by
    have h := congrArg Prod.snd ht
    change 0 * t.2 = t.2 at h
    simpa only [zero_mul] using h.symm
  have hins : s (e x) = (Pi.single v x, 0) := by change (Pi.single v (e.symm (e x)), _) = _; rw [e.symm_apply_apply]
  rw [← hins]
  exact (ratAdeleStandardCharacter_real t hfin).trans
    (congrArg (fun z : ℝ ↦ Circle.exp (2 * Real.pi * z)) (htr (e x)))

private theorem archCharacter_single (v : InfinitePlace F) (x : v.Completion) :
    adeleStandardCharacter F (Pi.single v x, 0) =
      Circle.exp (2 * Real.pi * ((v.mult : ℝ) * (extensionEmbedding v x).re)) := by
  rcases v.isReal_or_isComplex with hv | hv
  · let e := ringEquivRealOfIsReal hv
    have hc (a : 𝔸[ℚ]) : e ((rationalAdeleEmbedding F a).1 v) = rationalArchProjection a := by
      apply Complex.ofReal_injective
      exact (extensionEmbeddingOfIsReal_apply hv _).trans (rationalAdele_arch_scalar v a)
    rw [archCharacter_single_trace v e hc, Algebra.trace_self_apply, hv.mult_eq_one, Nat.cast_one,
      one_mul, ← extensionEmbeddingOfIsReal_apply hv, Complex.ofReal_re]
    rfl
  · rw [archCharacter_single_trace v (ringEquivComplexOfIsComplex hv) (rationalAdele_arch_scalar v),
      Algebra.trace_complex_apply, hv.mult_eq_two]
    rfl

/-- On the infinite adeles the standard character is the exponential of the sum of
the real traces, counted with the local multiplicities. -/
private theorem archCharacter_apply (z : InfiniteAdeleRing F) :
    adeleStandardCharacter F (z,0) = Circle.exp (2 * Real.pi *
      ∑ v : InfinitePlace F, (v.mult : ℝ) * (extensionEmbedding v (z v)).re) := by
  classical
  obtain ⟨d, hd, -⟩ := additiveTamagawaMeasure_selfDual F
  let ψ := d (Multiplicative.ofAdd (1 : 𝔸[F]))
  have hψ (y : 𝔸[F]) : ψ (Multiplicative.ofAdd y) = adeleStandardCharacter F y := by
    simpa only [one_mul] using hd (1 : 𝔸[F]) y
  let j : InfiniteAdeleRing F →+ 𝔸[F] := AddMonoidHom.inl _ _
  change adeleStandardCharacter F (j z) = _
  conv_lhs => rw [← hψ, ← Finset.univ_sum_single z, map_sum, ofAdd_sum, map_prod]
  rw [Finset.mul_sum]
  refine (Finset.prod_congr rfl fun v _ ↦ (hψ _).trans (archCharacter_single v (z v))).trans ?_
  let r (v : InfinitePlace F) := 2 * Real.pi * ((v.mult : ℝ) * (extensionEmbedding v (z v)).re)
  exact (congrArg Additive.toMul (map_sum Circle.expHom r Finset.univ)).symm

end

open scoped Classical in
/-- Multiplication by an archimedean coordinate on a pure tensor acts only on its
classical Schwartz factor. In particular each first absolute moment is finite. -/
private theorem adeleSchwartz_arch_moment (f : ℬ[F]) (v : InfinitePlace F) :
    Integrable (fun y : 𝔸[F] ↦ ‖f (Multiplicative.ofAdd y)‖ *
      ‖InfinitePlace.Completion.extensionEmbedding v (y.1 v)‖) (additiveTamagawaMeasure F) := by
  let V := mixedEmbedding.mixedSpace F
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  obtain ⟨L, hL⟩ : ∃ L : V →L[ℝ] ℂ, ∀ z, L (m z) =
      InfinitePlace.Completion.extensionEmbedding v (z v) := by
    rcases v.isReal_or_isComplex with hv | hv
    · refine ⟨Complex.ofRealCLM.comp ((ContinuousLinearMap.proj (R := ℝ) ⟨v, hv⟩).comp
        (ContinuousLinearMap.fst ℝ _ _)), fun z ↦ ?_⟩
      exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv _
    · refine ⟨(ContinuousLinearMap.proj (R := ℝ) ⟨v,hv⟩).comp
        (ContinuousLinearMap.snd ℝ _ _), fun _ ↦ rfl⟩
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B := SchwartzBruhat (Multiplicative 𝔸ᶠ[F])
  have lift (a : A) : ∃ d : A, ∀ y : InfiniteAdeleRing F,
      d (Multiplicative.ofAdd y) = L (m y) * a (Multiplicative.ofAdd y) := by
    obtain ⟨g, hg⟩ := (mem_archimedeanSchwartzBruhat_iff
      (fun z ↦ a (Multiplicative.ofAdd z))).mp a.property
    let D := SchwartzMap.smulLeftCLM ℂ L g
    have hm := (mem_archimedeanSchwartzBruhat_iff (fun y ↦ D (m y))).mpr ⟨D, fun _ ↦ rfl⟩
    refine ⟨⟨fun y ↦ D (m y.toAdd), hm⟩, fun y ↦ ?_⟩
    exact (SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) L.hasTemperateGrowth g (m y)).trans
      (congrArg (L (m y) * ·) (hg y))
  refine Exists.elim (adeleSchwartz_inductiveTensor_equiv F) fun e he ↦ ?_
  let E : (A ⊗[ℂ] B) ≃ₗ[ℂ] ℬ[F] := e.toLinearEquiv
  obtain ⟨n, a, b, hab⟩ := TensorProduct.exists_sum_tmul_eq (E.symm f)
  choose d hd using fun i ↦ lift (a i)
  let w : ℬ[F] := ∑ i, E (d i ⊗ₜ[ℂ] b i)
  have hw (y : 𝔸[F]) : w (Multiplicative.ofAdd y) = L (m y.1) * f (Multiplicative.ofAdd y) := by
    let ev : ℬ[F] →ₗ[ℂ] ℂ := (LinearMap.proj (Multiplicative.ofAdd y)).comp (schwartzBruhatSubmodule _).subtype
    have hf : f = ∑ i, E (a i ⊗ₜ[ℂ] b i) :=
      (E.apply_symm_apply f).symm.trans ((congrArg E hab).trans (map_sum E _ _))
    change ev w = L (m y.1) * ev f
    have hf' : ev f = ∑ i, ev (E (a i ⊗ₜ[ℂ] b i)) :=
      (congrArg ev hf).trans (map_sum ev _ _)
    calc
      ev w = ∑ i, ev (E (d i ⊗ₜ[ℂ] b i)) := map_sum ev _ _
      _ = ∑ i, L (m y.1) * ev (E (a i ⊗ₜ[ℂ] b i)) := Finset.sum_congr rfl fun i _ ↦
        (he (d i) (b i) y).trans (((congrArg (· * b i (Multiplicative.ofAdd y.2))
          (hd i y.1)).trans (mul_assoc _ _ _)).trans (congrArg (L (m y.1) * ·) (he (a i) (b i) y).symm))
      _ = L (m y.1) * ev f := (Finset.mul_sum _ _ _).symm.trans (congrArg (L (m y.1) * ·) hf'.symm)
  exact (adeleSchwartzFourier_apply_zero w).1.norm.congr (.of_forall fun y ↦
    (congrArg norm (hw y)).trans ((norm_mul _ _).trans
      ((congrArg (fun z : ℂ ↦ ‖z‖ * ‖f (Multiplicative.ofAdd y)‖) (hL y.1)).trans (mul_comm _ _))))

open InfinitePlace.Completion in
/-- Each archimedean coordinate of the subgroup in logarithmic time is an exponential. -/
private theorem exists_arch_velocity (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) :
    ∃ c : InfinitePlace F → ℂ, ∀ s v, extensionEmbedding v ((γ (expUnit s)).val.1 v) =
      Complex.exp ((s : ℂ) * c v) := by
  have h (v : InfinitePlace F) : ∃ c : ℂ, ∀ s : ℝ, extensionEmbedding v ((γ (expUnit s)).val.1 v) =
      Complex.exp ((s : ℂ) * c) := by
    let χ : ℝ≥0ˣ →ₜ* ℂ :=
      { toFun := fun t ↦ extensionEmbedding v ((γ t).val.1 v)
        map_one' := by rw [map_one]; exact map_one _
        map_mul' := fun t u ↦ by rw [map_mul]; exact map_mul _ _ _
        continuous_toFun := (isometry_extensionEmbedding v).continuous.comp
          ((continuous_apply v).comp (continuous_fst.comp (Units.continuous_val.comp γ.continuous))) }
    obtain ⟨c, hc, -⟩ := existsUnique_complexPower χ
    refine ⟨c, fun s ↦ (hc (expUnit s)).trans ?_⟩
    change (Real.exp s : ℂ) ^ c = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
      ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp]
  choose c hc using h
  exact ⟨c, fun s v ↦ hc v s⟩

/-- Translating the frequency only at infinity adds an explicit phase to the conjugate character. -/
private theorem archCharacter_difference (b c : 𝔸[F]) (h : b.2 = c.2) :
    star (adeleStandardCharacter F b : ℂ) = star (adeleStandardCharacter F c : ℂ) *
      (Circle.exp (2 * Real.pi * ∑ v : InfinitePlace F, (v.mult : ℝ) *
        (InfinitePlace.Completion.extensionEmbedding v (c.1 v - b.1 v)).re) : ℂ) := by
  obtain ⟨d, hd, -⟩ := additiveTamagawaMeasure_selfDual F
  let ψ := d (Multiplicative.ofAdd (1 : 𝔸[F]))
  have hψ (y : 𝔸[F]) : ψ (Multiplicative.ofAdd y) = adeleStandardCharacter F y := by
    simpa only [one_mul] using hd (1 : 𝔸[F]) y
  let w := c.1 - b.1
  have heq : c - b = (w, 0) := Prod.ext rfl (sub_eq_zero.mpr h.symm)
  change _ = _ * (Circle.exp (2 * Real.pi * ∑ v : InfinitePlace F, (v.mult : ℝ) *
    (InfinitePlace.Completion.extensionEmbedding v (w v)).re) : ℂ)
  rw [← archCharacter_apply w, ← heq, ← hψ, ← hψ, ← hψ, ofAdd_sub, map_div]
  change (starRingEnd ℂ) _ = (starRingEnd ℂ) _ * _
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
    div_eq_mul_inv, inv_mul_cancel_left]

open InfinitePlace.Completion in
/-- The Fourier kernel of an inverse dilation acquires the positive velocity term
when its conjugate character is differentiated. -/
private theorem fourier_inverse_orbit_derivative (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (f : ℬ[F]) (x : 𝔸[F])
    (c : InfinitePlace F → ℂ) (hc : ∀ s v, extensionEmbedding v ((γ (expUnit s)).val.1 v) =
      Complex.exp ((s : ℂ) * c v)) :
    let A (y : 𝔸[F]) := f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F (x * y) : ℂ)
    let T (y : 𝔸[F]) := ∑ v : InfinitePlace F, (v.mult : ℝ) *
      (c v * extensionEmbedding v (x.1 v * y.1 v)).re
    Integrable A (additiveTamagawaMeasure F) ∧
    Integrable (fun y ↦ A y * (2 * Real.pi * Complex.I * (T y : ℂ))) (additiveTamagawaMeasure F) ∧
    HasDerivAt (fun s : ℝ ↦ adeleSchwartzFourier f (Multiplicative.ofAdd ((γ (expUnit s))⁻¹.val * x)))
      (∫ y, A y * (2 * Real.pi * Complex.I * (T y : ℂ)) ∂additiveTamagawaMeasure F) 0 := by
  classical
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let μ := additiveTamagawaMeasure F
  let A (y : 𝔸[F]) := f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F (x * y) : ℂ)
  let V (v : InfinitePlace F) (y : 𝔸[F]) := extensionEmbedding v (x.1 v * y.1 v)
  let k (v : InfinitePlace F) (y : 𝔸[F]) := (v.mult : ℂ) * V v y
  let E (s : ℝ) (v : InfinitePlace F) := Complex.exp ((-(s : ℂ)) * c v)
  let z (s : ℝ) (v : InfinitePlace F) := 1 - E s v
  let dz (s : ℝ) (v : InfinitePlace F) := E s v * c v
  have hdz (s v) : HasDerivAt (fun t ↦ z t v) (dz s v) s := by
    have h : HasDerivAt (fun t : ℝ ↦ Complex.exp (-((t : ℂ)) * c v))
        (E s v * (-c v)) s := by
      have hc' : HasDerivAt (fun t : ℝ ↦ -(t : ℂ) * c v) (-c v) s := by
        have ht : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
        simpa only [Pi.neg_apply, neg_one_mul] using ht.neg.mul_const (c v)
      exact hc'.cexp
    exact (show -(E s v * -c v) = dz s v by simp [dz]) ▸ h.const_sub (1 : ℂ)
  have hV (v) : Continuous (V v) := (isometry_extensionEmbedding v).continuous.comp
    (continuous_const.mul ((continuous_apply v).comp continuous_fst))
  have hA_norm (y : 𝔸[F]) : ‖A y‖ = ‖f (Multiplicative.ofAdd y)‖ := by simp [A]
  have hA : Integrable A μ := by
    obtain ⟨d, hd, -⟩ := additiveTamagawaMeasure_selfDual F
    have hχ : Continuous (fun y : 𝔸[F] ↦ (adeleStandardCharacter F (x * y) : ℂ)) :=
      (continuous_subtype_val.comp ((d (Multiplicative.ofAdd x)).continuous.comp continuous_ofAdd)).congr
        (fun y ↦ congrArg Subtype.val (hd x y))
    exact (adeleSchwartzFourier_apply_zero f).1.mono
      (((schwartzBruhat_continuous f).comp continuous_ofAdd).mul hχ.star).aestronglyMeasurable
      (.of_forall fun y ↦ (hA_norm y).le)
  have hm (v : InfinitePlace F) : Integrable (fun y ↦ ‖A y‖ * ‖k v y‖) μ := by
    refine ((adeleSchwartz_arch_moment f v).const_mul
      (‖(v.mult : ℂ)‖ * ‖extensionEmbedding v (x.1 v)‖)).congr (.of_forall fun y ↦ ?_)
    simp only [hA_norm, k, V, map_mul, norm_mul]
    ring
  have hphase := hasDerivAt_integral_fourier_phase μ A hA k
    (fun v ↦ (continuous_const.mul (hV v)).aestronglyMeasurable) hm z dz hdz
    (fun v ↦ by simp [z, E]) (fun v ↦ by dsimp [dz, E]; fun_prop)
  let T (y : 𝔸[F]) := ∑ v : InfinitePlace F, (v.mult : ℝ) * (c v * V v y).re
  have hsum (u : InfinitePlace F → ℂ) (y : 𝔸[F]) :
      (∑ i, (u i * k i y).re) = ∑ i, (i.mult : ℝ) * (u i * V i y).re := by
    apply Finset.sum_congr rfl
    intro i _
    rw [show u i * k i y = ((i.mult : ℝ) : ℂ) * (u i * V i y) by simp [k]; ring,
      Complex.re_ofReal_mul]
  have hD (y) : A y * (((2 * Real.pi * ∑ i, (dz 0 i * k i y).re : ℝ) : ℂ) * Complex.I)
      = A y * (2 * Real.pi * Complex.I * (T y : ℂ)) := by
    simp only [hsum, dz, E, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul, T,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  simp only [hD] at hphase
  refine ⟨hA, hphase.1, hphase.2.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)⟩
  change (∫ y, f (Multiplicative.ofAdd y) *
    star (adeleStandardCharacter F (y * ((γ (expUnit s))⁻¹.val * x)) : ℂ) ∂μ) = _
  apply integral_congr_ae
  refine .of_forall fun y ↦ ?_
  have hneg : expUnit (-s) = (expUnit s)⁻¹ := Units.ext (NNReal.coe_inj.mp (Real.exp_neg s))
  have hg : γ (expUnit (-s)) = (γ (expUnit s))⁻¹ := (congrArg γ hneg).trans (map_inv γ _)
  let b := y * ((γ (expUnit s))⁻¹.val * x)
  have hfin : b.2 = (x * y).2 := by
    change y.2 * ((γ (expUnit s))⁻¹.val.2 * x.2) = x.2 * y.2
    rw [← hg, adeleOneParameter_finite_eq_one γ (expUnit (-s)), one_mul, mul_comm]
  have hinf (v : InfinitePlace F) :
      extensionEmbedding v ((x * y).1 v - b.1 v) = z s v * V v y := by
    change extensionEmbedding v (x.1 v * y.1 v - y.1 v * ((γ (expUnit s))⁻¹.val.1 v * x.1 v)) = _
    simp only [map_sub, map_mul, ← hg, hc, Complex.ofReal_neg, z, E, V]
    ring
  change f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F b : ℂ) =
    A y * (Circle.exp (2 * Real.pi * ∑ i, (z s i * k i y).re) : ℂ)
  rw [hsum (z s) y]
  have hchar := archCharacter_difference b (x * y) hfin
  simp only [hinf] at hchar
  change f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F b : ℂ) = _
  rw [hchar, ← mul_assoc]

/-- Product rule for a Fourier orbit with an exponential normalization. -/
private theorem normalized_orbit_integral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (A T : Y → ℂ) (α : ℝ) (U : ℝ → ℂ) (v : ℂ) (hA : Integrable A μ)
    (hT : Integrable (fun y ↦ A y * T y) μ) (hU0 : U 0 = ∫ y, A y ∂μ)
    (hU : HasDerivAt U (∫ y, A y * T y ∂μ) 0)
    (h : HasDerivAt (fun s : ℝ ↦ (Real.exp (-(s * α)) : ℂ) * U s) v 0) :
    Integrable (fun y ↦ A y * (-(α : ℂ) + T y)) μ ∧
      v = ∫ y, A y * (-(α : ℂ) + T y) ∂μ := by
  have hw : HasDerivAt (fun s : ℝ ↦ Real.exp (-(s * α))) (-α) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const α).neg.exp)
  have hn := h.unique (hw.ofReal_comp.mul hU)
  simp_rw [mul_add]
  refine ⟨(hA.mul_const _).add hT, ?_⟩
  rw [integral_add (hA.mul_const _) hT, integral_mul_const, hn, hU0]
  simp
  ring

/-- Paper: Equation (2.2.4.30), p. 92. The Fourier transform of the derivative
uses the conjugate standard character and the real trace of the archimedean
velocity times the frequency and integration variable. The integrand is integrable.
Deviation: The velocity is expressed using the complex embeddings of the local
completions in the logarithmic parameter. The real trace counts complex places twice. -/
theorem adeleDirectionalDeriv_fourier_integral (f : ℬ[F]) (α : ℝ)
    (hα : ∀ t : ℝ≥0ˣ, valueℝ (ideleNorm F (γ t)) = (valueℝ t) ^ α) :
    ∃ velocity : InfinitePlace F → ℂ,
      (∀ v, HasDerivAt (fun s : ℝ ↦
        InfinitePlace.Completion.extensionEmbedding v ((γ (expUnit s)).val.1 v))
        (velocity v) 0) ∧
      ∀ x : 𝔸[F],
        let integrand := fun y : 𝔸[F] ↦
          f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F (x * y) : ℂ) *
            (-(α : ℂ) + 2 * Real.pi * Complex.I *
              (∑ v : InfinitePlace F, (v.mult : ℝ) *
                (velocity v * InfinitePlace.Completion.extensionEmbedding v (x.1 v * y.1 v)).re : ℝ))
        Integrable integrand (additiveTamagawaMeasure F) ∧
          adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd x) =
            ∫ y, integrand y ∂additiveTamagawaMeasure F := by
  refine Exists.elim (exists_arch_velocity (F := F) γ) fun c hc ↦ ?_
  refine ⟨c, fun v ↦ ?_, fun x ↦ ?_⟩
  · have h : HasDerivAt (fun s : ℝ ↦ Complex.exp ((s : ℂ) * c v)) (c v) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (c v)).cexp
    exact h.congr_of_eventuallyEq (.of_forall fun s ↦ hc s v)
  · let A (y : 𝔸[F]) := f (Multiplicative.ofAdd y) * star (adeleStandardCharacter F (x * y) : ℂ)
    let T (y : 𝔸[F]) := 2 * Real.pi * Complex.I *
      ((∑ v : InfinitePlace F, (v.mult : ℝ) *
        (c v * InfinitePlace.Completion.extensionEmbedding v (x.1 v * y.1 v)).re : ℝ) : ℂ)
    let μ := additiveTamagawaMeasure F
    let U (s : ℝ) := adeleSchwartzFourier f (Multiplicative.ofAdd ((γ (expUnit s))⁻¹.val * x))
    have h1 : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
    have hU0 : U 0 = ∫ y, A y ∂μ := by
      simp only [U, h1, map_one, inv_one, Units.val_one, one_mul]
      exact integral_congr_ae (.of_forall fun y ↦ congrArg (fun b ↦ f (Multiplicative.ofAdd y) *
        star (adeleStandardCharacter F b : ℂ)) (mul_comm _ _))
    have hwt (s : ℝ) : (valueℝ (ideleNorm F (γ (expUnit s))))⁻¹ = Real.exp (-(s * α)) :=
      (congrArg Inv.inv (hα (expUnit s))).trans
        ((congrArg Inv.inv (Real.exp_mul s α).symm).trans (Real.exp_neg _).symm)
    have h := fourier_dilation_hasDerivAt (F := F) γ f x
    have hnorm : HasDerivAt (fun s : ℝ ↦ (Real.exp (-(s * α)) : ℂ) * U s)
        (adeleSchwartzFourier (adeleDirectionalDeriv γ f) (Multiplicative.ofAdd x)) 0 :=
      h.congr_of_eventuallyEq (.of_forall fun s ↦ by
        change _ = _ • U s
        rw [hwt s, Complex.real_smul])
    have H := fourier_inverse_orbit_derivative (F := F) γ f x c hc
    exact normalized_orbit_integral μ A T α U _ H.1 H.2.1 hU0 H.2.2 hnorm

-- TODO(paper-gap): On p. 92 the proof of Lemma 2.2.4.5 incorrectly drops
-- the norm factor at x = 0. The limit is -α * f̂(0), as in part (2).
-- The finite local factors of (2.2.4.32) also evaluate f_v at x_v under dν_v(y_v).

/-- Families of continuous operators on adelic Schwartz–Bruhat space in logarithmic time. -/
private abbrev AdeleDilationOperators (K : Type*) [Field K] [NumberField K] :=
  ℝ → ℬ[K] →L[ℂ] ℬ[K]

/-- Tensoring a family of operators with the identity preserves boundedness of its
orbits. Each tensor is a finite sum, and tensoring with a fixed vector is continuous. -/
private theorem bounded_inductiveTensor_orbit {I A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (P : I → A →L[ℂ] A) {K : Set I} (hb : ∀ a, IsVonNBounded ℂ ((fun i ↦ P i a) '' K))
    (u : InductiveTensor A B) :
    IsVonNBounded ℂ ((fun i ↦ inductiveTensorMap (P i).toLinearMap (LinearMap.id (M := B)) u) '' K) := by
  let T := InductiveTensor A B
  let hS := withGeneratingSeminorms_spec (A ⊗[ℂ] B)
    (fun p : {p : Seminorm ℂ (A ⊗[ℂ] B) // (∀ a : A, Continuous (fun b : B ↦ p (a ⊗ₜ[ℂ] b))) ∧
      (∀ b : B, Continuous (fun a : A ↦ p (a ⊗ₜ[ℂ] b)))} ↦ p.val)
  have : IsTopologicalAddGroup T := hS.toPolynormableSpace.isTopologicalAddGroup
  induction (show A ⊗[ℂ] B from u) using TensorProduct.inductionOn with
  | tmul a b =>
    let j : A →ₗ[ℂ] T := (TensorProduct.mk ℂ A B).flip b
    let J : A →L[ℂ] T := ⟨j, hS.continuous_of_continuous_comp j fun p ↦ p.2.2 b⟩
    apply IsVonNBounded.subset _ ((hb a).image J)
    rintro y ⟨i, hi, h⟩
    exact ⟨P i a, ⟨i, hi, rfl⟩, h⟩
  | add a b ha hb =>
    refine (ha.add hb).subset ?_
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨_, ⟨i,hi,rfl⟩, _, ⟨i,hi,rfl⟩, (map_add _ a b).symm⟩

private theorem bounded_image_comp {I E H : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [AddCommGroup H] [Module ℂ H]
    [TopologicalSpace H] (L : E →L[ℂ] H) (a : I → E) (K : Set I)
    (h : IsVonNBounded ℂ (a '' K)) : IsVonNBounded ℂ ((fun i ↦ L (a i)) '' K) := by
  simpa only [Set.image_image, Function.comp_def] using h.image L

/-- Lift operators on the first tensor factor through a topological isomorphism.
The evaluation identity need only be checked on pure tensors. -/
private theorem tensor_pullback_operators {I X A B E : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (e : InductiveTensor A B ≃L[ℂ] E) (ev : X → E →ₗ[ℂ] ℂ) (m : I → X → X)
    (L : I → A →L[ℂ] A) (K : Set I) (hb : ∀ a, IsVonNBounded ℂ ((fun i ↦ L i a) '' K))
    (ht : ∀ i x a b, ev x (e ((L i a) ⊗ₜ[ℂ] b)) = ev (m i x) (e (a ⊗ₜ[ℂ] b))) :
    ∃ U : I → E →L[ℂ] E, (∀ i f x, ev x (U i f) = ev (m i x) f) ∧
      ∀ f, IsVonNBounded ℂ ((fun i ↦ U i f) '' K) := by
  let T (i : I) : InductiveTensor A B →L[ℂ] InductiveTensor A B :=
    ⟨inductiveTensorMap (L i).toLinearMap (LinearMap.id (M := B)), continuous_inductiveTensorMap_id (L i)⟩
  let U (i : I) := e.toContinuousLinearMap.comp ((T i).comp e.symm.toContinuousLinearMap)
  refine ⟨U, fun i f x ↦ ?_, fun f ↦ ?_⟩
  · have h : (ev x).comp (e.toLinearEquiv.toLinearMap.comp (T i).toLinearMap) =
        (ev (m i x)).comp e.toLinearEquiv.toLinearMap := TensorProduct.ext' (ht i x)
    exact (LinearMap.congr_fun h (e.symm f)).trans (congrArg (ev (m i x)) (e.apply_symm_apply f))
  · exact bounded_image_comp e.toContinuousLinearMap (fun i ↦ T i (e.symm f)) K
      (bounded_inductiveTensor_orbit L hb (e.symm f))

/-- Pullback by a log-parametrized idele acts continuously and has bounded orbits on
compact time intervals, using the tensor product decomposition at infinity. -/
private theorem exists_adele_dilation_operators (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) :
    ∃ U : AdeleDilationOperators F,
      (∀ s f (x : 𝔸[F]), U s f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd ((γ (expUnit s)).val * x))) ∧
      ∀ f, IsVonNBounded ℂ ((fun s ↦ U s f) '' Icc (-1 : ℝ) 1) := by
  classical
  let V := mixedEmbedding.mixedSpace F
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B := SchwartzBruhat (Multiplicative 𝔸ᶠ[F])
  let : IsTopologicalAddGroup A := inferInstance
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let p := m.toRingHom.comp (RingHom.fst (InfiniteAdeleRing F) 𝔸ᶠ[F])
  let u (s : ℝ) : Vˣ := Units.map p.toMonoidHom (γ (expUnit s))
  have hp : Continuous p := (continuous_mixedCoordinates (F := F)).1.comp continuous_fst
  have hu : Continuous u := (hp.units_map p.toMonoidHom).comp
    (γ.continuous.comp ((Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous))
  refine Exists.elim (schwartz_unit_pullbacks u hu _ (isCompact_Icc (a := (-1 : ℝ)) (b := 1))) fun P hP' ↦ ?_
  have hP := hP'.1
  have hPb := hP'.2
  refine Exists.elim (archimedeanSchwartzBruhat_equiv (F := F)) fun J hJ ↦ ?_
  let L (s : ℝ) : A →L[ℂ] A := J.toContinuousLinearMap.comp ((P s).comp J.symm.toContinuousLinearMap)
  have hLb (a : A) : IsVonNBounded ℂ ((fun s ↦ L s a) '' Icc (-1 : ℝ) 1) :=
    bounded_image_comp J.toContinuousLinearMap (fun s ↦ P s (J.symm a)) _ (hPb (J.symm a))
  have hL (s : ℝ) (a : A) (x : InfiniteAdeleRing F) :
      L s a (Multiplicative.ofAdd x) = a (Multiplicative.ofAdd ((γ (expUnit s)).val.1 * x)) := by
    let b := J.symm a
    calc
      _ = P s b (m x) := hJ _ _
      _ = b (m ((γ (expUnit s)).val.1 * x)) := (hP s b _).trans (congrArg b (m.map_mul _ _).symm)
      _ = _ := (hJ b _).symm.trans (congrArg (fun h : A ↦ h (Multiplicative.ofAdd _)) (J.apply_symm_apply a))
  refine Exists.elim (adeleSchwartz_inductiveTensor_equiv F) fun e he ↦ ?_
  let ev (x : 𝔸[F]) : ℬ[F] →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd x)).comp (schwartzBruhatSubmodule _).subtype
  refine tensor_pullback_operators e ev (fun s x ↦ (γ (expUnit s)).val * x) L _ hLb (fun s x a b ↦ ?_)
  let t := (γ (expUnit s)).val * x
  have hfin : t.2 = x.2 := (congrArg (· * x.2) (adeleOneParameter_finite_eq_one γ _)).trans (one_mul _)
  exact (he (L s a) b x).trans ((congrArg₂ (· * ·) (hL s a x.1)
    (congrArg (fun y ↦ b (Multiplicative.ofAdd y)) hfin.symm)).trans (he a b t).symm)


/-- A map realized by a Pontryagin-dual Fourier operator is linear. Its action on
bounded sets suffices for continuity in the bornological Schwartz–Bruhat topology. -/
private theorem schwartzBruhat_clm_of_pullback {G K : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup K] [TopologicalSpace K]
    (T : SchwartzBruhat G → SchwartzBruhat G) (H : SchwartzBruhat G →L[ℂ] SchwartzBruhat K)
    (e : G → K) (hF : ∀ f x, T f x = H f (e x))
    (hb : ∀ B, IsVonNBounded ℂ B → IsVonNBounded ℂ (T '' B)) :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f, P f = T f := by
  let W : SchwartzBruhat G →ₗ[ℂ] G → ℂ :=
    (LinearMap.funLeft ℂ ℂ e).comp ((schwartzBruhatSubmodule K).subtype.comp H.toLinearMap)
  have heq (f : SchwartzBruhat G) : W f = (T f : G → ℂ) := funext fun x ↦ (hF f x).symm
  let L : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G := W.codRestrict (schwartzBruhatSubmodule G)
    (fun f ↦ (congrArg (· ∈ schwartzBruhatSubmodule G) (heq f).symm).mp (T f).property)
  have hL : ∀ f, L f = T f := fun f ↦ Subtype.ext (heq f)
  have hbound (B : Set (SchwartzBruhat G)) (hB : IsVonNBounded ℂ B) : IsVonNBounded ℂ (L '' B) :=
    (congrArg (fun t ↦ IsVonNBounded ℂ (t '' B)) (funext hL).symm).mp (hb B hB)
  exact ⟨⟨L, continuous_of_bornological_image (schwartzBruhat_bornological (G := G)) L hbound⟩, hL⟩

private theorem selfDual_fourier_clm {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalGroup (Multiplicative R)] [T2Space (Multiplicative R)]
    [LocallyCompactSpace (Multiplicative R)] [MeasurableSpace R] [BorelSpace (Multiplicative R)]
    (μ : Measure (Multiplicative R)) [μ.IsHaarMeasure] [μ.Regular]
    (ψ : R → Circle) (hψ : IsTamagawaSelfDual (show Measure R from μ) ψ)
    (T : SchwartzBruhat (Multiplicative R) → SchwartzBruhat (Multiplicative R))
    (hT : ∀ f (x : Multiplicative R), T f x =
      tamagawaFourier (show Measure R from μ) ψ (fun y ↦ f (Multiplicative.ofAdd y)) x.toAdd)
    (hb : ∀ B, IsVonNBounded ℂ B → IsVonNBounded ℂ (T '' B)) :
    ∃ P : SchwartzBruhat (Multiplicative R) →L[ℂ] SchwartzBruhat (Multiplicative R), ∀ f, P f = T f := by
  let G := Multiplicative R
  refine Exists.elim hψ fun e he ↦ ?_
  refine Exists.elim (schwartzBruhat_fourier_equiv (G := G) μ) fun H hH ↦ ?_
  refine schwartzBruhat_clm_of_pullback T H.toContinuousLinearMap e (fun f x ↦ ?_) hb
  exact (hT f x).trans ((tamagawaFourier_eq_lcaFourier (show Measure R from μ) ψ
    (fun y ↦ f (Multiplicative.ofAdd y)) x.toAdd (e x) (fun y ↦
      (he.1 x.toAdd y).trans (congrArg ψ (mul_comm _ _)))).trans ((hH f).2 (e x)).symm)

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The adelic Fourier map is continuous and complex-linear. Linearity follows from
its Pontryagin-dual realization, and the bornological criterion gives continuity. -/
private theorem exists_adeleFourier_clm :
    ∃ P : ℬ[F] →L[ℂ] ℬ[F], ∀ f, P f = adeleSchwartzFourier f := by
  let G := Multiplicative 𝔸[F]
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) × (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let μ : Measure G := additiveTamagawaMeasure F
  let : BorelSpace G := ⟨rfl⟩
  let : μ.IsHaarMeasure := additiveTamagawaMeasure_isHaar F
  let : μ.Regular := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.2.1
  exact selfDual_fourier_clm (R := 𝔸[F]) μ (adeleStandardCharacter F) (additiveTamagawaMeasure_selfDual F)
    (adeleSchwartzFourier (F := F)) (fun _ _ ↦ rfl) (adeleSchwartzFourier_image_isVonNBounded (F := F))


/-- Two scalar bounds suffice to control all the slopes near the identity. -/
private theorem eventually_log_slope_bounded :
    ∀ᶠ t : ℝ≥0ˣ in 𝓝[≠] 1, |Real.log (valueℝ t)| ≤ 1 ∧
      |Real.log (valueℝ t) / (valueℝ t - 1)| ≤ 2 := by
  have hv : Tendsto valueℝ (𝓝[≠] (1 : ℝ≥0ˣ)) (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (NNReal.continuous_coe.comp (Units.continuous_val (M := ℝ≥0))).continuousAt.continuousWithinAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact fun he ↦ ht (Units.val_injective (NNReal.coe_injective he))
  have hs : Tendsto (fun t : ℝ≥0ˣ ↦ Real.log (valueℝ t) / (valueℝ t - 1)) (𝓝[≠] 1) (𝓝 1) := by
    simpa only [Function.comp_def, slope_def_field, Real.log_one, sub_zero, inv_one] using
      (Real.hasDerivAt_log one_ne_zero).tendsto_slope.comp hv
  have hl : Tendsto (fun t : ℝ≥0ˣ ↦ Real.log (valueℝ t)) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp (hv.mono_right nhdsWithin_le_nhds)
  exact ((hl.abs.eventually_le_const (by norm_num : |(0:ℝ)| < 1))).and
    (hs.abs.eventually_le_const (by norm_num : |(1:ℝ)| < 2))

/-- For a fixed test function, slopes with bounded logarithmic step and bounded
change of parameter lie in one compact convex set. -/
private theorem adele_dilation_slopes_bounded (γ : ℝ≥0ˣ →ₜ* 𝕀[F])
    (U : AdeleDilationOperators F) (hU : ∀ s f (x : 𝔸[F]), U s f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd ((γ (expUnit s)).val * x)))
    (hb : ∀ f, IsVonNBounded ℂ ((fun s ↦ U s f) '' Icc (-1 : ℝ) 1)) (f : ℬ[F]) :
    ∃ C : Set ℬ[F], IsCompact C ∧ 0 ∈ C ∧
      ∀ s δ : ℝ, |s| ≤ 1 → |s / δ| ≤ 2 → (((δ : ℂ)⁻¹) • (U s f - f)) ∈ C := by
  let E := ℬ[F]
  let : T2Space E := (adeleSchwartz_nuclear.{_, 0} F).2.1
  let : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  let : MontelSpace ℂ E := (adeleSchwartz_montel F).2.2
  let ev (x : 𝔸[F]) : E →L[ℂ] ℂ :=
    ⟨(LinearMap.proj (Multiplicative.ofAdd x)).comp (schwartzBruhatSubmodule _).subtype,
      schwartzBruhat_continuous_eval (Multiplicative.ofAdd x)⟩
  have hder (φ : E) (x : 𝔸[F]) (s : ℝ) : HasDerivAt (fun t ↦ ev x (U t φ))
      (ev x (U s (adeleDirectionalDeriv γ φ))) s := by
    have h := adele_dilation_orbit_hasDerivAt γ φ x s
    have h' := h.congr_of_eventuallyEq (.of_forall (fun t ↦ hU t φ x))
    exact (congrArg (fun z : ℂ ↦ HasDerivAt (fun t ↦ ev x (U t φ)) z s)
      (hU s (adeleDirectionalDeriv γ φ) x).symm).mp h'
  let d := adeleDirectionalDeriv γ f
  have hzero : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have h0 : U 0 f = f := Subtype.ext (funext fun x ↦ (hU 0 f x.toAdd).trans
    (congrArg (fun g : 𝕀[F] ↦ f (Multiplicative.ofAdd (g.val * x.toAdd)))
      ((congrArg γ hzero).trans (map_one γ)) |>.trans
      (congrArg (fun z : 𝔸[F] ↦ f (Multiplicative.ofAdd z)) (one_mul _))))
  refine Exists.elim (exists_compact_slopes_of_velocity ev
    (fun _ _ h ↦ Subtype.ext (funext fun x ↦ h x.toAdd)) (fun t ↦ U t f) (fun t ↦ U t d)
    (fun x ↦ continuous_iff_continuousAt.mpr fun s ↦ (hder d x s).continuousAt)
    (hder f) (hb d)) fun C hC ↦ ?_
  exact ⟨C, hC.1, hC.2.1, fun s δ hs hδ ↦
    (congrArg (fun z : E ↦ (δ : ℂ)⁻¹ • (U s f - z) ∈ C) h0).mp (hC.2.2 s δ hs hδ)⟩

/-- A compact set of log-scaled slopes bounds the ordinary positive-unit slopes near one. -/
private theorem isVonNBounded_log_slopes {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (a : ℝ → E) (f : E)
    (h : ∃ C : Set E, IsCompact C ∧ 0 ∈ C ∧
      ∀ s δ : ℝ, |s| ≤ 1 → |s / δ| ≤ 2 → (δ : ℂ)⁻¹ • (a s - f) ∈ C) :
    IsVonNBounded ℂ ((fun t : ℝ≥0ˣ ↦ ((valueℝ t : ℂ) - 1)⁻¹ • (a (Real.log (valueℝ t)) - f)) ''
      {t | |Real.log (valueℝ t)| ≤ 1 ∧ |Real.log (valueℝ t) / (valueℝ t - 1)| ≤ 2}) := by
  obtain ⟨C, hC, _, h⟩ := h
  apply IsVonNBounded.subset _ (hC.isVonNBounded ℂ)
  rintro _ ⟨t, ht, rfl⟩
  simpa only [Complex.ofReal_sub, Complex.ofReal_one] using h _ _ ht.1 ht.2

private theorem adele_physical_slope_tendsto (γ : ℝ≥0ˣ →ₜ* 𝕀[F])
    (U : AdeleDilationOperators F) (hU : ∀ s f (x : 𝔸[F]), U s f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd ((γ (expUnit s)).val * x))) (f : ℬ[F]) (x : 𝔸[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦ ((valueℝ t : ℂ) - 1)⁻¹ *
      (U (Real.log (valueℝ t)) f (Multiplicative.ofAdd x) - f (Multiplicative.ofAdd x))) (𝓝[≠] 1)
      (𝓝 (adeleDirectionalDeriv γ f (Multiplicative.ofAdd x))) := by
  let u (t : ℝ≥0ˣ) := Real.log (valueℝ t)
  let c (t : ℝ≥0ˣ) := ((valueℝ t : ℂ) - 1)⁻¹
  refine (adeleDirectionalDeriv_tendsto γ f x).congr (fun t ↦ ?_)
  have hz : expUnit (u t) = t :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
  have hx := (hU (u t) f x).trans
    (congrArg (fun z : ℝ≥0ˣ ↦ f (Multiplicative.ofAdd ((γ z).val * x))) hz)
  exact (div_eq_inv_mul _ _).trans (congrArg (fun z : ℂ ↦ c t * (z - f (Multiplicative.ofAdd x))) hx.symm)

/-- Pointwise convergence of slopes and compact control near the identity imply uniform
convergence on bounded sets of Schwartz–Bruhat functions. -/
private theorem schwartz_uniform_log_slopes {G : Type*} [CommGroup G] [TopologicalSpace G]
    [T2Space (SchwartzBruhat G)] [ContinuousSMul ℂ (SchwartzBruhat G)] [MontelSpace ℂ (SchwartzBruhat G)]
    [BarrelledSpace ℂ (SchwartzBruhat G)] (U : ℝ → SchwartzBruhat G →L[ℂ] SchwartzBruhat G)
    (D : SchwartzBruhat G → SchwartzBruhat G)
    (hc : ∀ f, ∃ C : Set (SchwartzBruhat G), IsCompact C ∧ 0 ∈ C ∧ ∀ s δ : ℝ, |s| ≤ 1 →
      |s / δ| ≤ 2 → (δ : ℂ)⁻¹ • (U s f - f) ∈ C)
    (hl : ∀ f (x : G), Tendsto (fun t : ℝ≥0ˣ ↦ ((valueℝ t : ℂ) - 1)⁻¹ *
      (U (Real.log (valueℝ t)) f x - f x)) (𝓝[≠] 1) (𝓝 (D f x)))
    (B : Set (SchwartzBruhat G)) (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun (t : ℝ≥0ˣ) f ↦ ((valueℝ t : ℂ) - 1)⁻¹ •
      (U (Real.log (valueℝ t)) f - f)) D (𝓝[≠] 1) B := by
  let ev (f : SchwartzBruhat G) (x : G) := f x
  have hcont : Continuous ev := continuous_pi fun x ↦ schwartzBruhat_continuous_eval x
  have hinj : Injective ev := fun _ _ h ↦ Subtype.ext h
  let Q (t : ℝ≥0ˣ) : SchwartzBruhat G →L[ℂ] SchwartzBruhat G := ((valueℝ t : ℂ) - 1)⁻¹ •
    (U (Real.log (valueℝ t)) - ContinuousLinearMap.id ℂ (SchwartzBruhat G))
  exact uniformOn_montel_of_evaluations_near (𝓝[≠] 1) ev hcont hinj Q D
    eventually_log_slope_bounded (fun f ↦ isVonNBounded_log_slopes (fun s ↦ U s f) f (hc f)) hl B hB


private theorem adele_dilation_uniform (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (B : Set ℬ[F]) (hB : IsVonNBounded ℂ B)
    (U : AdeleDilationOperators F) (hU : ∀ s f (x : 𝔸[F]), U s f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd ((γ (expUnit s)).val * x)))
    (hb : ∀ f, IsVonNBounded ℂ ((fun s ↦ U s f) '' Icc (-1 : ℝ) 1)) :
    TendstoUniformlyOn (fun (t : ℝ≥0ˣ) (f : ℬ[F]) ↦ ((valueℝ t : ℂ) - 1)⁻¹ •
      (U (Real.log (valueℝ t)) f - f)) (adeleDirectionalDeriv γ) (𝓝[≠] 1) B := by
  have hc := @adele_dilation_slopes_bounded F _ _ γ U hU hb
  have hl := @adele_physical_slope_tendsto F _ _ γ U hU
  let E := ℬ[F]
  let : T2Space E := (adeleSchwartz_nuclear.{_, 0} F).2.1
  let : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  let : MontelSpace ℂ E := (adeleSchwartz_montel F).2.2
  let : BarrelledSpace ℂ E := (adeleSchwartz_montel F).2.1
  exact schwartz_uniform_log_slopes (G := Multiplicative 𝔸[F]) U (adeleDirectionalDeriv (F := F) γ)
    hc (fun f x ↦ hl f x.toAdd) B hB

/-- Fourier covariance carries uniform physical slopes to norm-weighted inverse dilations. -/
private theorem fourier_uniform_of_dilations (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (B : Set ℬ[F]) (U : AdeleDilationOperators F)
    (hU : ∀ s f (x : 𝔸[F]), U s f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd ((γ (expUnit s)).val * x)))
    (P : ℬ[F] →L[ℂ] ℬ[F]) (hP : ∀ f, P f = adeleSchwartzFourier f)
    (hlim : TendstoUniformlyOn (fun (t : ℝ≥0ˣ) (f : ℬ[F]) ↦ ((valueℝ t : ℂ) - 1)⁻¹ •
      (U (Real.log (valueℝ t)) f - f)) (adeleDirectionalDeriv γ) (𝓝[≠] 1) B) :
    TendstoUniformlyOn (fun (t : ℝ≥0ˣ) (f : ℬ[F]) ↦
      (((valueℝ t : ℂ) - 1)⁻¹) •
        (((valueℝ (ideleNorm F (γ t)) : ℂ)⁻¹) •
          schwartzBruhatUnitTranslate (γ t) (adeleSchwartzFourier f) - adeleSchwartzFourier f))
      (fun f ↦ adeleSchwartzFourier (adeleDirectionalDeriv γ f)) (𝓝[≠] 1) B := by
  have hcov (t : ℝ≥0ˣ) (f : ℬ[F]) : P (U (Real.log (valueℝ t)) f) =
      ((valueℝ (ideleNorm F (γ t)) : ℂ)⁻¹) • schwartzBruhatUnitTranslate (γ t) (adeleSchwartzFourier f) := by
    refine (hP _).trans (Subtype.ext (funext fun x ↦ ?_))
    have hz : expUnit (Real.log (valueℝ t)) = t :=
      Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t))))
    have hfun (y : 𝔸[F]) : U (Real.log (valueℝ t)) f (Multiplicative.ofAdd y) =
        f (Multiplicative.ofAdd ((γ t).val * y)) :=
      (hU _ f y).trans (congrArg (fun z : ℝ≥0ˣ ↦ f (Multiplicative.ofAdd ((γ z).val * y))) hz)
    let C (a : 𝔸[F] → ℂ) := tamagawaFourier (additiveTamagawaMeasure F)
      (adeleStandardCharacter F) a x.toAdd
    let r := valueℝ (ideleNorm F (γ t))
    let b := adeleSchwartzFourier f (Multiplicative.ofAdd ((γ t)⁻¹.val * x.toAdd))
    exact (congrArg C (funext hfun)).trans ((adeleSchwartzFourier_dilation f (γ t) x.toAdd).trans
      (show r⁻¹ • b = (r : ℂ)⁻¹ * b by rw [Complex.real_smul, Complex.ofReal_inv]))
  have H := P.uniformContinuous.comp_tendstoUniformlyOn hlim
  apply (H.congr (.of_forall fun t f _ ↦ ?_)).congr_right (fun f _ ↦ hP _)
  change P (_ • (_ - f)) = _
  let u := U (Real.log (valueℝ t)) f
  let c := ((valueℝ t : ℂ) - 1)⁻¹
  exact (map_smul P c (u - f)).trans (congrArg (c • ·)
    ((map_sub P u f).trans (congrArg₂ (· - ·) (hcov t f) (hP f))))

/-- Paper: Remark 2.2.4.6, p. 92. The norm-weighted inverse-dilation
quotients of the Fourier transforms converge in the Schwartz–Bruhat topology,
uniformly over every bounded set of inputs. -/
theorem adeleDirectionalDeriv_fourier_tendstoUniformlyOn (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) :
    TendstoUniformlyOn (fun (t : ℝ≥0ˣ) (f : ℬ[F]) ↦
      (((valueℝ t : ℂ) - 1)⁻¹) •
        (((valueℝ (ideleNorm F (γ t)) : ℂ)⁻¹) •
          schwartzBruhatUnitTranslate (γ t) (adeleSchwartzFourier f) - adeleSchwartzFourier f))
      (fun f ↦ adeleSchwartzFourier (adeleDirectionalDeriv γ f)) (𝓝[≠] 1) B := by
  -- Explicit instances keep elaboration from reconstructing the adelic Schwartz topology.
  rename_i fieldF nfF
  refine Exists.elim (@exists_adele_dilation_operators F fieldF nfF γ) fun U hu ↦ ?_
  refine Exists.elim (@exists_adeleFourier_clm F fieldF nfF) fun P hp ↦ ?_
  exact @fourier_uniform_of_dilations F fieldF nfF γ B U hu.1 P hp
    (@adele_dilation_uniform F fieldF nfF γ B hB U hu.1 hu.2)

end PolarHyperplanes

section HomogeneousTheta

local instance adelicThetaIdeleMeasurableSpace : MeasurableSpace 𝕀[F] := borel _
local instance adelicThetaClassMeasurableSpace : MeasurableSpace C[F] := borel _

local notation "χ[" F "]" => PontryaginDual C₁[F]
local notation "μ₁" => normOneIdeleTamagawaMeasure F
local notation "μ̄₁" => normOneIdeleClassTamagawaMeasure F
local notation "classIntegrand" => fun (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) (h : C₁[F]) ↦
  adelicTheta f (Subtype.val h * g) * (ω₁ h : ℂ)

/-- Paper: Definition 2.2.5.1, p. 95. The character-weighted theta integrand
is integrable over the compact group of norm-one idele classes. -/
theorem homogeneousAdelicTheta_integrable (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) :
    Integrable (classIntegrand ω₁ f g) μ̄₁ := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hcont : Continuous (classIntegrand ω₁ f g) :=
    ((adelicTheta f).continuous.comp (continuous_subtype_val.mul continuous_const)).mul
      (continuous_subtype_val.comp ω₁.continuous)
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Paper: Lemma 2.2.5.2(2), p. 95. Averaging theta against the character on
the norm-one idele classes gives a continuous function of the ambient class. -/
theorem homogeneousAdelicTheta_continuous (ω₁ : χ[F]) (f : ℬ[F]) :
    Continuous (fun g ↦ ∫ h, classIntegrand ω₁ f g h ∂μ̄₁) := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hjoint : Continuous (fun p : C[F] × C₁[F] ↦ classIntegrand ω₁ f p.1 p.2) :=
    ((adelicTheta f).continuous.comp ((continuous_subtype_val.comp continuous_snd).mul
      continuous_fst)).mul (continuous_subtype_val.comp (ω₁.continuous.comp continuous_snd))
  -- The integrand, as a function of the ambient class, is continuous for the sup norm.
  let Φ : C[F] → C(C₁[F], ℂ) := fun g ↦ ⟨classIntegrand ω₁ f g,
    ((adelicTheta f).continuous.comp (continuous_subtype_val.mul continuous_const)).mul
      (continuous_subtype_val.comp ω₁.continuous)⟩
  have hΦ : Continuous Φ := ContinuousMap.continuous_of_continuous_uncurry Φ hjoint
  -- Integration against the finite measure is Lipschitz for the sup norm.
  have hint (u : C(C₁[F], ℂ)) : Integrable u μ̄₁ :=
    u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlip : LipschitzWith (μ̄₁.real univ).toNNReal (fun u : C(C₁[F], ℂ) ↦ ∫ h, u h ∂μ̄₁) := by
    refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hint u) (hint v),
      Real.coe_toNNReal _ measureReal_nonneg, mul_comm]
    exact norm_integral_le_of_norm_le_const
      (.of_forall fun h ↦ (u - v).norm_coe_le_norm h)
  exact hlip.continuous.comp hΦ

/-- Paper: Definition 2.2.5.1, p. 95. Homogeneous theta is the integral of
theta at `h * g`, weighted by `ω₁ h` against norm-one class Haar measure. -/
def homogeneousAdelicTheta (ω₁ : χ[F]) (f : ℬ[F]) : C(C[F], ℂ) :=
  ⟨fun g ↦ ∫ h, classIntegrand ω₁ f g h ∂μ̄₁, homogeneousAdelicTheta_continuous ω₁ f⟩

/-- Paper: Definition 2.2.5.1, p. 95. For the trivial character and at the
identity class, homogeneous theta integrates theta over the norm-one classes. -/
theorem homogeneousAdelicTheta_trivial_at_one (f : ℬ[F]) :
    homogeneousAdelicTheta (1 : χ[F]) f 1 = ∫ h : C₁[F], adelicTheta f h.val ∂μ̄₁ := by
  simp only [homogeneousAdelicTheta, ContinuousMap.coe_mk]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  refine (congrArg₂ (· * ·) (congrArg (adelicTheta f) (mul_one h.val))
    (congrArg Subtype.val (PontryaginDual.one_apply h))).trans (mul_one _)

/-- Paper: Definition 2.2.5.1, p. 95. Formation of homogeneous theta is
complex linear in the test function. -/
theorem homogeneousAdelicTheta_isLinear (ω₁ : χ[F]) :
    IsLinearMap ℂ (homogeneousAdelicTheta ω₁) := by
  have hθ := adelicTheta_isLinear (F := F)
  constructor
  · intro f f'
    refine ContinuousMap.ext fun g ↦ ?_
    change ∫ h, classIntegrand ω₁ (f + f') g h ∂μ̄₁ =
      (∫ h, classIntegrand ω₁ f g h ∂μ̄₁) + ∫ h, classIntegrand ω₁ f' g h ∂μ̄₁
    refine (integral_congr_ae (.of_forall fun h ↦ ?_)).trans
      (integral_add (homogeneousAdelicTheta_integrable ω₁ f g)
        (homogeneousAdelicTheta_integrable ω₁ f' g))
    change adelicTheta (f + f') (h.val * g) * (ω₁ h : ℂ) =
      adelicTheta f (h.val * g) * (ω₁ h : ℂ) + adelicTheta f' (h.val * g) * (ω₁ h : ℂ)
    rw [hθ.map_add, ContinuousMap.add_apply, add_mul]
  · intro c f
    refine ContinuousMap.ext fun g ↦ ?_
    change ∫ h, classIntegrand ω₁ (c • f) g h ∂μ̄₁ = c • ∫ h, classIntegrand ω₁ f g h ∂μ̄₁
    refine (integral_congr_ae (.of_forall fun h ↦ ?_)).trans (integral_smul c _)
    change adelicTheta (c • f) (h.val * g) * (ω₁ h : ℂ) =
      c • (adelicTheta f (h.val * g) * (ω₁ h : ℂ))
    rw [hθ.map_smul, ContinuousMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

local notation "classOfNormOne" => fun h : N₁[F] ↦
  (Subtype.mk (classOf (Subtype.val h)) (Subtype.property h) : C₁[F])
local notation "ideleIntegrand" => fun (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) (h : N₁[F]) ↦
  f (Multiplicative.ofAdd (Units.val (Subtype.val h * g))) * (ω₁ (classOfNormOne h) : ℂ)

/-- The translates of the compact closure of the idelic fundamental domain
by principal ideles cover the norm-one ideles. -/
private theorem exists_compact_normOneIdele_cover :
    ∃ principal : Fˣ → N₁[F],
      (∀ ξ, (principal ξ).val = IdeleGroup.unitEmbedding (𝓞 F) F ξ) ∧
      ∃ K : Set N₁[F], IsCompact K ∧
        (⋃ ξ : Fˣ, (fun h : N₁[F] ↦ principal ξ * h) '' K) = univ := by
  obtain ⟨b⟩ := regulator_units_mod_torsion_basis F
  obtain ⟨r, hr₁, hr⟩ := exists_normOne_class_representatives F
  let v₀ := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  let E := ideleFundamentalDomain F b v₀ (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) r
  let principal := (IdeleGroup.unitEmbedding (𝓞 F) F).codRestrict (ideleNorm F).ker
    (fun ξ ↦ (ideleNorm_spec F).2 (Set.mem_range_self ξ))
  refine ⟨principal, fun _ ↦ rfl, closure E, ideleFundamentalDomain_precompact F b v₀ _ r hr₁ hr, ?_⟩
  have hcover : (⋃ ξ : Fˣ, (fun h : N₁[F] ↦ principal ξ * h) '' E) = univ :=
    (congrArg Set.iUnion (funext fun ξ : Fˣ ↦ Set.image_smul (a := principal ξ) (t := E))).trans
      (ideleFundamentalDomain_cover F b v₀ _ r hr₁ hr)
  exact Set.eq_univ_of_univ_subset (hcover ▸ iUnion_mono fun _ ↦ image_mono subset_closure)

/-- The restriction of an adelic test function along a translated norm-one
idele orbit is integrable for norm-one Tamagawa measure. -/
private theorem normOneIdele_testFunction_integrable (f : ℬ[F]) (g : 𝕀[F]) :
    Integrable (fun h : N₁[F] ↦ f (Multiplicative.ofAdd (h.val * g).val)) μ₁ := by
  classical
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let φ (h : N₁[F]) := f (Multiplicative.ofAdd (h.val * g).val)
  have hφ : Continuous φ := (schwartzBruhat_continuous f).comp
    (continuous_ofAdd.comp (Units.continuous_val.comp (continuous_subtype_val.mul_const g)))
  refine ⟨hφ.aestronglyMeasurable, (hasFiniteIntegral_iff_norm φ).mpr ?_⟩
  obtain ⟨principal, hprincipal, K, hK, hcover⟩ := exists_compact_normOneIdele_cover (F := F)
  let p (h : N₁[F]) : 𝕀[F] × 𝔸[F] := (h.val * g, 0)
  have hp : Continuous p := (continuous_subtype_val.mul_const g).prodMk continuous_const
  let term (ξ : Fˣ) (z : 𝕀[F] × 𝔸[F]) : ℝ :=
    ‖f (Multiplicative.ofAdd (z.1.val * (algebraMap F 𝔸[F] (ξ : F) + z.2)))‖
  have ht (ξ : Fˣ) : Continuous (term ξ) := ((schwartzBruhat_continuous f).comp
    (continuous_ofAdd.comp ((Units.continuous_val.comp continuous_fst).mul
      (continuous_const.add continuous_snd)))).norm
  have hs : SummableUniformlyOn term (p '' K) :=
    adelicAverage_summableUniformlyOn f _ (hK.image hp)
  have hcont : ContinuousOn (fun z ↦ ∑' ξ, term ξ z) (p '' K) :=
    hs.hasSumUniformlyOn.tendstoUniformlyOn.continuousOn
      (Eventually.of_forall fun s ↦ (continuous_finsetSum s fun ξ _ ↦ ht ξ).continuousOn).frequently
  obtain ⟨C, hC⟩ := (hK.image hp).exists_bound_of_continuousOn hcont
  have hterm (ξ : Fˣ) (h : N₁[F]) : ‖φ (principal ξ * h)‖ = term ξ (p h) := by
    change ‖f (Multiplicative.ofAdd (((principal ξ).val * h.val * g).val))‖ =
      ‖f (Multiplicative.ofAdd ((h.val * g).val * (algebraMap F 𝔸[F] (ξ : F) + 0)))‖
    rw [hprincipal ξ, add_zero, mul_assoc,
      mul_comm (IdeleGroup.unitEmbedding (𝓞 F) F ξ), Units.val_mul]
    rfl
  let H (h : N₁[F]) := ENNReal.ofReal ‖φ h‖
  -- The compact translates may overlap, which gives an upper bound by the sum.
  calc
    (∫⁻ h, H h ∂μ₁) = ∫⁻ h in ⋃ ξ : Fˣ, (fun x : N₁[F] ↦ principal ξ * x) '' K, H h ∂μ₁ := by
      rw [hcover, Measure.restrict_univ]
    _ ≤ ∑' ξ : Fˣ, ∫⁻ h in (fun x : N₁[F] ↦ principal ξ * x) '' K, H h ∂μ₁ :=
      lintegral_iUnion_le _ _
    _ = ∑' ξ : Fˣ, ∫⁻ h in K, ENNReal.ofReal (term ξ (p h)) ∂μ₁ := by
      apply tsum_congr
      intro ξ
      exact ((measurePreserving_mul_left μ₁ (principal ξ)).setLIntegral_comp_emb
        (Homeomorph.mulLeft (principal ξ)).measurableEmbedding H K).symm.trans
        (lintegral_congr fun h ↦ congrArg ENNReal.ofReal (hterm ξ h))
    _ = ∫⁻ h in K, ∑' ξ : Fˣ, ENNReal.ofReal (term ξ (p h)) ∂μ₁ := by
      exact (lintegral_tsum fun ξ ↦
        (ENNReal.continuous_ofReal.comp ((ht ξ).comp hp)).aemeasurable).symm
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal C ∂μ₁ := by
      apply setLIntegral_mono measurable_const
      intro h hh
      have hmem : p h ∈ p '' K := mem_image_of_mem p hh
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ ↦ norm_nonneg _) (hs.summable hmem)]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC _ hmem))
    _ < ⊤ := by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- Paper: Lemma 2.2.5.2(1), p. 95. The integral of the adelic test function
against the character pulled back from the norm-one classes converges absolutely
on norm-one ideles. -/
theorem homogeneousAdelicTheta_idele_integrable (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) :
    Integrable (ideleIntegrand ω₁ f g) μ₁ := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hf : Continuous (fun h : N₁[F] ↦ f (Multiplicative.ofAdd (h.val * g).val)) :=
    (schwartzBruhat_continuous f).comp
      (continuous_ofAdd.comp (Units.continuous_val.comp (continuous_subtype_val.mul_const g)))
  have hq : Continuous (fun h : N₁[F] ↦ classOfNormOne h) := by
    apply Continuous.subtype_mk
    exact QuotientGroup.continuous_mk.comp continuous_subtype_val
  have hω : Continuous (fun h : N₁[F] ↦ (ω₁ (classOfNormOne h) : ℂ)) :=
    continuous_subtype_val.comp (ω₁.continuous.comp hq)
  exact (normOneIdele_testFunction_integrable f g).mono
    (hf.mul hω).aestronglyMeasurable
    (.of_forall fun h ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

open scoped Pointwise in
set_option maxSynthPendingDepth 8 in
/-- The half-open logarithmic box and torsion sector define a Borel fundamental set. -/
private theorem measurableSet_normOneIdele_domain
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v : InfinitePlace F) (r : CommRing.Pic (𝓞 F) → N₁[F]) :
    MeasurableSet (ideleFundamentalDomain F b v (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) r) := by
  classical
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let A := (InfiniteAdeleRing F)ˣ
  let K := (infiniteIdeleNorm F).ker
  let : MeasurableSpace A := borel _
  let : BorelSpace A := ⟨rfl⟩
  let D := infiniteIdeleFundamentalDomain F b v (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ)
  have hD : MeasurableSet D := by
    let L (g : K) : Units.dirichletUnitTheorem.logSpace F := fun w ↦ infiniteIdeleLog F g.val w.val
    have hL : Continuous L := continuous_pi fun w ↦ (continuous_apply w.val).comp
      ((infiniteIdeleLog_continuous F).comp continuous_subtype_val)
    let z (g : K) := InfinitePlace.Completion.extensionEmbedding v (g.val.val v)
    have hz : Continuous z := (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
      ((continuous_apply v).comp (Units.continuous_val.comp continuous_subtype_val))
    exact ((ZSpan.fundamentalDomain_measurableSet _).preimage hL.measurable).inter
      (measurableSet_Ico.preimage (Complex.measurable_arg.comp hz.measurable))
  have himg : MeasurableSet (K.subtype '' D) :=
    ((infiniteIdeleNorm_ker_closed F).isClosedEmbedding_subtypeVal.measurableEmbedding).measurableSet_image' hD
  obtain ⟨_, _, _, _, _, hFinite, ⟨ePic⟩⟩ := ideleClassGroup_finiteness F
  have : Finite (CommRing.Pic (𝓞 F)) := @Finite.of_equiv _ _ hFinite ePic.toEquiv
  apply MeasurableSet.iUnion
  intro c
  apply MeasurableSet.const_smul
  let j := Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom
  let q := Units.map (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)).toMonoidHom
  have hfin : MeasurableSet ((Subtype.val : N₁[F] → 𝕀[F]) ⁻¹' Set.range j) :=
    ((isOpenEmbedding_integralAdeleUnits F ∅).isOpen_range.preimage continuous_subtype_val).measurableSet
  have harch : MeasurableSet ((fun g : N₁[F] ↦ q g.val) ⁻¹' (K.subtype '' D)) :=
    himg.preimage ((continuous_fst.units_map _).comp continuous_subtype_val).measurable
  exact hfin.inter harch

open scoped ENNReal in
set_option maxSynthPendingDepth 8 in
/-- Taking the section strip of logarithmic length one fixes the mass of the fundamental domain. -/
private theorem normOneIdele_domain_mass
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v : InfinitePlace F) (r : CommRing.Pic (𝓞 F) → N₁[F]) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c) :
    μ₁ (ideleFundamentalDomain F b v (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) r) = μ̄₁ univ := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let : SigmaCompactSpace N₁[F] := by
    obtain ⟨i, -, K, hK, hcover⟩ := exists_compact_normOneIdele_cover (F := F)
    let D (ξ : Fˣ) := (fun h : N₁[F] ↦ i ξ * h) '' K
    refine SigmaCompactSpace.of_countable (range D) (countable_range D) ?_ ?_
    · rintro _ ⟨ξ, rfl⟩
      exact hK.image (continuous_const.mul continuous_id)
    · rwa [sUnion_range]
  let s := canonicalIdeleNormSection F
  have hs := canonicalIdeleNormSection_continuous F
  have hn := canonicalIdeleNormSection_rightInverse F
  obtain ⟨e, he⟩ := ideleNormSection_product F s hs hn
  let D := ideleFundamentalDomain F b v (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) r
  let T : ℝ≥0ˣ := expUnit (1 : ℝ)
  let J := {t : ℝ≥0ˣ | valueℝ t ∈ Icc 1 (valueℝ T)}
  have hT : 1 ≤ valueℝ T := Real.one_le_exp (by norm_num)
  have hlog : Real.log (valueℝ T) = 1 := Real.log_exp 1
  have hm : (positiveRealHaar.prod μ₁).map e = multiplicativeTamagawaMeasure F := by
    rw [show (⇑e) = fun tg ↦ s tg.1 * tg.2.val from funext fun p ↦ he p.1 p.2]
    exact multiplicativeTamagawaMeasure_normProduct F s hs hn
  have hstrip := multiplicativeTamagawaMeasure_sectionStrip F s hs hn v
    (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) b r hr₁ hr T hT
  have hset : e '' (J ×ˢ D) =
      {g | ∃ t ∈ J, ∃ x ∈ D, g = s t * (x : N₁[F]).val} := by
    ext g
    constructor
    · rintro ⟨⟨t,x⟩, ⟨ht,hx⟩, rfl⟩
      exact ⟨t, ht, x, hx, he t x⟩
    · rintro ⟨t, ht, x, hx, rfl⟩
      exact ⟨(t,x), ⟨ht,hx⟩, he t x⟩
  change multiplicativeTamagawaMeasure F {g | ∃ t ∈ J, ∃ x ∈ D, g = s t * (x : N₁[F]).val} =
    ENNReal.ofReal (Real.log (valueℝ T)) * μ̄₁ univ at hstrip
  have heM : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hJ : positiveRealHaar J = ENNReal.ofReal (Real.log (valueℝ T)) := positiveRealHaar_interval T hT
  rw [← hset, ← hm, heM.map_apply, Set.preimage_image_eq _ e.injective,
    Measure.prod_prod, hJ] at hstrip
  simpa [hlog] using hstrip

open scoped Pointwise ENNReal in
set_option maxSynthPendingDepth 8 in
/-- The principal translates tile the norm-one ideles with the normalized domain mass. -/
private theorem exists_normOneIdele_fundamentalDomain
    (i : Fˣ →* N₁[F]) (hi : ∀ ξ, (i ξ).val = IdeleGroup.unitEmbedding (𝓞 F) F ξ)
    (e : Fˣ ≃* i.range) (he : ∀ ξ, (e ξ).val = i ξ) :
    ∃ D : Set N₁[F], IsFundamentalDomain i.range D μ₁ ∧ μ₁ D = μ̄₁ univ := by
  classical
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  obtain ⟨b⟩ := regulator_units_mod_torsion_basis F
  obtain ⟨r, hr₁, hr⟩ := exists_normOne_class_representatives F
  let v := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  let σ : ℂ ≃ₐ[ℝ] ℂ := AlgEquiv.refl
  let D := ideleFundamentalDomain F b v σ r
  let j := (IdeleGroup.unitEmbedding (𝓞 F) F).codRestrict (ideleNorm F).ker
    (fun ξ ↦ (ideleNorm_spec F).2 (Set.mem_range_self ξ))
  have hji (ξ : Fˣ) : j ξ = i ξ := Subtype.ext (hi ξ).symm
  have hD : IsFundamentalDomain i.range D μ₁ := by
    apply IsFundamentalDomain.mk'' (measurableSet_normOneIdele_domain b v r).nullMeasurableSet
    · refine .of_forall fun x ↦ ?_
      have hcover := ideleFundamentalDomain_cover F b v σ r hr₁ hr
      have hx : x ∈ ⋃ ξ : Fˣ, j ξ • D := hcover ▸ mem_univ _
      obtain ⟨ξ, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
      refine ⟨(e ξ)⁻¹, ?_⟩
      change (e ξ).val⁻¹ * x ∈ D
      rw [he]
      change j ξ * y = x at hxy
      rwa [← hxy, hji, inv_mul_cancel_left]
    · intro a ha
      obtain ⟨ξ, rfl⟩ := e.surjective a
      have hξ : ξ ≠ 1 := fun h ↦ ha (h ▸ map_one e)
      have hd := (ideleFundamentalDomain_disjoint F b v σ r hr₁ hr ξ hξ).aedisjoint (μ := μ₁)
      change AEDisjoint _ ((e ξ).val • D) D
      rwa [he, ← hji]
    · exact fun a ↦ (measurePreserving_mul_left μ₁ a.val).quasiMeasurePreserving
  exact ⟨D, hD, normOneIdele_domain_mass b v r hr₁ hr⟩

/-- The Haar normalizations on the two norm-one groups agree on the principal quotient. -/
private theorem normOneIdele_map_restrict_of_domain (p : N₁[F] →* C₁[F]) (H : Subgroup N₁[F])
    [Countable H] (hp : Continuous p) (hsur : Surjective p) (hk : H ≤ p.ker)
    {D : Set N₁[F]} (hD : IsFundamentalDomain H D μ₁) (hmass : μ₁ D = μ̄₁ univ) :
    ((normOneIdeleTamagawaMeasure F).restrict D).map p = μ̄₁ := by
  classical
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : BorelSpace C[F] := ⟨rfl⟩
  let : T2Space 𝕀[F] := (ideleGroup_topology F).1
  let : T2Space C₁[F] := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let : (normOneIdeleTamagawaMeasure F).Regular :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.2.1
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : μ̄₁.Regular := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.1
  exact map_restrict_fundamentalDomain_eq p hp hsur H hk μ₁ μ̄₁ hD hmass

/-- Counting principal ideles on the fibers realizes the normalized quotient measure. -/
private theorem exists_normOneIdele_quotient_measure :
    ∃ (i : Fˣ →* N₁[F]) (p : N₁[F] →* C₁[F]) (e : Fˣ ≃* i.range) (D : Set N₁[F]),
      (∀ ξ, (i ξ).val = IdeleGroup.unitEmbedding (𝓞 F) F ξ) ∧
      (∀ x, p x = classOfNormOne x) ∧ (∀ ξ, (e ξ).val = i ξ) ∧
      (∀ ξ, p (i ξ) = 1) ∧ Continuous p ∧ IsFundamentalDomain i.range D μ₁ ∧
      ((normOneIdeleTamagawaMeasure F).restrict D).map p = μ̄₁ := by
  classical
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  obtain ⟨i, p, hi, hp, hiinj, -, -, hex, hop, -⟩ := normOne_idele_quotient F
  let H := i.range
  let e : Fˣ ≃* H := MulEquiv.ofBijective i.rangeRestrict
    ⟨fun _ _ h ↦ hiinj (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  let : Countable H := e.surjective.countable
  have hk : H ≤ p.ker := fun x ⟨u, hu⟩ ↦ (hex x).mpr ⟨u, hu⟩
  have hq (x : N₁[F]) : p x = classOfNormOne x := Subtype.ext (hp x)
  obtain ⟨D, hD, hmass⟩ := exists_normOneIdele_fundamentalDomain i hi e (fun _ ↦ rfl)
  refine ⟨i, p, e, D, hi, hq, fun _ ↦ rfl, fun ξ ↦ (hex _).mpr ⟨ξ, rfl⟩,
    hop.continuous, hD, ?_⟩
  exact normOneIdele_map_restrict_of_domain (F := F) p H hop.continuous hop.surjective hk hD hmass

open scoped Pointwise ENNReal in
/-- Periodizing the translated test function along principal ideles gives the class integrand. -/
private theorem homogeneousTheta_unfold (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) :
    homogeneousAdelicTheta ω₁ f (classOf g) = ∫ h, ideleIntegrand ω₁ f g h ∂μ₁ := by
  classical
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : BorelSpace C[F] := ⟨rfl⟩
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  obtain ⟨i, p, e, D, hi, hq, he, hk, hp, hD, hm⟩ := exists_normOneIdele_quotient_measure (F := F)
  let H := i.range
  let : Countable H := e.surjective.countable
  let Φ (x : N₁[F]) : ℂ := f (Multiplicative.ofAdd (x.val * g).val) * (ω₁ (p x) : ℂ)
  let A (h : C₁[F]) : ℂ := adelicTheta f (h.val * classOf g) * (ω₁ h : ℂ)
  have hA : Continuous A := ((adelicTheta f).continuous.comp
    (continuous_subtype_val.mul_const (classOf g))).mul (continuous_subtype_val.comp ω₁.continuous)
  have hperiod (x : N₁[F]) : A (p x) = ∑' a : H, Φ (a • x) := by
    rw [← e.toEquiv.tsum_eq (fun a : H ↦ Φ (a • x))]
    have hclass (ξ : Fˣ) : p (i ξ * x) = p x := by
      rw [map_mul, hk, one_mul]
    change adelicTheta f ((p x).val * classOf g) * (ω₁ (p x) : ℂ) = _
    rw [show (p x).val = classOf x.val from congrArg Subtype.val (hq x),
      ← QuotientGroup.mk_mul, adelicTheta_mk, ← tsum_mul_right]
    apply tsum_congr
    intro ξ
    change _ = f (Multiplicative.ofAdd ((((e ξ).val * x).val * g).val)) * (ω₁ (p ((e ξ).val * x)) : ℂ)
    rw [he, hclass, Subgroup.coe_mul, hi, mul_assoc, Units.val_mul]
    rfl
  have hΦ (x : N₁[F]) : Φ x = ideleIntegrand ω₁ f g x := congrArg
    (fun k ↦ f (Multiplicative.ofAdd (x.val * g).val) * (ω₁ k : ℂ)) (hq x)
  have hInt : Integrable Φ μ₁ := (homogeneousAdelicTheta_idele_integrable ω₁ f g).congr
    (.of_forall fun x ↦ (hΦ x).symm)
  change (∫ h, A h ∂μ̄₁) = ∫ x, ideleIntegrand ω₁ f g x ∂μ₁
  simp_rw [← hΦ]
  rw [← hm, integral_map hp.aemeasurable hA.aestronglyMeasurable,
    hD.integral_eq_tsum'' Φ hInt]
  simp_rw [hperiod]
  apply integral_tsum
  · exact fun a ↦ (hInt.1.comp_quasiMeasurePreserving
      (measurePreserving_mul_left μ₁ a.val).quasiMeasurePreserving).restrict
  · rw [← hD.lintegral_eq_tsum'' (‖Φ ·‖ₑ)]
    exact hInt.2.ne

/-- Paper: Lemma 2.2.5.2(1), p. 95. The norm-one idele integral against the
pulled-back character is continuous in the ambient idele. -/
theorem homogeneousAdelicTheta_idele_continuous (ω₁ : χ[F]) (f : ℬ[F]) :
    Continuous (fun g ↦ ∫ h, ideleIntegrand ω₁ f g h ∂μ₁) := by
  exact ((homogeneousAdelicTheta ω₁ f).continuous.comp QuotientGroup.continuous_mk).congr
    (fun g ↦ homogeneousTheta_unfold ω₁ f g)

/-- Paper: Lemma 2.2.5.2(1), p. 95. Inverse translation of the ambient
idele by a norm-one idele multiplies the integral by the pulled-back character. -/
theorem homogeneousAdelicTheta_idele_homogeneous (ω₁ : χ[F]) (f : ℬ[F])
    (h₀ : N₁[F]) (g : 𝕀[F]) :
    (∫ h, ideleIntegrand ω₁ f (h₀.val⁻¹ * g) h ∂μ₁) =
      (ω₁ (classOfNormOne h₀) : ℂ) * ∫ h, ideleIntegrand ω₁ f g h ∂μ₁ := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  have : (normOneIdeleTamagawaMeasure F).IsMulRightInvariant := ⟨fun k ↦ by
    rw [show (· * k) = (k * ·) from funext fun x ↦ mul_comm x k]
    exact map_mul_left_eq_self μ₁ k⟩
  rw [← integral_const_mul, ← integral_mul_right_eq_self _ h₀]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  have key : (x * h₀).val * (h₀.val⁻¹ * g) = x.val * g :=
    (mul_assoc (x.val : 𝕀[F]) h₀ _).trans (congrArg ((x.val : 𝕀[F]) * ·) (mul_inv_cancel_left _ g))
  have hcl : classOfNormOne (x * h₀) = classOfNormOne x * classOfNormOne h₀ := rfl
  simp only [key, hcl, map_mul, Circle.coe_mul]
  ring

/-- Paper: Lemma 2.2.5.2(2), p. 95. At an idele representative, homogeneous
theta equals the test-function integral over the norm-one ideles. -/
theorem homogeneousAdelicTheta_eq_idele_integral (ω₁ : χ[F]) (f : ℬ[F]) (g : 𝕀[F]) :
    homogeneousAdelicTheta ω₁ f (classOf g) = ∫ h, ideleIntegrand ω₁ f g h ∂μ₁ :=
  homogeneousTheta_unfold ω₁ f g

-- TODO(paper-gap): The paragraph on p. 96 describes h⁻¹ * g inside (2.2.5.2),
-- while the displayed integral and the equivariance computation on p. 97 use h * g.
-- Bound (2.2.5.5) reuses the unrestricted estimate flagged in §2.2.2.1(3).
-- TODO(later): needs §4.3.3 for the general construction cited by Remark 2.2.5.3.

/-- Paper: Theorem 2.2.5.4(1), p. 97. Inverse translation of a class by a
norm-one class acts on homogeneous theta by the prescribed character. -/
theorem homogeneousAdelicTheta_homogeneous (ω₁ : χ[F]) (f : ℬ[F]) (h : C₁[F]) (g : C[F]) :
    homogeneousAdelicTheta ω₁ f (h.val⁻¹ * g) = (ω₁ h : ℂ) * homogeneousAdelicTheta ω₁ f g := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have : μ̄₁.IsMulRightInvariant := ⟨fun k ↦ by
    rw [show (· * k) = (k * ·) from funext fun x ↦ mul_comm x k]
    exact map_mul_left_eq_self μ̄₁ k⟩
  simp only [homogeneousAdelicTheta, ContinuousMap.coe_mk]
  rw [← integral_const_mul, ← integral_mul_right_eq_self _ h]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  have key : (x : C[F]) * h * ((h : C[F])⁻¹ * g) = x * g := by
    exact (mul_assoc (x : C[F]) h _).trans (congrArg ((x : C[F]) * ·) (mul_inv_cancel_left _ g))
  simp only [Subgroup.coe_mul, key, map_mul, Circle.coe_mul]
  ring

/-- Norm-one classes do not change the idele class norm. -/
private theorem normℝ_normOne_mul (h : C₁[F]) (g : C[F]) : normℝ (h.val * g) = normℝ g := by
  simp only [map_mul, MonoidHom.mem_ker.mp h.property, one_mul]

/-- The idele class norm is positive. -/
private theorem normℝ_pos (g : C[F]) : 0 < normℝ g :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero (ideleClassNorm F g)))

/-- For norm at least one, an inverse power is an exponential in the absolute logarithm. -/
private theorem inv_pow_eq_exp_neg_abs_log {n : ℝ} (hn : 0 < n) (hl : 0 ≤ Real.log n) (N : ℕ) :
    (n ^ N)⁻¹ = Real.exp (-(N : ℝ) * |Real.log n|) := by
  rw [abs_of_nonneg hl, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn]

/-- For norm at most one, a power is an exponential in the absolute logarithm. -/
private theorem pow_eq_exp_neg_abs_log {n : ℝ} (hn : 0 < n) (hl : Real.log n ≤ 0) (N : ℕ) :
    n ^ N = Real.exp (-(N : ℝ) * |Real.log n|) := by
  rw [abs_of_nonpos hl, neg_mul_neg, Real.exp_nat_mul, Real.exp_log hn]

/-- Homogeneous theta is bounded by the norm-one class volume times a bound for theta
on the norm-one orbit. -/
private theorem norm_homogeneousAdelicTheta_le (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) {B : ℝ}
    (hB : ∀ h : C₁[F], ‖adelicTheta f (h.val * g)‖ ≤ B) :
    ‖homogeneousAdelicTheta ω₁ f g‖ ≤ (μ̄₁ univ).toReal * B := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  simp only [homogeneousAdelicTheta, ContinuousMap.coe_mk]
  refine (norm_integral_le_of_norm_le_const (.of_forall fun h ↦ ?_)).trans_eq
    (by rw [measureReal_def, mul_comm])
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact hB h

open scoped Classical in
/-- A character of the norm-one classes integrates to the volume if it is trivial,
and to zero otherwise. -/
private theorem integral_normOneCharacter (ω₁ : χ[F]) :
    ∫ h, (ω₁ h : ℂ) ∂μ̄₁ = if ω₁ = 1 then (((μ̄₁ univ).toReal : ℝ) : ℂ) else 0 := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have : μ̄₁.IsMulRightInvariant := ⟨fun k ↦ by
    rw [show (· * k) = (k * ·) from funext fun x ↦ mul_comm x k]
    exact map_mul_left_eq_self μ̄₁ k⟩
  split_ifs with hω
  · subst hω
    simp [PontryaginDual.one_apply, measureReal_def]
  · obtain ⟨h₀, hh₀⟩ : ∃ h₀, ω₁ h₀ ≠ 1 := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hω (ContinuousMonoidHom.ext fun h ↦ (hc h).trans (PontryaginDual.one_apply h).symm)
    have hne : (ω₁ h₀ : ℂ) ≠ 1 := fun h ↦ hh₀ (Circle.ext (h.trans Circle.coe_one.symm))
    have hinv := integral_mul_right_eq_self (μ := μ̄₁) (fun h ↦ (ω₁ h : ℂ)) h₀
    simp only [map_mul, Circle.coe_mul, integral_mul_const] at hinv
    have hzero : (∫ h, (ω₁ h : ℂ) ∂μ̄₁) * ((ω₁ h₀ : ℂ) - 1) = 0 := by
      rw [mul_sub, hinv, mul_one, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hne)

/-- Paper: Theorem 2.2.5.4(2), p. 97. At large norm, homogeneous theta decays
faster than every inverse power of the norm. -/
theorem homogeneousAdelicTheta_decay_large (ω₁ : χ[F]) (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < normℝ g →
      ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
  obtain ⟨C, T, hC, hT, hlarge⟩ := adelicTheta_decay_large f N
  have hV : 0 ≤ (μ̄₁ univ).toReal := ENNReal.toReal_nonneg
  refine ⟨((μ̄₁ univ).toReal + 1) * C, T, by positivity, hT, fun g hg ↦ ?_⟩
  have hx : 0 ≤ ((normℝ g) ^ N)⁻¹ := by have := normℝ_pos g; positivity
  have hB (h : C₁[F]) : ‖adelicTheta f (h.val * g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
    simpa only [normℝ_normOne_mul] using
      hlarge (h.val * g) (by simpa only [normℝ_normOne_mul] using hg)
  refine (norm_homogeneousAdelicTheta_le ω₁ f g hB).trans ?_
  nlinarith [mul_nonneg hC.le hx]

open scoped Classical in
/-- Paper: Equation (2.2.5.10), p. 97. The polar term is the norm-one class
volume times the difference of the two polar evaluations with reciprocal norm
on the Fourier value. It contributes only for the trivial character. -/
def homogeneousAdelicTheta_polarTerm (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) : ℂ :=
  if ω₁ = 1 then (μ̄₁ univ).toReal •
    ((normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele) else 0

/-- Paper: Equation (2.2.5.10), p. 97. At norm one and for the trivial
character the polar term is the class volume times the difference of the evaluations. -/
theorem homogeneousAdelicTheta_polarTerm_trivial_at_one (f : ℬ[F]) :
    homogeneousAdelicTheta_polarTerm (1 : χ[F]) f 1 =
      (μ̄₁ univ).toReal • (adeleSchwartzFourier f zeroAdele - f zeroAdele) := by
  simp [homogeneousAdelicTheta_polarTerm]

/-- After subtracting the polar term, homogeneous theta is bounded by the norm-one class
volume times a bound for theta minus its polar terms on the norm-one orbit. -/
private theorem norm_homogeneousAdelicTheta_sub_polarTerm_le (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F])
    {B : ℝ} (hB : ∀ h : C₁[F], ‖adelicTheta f (h.val * g) -
      (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤ B) :
    ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
      (μ̄₁ univ).toReal * B := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let P : ℂ := (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele
  have hωint : Integrable (fun h : C₁[F] ↦ (ω₁ h : ℂ)) μ̄₁ :=
    (continuous_subtype_val.comp ω₁.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpol : homogeneousAdelicTheta_polarTerm ω₁ f g = ∫ h, P * (ω₁ h : ℂ) ∂μ̄₁ := by
    rw [integral_const_mul, integral_normOneCharacter, homogeneousAdelicTheta_polarTerm]
    split_ifs
    · rw [Complex.real_smul, mul_comm]
    · rw [mul_zero]
  have hΦ : homogeneousAdelicTheta ω₁ f g =
      ∫ h, adelicTheta f (h.val * g) * (ω₁ h : ℂ) ∂μ̄₁ := rfl
  have hint : Integrable (fun h : C₁[F] ↦ adelicTheta f (h.val * g) * (ω₁ h : ℂ)) μ̄₁ :=
    homogeneousAdelicTheta_integrable ω₁ f g
  have hsub : homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g =
      ∫ h, (adelicTheta f (h.val * g) - P) * (ω₁ h : ℂ) ∂μ̄₁ := by
    rw [hΦ, hpol, ← integral_sub hint (hωint.const_mul P)]
    exact integral_congr_ae (.of_forall fun h ↦ (sub_mul _ _ _).symm)
  rw [hsub]
  refine (norm_integral_le_of_norm_le_const (.of_forall fun h ↦ ?_)).trans_eq
    (by rw [measureReal_def, mul_comm])
  rw [norm_mul, Circle.norm_coe, mul_one]
  have hP : adelicTheta f (h.val * g) - P =
      adelicTheta f (h.val * g) - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele +
        f zeroAdele := by
    simp only [P]
    ring
  rw [hP]
  exact hB h

/-- Paper: Theorem 2.2.5.4(2), p. 97. After subtracting the polar term,
homogeneous theta decays faster than every power of the norm at small norm. -/
theorem homogeneousAdelicTheta_decay_small (ω₁ : χ[F]) (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], normℝ g < T →
      ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
        C * (normℝ g) ^ N := by
  obtain ⟨C, T, hC, hT, hsmall⟩ := adelicTheta_decay_small f N
  have hV : 0 ≤ (μ̄₁ univ).toReal := ENNReal.toReal_nonneg
  refine ⟨((μ̄₁ univ).toReal + 1) * C, T, by positivity, hT, fun g hg ↦ ?_⟩
  have hx : 0 ≤ (normℝ g) ^ N := by have := normℝ_pos g; positivity
  have hB (h : C₁[F]) : ‖adelicTheta f (h.val * g) -
      (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤ C * (normℝ g) ^ N := by
    simpa only [normℝ_normOne_mul] using
      hsmall (h.val * g) (by simpa only [normℝ_normOne_mul] using hg)
  refine (norm_homogeneousAdelicTheta_sub_polarTerm_le ω₁ f g hB).trans ?_
  nlinarith [mul_nonneg hC.le hx]

/-- A positive-real slope gives the ordinary derivative after exponential reparametrization. -/
private theorem log_deriv_of_tendsto_unit_slope (A : ℝ≥0ˣ → ℂ) (v : ℂ)
    (h : Tendsto (fun t : ℝ≥0ˣ ↦ (A t - A 1) / ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 v)) :
    HasDerivAt (fun s : ℝ ↦ A (expUnit s)) v 0 := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have h0 : E 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hE : Tendsto E (𝓝[≠] 0) (𝓝[≠] 1) := by
    rw [← h0]
    refine tendsto_nhdsWithin_iff.mpr ⟨E.continuous.continuousAt.continuousWithinAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun he ↦ ht (E.injective he)
  have he : HasDerivAt (fun t : ℝ ↦ (Real.exp t : ℂ)) 1 0 := by
    simpa only [Real.exp_zero, Complex.ofReal_one] using (Real.hasDerivAt_exp 0).ofReal_comp
  have hp := (h.comp hE).mul he.tendsto_slope
  rw [mul_one] at hp
  change HasDerivAt (A ∘ E) v 0
  rw [hasDerivAt_iff_tendsto_slope]
  refine hp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : (Real.exp t : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ ht (Real.exp_injective
    ((Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)).trans Real.exp_zero.symm))
  change ((A (E t) - A 1) / ((Real.exp t : ℂ) - 1)) * _ = _
  simp only [slope_def_module, sub_zero, Real.exp_zero, Complex.ofReal_one, Function.comp_apply, h0,
    Complex.real_smul]
  field_simp [hn]

/-- Translate the derivative at the identity to every point of a one-parameter orbit. -/
private theorem unit_orbit_hasDerivAt {G : Type*} [Group G] (a : ℝ≥0ˣ →* G) (A d : G → ℂ)
    (h : ∀ g, Tendsto (fun t : ℝ≥0ˣ ↦ (A (a t * g) - A g) / ((valueℝ t : ℂ) - 1))
      (𝓝[≠] 1) (𝓝 (d g))) (g : G) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ A (a (expUnit t) * g)) (d (a (expUnit s) * g)) s := by
  let E : ℝ → ℝ≥0ˣ := expUnit
  let y := a (E s) * g
  have hD : HasDerivAt (fun t : ℝ ↦ A (a (E t) * y)) (d y) (s - s) := by
    rw [sub_self]
    apply log_deriv_of_tendsto_unit_slope (fun t ↦ A (a t * y))
    simpa only [map_one, one_mul] using h y
  refine (hD.comp_sub_const s s).congr_of_eventuallyEq (.of_forall fun t ↦ ?_)
  have hmul : E (t - s) * E s = E t := Units.ext (NNReal.coe_inj.mp
    ((Real.exp_add (t - s) s).symm.trans (congrArg Real.exp (sub_add_cancel t s))))
  change A (a (E t) * g) = A (a (E (t - s)) * (a (E s) * g))
  rw [← mul_assoc, ← map_mul, hmul]

/-- On a compact parameter space a jointly continuous orbit derivative is bounded locally
in time, so differentiation commutes with integration. -/
private theorem compact_average_hasDerivAt {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (P Q : ℝ → K → ℂ) (hP : Continuous (uncurry P)) (hQ : Continuous (uncurry Q))
    (hd : ∀ h s, HasDerivAt (fun t ↦ P t h) (Q s h) s) :
    HasDerivAt (fun s ↦ ∫ h, P s h ∂μ) (∫ h, Q 0 h ∂μ) 0 := by
  have hint (s : ℝ) : Integrable (P s) μ :=
    (hP.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : IsCompact ((Icc (-1 : ℝ) 1) ×ˢ (univ : Set K)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hQ.continuousOn
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (s := Icc (-1 : ℝ) 1) (F := P) (F' := Q) (bound := fun _ ↦ B)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) zero_lt_one)
    (.of_forall fun s ↦ (hint s).aestronglyMeasurable) (hint 0)
    (hQ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall fun h s hs ↦ hB (s, h) ⟨hs, mem_univ _⟩) (integrable_const B)
    (.of_forall fun h s _ ↦ hd h s)).2

/-- Paper: Theorem 2.2.5.4(3), p. 97. Homogeneous theta commutes with
directional differentiation. The difference quotient tends to homogeneous theta
of the differentiated test function. -/
theorem homogeneousAdelicTheta_directionalDeriv (γ : ℝ≥0ˣ →ₜ* 𝕀[F])
    (ω₁ : χ[F]) (f : ℬ[F]) (g : C[F]) :
    Tendsto (fun t : ℝ≥0ˣ ↦
      (homogeneousAdelicTheta ω₁ f (classOf (γ t) * g) - homogeneousAdelicTheta ω₁ f g) /
        ((valueℝ t : ℂ) - 1)) (𝓝[≠] 1) (𝓝 (homogeneousAdelicTheta ω₁ (adeleDirectionalDeriv γ f) g)) := by
  let : BorelSpace C[F] := ⟨rfl⟩
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : μ̄₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let d := adeleDirectionalDeriv γ f
  let a (s : ℝ) : C[F] := classOf (γ (expUnit s))
  have ha : Continuous a := QuotientGroup.continuous_mk.comp (γ.continuous.comp
    ((Nonneg.unitsHomeomorphPos ℝ).symm.continuous.comp Real.expOrderIso.continuous))
  have ha0 : a 0 = 1 := by
    change classOf (γ (expUnit (0 : ℝ))) = 1
    have h0 : expUnit (0 : ℝ) = (1 : ℝ≥0ˣ) := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
    exact congrArg (fun z : 𝕀[F] ↦ (classOf z : C[F])) ((congrArg γ h0).trans (map_one γ))
  let P (φ : ℬ[F]) (s : ℝ) (h : C₁[F]) := classIntegrand ω₁ φ (a s * g) h
  have hP (φ : ℬ[F]) : Continuous (uncurry (P φ)) :=
    ((adelicTheta φ).continuous.comp ((continuous_subtype_val.comp continuous_snd).mul
      ((ha.comp continuous_fst).mul_const g))).mul
      (continuous_subtype_val.comp (ω₁.continuous.comp continuous_snd))
  let q : ℝ≥0ˣ →* C[F] := (QuotientGroup.mk' _).comp γ.toMonoidHom
  have hθ := unit_orbit_hasDerivAt q (adelicTheta f) (adelicTheta d) (adelicTheta_directionalDeriv γ f)
  have hD (h : C₁[F]) (s : ℝ) : HasDerivAt (fun t ↦ P f t h) (P d s h) s := by
    have hz := (hθ (h.val * g) s).mul_const (ω₁ h : ℂ)
    change HasDerivAt (fun t ↦ adelicTheta f (a t * (h.val * g)) * (ω₁ h : ℂ))
      (adelicTheta d (a s * (h.val * g)) * (ω₁ h : ℂ)) s at hz
    change HasDerivAt (fun t ↦ adelicTheta f (h.val * (a t * g)) * (ω₁ h : ℂ))
      (adelicTheta d (h.val * (a s * g)) * (ω₁ h : ℂ)) s
    simp only [mul_left_comm h.val]
    exact hz
  have h := compact_average_hasDerivAt μ̄₁ (P f) (P d) (hP f) (hP d) hD
  change HasDerivAt (fun s ↦ homogeneousAdelicTheta ω₁ f (a s * g))
    (homogeneousAdelicTheta ω₁ d (a 0 * g)) 0 at h
  rw [ha0, one_mul g] at h
  have h1 : (classOf (γ 1) : C[F]) * g = g := by rw [map_one γ]; exact one_mul g
  simpa only [h1] using tendsto_unit_slope_of_log_deriv
    (fun t ↦ homogeneousAdelicTheta ω₁ f (classOf (γ t) * g)) _ h

/-- Repeated differentiation of the test function gives smoothness along every real
one-parameter subgroup in the logarithmic parameter. -/
private theorem homogeneousTheta_log_orbit_smooth (γ : ℝ≥0ˣ →ₜ* 𝕀[F]) (ω₁ : χ[F]) (g : C[F])
    (f : ℬ[F]) : ContDiff ℝ (∞ : ℕ∞ω) (fun s : ℝ ↦ homogeneousAdelicTheta ω₁ f (classOf (γ (expUnit s)) * g)) := by
  let q : ℝ≥0ˣ →* C[F] := (QuotientGroup.mk' _).comp γ.toMonoidHom
  let A (φ : ℬ[F]) (s : ℝ) := homogeneousAdelicTheta ω₁ φ (q (expUnit s) * g)
  have h (φ : ℬ[F]) (s : ℝ) : HasDerivAt (A φ) (A (adeleDirectionalDeriv γ φ) s) s :=
    unit_orbit_hasDerivAt q (homogeneousAdelicTheta ω₁ φ) (homogeneousAdelicTheta ω₁ (adeleDirectionalDeriv γ φ))
      (homogeneousAdelicTheta_directionalDeriv γ ω₁ φ) g s
  have hN (n : ℕ) (φ : ℬ[F]) : ContDiff ℝ n (A φ) := by
    induction n generalizing φ with
    | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun s ↦ (h φ s).continuousAt)
    | succ n ih =>
      refine (contDiff_succ_iff_deriv (n := (n : ℕ∞ω))).mpr ⟨fun s ↦ (h φ s).differentiableAt, by simp, ?_⟩
      rw [show deriv (A φ) = A (adeleDirectionalDeriv γ φ) from funext fun s ↦ (h φ s).deriv]
      exact ih _
  exact contDiff_infty.mpr fun n ↦ hN n f

open scoped Classical in
set_option maxSynthPendingDepth 8 in
/-- Paper: Theorem 2.2.5.4(3), p. 98. With the finite component fixed,
homogeneous theta on ideles is smooth in the archimedean units. The charts
are the units charts in the real and complex completion coordinates. -/
theorem homogeneousAdelicTheta_archimedean_smooth (ω₁ : χ[F]) (f : ℬ[F])
    (g : 𝔸ᶠ[F]ˣ) :
    let e := Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMulEquiv
    ContMDiff 𝓘(ℝ, mixedEmbedding.mixedSpace F) 𝓘(ℝ, ℂ) (∞ : ℕ∞ω)
      (fun a : (mixedEmbedding.mixedSpace F)ˣ ↦
        homogeneousAdelicTheta ω₁ f (classOf
          ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) 𝔸ᶠ[F]).symm
            (e.symm a, g)))) := by
  let V := mixedEmbedding.mixedSpace F
  let e := Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMulEquiv
  let J := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) 𝔸ᶠ[F]).symm
  let j : Vˣ →* 𝕀[F] := J.toMonoidHom.comp ((MonoidHom.inl _ _).comp e.symm.toMonoidHom)
  have hj : Continuous j := J.continuous.comp
    (((continuous_mixedCoordinates (F := F)).2.units_map _).prodMk continuous_const)
  let n := (ideleNorm F).comp j
  have hn : Continuous n := (ideleGroup_topology F).2.2.2.2.1.comp hj
  let γ : ℝ≥0ˣ →ₜ* 𝕀[F] := ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  let q : 𝕀[F] →* C[F] := QuotientGroup.mk' _
  let k := (q.comp (γ.toMonoidHom.comp n)) / (q.comp j)
  have hkn (a : Vˣ) : k a ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (q (γ (n a)) / q (j a)) = 1
    rw [map_div]
    change ideleNorm F (canonicalIdeleNormSection F (n a)) / n a = 1
    rw [canonicalIdeleNormSection_rightInverse F, div_self']
  let K := k.codRestrict (ideleClassNorm F).ker hkn
  have hK : Continuous K := Continuous.subtype_mk
    (by
      have hq : Continuous q := QuotientGroup.continuous_mk
      change Continuous (fun x ↦ q (γ (n x)) / q (j x))
      simp_rw [div_eq_mul_inv]
      exact (hq.comp (γ.continuous.comp hn)).mul (hq.comp hj).inv) _
  let χ := Circle.coeHom.comp (ω₁.toMonoidHom.comp K)
  have hχ : Continuous χ := continuous_subtype_val.comp (ω₁.continuous.comp hK)
  let N : Vˣ →* ℂ :=
    { toFun := fun a ↦ (valueℝ (n a) : ℂ)
      map_one' := by simp
      map_mul' := fun a b ↦ by simp only [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul] }
  have hN : Continuous N := Complex.continuous_ofReal.comp
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hn))
  have hNre : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) (fun a ↦ valueℝ (n a)) :=
    Complex.reCLM.contDiff.contMDiff.comp (contMDiff_units_character N hN)
  let g₀ : C[F] := q (J (1,g))
  let R (s : ℝ) := homogeneousAdelicTheta ω₁ f (q (γ (expUnit s)) * g₀)
  have hR : ContDiff ℝ (∞ : ℕ∞ω) R := homogeneousTheta_log_orbit_smooth γ ω₁ g₀ f
  have hL : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) (fun a ↦ Real.log (valueℝ (n a))) := by
    intro a
    exact (Real.contDiffAt_log.mpr (NNReal.coe_ne_zero.mpr (n a).ne_zero)).contMDiffAt.comp a (hNre a)
  let P (a : Vˣ) := χ a * R (Real.log (valueℝ (n a)))
  have hP : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℂ) (∞ : ℕ∞ω) P :=
    (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
      ((contMDiff_prod_module_iff (fun a : Vˣ ↦ (χ a, R (Real.log (valueℝ (n a)))))).mpr
      ⟨contMDiff_units_character χ hχ, hR.contMDiff.comp hL⟩)
  apply hP.congr
  intro a
  have hE : expUnit (Real.log (valueℝ (n a))) = n a :=
    Units.ext (NNReal.coe_inj.mp (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))))
  have hsplit : J (e.symm a, g) = J (e.symm a, 1) * J (1, g) := by
    rw [← map_mul]
    simp
  have harg : (K a).val⁻¹ * (q (γ (n a)) * g₀) = q (J (e.symm a, g)) := by
    change (q (γ (n a)) / q (J (e.symm a, 1)))⁻¹ * (q (γ (n a)) * q (J (1, g))) = _
    rw [hsplit, map_mul, div_eq_mul_inv]; simp [mul_assoc]
  have hhom := homogeneousAdelicTheta_homogeneous ω₁ f (K a) (q (γ (n a)) * g₀)
  rw [harg] at hhom
  change homogeneousAdelicTheta ω₁ f (q (J (e.symm a, g))) = χ a * R (Real.log (valueℝ (n a)))
  rw [show R (Real.log (valueℝ (n a))) = homogeneousAdelicTheta ω₁ f (q (γ (n a)) * g₀) by simp only [R, hE]]
  exact hhom

-- TODO(paper-gap): The proof of Theorem 2.2.5.4(3) repeats the same term in
-- (2.2.5.13), then uses γ(t⁻¹) with the sign for γ(t) in (2.2.5.15).

/-- Paper: Theorem 2.2.5.4(4), p. 98. For a test function in the polar
subspace or a nontrivial character, homogeneous theta decays at both ends
at every exponential rate in the absolute logarithmic norm. -/
theorem homogeneousAdelicTheta_decay_both (ω₁ : χ[F]) (f : ℬ[F])
    (h : f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < |Real.log (normℝ g)| →
      ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by
  have hV : 0 ≤ (μ̄₁ univ).toReal := ENNReal.toReal_nonneg
  rcases h with hf | hω
  · obtain ⟨hf0, hF0⟩ := (mem_adelePolarSubspace f).mp hf
    obtain ⟨C, T, hC, hT, hboth⟩ := adelicTheta_decay_both f hf0 hF0 N
    refine ⟨((μ̄₁ univ).toReal + 1) * C, T, by positivity, hT, fun g hg ↦ ?_⟩
    have hx : 0 ≤ Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := (Real.exp_pos _).le
    have hB (h : C₁[F]) : ‖adelicTheta f (h.val * g)‖ ≤
        C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by
      simpa only [normℝ_normOne_mul] using
        hboth (h.val * g) (by simpa only [normℝ_normOne_mul] using hg)
    refine (norm_homogeneousAdelicTheta_le ω₁ f g hB).trans ?_
    nlinarith [mul_nonneg hC.le hx]
  · obtain ⟨C₁, T₁, hC₁, hT₁, hlarge⟩ := homogeneousAdelicTheta_decay_large ω₁ f N
    obtain ⟨C₂, T₂, hC₂, hT₂, hsmall⟩ := homogeneousAdelicTheta_decay_small ω₁ f N
    refine ⟨C₁ + C₂, max (max |Real.log T₁| |Real.log T₂|) 1, by positivity, by positivity,
      fun g hg ↦ ?_⟩
    have hn := normℝ_pos g
    have hx : 0 ≤ Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := (Real.exp_pos _).le
    have h1 := le_abs_self (Real.log T₁)
    have h2 := neg_abs_le (Real.log T₂)
    have hm1 := le_max_left (max |Real.log T₁| |Real.log T₂|) 1
    have hm11 := le_max_left |Real.log T₁| |Real.log T₂|
    have hm12 := le_max_right |Real.log T₁| |Real.log T₂|
    rcases le_or_gt 0 (Real.log (normℝ g)) with hl | hl
    · rw [abs_of_nonneg hl] at hg
      have hT : T₁ < normℝ g := by
        rw [← Real.log_lt_log_iff hT₁ hn]
        linarith
      have := hlarge g hT
      rw [inv_pow_eq_exp_neg_abs_log hn hl] at this
      nlinarith [mul_nonneg hC₂.le hx]
    · rw [abs_of_neg hl] at hg
      have hT : normℝ g < T₂ := by
        rw [← Real.log_lt_log_iff hn hT₂]
        linarith
      have := hsmall g hT
      simp only [homogeneousAdelicTheta_polarTerm, hω, ite_false, sub_zero] at this
      rw [pow_eq_exp_neg_abs_log hn hl.le] at this
      nlinarith [mul_nonneg hC₁.le hx]

-- TODO(paper-gap): The last sentence of Theorem 2.2.5.4(4) uses the
-- conjugate of ω to descend to the logarithmic norm. Even after choosing a
-- character extension, this transforms by ω(h)⁻² under translation by h.

-- TODO(paper-gap): Theorem 2.2.5.4(5) cites (2.2.5.11) among the estimates
-- with a constant and a threshold, although it is an identity valid everywhere.

/-- The uniform estimates of Theorem 2.2.5.4(5) with logarithmic threshold one: averaging the
uniform theta bounds of Theorem 2.2.3.4(5) over the norm-one classes. -/
private theorem homogeneousAdelicTheta_decay_bounded_uniform (ω₁ : χ[F]) (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F],
      (1 < Real.log (normℝ g) → ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (1 < -Real.log (normℝ g) →
        ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
          C * (normℝ g) ^ N) ∧
      ((f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) → 1 < |Real.log (normℝ g)| →
        ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by
  -- The application is elaborated in steps, each by `have`: applied in one step, or inside
  -- `obtain`, the unifier unfolds the Schwartz–Bruhat instances and times out.
  have hB₀ := adelicTheta_decay_bounded_threshold_one (F := F) B
  have hB₁ := hB₀ hB N
  obtain ⟨C, hC, hb⟩ := hB₁
  have hV : 0 ≤ (μ̄₁ univ).toReal := ENNReal.toReal_nonneg
  refine ⟨((μ̄₁ univ).toReal + 1) * C, by positivity, fun f hf g ↦ ?_⟩
  have hn := normℝ_pos g
  have P1 : 1 < Real.log (normℝ g) →
      ‖homogeneousAdelicTheta ω₁ f g‖ ≤ ((μ̄₁ univ).toReal + 1) * C * ((normℝ g) ^ N)⁻¹ := by
    intro hl
    have hg : 1 < normℝ g := by
      by_contra hc
      have := Real.log_nonpos hn.le (not_lt.mp hc)
      linarith
    have hx : 0 ≤ ((normℝ g) ^ N)⁻¹ := by positivity
    have hB' (h : C₁[F]) : ‖adelicTheta f (h.val * g)‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by
      simpa only [normℝ_normOne_mul] using
        (hb f hf (h.val * g)).1 (by simpa only [normℝ_normOne_mul] using hg)
    refine (norm_homogeneousAdelicTheta_le ω₁ f g hB').trans ?_
    nlinarith [mul_nonneg hC.le hx]
  have P2 : 1 < -Real.log (normℝ g) →
      ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
        ((μ̄₁ univ).toReal + 1) * C * (normℝ g) ^ N := by
    intro hl
    have hg : normℝ g < 1 := by
      by_contra hc
      have := Real.log_nonneg (not_lt.mp hc)
      linarith
    have hx : 0 ≤ (normℝ g) ^ N := by positivity
    have hB' (h : C₁[F]) : ‖adelicTheta f (h.val * g) -
        (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤ C * (normℝ g) ^ N := by
      simpa only [normℝ_normOne_mul] using
        (hb f hf (h.val * g)).2.1 (by simpa only [normℝ_normOne_mul] using hg)
    refine (norm_homogeneousAdelicTheta_sub_polarTerm_le ω₁ f g hB').trans ?_
    nlinarith [mul_nonneg hC.le hx]
  refine ⟨P1, P2, fun hpol habs ↦ ?_⟩
  have hx : 0 ≤ Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := (Real.exp_pos _).le
  rcases hpol with hf' | hω
  · obtain ⟨hf0, hF0⟩ := (mem_adelePolarSubspace f).mp hf'
    have he : Real.exp (-|Real.log (normℝ g)|) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hB' (h : C₁[F]) : ‖adelicTheta f (h.val * g)‖ ≤
        C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by
      simpa only [normℝ_normOne_mul] using
        (hb f hf (h.val * g)).2.2 hf0 hF0 (by simpa only [normℝ_normOne_mul] using he)
    refine (norm_homogeneousAdelicTheta_le ω₁ f g hB').trans ?_
    nlinarith [mul_nonneg hC.le hx]
  · rcases le_or_gt 0 (Real.log (normℝ g)) with hl | hl
    · rw [abs_of_nonneg hl] at habs
      have := P1 habs
      rwa [inv_pow_eq_exp_neg_abs_log hn hl] at this
    · rw [abs_of_neg hl] at habs
      have := P2 habs
      simp only [homogeneousAdelicTheta_polarTerm, hω, ite_false, sub_zero] at this
      rwa [pow_eq_exp_neg_abs_log hn hl.le] at this

/-- Paper: Theorem 2.2.5.4(5), p. 98. The large-norm, small-norm and two-sided
estimates have a common constant and logarithmic threshold uniform over a
bounded set of test functions. The two-sided bound retains the condition in (4). -/
theorem homogeneousAdelicTheta_decay_bounded (ω₁ : χ[F]) (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C[F],
      (T < Real.log (normℝ g) → ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (T < -Real.log (normℝ g) →
        ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
          C * (normℝ g) ^ N) ∧
      ((f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) → T < |Real.log (normℝ g)| →
        ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by
  have h₀ := homogeneousAdelicTheta_decay_bounded_uniform ω₁ B
  have h₁ := h₀ hB N
  obtain ⟨C, hC, hb⟩ := h₁
  exact ⟨C, 1, hC, zero_lt_one, hb⟩

/-- Paper: Theorem 2.2.5.4(6), p. 98. The three uniform estimates hold with
logarithmic threshold one and a common constant. -/
theorem homogeneousAdelicTheta_decay_bounded_threshold_one (ω₁ : χ[F]) (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F],
      (1 < Real.log (normℝ g) → ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (1 < -Real.log (normℝ g) →
        ‖homogeneousAdelicTheta ω₁ f g - homogeneousAdelicTheta_polarTerm ω₁ f g‖ ≤
          C * (normℝ g) ^ N) ∧
      ((f ∈ adelePolarSubspace F ∨ ω₁ ≠ 1) → 1 < |Real.log (normℝ g)| →
        ‖homogeneousAdelicTheta ω₁ f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by
  have h₀ := homogeneousAdelicTheta_decay_bounded_uniform ω₁ B
  exact h₀ hB N

end HomogeneousTheta

end RiemannMasullo
