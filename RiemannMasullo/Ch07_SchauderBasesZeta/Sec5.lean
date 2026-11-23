module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

import all RiemannMasullo.Ch03_IdelicZeta.Sec2

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec5

import Mathlib.Analysis.Calculus.DSlope
import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

/-! # §7.5 Strong co-primality -/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "C₁" => (ideleClassNorm F).ker
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "P" => adelePolarSubspace F
local notation "K(" ω ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P)
local notation "B" => SchwartzBergman (univ : Set ℝ)

local instance instIdeleClassT2Sec5 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec5 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

local instance instIdeleClassSecondCountableSec5 : SecondCountableTopology C𝔽 :=
  letI : SecondCountableTopology I𝔽 := idele_secondCountable F
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.1.secondCountableTopology

/-- Paper: Equation (7.5.0.2), p. 374.
The pole-free homogeneous theta space is the quotient of zero-moment tests
by the kernel of their homogeneous theta transform.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev StrongCoprimalityThetaSpace (ω : PontryaginDual C₁) := ↥P ⧸ K(ω)

/-- Paper: Equation (7.5.0.2), p. 374.
The comparison space is the norm-one isotype of the full exponential-decay space. -/
abbrev StrongCoprimalityDecaySpace (ω : PontryaginDual C₁) :=
  ↥(modulatedDecayIsotype m𝔽 univ (mem_univ (0 : ℝ)) ω)

/-- Paper: Equation (7.5.0.2), p. 374.
The homogeneous theta transform of a zero-moment test is an exponentially decaying function of
the given isotype, continuously in the test. Continuity is with respect to the topology of the
zero-moment test space and that of the isotype. -/
theorem exists_strongCoprimalityThetaLinearMap (ω : PontryaginDual C₁) :
    ∃ T : P →L[ℂ] StrongCoprimalityDecaySpace ω, ∀ (f : P) (g : C𝔽),
      (T f).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g := by sorry

private theorem exists_strongCoprimalityThetaEmbedding_ker_le (ω : PontryaginDual C₁)
    (T : P →L[ℂ] StrongCoprimalityDecaySpace ω)
    (hT : ∀ (f : P) (g : C𝔽),
      (T f).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g) :
    K(ω) ≤ T.ker := by
  intro f hf
  rw [LinearMap.mem_ker]
  have h0 : (homogeneousAdelicThetaLinearMap F ω) (f : P) = 0 := by
    simpa only [LinearMap.mem_ker, LinearMap.domRestrict_apply] using hf
  refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
  have hg : (T f).val.val g = 0 := by
    rw [hT, h0]
    simp
  exact hg.trans (by rfl)

/-- Paper: Equation (7.5.0.2), p. 374.
Two zero-moment tests with the same homogeneous theta function give the same class, so a
map with the theta values separates the classes of the pole-free theta space. -/
private theorem exists_strongCoprimalityThetaEmbedding_injective (ω : PontryaginDual C₁)
    (j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω)
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g) :
    Function.Injective j := by
  intro x y hxy
  obtain ⟨f, rfl⟩ := (K(ω)).mkQ_surjective x
  obtain ⟨f', rfl⟩ := (K(ω)).mkQ_surjective y
  have hθ : (homogeneousAdelicThetaLinearMap F ω) (f : P) =
      (homogeneousAdelicThetaLinearMap F ω) (f' : P) := by
    ext g
    rw [← hj f g, ← hj f' g, hxy]
  have hmem : f - f' ∈ (K(ω) : Submodule ℂ P) := by
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.coe_sub, map_sub, hθ, sub_self]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact hmem

/-- Paper: Equation (7.5.0.2), p. 374.
The homogeneous theta functions of zero-moment tests form a closed subspace of the
exponentially decaying isotype, so the theta transform is a topological embedding.
The paper obtains this from the Mellin model of §7.4, where the theta image is the
closed denominator of the nuclearity quotient. -/
private theorem exists_strongCoprimalityThetaEmbedding_isInducing (ω : PontryaginDual C₁)
    (j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω)
    (hj : ∀ (f : P) (g : C𝔽),
      (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g) :
    IsInducing j := by sorry

/-- Paper: Equation (7.5.0.2), p. 374.
The topological linear embedding takes a zero-moment test class to its homogeneous theta
function, viewed in the corresponding exponentially decaying isotype. -/
theorem exists_strongCoprimalityThetaEmbedding (ω : PontryaginDual C₁) :
    ∃ j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω,
      IsEmbedding j ∧ ∀ (f : P) (g : C𝔽),
        (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g := by
  obtain ⟨T, hT⟩ := exists_strongCoprimalityThetaLinearMap (F := F) ω
  have hker : K(ω) ≤ T.ker :=
    exists_strongCoprimalityThetaEmbedding_ker_le (F := F) ω T hT
  set j : StrongCoprimalityThetaSpace ω →L[ℂ] StrongCoprimalityDecaySpace ω :=
    (K(ω)).liftQL T hker with hj
  have hformula : ∀ (f : P) (g : C𝔽),
      (j ((K(ω)).mkQ f)).val.val g = homogeneousAdelicThetaLinearMap F ω f.val g := by
    intro f g
    rw [hj, Submodule.liftQL_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
    exact hT f g
  exact ⟨j, ⟨exists_strongCoprimalityThetaEmbedding_isInducing (F := F) ω j hformula,
      exists_strongCoprimalityThetaEmbedding_injective (F := F) ω j hformula⟩, hformula⟩

private theorem strongCoprimalityPrincipalValue_mem_polar_of_line
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (W : Submodule ℂ (StrongDual ℂ E)) (b l k : StrongDual ℂ E)
    (hw : W = Submodule.span ℂ {b}) (hl : l ∈ W) (hk : k ∈ W)
    (y x : E) (hy : l y = 1) (hx : l x = 0) : k x = 0 := by
  rw [hw, Submodule.mem_span_singleton] at hl hk
  obtain ⟨a, rfl⟩ := hl
  obtain ⟨c, rfl⟩ := hk
  change a * b y = 1 at hy
  change a * b x = 0 at hx
  change c * b x = 0
  have ha : a ≠ 0 := fun h ↦ by simp [h] at hy
  exact mul_eq_zero_of_right _ ((mul_eq_zero.mp hx).resolve_left ha)

/-- Paper: Theorem 7.5.0.1 and Equation (7.5.0.3), pp. 374–375.
The two zero moments are preserved by the finite principal-value operator. -/
theorem strongCoprimalityPrincipalValue_mem_polar (S : Finset V) (f : P) :
    adelePrincipalValue F S f.val ∈ P := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hn
  · rw [globalThetaPrincipalValue_isotypicAverage_emptyTest (F := F)]
    exact f.property
  let E := SchwartzBruhat (Multiplicative 𝔸[F])
  let pv : E →L[ℂ] E :=
    ⟨adelePrincipalValue F S, (adelePrincipalValue_isClosedEmbedding S).continuous⟩
  let vals : E →L[ℂ] ℂ × ℂ := ⟨adelePolarValues, adelePolarValues_continuous⟩
  obtain ⟨y, hy⟩ := adelePolarValues_surjective (F := F) ((1, 1) : ℂ × ℂ)
  change vals y = (1, 1) at hy
  have hx : vals f.val = 0 := f.property
  have coord (L : ℂ × ℂ →L[ℂ] ℂ) (c : QuasiCharacter C𝔽)
      (hL : L.comp vals ∈ adelicEigendistributions c) (h1 : L (1, 1) = 1) :
      L (vals (pv f.val)) = 0 := by
    let l := L.comp vals
    have hk : l.comp pv ∈ adelicEigendistributions c := by
      intro u t
      have he := congrArg (fun q : GlobalAdelicThetaSpace F ↦ L (globalThetaPolarValues q))
        (globalThetaPrincipalValue_equivariant hn u t)
      exact he.trans (hL u (pv t))
    exact strongCoprimalityPrincipalValue_mem_polar_of_line (adelicEigendistributions c)
      (adelicNormalizedEigendistribution c) l (l.comp pv) (adelicEigendistributions_eq_span c) hL hk y f.val
      ((congrArg L hy).trans h1) ((congrArg L hx).trans (map_zero L))
  apply (mem_adelePolarSubspace _).2
  constructor
  · apply coord (ContinuousLinearMap.fst ℂ ℂ ℂ) 1 _ rfl
    intro u t
    change t (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[F]) * 0)) = 1 * t (Multiplicative.ofAdd 0)
    rw [mul_zero, one_mul]
  · apply coord (ContinuousLinearMap.snd ℂ ℂ ℂ) (ideleClassNormTwist (1 : U) 1) _ rfl
    intro u t
    change adeleSchwartzFourier (schwartzBruhatUnitTranslate u t) (Multiplicative.ofAdd 0) =
      ((1 : ℂ) * (((ideleNorm F u).val : ℝ) : ℂ) ^ (1 : ℂ)) *
        adeleSchwartzFourier t (Multiplicative.ofAdd 0)
    rw [Complex.cpow_one, one_mul]
    exact adeleSchwartzFourier_zero_unitTranslate u t

/-- Paper: Equation (7.5.0.3), p. 375.
The denominator is the image in homogeneous theta classes of principal values of
zero-moment tests. -/
def strongCoprimalityDenominator (ω : PontryaginDual C₁) (S : Finset V) :
    Submodule ℂ (StrongCoprimalityThetaSpace ω) :=
  Submodule.span ℂ (range fun f : P ↦
    (Submodule.Quotient.mk ⟨adelePrincipalValue F S f.val,
      strongCoprimalityPrincipalValue_mem_polar S f⟩ : StrongCoprimalityThetaSpace ω))

/-- Paper: Equation (7.5.0.3), p. 375.
The global orbital quotient carries the quotient topology of the pole-free theta space.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev StrongCoprimalityQuotient (ω : PontryaginDual C₁) (S : Finset V) :=
  StrongCoprimalityThetaSpace ω ⧸ strongCoprimalityDenominator ω S

private theorem mkQ_span_range_eq_zero {E M : Type*} [AddCommGroup E] [AddCommGroup M]
    [Module ℂ E] [Module ℂ M] (L : E →ₗ[ℂ] M) (x : M) :
    (Submodule.span ℂ (Set.range L)).mkQ x = 0 ↔ ∃ y, x = L y := by
  have hle : Submodule.span ℂ (Set.range L) ≤ LinearMap.range L :=
    Submodule.span_le.mpr Set.Subset.rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact Submodule.subset_span ⟨y, hy.symm⟩

/-- Paper: Equation (7.5.0.3), p. 375.
A theta class represents zero in the quotient exactly when a principal-value test
represents that same theta class. -/
theorem strongCoprimalityQuotient_mk_eq_zero (ω : PontryaginDual C₁) (S : Finset V)
    (f : P) :
    (strongCoprimalityDenominator ω S).mkQ ((K(ω)).mkQ f) = 0 ↔
      ∃ g : P, (K(ω)).mkQ f = (K(ω)).mkQ
        ⟨adelePrincipalValue F S g.val, strongCoprimalityPrincipalValue_mem_polar S g⟩ :=
  by
    let A : P →ₗ[ℂ] P := ((adelePrincipalValue F S).domRestrict P).codRestrict P
      (strongCoprimalityPrincipalValue_mem_polar S)
    exact mkQ_span_range_eq_zero (((K(ω)).mkQ).comp A) ((K(ω)).mkQ f)

/-- Paper: Theorem 7.5.0.1, p. 374.
The class norm used for the comparison is the surjective modulation of §D.2. -/
theorem strongCoprimalityNorm_isModulation_surjective :
    IsModulation (m𝔽 : C𝔽 →ₜ* ℝ≥0ˣ) ∧ Surjective (m𝔽 : C𝔽 →ₜ* ℝ≥0ˣ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  exact ⟨⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩, hsurj⟩

/-- Paper: Theorem 7.5.0.1, pp. 374–375.
The comparison difference composes the operators that subtract translation by
each selected inverse uniformizer. -/
def strongCoprimalityDifference (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (f : C𝔽 → ℂ) : C𝔽 → ℂ :=
  S.toList.foldr (fun v h g ↦
    h g - h ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹ * g)) f

/-- Paper: Theorem 7.5.0.1, pp. 374–375.
A single-place difference subtracts the inverse uniformizer translate pointwise. -/
theorem strongCoprimalityDifference_singleton_apply
    (π : (v : V) → (v.adicCompletion F)ˣ) (v : V) (f : C𝔽 → ℂ) (g : C𝔽) :
    strongCoprimalityDifference {v} π f g =
      f g - f ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹ * g) := by
  simp [strongCoprimalityDifference]

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
/-- Paper: Equation (7.5.0.1), p. 374.
The comparison uses the range of the full-interval difference product of §4.6. -/
def fullDecayDifferenceRange (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ω : PontryaginDual m.toMonoidHom.ker) (gs : List G) :
    Submodule ℂ ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω) :=
  (modulatedIsotypicDifferenceProduct m hm hms ω univ ordConnected_univ
    (mem_univ (0 : ℝ)) gs).toLinearMap.range

/-- Paper: Equation (7.5.0.1), p. 374.
The span of pointwise iterated differences is the range of the continuous product
on the full decay isotype. -/
theorem fullDecayDifferenceRange_eq_span (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (hms : Surjective m) (ω : PontryaginDual m.toMonoidHom.ker) (gs : List G) :
    let E := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω)
    fullDecayDifferenceRange m hm hms ω gs = Submodule.span ℂ
      {h : E | ∃ f : E, h.val.val =
        gs.foldr (fun a (u : G → ℂ) x ↦ u x - u (a * x)) f.val.val} := by
  let E := ↥(modulatedDecayIsotype m univ (mem_univ (0 : ℝ)) ω)
  let D (l : List G) := modulatedIsotypicDifferenceProduct m hm hms ω univ
    ordConnected_univ (mem_univ (0 : ℝ)) l
  have eval (f : E) (l : List G) (x : G) : ((D l) f).val.val x =
      l.foldr (fun a (u : G → ℂ) y ↦ u y - u (a * y)) f.val.val x := by
    induction l generalizing x with
    | nil => rfl
    | cons a l ih =>
      exact (modulatedCyclicDifference_apply m a hm hms univ ordConnected_univ univ_nonempty
        ((D l) f).val x).trans (congrArg₂ (· - ·) (ih x) (ih (a * x)))
  apply le_antisymm
  · rintro h ⟨f, rfl⟩
    exact Submodule.subset_span ⟨f, funext (eval f gs)⟩
  · refine Submodule.span_le.mpr ?_
    rintro h ⟨f, hf⟩
    exact ⟨f, Subtype.ext (Subtype.ext ((funext (eval f gs)).trans hf.symm))⟩
end

/-- Paper: Equation (7.5.0.1), p. 374.
The comparison denominator is the submodule generated by differences of
exponentially decaying functions of the same isotype.
Specializing fullDecayDifferenceRange_eq_span to the class norm and the list
of inverse uniformizer classes recovers this formula by List.foldr_map. -/
def strongCoprimalityDifferenceRange (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) : Submodule ℂ (StrongCoprimalityDecaySpace ω) :=
  Submodule.span ℂ {h | ∃ f : StrongCoprimalityDecaySpace ω,
    h.val.val = strongCoprimalityDifference S π f.val.val}

private theorem strongCoprimalityDifference_add (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (f g : C𝔽 → ℂ) :
    strongCoprimalityDifference S π (f + g) =
      strongCoprimalityDifference S π f + strongCoprimalityDifference S π g := by
  unfold strongCoprimalityDifference
  induction S.toList with
  | nil => rfl
  | cons v l ih =>
    simp only [List.foldr_cons, ih]
    funext x
    simp only [Pi.add_apply]
    ring

private theorem strongCoprimalityDifference_smul (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (c : ℂ) (f : C𝔽 → ℂ) :
    strongCoprimalityDifference S π (c • f) = c • strongCoprimalityDifference S π f := by
  unfold strongCoprimalityDifference
  induction S.toList with
  | nil => rfl
  | cons v l ih =>
    simp only [List.foldr_cons, ih]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private theorem strongCoprimalityDifference_zero (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) :
    strongCoprimalityDifference S π (0 : C𝔽 → ℂ) = 0 := by
  simpa using strongCoprimalityDifference_smul S π 0 0

private theorem span_image_eq_of_linear {M X : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup X] [Module ℂ X] (φ : M → X) (D : X → X)
    (hφa : ∀ a b, φ (a + b) = φ a + φ b) (hφs : ∀ (c : ℂ) a, φ (c • a) = c • φ a)
    (hφ0 : φ 0 = 0)
    (hDa : ∀ a b, D (a + b) = D a + D b) (hDs : ∀ (c : ℂ) a, D (c • a) = c • D a)
    (hD0 : D 0 = 0) (h : M) :
    h ∈ Submodule.span ℂ {h | ∃ f : M, φ h = D (φ f)} ↔ ∃ f : M, φ h = D (φ f) := by
  let N : Submodule ℂ M :=
    { carrier := {h | ∃ f : M, φ h = D (φ f)}
      add_mem' := by
        rintro a b ⟨f, hf⟩ ⟨g, hg⟩
        exact ⟨f + g, by rw [hφa, hf, hg, hφa, hDa]⟩
      zero_mem' := ⟨0, by rw [hφ0, hD0]⟩
      smul_mem' := by
        rintro c a ⟨f, hf⟩
        exact ⟨c • f, by rw [hφs, hf, hφs, hDs]⟩ }
  constructor
  · intro hm
    exact (Submodule.span_le.mpr (fun x hx ↦ hx) : _ ≤ N) hm
  · intro hm
    exact Submodule.subset_span hm

/-- Paper: Equation (7.5.0.1), p. 374.
Each element of the comparison denominator is a single iterated difference
of an exponentially decaying function in the given isotype. -/
theorem mem_strongCoprimalityDifferenceRange (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ) (h : StrongCoprimalityDecaySpace ω) :
    h ∈ strongCoprimalityDifferenceRange ω S π ↔
      ∃ f : StrongCoprimalityDecaySpace ω,
        h.val.val = strongCoprimalityDifference S π f.val.val := by
  exact span_image_eq_of_linear (fun x : StrongCoprimalityDecaySpace ω ↦ x.val.val)
    (strongCoprimalityDifference S π) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) rfl
    (strongCoprimalityDifference_add S π) (strongCoprimalityDifference_smul S π)
    (strongCoprimalityDifference_zero S π) h

open Classical in
/-- Paper: Theorem 7.5.0.1, p. 374.
The map induced by homogeneous theta is a topological linear isomorphism from the Weil
principal-value quotient to the exponential-decay quotient.
Deviation: The comparison product uses the unramified places of the selected set.
At a ramified place Weil principal value acts as the identity on this isotype. -/
theorem strongCoprimality (χ : U) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (_hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    let ω := ω(χ)
    let j := (exists_strongCoprimalityThetaEmbedding ω).choose
    let D := strongCoprimalityDenominator ω S
    let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    let E := strongCoprimalityDifferenceRange ω T π
    ∃ e : (StrongCoprimalityThetaSpace ω ⧸ D) ≃L[ℂ] (StrongCoprimalityDecaySpace ω ⧸ E),
      ∀ x : StrongCoprimalityThetaSpace ω,
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x) := by sorry

private theorem strongCoprimalityDenominator_insert_le_conj_left {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (T₁ Q R : G →ₗ[ℂ] G) (h : T₁ = Q.comp R) :
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) T₁).comp
      e.symm.toLinearMap) =
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) Q).comp
      e.symm.toLinearMap)).comp
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) R).comp
      e.symm.toLinearMap)) := by
  subst h
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_comp (R := ℂ)
    (LinearMap.id : E →ₗ[ℂ] E) Q (LinearMap.id : E →ₗ[ℂ] E) R) (e.symm x)
  rw [LinearMap.id_comp] at h
  exact congrArg e (h.trans (congrArg (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) Q)
    (e.symm_apply_apply _).symm))

open scoped TensorProduct in
private theorem strongCoprimalityDenominator_insert_le_piMap {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] {p₁ p₂ p₃ : ι → Prop}
    {d₁ : ∀ i, Decidable (p₁ i)} {d₂ : ∀ i, Decidable (p₂ i)} {d₃ : ∀ i, Decidable (p₃ i)}
    {T : ∀ i, M i →ₗ[ℂ] M i} (h : ∀ i, (p₁ i ↔ p₂ i ∨ p₃ i) ∧ ¬ (p₂ i ∧ p₃ i)) :
    (PiTensorProduct.map (fun i ↦ if p₁ i then T i else LinearMap.id) :
        FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ] FinestLocallyConvex (⨂[ℂ] i, M i)) =
      (PiTensorProduct.map (fun i ↦ if p₂ i then T i else LinearMap.id) :
        FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ] FinestLocallyConvex (⨂[ℂ] i, M i)).comp
      (PiTensorProduct.map (fun i ↦ if p₃ i then T i else LinearMap.id) :
        FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ] FinestLocallyConvex (⨂[ℂ] i, M i)) := by
  have hf : (fun i ↦ if p₁ i then T i else LinearMap.id) = fun i ↦
      (if p₂ i then T i else LinearMap.id) ∘ₗ (if p₃ i then T i else LinearMap.id) := by
    funext i
    obtain ⟨h1, h23⟩ := h i
    by_cases a : p₂ i <;> by_cases b : p₃ i
    · exact absurd ⟨a, b⟩ h23
    · rw [ite_eq_left (h1.mpr (Or.inl a)), ite_eq_left a, ite_eq_right b, LinearMap.comp_id]
    · rw [ite_eq_left (h1.mpr (Or.inr b)), ite_eq_right a, ite_eq_left b, LinearMap.id_comp]
    · rw [ite_eq_right (fun c ↦ (h1.mp c).elim a b), ite_eq_right a, ite_eq_right b, LinearMap.id_comp]
  exact (congrArg PiTensorProduct.map hf).trans (PiTensorProduct.map_comp _ _)

open Classical in
private theorem strongCoprimalityDenominator_insert_le_sPV {S' S₁ S₂ S₃ : Finset V}
    (h₁ : S₁ ⊆ S') (h₂ : S₂ ⊆ S') (h₃ : S₃ ⊆ S')
    (h : ∀ w ∈ S', (w ∈ S₁ ↔ w ∈ S₂ ∨ w ∈ S₃) ∧ ¬ (w ∈ S₂ ∧ w ∈ S₃)) :
    sAdelePrincipalValue F h₁ = (sAdelePrincipalValue F h₂).comp (sAdelePrincipalValue F h₃) := by
  unfold sAdelePrincipalValue
  exact strongCoprimalityDenominator_insert_le_conj_left _ _ _ _ (strongCoprimalityDenominator_insert_le_piMap fun w ↦ h w.val w.2)

open scoped TensorProduct in
private theorem strongCoprimalityDenominator_insert_le_conj_right {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (T₁ Q R : E →ₗ[ℂ] E) (L₁ L₂ L₃ : N →ₗ[ℂ] N)
    (h : T₁ = Q.comp R) (hA : ∀ f g, L₁ (e (f ⊗ₜ[ℂ] g)) = e (T₁ f ⊗ₜ[ℂ] g))
    (hB : ∀ f g, L₂ (e (f ⊗ₜ[ℂ] g)) = e (Q f ⊗ₜ[ℂ] g))
    (hC : ∀ f g, L₃ (e (f ⊗ₜ[ℂ] g)) = e (R f ⊗ₜ[ℂ] g)) :
    L₁ = L₂.comp L₃ := by
  have key : L₁.comp (e.toLinearMap : E ⊗[ℂ] G →ₗ[ℂ] N) =
      (L₂.comp L₃).comp (e.toLinearMap : E ⊗[ℂ] G →ₗ[ℂ] N) := by
    refine TensorProduct.ext' fun f g ↦ ?_
    change L₁ (e (f ⊗ₜ[ℂ] g)) = L₂ (L₃ (e (f ⊗ₜ[ℂ] g)))
    rw [hA, hC, hB, h]
    rfl
  refine LinearMap.ext fun x ↦ ?_
  have hx := LinearMap.congr_fun key (e.symm x)
  change L₁ (e (e.symm x)) = L₂ (L₃ (e (e.symm x))) at hx
  rwa [e.apply_symm_apply] at hx

private theorem strongCoprimalityDenominator_insert_le_PV {S' S₁ S₂ S₃ : Finset V}
    (h₁ : S₁ ⊆ S') (h₂ : S₂ ⊆ S') (h₃ : S₃ ⊆ S')
    (hs : sAdelePrincipalValue F h₁ = (sAdelePrincipalValue F h₂).comp (sAdelePrincipalValue F h₃)) :
    adelePrincipalValue F S₁ = (adelePrincipalValue F S₂).comp (adelePrincipalValue F S₃) :=
  strongCoprimalityDenominator_insert_le_conj_right (sAdeleTailSchwartz_inductiveTensor_equiv F S').choose _ _ _ _ _ _ hs
    (fun f g ↦ adelePrincipalValue_tmul h₁ f g) (fun f g ↦ adelePrincipalValue_tmul h₂ f g)
    (fun f g ↦ adelePrincipalValue_tmul h₃ f g)

private theorem strongCoprimalityDenominator_insert_le_span_le {M X Y : Type*} [AddCommGroup M] [Module ℂ M]
    (a : X → M) (b : Y → M) (h : ∀ x, ∃ y, a x = b y) :
    Submodule.span ℂ (range a) ≤ Submodule.span ℂ (range b) :=
  Submodule.span_mono (by rintro _ ⟨x, rfl⟩; obtain ⟨y, hy⟩ := h x; exact ⟨y, hy.symm⟩)

private theorem strongCoprimalityDenominator_insert_le_final {E M : Type*} [AddCommGroup E]
    [Module ℂ E] [AddCommGroup M] [Module ℂ M] (W : Submodule ℂ E) (π : W → M)
    (L₁ L₂ L₃ : E →ₗ[ℂ] E) (hABC : L₁ = L₂.comp L₃)
    (hA : ∀ f : W, L₁ f.val ∈ W) (hB : ∀ f : W, L₂ f.val ∈ W) (hC : ∀ f : W, L₃ f.val ∈ W) :
    Submodule.span ℂ (range fun f : W ↦ π ⟨L₁ f.val, hA f⟩) ≤
      Submodule.span ℂ (range fun f : W ↦ π ⟨L₂ f.val, hB f⟩) :=
  strongCoprimalityDenominator_insert_le_span_le _ _ fun f ↦
    ⟨⟨L₃ f.val, hC f⟩, congrArg π (Subtype.ext (LinearMap.congr_fun hABC f.val))⟩

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
Adding one place shrinks the image of principal value, so its image is a submodule
of the image for the original set of places. -/
theorem strongCoprimalityDenominator_insert_le (ω : PontryaginDual C₁) (S : Finset V) (v : V) :
    strongCoprimalityDenominator ω (insert v S) ≤ strongCoprimalityDenominator ω S := by
  have hPV : ∃ C : _ →ₗ[ℂ] _,
      adelePrincipalValue F (insert v S) = (adelePrincipalValue F S).comp C ∧
      ∀ f : P, C f.val ∈ P := by
    by_cases hv : v ∈ S
    · exact ⟨LinearMap.id, (congrArg (adelePrincipalValue F) (Finset.insert_eq_of_mem hv)).trans
        (LinearMap.comp_id _).symm, fun f ↦ f.2⟩
    · have hdis : ∀ w ∈ insert v S, (w ∈ insert v S ↔ w ∈ S ∨ w ∈ ({v} : Finset V)) ∧
          ¬ (w ∈ S ∧ w ∈ ({v} : Finset V)) := fun w _ ↦
        ⟨by rw [Finset.mem_insert, Finset.mem_singleton, or_comm], fun ⟨a, b⟩ ↦
          hv (Finset.mem_singleton.mp b ▸ a)⟩
      have h₁ : insert v S ⊆ insert v S := Finset.Subset.refl _
      have h₂ : S ⊆ insert v S := Finset.subset_insert v S
      have h₃ : ({v} : Finset V) ⊆ insert v S :=
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v S)
      have hs := strongCoprimalityDenominator_insert_le_sPV (F := F) h₁ h₂ h₃ hdis
      have hPV := strongCoprimalityDenominator_insert_le_PV h₁ h₂ h₃ hs
      exact ⟨adelePrincipalValue F {v}, hPV, strongCoprimalityPrincipalValue_mem_polar {v}⟩
  obtain ⟨C, hC, hCP⟩ := hPV
  unfold strongCoprimalityDenominator
  have key := strongCoprimalityDenominator_insert_le_final (P)
    (Submodule.Quotient.mk : _ → StrongCoprimalityThetaSpace ω) _ _ C hC
    (strongCoprimalityPrincipalValue_mem_polar (insert v S))
    (strongCoprimalityPrincipalValue_mem_polar S) hCP
  with_reducible_and_instances exact key

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
The layer for one added place is the quotient of the current principal-value image
by the image after applying principal value at that place as well.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev StrongCoprimalityLayer (ω : PontryaginDual C₁) (S : Finset V) (v : V) :=
  let D := strongCoprimalityDenominator ω S
  D ⧸ (strongCoprimalityDenominator ω (insert v S)).comap D.subtype

open Classical in
/-- Paper: Equation (7.5.0.4), p. 375.
A vector in the current principal-value image vanishes in the layer exactly when it
belongs to the image after adding the new place. -/
theorem strongCoprimalityLayer_mk_eq_zero (ω : PontryaginDual C₁) (S : Finset V) (v : V)
    (x : strongCoprimalityDenominator ω S) :
    (Submodule.Quotient.mk x : StrongCoprimalityLayer ω S v) = 0 ↔
      x.val ∈ strongCoprimalityDenominator ω (insert v S) :=
  Submodule.Quotient.mk_eq_zero
    ((strongCoprimalityDenominator ω (insert v S)).comap
      (strongCoprimalityDenominator ω S).subtype)

-- TODO(paper-gap): The references to (8.1.0.4), (8.1.0.5), (8.1.0.7), and
-- (8.1.0.8) in the proof point to local formulas (7.5.0.5), (7.5.0.6),
-- (7.5.0.7), and (7.5.0.11), respectively.

-- TODO(paper-gap): In the injectivity argument on pp. 375–376 the pulled-back
-- functionals must separate the source quotient. A biorthogonal family alone
-- gives no such separation. In theta space H with comparison map j the required
-- identity is j⁻¹(range Δ) = PV(H), for the product on the unramified places.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Equation (7.5.0.8), p. 377.
The reflected Fourier jet is the derivative evaluation of the global Mellin transform at
the original spectral point, with the sign from reflection in odd orders.
Deviation: The functional is on the zero-moment quotient from (7.5.0.1), where the
global Mellin transform is entire. -/
def strongCoprimalityFourierJet (s : ℂ) (k : ℕ) : StrongDual ℂ (StrongCoprimalityThetaSpace (ω(χ))) :=
  (-1 : ℂ) ^ k • ((entireJet s k).comp
    (schwartzBergmanEntireInclusion.comp (exists_globalPolarThetaMellin χ τ hτ).choose))

/-- Paper: Equation (7.5.0.8), p. 377.
On a zero-moment representative, the reflected jet evaluates the k-th complex derivative
of the Fourier-transformed global zeta function at 1 − s. This zeta function is entire.
Deviation: Entireness uses the two zero moments, which the Fourier transform exchanges. -/
theorem strongCoprimalityFourierJet_mk (s : ℂ) (k : ℕ) (f : P) :
    let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f.val)
      (ideleClassNormTwist χ⁻¹ z)
    Differentiable ℂ Z ∧
      strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ f) = iteratedDeriv k Z (1 - s) := by
  let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f.val) (ideleClassNormTwist χ⁻¹ z)
  let G := fun z ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ z)
  have href : Z = fun z ↦ G (1 - z) := by
    funext z
    have hz := globalIdelicZFunction_functionalEquation f.val (ideleClassNormTwist χ (1 - z))
    rw [dualQuasiCharacter_ideleClassNormTwist, sub_sub_cancel] at hz
    exact hz.symm
  have hG : Differentiable ℂ G := globalIdelicZFunction_entire_of_vanishing f.val f.property χ
  change Differentiable ℂ Z ∧ _ = iteratedDeriv k Z (1 - s)
  constructor
  · rw [href]
    exact hG.comp ((differentiable_const (c := (1 : ℂ))).sub differentiable_id)
  · let M := (exists_globalPolarThetaMellin χ τ hτ).choose
    have he : ((schwartzBergmanEntireInclusion (M ((K(ω(χ))).mkQ f))).val : ℂ → ℂ) = G := by
      funext z
      rw [schwartzBergmanEntireInclusion_apply]
      exact ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f z).2
    change (-1 : ℂ) ^ k • iteratedDeriv k
      ((schwartzBergmanEntireInclusion (M ((K(ω(χ))).mkQ f))).val : ℂ → ℂ) s = _
    rw [he, href, iteratedDeriv_comp_const_sub]
    simp only [sub_sub_cancel]

/-- Paper: Equation (7.5.0.8), p. 377.
At each regular center on the imaginary axis the reflected jet is defined on
the full homogeneous theta space and restricts to the jet on polar tests.
Deviation: The trivial quasi-character is the exceptional center on this axis. -/
theorem exists_strongCoprimalityFourierJet_full (s : ℂ) (_hs : s.re = 0)
    (_hc : ideleClassNormTwist χ s ≠ 1) (k : ℕ) :
    let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω(χ)))).mkQ
    ∃ d : StrongDual ℂ (GlobalHomogeneousThetaSpace F (ω(χ))),
      (∀ f : SchwartzBruhat (Multiplicative (𝔸[F])),
        let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
          (ideleClassNormTwist χ⁻¹ z)
        AnalyticAt ℂ Z (1 - s) ∧ d (q f) = iteratedDeriv k Z (1 - s)) ∧
      ∀ f : P, d (q f.val) =
        strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ f) := by sorry

-- In the proof on pp. 376–377 one can enlarge S to contain the primes of
-- the different and all places above each rational prime occurring in S
-- (saturation in §7.3). Then the outside indicators are self-dual and
-- the outside unit masses are one. The local-to-global quotient in (7.5.0.16)
-- itself only needs the hypotheses in its statement below.

/-- Paper: Equation (7.5.0.13), p. 378.
Multiplication by a factor holomorphic at the reflected point acts on unnormalized
derivatives by an upper-triangular binomial matrix. For the regular blocks the
factor is the outside Euler product of the conjugate character when S contains
all primes of the different. Both sets of raw derivatives here use the reflected variable.
Deviation: A block of size N has indices 0 through N − 1, as in (7.5.0.11). -/
def strongCoprimalityJetMatrix (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ)
    (_hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let L := heckeEulerProductOutside S χ⁻¹ hS
  fun m k ↦
    if m ≤ k then (k.val.choose m.val : ℂ) * iteratedDeriv (k.val - m.val) L (1 - s) else 0

/-- Paper: Equation (7.5.0.13), p. 378.
The diagonal entries of the derivative matrix are the value of the multiplier at the
reflected point, so the determinant is that value raised to the block size. -/
theorem strongCoprimalityJetMatrix_det (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ)
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    (strongCoprimalityJetMatrix χ S hS s hL N).det =
      heckeEulerProductOutside S χ⁻¹ hS (1 - s) ^ N := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [strongCoprimalityJetMatrix, Finset.prod_const]
  · intro i j hij
    simp [strongCoprimalityJetMatrix, not_le.mpr (show j < i from hij)]

/-- The reciprocal finite Euler polynomial is entire and nonzero to the right
of the imaginary axis. -/
private theorem strongCoprimalityJetMatrix_det_ne_zero_euler
    {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (∀ z : ℂ, AnalyticAt ℂ (reciprocalPartialHeckeEulerProduct χ S) z) ∧
      ∀ z : ℂ, 0 < z.re → reciprocalPartialHeckeEulerProduct χ S z ≠ 0 := by
  classical
  have hfactor (v : HeightOneSpectrum (𝓞 F)) (z : ℂ) :
      AnalyticAt ℂ (fun w ↦ (finiteHeckeEulerFactor χ v w)⁻¹) z ∧
        (0 < z.re → (finiteHeckeEulerFactor χ v z)⁻¹ ≠ 0) := by
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      have hq0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
        exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
      simp only [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
      constructor
      · have hc : Differentiable ℂ (fun w : ℂ ↦ (v.asIdeal.absNorm : ℂ) ^ (-w)) :=
          differentiable_id.neg.const_cpow (Or.inl hq0)
        exact ((hc.const_mul ((ideleClassNormTwist χ 0).localValue v)).const_sub 1).analyticAt z
      · intro hz hzero
        have hlt : ‖(ideleClassNormTwist χ 0).localValue v *
            (v.asIdeal.absNorm : ℂ) ^ (-z)‖ < 1 := by
          rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
            ← Complex.ofReal_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
          exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
        have he := (sub_eq_zero.mp hzero).symm
        exact hlt.ne (by rw [he, norm_one])
    · simp only [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
      exact ⟨analyticAt_const, fun _ ↦ one_ne_zero⟩
  constructor
  · intro z
    exact S.analyticAt_fun_prod (fun v _ ↦ (hfactor v z).1)
  · intro z hz
    exact Finset.prod_ne_zero_iff.mpr (fun v _ ↦ (hfactor v z).2 hz)

/-- The boundary line of absolute convergence lies in the existing zero-free region. -/
private theorem strongCoprimalityJetMatrix_det_ne_zero_order
    {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (L : ℂ → ℂ)
    (hNF : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z)
    (z : ℂ) (hz : z.re = 1) : meromorphicOrderAt L z ≤ 0 := by
  obtain ⟨A, hA, hfield⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨scale, hB, hbound⟩ := hfield F χ
  apply hbound L hNF hSeries z
  have hlog : 0 ≤ Real.log (scale * (|z.im| + 3)) := by
    apply Real.log_nonneg
    have hBpos : 0 < scale := by linarith
    nlinarith [mul_nonneg hBpos.le (abs_nonneg z.im)]
  rw [hz]
  exact sub_le_self _ (div_nonneg hA.le (mul_nonneg (by positivity) hlog))

/-- Paper: Equation (7.5.0.13), p. 378.
The regular block is invertible at a spectral point on the imaginary axis.
Deviation: At the exceptional pole of a norm twist the regular-block hypothesis fails. -/
theorem strongCoprimalityJetMatrix_det_ne_zero (S : Finset V)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S) (s : ℂ) (_hs : s.re = 0)
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (N : ℕ) :
    (strongCoprimalityJetMatrix χ S hS s hL N).det ≠ 0 := by
  rw [strongCoprimalityJetMatrix_det]
  apply pow_ne_zero
  let r : ℂ := 1 - s
  have hr : r.re = 1 := by simp only [r, Complex.sub_re, Complex.one_re, _hs, sub_zero]
  obtain ⟨L, hNF, hSeries⟩ := finiteHeckeL_exists_continuation χ⁻¹
  obtain ⟨hP, hPne⟩ := strongCoprimalityJetMatrix_det_ne_zero_euler χ⁻¹ S
  have hM : MeromorphicOn
      (fun z ↦ reciprocalPartialHeckeEulerProduct χ⁻¹ S z * L z) univ :=
    fun z hz ↦ (hP z).meromorphicAt.mul (hNF hz).meromorphicAt
  have horder : meromorphicOrderAt (heckeEulerProductOutside S χ⁻¹ hS) r =
      meromorphicOrderAt L r := by
    rw [heckeEulerProductOutside_eq_finite S χ⁻¹ hS L hNF hSeries,
      meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ r)]
    exact meromorphicOrderAt_mul_of_ne_zero (hP r) (hPne r (by rw [hr]; norm_num))
  apply (hL.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mp
  apply le_antisymm _ hL.meromorphicOrderAt_nonneg
  change meromorphicOrderAt (heckeEulerProductOutside S χ⁻¹ hS) r ≤ 0
  rw [horder]
  exact strongCoprimalityJetMatrix_det_ne_zero_order χ⁻¹ L hNF hSeries r hr

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)

/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.15), p. 378.
At the places above one rational prime the denominator agrees with the
primary denominator of §7.4. -/
theorem strongCoprimalityDenominator_primary (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    strongCoprimalityDenominator (ω(χ)) T = finiteNuclearityDenominator χ p := by
  unfold strongCoprimalityDenominator finiteNuclearityDenominator
  with_reducible rfl

/-- A norm-one character extends by projecting along a section of the class norm. -/
private theorem strongCoprimalityPrimaryQuotient_lift (ω : PontryaginDual C₁) :
    ∃ χ : U, ω(χ) = ω := by
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  obtain ⟨σ, hσ⟩ := exists_surjectiveModulation_section m𝔽 hmod.1 hmod.2
  have hk (g : C𝔽) : g / σ (m𝔽 g) ∈ (ideleClassNorm F).ker := by
    change (ideleClassNorm F) (g / σ (m𝔽 g)) = 1
    rw [map_div, show ideleClassNorm F (σ (m𝔽 g)) = m𝔽 g from hσ (m𝔽 g)]
    change (ideleClassNorm F g) / (ideleClassNorm F g) = 1
    exact div_self' _
  let q : C𝔽 →ₜ* C₁ :=
    { toFun := fun g ↦ ⟨g / σ (m𝔽 g), hk g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by simp [mul_div_mul_comm])
      continuous_toFun := (continuous_id.div' (σ.continuous.comp (m𝔽).continuous)).subtype_mk hk }
  refine ⟨ω.comp q, ?_⟩
  ext1 u
  change ω (q u) = ω u
  congr 1
  apply Subtype.ext
  change u.val / σ ((ideleClassNorm F) u.val) = u.val
  rw [u.property, map_one, div_one]

/-- The comparison denominator is an expanding difference-product range, whose quotient
is separable, nuclear, and Fréchet. -/
private theorem strongCoprimalityPrimaryQuotient_decay (ω : PontryaginDual C₁) (S : Finset V)
    (π : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) :
    let X := StrongCoprimalityDecaySpace ω ⧸ strongCoprimalityDifferenceRange ω S π
    TopologicalSpace.SeparableSpace X ∧ IsNuclearTVS X ∧ IsFrechetTVS X := by
  classical
  have hmod := strongCoprimalityNorm_isModulation_surjective (F := F)
  let a := fun v : V ↦ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹
  let gs := S.toList.map a
  have hgs : ∀ g ∈ gs, 1 < (m𝔽 g).val := by
    rintro g hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    have hu := hπ v (Finset.mem_toList.mp hv)
    change (1 : ℝ≥0) < ((ideleClassNorm F ((IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (π v))⁻¹)).val)
    rw [map_inv, ideleClassNorm_ofAdicCompletion]
    rw [Units.coe_map_inv]
    change (1 : ℝ≥0) < ‖((π v)⁻¹).val‖₊
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_one, coe_nnNorm, Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_uniformizer_adicCompletion v _ hu, inv_inv]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have heq : strongCoprimalityDifferenceRange ω S π =
      fullDecayDifferenceRange m𝔽 hmod.1 hmod.2 ω gs := by
    rw [fullDecayDifferenceRange_eq_span]
    unfold strongCoprimalityDifferenceRange
    congr 1
    ext h
    simp only [gs, List.foldr_map, a, strongCoprimalityDifference]
  rw [heq]
  exact modulatedIsotypicDifferenceProduct_quotient m𝔽 hmod.1 hmod.2 ω gs hgs

/-- The strong-coprimality equivalence transfers the nuclear Fréchet structure from its
difference quotient. -/
private theorem strongCoprimalityPrimaryQuotient_character (χ : U) (S : Finset V) :
    IsFrechetTVS (StrongCoprimalityQuotient ω(χ) S) ∧
      IsNuclearTVS (StrongCoprimalityQuotient ω(χ) S) := by
  classical
  have h (v : V) := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v : V) → (v.adicCompletion F)ˣ := fun v ↦ Units.mk0 (h v).choose (h v).choose_spec.ne_zero
  have hπ (v : V) : Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val :=
    (h v).choose_spec
  let T := S.filter (fun v ↦ (ideleClassNormTwist χ 0).IsUnramifiedAt v)
  have hp := strongCoprimalityPrimaryQuotient_decay ω(χ) T π (fun v _ ↦ hπ v)
  let e := (strongCoprimality χ S π (fun v _ ↦ hπ v)).choose
  have ht := separable_nuclear_frechet_of_equiv e.symm hp
  exact ⟨ht.2.2, ht.2.1⟩

/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.15), p. 378.
The primary principal-value quotient is a Hausdorff nuclear Fréchet space. -/
theorem strongCoprimalityPrimaryQuotient_nuclearFrechet (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    IsFrechetTVS (StrongCoprimalityQuotient ω T) ∧ IsNuclearTVS (StrongCoprimalityQuotient ω T) := by
  let h := strongCoprimalityPrimaryQuotient_lift ω
  let χ := h.choose
  have hχ : ω(χ) = ω := h.choose_spec
  exact (congrArg (fun η ↦ IsFrechetTVS (StrongCoprimalityQuotient η
    (finite_nuclearityPlacesAbove (F := F) p).toFinset) ∧
      IsNuclearTVS (StrongCoprimalityQuotient η (finite_nuclearityPlacesAbove (F := F) p).toFinset))
    hχ).mp (strongCoprimalityPrimaryQuotient_character χ _)

section SLocal

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Pₛ" => sAdelePolarSubspace F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "Kₛ(" η ")" => LinearMap.ker ((sLocalHomogeneousAdelicThetaLinearMap F S η).domRestrict Pₛ)

local notation "twistₛ" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "insertPolar(" f ")" => (⟨sAdeleSchwartzToGlobal F S (f : Pₛ).val,
  sAdeleSchwartzToGlobal_mem_polarSubspace f⟩ : P)

section

private theorem strongCoprimalityFourierJet_toGlobal_reflected_product_jets (f L : ℂ → ℂ) (r : ℂ) (k : ℕ)
    (hf : AnalyticAt ℂ f r) (hL : AnalyticAt ℂ L r) :
    iteratedDeriv k (fun z ↦ f z * L z) r =
      ∑ i : Fin (k + 1), ((-1 : ℂ) ^ i.val * iteratedDeriv i.val (fun w ↦ f (r - w)) 0) *
        ((k.choose i.val : ℂ) * iteratedDeriv (k - i.val) L r) := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hL.contDiffAt, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_comp_const_sub]
  simp only [sub_zero, smul_eq_mul]
  have hs : (-1 : ℂ) ^ i.val * (-1) ^ i.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (k.choose i.val : ℂ) * iteratedDeriv i.val f r * iteratedDeriv (k - i.val) L r =
        (((-1 : ℂ) ^ i.val * (-1) ^ i.val) * iteratedDeriv i.val f r) *
          ((k.choose i.val : ℂ) * iteratedDeriv (k - i.val) L r) := by rw [hs]; ring
    _ = _ := by ring

private theorem strongCoprimalityFourierJet_toGlobal_jet_twist_add
    (G : Type*) [CommGroup G] [TopologicalSpace G] (m : G →* ℝ≥0ˣ)
    (hm : Continuous m) (c : QuasiCharacter G) (a z : ℂ) :
    quasiCharacterNormTwist m hm (quasiCharacterNormTwist m hm c a) z =
      quasiCharacterNormTwist m hm c (z + a) := by
  ext g
  let N : ℂ := (((m g : ℝ≥0) : ℝ) : ℂ)
  change c g * N ^ a * N ^ z = c g * N ^ (z + a)
  rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (m g).ne_zero)), mul_assoc]

private theorem strongCoprimalityFourierJet_toGlobal_jet_rightHalf_bound
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (z : ℂ) (hz : 1 < z.re) :
    0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ z) := by
  have h0 : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 = 1 := by
    ext g
    change 1 * _ ^ (0 : ℂ) = (1 : ℂ)
    simp
  rw [globalIdelicOrderBound, ite_eq_right]
  rintro (h | h)
  · rw [← h0] at h
    have he := congrArg (quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      ideleClassNorm_ne_one) h
    rw [quasiCharacterAbscissa_ideleClassNormTwist, quasiCharacterAbscissa_ideleClassNormTwist, Complex.zero_re] at he
    linarith
  · have he := congrArg (quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      ideleClassNorm_ne_one) h
    rw [quasiCharacterAbscissa_ideleClassNormTwist, quasiCharacterAbscissa_ideleClassNormTwist, Complex.one_re] at he
    exact hz.ne' he

private theorem strongCoprimalityFourierJet_toGlobal_theta_globalZ_congr
    (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (f g : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hq : (LinearMap.ker (adelicThetaLinearMap F)).mkQ f =
      (LinearMap.ker (adelicThetaLinearMap F)).mkQ g) :
    (fun z ↦ globalIdelicZFunction f (ideleClassNormTwist χ z)) =
      (fun z ↦ globalIdelicZFunction g (ideleClassNormTwist χ z)) := by
  have hM : globalIdelicMellin f = globalIdelicMellin g := by
    have hh := congrArg (globalThetaMellin (F := F)) hq
    change globalThetaMellin (Submodule.Quotient.mk f) = globalThetaMellin (Submodule.Quotient.mk g) at hh
    simpa only [globalThetaMellin_mk] using hh
  have hAgree (z : ℂ) (hz : 1 < z.re) :
      globalIdelicZFunction f (ideleClassNormTwist χ z) = globalIdelicZFunction g (ideleClassNormTwist χ z) := by
    let c : {c : QuasiCharacter (IdeleClassGroup (𝓞 F) F) // 0 ≤ globalIdelicOrderBound c} :=
      ⟨ideleClassNormTwist χ z, strongCoprimalityFourierJet_toGlobal_jet_rightHalf_bound F χ z hz⟩
    exact DFunLike.congr_fun (congrArg Subtype.val hM) c
  funext z
  exact globalIdelicZetaIntegral_chartContinuation_eq f
    (globalIdelicZFunction_meromorphic f χ) (globalIdelicZFunction_meromorphic g χ)
    (fun w hw ↦ globalIdelicZFunction_eq_integral f (tate_twist_mem_rightHalf χ w hw))
    (fun w hw ↦ (hAgree w hw).symm.trans (globalIdelicZFunction_eq_integral f (tate_twist_mem_rightHalf χ w hw)))
    (s := z) (s' := z) rfl

private theorem strongCoprimalityFourierJet_toGlobal_fourier_insert_theta
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    (LinearMap.ker (adelicThetaLinearMap F)).mkQ (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f)) =
      (LinearMap.ker (adelicThetaLinearMap F)).mkQ (sAdeleSchwartzToGlobal F S (sAdeleSchwartzFourier f)) := by
  have hh := sLocalThetaFourier_toGlobal hgood (Submodule.Quotient.mk f)
  have hG := (existsUnique_globalThetaFourier (F := F)).exists.choose_spec.2 (sAdeleSchwartzToGlobal F S f)
  have hS := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 f
  simp only [Submodule.mkQ_apply] at hG hS
  dsimp only at hh
  rw [sLocalThetaToGlobal_mk] at hh
  with_unfolding_all
    exact hG.symm.trans (hh.trans ((congrArg (sLocalThetaToGlobal F S) hS).trans
      (sLocalThetaToGlobal_mk (sAdeleSchwartzFourier f))))

private theorem strongCoprimalityFourierJet_toGlobal_insertion_factorization
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hS : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    (fun z ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ z))
      =ᶠ[Filter.codiscrete ℂ] fun z ↦
        sLocalIdelicZFunction f (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS⟩) z) *
          heckeEulerProductOutside S χ hS z := by
  classical
  obtain ⟨L, hNF, hSeries⟩ := finiteHeckeL_exists_continuation χ
  have hmass : (∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (((finiteLocalMultiplicativeTamagawaMeasure F v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv : ¬ v.val.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h ↦ v.property (hgood v.val h)
    simp [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, multiplicity_eq_zero_of_not_dvd hv]
  have hw := weilIdentity_unramifiedOutside_meromorphic S f χ hS L hNF (fun z hz ↦ hSeries ⟨z, hz⟩)
  have hP := (strongCoprimalityJetMatrix_det_ne_zero_euler χ S).1
  have hM : MeromorphicOn (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) univ :=
    fun z hz ↦ (hP z).meromorphicAt.mul (hNF hz).meromorphicAt
  have ho : (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) =ᶠ[Filter.codiscrete ℂ]
      heckeEulerProductOutside S χ hS := by
    rw [heckeEulerProductOutside_eq_finite S χ hS L hNF hSeries]
    exact toMeromorphicNFOn_eqOn_codiscrete hM
  filter_upwards [hw, ho] with z hz hzo
  rw [hmass, one_mul] at hz
  rw [← hzo, hz]
  dsimp only [reciprocalPartialHeckeEulerProduct]
  ring

private theorem strongCoprimalityFourierJet_toGlobal_reflected_insertion_factorization
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hS : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f)) (ideleClassNormTwist χ z))
      =ᶠ[Filter.codiscrete ℂ] fun z ↦
        sLocalIdelicZFunction (sAdeleSchwartzFourier f) (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS⟩) z) *
          heckeEulerProductOutside S χ hS z := by
  rw [strongCoprimalityFourierJet_toGlobal_theta_globalZ_congr F χ _ _ (strongCoprimalityFourierJet_toGlobal_fourier_insert_theta F S hgood f)]
  exact strongCoprimalityFourierJet_toGlobal_insertion_factorization F S χ hS hgood (sAdeleSchwartzFourier f)

private theorem strongCoprimalityFourierJet_toGlobal_local_reflection
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c b : QuasiCharacter (SIdeleQuotient F S)) (r : ℂ)
    (hc : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b r)
    (z : ℂ) :
    dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c z) =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b (r - z) := by
  have hh : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c z) =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        (dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c) (-z) := by
    ext g
    let N : ℂ := (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ)
    change N * (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous c z) g⁻¹ =
      (N * c g⁻¹) * N ^ (-z)
    rw [map_inv, map_inv]
    change N * (c g * N ^ z)⁻¹ = (N * (c g)⁻¹) * N ^ (-z)
    rw [mul_inv_rev, Complex.cpow_neg]
    ring
  rw [hh, hc, strongCoprimalityFourierJet_toGlobal_jet_twist_add]
  congr 1
  ring

private theorem strongCoprimalityFourierJet_toGlobal_local_reflected_analytic
    (F : Type*) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F)))
    (η : PontryaginDual (sIdeleQuotientNorm F S).ker)
    (j : SLocalOrbitalIndex (F := F) (S := S) T η)
    (b : QuasiCharacter (SIdeleQuotient F S)) (r : ℂ)
    (hc : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b r)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    AnalyticAt ℂ (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)) r := by
  let A (z : ℂ) := sLocalIdelicZFunction (sAdeleSchwartzFourier f)
    (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)
  have href : (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
      (dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 z))) =
      (fun z ↦ A (r - z)) := by
    funext z
    exact congrArg (sLocalIdelicZFunction (sAdeleSchwartzFourier f)) (strongCoprimalityFourierJet_toGlobal_local_reflection F S j.val.1 b r hc z)
  have h0 := sLocalOrbitalFourierZeta_analyticAt j f
  dsimp only at h0
  rw [href] at h0
  have hh := h0.comp_of_eq (f := fun z : ℂ ↦ r - z) (x := r) (by fun_prop) (sub_self r)
  simpa only [Function.comp_def, sub_sub_cancel, A] using hh

private theorem strongCoprimalityFourierJet_toGlobal_analytic_germ_of_codiscrete (f g : ℂ → ℂ) (r : ℂ)
    (hf : AnalyticAt ℂ f r) (hg : AnalyticAt ℂ g r) (he : f =ᶠ[Filter.codiscrete ℂ] g) :
    f =ᶠ[𝓝 r] g := by
  have hh := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp he) r (mem_univ r)
  exact (hf.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg.meromorphicNFAt).mp (hh.mono (fun y hy ↦ hy (mem_univ y)))

private theorem strongCoprimalityFourierJet_toGlobal_local_jet_reflection
    (F : Type*) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F)))
    (η : PontryaginDual (sIdeleQuotientNorm F S).ker)
    (j : SLocalOrbitalIndex (F := F) (S := S) T η)
    (b : QuasiCharacter (SIdeleQuotient F S)) (r : ℂ)
    (hc : dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 =
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b r)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sLocalOrbitalFourierJet j ((LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ f) =
      iteratedDeriv j.val.2 (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b (r - z))) 0 := by
  have hh := sLocalOrbitalFourierJet_mk j f
  have he : (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
      (dualQuasiCharacter (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous j.val.1 z))) =
      (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f)
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b (r - z))) := by
    funext z
    exact congrArg (sLocalIdelicZFunction (sAdeleSchwartzFourier f)) (strongCoprimalityFourierJet_toGlobal_local_reflection F S j.val.1 b r hc z)
  dsimp only at hh
  rw [he] at hh
  exact hh

end

/-- Paper: Equations (7.5.0.8)–(7.5.0.13), pp. 377–378.
On an inserted polar test, the regular change of coordinates uses the Fourier
functionals of §7.3 and their signs from differentiation before reflection.
Deviation: Taking S to contain all primes of the different makes the outside
insertion self-dual and gives every outside unit group mass one. -/
theorem strongCoprimalityFourierJet_toGlobal {T : Finset V} (_hT : T ⊆ S)
    {η : PontryaginDual J₁} (j : SLocalOrbitalIndex (F := F) (S := S) T η)
    (s : ℂ) (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S)
    (_hgood : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (_hc : dualₛ j.val.1 = twistₛ (sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩) (1 - s))
    (hL : AnalyticAt ℂ (heckeEulerProductOutside S χ⁻¹ hS) (1 - s)) (f : Pₛ) :
    let k := j.val.2
    let idx (i : Fin (k + 1)) : SLocalOrbitalIndex (F := F) (S := S) T η :=
      ⟨(j.val.1, i.val), j.property.1, lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.property.2⟩
    let x := (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ f.val
    let A := strongCoprimalityJetMatrix χ S hS s hL (k + 1)
    strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ insertPolar(f)) =
      ∑ i : Fin (k + 1), (-1 : ℂ) ^ i.val *
        sLocalOrbitalFourierJet (F := F) (S := S) (T := T) (ω := η) (idx i) x *
          A i (Fin.last k) := by
  intro k idx x mat
  let b := sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩
  let localZ (z : ℂ) := sLocalIdelicZFunction (sAdeleSchwartzFourier f.val) (twistₛ b z)
  let globalZ (z : ℂ) := globalIdelicZFunction (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f.val)) (ideleClassNormTwist χ⁻¹ z)
  let outside := heckeEulerProductOutside S χ⁻¹ hS
  have hlocal : AnalyticAt ℂ localZ (1 - s) := strongCoprimalityFourierJet_toGlobal_local_reflected_analytic F S T η j b (1 - s) _hc f.val
  have hglobal := strongCoprimalityFourierJet_mk χ τ hτ s k insertPolar(f)
  have hfactor : globalZ =ᶠ[Filter.codiscrete ℂ] (fun z ↦ localZ z * outside z) :=
    strongCoprimalityFourierJet_toGlobal_reflected_insertion_factorization F S χ⁻¹ hS _hgood f.val
  have heq := strongCoprimalityFourierJet_toGlobal_analytic_germ_of_codiscrete globalZ (fun z ↦ localZ z * outside z) (1 - s)
    (hglobal.1.analyticAt _) (by fun_prop) hfactor
  rw [hglobal.2, heq.iteratedDeriv_eq k, strongCoprimalityFourierJet_toGlobal_reflected_product_jets localZ outside (1 - s) k hlocal hL]
  apply Finset.sum_congr rfl
  intro i hi
  have hjet := strongCoprimalityFourierJet_toGlobal_local_jet_reflection F S T η (idx i) b (1 - s) _hc f.val
  rw [hjet]
  simp only [mat, strongCoprimalityJetMatrix, Fin.le_last, ite_true, Fin.val_last]
  rfl

section

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_linear_factor_deriv (g : ℂ → ℂ) (r : ℂ) (hg : AnalyticAt ℂ g r) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z ↦ (z - r) * g z) r = (n + 1 : ℂ) * iteratedDeriv n g r := by
  have hf : AnalyticAt ℂ (fun z : ℂ ↦ z - r) r := by fun_prop
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  have hlin (i : ℕ) : iteratedDeriv i (fun z : ℂ ↦ z - r) r = if i = 1 then 1 else 0 := by
    by_cases hi : i = 0
    · subst i; simp
    · have hh := congrFun (iteratedDeriv_comp_sub_const (f := id) (n := i) (s := r)) r
      simpa [id, iteratedDeriv_id, hi] using hh
  rw [Finset.sum_eq_single 1]
  · simp [hlin]
  · intro i hi hne
    rw [hlin, ite_eq_right hne, mul_zero, zero_mul]
  · intro hne
    exact (hne (by simp)).elim

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_dslope_jet (f : ℂ → ℂ) (r : ℂ) (hf : AnalyticAt ℂ f r) (hzero : f r = 0) (n : ℕ) :
    iteratedDeriv n (dslope f r) r = iteratedDeriv (n + 1) f r / (n + 1 : ℂ) := by
  have hfun : f = (fun z ↦ (z - r) * dslope f r z) := by
    funext z
    simpa only [hzero, sub_zero, smul_eq_mul] using (sub_smul_dslope f r z).symm
  have hh := strongCoprimalityFourierJet_toGlobal_at_pole_linear_factor_deriv (dslope f r) r (hf.dslope r) n
  rw [← hfun] at hh
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero n : (n + 1 : ℂ) ≠ 0)).mpr
  rw [mul_comm, ← hh]

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_cancelled_product_jets (Z H f : ℂ → ℂ) (r : ℂ) (k : ℕ)
    (hH : AnalyticAt ℂ H r) (hf : AnalyticAt ℂ f r) (hzero : f r = 0)
    (heq : Z =ᶠ[𝓝 r] fun z ↦ dslope f r z * H z) :
    iteratedDeriv k Z r = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℂ) *
      iteratedDeriv (k - m) H r * (iteratedDeriv (m + 1) f r / (m + 1 : ℂ)) := by
  rw [heq.iteratedDeriv_eq k, iteratedDeriv_fun_mul (hf.dslope r).contDiffAt hH.contDiffAt]
  apply Finset.sum_congr rfl
  intro m hm
  rw [strongCoprimalityFourierJet_toGlobal_at_pole_dslope_jet f r hf hzero m]
  ring

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_simple_pole_cancel (L f Z : ℂ → ℂ) (r : ℂ)
    (hL : MeromorphicNFOn L univ) (horder : meromorphicOrderAt L r = -1)
    (hf : AnalyticAt ℂ f r) (hZ : AnalyticAt ℂ Z r)
    (heq : Z =ᶠ[𝓝[≠] r] fun z ↦ f z * L z) :
    let H := toMeromorphicNFOn (fun z ↦ (z - r) * L z) univ
    AnalyticAt ℂ H r ∧ H r ≠ 0 ∧ f r = 0 ∧
      Z =ᶠ[𝓝 r] fun z ↦ dslope f r z * H z := by
  intro H
  have hlin (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ w - r) z := by fun_prop
  have hM : MeromorphicOn (fun z ↦ (z - r) * L z) univ :=
    fun z hz ↦ (hlin z).meromorphicAt.mul (hL.meromorphicOn z hz)
  have hHNF := meromorphicNFOn_toMeromorphicNFOn (fun z ↦ (z - r) * L z) univ (mem_univ r)
  have hHo : meromorphicOrderAt H r = 0 := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ r)]
    change meromorphicOrderAt ((fun z : ℂ ↦ z - r) * L) r = 0
    rw [meromorphicOrderAt_mul (hlin r).meromorphicAt (hL.meromorphicOn r (mem_univ r)),
      meromorphicOrderAt_id_sub_const, horder]
    norm_num
  have hHa : AnalyticAt ℂ H r := hHNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp (hHo ▸ le_rfl)
  have hHne : H r ≠ 0 := hHNF.meromorphicOrderAt_eq_zero_iff.mp hHo
  have hfzero : f r = 0 := by
    by_contra hn
    have hfo := hf.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
    have hzo := meromorphicOrderAt_congr heq
    change meromorphicOrderAt Z r = meromorphicOrderAt (f * L) r at hzo
    rw [meromorphicOrderAt_mul hf.meromorphicAt (hL.meromorphicOn r (mem_univ r)), hfo, horder] at hzo
    have hh := hZ.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hZ
    rw [hzo] at hh
    exact (show ¬ (0 : WithTop ℤ) ≤ -1 by decide) hh
  refine ⟨hHa, hHne, hfzero, ?_⟩
  let D (z : ℂ) := dslope f r z * H z
  have hEqNE : Z =ᶠ[𝓝[≠] r] D := by
    filter_upwards [heq, hM.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ r), self_mem_nhdsWithin] with z hz hHz hne
    change Z z = dslope f r z * H z
    change H z = (z - r) * L z at hHz
    rw [hz, hHz, dslope_of_ne f hne]
    simp only [slope, vsub_eq_sub, hfzero, sub_zero, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hne]
  have hD : ContinuousAt D r := (hf.dslope r).continuousAt.mul hHa.continuousAt
  have hsame : Z r = D r := tendsto_nhds_unique
    (hZ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hD.tendsto.mono_left nhdsWithin_le_nhds).congr' hEqNE.symm)
  have hn : ∀ᶠ z in 𝓝 r, z ≠ r → Z z = D z := eventually_nhdsWithin_iff.mp hEqNE
  filter_upwards [hn] with z hz
  by_cases he : z = r
  · simpa only [he] using hsame
  · exact hz he

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_jet_local_chart
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c : QuasiCharacter (SIdeleQuotient F S)) :
    ∃ (ψ : PontryaginDual (SIdeleQuotient F S)) (a : ℂ),
      quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) a = c := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  let m := sIdeleQuotientNorm F S
  have hm := isProperMap_sIdeleQuotientNorm F S
  have hne : ∃ g, m g ≠ 1 := ⟨σ t, (hσ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa m hm hne c
  let d := quasiCharacterNormTwist m hm.continuous c (-(a : ℂ))
  have hpos (g : SIdeleQuotient F S) : 0 < ((m g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hd (g : SIdeleQuotient F S) : ‖d g‖ = 1 := by
    change ‖c g * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (-(a : ℂ))‖ = 1
    rw [norm_mul, norm_quasiCharacter_eq_rpow_abscissa m hm hne,
      Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
    exact (Real.rpow_add (hpos g) a (-a)).symm.trans (by simp)
  let ψ : PontryaginDual (SIdeleQuotient F S) :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
      map_one' := Circle.ext (map_one d)
      map_mul' := fun x y ↦ Circle.ext (map_mul d x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨ψ, a, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change c g * _ ^ (-(a : ℂ)) * _ ^ (a : ℂ) = c g
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hpos g).ne'),
    neg_add_cancel, Complex.cpow_zero, mul_one]

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_pole_product_input_analytic (L A Z : ℂ → ℂ) (r : ℂ)
    (hL : MeromorphicAt L r) (horder : meromorphicOrderAt L r = -1)
    (hA : MeromorphicNFAt A r) (hZ : AnalyticAt ℂ Z r)
    (heq : Z =ᶠ[𝓝[≠] r] fun z ↦ A z * L z) : AnalyticAt ℂ A r := by
  have ho := meromorphicOrderAt_congr heq
  change meromorphicOrderAt Z r = meromorphicOrderAt (A * L) r at ho
  rw [meromorphicOrderAt_mul hA.meromorphicAt hL, horder] at ho
  apply hA.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_cases ht : meromorphicOrderAt A r = ⊤
  · simp [ht]
  · generalize hn : meromorphicOrderAt A r = n at ho ht ⊢
    lift n to ℤ using ht
    have hb := hZ.meromorphicOrderAt_nonneg
    rw [ho] at hb
    change ((0 : ℤ) : WithTop ℤ) ≤ ((n + -1 : ℤ) : WithTop ℤ) at hb
    have hb' : (0 : ℤ) ≤ n + -1 := by exact_mod_cast hb
    have hn' : (0 : ℤ) ≤ n := by omega
    exact_mod_cast hn'

private theorem strongCoprimalityFourierJet_toGlobal_at_pole_local_twist_meromorphicNF
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (b : QuasiCharacter (SIdeleQuotient F S))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    MeromorphicNFOn (fun z ↦ sLocalIdelicZFunction f
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)) univ := by
  obtain ⟨ψ, a, ha⟩ := strongCoprimalityFourierJet_toGlobal_at_pole_jet_local_chart F S b
  have he : (fun z ↦ sLocalIdelicZFunction f
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous b z)) =
      (fun z ↦ sLocalIdelicZFunction f
        (quasiCharacterNormTwist (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ) (z + a))) := by
    funext z
    rw [← ha, strongCoprimalityFourierJet_toGlobal_jet_twist_add]
  rw [he]
  intro z hz
  exact meromorphicNFAt_comp_add_const_iff_meromorphicNFAt.mpr
    (sLocalIdelicZFunction_meromorphic f ψ (mem_univ _))

end

/-- Paper: Equations (7.5.0.9)–(7.5.0.14), pp. 377–378.
At a simple pole r of the outside factor L, write H for the holomorphic extension
of (z − r)L(z). The local zeta function A of the Fourier-transformed polar test vanishes at r.
The k-th global derivative uses local derivatives of orders 1 through k + 1.
Deviation: This is the pole-cancelled Leibniz rule at the exceptional point. -/
theorem strongCoprimalityFourierJet_toGlobal_at_pole (s : ℂ)
    (hS : ideleClassNormTwist χ⁻¹ 0 ∈ unramifiedOutside F S)
    (_hgood : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (_hpole : meromorphicOrderAt (heckeEulerProductOutside S χ⁻¹ hS) (1 - s) = -1)
    (f : Pₛ) (k : ℕ) :
    let r := 1 - s
    let H := toMeromorphicNFOn (fun z ↦ (z - r) * heckeEulerProductOutside S χ⁻¹ hS z) univ
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ⁻¹ 0, hS⟩
    let A := fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f.val) (twistₛ c z)
    AnalyticAt ℂ H r ∧ H r ≠ 0 ∧ AnalyticAt ℂ A r ∧ A r = 0 ∧
      strongCoprimalityFourierJet χ τ hτ s k ((K(ω(χ))).mkQ insertPolar(f)) =
        ∑ m ∈ Finset.range (k + 1), (k.choose m : ℂ) * iteratedDeriv (k - m) H r *
          (iteratedDeriv (m + 1) A r / (m + 1 : ℂ)) := by
  intro r H c A
  let outside := heckeEulerProductOutside S χ⁻¹ hS
  let globalZ (z : ℂ) := globalIdelicZFunction (adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f.val)) (ideleClassNormTwist χ⁻¹ z)
  have hglobal := strongCoprimalityFourierJet_mk χ τ hτ s k insertPolar(f)
  have hfactor : globalZ =ᶠ[Filter.codiscrete ℂ] (fun z ↦ A z * outside z) :=
    strongCoprimalityFourierJet_toGlobal_reflected_insertion_factorization F S χ⁻¹ hS _hgood f.val
  have heq : globalZ =ᶠ[𝓝[≠] r] (fun z ↦ A z * outside z) := by
    have hh := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hfactor) r (mem_univ r)
    exact hh.mono (fun z hz ↦ hz (mem_univ z))
  have houtside : MeromorphicNFOn outside univ := by
    unfold outside heckeEulerProductOutside
    exact meromorphicNFOn_toMeromorphicNFOn _ _
  have hA := strongCoprimalityFourierJet_toGlobal_at_pole_local_twist_meromorphicNF F S c (sAdeleSchwartzFourier f.val) (mem_univ r)
  have hanalytic := strongCoprimalityFourierJet_toGlobal_at_pole_pole_product_input_analytic outside A globalZ r
    (houtside (mem_univ r)).meromorphicAt _hpole hA (hglobal.1.analyticAt r) heq
  obtain ⟨hH, hHne, hzero, hgerm⟩ := strongCoprimalityFourierJet_toGlobal_at_pole_simple_pole_cancel outside A globalZ r houtside _hpole
    hanalytic (hglobal.1.analyticAt r) heq
  refine ⟨hH, hHne, hanalytic, hzero, ?_⟩
  rw [hglobal.2]
  exact strongCoprimalityFourierJet_toGlobal_at_pole_cancelled_product_jets globalZ H A r k hH hanalytic hzero hgerm

-- TODO(paper-gap): The basis in §7.3 is for unrestricted local tests. On the
-- polar quotient its order-zero Fourier functional at the exceptional point
-- vanishes. To use that basis in (7.5.0.14), identify a basis of the polar
-- quotient with the shifted orders above (or use another surjectivity proof).

open MeasureTheory in
/-- Dilation by a local unit rescales additive Haar integration. -/
private theorem sAdelePV_integral_dilate (v : V) (a : (v.adicCompletion F)ˣ) :
    ∃ c : ℝ, ∀ p : v.adicCompletion F → ℂ,
      ∫ y, p ((a : v.adicCompletion F) * y) ∂finiteLocalAdditiveTamagawaMeasure F v =
        (c : ℂ) * ∫ y, p y ∂finiteLocalAdditiveTamagawaMeasure F v := by
  let K := v.adicCompletion F
  let : MeasurableSpace K := borel _
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let d := DomMulAct.mk a⁻¹
  refine ⟨Measure.addHaarScalarFactor (d • μ) μ, fun p ↦ ?_⟩
  have h := integral_domSMul (μ := μ) d p
  simp only [d, Equiv.symm_apply_apply, inv_inv, Units.smul_def, smul_eq_mul] at h
  apply h.symm.trans
  apply (congrArg (fun ν ↦ ∫ y, p y ∂ν) (Measure.isAddLeftInvariant_eq_smul (d • μ) μ)).trans
  rw [integral_smul_nnreal_measure]
  rfl

private theorem sAdelePV_uniformizer (v : V) :
    ∃ π : (v.adicCompletion F)ˣ,
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer π.val := by
  let h := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 (h.choose : v.adicCompletion F) h.choose_spec.ne_zero, h.choose_spec⟩

open MeasureTheory in
open scoped ENNReal in
/-- The local principal value rescales the integral by a scalar independent of the test. -/
private theorem sAdelePV_integral_local (v : V) :
    ∃ κ : ℂ, ∀ g : SchwartzBruhat (Multiplicative (v.adicCompletion F)),
      ∫ y, finitePlacePrincipalValue v g (Multiplicative.ofAdd y)
          ∂finiteLocalAdditiveTamagawaMeasure F v =
        κ * ∫ y, g (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F v := by
  let π := (sAdelePV_uniformizer (F := F) v).choose
  have hπ0 := (sAdelePV_uniformizer (F := F) v).choose_spec
  classical
  let Fv := v.adicCompletion F
  let : MeasurableSpace Fv := borel _
  let : MeasurableSpace Fvˣ := borel _
  let : BorelSpace Fv := ⟨rfl⟩
  let : BorelSpace Fvˣ := ⟨rfl⟩
  let : ProperSpace Fv := properSpace_adicCompletion v
  let : SecondCountableTopology Fvˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ := finiteLocalAdditiveTamagawaMeasure F v
  let : μ.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let Uv : Set Fvˣ := (v.adicCompletionIntegers F).units
  let μx := finiteLocalMultiplicativeTamagawaMeasure F v
  choose c hc using fun u : Fvˣ ↦ sAdelePV_integral_dilate (F := F) v (u⁻¹ * π⁻¹)
  have hUpos : 0 < μx.real Uv := (finitePlacePrincipalValue_integrable v π (finiteStandardGaussian v 1) 1).1
  have hUfin : μx Uv ≠ ∞ := fun h ↦ by
    simp [Measure.real, Uv, μx, h] at hUpos
  let ν := μx.restrict Uv
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hUfin
  let m := μx.real Uv
  refine ⟨1 - (m : ℂ)⁻¹ * ∫ u in Uv, (c u : ℂ) ∂μx, fun g ↦ ?_⟩
  let p : Fv → ℂ := fun y ↦ g (Multiplicative.ofAdd y)
  have hpm := (mem_finitePlaceSchwartz_iff F v p).mp ⟨g, fun _ ↦ rfl⟩
  have hcs : HasCompactSupport p := hpm.2
  have hpc : Continuous p := hpm.1.continuous
  have hpi : Integrable p μ := hpc.integrable_of_hasCompactSupport hcs
  let H : Fvˣ × Fv → ℂ := fun z ↦ p ((↑z.1⁻¹ : Fv) * ((↑π⁻¹ : Fv) * z.2))
  have hHi : Integrable H (ν.prod μ) := by
    have hHc : Continuous H := hpc.comp ((Units.continuous_val.comp
      (continuous_inv.comp continuous_fst)).mul (continuous_const.mul continuous_snd))
    have hUc : IsCompact Uv := Submonoid.units_isCompact
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
    have hUo : IsOpen Uv := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
    let L : Set Fv := (fun z : Fvˣ × Fv ↦ (π : Fv) * (z.1 : Fv) * z.2) '' (Uv ×ˢ tsupport p)
    have hLc : IsCompact L := (hUc.prod hcs).image (by fun_prop)
    have hK := hUc.prod hLc
    have hKint : IntegrableOn H (Uv ×ˢ L) (ν.prod μ) := hHc.continuousOn.integrableOn_compact hK
    apply ((integrable_indicator_iff (μ := ν.prod μ) hK.measurableSet).2 hKint).congr
    have hfst : ∀ᵐ z ∂(ν.prod μ), z.1 ∈ Uv :=
      QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
        (ae_restrict_mem hUo.measurableSet)
    filter_upwards [hfst] with z hz
    by_cases h0 : H z = 0
    · exact Set.indicator_apply_eq_self.mpr (fun _ ↦ h0)
    · have hk : (↑z.1⁻¹ : Fv) * ((↑π⁻¹ : Fv) * z.2) ∈ tsupport p := subset_tsupport _ h0
      have hzL : z.2 ∈ L := by
        refine ⟨(z.1, (↑z.1⁻¹ : Fv) * ((↑π⁻¹ : Fv) * z.2)), ⟨hz, hk⟩, ?_⟩
        have h1 := z.1.ne_zero
        have h2 := π.ne_zero
        simp only [Units.val_inv_eq_inv_val]
        field_simp
      exact Set.indicator_of_mem (show z ∈ Uv ×ˢ L from ⟨hz, hzL⟩) H
  have hpv : ∀ y, finitePlacePrincipalValue v g (Multiplicative.ofAdd y) =
      p y - (m : ℂ)⁻¹ * ∫ u, H (u, y) ∂ν := fun y ↦ by
    rw [finitePlacePrincipalValue_spec v π hπ0 g]
    rfl
  have hinner : ∀ u, ∫ y, H (u, y) ∂μ = c u * ∫ y, p y ∂μ := fun u ↦ by
    have := hc u p
    simp only [Units.val_mul] at this
    simp only [H, ← mul_assoc]
    exact this
  rw [integral_congr_ae (Filter.Eventually.of_forall hpv)]
  rw [integral_sub hpi (hHi.integral_prod_right.const_mul _), integral_const_mul,
    ← integral_integral_swap hHi]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const]
  change ∫ y, p y ∂μ - _ = (1 - (m : ℂ)⁻¹ * ∫ u, (c u : ℂ) ∂ν) * ∫ y, p y ∂μ
  ring

open scoped TensorProduct in
private theorem sAdelePV_ext_tensor {ι : Type*} [Fintype ι] {E X M : Type*} {W : ι → Type*}
    [AddCommGroup E] [Module ℂ E] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    (e : E ⊗[ℂ] PiTensorProduct ℂ W →ₗ[ℂ] X) (he : Function.Surjective e) (Q : X →ₗ[ℂ] X)
    (φ ψ : X →ₗ[ℂ] M)
    (h : ∀ a g, φ (Q (e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g))) =
      ψ (e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g))) (f : X) :
    φ (Q f) = ψ f := by
  obtain ⟨t, rfl⟩ := he f
  have key : (φ ∘ₗ Q) ∘ₗ e = ψ ∘ₗ e :=
    TensorProduct.ext (LinearMap.ext fun a ↦ PiTensorProduct.ext (MultilinearMap.ext fun g ↦ h a g))
  exact LinearMap.congr_fun key t

open Classical in
open scoped TensorProduct in
/-- An identity between linear maps after the S-local principal value can be checked on pure
tensors. -/
private theorem sAdelePV_ext {S T : Finset V} (hT : T ⊆ S) {M : Type*} [AddCommGroup M]
    [Module ℂ M] (φ ψ : SchwartzBruhat (Multiplicative (SAdeleRing F S)) →ₗ[ℂ] M)
    (h : ∀ (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
      φ ((sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w,
        if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w))) =
      ψ ((sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) : φ (sAdelePrincipalValue F hT f) = ψ f :=
  sAdelePV_ext_tensor (sAdeleSchwartz_inductiveTensor_equiv F S).choose.toLinearEquiv.toLinearMap
    (sAdeleSchwartz_inductiveTensor_equiv F S).choose.surjective (sAdelePrincipalValue F hT) φ ψ
    (fun a g ↦ (congrArg φ (sAdelePrincipalValue_tmul hT a g)).trans (h a g)) f

open MeasureTheory in
open scoped TensorProduct in
/-- At zero the Fourier transform of a pure tensor factors into the archimedean integral
and the product of the finite local integrals. -/
private theorem sAdelePV_fourier_tensor {S : Finset V}
    (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) :
    ∃ I : ℂ, ∀ g : (w : S) → SchwartzBruhat (Multiplicative (w.val.adicCompletion F)),
    sAdeleSchwartzFourier ((sAdeleSchwartz_inductiveTensor_equiv F S).choose
      (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd 0) =
      I * ∏ w, ∫ y, g w (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F w.val := by
  classical
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let A (x : InfiniteAdeleRing F) := a (Multiplicative.ofAdd x)
  refine ⟨∫ x, A x ∂Measure.pi (infiniteLocalAdditiveTamagawaMeasure F), fun g ↦ ?_⟩
  let factor (v : S) (y : v.val.adicCompletion F) := g v (Multiplicative.ofAdd y)
  rw [sAdeleSchwartzFourier_apply_zero]
  simp_rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g]
  exact (integral_prod_mul (μ := Measure.pi (infiniteLocalAdditiveTamagawaMeasure F))
    (ν := Measure.pi fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)
    A (fun x ↦ ∏ v, factor v (x v))).trans
      (congrArg (_ * ·) (integral_fintype_prod_eq_prod factor))

open Classical in
private theorem sAdelePV_zero_prod {S T : Finset V} (hT : T ⊆ S)
    (g : (w : S) → SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
    let g' := fun w : S ↦ if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w
    (∏ w : S, g' w (Multiplicative.ofAdd 0)) =
      (if T.Nonempty then 0 else 1) * ∏ w : S, g w (Multiplicative.ofAdd 0) := by
  intro g'
  by_cases h : T.Nonempty
  · obtain ⟨v, hv⟩ := h
    let w : S := ⟨v, hT hv⟩
    have hw : w.val ∈ T := hv
    have hz : finitePlacePrincipalValue w.val (g w) (Multiplicative.ofAdd 0) = 0 := by
      have hm : finitePlacePrincipalValue w.val (g w) ∈ range (finitePlacePrincipalValue w.val) := ⟨g w, rfl⟩
      rwa [finitePlacePrincipalValue_range] at hm
    have hp := Finset.prod_eq_zero (s := Finset.univ) (f := fun i : S ↦ g' i (Multiplicative.ofAdd 0))
      (Finset.mem_univ w) (show g' w (Multiplicative.ofAdd 0) = 0 by simpa only [g', ite_eq_left hw] using hz)
    exact hp.trans (by rw [ite_eq_left ⟨v, hv⟩, zero_mul])
  · have hg : g' = g := funext fun w ↦ ite_eq_right (fun hw ↦ h ⟨w.val, hw⟩)
    rw [hg, ite_eq_right h, one_mul]

open MeasureTheory in
open scoped TensorProduct in
/-- Paper: Remark 7.5.0.2 and Equation (7.5.0.16), p. 378.
The local principal-value operator preserves the common kernel of the two local polar moments. -/
theorem strongCoprimalityLocalPrincipalValue_mem_polar {T : Finset V} (hT : T ⊆ S) (f : Pₛ) :
    sAdelePrincipalValue F hT f.val ∈ Pₛ := by
  classical
  let L := (sAdelePolarValues_isLinear (F := F) (S := S)).mk' _
  let c (w : S) : ℂ := if w.val ∈ T then (sAdelePV_integral_local (F := F) w.val).choose else 1
  let k : ℂ := if T.Nonempty then 0 else 1
  let D := (k • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).prodMap ((∏ w, c w) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  have he := sAdelePV_ext (F := F) hT L (D.comp L) (fun a g ↦ ?_) f.val
  · change L (sAdelePrincipalValue F hT f.val) = 0
    exact he.trans (show D (L f.val) = 0 from (congrArg D f.property).trans (map_zero D))
  · let g' (w : S) := if w.val ∈ T then finitePlacePrincipalValue w.val (g w) else g w
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    refine Prod.ext ?_ ?_
    · change e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g' w)) (Multiplicative.ofAdd 0) =
        k * e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd 0)
      apply ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g' 0).trans
      refine Eq.trans ?_ (congrArg (k * ·) ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a g 0).symm)
      exact (congrArg (_ * ·) (sAdelePV_zero_prod hT g)).trans (mul_left_comm ..)
    · change sAdeleSchwartzFourier (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g' w))) (Multiplicative.ofAdd 0) =
        (∏ w, c w) * sAdeleSchwartzFourier (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd 0)
      let hI := sAdelePV_fourier_tensor (S := S) a
      apply (hI.choose_spec g').trans
      refine Eq.trans ?_ (congrArg ((∏ w, c w) * ·) (hI.choose_spec g).symm)
      have hi (w : S) : (∫ y, g' w (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F w.val) =
          c w * ∫ y, g w (Multiplicative.ofAdd y) ∂finiteLocalAdditiveTamagawaMeasure F w.val := by
        by_cases h : w.val ∈ T
        · simpa only [g', c, ite_eq_left h] using (sAdelePV_integral_local (F := F) w.val).choose_spec (g w)
        · simp only [g', c, ite_eq_right h, one_mul]
      have hprod := (Finset.prod_congr (s₁ := Finset.univ) rfl fun w _ ↦ hi w).trans Finset.prod_mul_distrib
      exact (congrArg (hI.choose * ·) hprod).trans (mul_left_comm ..)

/-- Paper: Remark 7.5.0.2 and Equations (7.5.0.15)–(7.5.0.16), pp. 378–379.
Insertion of the outside integer indicators gives the primary quotient isomorphism
once the norm-one character is unramified outside S and the S-integer Picard group is trivial.
Deviation: S includes the selected primary places. The denominator uses the same S-adelic
space as the numerator, with all archimedean places implicit. -/
theorem strongCoprimalityPrimaryQuotient_local_equiv (ω : PontryaginDual C₁) (p : Vℚ)
    (hp : (finite_nuclearityPlacesAbove (F := F) p).toFinset ⊆ S)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let η : PontryaginDual J₁ := sLocalNormOneCharacter S ω hω
    let Dₛ := Submodule.span ℂ (range fun f : Pₛ ↦
      (Submodule.Quotient.mk ⟨sAdelePrincipalValue F hp f.val,
        strongCoprimalityLocalPrincipalValue_mem_polar hp f⟩ : ↥Pₛ ⧸ Kₛ(η)))
    let D := strongCoprimalityDenominator ω T
    ∃ e : ((↥Pₛ ⧸ Kₛ(η)) ⧸ Dₛ) ≃L[ℂ] (StrongCoprimalityThetaSpace ω ⧸ D),
      ∀ f : Pₛ, e (Dₛ.mkQ ((Kₛ(η)).mkQ f)) = D.mkQ ((K(ω)).mkQ
        ⟨sAdeleSchwartzToGlobal F S f.val, sAdeleSchwartzToGlobal_mem_polarSubspace f⟩) := by sorry

end SLocal

/-- Paper: Remark 7.5.0.2, p. 379.
The primary quotient is a closed subspace of a Hausdorff quotient of a finite product
of smooth periodic spaces, expressed via their rapidly decreasing Fourier sequences. -/
theorem strongCoprimalityPrimaryQuotient_sequence_subquotient (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := Fin T.card → RapidDecaySequence 1
    ∃ (D : Submodule ℂ E) (W : Submodule ℂ (E ⧸ D)),
      IsClosed (D : Set E) ∧ IsClosed (W : Set (E ⧸ D)) ∧
        Nonempty (StrongCoprimalityQuotient ω T ≃L[ℂ] W) := by sorry

-- TODO(prerequisite): The separate Köthe-space assertion requires a general
-- Köthe-space model. The example in §C.1.5, p. 667 is unfinished.

/-- Paper: Remark 7.5.0.2, p. 379.
The strong dual of the primary quotient is a Hausdorff quotient of a closed subspace
of the strong dual of the finite product of rapidly decreasing sequence spaces.
Deviation: The ambient sequence spaces on the dual side are strong duals. -/
theorem strongCoprimalityPrimaryQuotient_strongDual_subquotient (ω : PontryaginDual C₁) (p : Vℚ) :
    let T := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    let E := StrongDual ℂ (Fin T.card → RapidDecaySequence 1)
    ∃ (W : Submodule ℂ E) (D : Submodule ℂ W),
      IsClosed (W : Set E) ∧ IsClosed (D : Set W) ∧
        Nonempty (StrongDual ℂ (StrongCoprimalityQuotient ω T) ≃L[ℂ] (W ⧸ D)) := by sorry

-- TODO(later): needs §8.1 for the orbital-support and support-constrained basis claims
-- announced on p. 374 and at the start of Chapter 8 on p. 381.

open Classical in
/-- Paper: Corollary 7.5.0.3 and Equation (7.5.0.17), p. 379.
Every entire Schwartz–Bergman function is the sum of an entire multiple of the
regularized completed Hecke function and an Euler polynomial times another
Schwartz–Bergman function. The first summand is itself Schwartz–Bergman.
The sign converts the pole polynomial of §7.1.4 to the convention in (7.5.0.17). -/
theorem strongCoprimality_bezout (S : Finset V)
    (_hS : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ : B) :
    let L := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    ∃ (u : entireContinuousMapSubalgebra) (v w : B),
      (∀ s : ℂ, w.val s = (-1 : ℂ) ^ δ * L.val s * u.val s) ∧
      ∀ s : ℂ, w.val s + reciprocalPartialHeckeEulerProduct χ S s * v.val s = φ.val s := by sorry

end RiemannMasullo
