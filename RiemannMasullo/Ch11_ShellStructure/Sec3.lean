module

public import Mathlib.NumberTheory.PrimeCounting
public import RiemannMasullo.Ch11_ShellStructure.Sec2b

import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch11_ShellStructure.Sec1a

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec5

/-!
# Orbital kernels and orbital traces

Masullo, §11.3, pp. 491–496. The divisorial filtration is on ideles.
All archimedean places are implicit in the finite-place base set.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleMeasurableSpaceSec1a

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "N𝔽" => (ideleNorm F).ker
local notation "C₁" => (ideleClassNorm F).ker
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "above(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "resChar(" v ")" => Rat.HeightOneSpectrum.natGenerator ((v).under (𝓞 ℚ))

/-- Paper: (11.3.1.1), p. 492. For a base with trivial S-integer Picard group and
an unramified outside character, each homogeneous polar theta function has a
representative obtained by adjoining the integer indicators to an S-local test.
Deviation: The printed condition that S contains the places ramified over ℚ is
not used by Theorem 6.2.1.1(2) and is omitted. As on the page, the S-local test
is not asserted to have zero polar values. -/
theorem exists_divisorialThetaRepresentative (S : Finset V)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (f : adelePolarSubspace F) :
    ∃ fS : ℬₛ(S), homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F S fS) =
      homogeneousAdelicTheta ω f.val := by
  obtain ⟨e, he⟩ :=
    sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) _hPic (ω := ω) _hω
  have hsurj : Function.Surjective (sLocalHomogeneousThetaToGlobal (F := F) (ω := ω) _hω) := by
    rw [← he]
    exact e.surjective
  obtain ⟨y, hy⟩ := hsurj ((LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)).mkQ f.val)
  obtain ⟨fS, hfS⟩ := Submodule.mkQ_surjective
    (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S
      (sLocalNormOneCharacter (F := F) S ω _hω))) y
  rw [← hfS] at hy
  refine ⟨fS, ?_⟩
  refine (globalHomogeneousThetaSpace_mk_eq_iff (F := F) ω _ _).mp ?_
  have h1 : (homogeneousAdelicThetaLinearMap F ω).ker.mkQ ((sAdeleSchwartzToGlobal F S) fS)
      = (homogeneousAdelicThetaLinearMap F ω).ker.mkQ (f.val) := by
    rw [← sLocalHomogeneousThetaToGlobal_mk (F := F) (S := S) _hω fS]
    exact hy
  simpa only [Submodule.mkQ_apply] using h1

/-- Paper: §11.3.1.1, p. 492, before (11.3.1.2). The local factor is the
indicator of ideles whose component at the chosen finite place is a unit.
Deviation: The unrestricted tensor coordinates contribute the constant one. -/
def divisorialLocalIndicator (v : V) (g : I𝔽) : ℂ :=
  if Valued.v (g.val.2 v) = 1 then 1 else 0

/-- Paper: §11.3.1.1, p. 492. The local indicator detects precisely the
integer units in the chosen coordinate. -/
theorem divisorialLocalIndicator_eq_one_iff (v : V) (g : I𝔽) :
    divisorialLocalIndicator v g = 1 ↔ Valued.v (g.val.2 v) = 1 := by
  unfold divisorialLocalIndicator
  split_ifs with h <;> simp [h]

/-- Paper: (11.3.1.2), p. 492. Multiply the local unit indicators at the
selected finite places. The base set enters through the choice of these places. -/
def divisorialIndicator (T : Finset V) (g : I𝔽) : ℂ :=
  ∏ v ∈ T, divisorialLocalIndicator v g

/-- Paper: (11.3.1.2), p. 492. For a singleton the product recovers the local
indicator. -/
theorem divisorialIndicator_singleton (v : V) (g : I𝔽) :
    divisorialIndicator {v} g = divisorialLocalIndicator v g := by
  simp [divisorialIndicator]

variable (F) in
/-- Paper: §11.3.1.1, p. 492, after (11.3.1.2). The divisorial stratum imposes
the local unit condition at each selected finite place.
Deviation: The ambient set on the right is the full idele group. -/
def divisorialStratum (T : Finset V) : Set I𝔽 :=
  {g | ∀ v ∈ T, Valued.v (g.val.2 v) = 1}

/-- Paper: §11.3.1.1, pp. 492–493. The finite product of local indicators
is the indicator of the stratum. -/
theorem divisorialIndicator_eq_indicator (T : Finset V) :
    divisorialIndicator T = (divisorialStratum F T).indicator (fun _ ↦ 1) := by
  ext g
  by_cases h : g ∈ divisorialStratum F T
  · rw [Set.indicator_of_mem h]
    exact Finset.prod_eq_one fun v hv ↦ by simp [divisorialLocalIndicator, h v hv]
  · rw [Set.indicator_of_notMem h]
    obtain ⟨v, hv, hne⟩ : ∃ v ∈ T, ¬ Valued.v (g.val.2 v) = 1 := by
      simpa [divisorialStratum] using h
    exact Finset.prod_eq_zero hv (by simp [divisorialLocalIndicator, hne])

/-- Paper: §11.3.1.1, p. 492. Every divisorial stratum is open and closed. -/
theorem isClopen_divisorialStratum (T : Finset V) :
    IsClopen (divisorialStratum F T) := by
  have h : divisorialStratum F T = ⋂ v ∈ T, {g : I𝔽 | Valued.v (g.val.2 v) = 1} := by
    ext g; simp [divisorialStratum]
  rw [h]
  refine isClopen_biInter_finset fun v _ ↦ ?_
  have hc : Continuous fun g : I𝔽 ↦ g.val.2 v :=
    (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
  have hs : IsClopen {x : v.adicCompletion F | Valued.v.restrict x = 1} :=
    Valued.isClopen_sphere _ one_ne_zero
  simp only [Valuation.restrict_eq_one_iff] at hs
  exact hs.preimage hc

/-- Paper: §11.3.1.1, pp. 492–493. The difference of two nested strata consists
of ideles satisfying the old conditions and failing a condition at some new place.
The failure of a unit condition is the union of the nonzero valuation classes. -/
theorem divisorialStratum_sdiff (T U : Finset V) (hTU : T ⊆ U) :
    divisorialStratum F T \ divisorialStratum F U =
      ⋃ v ∈ U \ T, {g ∈ divisorialStratum F T | Valued.v (g.val.2 v) ≠ 1} := by
  classical
  ext g
  simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_sdiff]
  constructor
  · rintro ⟨hT, hU⟩
    change ¬ ∀ v ∈ U, Valued.v (g.val.2 v) = 1 at hU
    push_neg at hU
    obtain ⟨v, hvU, hv⟩ := hU
    exact ⟨v, ⟨hvU, fun hvT ↦ hv (hT v hvT)⟩, hT, hv⟩
  · rintro ⟨v, ⟨hvU, _⟩, hT, hv⟩
    exact ⟨hT, fun hU ↦ hv (hU v hvU)⟩

private theorem primaryDivisorial_infinite (S : Finset V) :
    (setOf (fun p : ℕ ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v)))).Infinite := by
  have := Nat.infinite_setOf_prime.diff (S.image (fun v ↦ resChar(v))).finite_toSet
  refine this.mono ?_
  intro p hp
  exact ⟨hp.1, by simpa using hp.2⟩

/-- Paper: §11.3.1.1, pp. 492–493. The sequence of rational primes omitting the
residue characteristics represented in the finite base consists of primes. -/
theorem primaryDivisorialPrime_isPrime (S : Finset V) (k : ℕ) :
    (Nat.nth (fun p ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) k).Prime :=
  (Nat.nth_mem_of_infinite (primaryDivisorial_infinite S) k).1

/-- Paper: §11.3.1.1, p. 493. The rational prime for the next primary step is
selected in increasing order.
Deviation: Skip the residue characteristics in the base S as required by (11.3.1.2). -/
def primaryDivisorialPrime (S : Finset V) (k : ℕ) : Vℚ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨_, primaryDivisorialPrime_isPrime S k⟩

/-- Paper: §11.3.1.1, p. 493. With no excluded primes the first step uses the
prime 2. -/
theorem primaryDivisorialPrime_empty_zero :
    primaryDivisorialPrime (∅ : Finset V) 0 =
      Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩ := by
  unfold primaryDivisorialPrime
  refine congrArg Rat.HeightOneSpectrum.primesEquiv.symm (Subtype.ext ?_)
  show Nat.nth _ 0 = 2
  rw [Nat.nth_zero]
  simp only [Finset.image_empty, Finset.notMem_empty, not_false_eq_true, and_true]
  exact le_antisymm (Nat.sInf_le Nat.prime_two)
    (le_csInf ⟨2, Nat.prime_two⟩ fun p hp ↦ hp.two_le)

variable (F) in
/-- Paper: §11.3.1.1, p. 493. The kth primary place set takes the full fibres
over the first k rational primes of the sequence outside the base. -/
def primaryDivisorialPlaces (S : Finset V) (k : ℕ) : Finset V :=
  (Finset.range k).biUnion (fun j ↦ above(primaryDivisorialPrime S j))

/-- Paper: §11.3.1.1, p. 493. The next step adds precisely the places over the
next rational prime. -/
theorem primaryDivisorialPlaces_succ (S : Finset V) (k : ℕ) :
    primaryDivisorialPlaces F S (k + 1) =
      primaryDivisorialPlaces F S k ∪ above(primaryDivisorialPrime S k) := by
  simp only [primaryDivisorialPlaces, Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

private theorem primaryDivisorialPrime_eq_iff (S : Finset V) (k : ℕ) (p : Vℚ) :
    primaryDivisorialPrime S k = p ↔
      Rat.HeightOneSpectrum.natGenerator p =
        Nat.nth (fun p ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) k := by
  unfold primaryDivisorialPrime
  constructor
  · rintro rfl
    exact congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _)
  · intro h
    exact Rat.HeightOneSpectrum.primesEquiv.symm_apply_eq.2 (Subtype.ext h.symm)

/-- Paper: §11.3.1.1, p. 493. Together the indices exhaust the finite places
outside a saturated base. -/
theorem iUnion_primaryDivisorialPlaces (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) :
    (⋃ k, (primaryDivisorialPlaces F S k : Set V)) = (S : Set V)ᶜ := by
  ext w
  simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_compl_iff, primaryDivisorialPlaces,
    Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, j, hj, hw⟩ hwS
    have hw' : w.under (𝓞 ℚ) = primaryDivisorialPrime S j := by
      simpa [Set.Finite.mem_toFinset] using hw
    have h1 := (primaryDivisorialPrime_eq_iff S j _).1 hw'.symm
    have h2 := (Nat.nth_mem_of_infinite (primaryDivisorial_infinite S) j).2
    have h3 : Rat.HeightOneSpectrum.natGenerator (w.under (𝓞 ℚ)) ∈
        S.image (fun v ↦ resChar(v)) := Finset.mem_image.2 ⟨w, hwS, rfl⟩
    rw [h1] at h3
    exact h2 h3
  · intro hwS
    have hq : (fun p : ℕ ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) (resChar(w)) := by
      refine ⟨Rat.HeightOneSpectrum.prime_natGenerator _, fun hin ↦ ?_⟩
      obtain ⟨v, hv, hvq⟩ := Finset.mem_image.1 hin
      apply hwS
      apply _hS v hv w
      exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hvq.symm)
    have hq' : resChar(w) ∈ Set.ofPred
        (fun p : ℕ ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) := hq
    obtain ⟨k, hk⟩ := Nat.subset_range_nth hq'
    refine ⟨k + 1, k, by omega, ?_⟩
    rw [Set.Finite.mem_toFinset]
    exact ((primaryDivisorialPrime_eq_iff S k _).2 hk.symm).symm

/-- Paper: §11.3.1.1, p. 493. An idele with unit components at every place over
the chosen rational primes has unit norm components at those primes.
Deviation: The printed reverse inclusion fails when local valuations cancel above
a split prime. -/
theorem relativeIdeleNormRat_mem_divisorialStratum
    (T : Finset Vℚ) :
    divisorialStratum F (T.biUnion (fun p ↦ above(p))) ⊆
      (relativeIdeleNormRat F) ⁻¹' divisorialStratum ℚ T := by
  have hQ (v : Vℚ) (x : v.adicCompletion ℚ) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
    rw [FinitePlace.norm_def, NNReal.coe_eq_one,
      WithZeroMulInt.toNNReal_eq_one_iff _ _ (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']
  have hF (v : V) (x : v.adicCompletion F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
    rw [FinitePlace.norm_def, NNReal.coe_eq_one,
      WithZeroMulInt.toNNReal_eq_one_iff _ _ (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']
  intro g hg p hp
  refine (hQ p _).1 ?_
  refine (rationalAdeleNorm_finitePlace F p g.val).trans ?_
  refine finprod_eq_one_of_forall_eq_one fun w ↦ ?_
  rw [finprod_eq_if]
  split_ifs with hw
  · exact (hF w _).2 (hg w (Finset.mem_biUnion.2
      ⟨p, hp, (finite_nuclearityPlacesAbove p).mem_toFinset.2 hw⟩))
  · rfl

/-- Paper: §11.3.1.1, p. 493. The product of the unit indicators on a finite set
outside S converts the integer-extended test to its principal value at those places.
Deviation: Read the remaining integer factors as indexed outside S and the
selected places. The equality is recorded on the ideles. -/
theorem divisorialIndicator_mul_thetaRepresentative (S T : Finset V) (_hST : Disjoint S T)
    (f : ℬₛ(S)) (g : I𝔽) :
    divisorialIndicator T g * sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd g.val) =
      adelePrincipalValue F T (sAdeleSchwartzToGlobal F S f) (Multiplicative.ofAdd g.val) := by sorry

/-- Paper: §11.3.1.1, p. 493. Removing the next prime's integer factors
multiplies the zeta transform of the depleted test by the reciprocal Euler
product over that prime.
Deviation: State the identity on the half-plane of absolute convergence. -/
theorem primaryDivisorialZeta_succ (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (_hχ : ∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : ℬₛ(S)) (z : ℂ) (_hz : 1 < z.re) :
    let c := ideleClassNormTwist χ z
    let Z := fun j ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S j) (sAdeleSchwartzToGlobal F S f)) c
    Z (k + 1) = reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k) z * Z k :=
  by sorry

/-- Paper: §11.3.1.1, p. 493. For a test whose global extension has both polar
values zero the depletion identity holds at every exponent, in particular at the
zeros of the reciprocal Euler product, which lie on the line of real part zero.
Deviation: The polar condition makes both zeta functions entire, so the
normal-form values at poles do not enter. -/
theorem primaryDivisorialZeta_succ_of_polar (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (_hχ : ∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : ℬₛ(S)) (_hf : sAdeleSchwartzToGlobal F S f ∈ adelePolarSubspace F) (z : ℂ) :
    let c := ideleClassNormTwist χ z
    let Z := fun j ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S j) (sAdeleSchwartzToGlobal F S f)) c
    Z (k + 1) = reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k) z * Z k :=
  by
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f, _hf⟩
  let Z (j : ℕ) (w : ℂ) := globalIdelicZFunction
    (adelePrincipalValue F (primaryDivisorialPlaces F S j) f₀.val) (ideleClassNormTwist χ w)
  have ha (j : ℕ) : AnalyticOnNhd ℂ (Z j) univ := fun z _ ↦
    (globalIdelicZFunction_entire_of_vanishing _
      (adelePrincipalValue_mem_polarSubspace (primaryDivisorialPlaces F S j) f₀) χ).analyticAt z
  let Q := reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k)
  have hQ : AnalyticOnNhd ℂ Q univ := fun w _ ↦
    (strongCoprimalityJetMatrix_det_ne_zero_euler χ above(primaryDivisorialPrime S k)).1 w
  have he : Z (k + 1) =ᶠ[nhds (2 : ℂ)] Q * Z k := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually
      (eventually_gt_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num))] with w hw
    exact primaryDivisorialZeta_succ S k χ _hχ f w hw
  exact congrFun ((ha _).eq_of_eventuallyEq (hQ.mul (ha k)) he) z

-- TODO(paper-gap): The local "Weil's Identity" on p. 492 has an extra factor
-- μᵥ(𝒪ᵥˣ) on the left. With the Tamagawa measure of (A.3.2.2) both
-- Zᵥ(1_{𝒪ᵥˣ}, c) and Lᵥ(c)⁻¹ Zᵥ(1_{𝒪ᵥ}, c) equal μᵥ(𝒪ᵥˣ) for unramified c, so
-- the print holds only where this mass is one. At the place over 2 of ℚ(i) the
-- mass is 1/2 and the two printed sides are 1/4 and 1/2. The same page gives the
-- product of all unit masses as the square root of the absolute different. It
-- is the reciprocal square root of the absolute discriminant.

section ThetaSubquotient

local notation "P" => adelePolarSubspace F
local notation "Θ(" ω ")" =>
  (↥P ⧸ LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P))

/-- Paper: (11.3.1.3), p. 494. The theta denominator at a given stage is the
image of polar-free tests after the selected principal values in the polar
homogeneous theta space. -/
def divisorialThetaStage (ω : PontryaginDual C₁) (T : Finset V) : Submodule ℂ Θ(ω) :=
  Submodule.span ℂ (Set.range fun f : P ↦ (Submodule.Quotient.mk
    ⟨adelePrincipalValue F T f.val, adelePrincipalValue_mem_polarSubspace T f⟩ : Θ(ω)))

/-- Conjugating `map id Q` by an equivalence gives the identity when `Q` fixes every vector.
Stated in the shape of `sAdelePrincipalValue`, so that it applies syntactically. -/
private theorem divisorialThetaStage_empty_conj_left {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (Q : G →ₗ[ℂ] G) (hQ : ∀ x, Q x = x) :
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) Q).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hQ' : Q = LinearMap.id := LinearMap.ext hQ
  subst hQ'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

/-- Conjugating `map Q id` by an equivalence gives the identity when `Q` fixes every vector.
Stated in the shape of `adelePrincipalValue`, so that it applies syntactically. -/
private theorem divisorialThetaStage_empty_conj_right {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (Q : E →ₗ[ℂ] E) (hQ : ∀ x, Q x = x) :
    e.toLinearMap.comp ((TensorProduct.map Q (LinearMap.id : G →ₗ[ℂ] G)).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hQ' : Q = LinearMap.id := LinearMap.ext hQ
  subst hQ'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

open scoped TensorProduct in
/-- A tensor power of identity maps fixes every vector of the finest locally convex copy. -/
private theorem divisorialThetaStage_empty_piMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (f : ∀ i, M i →ₗ[ℂ] M i) (hf : ∀ i, f i = LinearMap.id)
    (x : FinestLocallyConvex (⨂[ℂ] i, M i)) :
    (PiTensorProduct.map f : FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ]
      FinestLocallyConvex (⨂[ℂ] i, M i)) x = x := by
  have : f = fun _ ↦ LinearMap.id := funext hf
  subst this
  rw [PiTensorProduct.map_id]
  rfl

/-- With no selected places the S-local principal value is the identity. -/
private theorem divisorialThetaStage_empty_sPV (h : (∅ : Finset V) ⊆ ∅) :
    sAdelePrincipalValue F h = LinearMap.id := by
  unfold sAdelePrincipalValue
  exact divisorialThetaStage_empty_conj_left _ _
    (divisorialThetaStage_empty_piMap _ fun w ↦ absurd w.2 (Finset.notMem_empty _))

/-- With no selected places the global principal value is the identity. -/
private theorem divisorialThetaStage_empty_PV :
    adelePrincipalValue F (∅ : Finset V) = LinearMap.id := by
  unfold adelePrincipalValue
  exact divisorialThetaStage_empty_conj_right _ _ fun x ↦
    LinearMap.congr_fun (divisorialThetaStage_empty_sPV _) x

private theorem divisorialThetaStage_empty_span {α M : Type*} [AddCommMonoid M] [Module ℂ M]
    (f g : α → M) (hfg : f = g) (hg : Function.Surjective g) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  subst hfg
  rw [hg.range_eq]
  exact Submodule.span_univ

/-- Paper: (11.3.1.3), p. 494. With no principal values the stage is the entire
polar homogeneous theta space. -/
theorem divisorialThetaStage_empty (ω : PontryaginDual C₁) :
    divisorialThetaStage ω ∅ = ⊤ := by
  unfold divisorialThetaStage
  refine divisorialThetaStage_empty_span _ (fun p : P ↦ (Submodule.Quotient.mk p : Θ(ω))) ?_
    (Submodule.Quotient.mk_surjective _)
  funext p
  have e : (⟨adelePrincipalValue F ∅ p.val, adelePrincipalValue_mem_polarSubspace ∅ p⟩ : P) = p :=
    Subtype.ext (LinearMap.ext_iff.mp divisorialThetaStage_empty_PV p.val)
  exact congrArg (fun y : P ↦ (Submodule.Quotient.mk y : Θ(ω))) e

/-- Two linear maps agree once they agree on the pure tensors of an
inductive tensor product with a finite tensor product. -/
private theorem divisorialThetaStage_antitone_extPi {ι : Type*} [Fintype ι] {E N : Type*}
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E (FinestLocallyConvex (PiTensorProduct ℂ M)) ≃L[ℂ] N)
    (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (g : ∀ i, M i),
      L₁ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g))) =
        L₂ (e (TensorProduct.tmul ℂ a (PiTensorProduct.tprod ℂ g)))) :
    L₁ = L₂ := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top (h a)

/-- The S-local principal values compose over disjoint sets of selected places. -/
private theorem divisorialThetaStage_antitone_sPV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    sAdelePrincipalValue F (Finset.Subset.refl T') =
      (sAdelePrincipalValue F hT).comp (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T))) := by
  refine divisorialThetaStage_antitone_extPi (sAdeleSchwartz_inductiveTensor_equiv F T').choose _ _ fun a g ↦ ?_
  have h1 := sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a g
  have h2 := sAdelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a g
  have h3 := sAdelePrincipalValue_tmul (F := F) hT a
    (fun w : T' ↦ if (w : HeightOneSpectrum (𝓞 F)) ∈ T' \ T then
      finitePlacePrincipalValue (F := F) w.val (g w) else g w)
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (sAdelePrincipalValue F hT) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg
  apply congrArg
  funext w
  by_cases hw : (w : HeightOneSpectrum (𝓞 F)) ∈ T
  · simp [hw, w.2, Finset.mem_sdiff]
  · simp [hw, w.2, Finset.mem_sdiff]

/-- Two linear maps agree once they agree on the pure tensors of an inductive tensor product. -/
private theorem divisorialThetaStage_antitone_extTail {E G N : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (b : G), L₁ (e (TensorProduct.tmul ℂ a b)) = L₂ (e (TensorProduct.tmul ℂ a b))) :
    L₁ = L₂ := by
  apply (LinearMap.cancel_right (g := e.toLinearMap) e.surjective).mp
  apply TensorProduct.ext
  exact LinearMap.ext fun a ↦ LinearMap.ext (h a)

/-- The global principal value at a larger set is the one at the smaller set after the one
at the difference. -/
private theorem divisorialThetaStage_antitone_PV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    adelePrincipalValue F T' =
      (adelePrincipalValue F T).comp (adelePrincipalValue F (T' \ T)) := by
  refine divisorialThetaStage_antitone_extTail (sAdeleTailSchwartz_inductiveTensor_equiv F T').choose _ _ fun a b ↦ ?_
  have h1 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a b
  have h2 := adelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a b
  have h3 := adelePrincipalValue_tmul (F := F) hT
    (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T)) a) b
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (adelePrincipalValue F T) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg₂ _ _ rfl
  exact (LinearMap.ext_iff.mp (divisorialThetaStage_antitone_sPV hT) a).trans (LinearMap.comp_apply _ _ _)

/-- A factorization through a map preserving the submodule gives inclusion of images
after applying the quotient map. -/
private theorem divisorialThetaStage_antitone_range {A β : Type*} [AddCommMonoid A] [Module ℂ A]
    (B : Submodule ℂ A) (Φ : B → β) (L L' R : A → A)
    (h : ∀ f : B, L f.val ∈ B) (h' : ∀ f : B, L' f.val ∈ B) (hR : ∀ f : B, R f.val ∈ B)
    (hc : ∀ f : B, L (R f.val) = L' f.val) :
    Set.range (fun f : B ↦ Φ ⟨L' f.val, h' f⟩) ⊆ Set.range (fun f : B ↦ Φ ⟨L f.val, h f⟩) := by
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨R f.val, hR f⟩, congrArg Φ (Subtype.ext (hc f))⟩

/-- Paper: (11.3.1.3), p. 494. Adding places decreases the principal-value image
of the polar theta space. -/
theorem divisorialThetaStage_antitone (ω : PontryaginDual C₁) :
    Antitone (divisorialThetaStage ω) := by
  intro T T' hTT'
  have hP : ∀ f : P, adelePrincipalValue F T (adelePrincipalValue F (T' \ T) f.val) =
      adelePrincipalValue F T' f.val := fun f ↦
    ((LinearMap.ext_iff.mp (divisorialThetaStage_antitone_PV hTT') f.val).trans
      (LinearMap.comp_apply _ _ _)).symm
  unfold divisorialThetaStage
  exact Submodule.span_mono (divisorialThetaStage_antitone_range P
    (fun f : P ↦ (Submodule.Quotient.mk f : Θ(ω)))
    (adelePrincipalValue F T) (adelePrincipalValue F T') (adelePrincipalValue F (T' \ T))
    (adelePrincipalValue_mem_polarSubspace T) (adelePrincipalValue_mem_polarSubspace T')
    (adelePrincipalValue_mem_polarSubspace (T' \ T)) hP)

/-- Paper: (11.3.1.3), p. 494, and (7.4.0.2), p. 366. At the fibre over one
rational prime the stage is the finite-place denominator of §7.4, so the first
subquotient of the chain is the finite orbital quotient used there. -/
theorem divisorialThetaStage_above (χ : PontryaginDual C𝔽) (p : Vℚ) :
    divisorialThetaStage (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      C₁ →ₜ* C𝔽)) above(p) = finiteNuclearityDenominator χ p := by
  unfold divisorialThetaStage finiteNuclearityDenominator
  with_reducible rfl

/-- Paper: (11.3.1.3), p. 494. Divide the kth principal-value theta image
by the next image, viewed inside the kth stage.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def PrimaryDivisorialThetaSubquotient (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :=
  ↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
      (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype

namespace PrimaryDivisorialThetaSubquotient

instance instAddCommGroup (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    AddCommGroup (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (AddCommGroup
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instModule (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    Module ℂ (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (Module ℂ
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instTopologicalSpace (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    TopologicalSpace (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (TopologicalSpace
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instIsTopologicalAddGroup (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    IsTopologicalAddGroup (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (IsTopologicalAddGroup
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

instance instContinuousSMul (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :
    ContinuousSMul ℂ (PrimaryDivisorialThetaSubquotient S ω k) :=
  inferInstanceAs (ContinuousSMul ℂ
    (↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
    (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype))

end PrimaryDivisorialThetaSubquotient

/-- Paper: (11.3.1.3), p. 494. A representative in the kth stage has zero
class precisely when it belongs to the next stage. -/
theorem primaryDivisorialThetaSubquotient_mk_eq_zero (S : Finset V) (ω : PontryaginDual C₁)
    (k : ℕ) (x : divisorialThetaStage ω (primaryDivisorialPlaces F S k)) :
    (Submodule.Quotient.mk x : PrimaryDivisorialThetaSubquotient S ω k) = 0 ↔
      x.val ∈ divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1)) := by
  simp only [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

-- TODO(paper-gap): The claimed Schauder systems need a specified Paley–Wiener
-- subquotient at each global stage and compatible lifts in the strip Sobolev space.
-- The local subquotients of §7.3 and the zero-line quotient of §11.2.2 do not
-- identify these global stage quotients with the basis model used here.

end ThetaSubquotient

/-- Paper: (11.3.1.4), p. 494. Multiply an idelic kernel by the next indicator
minus the current indicator.
Deviation: The difference acts on the input coordinate, as in the shell
calculation on pp. 495–496. -/
def divisorialKernelDifference (S : Finset V) (k : ℕ) (K : I𝔽 × I𝔽 → ℂ)
    (xy : I𝔽 × I𝔽) : ℂ :=
  (divisorialIndicator (primaryDivisorialPlaces F S (k + 1)) xy.2 -
    divisorialIndicator (primaryDivisorialPlaces F S k) xy.2) * K xy

/-- Paper: (11.3.1.4), p. 494. On the removed part of the kth stratum the
successive difference is the negative of the original kernel. -/
theorem divisorialKernelDifference_eq_neg (S : Finset V) (k : ℕ) (K : I𝔽 × I𝔽 → ℂ)
    (xy : I𝔽 × I𝔽)
    (_hxy : xy.2 ∈ divisorialStratum F (primaryDivisorialPlaces F S k) \
      divisorialStratum F (primaryDivisorialPlaces F S (k + 1))) :
    divisorialKernelDifference S k K xy = -K xy := by
  have h1 : divisorialIndicator (primaryDivisorialPlaces F S k) xy.2 = 1 := by
    rw [divisorialIndicator_eq_indicator]; exact Set.indicator_of_mem _hxy.1 _
  have h2 : divisorialIndicator (primaryDivisorialPlaces F S (k + 1)) xy.2 = 0 := by
    rw [divisorialIndicator_eq_indicator]; exact Set.indicator_of_notMem _hxy.2 _
  simp [divisorialKernelDifference, h1, h2]

variable (F) in
/-- Paper: §11.3.1.1, p. 491, and §11.3.2, p. 495. The S-local idelic
region in the definition of β consists of ideles that are units outside S. -/
def sLocalDivisorialStratum (S : Finset V) : Set I𝔽 :=
  {g | ∀ v ∉ S, Valued.v (g.val.2 v) = 1}

/-- the finite components of an idele and its inverse multiply to one. -/
private theorem mem_sLocalDivisorialStratum_iff_inv_mul {F : Type*} [Field F] [NumberField F]
    (g : IdeleGroup (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (g⁻¹).val.2 v * g.val.2 v = 1 := by
  change ((g⁻¹ * g : IdeleGroup (𝓞 F) F).val).2 v = 1
  rw [inv_mul_cancel]
  rfl

/-- an idele component has valuation one exactly when it and the inverse component are
integral. -/
private theorem mem_sLocalDivisorialStratum_iff_valued_eq_one {F : Type*} [Field F]
    [NumberField F] (g : IdeleGroup (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (g.val.2 v) = 1 ↔
      g.val.2 v ∈ v.adicCompletionIntegers F ∧ (g⁻¹).val.2 v ∈ v.adicCompletionIntegers F := by
  have h := congrArg Valued.v (mem_sLocalDivisorialStratum_iff_inv_mul g v)
  rw [map_mul, map_one] at h
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h1
    rw [h1, mul_one] at h
    exact ⟨h1.le, h.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    calc (1 : _) = Valued.v ((g⁻¹).val.2 v) * Valued.v (g.val.2 v) := h.symm
      _ ≤ 1 * Valued.v (g.val.2 v) := mul_le_mul_left h2 _
      _ = Valued.v (g.val.2 v) := one_mul _

/-- Paper: §11.3.2, p. 495. The region of β is the product of the inserted
S-ideles and the outside integer unit group. -/
theorem mem_sLocalDivisorialStratum_iff (S : Finset V) (g : I𝔽) :
    g ∈ sLocalDivisorialStratum F S ↔
      ∃ (a : (SAdeleRing F S)ˣ) (u : outsideIntegralIdeleUnits F S),
        g = sIdeleInsertion F S a * u.val := by
  constructor
  · intro hg
    set b := sIdeleInsertion F S (Units.map (adeleProjection F S).toMonoidHom g)
    obtain ⟨hb1, hbS, hbout⟩ :=
      sIdeleInsertion_apply F S (Units.map (adeleProjection F S).toMonoidHom g)
    have hinv1 : (b⁻¹).val.1 * b.val.1 = 1 := by
      change ((b⁻¹ * b : I𝔽).val).1 = 1
      rw [inv_mul_cancel]
      rfl
    refine ⟨_, ⟨b⁻¹ * g, ?_⟩, (mul_inv_cancel_left b g).symm⟩
    rw [mem_outsideIntegralIdeleUnits_iff]
    refine ⟨?_, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
    · change (b⁻¹).val.1 * g.val.1 = 1
      rw [← hinv1, hb1]
      rfl
    · change (b⁻¹).val.2 w * g.val.2 w = 1
      rw [← mem_sLocalDivisorialStratum_iff_inv_mul b w, hbS ⟨w, hw⟩]
      rfl
    · have hbw : (b⁻¹).val.2 w = 1 := by
        have h := mem_sLocalDivisorialStratum_iff_inv_mul b w
        rwa [hbout w hw, mul_one] at h
      have h1 : (b⁻¹ * g).val.2 w = g.val.2 w := by
        change (b⁻¹).val.2 w * g.val.2 w = _
        rw [hbw, one_mul]
      have h2 : ((b⁻¹ * g)⁻¹).val.2 w = (g⁻¹).val.2 w := by
        rw [mul_inv_rev, inv_inv]
        change (g⁻¹).val.2 w * b.val.2 w = _
        rw [hbout w hw, mul_one]
      rw [h1, h2]
      exact (mem_sLocalDivisorialStratum_iff_valued_eq_one g w).1 (hg w hw)
  · rintro ⟨a, ⟨u, hu⟩, rfl⟩ v hv
    obtain ⟨-, -, hu⟩ := (mem_outsideIntegralIdeleUnits_iff u).1 hu
    have hb := (sIdeleInsertion_apply F S a).2.2 v hv
    have hval : (sIdeleInsertion F S a * u).val.2 v = u.val.2 v := by
      change (sIdeleInsertion F S a).val.2 v * u.val.2 v = _
      rw [hb, one_mul]
    rw [hval]
    exact (mem_sLocalDivisorialStratum_iff_valued_eq_one u v).2 (hu v hv)

/-- Paper: §11.3.2, p. 495, and (D.1.10.1), p. 783. The region of β is the range
of the insertion of the ideles integral outside S. -/
theorem sLocalDivisorialStratum_eq_range_integralIdeleInsertion (S : Finset V) :
    sLocalDivisorialStratum F S = Set.range (integralIdeleInsertion F S) := by
  ext g
  rw [mem_range_integralIdeleInsertion]
  change (∀ v ∉ S, Valued.v (g.val.2 v) = 1) ↔ _
  refine forall_congr' fun v ↦ imp_congr_right fun _ ↦ ?_
  let u := Units.map ((RestrictedProduct.evalRingHom (fun w : V ↦ w.adicCompletion F) v).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom g
  change Valued.v u.val = 1 ↔
    u.val ∈ v.adicCompletionIntegers F ∧ u.inv ∈ v.adicCompletionIntegers F
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hinv : Valued.v u.inv = (Valued.v u.val)⁻¹ := by
    rw [show u.inv = u.val⁻¹ from Units.val_inv_eq_inv_val u, map_inv₀]
  rw [hinv, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr u.ne_zero))]
  exact le_antisymm_iff

/-- Paper: §11.3.1.1, pp. 492–493. At a saturated base, the limit of the
descending primary strata is the S-local idelic region. -/
theorem iInter_primaryDivisorialStratum (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) :
    (⋂ k, divisorialStratum F (primaryDivisorialPlaces F S k)) =
      sLocalDivisorialStratum F S := by
  have hplaces := iUnion_primaryDivisorialPlaces S _hS
  ext g
  rw [Set.mem_iInter]
  change (∀ k v, v ∈ primaryDivisorialPlaces F S k → Valued.v (g.val.2 v) = 1) ↔
    ∀ v ∉ S, Valued.v (g.val.2 v) = 1
  constructor
  · intro hg v hv
    have hu : v ∈ ⋃ k, (primaryDivisorialPlaces F S k : Set V) := by
      rw [hplaces]
      exact hv
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hu
    exact hg k v hk
  · intro hg k v hv
    apply hg v
    have hu : v ∈ ⋃ k, (primaryDivisorialPlaces F S k : Set V) :=
      Set.mem_iUnion.mpr ⟨k, hv⟩
    rwa [hplaces] at hu

/-- Paper: §11.3.1.1, p. 491 and (11.3.1.4), p. 494. The differences telescope
pointwise to the S-local restriction minus the original kernel. For each pair
of ideles at most one difference contributes.
Deviation: The sign here follows (11.3.1.4). The opening display on p. 491
adds the differences where it would need to subtract them. -/
theorem hasSum_divisorialKernelDifference (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    (K : I𝔽 × I𝔽 → ℂ) (xy : I𝔽 × I𝔽) :
    HasSum (fun k ↦ divisorialKernelDifference S k K xy)
      ((sLocalDivisorialStratum F S).indicator (fun _ ↦ K xy) xy.2 - K xy) := by
  classical
  let a : ℕ → ℂ := fun k ↦ divisorialIndicator (primaryDivisorialPlaces F S k) xy.2
  let b := (sLocalDivisorialStratum F S).indicator (fun _ ↦ (1 : ℂ)) xy.2
  have hi := iInter_primaryDivisorialStratum S _hS
  have hmono : Monotone (primaryDivisorialPlaces F S) :=
    monotone_nat_of_le_succ fun k ↦ by
      rw [primaryDivisorialPlaces_succ]
      exact Finset.subset_union_left
  have htail : ∃ N : ℕ, ∀ k ≥ N, a k = b := by
    by_cases h : xy.2 ∈ sLocalDivisorialStratum F S
    · have hall := Set.mem_iInter.mp (hi.symm ▸ h)
      exact ⟨0, fun k _ ↦ by
        simp [a, b, divisorialIndicator_eq_indicator, h, hall k]⟩
    · have hn : ¬ ∀ k, xy.2 ∈ divisorialStratum F (primaryDivisorialPlaces F S k) :=
        fun hk ↦ h (hi ▸ Set.mem_iInter.mpr hk)
      push_neg at hn
      obtain ⟨N, hN⟩ := hn
      refine ⟨N, fun k hk ↦ ?_⟩
      have hk' : xy.2 ∉ divisorialStratum F (primaryDivisorialPlaces F S k) :=
        fun hg ↦ hN (fun v hv ↦ hg v (hmono hk hv))
      simp [a, b, divisorialIndicator_eq_indicator, h, hk']
  obtain ⟨N, hN⟩ := htail
  have hs : HasSum (fun k ↦ divisorialKernelDifference S k K xy)
      (∑ k ∈ Finset.range N, divisorialKernelDifference S k K xy) :=
    hasSum_sum_of_ne_finset_zero fun k hk ↦ by
      have hk' : N ≤ k := Nat.le_of_not_gt (fun h ↦ hk (Finset.mem_range.mpr h))
      change (a (k + 1) - a k) * K xy = 0
      rw [hN k hk', hN (k + 1) (hk'.trans (Nat.le_succ k)), sub_self, zero_mul]
  change HasSum _ ((∑ k ∈ Finset.range N, (a (k + 1) - a k) * K xy)) at hs
  rw [← Finset.sum_mul, Finset.sum_range_sub a, hN N le_rfl] at hs
  have ha : a 0 = 1 := by simp [a, primaryDivisorialPlaces, divisorialIndicator]
  rw [ha, sub_mul, one_mul] at hs
  by_cases h : xy.2 ∈ sLocalDivisorialStratum F S <;> simpa [b, h] using hs

section OrbitalTraces

local notation "𝒟" => BruhatCompactSupport C𝔽
local notation "πclass(" v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "q(" v ")" => (v).asIdeal.absNorm

/-- Paper: §11.3.1.1(2), pp. 494–495, and (11.3.2.5), p. 496.
The local summand of the Poisson evaluation integrates the test against the
character on each norm-one coset through a power of the local uniformizer.
Deviation: For the half-shifted Mellin sum the terms carry the norm weight
`qᵥ^(n/2)`. The Haar factor comes from the norm-one idele class measure. -/
def orbitalPlacePoissonTerm (χ : PontryaginDual C𝔽) (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (n : ℤ) : ℂ :=
  (Real.log (q(v) : ℝ) : ℂ) * (q(v) : ℂ) ^ ((n : ℂ) / 2) *
    ∫ h : C₁, φ.val (πclass(v, π) ^ n * h.val) * (χ h.val : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F

/-- Paper: §11.3.1.1(2), p. 494. At exponent zero and for the trivial
character, the Poisson term is the log residue size times the norm-one integral. -/
theorem orbitalPlacePoissonTerm_trivial_zero (φ : 𝒟) (v : V) (π : (v.adicCompletion F)ˣ) :
    orbitalPlacePoissonTerm 1 φ v π 0 =
      (Real.log (q(v) : ℝ) : ℂ) * ∫ h : C₁, φ.val h.val
        ∂normOneIdeleClassTamagawaMeasure F := by
  simp [orbitalPlacePoissonTerm]

/-- Paper: §11.3.1.1(2), p. 494, and (11.3.2.5), p. 496.
For one unramified place, the half-shifted Mellin values at the zeros of its
reciprocal Euler factor sum to its norm-one coset contributions.
Deviation: Uses the angular integral and half-shift weight of the repaired formula.
This is the analytic part of the split: decompose the Mellin integral along the
norm fibres and apply Poisson summation in the logarithmic norm coordinate. -/
private theorem orbitalEulerSum_eq_poisson_local (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F))
    (hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F)) :
    HasSum (fun z : {z : ℂ // (finiteHeckeEulerFactor χ v z)⁻¹ = 0} ↦
      nuclearityTestMellin χ φ (z.val - 1 / 2))
      (∑' n : ℤ, orbitalPlacePoissonTerm χ φ v π n) := by
  sorry

/-- Paper: §11.3.1.1(2), p. 494.
Adding the local zero sums counts a shared zero once for each vanishing factor,
which is exactly its multiplicity in the reciprocal Euler product. -/
private theorem orbitalEulerSum_eq_poisson_assemble (F : Type*) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : HeightOneSpectrum (𝓞 F) → ℂ)
    (hs : ∀ v ∈ S, HasSum
      (fun z : {z : ℂ // (finiteHeckeEulerFactor χ v z)⁻¹ = 0} ↦
        nuclearityTestMellin χ φ (z.val - 1 / 2)) (a v)) :
    HasSum (fun z : {z : ℂ // reciprocalPartialHeckeEulerProduct χ S z = 0} ↦
      (orbitalEulerMultiplicity χ S z.val : ℂ) *
        nuclearityTestMellin χ φ (z.val - 1 / 2)) (∑ v ∈ S, a v) := by
  classical
  let f : ℂ → ℂ := fun z ↦ nuclearityTestMellin χ φ (z - 1 / 2)
  have hv (v) (hv : v ∈ S) :
      HasSum ({z : ℂ | (finiteHeckeEulerFactor χ v z)⁻¹ = 0}.indicator f) (a v) :=
    hasSum_subtype_iff_indicator.mp (hs v hv)
  have h := hasSum_sum hv
  have he (z : ℂ) :
      (∑ v ∈ S, {z : ℂ | (finiteHeckeEulerFactor χ v z)⁻¹ = 0}.indicator f z) =
        (orbitalEulerMultiplicity χ S z : ℂ) * f z := by
    rw [orbitalEulerMultiplicity_eq_card]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [← Finset.sum_filter]
    simp
  have hglobal : HasSum (fun z : ℂ ↦ (orbitalEulerMultiplicity χ S z : ℂ) * f z)
      (∑ v ∈ S, a v) := h.congr_fun (fun z ↦ (he z).symm)
  apply (hasSum_subtype_iff_of_support_subset (s :=
    {z : ℂ | reciprocalPartialHeckeEulerProduct χ S z = 0}) ?_).mpr hglobal
  intro z hz
  by_contra hn
  have hnone : ∀ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹ ≠ 0 := by
    intro v hv hzv
    exact hn (Finset.prod_eq_zero hv hzv)
  have hzero : orbitalEulerMultiplicity χ S z = 0 := by
    rw [orbitalEulerMultiplicity_eq_card, Finset.filter_eq_empty_iff.mpr hnone]
    rfl
  exact hz (by simp [hzero])

/-- Paper: §11.3.1.1(2), p. 494, and (11.3.2.5), p. 496.
The half-shifted Mellin values at the zeros of the reciprocal Euler product sum,
with multiplicity, to the Poisson contributions of the places over the prime.
Deviation: This is the Poisson evaluation of the spectral expression. A layer
uses all its places, with the angular integral and the half-shift weight. -/
theorem orbitalEulerSum_eq_poisson (χ : PontryaginDual C𝔽) (φ : 𝒟) (p : Vℚ)
    (_hχ : ∀ v ∈ above(p), (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (_hπ : ∀ v ∈ above(p), Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    let zeros := {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(p) z = 0}
    HasSum (fun z : zeros ↦ (orbitalEulerMultiplicity χ above(p) z.val : ℂ) *
      nuclearityTestMellin χ φ (z.val - 1 / 2))
      (∑ v ∈ above(p), ∑' n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n) := by
  exact orbitalEulerSum_eq_poisson_assemble F χ φ above(p)
    (fun v ↦ ∑' n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n)
    (fun v hv ↦ orbitalEulerSum_eq_poisson_local F χ φ v (_hχ v hv) (π v) (_hπ v hv))

/-- Paper: §11.3.1.1(2), pp. 494–495. If the test is supported at norms
strictly between one and the residue size, every summand at that place vanishes. -/
theorem orbitalPlacePoissonTerm_eq_zero (χ : PontryaginDual C𝔽) (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (_hπ : Valued.v.IsUniformizer (π : v.adicCompletion F))
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | ((ideleClassNorm F g).val : ℝ) ∈ Ioo 1 (q(v) : ℝ)})
    (n : ℤ) :
    orbitalPlacePoissonTerm χ φ v π n = 0 := by
  have hz : ∀ h : C₁, φ.val (πclass(v, π) ^ n * h.val) = 0 := by
    intro h
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hm := _hφ hmem
    simp only [Set.mem_setOf_eq] at hm
    have h1 : ideleClassNorm F h.val = 1 := h.2
    have hq : (1 : ℝ) < q(v) := by
      exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.2
        ⟨(Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)).ne', by
          intro h0; exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h0)⟩
    have hn : (((ideleClassNorm F (πclass(v, π) ^ n * h.val)).val : ℝ≥0) : ℝ) =
        (q(v) : ℝ) ^ (-n) := by
      rw [map_mul, map_zpow, ideleClassNorm_ofAdicCompletion, h1, mul_one]
      rw [Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Units.coe_map]
      change ‖π.val‖ ^ n = _
      rw [norm_uniformizer_adicCompletion v _ _hπ, inv_zpow', zpow_neg]
    rw [hn] at hm
    obtain ⟨hm1, hm2⟩ := hm
    rcases lt_trichotomy n 0 with h0 | h0 | h0
    · have : (q(v) : ℝ) ≤ (q(v) : ℝ) ^ (-n) := by
        calc (q(v) : ℝ) = (q(v) : ℝ) ^ (1 : ℤ) := (zpow_one _).symm
          _ ≤ _ := zpow_le_zpow_right₀ hq.le (by omega)
      linarith
    · subst h0; simp at hm1
    · have : (q(v) : ℝ) ^ (-n) ≤ 1 := zpow_le_one_of_nonpos₀ hq.le (by omega)
      linarith
  unfold orbitalPlacePoissonTerm
  simp_rw [hz, zero_mul]
  simp

/-- Paper: §11.3.1.1(2), pp. 494–495. For a fixed compactly supported test
above norm one, only finitely many finite places contribute to the Poisson sum.
Deviation: The vanishing applies to the Poisson terms in (11.3.2.5).
Their identification with masses of geometric kernels requires a separate argument. -/
theorem finite_support_orbitalPlacePoisson (χ : PontryaginDual C𝔽) (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)})
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (_hπ : ∀ v, Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    {v : V | ∃ n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n ≠ 0}.Finite := by
  let normReal : C𝔽 → ℝ := fun g ↦ ((ideleClassNorm F g).val : ℝ)
  have hc : Continuous normReal :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hcomp : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨B, hB⟩ := hcomp.bddAbove_image hc.continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F) N).subset ?_
  intro v hv
  change q(v) ≤ N
  by_contra! hNv
  obtain ⟨n, hn⟩ := hv
  apply hn
  apply orbitalPlacePoissonTerm_eq_zero χ φ v (π v) (_hπ v) _ n
  intro g hg
  exact ⟨_hφ hg, (hB ⟨g, hg, rfl⟩).trans_lt (hN.trans (by exact_mod_cast hNv))⟩

/-- Paper: (11.3.2.2), p. 495. The printed weight averages products of the
two translated section indicators over the norm-one fundamental domain and
then sums over nonzero principal ideles.
Deviation: The domain is explicit and the right-hand side is a scalar weight. -/
def orbitalSectionWeight (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽) (xy : I𝔽 × I𝔽) : ℝ :=
  ∑' ξ : Fˣ, ∫ g in E,
    (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
      (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2)
      ∂normOneIdeleTamagawaMeasure F

private theorem local_principalUnits {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] :
    ∃ u : ℕ → Lˣ, Filter.Tendsto u Filter.atTop (nhds 1) ∧ (∀ n, ‖(u n : L)‖ = 1) ∧ ∀ n, u n ≠ 1 := by
  obtain ⟨π, hpos, hlt⟩ := NormedField.exists_norm_lt_one L
  let a (n : ℕ) := π ^ (n + 1)
  have ha (n : ℕ) : ‖a n‖ < 1 := by
    change ‖π ^ (n + 1)‖ < 1
    rw [norm_pow]
    exact pow_lt_one₀ hpos.le hlt n.succ_ne_zero
  have hne (n : ℕ) : 1 + a n ≠ 0 := by
    intro he
    have h := ha n
    rw [show a n = -1 by linear_combination he, norm_neg, norm_one] at h
    exact lt_irrefl _ h
  let u (n : ℕ) := Units.mk0 (1 + a n) (hne n)
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [Units.isEmbedding_val₀.isInducing.tendsto_nhds_iff]
    have hlim : Filter.Tendsto a Filter.atTop (nhds (0 : L)) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).comp (Filter.tendsto_add_atTop_nat 1)
    have h1 : Filter.Tendsto (fun n : ℕ ↦ (1 : L) + a n) Filter.atTop (nhds (1 + 0)) := tendsto_const_nhds.add hlim
    rw [add_zero] at h1
    simpa only [Function.comp_def, u, Units.val_mk0, Units.val_one] using h1
  · intro n
    change ‖1 + a n‖ = 1
    have hlow : (1 : ℝ) ≤ max ‖1 + a n‖ ‖a n‖ := by
      have h := IsUltrametricDist.norm_add_le_max (1 + a n) (-(a n))
      simpa using h
    have hge : (1 : ℝ) ≤ ‖1 + a n‖ := by
      by_contra h
      rw [not_le] at h
      exact absurd (max_lt h (ha n)) (not_lt.mpr hlow)
    have hle : ‖1 + a n‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max (1 : L) (a n)).trans (max_le norm_one.le (ha n).le)
    linarith
  · intro n h
    exact pow_ne_zero _ (norm_pos_iff.mp hpos) (add_eq_left.mp (congrArg Units.val h))


/-- The idele with a unit of norm one at one finite place and 1 elsewhere has idele norm one. -/
private theorem ideleNorm_ofAdicCompletion_of_norm_one (v : V) (u : (v.adicCompletion F)ˣ)
    (hu : ‖(u : v.adicCompletion F)‖ = 1) :
    ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = 1 := by
  classical
  let g := IdeleGroup.ofAdicCompletion (𝓞 F) F v u
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm F g : ℝ≥0) : ℝ) = 1
  rw [((ideleNorm_spec F).1 g).2]
  change (∏ w : InfinitePlace F, ‖(1 : w.Completion)‖ ^ w.mult) *
    ∏ᶠ w, ‖RestrictedProduct.mulSingle (fun w : V ↦ w.adicCompletionIntegers F) v u.val w‖ =
    ((1 : ℝ≥0ˣ) : ℝ)
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul, Units.val_one, NNReal.coe_one]
  rw [finprod_eq_single _ v]
  · rw [RestrictedProduct.mulSingle_eq_same]
    exact hu
  · intro w hw
    rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hw, norm_one]

/-- Inserting a finite completion into the idele group is continuous. -/
private theorem continuous_ideleGroup_ofAdicCompletion (v : V) :
    Continuous (IdeleGroup.ofAdicCompletion (𝓞 F) F v) := by
  classical
  apply Continuous.units_map
  apply continuous_const.prodMk
  apply continuous_restrictedProduct_of_uniform
  · intro w
    exact (continuous_apply w).comp (continuous_mulSingle (A := fun u : V ↦ u.adicCompletion F) v)
  · filter_upwards [Filter.eventually_cofinite_ne v] with w hw x
    change Pi.mulSingle v x w ∈ w.adicCompletionIntegers F
    rw [Pi.mulSingle_eq_of_ne hw]
    exact (w.adicCompletionIntegers F).one_mem

/-- The single-place insertion is injective. -/
private theorem ofAdicCompletion_injective (v : V) {x : (v.adicCompletion F)ˣ}
    (hx : IdeleGroup.ofAdicCompletion (𝓞 F) F v x = 1) : x = 1 := by
  have hv := congrArg (fun d : I𝔽 ↦ d.val.2 v) hx
  have hcoord : (IdeleGroup.ofAdicCompletion (𝓞 F) F v x).val.2 v = x.val := by
    change RestrictedProduct.mulSingle (fun w : V ↦ w.adicCompletionIntegers F) v x.val v = x.val
    exact RestrictedProduct.mulSingle_eq_same ..
  rw [hcoord] at hv
  simp at hv
  exact Units.val_eq_one.mp hv


open scoped Valued in
/-- The norm-one ideles have no isolated point: a sequence of principal units at one
finite place gives ideles of norm one tending to one but never equal to it. -/
private theorem nhdsNE_neBot_normOne (v : V) : Filter.NeBot (nhdsWithin (1 : N𝔽) {1}ᶜ) := by
  classical
  obtain ⟨u, hu_tend, hu_norm, hu_ne⟩ := local_principalUnits (L := v.adicCompletion F)
  have hcont : Continuous (IdeleGroup.ofAdicCompletion (𝓞 F) F v) :=
    continuous_ideleGroup_ofAdicCompletion v
  let φ (n : ℕ) : N𝔽 :=
    ⟨IdeleGroup.ofAdicCompletion (𝓞 F) F v (u n), by
      rw [MonoidHom.mem_ker]
      exact ideleNorm_ofAdicCompletion_of_norm_one v (u n) (hu_norm n)⟩
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_frequently, Filter.frequently_iff]
  intro U hU
  rw [show nhds (1 : N𝔽) = (nhds (1 : I𝔽)).comap (Subtype.val : N𝔽 → I𝔽) from nhds_induced _ _] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
  have hpre : (IdeleGroup.ofAdicCompletion (𝓞 F) F v) ⁻¹' W ∈ nhds (1 : (v.adicCompletion F)ˣ) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hW)
  obtain ⟨n, hn⟩ := (hu_tend.eventually hpre).exists
  refine ⟨φ n, hWU hn, ?_⟩
  intro hEq
  have h1 : u n = 1 := by
    apply ofAdicCompletion_injective v
    exact congrArg Subtype.val hEq
  exact hu_ne n h1


/-- The norm-one Tamagawa measure gives measure zero to singletons. -/
private theorem normOneIdeleTamagawaMeasure_nullSingleton (v : V) :
    NullSingletonClass (normOneIdeleTamagawaMeasure F) := by
  have htop : IsTopologicalGroup I𝔽 := (ideleGroup_topology F).2.2.1
  have hcl : IsClosed ((ideleNorm F).ker : Set I𝔽) := (ideleGroup_topology F).2.2.2.2.2
  let : IsTopologicalGroup I𝔽 := htop
  let : LocallyCompactSpace I𝔽 := (ideleGroup_topology F).2.1
  let : T2Space I𝔽 := (ideleGroup_topology F).1
  let : LocallyCompactSpace N𝔽 := hcl.locallyCompactSpace
  let : BorelSpace I𝔽 := ⟨rfl⟩
  let : BorelSpace N𝔽 := ⟨by rw [borel_comap]; rfl⟩
  let : (normOneIdeleTamagawaMeasure F).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  have hbot : Filter.NeBot (nhdsWithin (1 : N𝔽) {1}ᶜ) := nhdsNE_neBot_normOne v
  exact MeasureTheory.Measure.IsHaarMeasure.nullSingletonClass _


/-- A number field has a finite place. -/
private theorem finitePlace_nonempty (F : Type*) [Field F] [NumberField F] :
    Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨m, hm.isPrime, NeZero.ne m⟩⟩

/-- Paper: (11.3.2.2), p. 495. The displayed weight vanishes everywhere.
For each principal multiplier, the first translated section condition forces
the integration variable into a single Haar-null point.
Deviation: The printed weight cannot implement a normalized indentation. -/
theorem orbitalSectionWeight_eq_zero (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) (xy : I𝔽 × I𝔽) :
    orbitalSectionWeight E τ xy = 0 := by
  classical
  have hτ : RightInverse τ (ideleNorm F) := _hτ
  obtain ⟨v⟩ := finitePlace_nonempty F
  haveI hns : NullSingletonClass (normOneIdeleTamagawaMeasure F) :=
    normOneIdeleTamagawaMeasure_nullSingleton v
  have hprincipal (ξ : Fˣ) : ideleNorm F (principal ξ) = 1 := by
    have h : principal ξ ∈ (ideleNorm F).ker := (ideleNorm_spec F).2 ⟨ξ, rfl⟩
    simpa using h
  have hterm : ∀ ξ : Fˣ, ∫ g in E,
      (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
        (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2)
        ∂normOneIdeleTamagawaMeasure F = 0 := by
    intro ξ
    let g₀ : N𝔽 := ⟨(principal ξ)⁻¹ * τ (ideleNorm F xy.1) * (xy.1)⁻¹, by
      rw [MonoidHom.mem_ker]
      have hτ' : ∀ t : ℝ≥0ˣ, ideleNorm F (τ t) = t := hτ
      simp only [map_mul, map_inv, hprincipal, hτ', inv_one, one_mul]
      simp⟩
    have hsupp : ∀ᵐ g ∂(normOneIdeleTamagawaMeasure F |>.restrict E),
        (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
          (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2) = 0 := by
      filter_upwards [Measure.ae_ne (normOneIdeleTamagawaMeasure F |>.restrict E) g₀]
        with g hg
      by_cases h1 : principal ξ * g.val * xy.1 ∈ Set.range τ
      · exfalso
        apply hg
        obtain ⟨t, ht⟩ := h1
        have hg1 : ideleNorm F (g : I𝔽) = 1 := MonoidHom.mem_ker.mp g.property
        have hnorm : t = ideleNorm F xy.1 := by
          have h := congrArg (ideleNorm F) ht
          rw [hτ] at h
          simp only [map_mul, hprincipal, hg1, one_mul] at h
          exact h
        have hg' : g.val = (principal ξ)⁻¹ * τ t * (xy.1)⁻¹ := by
          rw [ht]
          group
        apply Subtype.ext
        rw [hg', hnorm]
      · rw [Set.indicator_of_notMem h1, zero_mul]
    rw [integral_eq_zero_of_ae hsupp]
  unfold orbitalSectionWeight
  simp [hterm]

/-- Paper: (11.3.2.1) and (11.3.2.3)–(11.3.2.4), pp. 495–496.
The printed weight gives a zero skew-diagonal integral for any kernel,
including when the cutoff and further indicators are absorbed into it. -/
theorem orbitalSectionWeight_skewIntegral_eq_zero (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) (K : I𝔽 × I𝔽 → ℂ) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
      let xy := (τ t, principal ξ * g.val * τ t)
      (orbitalSectionWeight E τ xy : ℂ) * K xy
      ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) = 0 := by
  simp [orbitalSectionWeight_eq_zero E τ _hτ]

-- TODO(paper-gap): Theorem 11.3.2.1 (11.3.2.1) cannot use the weight (11.3.2.2).
-- A normalized lift and a shell-by-shell identification with the trace operator
-- are missing. The total skew-diagonal formula of §12.2 does not give these.
-- TODO(paper-gap): The proof of (11.3.2.3)–(11.3.2.5) gives no support bound for
-- a repaired lift, and the original primary indicators cut out the new place
-- once that place enters the index. A separate tail based at S′ and proof of the
-- cutoff limit on the global Paley–Wiener subquotients are needed.

end OrbitalTraces

end RiemannMasullo
