module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec5
import all RiemannMasullo.Ch03_IdelicZeta.Sec2

/-! # False claims printed in §7.5 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option Elab.async false

local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "ω[" F ", " χ "]" => (χ : U[F]).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C[F])

/-- Paper: Theorem 7.5.0.1, p. 374.
The printed quotient map is a topological linear isomorphism with a translation
difference for every selected finite place. -/
def Printed.strongCoprimality : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (S : Finset V[F])
    (π : (v : V[F]) → (v.adicCompletion F)ˣ),
    (∀ v ∈ S, Valuation.IsUniformizer
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) (π v).val) →
    let ω := ω[F, χ]
    let j := (exists_strongCoprimalityThetaEmbedding ω).choose
    let D := strongCoprimalityDenominator ω S
    let E := strongCoprimalityDifferenceRange ω S π
    ∃ e : (StrongCoprimalityThetaSpace ω ⧸ D) ≃L[ℂ] (StrongCoprimalityDecaySpace ω ⧸ E),
      ∀ x : StrongCoprimalityThetaSpace ω,
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (j x)

/-- Paper: Theorem 7.5.0.1, p. 374.
Over ℚ take the even quadratic character modulo 5, S = {(5)}, and the uniformizer 5.
In the splitting of the idele classes by the positive norm, this character has value
one on the uniformizer class. Its nontrivial restriction to the 5-adic units makes
the local unit average zero on this isotype. Weil principal value then acts as the
identity, giving a zero source quotient. The χ-weighted Haar integral annihilates the
printed difference and is nonzero on the product of the inverse compact character
with exp(−(log t)²) in the positive norm coordinate t. Thus the target is nonzero. -/
theorem Printed.strongCoprimality_false : ¬ Printed.strongCoprimality := by sorry

/-- Paper: Remark 7.5.0.2, p. 379.
The printed strong dual is a Hausdorff quotient of a closed subspace of a finite
locally convex sum of rapidly decreasing sequence spaces. -/
def Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ω : PontryaginDual (ideleClassNorm F).ker)
    (p : V[ℚ]),
    let S := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    ∃ n : ℕ, let E := Fin n → RapidDecaySequence 1
      ∃ (W : Submodule ℂ E) (D : Submodule ℂ W),
        IsClosed (W : Set E) ∧ IsClosed (D : Set W) ∧
          Nonempty (StrongDual ℂ (StrongCoprimalityQuotient ω S) ≃L[ℂ] (W ⧸ D))

/-- Paper: Remark 7.5.0.2, p. 379.
Over ℚ with trivial character and p = 2, the primary quotient is the smooth
periodic space for period log 2. Its Fourier sequence space has strong dual
consisting of polynomially growing sequences. This dual is meagre in itself:
the closed sets of sequences bounded by m(1 + |n|)^m, for m ≥ 1, cover it
and have empty interior. A closed subspace of a finite product of Schwartz
sequence spaces, quotiented by a closed subspace, is Fréchet and hence Baire. -/
theorem Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient_false :
    ¬ Printed.strongCoprimalityPrimaryQuotient_strongDual_subquotient := by sorry

/-- Paper: Theorem 7.5.0.1, proof, equation (7.5.0.8), p. 377.
At each reciprocal Euler zero for a place in the primary set S₀ = Sₚ of
p. 376, the zeroth reflected Fourier jet defines a continuous linear functional
on the full homogeneous theta space. This is the assertion at order zero.
Analyticity at the evaluation point
expresses ordinary evaluation of the meromorphic continuation there.
See `strongCoprimalityFourierJet_mk`, `exists_strongCoprimalityFourierJet_full`
and ERRATA F142. -/
def Printed.strongCoprimalityFourierJet_zero_full : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (p : V[ℚ]) (S : Finset V[F]),
    let S₀ := (finite_nuclearityPlacesAbove (F := F) p).toFinset
    S₀ ⊆ S → Subsingleton (CommRing.Pic ((S : Set V[F]).integer F)) →
      ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
      ∀ v ∈ S₀, ∀ s : ℂ, (finiteHeckeEulerFactor χ v s)⁻¹ = 0 →
        let ω := ω[F, χ]
        let q := (LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)).mkQ
        ∃ d : StrongDual ℂ (GlobalHomogeneousThetaSpace F ω),
          ∀ f : SchwartzBruhat (Multiplicative (𝔸[F])),
            let Z := fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
              (ideleClassNormTwist χ⁻¹ z)
            AnalyticAt ℂ Z (1 - s) ∧ d (q f) = Z (1 - s)

section

open Filter
open scoped Topology

local instance strongCoprimalityFourierJetFalseClassMeasurable : MeasurableSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := borel _
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[ℚ])
/-- The trivial character has value one on every local unit. -/
private theorem strongCoprimalityFourierJet_false_restrict_one (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).restrict v u = 1 := by
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  change (1 : ℂ) * _ ^ (0 : ℂ) = 1
  rw [Complex.cpow_zero, mul_one]
/-- The trivial character is unramified at every finite place. -/
private theorem strongCoprimalityFourierJet_false_unramified (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).IsUnramifiedAt v := by
  rw [HeckeCharacter.isUnramifiedAt_iff]
  intro u
  exact strongCoprimalityFourierJet_false_restrict_one v (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom u)
/-- At exponent zero, the reciprocal Euler factor of the trivial character vanishes. -/
private theorem strongCoprimalityFourierJet_false_euler (v : HeightOneSpectrum (𝓞 ℚ)) :
    (finiteHeckeEulerFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) v 0)⁻¹ = 0 := by
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion ℚ)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv : (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0).localValue v = 1 := strongCoprimalityFourierJet_false_restrict_one v u
  simp [finiteHeckeEulerFactor, strongCoprimalityFourierJet_false_unramified v, hv]
/-- A test nonzero at zero gives a reflected Fourier zeta function that is not analytic at one. -/
private theorem strongCoprimalityFourierJet_false_nonanalytic (f : SchwartzBruhat (Multiplicative (𝔸[ℚ]))) (hf : f zeroAdele ≠ 0) :
    ¬ AnalyticAt ℂ (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)) 1 := by
  intro ha
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hm : (ν univ).toReal ≠ 0 := by
    exact (ENNReal.toReal_pos (isOpen_univ.measure_pos ν Set.univ_nonempty).ne'
      isCompact_univ.measure_lt_top.ne).ne'
  have hc : ContinuousAt (fun s : ℂ ↦ globalIdelicZFunction f
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) s)) 0 := by
    have ha' : ContinuousAt (fun z ↦ globalIdelicZFunction (adeleSchwartzFourier f)
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)) (1 - 0) := by
      simpa using ha.continuousAt
    have h := ha'.comp (by fun_prop : ContinuousAt (fun s : ℂ ↦ 1 - s) 0)
    have heq : (fun s : ℂ ↦ globalIdelicZFunction f
        (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) s)) =
        (fun s : ℂ ↦ globalIdelicZFunction (adeleSchwartzFourier f)
          (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) (1 - s))) := by
      funext s
      rw [globalIdelicZFunction_functionalEquation, dualQuasiCharacter_ideleClassNormTwist, inv_one]
    rw [heq]
    exact h
  have ht : Tendsto (fun s : ℂ ↦ s * globalIdelicZFunction f
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) s))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Pi.mul_apply, id_eq, zero_mul] using
      (continuousAt_id.tendsto.mul hc.tendsto).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have he := tendsto_nhds_unique ht (globalIdelicZFunction_residue_zero f)
  exact (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hm)) hf) he.symm
/-- Paper: Theorem 7.5.0.1, proof, equation (7.5.0.8), p. 377.
Take F = ℚ, χ = 1, the rational prime 2, and s = 0. Enlarge the primary
set S₀ to a finite set S with trivial S-ideal class group. The reciprocal
Euler factor vanishes at zero. If the reflected Fourier zeta function of
the standard adelic Gaussian were analytic at one, the functional equation
would make its original zeta function continuous at zero. Its nonzero
residue there contradicts this continuity. -/
theorem Printed.strongCoprimalityFourierJet_zero_full_false :
    ¬ Printed.strongCoprimalityFourierJet_zero_full := by
  intro h
  classical
  let p : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  let S₀ := (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset
  let T := (eventually_trivial_sIdealClassGroup (F := ℚ)).choose
  let S := T ∪ S₀
  have hS : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)) :=
    (eventually_trivial_sIdealClassGroup (F := ℚ)).choose_spec S Finset.subset_union_left
  have hp : p ∈ S₀ := by
    change p ∈ (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    apply HeightOneSpectrum.ext
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) p.asIdeal = p.asIdeal
    have he : algebraMap (𝓞 ℚ) (𝓞 ℚ) = RingHom.id _ := by
      ext x
      simp
    rw [he, Ideal.comap_id]
  have hu : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) 0 ∈
      unramifiedOutside ℚ S := fun v _ ↦ strongCoprimalityFourierJet_false_unramified v
  have hd := h ℚ 1 p S Finset.subset_union_right hS hu p hp 0 (strongCoprimalityFourierJet_false_euler p)
  let f := adelicStandardGaussian (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
  have hf : f zeroAdele ≠ 0 := by
    change adelicStandardGaussian _ (Multiplicative.ofAdd 0) ≠ 0
    rw [adelicStandardGaussian_trivial_zero]
    exact pow_ne_zero _ (inv_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  apply strongCoprimalityFourierJet_false_nonanalytic f hf
  simpa only [inv_one, sub_zero] using (hd.choose_spec f).1

end

end RiemannMasullo
