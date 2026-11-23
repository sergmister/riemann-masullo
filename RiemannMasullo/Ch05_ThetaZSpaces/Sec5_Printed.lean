module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Chapter 5.5: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding results are in `Sec5.lean` and the errata are recorded in `ERRATA.md`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing

/-- Paper: Lemma 5.5.2.1, (5.5.2.3), p. 280.
As printed: evaluation at zero and Fourier evaluation at zero on the global theta
quotient are the normalized eigendistributions of weights one and the idelic norm,
respectively. `globalThetaPolarValues_eq_eigendistributions` includes the values on the
standard Gaussian as scalar factors. See ERRATA F65. -/
def Printed.globalThetaPolarValues_eq_eigendistributions : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (x : GlobalAdelicThetaSpace F),
    let C := IdeleClassGroup (𝓞 F) F
    globalThetaPolarValues (F := F) x =
      (globalThetaEigendistribution (F := F) (1 : QuasiCharacter C) x,
        globalThetaEigendistribution (F := F) (ideleClassNormTwist (1 : PontryaginDual C) 1) x)

/-- At a field with one complex place, the Gaussian already contradicts the first coordinate. -/
private theorem globalThetaPolarValues_gaussian_contradiction (F : Type) [Field F] [NumberField F]
    (hF : InfinitePlace.nrComplexPlaces F = 1)
    (hall : Printed.globalThetaPolarValues_eq_eigendistributions) : False := by
  let χ : PontryaginDual (IdeleClassGroup (𝓞 F) F) := 1
  let f := adelicStandardGaussian χ
  let q := (LinearMap.ker (adelicThetaLinearMap F)).mkQL
  have h := congrArg Prod.fst (hall F (q f))
  have hp := congrArg Prod.fst (globalThetaPolarValues_mk f)
  have he := globalThetaEigendistribution_mk (F := F) 1 f
  have ht : ideleClassNormTwist χ 0 = 1 := by
    ext g
    change (1 : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 : ℂ) = 1
    simp
  have hn := adelicNormalizedEigendistribution_gaussian (F := F) χ 0
  rw [ht] at hn
  have hval : f (Multiplicative.ofAdd 0) = (1 : ℂ) := hp.symm.trans (h.trans (he.trans hn))
  have hzero := adelicStandardGaussian_trivial_zero (F := F)
  rw [hF, pow_one] at hzero
  have hinv : (2 * (Real.pi : ℂ))⁻¹ = 1 := hzero.symm.trans hval
  have heq := inv_eq_one.mp hinv
  have hre : 2 * Real.pi = 1 := by exact_mod_cast heq
  linarith [Real.pi_gt_three]

/-- Paper: Lemma 5.5.2.1, (5.5.2.3), p. 280.
Take `F = ℚ(i)` and the theta class of the trivial-character standard adelic Gaussian
`E`. The complex Gaussian factor is `(2π)⁻¹ exp(−2π|z|²)`, and the finite factors are
the integer-ring indicators. Both normalized eigendistributions take value `1` on the
class. Evaluation at zero gives `1/(2π)`. Fourier evaluation at zero gives `1/(4π)`,
since the complex integral against `2 dx dy` is `1/(2π)` and the finite integer rings
have product additive mass `1/2`. -/
theorem Printed.globalThetaPolarValues_eq_eigendistributions_false :
    ¬ Printed.globalThetaPolarValues_eq_eigendistributions := by
  let F := CyclotomicField 4 ℚ
  have : NeZero (4 : ℕ) := ⟨by decide⟩
  have : IsCyclotomicExtension {4} ℚ F := by
    convert CyclotomicField.isCyclotomicExtension 4 ℚ
    exact Subsingleton.elim _ _
  have : NumberField F := IsCyclotomicExtension.numberField {4} ℚ F
  apply globalThetaPolarValues_gaussian_contradiction F
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4) F]
  decide

/-- Paper: Remark 5.5.3.3, p. 285.
As printed: if the weights range over a connected set containing an interval with
nonempty one-dimensional interior, the corresponding eigendistributions have trivial
joint kernel on the ordinary S-local theta quotient. An interval is expressed by a
nondegenerate real segment in a complex norm coordinate. The declaration
`sLocalThetaEigendistributions_separate_of_accumulation` tests every norm chart.
See ERRATA F67. -/
def Printed.sLocalThetaEigendistributions_separate_of_interval : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let J := SIdeleQuotient F S
    ∀ (W : Set (QuasiCharacter J)), IsConnected W →
      (∃ (χ : PontryaginDual J) (a b : ℂ), a ≠ b ∧
        let chart := quasiCharacterNormTwist (G := J) (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous
          ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
        chart '' segment ℝ a b ⊆ W) →
      ∀ x : SLocalAdelicThetaSpace F S,
        (∀ c ∈ W, sLocalThetaEigendistribution c x = 0) → x = 0

/-- A rational number is integral in the completion at `v` exactly when the prime of `v`
does not divide its denominator. -/
private theorem sLocalThetaEigendistributions_separate_of_interval_false_integral (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) :
    algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ ↔
      ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ x.den := by
  have : Fact (Rat.HeightOneSpectrum.primesEquiv v).1.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    ((Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).le_one_iff_le_one),
    Rat.padicValuation_le_one_iff]

/-- A rational S-integer for `S = {v}` that is integral at `v` has denominator one. -/
private theorem sLocalThetaEigendistributions_separate_of_interval_false_den (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ)
    (hx : x ∈ ({v} : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)
    (hv : ¬ (Rat.HeightOneSpectrum.primesEquiv v).1 ∣ x.den) : x.den = 1 := by
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  let w := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩
  have hw : (Rat.HeightOneSpectrum.primesEquiv w).1 = q :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩)
  by_cases hwv : w = v
  · exact hv (hwv ▸ hw ▸ hqd)
  · have h1 : w.valuation ℚ x ≤ 1 := hx w hwv
    have : Fact (Rat.HeightOneSpectrum.primesEquiv w).1.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv w).2⟩
    rw [(Rat.HeightOneSpectrum.valuation_equiv_padicValuation w).le_one_iff_le_one,
      Rat.padicValuation_le_one_iff, hw] at h1
    exact h1 hqd


open scoped ContDiff in
/-- An archimedean test with value one at one that vanishes at every rational at
distance at least `1/2` from one. -/
private theorem sLocalThetaEigendistributions_separate_of_interval_false_arch :
    ∃ fA : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)),
      fA (Multiplicative.ofAdd 1) = 1 ∧
      ∀ ξ : ℚ, fA (Multiplicative.ofAdd (algebraMap ℚ (InfiniteAdeleRing ℚ) ξ)) ≠ 0 →
        |(ξ : ℝ) - 1| < 1 / 2 := by
  classical
  let c := InfiniteAdeleRing.ringEquiv_mixedSpace ℚ 1
  let b : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let bC : mixedEmbedding.mixedSpace ℚ → ℂ := fun y ↦ (b y : ℂ)
  have hsupp : HasCompactSupport bC := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hsmooth : ContDiff ℝ (∞) bC := Complex.ofRealCLM.contDiff.comp b.contDiff
  let G := hsupp.toSchwartzMap hsmooth
  have hG : (fun x : Multiplicative (InfiniteAdeleRing ℚ) ↦
      G (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.toAdd)) ∈
      schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing ℚ)) :=
    (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
      (fun x ↦ G (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x))).mpr ⟨G, fun _ ↦ rfl⟩
  refine ⟨⟨_, hG⟩, ?_, fun ξ hξ ↦ ?_⟩
  · change ((b c : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num)), Complex.ofReal_one]
  · have hs : InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (algebraMap ℚ (InfiniteAdeleRing ℚ) ξ) ∈
        Function.support b := fun h0 ↦ hξ (by
          change ((b _ : ℝ) : ℂ) = 0
          exact (congrArg (fun r : ℝ ↦ (r : ℂ)) h0).trans Complex.ofReal_zero)
    have hc : c = InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (algebraMap ℚ (InfiniteAdeleRing ℚ) 1) := by
      rw [map_one]
    rw [b.support_eq, Metric.mem_ball, dist_eq_norm] at hs
    change _ < 1 / 2 at hs
    rw [hc, ← map_sub, ← map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp] at hs
    let w : {w : InfinitePlace ℚ // w.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
    have h1 := (norm_le_pi_norm (mixedEmbedding ℚ (ξ - 1)).1 w).trans (norm_fst_le _)
    rw [mixedEmbedding.mixedEmbedding_apply_isReal, eq_ratCast, Real.norm_eq_abs] at h1
    push_cast at h1
    exact h1.trans_lt hs

/-- The indicator of `1 + 5𝒪` at a finite place of `ℚ`. -/
private theorem sLocalThetaEigendistributions_separate_of_interval_false_fin
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ g : SchwartzBruhat (Multiplicative (w.adicCompletion ℚ)), ∀ y : w.adicCompletion ℚ,
      g (Multiplicative.ofAdd y) =
        (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)).indicator (fun _ ↦ 1)
          ((5 : w.adicCompletion ℚ)⁻¹ * (y - 1)) := by
  have : LocallyCompactSpace (Multiplicative (w.adicCompletion ℚ)) :=
    locallyCompactSpace_adicCompletion (K := ℚ) w
  have h5 : (5 : w.adicCompletion ℚ) ≠ 0 := by
    simpa using (map_ne_zero (algebraMap ℚ (w.adicCompletion ℚ))).mpr (by norm_num : (5 : ℚ) ≠ 0)
  refine ⟨schwartzBruhatTranslate (Multiplicative.ofAdd (1 : w.adicCompletion ℚ))
    (schwartzBruhatUnitTranslate (Units.mk0 5 h5) (finiteStandardGaussian w 1)), fun y ↦ ?_⟩
  change finiteStandardGaussianValue w 1
    (((Units.mk0 (5 : w.adicCompletion ℚ) h5)⁻¹ : (w.adicCompletion ℚ)ˣ) * (-1 + y)) = _
  rw [finiteStandardGaussianValue]
  split_ifs with hc
  · rw [neg_add_eq_sub, Units.val_inv_eq_inv_val, Units.val_mk0]
  · exact absurd (fun _ _ ↦ rfl) hc

/-- An S-integer whose twisted 5-adic coordinate lies in `1 + 5𝒪` and whose real coordinate
is near one is one. -/
private theorem sLocalThetaEigendistributions_separate_of_interval_false_term
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (Rat.HeightOneSpectrum.primesEquiv v).1 = 5)
    (ξ : ℚ) (hξ : ξ ∈ ({v} : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)
    (hreal : |(ξ : ℝ) - 1| < 1 / 2) (ε : ℚ) (hε : ε = 1 ∨ ε = -1)
    (hmem : (5 : v.adicCompletion ℚ)⁻¹ * (algebraMap ℚ (v.adicCompletion ℚ) (ε * ξ) - 1) ∈
      v.adicCompletionIntegers ℚ) :
    ξ = 1 ∧ ε = 1 := by
  have ht : (5 : v.adicCompletion ℚ)⁻¹ * (algebraMap ℚ (v.adicCompletion ℚ) (ε * ξ) - 1) =
      algebraMap ℚ (v.adicCompletion ℚ) ((ε * ξ - 1) / 5) := by
    rw [map_div₀, map_sub, map_one, map_ofNat, div_eq_inv_mul]
  rw [ht] at hmem
  have hint : algebraMap ℚ (v.adicCompletion ℚ) (ε * ξ) ∈ v.adicCompletionIntegers ℚ := by
    have h5 : (5 : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
      simp
    have : ε * ξ = 5 * ((ε * ξ - 1) / 5) + 1 := by ring
    rw [this, map_add, map_mul, map_ofNat, map_one]
    exact add_mem (mul_mem h5 hmem) (one_mem _)
  rw [sLocalThetaEigendistributions_separate_of_interval_false_integral, hv] at hint hmem
  have hεξ : ε * ξ ∈ ({v} : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ := by
    rcases hε with rfl | rfl
    · simpa using hξ
    · simpa using neg_mem hξ
  have hden := sLocalThetaEigendistributions_separate_of_interval_false_den v (ε * ξ) hεξ (hv ▸ hint)
  have hden' : ξ.den = 1 := by rcases hε with rfl | rfl <;> simpa using hden
  have hξ1 : ξ = 1 := by
    have hn : ξ = (ξ.num : ℚ) := ((Rat.den_eq_one_iff ξ).mp hden').symm
    rw [hn] at hreal ⊢
    push_cast at hreal
    rw [abs_lt] at hreal
    have h2 : ξ.num < 2 := by exact_mod_cast (show (ξ.num : ℝ) < 2 by linarith)
    have h0 : 0 < ξ.num := by exact_mod_cast (show (0 : ℝ) < ξ.num by linarith)
    have : ξ.num = 1 := by omega
    rw [this]; rfl
  refine ⟨hξ1, ?_⟩
  rcases hε with rfl | rfl
  · rfl
  · exfalso
    subst hξ1
    exact hmem (by norm_num)

/-- Norm twists of a fixed quasi-character along a segment form a connected set. -/
private theorem sLocalThetaEigendistributions_separate_of_interval_false_connected
    {G : Type*} [CommGroup G] [TopologicalSpace G] (m : G →* NNRealˣ) (hm : Continuous m)
    (c : QuasiCharacter G) (a b : ℂ) :
    IsConnected ((fun s ↦ quasiCharacterNormTwist m hm c s) '' segment ℝ a b) := by
  refine ((convex_segment a b).isConnected ⟨a, left_mem_segment ℝ a b⟩).image _
    (Continuous.continuousOn ?_)
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous fun p : ℂ × G ↦ c p.2 * (((m p.2 : NNReal) : ℝ) : ℂ) ^ p.1
  refine (c.continuous.comp continuous_snd).mul (Continuous.cpow ?_ continuous_fst ?_)
  · exact Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (hm.comp continuous_snd)))
  · intro p
    exact Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))

open scoped TensorProduct in
/-- Paper: Remark 5.5.3.3, p. 285.
Take `F = ℚ`, `S = {∞, 5}`, and let `W` be the image of the real segment `[2,3]`
in the norm chart of the trivial character. Tensor an even smooth real bump equal to
one at `±1` and supported in `1/2 < |x| < 3/2` with the quadratic character modulo `5`
on `ℤ₅ˣ`, extended by zero. At the identity only the S-units `±1` contribute to
theta, giving value two. The norm-one idele `(1, 2)` acts by negation on the test
and its theta class. Every weight in `W` takes value one on that idele, so each
corresponding eigendistribution kills the class. -/
theorem Printed.sLocalThetaEigendistributions_separate_of_interval_false :
    ¬ Printed.sLocalThetaEigendistributions_separate_of_interval := by
  -- Same `S` and `W`, with a simpler test: an archimedean bump at one tensored with the
  -- indicator of `1 + 5ℤ₅`, and the norm-one idele `(1, -1)` in place of `(1, 2)`. The class
  -- of `h - (1, -1) • h` is killed by every weight in `W`, and its theta function is one at
  -- the identity, since `1` is the only S-unit near one that is `≡ 1 mod 5`.
  intro hall
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨5, Nat.prime_five⟩
  have hv : (Rat.HeightOneSpectrum.primesEquiv v).1 = 5 :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply _)
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v}
  let w₀ : S := ⟨v, Finset.mem_singleton_self v⟩
  have hS (w : S) : w = w₀ := Subtype.ext (Finset.mem_singleton.mp w.2)
  have hA := sLocalThetaEigendistributions_separate_of_interval_false_arch
  let fA := hA.choose
  have hfA1 : fA (Multiplicative.ofAdd 1) = 1 := hA.choose_spec.1
  have hfA := hA.choose_spec.2
  have hF := fun w ↦ sLocalThetaEigendistributions_separate_of_interval_false_fin w
  let g := fun w : S ↦ (hF w.val).choose
  have hg (w : S) := (hF w.val).choose_spec
  have hE := sAdeleSchwartz_inductiveTensor_equiv ℚ S
  let h := hE.choose (fA ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))
  let ind := fun y : v.adicCompletion ℚ ↦
    (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator (fun _ ↦ (1 : ℂ))
      ((5 : v.adicCompletion ℚ)⁻¹ * (y - 1))
  have hval (y : SAdeleRing ℚ S) :
      h (Multiplicative.ofAdd y) = fA (Multiplicative.ofAdd y.1) * ind (y.2 w₀) := by
    rw [hE.choose_spec fA g y, Fintype.prod_eq_single w₀ (fun w hw ↦ absurd (hS w) hw), hg w₀]
  let u : (SAdeleRing ℚ S)ˣ := ⟨(1, -1), (1, -1), by ext <;> simp, by ext <;> simp⟩
  let f := h - schwartzBruhatUnitTranslate u h
  have hfval (y : SAdeleRing ℚ S) : f (Multiplicative.ofAdd y) =
      fA (Multiplicative.ofAdd y.1) * ind (y.2 w₀) -
        fA (Multiplicative.ofAdd y.1) * ind (-y.2 w₀) := by
    change h (Multiplicative.ofAdd y) - h (Multiplicative.ofAdd ((1, -1) * y)) = _
    rw [hval, hval]
    simp
  let x : SLocalAdelicThetaSpace ℚ S := Submodule.Quotient.mk f
  let chart := quasiCharacterNormTwist (G := SIdeleQuotient ℚ S) (sIdeleQuotientNorm ℚ S)
    (isProperMap_sIdeleQuotientNorm ℚ S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp 1)
  have hnorm : sIdeleNorm ℚ S u = 1 := by
    apply Units.ext
    simp [sIdeleNorm, u]
    exact nnNorm_one
  have hc (s : ℂ) : chart s (QuotientGroup.mk u) = 1 := by
    change ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp 1) (QuotientGroup.mk u) *
      (((sIdeleQuotientNorm ℚ S (QuotientGroup.mk u) : NNReal) : ℝ) : ℂ) ^ s = 1
    rw [sIdeleQuotientNorm_mk, hnorm]
    simp
  have hker (s : ℂ) : sLocalThetaEigendistribution (chart s) x = 0 := by
    have hmem : sLocalNormalizedEigendistribution (chart s) ∈
        sLocalEigendistributions (chart s) := by
      rw [sLocalEigendistributions_eq_span]
      exact Submodule.mem_span_singleton_self _
    have h1 := (mem_sLocalEigendistributions _ _).mp hmem u h
    change sLocalNormalizedEigendistribution (chart s) (h - schwartzBruhatUnitTranslate u h) = 0
    rw [map_sub, h1, hc, one_mul, sub_self]
  have hSv : (S : Set (HeightOneSpectrum (𝓞 ℚ))) = {v} := Finset.coe_singleton v
  have hind (q : ℚ) (hq : q ∈ ({v} : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)
      (hreal : |(q : ℝ) - 1| < 1 / 2) (ε : ℚ) (hε : ε = 1 ∨ ε = -1) (hne : ¬ (q = 1 ∧ ε = 1)) :
      ind (algebraMap ℚ (v.adicCompletion ℚ) (ε * q)) = 0 :=
    Set.indicator_of_notMem (fun hm ↦ hne
      (sLocalThetaEigendistributions_separate_of_interval_false_term v hv q hq hreal ε hε hm)) _
  have hterm (ξ : ((S : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ) (y : SAdeleRing ℚ S)
      (hy1 : y.1 = algebraMap ℚ (InfiniteAdeleRing ℚ) ξ.val.val)
      (hy2 : y.2 w₀ = algebraMap ℚ (v.adicCompletion ℚ) ξ.val.val) :
      f (Multiplicative.ofAdd y) = if ξ = 1 then 1 else 0 := by
    have hq : ξ.val.val ∈ ({v} : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ :=
      hSv ▸ ξ.val.2
    have hξ1 : ξ = 1 ↔ ξ.val.val = 1 :=
      ⟨fun h ↦ by rw [h]; rfl, fun h ↦ Units.ext (Subtype.ext h)⟩
    rw [hfval, hy1, hy2]
    have hneg : -algebraMap ℚ (v.adicCompletion ℚ) ξ.val.val =
        algebraMap ℚ (v.adicCompletion ℚ) ((-1) * ξ.val.val) := by simp
    have hpos : algebraMap ℚ (v.adicCompletion ℚ) ξ.val.val =
        algebraMap ℚ (v.adicCompletion ℚ) (1 * ξ.val.val) := by simp
    by_cases hA0 : fA (Multiplicative.ofAdd
        (algebraMap ℚ (InfiniteAdeleRing ℚ) ξ.val.val)) = 0
    · have h : ¬ ξ = 1 := fun h ↦ by
        rw [hξ1.mp h, map_one, hfA1] at hA0
        exact one_ne_zero hA0
      rw [hA0, zero_mul, zero_mul, sub_zero]
      simp [h]
    · have hreal := hfA _ hA0
      rw [hneg, hind _ hq hreal (-1) (Or.inr rfl) (by norm_num), mul_zero, sub_zero]
      by_cases h : ξ = 1
      · rw [hξ1.mp h, map_one, hfA1, one_mul, map_one]
        simp [ind, h]
      · rw [hpos, hind _ hq hreal 1 (Or.inl rfl) (fun h' ↦ h (hξ1.mpr h'.1)), mul_zero]
        simp [h]
  have hx : x ≠ 0 := by
    intro h0
    have hk := LinearMap.mem_ker.mp ((Submodule.Quotient.mk_eq_zero _).mp h0)
    have h1 := congrArg (fun φ : C((SAdeleRing ℚ S)ˣ, ℂ) ↦ φ 1) hk
    simp only [sLocalAdelicTheta_apply, ContinuousMap.zero_apply] at h1
    rw [tsum_eq_single 1 ?_] at h1
    · rw [mul_one, hterm 1 _ rfl rfl] at h1
      simp at h1
    · intro ξ hξ
      rw [mul_one, hterm ξ _ rfl rfl]
      simp [hξ]
  exact hx (hall ℚ S _ (sLocalThetaEigendistributions_separate_of_interval_false_connected _ _ _ 2 3)
    ⟨1, 2, 3, by norm_num, subset_rfl⟩ x (by rintro c ⟨s, -, rfl⟩; exact hker s))


/-- Paper: §6.3.2, following (6.3.2.2), p. 304. As printed: the two polar evaluations on
the global theta quotient equal the normalized eigendistributions of weights one and the
idelic norm. This repeats (5.5.2.3), which is `Printed.globalThetaPolarValues_eq_eigendistributions`
above; the same counterexample refutes both. See `globalThetaPolarValues_eq_eigendistributions`
and ERRATA F77. -/
def Printed.globalConverse_polarValues_eq_eigendistributions : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (x : GlobalAdelicThetaSpace F),
    globalThetaPolarValues (F := F) x =
      (globalThetaEigendistribution (F := F) 1 x,
        globalThetaEigendistribution (ideleClassNormTwist
          (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 1) x)

/-- Paper: §6.3.2, following (6.3.2.2), p. 304. Take F = ℚ(i) and the class of the trivial
standard Gaussian E. Both normalized generators take value 1 there. The complex factor is
`(2π)⁻¹ exp(-2π|z|²)`, so E(0) = (2π)⁻¹. Its complex integral against `2 dx dy` is also
`(2π)⁻¹`, and the product of the finite integer-ring masses is 1/2. The Fourier evaluation
is therefore `(4π)⁻¹`. -/
theorem Printed.globalConverse_polarValues_eq_eigendistributions_false :
    ¬ Printed.globalConverse_polarValues_eq_eigendistributions :=
  Printed.globalThetaPolarValues_eq_eigendistributions_false

end RiemannMasullo
