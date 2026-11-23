module

public import RiemannMasullo.Ch01_Introduction.Sec4
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHecke

/-!
# From the idelic zero statement to the Comparator targets

Section 1.4.5, p. 30, locates the zeros of the completed idelic Hecke L-function.
This file states the classical comparisons with the Mathlib L-functions and
deduces the seven target statements. The comparisons are supplementary to §1.4.
-/

@[expose] public noncomputable section

open Filter NumberField Set
open scoped BigOperators Topology

namespace RiemannMasullo

section Hecke

variable {K : Type*} [Field K] [NumberField K]

local notation "U[" K "]" => PontryaginDual (IdeleClassGroup (𝓞 K) K)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- A unitary Mathlib Hecke character takes values in the unit circle and hence
defines a character in the Pontryagin dual of the same idele class group. -/
def unitaryHeckeCharacterToPontryaginDual (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x, ‖χ x‖ = 1) : U[K] :=
  ⟨{ toFun := fun x ↦ ⟨χ x, mem_sphere_zero_iff_norm.2 (hχ x)⟩
     map_one' := Circle.ext χ.map_one
     map_mul' := fun x y ↦ Circle.ext (χ.map_mul x y) }, χ.continuous.subtype_mk _⟩

/-- Viewed as a complex-valued character via the zero norm twist, the
circle-valued character recovers the original Mathlib character. -/
theorem ideleClassNormTwist_unitaryHeckeCharacter_zero (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x, ‖χ x‖ = 1) :
    ideleClassNormTwist (unitaryHeckeCharacterToPontryaginDual χ hχ) 0 = χ := by
  ext1 x
  change χ x * (_ : ℂ) ^ (0 : ℂ) = χ x
  rw [Complex.cpow_zero, mul_one]

/-- The finite idelic Hecke L-function agrees with Mathlib's Hecke L-series
on the half-plane of absolute convergence. -/
theorem finiteHeckeL_unitaryHeckeCharacter (χ : HeckeCharacter (𝓞 K) K)
    (hχ : ∀ x, ‖χ x‖ = 1) (s : halfPlane) :
    finiteHeckeL (unitaryHeckeCharacterToPontryaginDual χ hχ) s = χ.LSeries s := by
  unfold finiteHeckeL
  rw [ideleClassNormTwist_unitaryHeckeCharacter_zero]

/-- Two meromorphic functions agreeing to the right of one have the same
meromorphic germ at every point, expressed as equality on a punctured neighborhood. -/
theorem meromorphicContinuation_eventuallyEq {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) (s : ℂ) : f =ᶠ[𝓝[≠] s] g := by
  have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hzero : meromorphicOrderAt (f - g) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr <|
      (hnear.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  have hs := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ s) hzero
  exact (meromorphicOrderAt_eq_top_iff.mp hs).mono fun _ hz ↦ sub_eq_zero.mp hz

/-- The archimedean factor is holomorphic and nonvanishing in the positive
half-plane, so every meromorphic continuation of the finite L-function has
the same order there as the continued completed L-function. -/
theorem meromorphicOrderAt_finiteHeckeL_continuation (χ : U[K]) {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (h : ∀ s : halfPlane, f s = finiteHeckeL χ s)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt f s = meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
  let L := continuedCompletedHeckeL χ
  have hL := (completedHeckeL_exists_continuation χ).choose_spec
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  have hG : Differentiable ℂ G := differentiable_inv_heckeGammaFactor χ
  have hm : MeromorphicOn (fun z ↦ G z * L z) univ :=
    fun z hz ↦ (hG.analyticAt z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have he := meromorphicContinuation_eventuallyEq hf hm (fun z hz ↦ by
    rw [h ⟨z, hz⟩]
    change finiteHeckeL χ ⟨z, hz⟩ = (heckeGammaFactor χ z)⁻¹ * continuedCompletedHeckeL χ z
    rw [show continuedCompletedHeckeL χ z = completedHeckeL χ ⟨z, hz⟩ from hL.2 ⟨z, hz⟩]
    exact (inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)) _).symm) s
  rw [meromorphicOrderAt_congr he]
  exact meromorphicOrderAt_mul_of_ne_zero (hG.analyticAt s) (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs))

/-- Paper: §1.4.5, p. 30. Every zero in the open critical strip of any
meromorphic continuation of a unitary Hecke L-series lies on the critical line.
Deviation: The target uses Mathlib's finite Hecke series and positive meromorphic order. -/
theorem heckeLFunction_zeros_re :
    ∀ (K : Type) [Field K] [NumberField K] (χ : HeckeCharacter (𝓞 K) K), (∀ x, ‖χ x‖ = 1) →
      ∀ f : ℂ → ℂ, MeromorphicOn f Set.univ → (∀ s : ℂ, 1 < s.re → f s = χ.LSeries s) →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < meromorphicOrderAt f s → s.re = 1 / 2 := by
  intro K _ _ χ hχ f hf h s hs₀ hs₁ hz
  let ψ := unitaryHeckeCharacterToPontryaginDual χ hχ
  rw [meromorphicOrderAt_finiteHeckeL_continuation ψ hf
    (fun z ↦ (h z z.property).trans (finiteHeckeL_unitaryHeckeCharacter χ hχ z).symm) hs₀] at hz
  exact heckeL_zero_re_eq_half ψ s hs₀ hs₁ hz

/-- The finite L-function of the trivial idelic character is the Dedekind
zeta series on the convergence half-plane. -/
theorem finiteHeckeL_one_eq_dedekindZeta (s : halfPlane) :
    finiteHeckeL (1 : U[K]) s = dedekindZeta K s := by
  have he := completedHeckeL_one_eq_dedekindZeta (F := K) s
  rw [← heckeGammaFactor_one] at he
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[K])
    (zero_lt_one.trans s.property)) he

/-- Specializing the idelic claim to the trivial character places the
critical-strip zeros of any meromorphic continuation of Dedekind zeta on the critical line. -/
theorem dedekindZeta_zeros_re :
    ∀ (K : Type) [Field K] [NumberField K] (f : ℂ → ℂ),
      MeromorphicOn f Set.univ → (∀ s : ℂ, 1 < s.re → f s = dedekindZeta K s) →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < meromorphicOrderAt f s → s.re = 1 / 2 := by
  intro K _ _ f hf h s hs₀ hs₁ hz
  rw [meromorphicOrderAt_finiteHeckeL_continuation (1 : U[K]) hf
    (fun z ↦ (h z z.property).trans (finiteHeckeL_one_eq_dedekindZeta (K := K) z).symm) hs₀] at hz
  exact heckeL_zero_re_eq_half (1 : U[K]) s hs₀ hs₁ hz

end Hecke

section Rational

/-- Mathlib's Dirichlet L-function is meromorphic on the whole plane. -/
theorem meromorphic_dirichletLFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    MeromorphicOn (DirichletCharacter.LFunction χ) univ := by
  rcases eq_or_ne χ 1 with rfl | hχ
  · intro s _
    have ha := (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).analyticAt s
    have hm : MeromorphicAt (fun z : ℂ ↦ DirichletCharacter.LFunctionTrivChar₁ N z / (z - 1)) s :=
      ha.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
    apply hm.congr
    filter_upwards [(eventually_cofinite_ne (1 : ℂ)).filter_mono (nhdsNE_le_cofinite s)] with z hz
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz)
  · exact fun s _ ↦ ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s).meromorphicAt

/-- Over the rational field, the Dedekind zeta series agrees with Riemann
zeta on the half-plane of absolute convergence. -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta ℚ s = riemannZeta s := by
  have hc (n : ℕ) : Nat.card {I : Ideal (𝓞 ℚ) // I.absNorm = n} = 1 := by
    let : Unique {I : Ideal (𝓞 ℚ) // I.absNorm = n} :=
      { default := ⟨_, RatRingOfIntegers.absNorm_span_natCast n⟩
        uniq := fun I ↦ by
          apply Subtype.ext
          obtain ⟨m, hm⟩ := RatRingOfIntegers.exists_eq_span_natCast I.val
          have hmn : m = n := by simpa only [hm, RatRingOfIntegers.absNorm_span_natCast] using I.property
          simpa only [hmn] using hm }
    exact Nat.card_unique
  simpa only [dedekindZeta, hc, Nat.cast_one, Pi.one_def] using LSeries_one_eq_riemannZeta hs

/-- Riemann zeta zeros away from the negative even integers and the point one
lie on the critical line. The Dedekind specialization over the rationals handles
the open strip, and Mathlib classifies the zeros outside it. -/
theorem riemannZeta_eq_zero_re :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 := by
  intro s hz htriv hs
  have hs₀ : 0 < s.re := lt_of_not_ge fun h ↦ htriv ((riemannZeta_eq_zero_iff_of_re_nonpos h).mp hz)
  have hs₁ : s.re < 1 := lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using meromorphic_dirichletLFunction
      (1 : DirichletCharacter ℂ 1)
  have ha := analyticOn_riemannZeta s hs
  exact dedekindZeta_zeros_re ℚ riemannZeta hm (fun z hz ↦ (dedekindZeta_rat_eq_riemannZeta hz).symm)
    s hs₀ hs₁ (lt_of_le_of_ne ha.meromorphicOrderAt_nonneg fun h ↦
      ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h.symm hz)

/-- The Riemann hypothesis in the form used by Mathlib. -/
theorem riemannHypothesis :
    ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2 :=
  riemannZeta_eq_zero_re

open IsDedekindDomain.HeightOneSpectrum NumberFieldKB.Chebotarev.RatIdele WithZero in
/-- A unit residue class trivial modulo N/p is realized by an idele supported at p.
Its natural representative is a p-adic unit, and has residue one at every other
prime power dividing N. -/
private theorem rationalDirichletLift_unitResidue {N : ℕ} [NeZero N] (v : Pl)
    (hpN : pr v ∣ N) (a : (ZMod N)ˣ)
    (ha : a ∈ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)).ker) :
    ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v u.val = 1 ∧
      (resMod N).toHomUnits (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = a := by
  let n := (a.val : ZMod N).val
  have hn : (n : ZMod N) = a.val := ZMod.natCast_zmod_val _
  have hcop := (ZMod.isUnit_iff_coprime n N).mp (hn ▸ a.isUnit)
  have hval : Valued.v (n : v.adicCompletion ℚ) = 1 := by
    rw [← Rat.cast_natCast, valued_ratCast,
      show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) by simp,
      valuation_of_algebraMap, intValuation_eq_one_iff, natCast_mem_asIdeal_iff]
    exact (pr_prime v).coprime_iff_not_dvd.mp (hcop.symm.coprime_dvd_left hpN)
  let u := Units.mk0 (n : v.adicCompletion ℚ) (fun h ↦ by simp [h] at hval)
  let x := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u
  have hrat : ratPart x = 1 := by
    rw [ratPart_ofAdicCompletion v u 0 (by simpa [u] using hval), zpow_zero]
  have hunit : unitPart x = x := by simp [unitPart_apply, hrat]
  refine ⟨u, hval, Units.ext ?_⟩
  change resMod N x = a.val
  apply (ZMod.equivPi N (NeZero.ne N)).injective
  rw [resMod_apply, resModFun, RingEquiv.apply_symm_apply, ← hn, map_natCast]
  funext q
  change redP q.val _ (N.factorization q) (compV (placeP N q) (unitPart x)).val = (n : ZMod _)
  rw [hunit]
  by_cases he : placeP N q = v
  · subst v
    rw [compV_ofAdicCompletion_self]
    exact redP_natCast n
  · rw [compV_ofAdicCompletion_ne he, Units.val_one, redP_one]
    have hne : q.val ≠ pr v := by
      intro h
      exact he ((eq_placeOf_iff v q.val (Nat.prime_of_mem_primeFactors q.property)).2 h.symm).symm
    have hcop' : q.val.Coprime (pr v) :=
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactors q.property) (pr_prime v)).mpr hne
    have hdiv : q.val ^ N.factorization q.val ∣ N / pr v :=
      (Nat.dvd_div_iff_mul_dvd hpN).mpr
        ((hcop'.pow_left _).symm.mul_dvd_of_dvd_of_dvd hpN (Nat.ordProj_dvd N q.val))
    have hred : (n : ZMod (N / pr v)) = 1 := by
      have h := congrArg Units.val (MonoidHom.mem_ker.mp ha)
      change ZMod.castHom (Nat.div_dvd_of_dvd hpN) _ a.val = 1 at h
      simpa only [← hn, map_natCast] using h
    simpa only [map_one, map_natCast] using
      (congrArg (ZMod.castHom hdiv (ZMod (q.val ^ N.factorization q.val))) hred).symm

open NumberFieldKB.Chebotarev.RatIdele in
/-- At a conductor prime, triviality on local units would force descent to N/p. -/
private theorem rationalDirichletLift_ramified {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (η : HeckeCharacter (𝓞 ℚ) ℚ) (v : Pl) (hpN : pr v ∣ N)
    (hres : ∀ u : (v.adicCompletion ℚ)ˣ, η.restrict v u.val =
      (ideleChar N χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂ)) :
    ¬η.IsUnramifiedAt v := by
  intro hU
  have hd := Nat.div_dvd_of_dvd hpN
  have hf : χ.FactorsThrough (N / pr v) := by
    apply (χ.factorsThrough_iff_ker_unitsMap hd).mpr
    intro a ha
    obtain ⟨u, hu, hr⟩ := rationalDirichletLift_unitResidue v hpN a ha
    have h := hU.restrict_apply_eq_one u.val hu
    rw [hres, coe_ideleChar, hr, inv_eq_one] at h
    exact MonoidHom.mem_ker.mpr (Units.ext h)
  have hdiv := χ.conductor_dvd_of_mem_conductorSet hf
  rw [show χ.conductor = N from hχ] at hdiv
  have hpos := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hpN) (pr_prime v).pos
  exact (Nat.not_le_of_gt (Nat.div_lt_self (NeZero.pos N) (pr_prime v).one_lt))
    (Nat.le_of_dvd hpos hdiv)

open IsDedekindDomain.HeightOneSpectrum NumberFieldKB.Chebotarev.RatIdele WithZero in
/-- Away from the modulus, the uniformizer has the original Dirichlet character value. -/
private theorem rationalDirichletLift_unramified {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (η : HeckeCharacter (𝓞 ℚ) ℚ) (v : Pl) (hc : (pr v).Coprime N)
    (hres : ∀ u : (v.adicCompletion ℚ)ˣ, η.restrict v u.val =
      (ideleChar N χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂ)) :
    η.IsUnramifiedAt v ∧ η.localValue v = χ (pr v) := by
  have hU : η.IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro t
    let u := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom t
    have ht : Valued.v u.val = 1 := adicCompletionIntegers.isUnit_iff_valued_eq_one.mp t.isUnit
    change η.restrict v u.val = 1
    rw [hres, ideleChar_unit N χ hc u ht, Units.val_one]
  refine ⟨hU, ?_⟩
  have hv : Valued.v (pr v : v.adicCompletion ℚ) = exp (-1) := by
    simpa only [Rat.cast_natCast, eq_self, ↓reduceIte] using valued_prime v (pr_prime v)
  have hπ : Valued.v.IsUniformizer (pr v : v.adicCompletion ℚ) := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range ⟨_, hv⟩]
    exact hv
  let π := Units.mk0 (pr v : v.adicCompletion ℚ) hπ.ne_zero
  rw [hU.localValue_eq _ hπ]
  exact (hres π).trans (ideleChar_uniformizer N χ hc π hv)

open NumberFieldKB.Chebotarev.RatIdele in
/-- A primitive Dirichlet character has a finite-order idelic character over
the rationals whose finite Hecke L-function agrees with its Dirichlet series. -/
theorem DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (_hχ : χ.IsPrimitive) :
    ∃ ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ), IsOfFinOrder ψ ∧
      ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s := by
  let η : HeckeCharacter (𝓞 ℚ) ℚ :=
    ⟨(Units.coeHom ℂ).comp (ratDirichletChar N χ).toMonoidHom,
      Units.continuous_val.comp (ratDirichletChar N χ).continuous⟩
  have hpow (g) : η g ^ orderOf χ = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    change ((ideleChar N χ x : ℂˣ) : ℂ) ^ orderOf χ = 1
    have h := congrArg (fun f : IdQ →* ℂˣ ↦ (f x : ℂ))
      (ideleChar_pow_eq_one N χ (pow_orderOf_eq_one χ))
    simpa only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply,
      Units.val_one] using h
  have hu (g) : ‖η g‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (hpow g) χ.orderOf_pos.ne'
  let ψ := unitaryHeckeCharacterToPontryaginDual η hu
  refine ⟨ψ, isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf χ, χ.orderOf_pos, ?_⟩, ?_⟩
  · ext1 g
    exact (ContinuousMonoidHom.pow_apply (ψ : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* Circle)
      (orderOf χ) g).trans (Circle.ext (hpow g))
  intro s hs
  have hres (v : Pl) (u : (v.adicCompletion ℚ)ˣ) : η.restrict v u.val =
      (ideleChar N χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  have h := (e.hasProd_iff).mpr (χ.LSeries_eulerProduct_hasProd hs)
  apply (finiteHeckeL_hasProd ψ ⟨s, hs⟩).unique
  apply h.congr_fun
  intro v
  change finiteHeckeEulerFactor ψ v s = (1 - χ (pr v) * (pr v : ℂ) ^ (-s))⁻¹
  rw [finiteHeckeEulerFactor, show ideleClassNormTwist ψ 0 = η from
    ideleClassNormTwist_unitaryHeckeCharacter_zero η hu, absNorm_asIdeal]
  by_cases hc : (pr v).Coprime N
  · obtain ⟨hU, hv⟩ := rationalDirichletLift_unramified χ η v hc (hres v)
    rw [ite_eq_left hU, hv]
  · have hpN := not_not.mp (mt (pr_prime v).coprime_iff_not_dvd.mpr hc)
    rw [ite_eq_right (rationalDirichletLift_ramified _hχ η v hpN (hres v)),
      χ.map_nonunit (mt (ZMod.isUnit_iff_coprime _ _).mp hc)]
    simp

/-- For a primitive Dirichlet character, all zeros in the open critical strip
lie on the critical line by comparison with its finite Hecke L-function. -/
theorem LFunction_eq_zero_re_of_isPrimitive :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 := by
  intro N _ χ hχ s hs₀ hs₁ hz
  obtain ⟨ψ, _, hψ⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq hχ
  have hs : s ≠ 1 := fun h ↦ by simp [h] at hs₁
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun z hz ↦
    (DirichletCharacter.differentiableAt_LFunction χ z (.inl hz)).differentiableWithinAt
  have ha := hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)
  have hz' := lt_of_le_of_ne ha.meromorphicOrderAt_nonneg fun h ↦
    ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h.symm hz
  rw [meromorphicOrderAt_finiteHeckeL_continuation ψ (meromorphic_dirichletLFunction χ)
    (fun z ↦ (DirichletCharacter.LFunction_eq_LSeries χ z.property).trans (hψ z z.property).symm)
    hs₀] at hz'
  exact heckeL_zero_re_eq_half ψ s hs₀ hs₁ hz'

/-- A zero of a factor inserted when raising the modulus of a Dirichlet
character has real part zero. -/
theorem dirichletEulerFactor_zero_re_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hz : 1 - χ p * (p : ℂ) ^ (-s) = 0) : s.re = 0 := by
  have he := (sub_eq_zero.mp hz).symm
  have hc : χ (p : ZMod N) ≠ 0 := fun hc ↦ by simp [hc] at he
  have hu := MulChar.apply_ne_zero_iff.mp hc
  have hn : ‖χ (p : ZMod N)‖ = 1 := χ.unit_norm_eq_one hu.unit
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow := congrArg norm he
  rw [norm_mul, hn, one_mul, norm_one, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hp₁), Complex.neg_re] at hpow
  have hneg := (Real.rpow_right_inj (zero_lt_one.trans hp₁) hp₁.ne').mp
    (hpow.trans (Real.rpow_zero (p : ℝ)).symm)
  exact neg_eq_zero.mp hneg

/-- The omitted Euler factors of an imprimitive character have no zeros in
the open critical strip. The zeros there lie on the critical line. -/
theorem LFunction_eq_zero_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 := by
  intro N _ χ s hs₀ hs₁ hz
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hs : s ≠ 1 := fun h ↦ by simp [h] at hs₁
  rw [← χ.changeLevel_primitiveCharacter,
    DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (.inr hs)] at hz
  obtain h | h := mul_eq_zero.mp hz
  · exact LFunction_eq_zero_re_of_isPrimitive _ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      s hs₀ hs₁ h
  · obtain ⟨p, hp, he⟩ := Finset.prod_eq_zero_iff.mp h
    exact (hs₀.ne' (dirichletEulerFactor_zero_re_eq_zero χ.primitiveCharacter
      (Nat.prime_of_mem_primeFactors hp) he)).elim

/-- Dirichlet L-functions are nonzero to the right of the critical line,
with the principal pole at one excluded. Mathlib handles real parts at least one. -/
theorem LFunction_ne_zero_of_half_lt_re :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 := by
  intro N _ χ s hs hχ
  obtain h | h := lt_or_ge s.re 1
  · exact fun hz ↦ hs.ne' (LFunction_eq_zero_re N χ s (lt_trans (by norm_num) hs) h hz)
  · exact χ.LFunction_ne_zero_of_one_le_re hχ h

end Rational

end RiemannMasullo
