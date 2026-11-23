module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Local and global converse theorems

Masullo, §6.3, pp. 302–310. Finite sets in the S-local notation specify the
finite places. The S-local Euler product always includes all infinite places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual C𝔽
local notation "C₁" => (ideleClassNorm F).ker
local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0
local notation "χ₁(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "normChartₛ(" χ ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F _)
  (isProperMap_sIdeleQuotientNorm F _).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

-- Equation (6.3.1.1) uses `ideleClassNormTwist` from §3.2.

/-- At a place where a Hecke character is unramified, its value on a local unit is the value on
a given uniformizer raised to the valuation exponent, and the norm is the same power of the
norm of the uniformizer. -/
private theorem unramifiedHeckeCharacter_existsUnique_phase_local
    (c : HeckeCharacter (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F))
    (hc : c.IsUnramifiedAt v) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) (x : (v.adicCompletion F)ˣ) :
    ∃ n : ℤ, finitePlaceRestriction F v c x = finitePlaceRestriction F v c π ^ n ∧
      ‖(x : v.adicCompletion F)‖ = ‖(π : v.adicCompletion F)‖ ^ n := by
  have hval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  set k := WithZero.log (Valued.v (x : v.adicCompletion F))
  let y : (v.adicCompletion F)ˣ := x * π ^ k
  have hv : Valued.v (y : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hval,
      ← WithZero.exp_zsmul]
    conv_lhs => rw [← WithZero.exp_log hx0]
    rw [← WithZero.exp_add]
    simp [k]
  have hxy : x = y * π ^ (-k) := by simp [y]
  have hy : finitePlaceRestriction F v c y = 1 := by
    have := hc.restrict_apply_eq_one (y : v.adicCompletion F) hv
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at this
    exact this
  refine ⟨-k, ?_, ?_⟩
  · rw [hxy, map_mul, map_zpow, hy, one_mul]
  · have hn : ‖(y : v.adicCompletion F)‖ = 1 := by
      rw [FinitePlace.norm_def, hv, map_one, NNReal.coe_one]
    rw [hxy, Units.val_mul, norm_mul, hn, one_mul, Units.val_zpow_eq_zpow_val, norm_zpow]

/-- Paper: Equations (6.3.1.2)–(6.3.1.3), p. 303.
At an unramified place a uniformizer determines a unique local phase in the chosen
half-open period. Every norm twist of the local character is then the indicated norm power.
Deviation: The phase is specified by exponentiating the logarithm identity with the
chosen period. The logarithm is of the uniformizer value. -/
theorem unramifiedHeckeCharacter_existsUnique_phase (χ : U) (v : V)
    (hχ : χ₀(χ).IsUnramifiedAt v) (π : (v.adicCompletion F)ˣ)
    (_hπ : Valued.v.IsUniformizer π.val) :
    ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi / Real.log (q(v) : ℝ)) ∧
      finitePlaceRestriction F v χ₀(χ) π = (q(v) : ℂ) ^ (-(t : ℂ) * Complex.I) ∧
      ∀ (s : ℂ) (x : (v.adicCompletion F)ˣ),
        finitePlaceRestriction F v (ideleClassNormTwist χ s) x =
          ((‖x.val‖ : ℝ) : ℂ) ^ (s + (t : ℂ) * Complex.I) := by
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq1).ne'
  set ℓ := Real.log (q : ℝ) with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos hq1
  have hP : 0 < 2 * Real.pi / ℓ := div_pos Real.two_pi_pos hℓ
  set a := finitePlaceRestriction F v (ideleClassNormTwist χ 0) π with hadef
  have htwist (s : ℂ) (x : (v.adicCompletion F)ˣ) :
      finitePlaceRestriction F v (ideleClassNormTwist χ s) x =
        (χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x) : ℂ) *
          ((‖x.val‖ : ℝ) : ℂ) ^ s := by
    change (χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x) : ℂ) *
      (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x) : ℝ≥0) : ℝ) : ℂ) ^ s =
        _
    rw [ideleClassNorm_ofAdicCompletion]
    rfl
  have hχ0 (x : (v.adicCompletion F)ˣ) : finitePlaceRestriction F v (ideleClassNormTwist χ 0) x =
      (χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x) : ℂ) := by
    rw [htwist, Complex.cpow_zero, mul_one]
  have ha1 : ‖a‖ = 1 := by rw [hadef, hχ0]; exact Circle.norm_coe _
  have hlog : Complex.log (q : ℂ) = (ℓ : ℂ) := by rw [hℓdef, Complex.natCast_log]
  have hcpow (t : ℝ) : (q : ℂ) ^ (-(t : ℂ) * Complex.I) =
      Complex.exp (((-t * ℓ : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hq0, hlog]
    congr 1
    push_cast
    ring
  -- existence of the phase
  set t₀ : ℝ := -Complex.arg a / ℓ
  set t : ℝ := toIcoMod hP 0 t₀
  have ht : t ∈ Ico 0 (2 * Real.pi / ℓ) := by simpa using toIcoMod_mem_Ico hP 0 t₀
  have hta : a = (q : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    rw [hcpow]
    have hm := toIcoMod_add_toIcoDiv_zsmul hP 0 t₀
    set m := toIcoDiv hP 0 t₀
    have : -t * ℓ = Complex.arg a + (m : ℝ) * (2 * Real.pi) := by
      have h1 : t = t₀ - m * (2 * Real.pi / ℓ) := by rw [zsmul_eq_mul] at hm; linarith
      rw [h1]
      simp only [t₀]
      field_simp
      ring
    rw [this]
    push_cast
    rw [add_mul, Complex.exp_add, show (m : ℂ) * (2 * Real.pi) * Complex.I =
      m * (2 * Real.pi * Complex.I) by ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a, ha1]
    simp
  refine ⟨t, ⟨ht, hta, fun s x ↦ ?_⟩, ?_⟩
  · obtain ⟨n, hn, hnorm⟩ := unramifiedHeckeCharacter_existsUnique_phase_local _ v hχ π _hπ x
    rw [norm_uniformizer_adicCompletion v _ _hπ] at hnorm
    rw [htwist, ← hχ0, hn]
    have hr : (0 : ℝ) < ((q : ℝ)⁻¹) ^ n := zpow_pos (inv_pos.mpr (zero_lt_one.trans hq1)) n
    rw [hnorm, Complex.cpow_add _ _ (by exact_mod_cast hr.ne'), mul_comm (_ ^ s)]
    congr 1
    rw [← hadef, hta, hcpow, ← Complex.exp_int_mul, ← hqdef,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
      ← Complex.ofReal_log hr.le, Real.log_zpow, Real.log_inv]
    congr 1
    push_cast
    rw [hlog]
    ring
  · rintro t' ⟨ht', hta', -⟩
    rw [hta, hcpow, hcpow, Complex.exp_eq_exp_iff_exists_int] at hta'
    obtain ⟨n, hn⟩ := hta'
    have h2 : (t' - t) * ℓ = n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simp at this
      linarith
    have hd : t' - t = n * (2 * Real.pi / ℓ) := by field_simp; linarith
    have hlt : (n : ℝ) * (2 * Real.pi / ℓ) < 1 * (2 * Real.pi / ℓ) := by
      rw [← hd]; linarith [ht.1, ht'.2]
    have hgt : (-1 : ℝ) * (2 * Real.pi / ℓ) < n * (2 * Real.pi / ℓ) := by
      rw [← hd]; linarith [ht.2, ht'.1]
    have h1 : (n : ℝ) < 1 := lt_of_mul_lt_mul_right hlt hP.le
    have h3 : (-1 : ℝ) < n := lt_of_mul_lt_mul_right hgt hP.le
    have : n = 0 := by
      have : n < 1 := by exact_mod_cast h1
      have : -1 < n := by exact_mod_cast h3
      omega
    subst this
    simp at hd
    linarith


/-- Paper: Equation (6.3.1.4), p. 303.
The reciprocal of the unramified Euler factor is the geometric denominator with
the local phase. Inversion expresses the formula through its poles. -/
theorem finiteHeckeEulerFactor_inv_eq_phase (χ : U) (v : V)
    (hχ : χ₀(χ).IsUnramifiedAt v) (t : ℝ)
    (ht : χ₀(χ).localValue v = (q(v) : ℂ) ^ (-(t : ℂ) * Complex.I)) (s : ℂ) :
    (finiteHeckeEulerFactor χ v s)⁻¹ = 1 - (q(v) : ℂ) ^ (-s - (t : ℂ) * Complex.I) := by
  classical
  have hq : (q(v) : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [finiteHeckeEulerFactor, ite_eq_left hχ, inv_inv, ht, ← Complex.cpow_add _ _ hq]
  ring_nf

-- The ramified and infinite factors are already given by `finiteHeckeEulerFactor`,
-- `realHeckeCharacter_parameters`, `complexHeckeCharacter_parameters` and `heckeGammaFactor`.
-- In Terminology 6.3.1.1 the descent is `sIdeleRestriction` from §3.1 and the
-- product (6.3.1.5) is `sLocalHeckeL` from §3.3.

private theorem sLocalHeckeL_poleOrder_eq_rightHalf {S : Finset V}
    (χ : PontryaginDual (SIdeleQuotient F S)) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z ↦ sLocalHeckeL (normChartₛ(χ) z)) s ∧
      sLocalHeckeL (normChartₛ(χ) s) ≠ 0 := by
  classical
  obtain ⟨η, h, hχ, -⟩ := sLocal_character_extension χ
  simp_rw [sLocalHeckeL_eq_partialEulerProduct χ η h hχ]
  have hΓ := heckeGammaFactor_ne_zero_of_re_pos η hs
  have haΓ : AnalyticAt ℂ (heckeGammaFactor η) s := by
    simpa only [Pi.inv_def, inv_inv] using
      (((differentiable_inv_heckeGammaFactor η).analyticAt s).inv (inv_ne_zero hΓ))
  have hfinite (v : V) : AnalyticAt ℂ (finiteHeckeEulerFactor η v) s ∧
      finiteHeckeEulerFactor η v s ≠ 0 := by
    by_cases hv : χ₀(η).IsUnramifiedAt v
    · have hq : 1 < (q(v) : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      have hq' : (q(v) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (HeightOneSpectrum.one_lt_absNorm v).ne_zero
      have hlt : ‖χ₀(η).localValue v * (q(v) : ℂ) ^ (-s)‖ < 1 := by
        rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
          ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq)]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq (by simpa using hs)
      have hn : 1 - χ₀(η).localValue v * (q(v) : ℂ) ^ (-s) ≠ 0 :=
        sub_ne_zero.mpr fun he ↦ hlt.ne (he ▸ norm_one)
      have hd : Differentiable ℂ (fun z : ℂ ↦ 1 - χ₀(η).localValue v * (q(v) : ℂ) ^ (-z)) :=
        (differentiable_const _).sub ((differentiable_const _).mul
          (differentiable_neg.const_cpow (Or.inl hq')))
      change AnalyticAt ℂ (fun z ↦ finiteHeckeEulerFactor η v z) s ∧ _
      simp only [finiteHeckeEulerFactor, ite_eq_left hv]
      exact ⟨(hd.analyticAt s).inv hn, inv_ne_zero hn⟩
    · change AnalyticAt ℂ (fun z ↦ finiteHeckeEulerFactor η v z) s ∧ _
      simp only [finiteHeckeEulerFactor, ite_eq_right hv]
      exact ⟨analyticAt_const, one_ne_zero⟩
  exact ⟨haΓ.mul (Finset.univ.analyticAt_fun_prod fun (v : S) _ ↦ (hfinite v.val).1),
    mul_ne_zero hΓ (Finset.prod_ne_zero_iff.mpr fun (v : S) _ ↦ (hfinite v.val).2)⟩

/-- Paper: Terminology 6.3.1.1, p. 303.
The S-local Hecke L-function and the local functional-equation factor have the
same poles with the same orders.
Deviation: This local comparison applies to every unitary character of the S-idèle quotient. -/
theorem sLocalHeckeL_poleOrder_eq (S : Finset V) (χ : PontryaginDual (SIdeleQuotient F S))
    (s : ℂ) :
    min 0 (meromorphicOrderAt (fun z ↦ sLocalHeckeL (normChartₛ(χ) z)) s) =
      min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (normChartₛ(χ) z)) s) := by
  let L (η : PontryaginDual (SIdeleQuotient F S)) (z : ℂ) := sLocalHeckeL (normChartₛ(η) z)
  by_cases hs : 0 < s.re
  · have hρ := sLocalRhoFactor_iteratedDeriv_analyticOn χ 0 s hs
    rw [iteratedDeriv_zero] at hρ
    rw [min_eq_left (sLocalHeckeL_poleOrder_eq_rightHalf χ hs).1.meromorphicOrderAt_nonneg,
      min_eq_left hρ.meromorphicOrderAt_nonneg]
  · have hs' : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    obtain ⟨ha, hn⟩ := sLocalHeckeL_poleOrder_eq_rightHalf χ⁻¹ hs'
    let D (z : ℂ) := L χ⁻¹ (1 - z)
    let ε (z : ℂ) := sLocalEpsilonFactor (normChartₛ(χ) z)
    have hD : AnalyticAt ℂ D s := ha.comp (show AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s by fun_prop)
    have hunit : AnalyticAt ℂ (ε / D) s := (sLocalEpsilonFactor_entire χ s trivial).div hD hn
    have hne : (ε / D) s ≠ 0 := div_ne_zero (sLocalEpsilonFactor_ne_zero _) hn
    have heq : (fun z ↦ sLocalRhoFactor (normChartₛ(χ) z)) =ᶠ[𝓝[≠] s] (ε / D) * L χ := by
      filter_upwards [nhdsNE_le_codiscrete s (sLocalRhoFactor_eq_epsilon_mul χ)] with z hz
      have hd : dualQuasiCharacter (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous (normChartₛ(χ) z) =
          normChartₛ(χ⁻¹) (1 - z) := by
        ext1 g
        let N : ℂ := (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ)
        have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr
          (NNReal.coe_ne_zero.mpr (sIdeleQuotientNorm F S g).ne_zero)
        change N * normChartₛ(χ) z g⁻¹ = _
        rw [map_inv]
        change N * ((χ g : ℂ) * N ^ z)⁻¹ = (χ g : ℂ)⁻¹ * N ^ (1 - z)
        rw [mul_inv_rev, Complex.cpow_sub 1 z hN, Complex.cpow_one, div_eq_mul_inv]
        ac_rfl
      dsimp only at hz
      rw [hd] at hz
      change sLocalRhoFactor (normChartₛ(χ) z) = ε z / D z * L χ z
      exact hz.trans (by change ε z * (L χ z / D z) = _; ring)
    rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul_of_ne_zero hunit hne]

/-- Paper: Terminology 6.3.1.1, p. 303.
The completed Hecke L-function on the norm chart is the meromorphic continuation
of the Euler product of §3.2. -/
abbrev continuedCompletedHeckeL (χ : U) : ℂ → ℂ :=
  (completedHeckeL_exists_continuation χ).choose

/-- Paper: Terminology 6.3.1.1, p. 303.
The continuation is in meromorphic normal form and recovers the completed Euler
product on the half-plane of absolute convergence. -/
theorem continuedCompletedHeckeL_spec (χ : U) :
    MeromorphicNFOn (continuedCompletedHeckeL χ) univ ∧
      ∀ s : halfPlane, continuedCompletedHeckeL χ s = completedHeckeL χ s :=
  (completedHeckeL_exists_continuation χ).choose_spec

/-- Paper: Equation (6.3.1.6), p. 303.
The product outside S divides the completed Hecke L-function by the S-local factor.
Deviation: Normal form fills in removable singularities of the quotient. Restriction and
this product are defined for every S outside which the character is unramified. -/
def heckeEulerProductOutside (S : Finset V) (χ : U)
    (hχ : χ₀(χ) ∈ unramifiedOutside F S) : ℂ → ℂ :=
  let twist := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous (sIdeleRestriction F S ⟨χ₀(χ), hχ⟩)
  toMeromorphicNFOn
    (fun s ↦ continuedCompletedHeckeL χ s / sLocalHeckeL (twist s)) univ

/-- The descended restriction of a unitary character is unitary. -/
private theorem heckeEulerProductOutside_eq_finite_unitary (S : Finset V) (χ : U)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S) :
    ∃ η : PontryaginDual (SIdeleQuotient F S),
      sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩ =
        quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
          (isProperMap_sIdeleQuotientNorm F S).continuous
          ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) 0 := by
  let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
  have hc (x : SIdeleQuotient F S) : ‖c x‖ = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [show c (QuotientGroup.mk g) = ideleClassNormTwist χ 0
      (QuotientGroup.mk (sIdeleInsertion F S g)) from sIdeleRestriction_mk F S _ g]
    change ‖(χ _ : ℂ) * _ ^ (0 : ℂ)‖ = 1
    simp
  let η : PontryaginDual (SIdeleQuotient F S) :=
    { toFun := fun x ↦ ⟨c x, mem_sphere_zero_iff_norm.mpr (hc x)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' x y := Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  refine ⟨η, ?_⟩
  ext x
  change c x = (η x : ℂ) * _ ^ (0 : ℂ)
  rw [Complex.cpow_zero, mul_one]
  rfl

/-- The descended local product consists of the archimedean and selected finite factors. -/
private theorem heckeEulerProductOutside_eq_finite_local_factor (S : Finset V) (χ : U)
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S) :
    ∀ s, sLocalHeckeL (quasiCharacterNormTwist (G := SIdeleQuotient F S)
      (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩) s) =
      heckeGammaFactor χ s * ∏ v : S, finiteHeckeEulerFactor χ v.val s := by
  obtain ⟨η, hη⟩ := heckeEulerProductOutside_eq_finite_unitary S χ hχ
  intro s
  have heq : quasiCharacterNormTwist (G := SIdeleQuotient F S)
      (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩) s =
      quasiCharacterNormTwist (G := SIdeleQuotient F S)
      (sIdeleQuotientNorm F S) (isProperMap_sIdeleQuotientNorm F S).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) s := by
    ext x
    have h := DFunLike.congr_fun hη x
    change _ = (η x : ℂ) * _ ^ (0 : ℂ) at h
    rw [Complex.cpow_zero, mul_one] at h
    change (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩) x *
      (((sIdeleQuotientNorm F S x : ℝ≥0) : ℝ) : ℂ) ^ s =
      (η x : ℂ) * (((sIdeleQuotientNorm F S x : ℝ≥0) : ℝ) : ℂ) ^ s
    rw [h]
  rw [heq]
  exact sLocalHeckeL_eq_partialEulerProduct η χ hχ hη s

/-- Meromorphic functions equal on a right half-plane have the same normal form. -/
private theorem heckeEulerProductOutside_eq_finite_nf_eq (f g : ℂ → ℂ) (hf : MeromorphicOn f univ)
    (hg : MeromorphicOn g univ) (hfg : ∀ z : ℂ, 1 < z.re → f z = g z) :
    toMeromorphicNFOn f univ = toMeromorphicNFOn g univ := by
  have hAtTwo : meromorphicOrderAt (f - g) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (hfg z hz)
  ext z
  have ho := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z) hAtTwo
  have hnear : f =ᶠ[𝓝[≠] z] g :=
    (meromorphicOrderAt_eq_top_iff.mp ho).mono fun _ h ↦ sub_eq_zero.mp h
  have hn : toMeromorphicNFOn f univ =ᶠ[𝓝[≠] z] toMeromorphicNFOn g univ :=
    (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).trans
      (hnear.trans (hg.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).symm)
  exact (((meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (meromorphicNFOn_toMeromorphicNFOn g univ (mem_univ z))).mp hn).eq_of_nhds


/-- Paper: Equation (6.3.1.6), p. 303.
The outside product equals the finite continuation with the finite factors in S removed,
as used in Appendix B.6. -/
theorem heckeEulerProductOutside_eq_finite (S : Finset V) (χ : U)
    (hχ : χ₀(χ) ∈ unramifiedOutside F S) (L : ℂ → ℂ)
    (_hL : MeromorphicNFOn L univ) (_hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    heckeEulerProductOutside S χ hχ = toMeromorphicNFOn
      (fun s ↦ reciprocalPartialHeckeEulerProduct χ S s * L s) univ := by
  classical
  have hfactor (v : V) : Differentiable ℂ (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) := by
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp_rw [inv_inv]
      have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
        ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
      exact (differentiable_const _).sub ((differentiable_const _).mul
        ((differentiable_neg).const_cpow (Or.inl hq)))
    · simp_rw [inv_one]
      exact differentiable_const _
  have hp : Differentiable ℂ (reciprocalPartialHeckeEulerProduct χ S) := by
    unfold reciprocalPartialHeckeEulerProduct
    exact Differentiable.fun_finsetProd fun v _ ↦ hfactor v
  have hlocal : MeromorphicOn (fun s ↦ sLocalHeckeL
      (quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous
        (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩) s)) univ := by
    simp_rw [heckeEulerProductOutside_eq_finite_local_factor S χ hχ]
    apply (meromorphic_heckeGammaFactor χ).meromorphicOn.mul
    apply MeromorphicOn.fun_prod
    intro v _ z _
    convert ((hfactor v.val).analyticAt z).meromorphicAt.inv using 1
    ext w
    simp
  unfold heckeEulerProductOutside
  apply heckeEulerProductOutside_eq_finite_nf_eq
  · exact (continuedCompletedHeckeL_spec χ).1.meromorphicOn.div hlocal
  · exact (fun z _ ↦ (hp.analyticAt z).meromorphicAt.mul (_hL.meromorphicOn z (mem_univ z)))
  · intro z hz
    rw [heckeEulerProductOutside_eq_finite_local_factor S χ hχ, (continuedCompletedHeckeL_spec χ).2 ⟨z, hz⟩,
      _hSeries ⟨z, hz⟩]
    change (heckeGammaFactor χ z * finiteHeckeL χ ⟨z, hz⟩) / _ = _
    have hn := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)
    have hprod : reciprocalPartialHeckeEulerProduct χ S z =
        (∏ v : S, finiteHeckeEulerFactor χ v.val z)⁻¹ := by
      unfold reciprocalPartialHeckeEulerProduct
      rw [← Finset.prod_coe_sort, Finset.prod_inv_distrib]
    rw [hprod]
    field_simp

section GlobalConverse

local notation "ℬ" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "P" => adelePolarSubspace F
local notation "Θ(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "K(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "Z(" f ", " χ ", " s ")" => globalIdelicZFunction f (ideleClassNormTwist χ s)
local notation "B" => SchwartzBergman (univ : Set ℝ)
local notation "bergmanIdeal(" G ")" =>
  {φ : B | ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = (G : ℂ → ℂ) s * u s}
local notation "shift(" t ")" => ((t : ℝ) : ℂ) * Complex.I
local notation "polePolynomial(" t ")" => (fun s : ℂ ↦ (s + shift(t)) * (1 - s - shift(t)))
local notation "regularizedL(" χ ", " t ")" =>
  toMeromorphicNFOn (fun s ↦ polePolynomial(t) s * continuedCompletedHeckeL χ s) univ
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])
local notation "mass" => ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- The rational adele ring is second countable, by its countable open cover. -/
private theorem homogeneousTheta_classMellin_rat_countable : SecondCountableTopology (Multiplicative 𝔸[ℚ]) := by
  let I := HeightOneSpectrum (𝓞 ℚ)
  let K (v : I) := v.adicCompletion ℚ
  let O (v : I) : Set (K v) := v.adicCompletionIntegers ℚ
  let : Countable I := Rat.HeightOneSpectrum.primesEquiv.injective.countable
  let (v : I) : SecondCountableTopology (K v) := by
    let p := Rat.HeightOneSpectrum.primesEquiv v
    let : Fact p.val.Prime := ⟨p.property⟩
    let : TopologicalSpace.SeparableSpace ℚ_[p.val] :=
      ⟨⟨range ((↑) : ℚ → ℚ_[p.val]), countable_range _, Padic.denseRange_ratCast _⟩⟩
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding
      |>.secondCountableTopology
  let Vset := fun s : Finset I ↦ {a : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v ∉ s, a v ∈ O v}
  have hopen (v : I) : IsOpen (O v) := Valued.isOpen_integer (K v)
  let (s : Finset I) : SecondCountableTopology (Vset s) := by
    have hs : Filter.cofinite ≤ Filter.principal (s : Set I)ᶜ :=
      Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have he := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := K) (A := O) hopen hs
    let : SecondCountableTopology (Πʳ v : I, [K v, O v]_[Filter.principal (s : Set I)ᶜ]) :=
      (RestrictedProduct.isEmbedding_coe_of_principal (R := K) (A := O)).secondCountableTopology
    have hrange : range (RestrictedProduct.inclusion K O hs) = Vset s := by
      rw [RestrictedProduct.range_inclusion]
      rfl
    exact hrange ▸ he.toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    refine TopologicalSpace.secondCountableTopology_of_countable_cover («U» := Vset)
      (fun _ ↦ RestrictedProduct.isOpen_forall_imp_mem hopen) (eq_univ_of_forall fun a ↦ ?_)
    have he := Filter.eventually_cofinite.mp a.2
    exact mem_iUnion.mpr ⟨he.toFinset, fun v hv ↦ by
      by_contra h
      exact hv (he.mem_toFinset.mpr h)⟩
  let (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  change SecondCountableTopology (((v : InfinitePlace ℚ) → v.Completion) × FiniteAdeleRing (𝓞 ℚ) ℚ)
  infer_instance


/-- Paper: Theorem 6.3.2.1(2), p. 304, following equation (6.3.2.6).
Integrating the homogeneous theta representative over the full class group
multiplies its component Mellin transform by the norm-one class mass.
Deviation: The component Mellin transform in (5.2.3.14) uses the norm-section
integral with dt/t. Dividing the displayed full class integral by the mass gives
that transform on its half-plane of absolute convergence. The same convention
applies after (6.3.2.22). -/
theorem homogeneousTheta_classMellin_eq_mass_mul (χ : U) (f : ℬ) (s : halfPlane) :
    let c := ideleClassNormTwist χ (s : ℂ)
    let integrand := fun g : C𝔽 ↦ homogeneousAdelicTheta χ₁(χ) f g * c g
    Integrable integrand (ideleClassTamagawaMeasure F) ∧
      (∫ g, integrand g ∂ideleClassTamagawaMeasure F) = mass * Z(f, χ, (s : ℂ)) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : SecondCountableTopology (Multiplicative 𝔸[ℚ]) := homogeneousTheta_classMellin_rat_countable
  obtain ⟨u, _, _⟩ := exists_adeleTrace_dualCoordinates F
  let : SecondCountableTopology 𝔸[F] := u.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : SecondCountableTopology 𝔸[F]ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (IdeleGroup (𝓞 F) F) := Units.isEmbedding_embedProduct.secondCountableTopology
  let : SecondCountableTopology C𝔽 := inferInstanceAs (SecondCountableTopology (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  let ν := normOneIdeleClassTamagawaMeasure F
  let μ := ideleClassTamagawaMeasure F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let ω : PontryaginDual C₁ := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
  let c := ideleClassNormTwist χ (s : ℂ)
  let W (g : C𝔽) := adelicTheta f g * c g
  let A (g : C𝔽) := homogeneousAdelicTheta ω f g * c g
  let Φ (p : C𝔽 × C₁) := W (p.2.val * p.1)
  have hc : c ∈ relativeRightHalfPlane (ideleClassNorm F) (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 1 := by
    change 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F) ideleClassNorm_ne_one c
    rw [quasiCharacterAbscissa_ideleClassNormTwist]
    exact s.property
  have hi : Integrable W μ := globalThetaMellinIntegral_integrable f c hc
  have hP : AEStronglyMeasurable Φ (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    exact ((adelicTheta f).continuous.mul c.continuous).comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have hp : Integrable Φ (μ.prod ν) := by
    apply (integrable_prod_iff' hP).mpr
    constructor
    · filter_upwards with u
      change Integrable (fun g ↦ W (u.val * g)) μ
      have hm : Measure.map (fun g : C𝔽 ↦ u.val * g) μ = μ := map_mul_left_eq_self μ u.val
      have hw : AEStronglyMeasurable W (Measure.map (fun g : C𝔽 ↦ u.val * g) μ) := by
        rw [hm]; exact hi.aestronglyMeasurable
      have hi' : Integrable W (Measure.map (fun g : C𝔽 ↦ u.val * g) μ) := by rw [hm]; exact hi
      have h := (integrable_map_measure hw ((continuous_const.mul continuous_id).measurable.aemeasurable)).mp hi'
      exact h
    · have he : (fun u : C₁ ↦ ∫ g, ‖Φ (g,u)‖ ∂μ) = fun _ ↦ ∫ g, ‖W g‖ ∂μ := by
        funext u
        change (∫ g, ‖W (u.val * g)‖ ∂μ) = _
        exact integral_mul_left_eq_self (fun g ↦ ‖W g‖) u.val
      rw [he]
      exact integrable_const _
  have ha (g : C𝔽) : (∫ u, Φ (g,u) ∂ν) = A g := by
    have hu (u : C₁) : c u.val = (ω u : ℂ) := by
      change (χ u.val : ℂ) * (((ideleClassNorm F u.val : ℝ≥0) : ℝ) : ℂ) ^ (s : ℂ) = _
      simp only [MonoidHom.mem_ker.mp u.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
      rfl
    change (∫ u, adelicTheta f (u.val * g) * c (u.val * g) ∂ν) = _
    simp_rw [map_mul c, hu, ← mul_assoc, integral_mul_const]
    rfl
  have hI : Integrable A μ := hp.integral_prod_left.congr (Filter.Eventually.of_forall ha)
  refine ⟨hI, ?_⟩
  change (∫ g, A g ∂μ) = ((ν univ).toReal : ℂ) * globalIdelicZFunction f c
  rw [← integral_congr_ae (Filter.Eventually.of_forall ha), ← integral_prod Φ hp, integral_prod_symm Φ hp]
  have he (u : C₁) : (∫ g, Φ (g,u) ∂μ) = ∫ g, W g ∂μ := integral_mul_left_eq_self W u.val
  simp_rw [he, integral_const]
  rw [RCLike.real_smul_eq_coe_mul]
  congr 1
  have hh := globalThetaMellinIntegral_eq_idelic f hc
  have hz := globalIdelicZFunction_eq_integral f hc
  exact hh.trans hz.symm

-- Equation (6.3.2.1) is `adelePolarSubspace`. Equation (6.3.2.2) is
-- `globalThetaPolarValues_fst_translate` and `globalThetaPolarValues_snd_translate`.
-- TODO(paper-gap): The identities following (6.3.2.2) lose the Gaussian values.
-- Use `globalThetaPolarValues_eq_eigendistributions` from §5.5.

/-- Paper: Theorem 6.3.2.1(1), p. 304, equation (6.3.2.3).
On a nontrivial norm-one component the global Mellin transform is a closed
topological embedding with range the completed Hecke principal ideal in the
Schwartz–Bergman space. -/
theorem globalConverse_nontrivial (χ : U) (_hχ : χ₁(χ) ≠ 1) :
    ∃ ZB : Θ(χ₁(χ)) →L[ℂ] B, IsClosedEmbedding ZB ∧
      (∀ (f : ℬ) s, (ZB ((K(χ₁(χ))).mkQ f)).val s = Z(f, χ, s)) ∧
      Set.range ZB = bergmanIdeal(continuedCompletedHeckeL χ) := by
  sorry

/-- Paper: Theorem 6.3.2.1(1)–(2), p. 304.
A unitary character trivial on the norm-one subgroup has a unique real
norm-twist parameter. -/
theorem globalConverse_existsUnique_normTwist (χ : U) (_hχ : χ₁(χ) = 1) :
    ∃! t : ℝ, χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t)) := by
  have hTriv (g : C𝔽) (hg : ideleClassNorm F g = 1) : χ g = 1 :=
    DFunLike.congr_fun _hχ ⟨g, hg⟩
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  obtain ⟨z, ⟨hzre, hz⟩, huniq⟩ :=
    existsUnique_unitaryComplexPower (j.comp (χ.comp σ)) (fun r ↦ Circle.norm_coe _)
  have hval (ψ : U) (s : ℂ) (g : C𝔽) : ideleClassNormTwist ψ s g =
      (ψ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s := rfl
  have hzI : z = shift(z.im) := by
    apply Complex.ext <;> simp [hzre]
  have hχg (g : C𝔽) : (χ g : ℂ) = (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ z := by
    have hn : ideleClassNorm F (g * (σ (ideleClassNorm F g))⁻¹) = 1 := by
      rw [map_mul, map_inv, hσ _, mul_inv_cancel]
    have hg : g = (g * (σ (ideleClassNorm F g))⁻¹) * σ (ideleClassNorm F g) := by group
    conv_lhs => rw [hg, map_mul, hTriv _ hn, one_mul]
    exact hz (ideleClassNorm F g)
  refine ⟨z.im, ?_, fun t ht ↦ ?_⟩
  · ext g
    rw [hval, hval, Complex.cpow_zero, mul_one, PontryaginDual.one_apply, Circle.coe_one, one_mul,
      ← hzI]
    exact hχg g
  · have := huniq (shift(t)) ⟨by simp, fun r ↦ ?_⟩
    · rw [← this]; simp
    have h := DFunLike.congr_fun ht (σ r)
    rw [hval, hval, Complex.cpow_zero, mul_one, PontryaginDual.one_apply, Circle.coe_one,
      one_mul, hσ r] at h
    exact h


/-- Paper: Theorem 6.3.2.1(1), p. 304, equation (6.3.2.4).
On tests with both polar values zero the Mellin transform is relatively open,
with closed range generated by the pole-cancelled completed Hecke L-function.
Its kernel is the restriction of the trivial homogeneous theta kernel.
Deviation: Normal form supplies the regularized generator's values at the two poles. -/
theorem globalConverse_normTwist (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    ∃ ZB : P →L[ℂ] B, IsOpenMap ZB.rangeRestrict ∧ IsClosed (Set.range ZB) ∧
      (∀ (f : P) s, (ZB f).val s = Z(f.val, χ, s)) ∧
      Set.range ZB = bergmanIdeal(regularizedL(χ, t)) ∧
      ZB.ker = (K(1)).comap (P).subtype := by
  sorry

/-- Paper: Theorem 6.3.2.1(2), p. 304, equation (6.3.2.5).
The ordinary pole-free theta space is the topological quotient of the polar
test subspace by the restriction of the ordinary theta kernel. -/
abbrev GlobalPolarFreeThetaSpace (F : Type*) [Field F] [NumberField F] :=
  (adelePolarSubspace F) ⧸ (LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype

/-- In a quotient of a submodule by the pullback of a kernel, two classes agree exactly when
the linear map agrees on their representatives. Stated for abstract modules, so that it
elaborates without unfolding the Schwartz–Bruhat instances. -/
private theorem globalPolarFreeThetaSpace_mk_eq_iff_quotient {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (Q : Submodule R M)
    (θ : M →ₗ[R] N) (f g : Q) :
    (Submodule.Quotient.mk f : Q ⧸ (LinearMap.ker θ).comap Q.subtype) =
        Submodule.Quotient.mk g ↔
      θ f = θ g := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, LinearMap.mem_ker, map_sub,
    Submodule.subtype_apply, Submodule.subtype_apply, map_sub, sub_eq_zero]

/-- Paper: Theorem 6.3.2.1(2), p. 304, equation (6.3.2.5).
Two pole-free tests give the same quotient class exactly when their ordinary
theta functions agree. -/
theorem globalPolarFreeThetaSpace_mk_eq_iff (f g : P) :
    (Submodule.Quotient.mk f : GlobalPolarFreeThetaSpace F) = Submodule.Quotient.mk g ↔
      adelicThetaLinearMap F f.val = adelicThetaLinearMap F g.val := by
  exact globalPolarFreeThetaSpace_mk_eq_iff_quotient (adelePolarSubspace F)
    (adelicThetaLinearMap F) f g

/-- Paper: Theorem 6.3.2.1(2), p. 304, equation (6.3.2.5).
The pole-free theta quotient is represented by the image of the polar test
subspace in the homogeneous theta space. The natural quotient topology is
identified with the subspace topology by the open quotient assertions below. -/
def globalPolarFreeThetaSubmodule (ω : PontryaginDual C₁) : Submodule ℂ Θ(ω) :=
  (P).map (K(ω)).mkQ

/-- Paper: Theorem 6.3.2.1(2), p. 304, equation (6.3.2.5).
A homogeneous class belongs to the pole-free subspace exactly when it has
a representative with both polar values zero. -/
theorem mem_globalPolarFreeThetaSubmodule (ω : PontryaginDual C₁) (x : Θ(ω)) :
    x ∈ globalPolarFreeThetaSubmodule ω ↔
      ∃ f : ℬ, f zeroAdele = 0 ∧ adeleSchwartzFourier f zeroAdele = 0 ∧ (K(ω)).mkQ f = x := by
  simp only [globalPolarFreeThetaSubmodule, Submodule.mem_map, mem_adelePolarSubspace, and_assoc]

-- TODO(paper-gap): The codomain in (6.3.2.5) is zero on a nontrivial norm-one
-- component. The map (6.3.2.6) is identically zero there.

private theorem globalConverse_nontrivial_exact_polar_translate (g : IdeleGroup (𝓞 F) F)
    (hg : ideleNorm F g = 1) (f : ℬ) :
    adelePolarValues (F := F) (schwartzBruhatUnitTranslate g f) = adelePolarValues (F := F) f := by
  apply Prod.ext
  · change f (Multiplicative.ofAdd (g.inv * 0)) = f zeroAdele
    rw [mul_zero]
  · change adeleSchwartzFourier (schwartzBruhatUnitTranslate g f) zeroAdele =
      adeleSchwartzFourier f zeroAdele
    rw [(adeleSchwartzFourier_apply_zero _).2, (adeleSchwartzFourier_apply_zero f).2]
    let : MeasurableSpace 𝔸[F] := borel _
    let : BorelSpace 𝔸[F] := ⟨rfl⟩
    let μ := additiveTamagawaMeasure F
    let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
    let d := (Homeomorph.smul (α := 𝔸[F]) g⁻¹).toMeasurableEquiv
    have hmap : μ.map d = μ := by
      ext s hs
      rw [Measure.map_apply d.measurable hs]
      change μ ((fun x : 𝔸[F] ↦ g⁻¹ • x) ⁻¹' s) = μ s
      rw [Set.preimage_smul_inv]
      change μ ((fun x : 𝔸[F] ↦ g.val * x) '' s) = μ s
      simpa [hg] using adeleHaar_mul_image F μ g s hs
    change (∫ x, (fun y ↦ f (Multiplicative.ofAdd y)) (d x) ∂μ) = _
    rw [← integral_map_equiv d (fun y : 𝔸[F] ↦ f (Multiplicative.ofAdd y)), hmap]

private theorem globalConverse_nontrivial_exact_theta_translate (ω : PontryaginDual C₁)
    (h : C₁) (g : IdeleGroup (𝓞 F) F) (hg : QuotientGroup.mk g = h.val) (f : ℬ) :
    homogeneousAdelicThetaLinearMap F ω (schwartzBruhatUnitTranslate g f) =
      (ω h : ℂ) • homogeneousAdelicThetaLinearMap F ω f := by
  have ht (a : C𝔽) : adelicTheta (schwartzBruhatUnitTranslate g f) a =
      adelicTheta f ((QuotientGroup.mk g)⁻¹ * a) := by
    induction a using QuotientGroup.induction_on with | H x => ?_
    change _ = adelicTheta f (QuotientGroup.mk (g⁻¹ * x))
    rw [adelicTheta_mk, adelicTheta_mk]
    exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
      (mul_left_comm g.inv (algebraMap F 𝔸[F] (t : F)) x.val)
  apply ContinuousMap.ext
  intro a
  change homogeneousAdelicTheta ω (schwartzBruhatUnitTranslate g f) a =
    (ω h : ℂ) * homogeneousAdelicTheta ω f a
  rw [← homogeneousAdelicTheta_homogeneous]
  apply integral_congr_ae (.of_forall fun k ↦ ?_)
  have he : (QuotientGroup.mk g)⁻¹ * (k.val * a) = k.val * (h.val⁻¹ * a) := by
    rw [hg, mul_left_comm]
  exact congrArg (· * (ω k : ℂ)) ((ht (k.val * a)).trans (congrArg (adelicTheta f) he))

private theorem globalConverse_nontrivial_exact_of_translate.{u, v} {E : Type u} {W : Type v}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E]
    [AddCommGroup W] [Module ℂ W] (p : E →ₗ[ℂ] ℂ × ℂ) (θ : E →ₗ[ℂ] W) (hp : Continuous p)
    (hsurj : Surjective p) (T : E → E) (a : ℂ) (ha : a ≠ 1)
    (hpT : ∀ f, p (T f) = p f) (hθT : ∀ f, θ (T f) = a • θ f) :
    IsOpenQuotientMap (θ.ker.mkQ.comp p.ker.subtype) := by
  -- The twisted difference is in the theta kernel and retains both polar values.
  have hK : Surjective (p.comp θ.ker.subtype) := by
    intro z
    obtain ⟨f, hf⟩ := hsurj z
    let k := (a - 1)⁻¹ • (a • f - T f)
    have hk : k ∈ θ.ker := by simp [LinearMap.mem_ker, k, hθT]
    refine ⟨⟨k, hk⟩, ?_⟩
    change p ((a - 1)⁻¹ • (a • f - T f)) = z
    rw [map_smul, map_sub, map_smul, hpT, hf]
    simpa only [sub_smul, one_smul] using inv_smul_smul₀ (sub_ne_zero.mpr ha) z
  -- A section of the polar map on that kernel is continuous, since its domain is ℂ².
  obtain ⟨s, hs⟩ := (p.comp θ.ker.subtype).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hK)
  have hs' (z : ℂ × ℂ) : p (s z).val = z := LinearMap.congr_fun hs z
  let r (f : E) : p.ker := ⟨f - (s (p f)).val, show p _ = 0 by rw [map_sub, hs', sub_self]⟩
  have hr : Continuous r := (continuous_id.sub (continuous_subtype_val.comp
    (s.continuous_of_finiteDimensional.comp hp))).subtype_mk _
  let q := θ.ker.mkQ.comp p.ker.subtype
  have he : q ∘ r = θ.ker.mkQ := by
    funext f
    change θ.ker.mkQ (f - (s (p f)).val) = θ.ker.mkQ f
    have hz : θ.ker.mkQ (s (p f)).val = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (s (p f)).property
    rw [map_sub, hz, sub_zero]
  apply AddMonoidHom.isOpenQuotientMap_of_isQuotientMap (φ := q)
  apply IsQuotientMap.of_comp hr (θ.ker.mkQL.continuous.comp continuous_subtype_val)
  change IsQuotientMap (q ∘ r)
  rw [he]
  exact θ.ker.isQuotientMap_mkQ

/-- Paper: Theorem 6.3.2.1(2), p. 304, equations (6.3.2.5) and (6.3.2.7).
On a nontrivial norm-one component the polar test subspace maps openly and
surjectively onto the full homogeneous theta space. In Mellin coordinates
the inclusion becomes the identity of the range in (6.3.2.3).
Deviation: The terminal residue space is zero on this component, as in (6.3.2.7). -/
theorem globalConverse_nontrivial_exact (ω : PontryaginDual C₁) (_hω : ω ≠ 1) :
    IsOpenQuotientMap ((K(ω)).mkQ.comp (P).subtype) := by
  have hex : ∃ h : C₁, (ω h : ℂ) ≠ 1 :=
    not_forall.mp fun hall ↦ _hω (PontryaginDual.ext fun x ↦ Subtype.ext (hall x))
  refine hex.elim fun h hh ↦ ?_
  refine (QuotientGroup.mk_surjective (s := IdeleGroup.principalSubgroup (𝓞 F) F) h.val).elim
    fun g hg ↦ ?_
  have hnorm : ideleNorm F g = 1 := by
    change ideleClassNorm F (QuotientGroup.mk g) = 1
    rw [hg, MonoidHom.mem_ker.mp h.property]
  exact globalConverse_nontrivial_exact_of_translate (E := ℬ) (W := C(C𝔽, ℂ))
    (adelePolarValues (F := F)) (homogeneousAdelicThetaLinearMap F ω)
    (adelePolarValues_continuous (F := F)) (adelePolarValues_surjective (F := F))
    (schwartzBruhatUnitTranslate (R := 𝔸[F]) g) (ω h : ℂ) hh
    (globalConverse_nontrivial_exact_polar_translate (F := F) g hnorm)
    (globalConverse_nontrivial_exact_theta_translate (F := F) ω h g hg)

/-- Paper: Theorem 6.3.2.1(2), p. 304, equations (6.3.2.5)–(6.3.2.6).
The signed polar evaluations descend to a continuous residue map on the trivial
norm-one quotient. Its kernel is the pole-free theta subspace with its quotient
topology, and the residue map is open and surjective. -/
theorem globalConverse_normTwist_exact :
    ∃ R : Θ(1) →L[ℂ] ℂ × ℂ,
      (∀ f : ℬ, R ((K(1)).mkQ f) = (-mass * f zeroAdele,
        mass * adeleSchwartzFourier f zeroAdele)) ∧
      R.ker = globalPolarFreeThetaSubmodule (F := F) 1 ∧ IsOpenQuotientMap R ∧
      IsOpenQuotientMap (((K(1)).mkQ.comp (P).subtype).rangeRestrict) := by
  sorry

-- TODO(paper-gap): In (6.3.2.8), the middle ideal contains functions with
-- poles, so intersection with the entire Schwartz–Bergman space kills both
-- residues. The first pole-cancelling factor must be s + it₀.

/-- Paper: Theorem 6.3.2.1(2), pp. 304–305, equation (6.3.2.8).
The Mellin chart identifies the trivial norm-one quotient with the meromorphic
Mellin image and its pole-free subspace with the kernel of the two residues.
A function on the punctured chart is in the middle term exactly when multiplying
by the pole polynomial extends it to the pole-cancelled Schwartz–Bergman ideal.
Deviation: The middle term uses the Mellin image with the stated quotient
topology. Its elements are represented by their values away from the two
possible poles. The growth test is on the polynomial multiple, which extends
across both poles. The left term uses the pole-cancelled generator and the
Schwartz–Bergman subspace topology of (6.3.2.4). -/
theorem globalConverse_normTwist_meromorphic_exact (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    let regular := ({-shift(t), 1 - shift(t)} : Set ℂ)ᶜ
    let polarFree := globalPolarFreeThetaSubmodule (F := F) 1
    ∃ (ZB : P →L[ℂ] B) (M : Θ(1) →ₗ[ℂ] regular → ℂ) (R : M.range →ₗ[ℂ] ℂ × ℂ),
      letI : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
      IsHomeomorph M.rangeRestrict ∧
      (∀ (f : ℬ) (s : regular), M ((K(1)).mkQ f) s = Z(f, χ, s.val)) ∧
      (∀ (f : P) s, (ZB f).val s = Z(f.val, χ, s)) ∧
      Set.range ZB = bergmanIdeal(regularizedL(χ, t)) ∧
      (∀ h : regular → ℂ, h ∈ M.range ↔
        ∃ b : B, b ∈ bergmanIdeal(regularizedL(χ, t)) ∧
          ∀ s : regular, b.val s.val = polePolynomial(t) s.val * h s) ∧
      (∀ (φ : M.range) (g : ℂ → ℂ), Meromorphic g → (∀ s : regular, g s.val = φ.val s) →
        R φ = (complexResidue g (-shift(t)), complexResidue g (1 - shift(t)))) ∧
      R.ker = polarFree.map M.rangeRestrict ∧ IsOpenQuotientMap R ∧
      IsClosedEmbedding (M.rangeRestrict.comp polarFree.subtype) ∧
      ∃ e : polarFree ≃L[ℂ] ZB.range, ∀ (x : polarFree) (s : regular),
        M x.val s = (e x).val.val s := by
  sorry

-- TODO(paper-gap): The argument on pp. 305–306 glues one-sided pole-cancelled
-- products using an unweighted difference. The two cancellation factors in
-- (6.3.2.11) differ even after applying the global functional equation.
-- TODO(paper-gap): The formula on p. 307 for global insertion omits the outside
-- integer-unit masses. See `weilIdentity_unramifiedOutside_meromorphic`.
-- Include the primes of the different in S for the unweighted local/global
-- Fourier comparison in (6.3.2.13): outside integer indicators must be self-dual.
-- The zero condition after (6.3.2.15) must allow higher multiplicities.
-- At F = ℚ, multiplying the Mellin transform of the Gaussian by s(1-s) gives
-- a pole-free test in (6.3.2.14) whose ψ is Γℝ(s), meromorphic at the trivial
-- zeros of the finite zeta function. The entire quotient here is ψ / Γℝ.
-- The final display on p. 309 yields a pole-polynomial multiple of a transform.
-- To obtain a polar-free test one must realize that multiplier on the test.
-- TODO(paper-gap): The inverse multiplier on p. 308 can have poles on Re s = 0
-- after Euler-factor removal and at trivial zeros of the finite L-function even
-- without any removal. Equations (6.3.2.16)–(6.3.2.17) substitute L_S for L_outside.

section PrincipalValue

local notation "PV(" S ")" => adelePrincipalValue F S
local notation "pvMorphism(" S ", " ω ")" => (K(ω)).mkQ.comp (PV(S))
local notation "pvTheta(" S ", " ω ")" => (pvMorphism(S, ω)).range
local notation "pvPolar(" S ")" => (P).map (PV(S))
local notation "removal(" χ ", " S ")" => reciprocalPartialHeckeEulerProduct χ S

/-- Paper: Theorem 6.3.2.2(1), pp. 309–310, equation (6.3.2.19).
On a nontrivial norm-one component, the principal-value image embeds as the
closed Schwartz–Bergman subspace divisible by the completed Hecke L-function
times the reciprocals of the removed Euler factors. The ramified factors are one. -/
theorem globalPrincipalValueConverse_nontrivial (S : Finset V) (χ : U) (_hχ : χ₁(χ) ≠ 1) :
    ∃ ZB : pvTheta(S, χ₁(χ)) →L[ℂ] B, IsClosedEmbedding ZB ∧
      (∀ (f : ℬ) s, (ZB ((pvMorphism(S, χ₁(χ))).rangeRestrict f)).val s = Z(PV(S) f, χ, s)) ∧
      Set.range ZB = bergmanIdeal(fun s ↦ removal(χ, S) s * continuedCompletedHeckeL χ s) := by
  sorry

-- TODO(paper-gap): Equation (6.3.2.20) uses the unshifted zeta generator and
-- omits the Schwartz–Bergman intersection. Even for S empty and trivial χ,
-- the entire multiple with multiplier exp(s^4) is not Schwartz on a vertical line.

/-- Paper: Theorem 6.3.2.2(1), pp. 309–310, equation (6.3.2.20).
On the principal-value image of the polar test space the Mellin map is open
onto a closed range. Its kernel is the principal-value image of the restricted
trivial homogeneous theta kernel.
Deviation: The generator uses the same norm-twist shift and cancellation as
(6.3.2.4), with the removed Euler factors. Divisibility is tested within the
Schwartz–Bergman space. -/
theorem globalPrincipalValueConverse_normTwist (S : Finset V) (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    ∃ ZB : pvPolar(S) →L[ℂ] B, IsOpenMap ZB.rangeRestrict ∧ IsClosed (Set.range ZB) ∧
      (∀ (f : pvPolar(S)) s, (ZB f).val s = Z(f.val, χ, s)) ∧
      Set.range ZB = bergmanIdeal(fun s ↦ removal(χ, S) s * regularizedL(χ, t) s) ∧
      ZB.ker = (((K(1) ⊓ (P)).map (PV(S))).comap (pvPolar(S)).subtype) := by
  sorry

-- TODO(paper-gap): In (6.3.2.21) the terminal space must be zero on a nontrivial
-- component, as in (6.3.2.23). In a pure norm-twist component with a nonempty
-- removal set, the first residue vanishes on the entire principal-value image.

/-- Paper: Theorem 6.3.2.2(2), p. 310, equations (6.3.2.21) and (6.3.2.23).
On a nontrivial norm-one component, principal values of polar-free tests already
give the full homogeneous principal-value image with its subspace topology.
The inclusion corresponds to the identity on the range in (6.3.2.19).
Deviation: The terminal residue space is zero, as in (6.3.2.23). -/
theorem globalPrincipalValueConverse_nontrivial_exact (S : Finset V)
    (ω : PontryaginDual C₁) (_hω : ω ≠ 1) :
    IsOpenQuotientMap ((pvMorphism(S, ω)).rangeRestrict.comp (P).subtype) := by
  sorry

-- TODO(paper-gap): The powers in (6.3.2.22) drop the local phases when
-- evaluating at the two shifted poles. The factors are 1 - 1 and 1 - qᵥ⁻¹
-- on a pure norm-twist component.

/-- Insertion through the stage agrees with insertion at the chosen finite place. -/
private theorem globalPrincipalValueConverse_mellin_insertion {T : Finset V}
    (v : T) (x : (v.val.adicCompletion F)ˣ) :
    sIdeleInsertion F T ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
        ((w : T) → w.val.adicCompletion F)).symm
      (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))) = IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x := by
  classical
  let : DecidableEq T := Classical.decEq _
  let g : (SAdeleRing F T)ˣ := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) _).symm
    (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))
  obtain ⟨ha, hf, ho⟩ := sIdeleInsertion_apply F T g
  apply Units.ext
  apply Prod.ext
  · exact ha
  · apply RestrictedProduct.ext
    intro u
    change (sIdeleInsertion F T g).val.2 u =
      RestrictedProduct.mulSingle (fun w : V ↦ w.adicCompletionIntegers F) v.val x.val u
    by_cases hu : u = v.val
    · subst u
      rw [hf v, RestrictedProduct.mulSingle_eq_same]
      change ((Pi.mulSingle (M := fun t : T ↦ (t.val.adicCompletion F)ˣ) v x v :
        (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F) = _
      rw [Pi.mulSingle_eq_same]
    · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
      by_cases hm : u ∈ T
      · rw [hf ⟨u, hm⟩]
        change ((Pi.mulSingle (M := fun t : T ↦ (t.val.adicCompletion F)ˣ) v x ⟨u, hm⟩ :
          (u.adicCompletion F)ˣ) : u.adicCompletion F) = 1
        rw [Pi.mulSingle_eq_of_ne (fun e ↦ hu (congrArg Subtype.val e)), Units.val_one]
      · exact ho u hm

/-- The finite Euler factors in the local and global conventions agree. -/
private theorem globalPrincipalValueConverse_mellin_factor
    (χ' : U) (v : V) (s : ℂ) :
    finiteLocalEulerFactor v (finitePlaceRestriction F v (ideleClassNormTwist χ' s)) =
      finiteHeckeEulerFactor χ' v s := by
  classical
  let c := finitePlaceRestriction F v (ideleClassNormTwist χ' s)
  let c₀ := finitePlaceRestriction F v (ideleClassNormTwist χ' 0)
  have htwist (x : (v.adicCompletion F)ˣ) :
      c x = c₀ x * (‖x.val‖ : ℂ) ^ s := by
    let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x
    change (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) * _
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofAdicCompletion]
    rfl
  have hrestrict (x : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist χ' 0).restrict v x.val = c₀ x := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hunram : (∀ u : (v.adicCompletionIntegers F)ˣ,
      c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1) ↔ (ideleClassNormTwist χ' 0).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    refine forall_congr' fun u ↦ ?_
    let x := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    change c x = 1 ↔ (ideleClassNormTwist χ' 0).restrict v x.val = 1
    have hn : ‖x.val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := x)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [htwist, hn, Complex.ofReal_one, Complex.one_cpow, mul_one, hrestrict]
  change finiteLocalEulerFactor v c = finiteHeckeEulerFactor χ' v s
  by_cases hv : (ideleClassNormTwist χ' 0).IsUnramifiedAt v
  · rw [finiteLocalEulerFactor, ite_eq_left (hunram.mpr hv), finiteHeckeEulerFactor, ite_eq_left hv]
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    let hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
    let π := Units.mk0 _ hπ.ne_zero
    change (1 - c π)⁻¹ = _
    have hn := norm_uniformizer_adicCompletion v π.val hπ
    rw [htwist, hv.localValue_eq π.val hπ, hrestrict, hn,
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) s,
      Complex.cpow_neg, Complex.ofReal_natCast]
  · rw [finiteLocalEulerFactor, ite_eq_right (mt hunram.mp hv), finiteHeckeEulerFactor,
      ite_eq_right hv]

/-- Restriction to the local stage preserves each selected Euler factor. -/
private theorem globalPrincipalValueConverse_mellin_localFactor {T : Finset V} (χ : U)
    (hc : χ₀(χ) ∈ unramifiedOutside F T) (η : PontryaginDual (SIdeleQuotient F T))
    (hχ : sIdeleRestriction F T ⟨χ₀(χ), hc⟩ = normChartₛ(η) 0) (v : T) (s : ℂ) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (normChartₛ(η) s)) =
      finiteHeckeEulerFactor χ v.val s := by
  have htwist (g : (SAdeleRing F T)ˣ) :
      normChartₛ(η) s (QuotientGroup.mk g) =
        ideleClassNormTwist χ s (QuotientGroup.mk (sIdeleInsertion F T g)) := by
    have hbase := DFunLike.congr_fun hχ (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at hbase
    change (χ (QuotientGroup.mk (sIdeleInsertion F T g)) : ℂ) * _ ^ (0 : ℂ) =
      (η (QuotientGroup.mk g) : ℂ) * _ ^ (0 : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (η (QuotientGroup.mk g) : ℂ) *
        ((((sIdeleQuotientNorm F T) (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ (QuotientGroup.mk (sIdeleInsertion F T g)) : ℂ) * _ ^ s
    rw [← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  have hfinite (v : T) : sLocalFiniteRestriction v (normChartₛ(η) s) =
      finitePlaceRestriction F v.val (ideleClassNormTwist χ s) := by
    ext1 x
    change normChartₛ(η) s (QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
        ((w : T) → w.val.adicCompletion F)).symm
      (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))) =
      ideleClassNormTwist χ s (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x))
    rw [htwist, globalPrincipalValueConverse_mellin_insertion]
  rw [hfinite, globalPrincipalValueConverse_mellin_factor]

/-- The meromorphic Mellin transform only depends on the global theta class. -/
private theorem globalPrincipalValueConverse_mellin_class (χ : U) (f g : ℬ)
    (hq : (Submodule.Quotient.mk f : GlobalAdelicThetaSpace F) = Submodule.Quotient.mk g) :
    (fun z ↦ Z(f, χ, z)) = (fun z ↦ Z(g, χ, z)) := by
  have hf := globalIdelicZFunction_meromorphic f χ
  have hg := globalIdelicZFunction_meromorphic g χ
  rw [← toMeromorphicNFOn_eq_self.mpr hf, ← toMeromorphicNFOn_eq_self.mpr hg]
  apply heckeEulerProductOutside_eq_finite_nf_eq _ _ hf.meromorphicOn hg.meromorphicOn
  intro z hz
  have h₀ : ideleClassNormTwist (1 : U) 0 = 1 := by
    ext1 x
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hreg : 0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ z) := by
    rw [globalIdelicOrderBound, ite_eq_right]
    rintro (h | h)
    · rw [← h₀] at h
      have he := quasiCharacterAbscissa_ideleClassNormTwist χ z
      rw [h, quasiCharacterAbscissa_ideleClassNormTwist] at he
      simp at he
      linarith
    · have he := quasiCharacterAbscissa_ideleClassNormTwist χ z
      rw [h, quasiCharacterAbscissa_ideleClassNormTwist] at he
      simp at he
      linarith
  exact congrArg (fun x : GlobalAdelicThetaSpace F ↦
    (globalThetaMellin x).val ⟨ideleClassNormTwist χ z, hreg⟩) hq

private theorem globalPrincipalValueConverse_mellin_tensor
    {M N Y : Type*} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (e : InductiveTensor M N ≃L[ℂ] Y)
    (f : M →ₗ[ℂ] M) (g : N →ₗ[ℂ] N) (hf : f = LinearMap.id) (hg : g = LinearMap.id) :
    e.toLinearMap.comp ((TensorProduct.map f g).comp e.symm.toLinearMap) = LinearMap.id := by
  subst f g
  have H : TensorProduct.map (LinearMap.id (R := ℂ) (M := M)) (LinearMap.id (R := ℂ) (M := N)) =
      LinearMap.id := TensorProduct.map_id
  rw [H]
  apply LinearMap.ext
  exact e.apply_symm_apply

open scoped TensorProduct in
private theorem globalPrincipalValueConverse_mellin_emptyTensor
    {ι M Y : Type*} {N : ι → Type*} [IsEmpty ι]
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (e : InductiveTensor M (FinestLocallyConvex (⨂[ℂ] i, N i)) ≃L[ℂ] Y)
    (L : ∀ i, N i →ₗ[ℂ] N i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, N i)
    let op : W →ₗ[ℂ] W := PiTensorProduct.map L
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id (R := ℂ) (M := M)) op).comp
      e.symm.toLinearMap) = LinearMap.id := by
  intro W op
  have hp : op = LinearMap.id := (congrArg (PiTensorProduct.map (R := ℂ))
    (Subsingleton.elim L (fun i ↦ (LinearMap.id : N i →ₗ[ℂ] N i)))).trans PiTensorProduct.map_id
  exact globalPrincipalValueConverse_mellin_tensor e LinearMap.id op rfl hp

private theorem globalPrincipalValueConverse_mellin_emptyTest :
    adelePrincipalValue F ∅ = LinearMap.id := by
  unfold adelePrincipalValue
  with_reducible_and_instances
    refine globalPrincipalValueConverse_mellin_tensor _ _ _ ?_ rfl
  unfold sAdelePrincipalValue
  with_reducible_and_instances
    exact globalPrincipalValueConverse_mellin_emptyTensor (ι := ↥(∅ : Finset V)) _ _

/-- Compare both global transforms at a stage containing the test, the conductor and the removed places. -/
private theorem globalPrincipalValueConverse_mellin_stage (S : Finset V) (χ : U) (f : ℬ) :
    (fun s ↦ Z(PV(S) f, χ, s)) =ᶠ[codiscrete ℂ] (fun s ↦ removal(χ, S) s * Z(f, χ, s)) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hn
  · simp [globalPrincipalValueConverse_mellin_emptyTest, reciprocalPartialHeckeEulerProduct]
  obtain ⟨A, g, rfl⟩ := sAdeleSchwartzToGlobal_exhaustive F f
  obtain ⟨U₀, hB⟩ : ∃ U₀ : Finset V, χ₀(χ) ∈ unramifiedOutside F U₀ := by
    apply Set.mem_iUnion.mp
    rw [iUnion_unramifiedOutside]
    trivial
  let T := A ∪ (U₀ ∪ S)
  have hAT : A ⊆ T := Finset.subset_union_left
  have hST : S ⊆ T := Finset.subset_union_right.trans Finset.subset_union_right
  have hc : χ₀(χ) ∈ unramifiedOutside F T := fun v hv ↦
    hB v (fun h ↦ hv (Finset.mem_union_right _ (Finset.mem_union_left _ h)))
  let k := sAdeleSchwartzTransition F hAT g
  have hk : sAdeleSchwartzToGlobal F T k = sAdeleSchwartzToGlobal F A g :=
    LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hAT) g
  rw [← hk]
  let p := sAdelePrincipalValue F hST k
  have hq := LinearMap.congr_fun (sLocalThetaPrincipalValue_toGlobal (F := F) hST hn)
    (Submodule.Quotient.mk k)
  have hZ := globalPrincipalValueConverse_mellin_class χ
    (sAdeleSchwartzToGlobal F T p) (PV(S) (sAdeleSchwartzToGlobal F T k)) hq
  rw [← hZ]
  obtain ⟨η, hη⟩ := heckeEulerProductOutside_eq_finite_unitary T χ hc
  obtain ⟨L, hL, hLe⟩ := finiteHeckeL_exists_continuation χ
  have hW := fun b ↦ weilIdentity_unramifiedOutside_meromorphic T b χ hc L hL (fun z hz ↦ hLe ⟨z, hz⟩)
  have hbase : sIdeleRestriction F T ⟨χ₀(χ), hc⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η := by
    ext1 x
    have hx := DFunLike.congr_fun hη x
    change _ = (η x : ℂ) * _ ^ (0 : ℂ) at hx
    change _ = (η x : ℂ)
    simpa only [Complex.cpow_zero, mul_one] using hx
  filter_upwards [hW p, hW k, sLocalIdelicZFunction_principalValue S hST k η] with z hp hkz hloc
  dsimp only at hp hkz hloc ⊢
  rw [hbase] at hp hkz
  rw [hp, hkz]
  dsimp only [p] at *
  rw [hloc]
  have hprod : (∏ v : T, if v.val ∈ S then
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (normChartₛ(η) z)) else 1) =
      ∏ v ∈ S, finiteHeckeEulerFactor χ v z := by
    simp_rw [globalPrincipalValueConverse_mellin_localFactor χ hc η hη]
    rw [Finset.prod_coe_sort T (fun v : V ↦ if v ∈ S then finiteHeckeEulerFactor χ v z else 1)]
    rw [← Finset.prod_filter]
    congr 1
    ext v
    simp [and_iff_right_of_imp (fun h ↦ hST h)]
  rw [hprod, div_eq_mul_inv, reciprocalPartialHeckeEulerProduct, ← Finset.prod_inv_distrib]
  ring

/-- A finite limit of the pole-cancelled transform gives its contour residue. -/
private theorem globalPrincipalValueConverse_normTwist_residues_limit (M : ℂ → ℂ) (r c : ℂ)
    (hm : MeromorphicAt M r)
    (hl : Tendsto (fun z ↦ (z - r) * M z) (𝓝[≠] r) (𝓝 c)) : complexResidue M r = c := by
  let H := fun z ↦ (z - r) * M z
  have hH : MeromorphicAt H r := (analyticAt_id.sub analyticAt_const).meromorphicAt.mul hm
  let G := toMeromorphicNFAt H r
  have ha : AnalyticAt ℂ G r := hH.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hH).mp ⟨c, hl⟩)
  have hG : H =ᶠ[𝓝[≠] r] G := hH.eq_nhdsNE_toMeromorphicNFAt
  have hv : G r = c := tendsto_nhds_unique
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hl.congr' hG)
  have he : M =ᶠ[𝓝[≠] r] fun z ↦ G z / (z - r) := by
    filter_upwards [hG, self_mem_nhdsWithin] with z hz hzr
    rw [eq_div_iff (sub_ne_zero.mpr hzr)]
    exact (mul_comm _ _).trans hz
  calc complexResidue M r = complexResidue (fun z ↦ G z / (z - r)) r := by
         obtain ⟨R, hR, hball⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
         unfold complexResidue Filter.limUnder
         apply congrArg Filter.lim
         apply Filter.map_congr
         filter_upwards [Ioo_mem_nhdsGT hR] with d hd
         congr 1
         apply circleIntegral.integral_congr hd.1.le
         intro z hz
         have hdist := Metric.mem_sphere.mp hz
         refine hball ⟨Metric.mem_ball.mpr (hdist.trans_lt hd.2), ?_⟩
         rintro rfl
         exact hd.1.ne (by simpa using hdist)
       _ = c := (complexResidue_div_sub ha).trans hv

/-- Paper: Theorem 6.3.2.2(2), p. 310, equation (6.3.2.22).
The residues of a principal-value transform are the signed polar evaluations
times the reciprocal partial Euler product at the respective poles.
Deviation: The multipliers are evaluated in the norm-twist chart, retaining
the local phases. -/
theorem globalPrincipalValueConverse_normTwist_residues (S : Finset V) (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (f : ℬ) :
    (complexResidue (fun s ↦ Z(PV(S) f, χ, s)) (-shift(t)),
      complexResidue (fun s ↦ Z(PV(S) f, χ, s)) (1 - shift(t))) =
      (removal(χ, S) (-shift(t)) * (-mass * f zeroAdele),
        removal(χ, S) (1 - shift(t)) * (mass * adeleSchwartzFourier f zeroAdele)) := by
  have hM := globalPrincipalValueConverse_mellin_stage S χ f
  have he : Continuous (removal(χ, S)) := by
    classical
    apply continuous_finsetProd
    intro v _
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp only [inv_inv]
      have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
      exact (continuous_const.sub (continuous_const.mul
        (continuous_neg.const_cpow (Or.inl hq))))
    · simpa only [inv_one] using (continuous_const : Continuous (fun _ : ℂ ↦ (1 : ℂ)))
  have htw (z : ℂ) : ideleClassNormTwist χ z = ideleClassNormTwist (1 : U) (z + shift(t)) := by
    simpa only [zero_add, add_comm (shift(t))] using ideleClassNormTwist_add_of_eq _hχ z
  have hres (r c : ℂ) (hr : Tendsto (fun w ↦ (w - r) * Z(f, 1, w)) (𝓝[≠] r) (𝓝 c)) :
      complexResidue (fun z ↦ Z(PV(S) f, χ, z)) (r - shift(t)) =
        removal(χ, S) (r - shift(t)) * c := by
    have hadd : Tendsto (fun z : ℂ ↦ z + shift(t)) (𝓝[≠] (r - shift(t))) (𝓝[≠] r) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun z : ℂ ↦ z + shift(t)) := continuous_id.add continuous_const
        simpa only [sub_add_cancel] using
          (hc.continuousAt (x := r - shift(t))).tendsto.mono_left (nhdsWithin_le_nhds (s := {r - shift(t)}ᶜ))
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact fun h ↦ hz (eq_sub_iff_add_eq.mpr h)
    apply globalPrincipalValueConverse_normTwist_residues_limit _ _ _
      ((globalIdelicZFunction_meromorphic _ _) (mem_univ _)).meromorphicAt
    apply ((he.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul (hr.comp hadd)).congr'
    filter_upwards [hM.filter_mono (nhdsNE_le_codiscrete _)] with z hz
    change removal(χ, S) z * ((z + shift(t) - r) * Z(f, 1, z + shift(t))) =
      (z - (r - shift(t))) * Z(PV(S) f, χ, z)
    rw [hz, htw]
    ring
  apply Prod.ext
  · simpa only [zero_sub, sub_zero] using hres 0 _ (by
      simpa only [sub_zero] using globalIdelicZFunction_residue_zero f)
  · exact hres 1 _ (globalIdelicZFunction_residue_one f)

-- TODO(paper-gap): Equations (6.3.2.24)–(6.3.2.26) repeat the shift and entire
-- middle-term errors of (6.3.2.8). Even with those corrected, at F = ℚ, χ = 1
-- and S₀ = {2}, the factor 1 - 2⁻ˢ cancels the pole at zero, so the residues
-- cannot map onto ℂ × ℂ. The divided residues below recover the two coordinates.

/-- Paper: Theorem 6.3.2.2, pp. 309–310.
Principal value multiplies the component Mellin transform by the reciprocal
Euler product, as an identity of meromorphic functions.
Deviation: Pointwise products are compared off a discrete set to allow for cancellation. -/
theorem globalPrincipalValueConverse_mellin (S : Finset V) (χ : U) (f : ℬ) :
    (fun s ↦ Z(PV(S) f, χ, s)) =ᶠ[codiscrete ℂ] (fun s ↦ removal(χ, S) s * Z(f, χ, s)) := by
  exact globalPrincipalValueConverse_mellin_stage S χ f

/-- Paper: Theorem 6.3.2.2(2), p. 310, equations (6.3.2.21)–(6.3.2.26).
On the principal-value theta image the two original residue coordinates are
recovered by dividing its Mellin transform by the known Euler multiplier.
Their common kernel is the principal-value image of the pole-free tests.
Deviation: Ordinary residues of the principal-value transform are given above.
For nonempty S its first ordinary residue vanishes identically. Division on
the punctured germs recovers the coefficient lost to that cancellation. -/
theorem globalPrincipalValueConverse_normTwist_divided_exact (S : Finset V) (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    let q := (pvMorphism(S, (1 : PontryaginDual C₁))).rangeRestrict
    ∃ R : pvTheta(S, (1 : PontryaginDual C₁)) →L[ℂ] ℂ × ℂ,
      (∀ f : ℬ,
        let h := fun s ↦ Z(PV(S) f, χ, s) / removal(χ, S) s
        R (q f) = (complexResidue h (-shift(t)), complexResidue h (1 - shift(t)))) ∧
      (∀ f : ℬ, R (q f) = (-mass * f zeroAdele, mass * adeleSchwartzFourier f zeroAdele)) ∧
      R.ker = (P).map q ∧ IsOpenQuotientMap R ∧
      IsOpenQuotientMap (q.comp (P).subtype).rangeRestrict := by
  sorry

end PrincipalValue

end GlobalConverse

end RiemannMasullo
