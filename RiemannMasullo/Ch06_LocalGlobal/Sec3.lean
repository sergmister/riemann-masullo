module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.External.Grh.Lemmas.AnalyticGoodHeightDisk

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
theorem heckeEulerProductOutside_eq_finite_nf_eq (f g : ℂ → ℂ) (hf : MeromorphicOn f univ)
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

/-- As in `exists_normTwist_of_agree_on_ker` in §5.2b, restriction to a norm section
determines the exponent relating two quasi-characters in the same component. -/
private theorem globalConverse_nontrivial_chart_surjective (χ : U) (c : QuasiCharacter C𝔽)
    (hc : ∀ h : C₁, c h.val = (χ h.val : ℂ)) : ∃ s, ideleClassNormTwist χ s = c := by
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
    IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let b := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨u, hu, -⟩ := existsUnique_complexPower (b.comp σ)
  obtain ⟨v, hv, -⟩ := existsUnique_complexPower (c.comp σ)
  refine ⟨v - u, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  let t := ideleClassNorm F x
  let y : C₁ := ⟨x / σ t, by simp [MonoidHom.mem_ker, t, hσ (ideleClassNorm F x)]⟩
  have hxy : y.val * σ t = x := div_mul_cancel x _
  have hb : b x = b y.val * (((t.val : ℝ) : ℂ)) ^ u :=
    (congrArg b hxy).symm.trans ((map_mul b _ _).trans (congrArg (b y.val * ·) (hu t)))
  have he : c x = c y.val * (((t.val : ℝ) : ℂ)) ^ v :=
    (congrArg c hxy).symm.trans ((map_mul c _ _).trans (congrArg (c y.val * ·) (hv t)))
  change b x * (((t.val : ℝ) : ℂ)) ^ (v - u) = c x
  rw [hb, he, hc y, mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr t.ne_zero)), add_sub_cancel]
  rfl

/-- In the nontrivial chart every evaluation is regular, and these evaluations
separate homogeneous classes by (5.2.3.14). -/
private theorem globalConverse_nontrivial_evaluations (χ : U) (hχ : χ₁(χ) ≠ 1) :
    ∃ A : Θ(χ₁(χ)) →L[ℂ] (ℂ → ℂ), Injective A ∧
      ∀ (f : ℬ) s, A ((K(χ₁(χ))).mkQ f) s = Z(f, χ, s) := by
  let ω := χ₁(χ)
  let Ω := {c : QuasiCharacter C𝔽 // ∀ h : C₁, c h.val = (ω h : ℂ)}
  have hres (s : ℂ) (h : C₁) : ideleClassNormTwist χ s h.val = (ω h : ℂ) :=
    normOneRestriction_unitaryChart _ (isProperMap_ideleClassNorm F).continuous χ s h
  have ht (s : ℂ) : 0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ s) := by
    suffices hn : ¬ (ideleClassNormTwist χ s = 1 ∨
        ideleClassNormTwist χ s = ideleClassNormTwist (1 : U) 1) by
      simp [globalIdelicOrderBound, hn]
    intro hp
    apply hχ
    ext1 h
    apply Circle.ext
    rw [← hres]
    rcases hp with hp | hp
    · rw [hp]; rfl
    · rw [hp]
      exact normOneRestriction_unitaryChart _ (isProperMap_ideleClassNorm F).continuous (1 : U) 1 h
  let j (s : ℂ) : {c : Ω // 0 ≤ globalIdelicOrderBound c.val} :=
    ⟨⟨ideleClassNormTwist χ s, hres s⟩, ht s⟩
  have hj : Surjective j := fun c ↦ by
    obtain ⟨s, hs⟩ := globalConverse_nontrivial_chart_surjective χ c.val.val c.val.property
    exact ⟨s, Subtype.ext (Subtype.ext hs)⟩
  obtain ⟨M, hi, hv⟩ := exists_globalHomogeneousThetaMellin (F := F) ω
  let W := meromorphicNormOneComponent (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
    ω (globalIdelicOrderBound (F := F))
  let A := ContinuousLinearMap.pi fun s ↦ (ContinuousMap.evalCLM ℂ (j s)).comp (W.subtypeL.comp M)
  refine ⟨A, fun x y h ↦ hi (Subtype.ext (ContinuousMap.ext fun c ↦ ?_)), fun f s ↦ hv f (j s)⟩
  obtain ⟨s, rfl⟩ := hj c
  exact congrFun h s

/-- The Gaussian-normalized adelic distribution supplies an entire quotient of each
test transform by the completed Hecke function, including at its zeros. -/
private theorem globalConverse_nontrivial_factor (χ : U) (hχ : χ₁(χ) ≠ 1) (f : ℬ) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, Z(f, χ, s) = continuedCompletedHeckeL χ s * u s := by
  let D := (adelicEigendistribution_normalized χ).choose
  let a : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  have hD : Differentiable ℂ (fun z ↦ D z f) := fun z ↦
    (analytic_eval_normalized (adelicEigendistribution_normalized χ).choose_spec.1 f z trivial).differentiableAt
  have hL := completedHeckeL_continuation_entire χ _ (continuedCompletedHeckeL_spec χ).1
    (continuedCompletedHeckeL_spec χ).2 (fun h ↦ hχ (PontryaginDual.ext fun x ↦ DFunLike.congr_fun h x))
  have ha := hD.const_mul a
  refine ⟨_, ha, congrFun (eq_of_agree_rightHalf (globalIdelicZFunction_meromorphic f χ)
    (fun z _ ↦ ((hL.mul ha).analyticAt z).meromorphicNFAt) 1 fun s hs ↦ ?_)⟩
  rw [globalIdelicZFunction_eq_integral f (globalTwist_mem_rightHalf χ hs),
    globalIntegral_normalized_ratio χ hs f, gaussianCompletedHeckeL_eq_completedHeckeL χ s hs]
  change a * completedHeckeL χ ⟨s, hs⟩ * D s f = continuedCompletedHeckeL χ s * (a * D s f)
  rw [(continuedCompletedHeckeL_spec χ).2 ⟨s, hs⟩]
  ring

/-- Apply the open mapping theorem to the two projections of the closed graph. The
graph and the range have their subspace topologies. -/
private theorem globalConverse_nontrivial_embedding {E Y : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    (hE : IsFrechetTVS E) (hY : IsFrechetTVS Y) (T : E →ₗ[ℂ] Y) (hi : Injective T)
    (hg : IsClosed (T.graph : Set (E × Y))) (hr : IsClosed (Set.range T)) :
    IsClosedEmbedding T := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hE.2.2.2
  have : CompleteSpace Y := hY.2.2.2
  have : TopologicalSpace.MetrizableSpace E := hE.2.2.1
  have : TopologicalSpace.MetrizableSpace Y := hY.2.2.1
  let G := T.graph
  let R := T.range
  have : CompleteSpace G := hg.completeSpace_coe
  have : CompleteSpace R := hr.completeSpace_coe
  have : IsUniformAddGroup G := G.toAddSubgroup.isUniformAddGroup
  have : IsUniformAddGroup R := R.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace G := TopologicalSpace.MetrizableSpace.subtype _
  have : TopologicalSpace.MetrizableSpace R := TopologicalSpace.MetrizableSpace.subtype _
  have : PolynormableSpace ℂ E := hE.2.1
  have : PolynormableSpace ℂ Y := hY.2.1
  have hG : IsFrechetTVS G := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have hR : IsFrechetTVS R := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  let p := (ContinuousLinearMap.fst ℂ E Y).comp G.subtypeL
  have hp : Bijective p := by
    constructor
    · intro x y h
      exact Subtype.ext (Prod.ext h (x.property.trans ((congrArg T h).trans y.property.symm)))
    · exact fun x ↦ ⟨⟨(x, T x), rfl⟩, rfl⟩
  let q : G →L[ℂ] R := ((ContinuousLinearMap.snd ℂ E Y).comp G.subtypeL).codRestrict R
    fun x ↦ ⟨x.val.1, x.property.symm⟩
  have hq : Bijective q := by
    constructor
    · intro x y h
      have h2 : x.val.2 = y.val.2 := congrArg Subtype.val h
      exact Subtype.ext (Prod.ext (hi (x.property.symm.trans (h2.trans y.property))) h2)
    · rintro ⟨_, x, rfl⟩
      exact ⟨⟨(x, T x), rfl⟩, rfl⟩
  let stages (_ : ℕ) := ContinuousLinearMap.id ℂ G
  have cover (x : G) : ∃ k, x ∈ Set.range (stages k) := ⟨0, x, rfl⟩
  have po := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hE) (fun _ ↦ hG)
    stages (fun _ ↦ le_rfl) cover p hp.2
  have qo := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hR) (fun _ ↦ hG)
    stages (fun _ ↦ le_rfl) cover q hq.2
  let e := (Equiv.ofBijective p hp).toHomeomorphOfContinuousOpen p.continuous po
  let d := (Equiv.ofBijective q hq).toHomeomorphOfContinuousOpen q.continuous qo
  have heq : (T : E → Y) = Subtype.val ∘ d ∘ e.symm := by
    funext x
    change T x = (e.symm x).val.2
    have hx : (e.symm x).val.1 = x := e.apply_symm_apply x
    exact (congrArg T hx.symm).trans (e.symm x).property.symm
  rw [heq]
  exact hr.isClosedEmbedding_subtypeVal.comp (d.isClosedEmbedding.comp e.symm.isClosedEmbedding)

/-- Evaluations on Schwartz vertical lines are continuous. Holomorphic dependence then
gives continuity of every jet by the uniform boundedness principle. -/
private theorem globalConverse_nontrivial_jets (z : ℂ) (n : ℕ) :
    Continuous (fun b : B ↦ iteratedDeriv n b.val z) := by
  obtain ⟨ht, hp, hm, hc⟩ := schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace B := hc
  have : (uniformity B).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace B := BaireSpace.of_completelyPseudoMetrizable
  have hev (s : ℂ) : ∃ L : B →L[ℂ] ℂ, ∀ b, L b = b.val s := by
    obtain ⟨S, hs, he⟩ := schwartzBergman_schwartzLine_topology univ isOpen_univ
      ordConnected_univ univ_nonempty
    let a : (univ : Set ℝ) := ⟨s.re, trivial⟩
    let ev := (BoundedContinuousFunction.evalCLM ℂ s.im).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
    refine ⟨⟨(LinearMap.proj s).comp (schwartzBergmanSubmodule univ).subtype, ?_⟩, fun _ ↦ rfl⟩
    apply (ev.continuous.comp ((continuous_apply a).comp he.continuous)).congr
    intro b
    change S b a s.im = b.val s
    simpa only [weightedVerticalTrace, a, pow_zero, one_mul, Complex.re_add_im] using hs b a s.im
  have jets (k : ℕ) (s : ℂ) : ∃ D : B →L[ℂ] ℂ, ∀ b, D b = iteratedDeriv k b.val s := by
    induction k generalizing s with
    | zero => simpa only [iteratedDeriv_zero] using hev s
    | succ k ih =>
      choose d hd using ih
      let A (y : ℂ) := (y - s)⁻¹ • (d y - d s)
      have hlim : Tendsto (fun y b ↦ A y b) (𝓝[≠] s) (𝓝 fun b ↦ iteratedDeriv (k+1) b.val s) := by
        refine tendsto_pi_nhds.mpr fun b ↦ ?_
        have hb : Differentiable ℂ b.val := fun w ↦ (b.property.2.1 w (by simp)).differentiableAt (by simp)
        have h := (((hb.contDiff : ContDiff ℂ (k+1) b.val).differentiable_iteratedDeriv' k) s).hasDerivAt.tendsto_slope
        rw [iteratedDeriv_succ]
        exact h.congr' (.of_forall fun y ↦ by simp only [slope_def_module, A, smul_apply, sub_apply, hd])
      exact ⟨continuousLinearMapOfTendsto A hlim, fun _ ↦ rfl⟩
  obtain ⟨D, hD⟩ := jets n z
  exact D.continuous.congr hD

/-- A positive-real slope gives the ordinary derivative after exponential reparametrization,
as in `log_deriv_of_tendsto_unit_slope` in §2.2b. -/
private theorem globalConverse_nontrivial_log_deriv (A : ℝ≥0ˣ → ℂ) (v : ℂ)
    (h : Tendsto (fun t : ℝ≥0ˣ ↦ (A t - A 1) / ((((t.val : ℝ) : ℂ)) - 1)) (𝓝[≠] 1) (𝓝 v)) :
    let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    HasDerivAt (fun s : ℝ ↦ A (E s)) v 0 := by
  intro E
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

/-- Translate the derivative at the identity to every point of a one-parameter orbit,
as in `unit_orbit_hasDerivAt` in §2.2b. -/
private theorem globalConverse_nontrivial_orbit_deriv {G : Type*} [Group G] (a : ℝ≥0ˣ →* G) (A d : G → ℂ)
    (h : ∀ g, Tendsto (fun t : ℝ≥0ˣ ↦ (A (a t * g) - A g) / ((((t.val : ℝ) : ℂ)) - 1))
      (𝓝[≠] 1) (𝓝 (d g))) (g : G) (s : ℝ) :
    let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    HasDerivAt (fun t : ℝ ↦ A (a (E t) * g)) (d (a (E s) * g)) s := by
  intro E
  let y := a (E s) * g
  have hD : HasDerivAt (fun t : ℝ ↦ A (a (E t) * y)) (d y) (s - s) := by
    rw [sub_self]
    apply globalConverse_nontrivial_log_deriv (fun t ↦ A (a t * y))
    simpa only [map_one, one_mul] using h y
  refine (hD.comp_sub_const s s).congr_of_eventuallyEq (.of_forall fun t ↦ ?_)
  have hmul : E (t - s) * E s = E t := Units.ext (NNReal.coe_inj.mp
    ((Real.exp_add (t - s) s).symm.trans (congrArg Real.exp (sub_add_cancel t s))))
  change A (a (E t) * g) = A (a (E (t - s)) * (a (E s) * g))
  rw [← mul_assoc, ← map_mul, hmul]

/-- A family of log profiles stable under differentiation and decaying at every
exponential rate remains Schwartz after multiplication by any complex exponential. -/
private theorem globalConverse_nontrivial_weighted_profile {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H : E →ₗ[ℂ] (ℝ → ℂ)) (D : E → E)
    (hd : ∀ f x, HasDerivAt (H f) (H (D f) x) x)
    (hdec : ∀ f (N : ℕ), ∃ C T : ℝ, ∀ x, T < |x| → ‖H f x‖ ≤ C * Real.exp (-(N : ℝ) * |x|))
    (b : ℂ) (f : E) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ x, g x = Complex.exp (b * x) * H f x := by
  let W (v : E) (x : ℝ) := Complex.exp (b * x) * H v x
  let d (v : E) := b • v + D v
  have hw (v : E) (x : ℝ) : HasDerivAt (W v) (W (d v) x) x := by
    have h := (((Complex.hasDerivAt_exp _).comp _ ((hasDerivAt_id' (x : ℂ)).const_mul b)).comp_ofReal).mul (hd v x)
    convert h using 1 <;> try rfl
    simp only [W, d, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, Function.comp_apply]
    ring
  have hs (n : ℕ) (v : E) : ContDiff ℝ n (W v) := by
    induction n generalizing v with
    | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x ↦ (hw v x).continuousAt)
    | succ n ih =>
      refine (contDiff_succ_iff_deriv (n := (n : WithTop ℕ∞))).mpr ⟨fun x ↦ (hw v x).differentiableAt, by simp, ?_⟩
      rw [show deriv (W v) = W (d v) from funext fun x ↦ (hw v x).deriv]
      exact ih _
  refine ⟨⟨W f, contDiff_infty.mpr fun n ↦ hs n f, fun k n ↦ ?_⟩, fun _ ↦ rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, iteratedDeriv n (W f) = W v := by
    induction n with
    | zero => exact ⟨f, iteratedDeriv_zero⟩
    | succ n ih =>
      obtain ⟨v, hv⟩ := ih
      exact ⟨d v, (iteratedDeriv_succ ..).trans ((congrArg deriv hv).trans (funext fun x ↦ (hw v x).deriv))⟩
  obtain ⟨N, hN⟩ := exists_nat_ge (1 + |b.re|)
  obtain ⟨C, T, hT⟩ := hdec v N
  have hc : Continuous (fun x : ℝ ↦ |x| ^ k * ‖W v x‖) :=
    (continuous_abs.pow k).mul (continuous_iff_continuousAt.mpr fun x ↦ (hw v x).continuousAt.norm)
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image (K := Icc (-T) T) hc.continuousOn
  refine ⟨max K (k.factorial * C), fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hv, Real.norm_eq_abs]
  by_cases h : T < |x|
  · apply le_max_of_le_right
    have hpos : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hT x h)) (Real.exp_pos _)
    have hk := (div_le_iff₀ (show 0 < (k.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp |x| (abs_nonneg _) k)
    have hr : b.re * x ≤ |b.re| * |x| := (le_abs_self _).trans (abs_mul _ _).le
    change |x| ^ k * ‖Complex.exp (b * x) * H v x‖ ≤ _
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ (Real.exp |x| * k.factorial) * (Real.exp (b.re * x) * (C * Real.exp (-(N : ℝ) * |x|))) := by
        gcongr
        exact hT x h
      _ = (k.factorial * C) * Real.exp ((|x| + b.re * x) + -(N : ℝ) * |x|) := by
        rw [Real.exp_add, Real.exp_add]; ring
      _ ≤ (k.factorial * C) * 1 := by
        gcongr
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_le_mul_of_nonneg_right hN (abs_nonneg x)]
      _ = _ := mul_one _
  · exact le_max_of_le_left (hK ⟨x, abs_le.mp (le_of_not_gt h), rfl⟩)

/-- Logarithmic change of variables for `dt/t`, as in the Mellin integral helper
`sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_mellin` in §5.3b. -/
private theorem globalConverse_nontrivial_log_mellin (p : ℝ → ℂ) (s : ℂ) :
    (∫ t : ℝ≥0ˣ, p (Real.log (t.val : ℝ)) * (((t.val : ℝ) : ℂ) ^ s) ∂positiveRealHaar) =
      mellin (fun t ↦ p (Real.log t)) s := by
  let : BorelSpace ℝ≥0ˣ := by
    constructor
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℝ≥0) = _
    rw [Units.isEmbedding_val₀.eq_induced, borel_comap, BorelSpace.measurable_eq (α := ℝ≥0)]
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (x : ℝ) : (e x).val = (Real.exp x).toNNReal := by
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  have hm : positiveRealHaar = volume.map e := by
    apply congrArg (fun a : ℝ → ℝ≥0ˣ ↦ volume.map a)
    funext x
    exact Units.ext (he x).symm
  rw [hm, e.measurableEmbedding.integral_map, mellin, ← integral_comp_exp]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [he, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (p x)]
  congr 2
  ring

/-- The canonical norm section identifies a homogeneous theta integral with the Mellin
transform of its logarithmic profile. All differentiated tests retain two-sided decay. -/
private theorem globalConverse_nontrivial_bergman (χ : U) (hχ : χ₁(χ) ≠ 1) (f : ℬ) :
    (fun s ↦ Z(f, χ, s)) ∈ schwartzBergmanSubmodule univ := by
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  let σ := (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ : IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp τ
  have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let H : ℬ →ₗ[ℂ] (ℝ → ℂ) := LinearMap.pi fun x ↦
    (ContinuousMap.evalCLM ℂ (σ (e x))).toLinearMap.comp (homogeneousAdelicThetaLinearMap F χ₁(χ))
  have hH (v : ℬ) : H v = fun x ↦ homogeneousAdelicTheta χ₁(χ) v (σ (e x)) := by
    funext x
    change (homogeneousAdelicThetaLinearMap F χ₁(χ) v) _ = _
    exact DFunLike.congr_fun (homogeneousAdelicThetaLinearMap_apply χ₁(χ) v) _
  have hd (v : ℬ) (x : ℝ) : HasDerivAt (H v) (H (adeleDirectionalDeriv τ v) x) x := by
    rw [hH, hH]
    have ht := globalConverse_nontrivial_orbit_deriv σ.toMonoidHom
      (homogeneousAdelicTheta χ₁(χ) v) (homogeneousAdelicTheta χ₁(χ) (adeleDirectionalDeriv τ v))
      (homogeneousAdelicTheta_directionalDeriv τ χ₁(χ) v) 1 x
    change HasDerivAt (fun t ↦ homogeneousAdelicTheta χ₁(χ) v (σ (e t) * 1))
      (homogeneousAdelicTheta χ₁(χ) (adeleDirectionalDeriv τ v) (σ (e x) * 1)) x at ht
    simpa only [mul_one] using ht
  have hdec (v : ℬ) (N : ℕ) : ∃ C T : ℝ, ∀ x, T < |x| → ‖H v x‖ ≤ C * Real.exp (-(N : ℝ) * |x|) := by
    obtain ⟨C, T, _, _, h⟩ := homogeneousAdelicTheta_decay_both χ₁(χ) v (Or.inr hχ) N
    refine ⟨C, T, fun x hx ↦ ?_⟩
    have hn : Real.log ((ideleClassNorm F (σ (e x))).val : ℝ) = x := by rw [hσ (e x)]; exact Real.log_exp x
    rw [hH]
    simpa only [hn] using h (σ (e x)) (hn.symm ▸ hx)
  obtain ⟨b, hb, -⟩ := existsUnique_complexPower
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ.comp σ))
  let p (x : ℝ) := Complex.exp (b * x) * H f x
  have hp : p ∈ logExponentialDecaySubmodule univ := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    obtain ⟨g, hg⟩ := globalConverse_nontrivial_weighted_profile H (adeleDirectionalDeriv τ)
      hd hdec ((a.val : ℂ) + b) f
    refine ⟨g, funext fun x ↦ ?_⟩
    change g x = (Real.exp (a.val * x) : ℂ) * p x
    rw [hg, add_mul, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul, mul_assoc]
  let u := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty ⟨p, hp⟩
  have hu : Differentiable ℂ u.val := fun s ↦ (u.property.2.1 s (by simp)).differentiableAt (by simp)
  have heq := (homogeneousThetaMellinIntegral_meromorphicContinuation τ χ₁(χ) f
    (canonicalIdeleNormSection_rightInverse F) χ (fun _ ↦ rfl) u.val).mp
  apply (show u.val = fun s ↦ Z(f, χ, s) from heq ⟨fun z _ ↦ (hu.analyticAt z).meromorphicNFAt, ?_⟩) ▸ u.property
  intro s _
  rw [show u.val s = mellin (fun t ↦ p (Real.log t)) s from
    positiveRealFourierMellin_apply _ _ _ _ _ _ trivial]
  rw [← globalConverse_nontrivial_log_mellin]
  change _ = ∫ t, homogeneousAdelicTheta χ₁(χ) f (σ t) * ideleClassNormTwist χ s (σ t) ∂positiveRealHaar
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  have he : e (Real.log (t.val : ℝ)) = t := Units.ext (NNReal.eq (Real.exp_log (Units.zero_lt t)))
  have hpow := hb t
  change (χ (σ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ b at hpow
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)),
    ← Complex.ofReal_log (NNReal.coe_nonneg _), mul_comm] at hpow
  change (p _ * _) = _ * ((χ (σ t) : ℂ) * (((ideleClassNorm F (σ t)).val : ℝ) : ℂ) ^ s)
  dsimp only [p]
  have hh := (congrFun (hH f) (Real.log (t.val : ℝ))).trans
    (congrArg (fun r ↦ homogeneousAdelicTheta χ₁(χ) f (σ r)) he)
  rw [hh, hσ t, ← hpow]
  ring

/-- As in the principal-value argument below, the local order inequalities give
an entire quotient by removal of singularities. -/
private theorem globalConverse_nontrivial_orders {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ z, f z = g z * u z) ↔
      ∀ z, analyticOrderAt g z ≤ analyticOrderAt f z := by
  constructor
  · rintro ⟨u, hu, he⟩ z
    rw [show f = g * u from funext he, analyticOrderAt_mul (hg.analyticAt z) (hu.analyticAt z)]
    exact self_le_add_right _ _
  · intro hord
    let q := f / g
    have hq : MeromorphicOn q univ := fun z _ ↦ (hf.analyticAt z).meromorphicAt.div (hg.analyticAt z).meromorphicAt
    have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
      intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hg.analyticAt z).meromorphicAt,
        (hf.analyticAt z).meromorphicOrderAt_eq, (hg.analyticAt z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt f z = m at hle ⊢
      generalize analyticOrderAt g z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    refine ⟨_, hdiff, fun z ↦ ?_⟩
    by_cases hz : g z = 0
    · have hpos := lt_of_lt_of_le (pos_iff_ne_zero.mpr ((hg.analyticAt z).analyticOrderAt_ne_zero.mpr hz))
          (hord z)
      rw [hz, zero_mul]
      exact (hf.analyticAt z).analyticOrderAt_ne_zero.mp hpos.ne'
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((hf.analyticAt z).div (hg.analyticAt z) hz).meromorphicNFAt]
      exact (mul_div_cancel₀ _ hz).symm

/-- Each vanishing jet is a closed condition in the Schwartz–Bergman topology. -/
private theorem globalConverse_nontrivial_closed {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) : IsClosed bergmanIdeal(g) := by
  have hdiff (f : B) : Differentiable ℂ f.val := fun w ↦
    (f.property.2.1 w (by simp)).differentiableAt (by simp)
  have hset : bergmanIdeal(g) = ⋂ (z : ℂ) (n : ℕ) (_ : (n : ℕ∞) ≤ analyticOrderAt g z)
      (i : ℕ) (_ : i < n), {f : B | iteratedDeriv i f.val z = 0} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter, globalConverse_nontrivial_orders (hdiff f) hg]
    apply forall_congr'
    intro z
    rw [← ENat.forall_natCast_le_iff_le]
    simp_rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hdiff f).analyticAt z)]
  rw [hset]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
      isClosed_eq (globalConverse_nontrivial_jets z i) continuous_const

/-- On a circle about `z`, reflecting the linear factors of a polynomial preserves
their boundary moduli and gives each reflected factor modulus `r` at the center.
The maximum principle thus divides out all the factors at a cost of `r⁻¹` per root. -/
private theorem globalConverse_nontrivial_strip_bounds_polynomial (z : ℂ) (r : ℝ) (hr : 0 < r)
    (A : Finset ℂ) (n : ℂ → ℕ) (v : ℂ → ℂ) (hv : AnalyticOnNhd ℂ v (Metric.closedBall z r))
    (M : ℝ) (hb : ∀ w ∈ Metric.sphere z r, ‖(∏ ρ ∈ A, (w - ρ) ^ n ρ) * v w‖ ≤ M) :
    r ^ (∑ ρ ∈ A, n ρ) * ‖v z‖ ≤ M := by
  let q (ρ w : ℂ) := (r : ℂ) - starRingEnd ℂ (ρ - z) * (w - z) / r
  have hq (w : ℂ) (hw : w ∈ Metric.sphere z r) (ρ : ℂ) : ‖q ρ w‖ = ‖w - ρ‖ := by
    have hw' : ‖w - z‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have he : (w - z) * starRingEnd ℂ (w - z) = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw']; push_cast; rfl
    have hid : q ρ w * (r : ℂ) = (w - z) * starRingEnd ℂ (w - ρ) := by
      rw [show w - ρ = (w - z) - (ρ - z) by ring, map_sub, mul_sub, he]
      dsimp [q]
      field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    have hn := congrArg norm hid
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hw', Complex.norm_conj,
      mul_comm r] at hn
    exact mul_right_cancel₀ hr.ne' hn
  let G (w : ℂ) := (∏ ρ ∈ A, q ρ w ^ n ρ) * v w
  have hG : AnalyticOnNhd ℂ G (Metric.closedBall z r) := by
    intro w hw
    exact (Finset.analyticAt_fun_prod A fun ρ _ ↦
      (show AnalyticAt ℂ (q ρ) w by dsimp [q]; fun_prop).pow _).mul (hv w hw)
  have hd : DiffContOnCl ℂ G (Metric.ball z r) := DifferentiableOn.diffContOnCl (by
    rw [closure_ball z hr.ne']; exact hG.differentiableOn)
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd
    (C := M) (fun w hw ↦ by
      rw [frontier_ball z hr.ne'] at hw
      simpa only [G, norm_mul, norm_prod, norm_pow, hq w hw] using hb w hw)
    (subset_closure (Metric.mem_ball_self hr))
  simpa [G, q, norm_mul, norm_pow, norm_prod, Complex.norm_real, abs_of_pos hr,
    Finset.prod_pow_eq_pow_sum] using h

/-- A denominator bounded by `M` on the radius-six circle and bounded away from zero
at its center costs only a fixed power of `M` in division on a smaller disk. The
factorization counts the zeros with multiplicity and bounds the zero-free factor. -/
private theorem globalConverse_nontrivial_strip_bounds_disk (r δ : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) :
    ∃ (k : ℕ) (K : ℝ), 0 < K ∧ ∀ (D v : ℂ → ℂ) (c z : ℂ) (M A : ℝ),
      AnalyticOnNhd ℂ D univ → AnalyticOnNhd ℂ v (Metric.closedBall z r) →
      dist z c ≤ 2 → 1 ≤ M → δ ≤ ‖D c‖ → (∀ w ∈ Metric.sphere c 6, ‖D w‖ ≤ M) →
      (∀ w ∈ Metric.sphere z r, ‖D w * v w‖ ≤ A) → ‖v z‖ ≤ K * M ^ k * A := by
  let J := Real.log (6 / 5 : ℝ)
  have hJ : 0 < J := Real.log_pos (by norm_num)
  let H := 8 + 9 * (Real.log 5 / J)
  let e := H - Real.log r / J
  have hlr : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let k := ⌈e⌉₊
  refine ⟨k, Real.exp (8 - Real.log δ - e * Real.log δ), Real.exp_pos _, ?_⟩
  intro D v c z M A hD hv hzc hM hcenter hbd hprod
  have hc : 0 < ‖D c‖ := hδ.trans_le hcenter
  obtain ⟨S, n, g, hf, hn, hg⟩ := External.Grh.exists_goodHeight_disk_factorization hD
    (norm_pos_iff.mp hc) hM hbd
  let X := Real.log M - Real.log δ
  have hX : Real.log (M / ‖D c‖) ≤ X := by
    rw [Real.log_div (by linarith) hc.ne']
    exact sub_le_sub_left (Real.log_le_log hδ hcenter) _
  have hcount : ((∑ ρ ∈ S, n ρ : ℕ) : ℝ) ≤ X / J := by
    push_cast
    exact hn.trans (div_le_div_of_nonneg_right hX hJ.le)
  let L := Real.exp (Real.log δ - 8 - H * X)
  have hL : 0 < L := Real.exp_pos _
  have hlow (w : ℂ) (hw : w ∈ Metric.sphere z r) : L ≤ ‖g w‖ := by
    have hwc : w ∈ Metric.closedBall c 3 := by
      have := dist_triangle w z c
      rw [Metric.mem_sphere.mp hw] at this
      exact Metric.mem_closedBall.mpr (by linarith)
    obtain ⟨hne, hl⟩ := hg w hwc
    rw [← Real.exp_log (norm_pos_iff.mpr hne)]
    apply Real.exp_le_exp.mpr
    exact (sub_le_sub (sub_le_sub_right (Real.log_le_log hδ hcenter) _)
      (mul_le_mul_of_nonneg_left hX hH)).trans hl
  have hpoly := globalConverse_nontrivial_strip_bounds_polynomial z r hr S n v hv (A / L)
    (fun w hw ↦ by
      apply (le_div_iff₀ hL).mpr
      have h := hprod w hw
      rw [hf, norm_mul, norm_mul] at h
      rw [norm_mul, mul_right_comm]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlow w hw) (norm_nonneg _))
        (norm_nonneg _)).trans h)
  have hAn : 0 ≤ A := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := z)).mpr hr.le
    exact (norm_nonneg _).trans (hprod w hw)
  let d := ∑ ρ ∈ S, n ρ
  have hcost : (L * r ^ d)⁻¹ ≤ Real.exp (8 - Real.log δ - e * Real.log δ) * M ^ k := by
    have hM0 : 0 < M := zero_lt_one.trans_le hM
    have hp : 0 < L * r ^ d := mul_pos hL (pow_pos hr _)
    rw [← Real.exp_log (inv_pos.mpr hp), Real.log_inv, Real.log_mul hL.ne' (pow_pos hr _).ne',
      Real.log_pow, show Real.log L = _ from Real.log_exp _,
      show M ^ k = Real.exp ((k : ℝ) * Real.log M) by rw [Real.exp_nat_mul, Real.exp_log hM0],
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog := mul_le_mul_of_nonpos_right hcount hlr
    have hk := mul_le_mul_of_nonneg_right (Nat.le_ceil e) (Real.log_nonneg hM)
    dsimp only [e] at hk ⊢
    dsimp only [d, X] at *
    linarith [show (Real.log M - Real.log δ) / J * Real.log r =
      Real.log r / J * (Real.log M - Real.log δ) by ring]
  calc
    ‖v z‖ ≤ (L * r ^ d)⁻¹ * A := by
      rw [← div_eq_inv_mul, le_div_iff₀ (mul_pos hL (pow_pos hr _))]
      simpa only [d, mul_left_comm, mul_comm, mul_assoc] using (le_div_iff₀ hL).mp hpoly
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost hAn

/-- On a positive substrip, use disks centered at the target height on or to the
right of the line 2. Rapid decay of the product on the target disk absorbs the
polynomial loss coming from the larger disk about the Euler-product center. -/
private theorem globalConverse_nontrivial_strip_bounds_divide (D v : ℂ → ℂ)
    (hD : AnalyticOnNhd ℂ D univ) (hv : AnalyticOnNhd ℂ v (Complex.re ⁻¹' Ioi 0))
    (hlo : ∃ δ > 0, ∀ z : ℂ, 2 ≤ z.re → δ ≤ ‖D z‖)
    (hup : ∀ b ≥ (2 : ℝ), ∃ C ≥ (1 : ℝ), ∃ m : ℕ, ∀ z : ℂ, z.re ∈ Icc (-4) (b + 6) →
      ‖D z‖ ≤ C * (1 + |z.im|) ^ m)
    (hprod : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ n : ℕ, ∃ A : ℝ, ∀ w : ℂ, w.re ∈ Icc a b →
      (1 + |w.im|) ^ n * ‖D w * v w‖ ≤ A)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    BddAbove ((fun z ↦ ‖v z‖) '' (Complex.re ⁻¹' Icc a b)) := by
  obtain ⟨δ, hδ, hlo⟩ := hlo
  let r := min (a / 2) 1
  have hr : 0 < r := lt_min (by positivity) zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  obtain ⟨k, K, hK, hdisk⟩ := globalConverse_nontrivial_strip_bounds_disk r δ hr hr1 hδ
  obtain ⟨C, hC, m, hM⟩ := hup (max 2 b) (le_max_left _ _)
  obtain ⟨A, hA⟩ := hprod (a / 2) (b + 1) (by positivity) (by linarith) (m * k)
  refine ⟨K * (C * 7 ^ m) ^ k * (2 ^ (m * k) * A), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change a ≤ z.re ∧ z.re ≤ b at hz
  let c : ℂ := ⟨max 2 z.re, z.im⟩
  let T := 1 + |z.im|
  have hT : 1 ≤ T := le_add_of_nonneg_right (abs_nonneg _)
  have hc : dist z c ≤ 2 := by
    have e : z - c = ((z.re - max 2 z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [c]
    rw [dist_eq_norm, e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    rcases le_total 2 z.re with h | h
    · rw [max_eq_right h]; norm_num
    · rw [max_eq_left h]; constructor <;> linarith [hz.1]
  have hnear (w : ℂ) (hw : w ∈ Metric.closedBall z r) :
      w.re ∈ Icc (a / 2) (b + 1) ∧ T ≤ 2 * (1 + |w.im|) := by
    have hd : ‖w - z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have h₁ := (Complex.abs_re_le_norm (w - z)).trans hd
    have h₂ := (Complex.abs_im_le_norm (w - z)).trans hd
    rw [Complex.sub_re, abs_le] at h₁
    rw [Complex.sub_im] at h₂
    have hrs : r ≤ a / 2 := min_le_left _ _
    refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, ?_⟩
    have := abs_sub_abs_le_abs_sub z.im w.im
    rw [abs_sub_comm] at this
    dsimp only [T]; linarith [abs_nonneg w.im]
  let M := (C * 7 ^ m) * T ^ m
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by norm_num))) (one_le_pow₀ hT)
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere c 6) : ‖D w‖ ≤ M := by
    have hd : ‖w - c‖ = 6 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have h₁ := Complex.abs_re_le_norm (w - c)
    have h₂ := Complex.abs_im_le_norm (w - c)
    rw [hd, Complex.sub_re, abs_le] at h₁
    rw [hd, Complex.sub_im] at h₂
    have hcre : c.re ∈ Icc 2 (max 2 b) := ⟨le_max_left _ _, max_le_max_left _ hz.2⟩
    refine (hM w ⟨by linarith [hcre.1], by linarith [hcre.2]⟩).trans ?_
    have hi := abs_sub_abs_le_abs_sub w.im c.im
    have ht : 1 + |w.im| ≤ 7 * T := by dsimp [T, c] at *; linarith [abs_nonneg z.im]
    dsimp only [M]
    rw [mul_assoc, ← mul_pow]
    gcongr
  have hTk : 0 < T ^ (m * k) := pow_pos (zero_lt_one.trans_le hT) _
  have h := hdisk D v c z M (2 ^ (m * k) * A / T ^ (m * k)) hD
    (hv.mono fun w hw ↦ lt_of_lt_of_le (half_pos ha) (hnear w hw).1.1) hc hM1
    (hlo c (le_max_left _ _)) hcircle (fun w hw ↦ by
      obtain ⟨hre, ht⟩ := hnear w (Metric.sphere_subset_closedBall hw)
      apply (le_div_iff₀ hTk).mpr
      rw [mul_comm]
      calc
        _ ≤ (2 * (1 + |w.im|)) ^ (m * k) * ‖D w * v w‖ := by gcongr
        _ ≤ _ := by rw [mul_pow, mul_assoc]; gcongr; exact hA w hre)
  refine h.trans (le_of_eq ?_)
  dsimp only [M]
  rw [mul_pow, ← pow_mul]
  field_simp [hTk.ne']

/-- Each removed Euler factor is an entire geometric denominator. Its upper and
lower triangle inequalities are uniform in the height of the complex argument. -/
private theorem globalConverse_nontrivial_strip_bounds_factor (χ : U) (v : V) :
    Differentiable ℂ (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) ∧ ∀ z : ℂ,
      1 - (q(v) : ℝ) ^ (-z.re) ≤ ‖(finiteHeckeEulerFactor χ v z)⁻¹‖ ∧
      ‖(finiteHeckeEulerFactor χ v z)⁻¹‖ ≤ 1 + (q(v) : ℝ) ^ (-z.re) := by
  let q : ℝ := q(v)
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp only [inv_inv]
    have hn : (q(v) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    refine ⟨(differentiable_const _).sub ((differentiable_const _).mul
      (differentiable_neg.const_cpow (Or.inl hn))), fun z ↦ ?_⟩
    let w := χ₀(χ).localValue v * (q(v) : ℂ) ^ (-z)
    have hw : ‖w‖ = q ^ (-z.re) := by
      change ‖_ * (q : ℂ) ^ (-z)‖ = _
      rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re]
    change 1 - q ^ (-z.re) ≤ ‖1 - w‖ ∧ ‖1 - w‖ ≤ 1 + q ^ (-z.re)
    simpa only [hw, norm_one] using And.intro (norm_sub_norm_le (1 : ℂ) w) (norm_sub_le (1 : ℂ) w)
  · simp only [inv_one, norm_one]
    exact ⟨differentiable_const _, fun z ↦ ⟨sub_le_self _ (Real.rpow_nonneg hq₀.le _),
      le_add_of_nonneg_right (Real.rpow_nonneg hq₀.le _)⟩⟩

/-- For a nontrivial component the finite continuation is entire. The outside
Euler product has polynomial upper bounds on strips and a uniform positive
lower bound at real parts at least two. Weil's identity identifies its product
with the local zeta function throughout the positive half-plane. -/
private theorem globalConverse_nontrivial_strip_bounds_euler (χ : U) (hχ : χ₁(χ) ≠ 1)
    (S : Finset V) (hD : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (hc : χ₀(χ) ∈ unramifiedOutside F S) (η : PontryaginDual (SIdeleQuotient F S))
    (hη : sIdeleRestriction F S ⟨χ₀(χ), hc⟩ = normChartₛ(η) 0)
    (g : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    ∃ D : ℂ → ℂ, AnalyticOnNhd ℂ D univ ∧
      (∃ δ > 0, ∀ z : ℂ, 2 ≤ z.re → δ ≤ ‖D z‖) ∧
      (∀ b ≥ (2 : ℝ), ∃ C ≥ (1 : ℝ), ∃ m : ℕ, ∀ z : ℂ, z.re ∈ Icc (-4) (b + 6) →
        ‖D z‖ ≤ C * (1 + |z.im|) ^ m) ∧
      ∀ z : ℂ, 0 < z.re → D z * sLocalIdelicZFunction g (normChartₛ(η) z) =
        globalIdelicZFunction (sAdeleSchwartzToGlobal F S g) (ideleClassNormTwist χ z) := by
  classical
  have hnχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 :=
    fun h ↦ hχ (PontryaginDual.ext fun y ↦ DFunLike.congr_fun h y)
  let L (z : ℂ) := (heckeGammaFactor χ z)⁻¹ * continuedCompletedHeckeL χ z
  have hL := (differentiable_inv_heckeGammaFactor χ).mul (completedHeckeL_continuation_entire χ _
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hnχ)
  have hNF : MeromorphicNFOn L univ := fun z _ ↦ (hL.analyticAt z).meromorphicNFAt
  have hs (s : halfPlane) : L s = finiteHeckeL χ s := by
    dsimp only [L]
    rw [(continuedCompletedHeckeL_spec χ).2 s]
    change _ * (heckeGammaFactor χ s * _) = _
    rw [inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property))]
    rfl
  let removedFactors (z : ℂ) := ∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹
  have hP : Differentiable ℂ removedFactors := Differentiable.fun_finsetProd fun v _ ↦
    (globalConverse_nontrivial_strip_bounds_factor χ v).1
  let D := removedFactors * L
  have han : AnalyticOnNhd ℂ D univ := fun z _ ↦ (hP.mul hL).analyticAt z
  refine ⟨D, han, ?_, ?_, ?_⟩
  · let d := ∏ v ∈ S, (1 - (q(v) : ℝ) ^ (-(2 : ℝ)))
    have hdv (v : V) : 0 < 1 - (q(v) : ℝ) ^ (-(2 : ℝ)) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v) (by norm_num))
    have hd : 0 < d := Finset.prod_pos (fun v _ ↦ hdv v)
    let Z := max 1 ‖dedekindZeta F (2 : ℝ)‖
    have hZ : 0 < Z := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨d / Z, div_pos hd hZ, fun z hz ↦ ?_⟩
    have h := (finiteHeckeL_zeroFreeRegion_euler F χ ⟨z, one_lt_two.trans_le hz⟩
      (y := 2) one_lt_two hz).2
    rw [← hs] at h
    have hl : 1 / Z ≤ ‖L z‖ := (div_le_iff₀ hZ).mpr
      (h.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)))
    have hp : d ≤ ‖removedFactors z‖ := by
      dsimp only [removedFactors, d]; rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun v _ ↦ (hdv v).le)
      intro v _
      refine (sub_le_sub_left ?_ _).trans ((globalConverse_nontrivial_strip_bounds_factor χ v).2 z).1
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le) (neg_le_neg hz)
    simpa only [D, Pi.mul_apply, norm_mul, div_eq_mul_inv, one_mul] using
      mul_le_mul hp hl (by positivity) (norm_nonneg _)
  · intro b hb
    obtain ⟨p, hp, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hNF hs (-4) (b + 6) (by linarith)
    obtain ⟨C, hC, hbound⟩ := Asymptotics.isBigO_iff'.mp hO
    rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hbound
    obtain ⟨t, ht⟩ := hbound
    let m := ⌈p⌉₊
    let heightCutoff := max t 1
    let rect := Complex.reProdIm (Icc (-4 : ℝ) (b + 6)) (Icc (-heightCutoff) heightCutoff)
    obtain ⟨K, hK⟩ := (isCompact_Icc.reProdIm isCompact_Icc).bddAbove_image
      (f := fun z : ℂ ↦ ‖L z‖) hL.continuous.norm.continuousOn (K := rect)
    let Q := ∏ v ∈ S, (1 + (q(v) : ℝ) ^ (4 : ℝ))
    have hQ : 1 ≤ Q := Finset.one_le_prod₀ fun v _ ↦ le_add_of_nonneg_right
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    let C' := max 1 (max K C)
    have hC' : 1 ≤ C' := le_max_left _ _
    refine ⟨Q * C', one_le_mul_of_one_le_of_one_le hQ hC', m, fun z hz ↦ ?_⟩
    have hpz : ‖removedFactors z‖ ≤ Q := by
      dsimp only [removedFactors, Q]; rw [norm_prod]
      apply Finset.prod_le_prod₀ fun _ _ ↦ norm_nonneg _
      intro v _
      refine ((globalConverse_nontrivial_strip_bounds_factor χ v).2 z).2.trans (add_le_add_right ?_ _)
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le) (by linarith [hz.1])
    have hbz : 1 ≤ 1 + |z.im| := le_add_of_nonneg_right (abs_nonneg _)
    have hlz : ‖L z‖ ≤ C' * (1 + |z.im|) ^ m := by
      by_cases hy : |z.im| ≤ heightCutoff
      · exact (hK ⟨z, ⟨hz, abs_le.mp hy⟩, rfl⟩).trans (((le_max_left K C).trans (le_max_right _ _)).trans
          (le_mul_of_one_le_right (zero_le_one.trans hC') (one_le_pow₀ hbz)))
      · have ht' : t ≤ |z.im| := (le_max_left _ _).trans (le_of_not_ge hy)
        have h := ht _ ht' z rfl hz
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
        apply h.trans
        apply mul_le_mul ((le_max_right K C).trans (le_max_right _ _)) _ (by positivity) (zero_le_one.trans hC')
        calc
          _ ≤ (1 + |z.im|) ^ p := Real.rpow_le_rpow (abs_nonneg _) (by linarith) hp.le
          _ ≤ (1 + |z.im|) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hbz (Nat.le_ceil _)
          _ = _ := Real.rpow_natCast _ _
    simpa only [D, Pi.mul_apply, norm_mul, mul_assoc] using
      mul_le_mul hpz hlz (norm_nonneg _) (zero_le_one.trans hQ)
  · have hbase : sIdeleRestriction F S ⟨χ₀(χ), hc⟩ =
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η := by
      ext1 y
      have h := DFunLike.congr_fun hη y
      change _ = (η y : ℂ) * _ ^ (0 : ℂ) at h
      change _ = (η y : ℂ)
      simpa only [Complex.cpow_zero, mul_one] using h
    have hmass : (∏ᶠ v : {v : V // v ∉ S},
        (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
          (v.val.adicCompletionIntegers F).units).toReal : ℂ)) = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro v
      have hv := fun h ↦ v.property (hD v.val h)
      simp [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, multiplicity_eq_zero_of_not_dvd hv]
    have hw := weilIdentity_unramifiedOutside_meromorphic S g χ hc L hNF (fun z hz ↦ hs ⟨z, hz⟩)
    rw [hbase] at hw
    intro z hz
    have hloc := (sLocalIdelicZetaIntegral_analyticOn g η).differentiableOn.congr (fun w hw ↦
      sLocalIdelicZFunction_eq_integral g ⟨η, w, hw, rfl⟩)
    have hcont := (han z trivial).continuousAt.mul (hloc.continuousOn.continuousAt
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hz))
    apply tendsto_nhds_unique (l := 𝓝[≠] z) (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    apply ((globalIdelicZFunction_entire_of_nontrivial _ χ hnχ z).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr'
    filter_upwards [nhdsNE_le_codiscrete z hw] with w h
    rw [h, hmass, one_mul]
    change _ = (removedFactors w * L w) * _
    ring

/-- The extra imaginary-height weights needed for division are absorbed by the
ordinary Schwartz–Bergman seminorms, also after reflecting the argument. -/
private theorem globalConverse_nontrivial_strip_bounds_weight (f : ℂ → ℂ)
    (hf : f ∈ schwartzBergmanSubmodule univ) (a b : ℝ) (hab : a ≤ b) (N n : ℕ) :
    ∃ A : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → (1 + |z.im|) ^ n * ‖z ^ N * f z‖ ≤ A := by
  obtain ⟨C, hC⟩ := hf.2.2 a b hab (subset_univ _) N
  obtain ⟨E, hE⟩ := hf.2.2 a b hab (subset_univ _) (n + N)
  refine ⟨2 ^ n * max C E, fun z hz ↦ ?_⟩
  have hi := Complex.abs_im_le_norm z
  rcases le_total ‖z‖ 1 with h | h
  · exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _)
      ((hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  · calc
      _ ≤ (2 * ‖z‖) ^ n * ‖z ^ N * f z‖ := by gcongr; linarith
      _ = 2 ^ n * ‖z ^ (n + N) * f z‖ := by simp only [mul_pow, pow_add, norm_mul, norm_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hE (mem_image_of_mem _ hz)).trans (le_max_right _ _)) (by positivity)

/-- For an entire multiplier whose product with the completed Hecke function is
Schwartz on strips, the two multiplied local zeta coordinates of a normalized
test have rapid decay on closed substrips of their respective half-planes.
The stage contains the different, so insertion commutes with Fourier transformation.
On pp. 306 and 308 the reciprocal estimates on selected horizontal segments do
not by themselves give these bounds at all heights. Uniform division estimates
on the right and reflected left half-planes would suffice. -/
private theorem globalConverse_nontrivial_strip_bounds (χ : U) (hχ : χ₁(χ) ≠ 1)
    (S : Finset V) (hD : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (hc : χ₀(χ) ∈ unramifiedOutside F S) (η : PontryaginDual (SIdeleQuotient F S))
    (hη : sIdeleRestriction F S ⟨χ₀(χ), hc⟩ = normChartₛ(η) 0)
    (g : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hg : ∀ s : halfPlane, globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S g)
      (ideleClassNormTwist χ s) = completedHeckeL χ s)
    (u : ℂ → ℂ) (hu : Differentiable ℂ u)
    (hB : (continuedCompletedHeckeL χ * u) ∈ schwartzBergmanSubmodule univ) :
    let p := sLocalZetaPair η (Submodule.Quotient.mk g)
    ∀ a b : ℝ, a ≤ b → ∀ N : ℕ,
      (0 < a → BddAbove ((fun z : ℂ ↦ ‖z ^ N * (u z * p.1.val z)‖) '' (Complex.re ⁻¹' Icc a b))) ∧
      (b < 1 → BddAbove ((fun z : ℂ ↦ ‖z ^ N * (u z * p.2.val z)‖) '' (Complex.re ⁻¹' Icc a b))) := by
  let G := sAdeleSchwartzToGlobal F S g
  let p := sLocalZetaPair η (Submodule.Quotient.mk g)
  have hZ : (fun z ↦ globalIdelicZFunction G (ideleClassNormTwist χ z)) = continuedCompletedHeckeL χ :=
    eq_of_agree_rightHalf (globalIdelicZFunction_meromorphic G χ) (continuedCompletedHeckeL_spec χ).1 1
      (fun z hz ↦ (globalIdelicZFunction_eq_integral G (globalTwist_mem_rightHalf χ hz)).trans
        ((hg ⟨z, hz⟩).trans ((continuedCompletedHeckeL_spec χ).2 ⟨z, hz⟩).symm))
  have hop : IsOpen (Complex.re ⁻¹' Ioi 0) := isOpen_Ioi.preimage Complex.continuous_re
  dsimp only
  intro a b hab N
  constructor
  · intro ha
    obtain ⟨D, han, hlo, hup, he⟩ := globalConverse_nontrivial_strip_bounds_euler χ hχ S hD hc η hη g
    let v (z : ℂ) := z ^ N * (u z * p.1.val z)
    apply globalConverse_nontrivial_strip_bounds_divide D v han _ hlo hup _ a b ha hab
    · exact ((differentiable_id.pow N).differentiableOn.mul
        (hu.differentiableOn.mul p.1.property.2.1)).analyticOnNhd hop
    · intro l r hl hlr n
      obtain ⟨A, hA⟩ := globalConverse_nontrivial_strip_bounds_weight _ hB l r hlr N n
      refine ⟨A, fun w hw ↦ ?_⟩
      have h := (he w (hl.trans_le hw.1)).trans (congrFun hZ w)
      have hloc : p.1.val w = sLocalIdelicZFunction g (normChartₛ(η) w) :=
        (sLocalZetaPair_mk η g).1 (hl.trans_le hw.1)
      rw [← hloc] at h
      have eq : D w * v w = w ^ N * ((continuedCompletedHeckeL χ * u) w) := by
        change D w * (w ^ N * (u w * p.1.val w)) = w ^ N * (continuedCompletedHeckeL χ w * u w)
        rw [← h]; ring
      simpa only [eq] using hA w hw
  · intro hb
    have hi (x : C𝔽) : χ₀(χ⁻¹) x = (χ₀(χ) x)⁻¹ := by
      change ((χ x : ℂ)⁻¹ * _ ^ (0 : ℂ)) = ((χ x : ℂ) * _ ^ (0 : ℂ))⁻¹
      simp
    have hci : χ₀(χ⁻¹) ∈ unramifiedOutside F S := by
      rw [mem_unramifiedOutside_iff] at hc ⊢
      intro v hv y
      have h := hc v hv y
      exact (hi _).trans (by rw [show χ₀(χ) _ = 1 from h, inv_one])
    have hηi : sIdeleRestriction F S ⟨χ₀(χ⁻¹), hci⟩ = normChartₛ(η⁻¹) 0 := by
      ext1 x
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
      have h := DFunLike.congr_fun hη (QuotientGroup.mk t)
      rw [sIdeleRestriction_mk] at h ⊢
      rw [hi, h]
      change ((η _ : ℂ) * _ ^ (0 : ℂ))⁻¹ = (η _ : ℂ)⁻¹ * _ ^ (0 : ℂ)
      simp
    have hχi : χ₁(χ⁻¹) ≠ 1 := by
      intro h
      apply hχ
      ext1 x
      have e := DFunLike.congr_fun h x
      change (χ x.val)⁻¹ = 1 at e
      exact inv_eq_one.mp e
    let g' := sAdeleSchwartzFourier g
    obtain ⟨D, han, hlo, hup, he⟩ :=
      globalConverse_nontrivial_strip_bounds_euler χ⁻¹ hχi S hD hci η⁻¹ hηi g'
    have hfour : adeleSchwartzFourier G = sAdeleSchwartzToGlobal F S g' :=
      adeleSchwartzFourier_sAdeleSchwartzToGlobal_of_different F S hD g g' rfl
    have hzref (w : ℂ) : globalIdelicZFunction (sAdeleSchwartzToGlobal F S g') (ideleClassNormTwist χ⁻¹ w) =
        continuedCompletedHeckeL χ (1 - w) := by
      rw [← congrFun hZ (1 - w), globalIdelicZFunction_functionalEquation G, hfour]
      congr 1
      ext1 x
      let q : ℂ := (((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ)
      have hq : q ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F x).ne_zero)
      change _ = q * ideleClassNormTwist χ (1 - w) x⁻¹
      rw [map_inv]
      change (χ x : ℂ)⁻¹ * q ^ w = q * ((χ x : ℂ) * q ^ (1 - w))⁻¹
      rw [Complex.cpow_sub 1 w hq, Complex.cpow_one]
      field_simp
    let v (w : ℂ) := (1 - w) ^ N * (u (1 - w) * p.2.val (1 - w))
    have href (w : ℂ) (hw : 0 < w.re) : (1 - w).re < 1 := by simpa using hw
    have hv : AnalyticOnNhd ℂ v (Complex.re ⁻¹' Ioi 0) := by
      have h := ((differentiable_id.pow N).differentiableOn.mul
        (hu.differentiableOn.mul p.2.property.2.1)).analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re)
      exact fun w hw ↦ (h _ (href w hw)).comp (analyticAt_const.sub analyticAt_id)
    have bound := globalConverse_nontrivial_strip_bounds_divide D v han hv hlo hup (fun l r hl hlr n ↦ by
      obtain ⟨A, hA⟩ := globalConverse_nontrivial_strip_bounds_weight
        _ hB (1 - r) (1 - l) (sub_le_sub_left hlr _) N n
      refine ⟨A, fun w hw ↦ ?_⟩
      have h := (he w (hl.trans_le hw.1)).trans (hzref w)
      have hloc : p.2.val (1 - w) = sLocalIdelicZFunction g' (normChartₛ(η⁻¹) (1 - (1 - w))) :=
        (sLocalZetaPair_mk η g).2 (href w (hl.trans_le hw.1))
      rw [sub_sub_cancel] at hloc
      have eq : D w * v w = (1 - w) ^ N * ((continuedCompletedHeckeL χ * u) (1 - w)) := by
        change D w * ((1 - w) ^ N * (u (1 - w) * p.2.val (1 - w))) =
          (1 - w) ^ N * (continuedCompletedHeckeL χ (1 - w) * u (1 - w))
        rw [← (show D w * p.2.val (1 - w) = continuedCompletedHeckeL χ (1 - w) from
          (congrArg (D w * ·) hloc).trans h)]
        ac_rfl
      rw [eq]
      simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hA (1 - w)
        (show (1 - w).re ∈ Icc (1 - r) (1 - l) from ⟨sub_le_sub_left hw.2 _, sub_le_sub_left hw.1 _⟩))
      (1 - b) (1 - a) (sub_pos.mpr hb) (sub_le_sub_left hab _)
    apply bound.mono
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨1 - w, ⟨sub_le_sub_left hw.2 _, sub_le_sub_left hw.1 _⟩, ?_⟩
    simp only [v, p, sub_sub_cancel]

/-- Multiply both coordinates of the normalized local pair by the same entire
function. The local functional equation survives, so the local converse supplies
a test. Weil's identity then identifies its global transform near two. -/
private theorem globalConverse_nontrivial_realize (χ : U) (hχ : χ₁(χ) ≠ 1) (b : B)
    (u : ℂ → ℂ) (hu : Differentiable ℂ u) (hb : ∀ z, b.val z = continuedCompletedHeckeL χ z * u z) :
    ∃ f : ℬ, (fun z ↦ Z(f, χ, z)) = b.val := by
  classical
  obtain ⟨f₀, hf₀⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL χ
  obtain ⟨A, k, hk⟩ := sAdeleSchwartzToGlobal_exhaustive F f₀
  obtain ⟨R, hR⟩ : ∃ R : Finset V, χ₀(χ) ∈ unramifiedOutside F R := by
    apply mem_iUnion.mp
    rw [iUnion_unramifiedOutside]
    trivial
  have hdiff : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  let D := (Ideal.finite_factors hdiff).toFinset
  let S := A ∪ (R ∪ D)
  have hAS : A ⊆ S := Finset.subset_union_left
  have hD (v : V) (hv : v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) : v ∈ S :=
    Finset.mem_union_right _ (Finset.mem_union_right _ (by simpa [D] using hv))
  have hc : χ₀(χ) ∈ unramifiedOutside F S := fun v hv ↦
    hR v fun h ↦ hv (Finset.mem_union_right _ (Finset.mem_union_left _ h))
  let g := sAdeleSchwartzTransition F hAS k
  have hg : sAdeleSchwartzToGlobal F S g = f₀ :=
    (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hAS) k).trans hk
  obtain ⟨η, hη⟩ := heckeEulerProductOutside_eq_finite_unitary S χ hc
  let p := sLocalZetaPair η (Submodule.Quotient.mk g)
  have bound := globalConverse_nontrivial_strip_bounds χ hχ S hD hc η hη g (hg ▸ hf₀) u hu
    (show continuedCompletedHeckeL χ * u ∈ schwartzBergmanSubmodule univ from
      (show b.val = continuedCompletedHeckeL χ * u from funext hb) ▸ b.property)
  have mk {I : Set ℝ} (v : SchwartzBergman I)
      (h : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ N * (u z * v.val z)‖) '' (Complex.re ⁻¹' Icc a b))) :
      u * v.val ∈ schwartzBergmanSubmodule I := by
    refine ⟨fun z hz ↦ ?_, hu.differentiableOn.mul v.property.2.1, h⟩
    change u z * v.val z = 0
    rw [show v.val z = 0 from v.property.1 hz, mul_zero]
  let q : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) :=
    (⟨_, mk p.1 fun a b hab hs N ↦ (bound a b hab N).1 (hs (left_mem_Icc.mpr hab))⟩,
     ⟨_, mk p.2 fun a b hab hs N ↦ (bound a b hab N).2 (hs (right_mem_Icc.mpr hab))⟩)
  have hp : p ∈ sLocalZetaMatching η := (sLocalZetaPair_range η) ▸
    (show p ∈ (sLocalZetaPair η).range from ⟨_, rfl⟩)
  have hq : q ∈ (sLocalZetaPair η).range := by
    rw [sLocalZetaPair_range, mem_sLocalZetaMatching]
    intro z hz
    change u z * p.1.val z = _ * (u z * p.2.val z)
    rw [(mem_sLocalZetaMatching η p).mp hp hz, mul_left_comm]
  obtain ⟨x, hx⟩ := hq
  obtain ⟨f, rfl⟩ : ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)), Submodule.Quotient.mk f = x :=
    Submodule.Quotient.mk_surjective _ x
  refine ⟨sAdeleSchwartzToGlobal F S f, ?_⟩
  have hlocal (z : ℂ) (hz : 0 < z.re) :
      sLocalIdelicZFunction f (normChartₛ(η) z) = u z * sLocalIdelicZFunction g (normChartₛ(η) z) := by
    have h := congrArg (fun v : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) ↦ v.1.val z) hx
    exact ((sLocalZetaPair_mk η f).1 hz).symm.trans (h.trans (congrArg (u z * ·) ((sLocalZetaPair_mk η g).1 hz)))
  obtain ⟨L, hL, hLe⟩ := finiteHeckeL_exists_continuation χ
  have hW := fun v ↦ weilIdentity_unramifiedOutside_meromorphic S v χ hc L hL (fun z hz ↦ hLe ⟨z, hz⟩)
  have hbase : sIdeleRestriction F S ⟨χ₀(χ), hc⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η := by
    ext1 y
    have hy := DFunLike.congr_fun hη y
    change _ = (η y : ℂ) * _ ^ (0 : ℂ) at hy
    change _ = (η y : ℂ)
    simpa only [Complex.cpow_zero, mul_one] using hy
  -- Compare on a punctured neighborhood of two, where the normalization is known.
  have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hf := globalIdelicZFunction_entire_of_nontrivial (sAdeleSchwartzToGlobal F S f) χ
    (fun h ↦ hχ (PontryaginDual.ext fun y ↦ DFunLike.congr_fun h y))
  have hbd : Differentiable ℂ b.val := fun z ↦ (b.property.2.1 z (by simp)).differentiableAt (by simp)
  apply (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_frequently_eq
    (hbd.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2 : ℂ))
  apply Filter.Eventually.frequently
  filter_upwards [nhdsNE_le_codiscrete (2 : ℂ) (hW f), nhdsNE_le_codiscrete (2 : ℂ) (hW g),
    hn.filter_mono nhdsWithin_le_nhds] with z h₁ h₂ hz
  rw [hbase] at h₁ h₂
  have he : Z(sAdeleSchwartzToGlobal F S g, χ, z) = continuedCompletedHeckeL χ z :=
    (globalIdelicZFunction_eq_integral _ (globalTwist_mem_rightHalf χ hz)).trans
      ((hg ▸ hf₀ ⟨z, hz⟩).trans ((continuedCompletedHeckeL_spec χ).2 ⟨z, hz⟩).symm)
  rw [h₁, hb, ← he, h₂, hlocal z (zero_lt_one.trans hz)]
  ring

/-- Paper: Theorem 6.3.2.1(1), p. 304, equation (6.3.2.3).
On a nontrivial norm-one component the global Mellin transform is a closed
topological embedding with range the completed Hecke principal ideal in the
Schwartz–Bergman space. -/
theorem globalConverse_nontrivial (χ : U) (_hχ : χ₁(χ) ≠ 1) :
    ∃ ZB : Θ(χ₁(χ)) →L[ℂ] B, IsClosedEmbedding ZB ∧
      (∀ (f : ℬ) s, (ZB ((K(χ₁(χ))).mkQ f)).val s = Z(f, χ, s)) ∧
      Set.range ZB = bergmanIdeal(continuedCompletedHeckeL χ) := by
  obtain ⟨A, hi, hA⟩ := globalConverse_nontrivial_evaluations χ _hχ
  have hB (x : Θ(χ₁(χ))) : A x ∈ schwartzBergmanSubmodule univ := by
    obtain ⟨f, rfl⟩ := (K(χ₁(χ))).mkQ_surjective x
    rw [funext (hA f)]
    exact globalConverse_nontrivial_bergman χ _hχ f
  let T : Θ(χ₁(χ)) →ₗ[ℂ] B := A.toLinearMap.codRestrict _ hB
  have hiT : Injective T := fun x y he ↦ hi (congrArg Subtype.val he)
  have hc : Continuous (fun b : B ↦ b.val) := continuous_pi fun z ↦ by
    simpa only [iteratedDeriv_zero] using globalConverse_nontrivial_jets z 0
  have hg : IsClosed (T.graph : Set (Θ(χ₁(χ)) × B)) := by
    rw [show (T.graph : Set (Θ(χ₁(χ)) × B)) = {p | p.2.val = A p.1} from
      Set.ext fun p ↦ (T.mem_graph_iff p).trans (show p.2 = T p.1 ↔ p.2.val = (T p.1).val from Subtype.ext_iff)]
    exact isClosed_eq (hc.comp continuous_snd) (A.continuous.comp continuous_fst)
  have hr : Set.range T = bergmanIdeal(continuedCompletedHeckeL χ) := by
    ext b
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨f, rfl⟩ := (K(χ₁(χ))).mkQ_surjective x
      obtain ⟨u, hu, he⟩ := globalConverse_nontrivial_factor χ _hχ f
      exact ⟨u, hu, fun z ↦ (hA f z).trans (he z)⟩
    · rintro ⟨u, hu, hb⟩
      obtain ⟨f, hf⟩ := globalConverse_nontrivial_realize χ _hχ b u hu hb
      exact ⟨_, Subtype.ext ((funext (hA f)).trans hf)⟩
  have hL := completedHeckeL_continuation_entire χ _ (continuedCompletedHeckeL_spec χ).1
    (continuedCompletedHeckeL_spec χ).2 (fun h ↦ _hχ (PontryaginDual.ext fun x ↦ DFunLike.congr_fun h x))
  have emb := globalConverse_nontrivial_embedding (globalHomogeneousThetaSpace_nuclearFrechet.{_, 0} χ₁(χ)).1
    (schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty) T hiT hg
    (hr ▸ globalConverse_nontrivial_closed hL)
  exact ⟨⟨T, emb.continuous⟩, emb, hA, hr⟩

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


/-- A norm twist runs through the entire trivial norm-one component. The values on the
half-plane of convergence therefore detect its homogeneous theta kernel. -/
private theorem globalConverse_normTwist_kernel (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (f : ℬ) :
    f ∈ K(1) ↔ ∀ s : ℂ, 1 < s.re → Z(f, χ, s) = 0 := by
  have hres (η : U) (s : ℂ) (u : C₁) :
      normOneRestriction (ideleClassNorm F) (ideleClassNormTwist η s) u = (η u.val : ℂ) :=
    normOneRestriction_unitaryChart _ (isProperMap_ideleClassNorm F).continuous η s u
  have hshift (s : ℂ) : ideleClassNormTwist χ s = ideleClassNormTwist (1 : U) (shift(t) + s) := by
    simpa only [zero_add] using ideleClassNormTwist_add_of_eq ht s
  refine (mem_homogeneousAdelicTheta_ker_iff 1 f).trans ?_
  constructor
  · intro h s hs
    apply h ⟨_, globalOrderBound_rightHalf χ hs⟩
    intro u
    change normOneRestriction _ (ideleClassNormTwist χ s) u = _
    rw [hshift]
    exact hres 1 _ u
  · intro h c hc
    obtain ⟨η, z, he⟩ := exists_ideleClassNormTwist (F := F) c.val
    have hη : χ₁(η) = 1 := by
      ext u
      exact (hres η z u).symm.trans (he ▸ hc u)
    obtain ⟨v, hv⟩ := (globalConverse_existsUnique_normTwist η hη).exists
    have e := ideleClassNormTwist_add_of_eq hv z
    rw [zero_add, he] at e
    have e' : ideleClassNormTwist χ (shift(v) + z - shift(t)) = c.val := by
      rw [hshift, e]
      congr 1
      ring
    change globalIdelicZFunction f c.val = 0
    rw [← e']
    exact congrFun (eq_of_agree_rightHalf (globalIdelicZFunction_meromorphic f χ)
      (show MeromorphicNFOn (0 : ℂ → ℂ) univ from fun _ _ ↦ analyticAt_const.meromorphicNFAt) 1 h) _

/-- The real vertical trace differentiates by one factor of I at each step. This and the
following jet and divisibility arguments also occur in the principal-value theorem below. -/
private theorem globalConverse_normTwist_vertical_deriv (b : B) (a : (univ : Set ℝ))
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ b.val ((a.val : ℂ) + (y : ℂ) * Complex.I)) x =
      Complex.I ^ n * iteratedDeriv n b.val ((a.val : ℂ) + (x : ℂ) * Complex.I) := by
  let L (z : ℂ) := (a.val : ℂ) + z * Complex.I
  have hL (z : ℂ) : HasDerivAt L Complex.I z := by
    change HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I z
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id z).mul_const Complex.I).const_add (a.val : ℂ)
  have ha : AnalyticOnNhd ℂ b.val univ :=
    fun z _ ↦ (show Differentiable ℂ b.val from fun w ↦
      (b.property.2.1 w (by simp)).differentiableAt (by simp)).analyticAt z
  have hn (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k b.val) univ := by
    rw [iteratedDeriv_eq_iterate]
    exact ha.iterated_deriv k
  change iteratedDeriv n (fun y : ℝ ↦ b.val (L y)) x = Complex.I ^ n * iteratedDeriv n b.val (L x)
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    have hx : L x ∈ univ := mem_univ _
    have hh : HasDerivAt (iteratedDeriv k b.val) (iteratedDeriv (k + 1) b.val (L x)) (L x) := by
      rw [iteratedDeriv_succ]
      exact (hn k (L x) hx).differentiableAt.hasDerivAt
    have he : (iteratedDeriv k (fun y : ℝ ↦ b.val (L y))) =
        fun y : ℝ ↦ Complex.I ^ k * iteratedDeriv k b.val (L y) := funext ih
    have hdiff : HasDerivAt (fun y : ℝ ↦ Complex.I ^ k * iteratedDeriv k b.val (L y))
        (Complex.I ^ k * (iteratedDeriv (k + 1) b.val (L x) * Complex.I)) x :=
      (((hh.comp (x : ℂ) (hL x)).comp_ofReal).const_mul (Complex.I ^ k))
    rw [iteratedDeriv_succ, he]
    exact hdiff.deriv.trans (by ring)

/-- Iterated differentiation followed by evaluation is continuous in the Schwartz topology. -/
private theorem globalConverse_normTwist_schwartz_deriv_continuous (n : ℕ) :
    Continuous (fun f : SchwartzMap ℝ ℂ ↦ iteratedDeriv n (f : ℝ → ℂ)) := by
  have h (n : ℕ) : ∀ f : SchwartzMap ℝ ℂ,
      (⇑((SchwartzMap.derivCLM ℂ ℂ)^[n] f) : ℝ → ℂ) = iteratedDeriv n (f : ℝ → ℂ) := by
    induction n with
    | zero => intro f; simp [iteratedDeriv_zero]
    | succ k ih =>
      intro f
      rw [Function.iterate_succ_apply', iteratedDeriv_succ, ← ih f]
      exact funext (SchwartzMap.derivCLM_apply ℂ ((SchwartzMap.derivCLM ℂ ℂ)^[k] f))
  simp_rw [← h]
  have hc : Continuous (fun f : SchwartzMap ℝ ℂ ↦ (f : ℝ → ℂ)) :=
    continuous_pi fun x ↦ ((continuous_eval_const (F := BoundedContinuousFunction ℝ ℂ) x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous)
  exact hc.comp ((SchwartzMap.derivCLM ℂ ℂ).continuous.iterate n)

/-- The Schwartz-line realization of a Bergman function makes each complex jet continuous. -/
private theorem globalConverse_normTwist_continuous_jet (s : ℂ) (n : ℕ) :
    Continuous (fun b : B ↦ iteratedDeriv n b.val s) := by
  obtain ⟨T, hT, hE⟩ := schwartzBergman_schwartzLine_topology (univ : Set ℝ) isOpen_univ
    ordConnected_univ univ_nonempty
  let a : (univ : Set ℝ) := ⟨s.re, mem_univ _⟩
  have hL : (a.val : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  have hTeq (b : B) : ⇑(T b a) = fun y : ℝ ↦ b.val ((a.val : ℂ) + (y : ℂ) * Complex.I) := by
    funext y
    simpa only [weightedVerticalTrace, pow_zero, one_mul] using hT b a y
  have hC : Continuous (fun b : B ↦ iteratedDeriv n ((T b a : SchwartzMap ℝ ℂ) : ℝ → ℂ) s.im) :=
    (continuous_apply s.im).comp ((globalConverse_normTwist_schwartz_deriv_continuous n).comp
      ((continuous_apply a).comp hE.continuous))
  apply (hC.const_mul ((Complex.I ^ n)⁻¹)).congr
  intro b
  rw [hTeq, globalConverse_normTwist_vertical_deriv b a n, hL,
    inv_mul_cancel_left₀ (pow_ne_zero _ Complex.I_ne_zero)]

/-- The order inequalities remove all singularities of the quotient. -/
private theorem globalConverse_normTwist_factor {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ z, f z = g z * u z) ↔
      ∀ z, analyticOrderAt g z ≤ analyticOrderAt f z := by
  constructor
  · rintro ⟨u, hu, he⟩ z
    rw [show f = g * u from funext he, analyticOrderAt_mul (hg.analyticAt z) (hu.analyticAt z)]
    exact self_le_add_right _ _
  · intro hord
    let q := f / g
    have hq : MeromorphicOn q univ := fun z _ ↦ (hf.analyticAt z).meromorphicAt.div (hg.analyticAt z).meromorphicAt
    have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
      intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hg.analyticAt z).meromorphicAt,
        (hf.analyticAt z).meromorphicOrderAt_eq, (hg.analyticAt z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt f z = m at hle ⊢
      generalize analyticOrderAt g z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    refine ⟨_, hdiff, fun z ↦ ?_⟩
    by_cases hz : g z = 0
    · have hpos := lt_of_lt_of_le (pos_iff_ne_zero.mpr ((hg.analyticAt z).analyticOrderAt_ne_zero.mpr hz))
          (hord z)
      rw [hz, zero_mul]
      exact (hf.analyticAt z).analyticOrderAt_ne_zero.mp hpos.ne'
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((hf.analyticAt z).div (hg.analyticAt z) hz).meromorphicNFAt]
      exact (mul_div_cancel₀ _ hz).symm

/-- Each vanishing jet is a closed condition in the Schwartz–Bergman topology. -/
private theorem globalConverse_normTwist_closed {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) : IsClosed bergmanIdeal(g) := by
  have hdiff (f : B) : Differentiable ℂ f.val := fun w ↦
    (f.property.2.1 w (by simp)).differentiableAt (by simp)
  have hset : bergmanIdeal(g) = ⋂ (z : ℂ) (n : ℕ) (_ : (n : ℕ∞) ≤ analyticOrderAt g z)
      (i : ℕ) (_ : i < n), {f : B | iteratedDeriv i f.val z = 0} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter, globalConverse_normTwist_factor (hdiff f) hg]
    apply forall_congr'
    intro z
    rw [← ENat.forall_natCast_le_iff_le]
    simp_rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hdiff f).analyticAt z)]
  rw [hset]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
      isClosed_eq (globalConverse_normTwist_continuous_jet z i) continuous_const

/-- The two zeros of the shifted pole polynomial cancel the simple poles of the completion. -/
private theorem globalConverse_normTwist_regular (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    Differentiable ℂ (regularizedL(χ, t)) ∧
      ∀ z, polePolynomial(t) z = 0 → meromorphicOrderAt (regularizedL(χ, t)) z = 0 := by
  let b := shift(t)
  let p := polePolynomial(t)
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext x
    have he := DFunLike.congr_fun ht x.val
    change (χ x.val : ℂ) * _ ^ (0 : ℂ) = 1 * ((((ideleClassNorm F x.val).val : ℝ) : ℂ) ^ b) at he
    rw [Complex.cpow_zero, mul_one, show ideleClassNorm F x.val = 1 from x.property,
      Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul] at he
    exact he
  have hω : χ₁(χ) = 1 := PontryaginDual.ext fun x ↦ DFunLike.congr_fun hk x
  obtain ⟨u, ⟨hchar, hzero, hone, haway⟩, -⟩ := completedHeckeL_continuation_simplePoles χ L hL hEq hk
  have hu : t = -u := (globalConverse_existsUnique_normTwist χ hω).unique ht (by
    convert hchar using 2
    push_cast
    ring)
  have hb : b = -(Complex.I * (u : ℂ)) := by dsimp [b]; rw [hu]; push_cast; ring
  have hp (s : ℂ) : AnalyticAt ℂ p s := by dsimp [p]; fun_prop
  have hmer : MeromorphicOn (p * L) univ := fun s hs ↦ (hp s).meromorphicAt.mul (hL hs).meromorphicAt
  have hD (s : ℂ) : HasDerivAt p ((1 - s - b) - (s + b)) s := by
    simpa [p, b, sub_eq_add_neg] using ((hasDerivAt_id s).add_const b).fun_mul
      (((hasDerivAt_const s (1 : ℂ)).fun_sub (hasDerivAt_id s)).sub_const b)
  have hcancel (z : ℂ) (hz : p z = 0) : meromorphicOrderAt (regularizedL(χ, t)) z = 0 := by
    have hroots : z = -b ∨ z = 1 - b := by
      rcases mul_eq_zero.mp hz with h | h
      · left; linear_combination h
      · right; linear_combination -h
    have hd : (1 - z - b) - (z + b) ≠ 0 := by
      rcases hroots with rfl | rfl <;> ring_nf <;> norm_num
    have ho : meromorphicOrderAt L z = -1 := by
      rcases hroots with rfl | rfl
      · simpa [hb] using hzero
      · simpa [hb] using hone
    have h1 := (hp z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz (by rwa [(hD z).deriv])
    change meromorphicOrderAt (toMeromorphicNFOn (p * L) univ) z = 0
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z),
      meromorphicOrderAt_mul (hp z).meromorphicAt (hL (mem_univ z)).meromorphicAt,
      (hp z).meromorphicOrderAt_eq, h1, ho]
    norm_num
  refine ⟨fun z ↦ AnalyticAt.differentiableAt ?_, hcancel⟩
  apply (meromorphicNFOn_toMeromorphicNFOn (p * L) univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_cases hz : p z = 0
  · exact (hcancel z hz).ge
  rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z)]
  apply ((hp z).mul (haway z ?_)).meromorphicOrderAt_nonneg
  rintro (rfl | hz')
  · exact hz (by change (_ + b) * (1 - _ - b) = 0; rw [hb]; ring)
  · rw [Set.mem_singleton_iff] at hz'
    exact hz (by change (_ + b) * (1 - _ - b) = 0; rw [hz', hb]; ring)

/-- In logarithmic norm coordinates the derivative of theta is theta of the
directional derivative. This is the global version of the radial calculation in §3.3. -/
private theorem globalConverse_normTwist_radial_deriv (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (f : ℬ) (x : ℝ) :
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let q (u : ℝ≥0ˣ) : C𝔽 := QuotientGroup.mk (τ u)
    HasDerivAt (fun y : ℝ ↦ homogeneousAdelicTheta 1 f (q (e y)))
      (homogeneousAdelicTheta 1 (adeleDirectionalDeriv τ f) (q (e x))) x := by
  intro e q
  have h0 : e 0 = 1 := Units.ext (NNReal.coe_inj.mp Real.exp_zero)
  have hE : Tendsto e (𝓝[≠] 0) (𝓝[≠] 1) := by
    rw [← h0]
    refine tendsto_nhdsWithin_iff.mpr ⟨e.continuous.continuousAt.continuousWithinAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := ({0} : Set ℝ)ᶜ)] with u hu
    exact fun he ↦ hu (e.injective he)
  have h := (homogeneousAdelicTheta_directionalDeriv τ 1 f (q (e x))).comp hE
  have he : HasDerivAt (fun t : ℝ ↦ (Real.exp t : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_exp 0).ofReal_comp
  have hd := h.mul he.tendsto_slope
  rw [mul_one] at hd
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ)] with y hy
  have hn : (Real.exp y : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ hy (Real.exp_injective
    ((Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)).trans Real.exp_zero.symm))
  have hxy : q (e y) * q (e x) = q (e (x+y)) := by
    change QuotientGroup.mk (τ (e y) * τ (e x)) = _
    apply (congrArg (fun z : IdeleGroup (𝓞 F) F ↦ (QuotientGroup.mk z : C𝔽)) (map_mul τ (e y) (e x)).symm).trans
    exact congrArg q (Units.ext (NNReal.coe_inj.mp ((Real.exp_add y x).symm.trans (by rw [add_comm]; rfl))))
  change ((_ - _) / ((Real.exp y : ℂ) - 1)) * slope (fun t : ℝ ↦ (Real.exp t : ℂ)) 0 y = _
  simp only [slope_def_module, sub_zero, Real.exp_zero, Complex.ofReal_one, Complex.real_smul]
  change ((homogeneousAdelicTheta 1 f (q (e y) * q (e x)) - _) / _) * _ = _
  rw [hxy]
  field_simp [hn]

/-- Every real exponential weight of a polar theta profile, including a fixed imaginary
twist, is Schwartz. Differentiating the weighted profile preserves polar tests, and
Theorem 2.2.5.4(4) absorbs each polynomial weight in its two-sided decay bound. -/
private theorem globalConverse_normTwist_weighted (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F)
    (hτ : RightInverse τ (ideleNorm F)) (f : P) (c : ℂ) :
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let q (x : ℝ) : C𝔽 := QuotientGroup.mk (τ (e x))
    ∃ g : SchwartzMap ℝ ℂ, ∀ x, g x = Complex.exp (c * x) * homogeneousAdelicTheta 1 f.val (q x) := by
  intro e q
  let θ (v : P) (x : ℝ) := homogeneousAdelicTheta 1 v.val (q x)
  let A (v : P) (x : ℝ) := Complex.exp (c * x) * θ v x
  let D (v : P) : P := c • v + ⟨adeleDirectionalDeriv τ v.val,
    adeleDirectionalDeriv_preserves_polarSubspace τ v.property⟩
  have hd (v : P) (x : ℝ) : HasDerivAt (A v) (A (D v) x) x := by
    apply ((((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c).cexp).mul
      (globalConverse_normTwist_radial_deriv τ v.val x)).congr_deriv
    let H := homogeneousAdelicThetaLinearMap F (1 : PontryaginDual C₁)
    have he : θ (D v) x = c * θ v x + H (adeleDirectionalDeriv τ v.val) (q x) :=
      congrArg (fun u : C(C𝔽, ℂ) ↦ u (q x))
        ((H.map_add _ _).trans (congrArg (· + H (adeleDirectionalDeriv τ v.val)) (H.map_smul c v.val)))
    change _ = Complex.exp _ * θ (D v) x
    rw [he]
    change _ * (c * 1) * θ v x + _ * H _ (q x) = _
    simp only [Complex.ofRealCLM_apply]
    ring
  have hi (n : ℕ) : iteratedDeriv n (A f) = A (D^[n] f) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']; exact funext fun x ↦ (hd _ x).deriv
  have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) (A f) := contDiff_of_differentiable_iteratedDeriv fun n _ ↦
    hi n ▸ fun x ↦ (hd _ x).differentiableAt
  refine ⟨⟨A f, hs, ?_⟩, fun _ ↦ rfl⟩
  intro k n
  let v := D^[n] f
  let N := ⌈|c.re|⌉₊ + k
  obtain ⟨C, T, hC, _, ht⟩ := homogeneousAdelicTheta_decay_both 1 v.val (Or.inl v.property) N
  have hct : Continuous (fun x : ℝ ↦ ‖x‖ ^ k * ‖A v x‖) :=
    (continuous_norm.pow k).mul (continuous_iff_continuousAt.mpr fun x ↦ (hd v x).continuousAt).norm
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc : IsCompact (Icc (-T) T)).bddAbove_image hct.continuousOn
  refine ⟨max B₀ C, fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hi]
  change ‖x‖ ^ k * ‖A v x‖ ≤ _
  by_cases hx : |x| ≤ T
  · exact (hB₀ ⟨x, abs_le.mp hx, rfl⟩).trans (le_max_left _ _)
  have hn : Real.log (((ideleClassNorm F (q x) : ℝ≥0) : ℝ)) = x := by
    change Real.log (((ideleNorm F (τ (e x)) : ℝ≥0) : ℝ)) = x
    exact (congrArg (fun u : ℝ≥0ˣ ↦ Real.log (u.val : ℝ)) (hτ (e x))).trans (Real.log_exp x)
  have hh := ht (q x) (show T < |Real.log (((ideleClassNorm F (q x)).val : ℝ))| by rw [hn]; exact lt_of_not_ge hx)
  change ‖θ v x‖ ≤ C * Real.exp (- (N : ℝ) * |Real.log (((ideleClassNorm F (q x)).val : ℝ))|) at hh
  rw [hn] at hh
  have hpow : ‖x‖ ^ k ≤ Real.exp ((k : ℝ) * |x|) := by
    rw [Real.exp_nat_mul, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [Real.add_one_le_exp |x|]) _
  have hcx : c.re * x ≤ |c.re| * |x| := (le_abs_self _).trans_eq (abs_mul _ _)
  have hN : |c.re| ≤ (⌈|c.re|⌉₊ : ℝ) := Nat.le_ceil _
  change ‖x‖ ^ k * ‖Complex.exp (c * x) * θ v x‖ ≤ _
  rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  apply le_trans _ (le_max_right B₀ C)
  calc
    _ ≤ Real.exp ((k : ℝ) * |x|) * (Real.exp (c.re*x) * (C * Real.exp (-(N : ℝ) * |x|))) :=
      mul_le_mul hpow (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le)
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (Real.exp_pos _).le
    _ = C * Real.exp (((k : ℝ) - N) * |x| + c.re * x) := by
      rw [sub_mul, sub_eq_add_neg, Real.exp_add, Real.exp_add, ← neg_mul]; ring
    _ ≤ C := mul_le_of_le_one_right hC.le (Real.exp_le_one_iff.mpr (by
      dsimp [N]; push_cast; nlinarith [mul_le_mul_of_nonneg_right hN (abs_nonneg x)]))

/-- The logarithmic substitution in the Mellin integral (Appendix B.2). -/
private theorem globalConverse_normTwist_log_integral (p : ℝ → ℂ) (s : ℂ) :
    mellin (fun t ↦ p (Real.log t)) s = ∫ x : ℝ, Complex.exp (s * x) * p x := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Positive multiplicative Haar measure is the image of Lebesgue measure by exp. -/
private theorem globalConverse_normTwist_log_haar (v : ℝ≥0ˣ → ℂ) :
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    ∫ u, v u ∂positiveRealHaar = ∫ x : ℝ, v (e x) := by
  intro e
  -- The units projection induces both the topology and the measurable space.
  let : BorelSpace ℝ≥0ˣ := by
    constructor
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℝ≥0) = _
    rw [Units.isEmbedding_val₀.eq_induced, borel_comap, BorelSpace.measurable_eq (α := ℝ≥0)]
  have hμ : positiveRealHaar = volume.map e := by
    apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
    exact funext fun x ↦ Units.ext (NNReal.coe_inj.mp (Real.coe_toNNReal _ (Real.exp_pos x).le))
  rw [hμ, e.measurableEmbedding.integral_map]

/-- Along a norm section the norm-twisted homogeneous integral is an ordinary Mellin integral. -/
private theorem globalConverse_normTwist_section_integral (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t)))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (f : ℬ) (s : ℂ) :
    let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let q (x : ℝ) : C𝔽 := QuotientGroup.mk (τ (e x))
    let θ (x : ℝ) := homogeneousAdelicTheta 1 f (q x)
    mellin (fun y ↦ Complex.exp (shift(t) * (Real.log y : ℝ)) * θ (Real.log y)) s =
      homogeneousThetaMellinIntegral τ 1 f (ideleClassNormTwist χ s) := by
  intro e q θ
  let v (u : ℝ≥0ˣ) := homogeneousAdelicTheta 1 f (QuotientGroup.mk (τ u)) *
    ideleClassNormTwist χ s (QuotientGroup.mk (τ u))
  have hshift : ideleClassNormTwist χ s = ideleClassNormTwist (1 : U) (shift(t) + s) := by
    simpa only [zero_add] using ideleClassNormTwist_add_of_eq ht s
  have hweight (x : ℝ) : ideleClassNormTwist χ s (q x) =
      Complex.exp (s * x) * Complex.exp (shift(t) * x) := by
    apply (DFunLike.congr_fun hshift (q x)).trans
    have hn : ideleClassNorm F (q x) = e x := hτ (e x)
    change 1 * ((((ideleClassNorm F (q x)).val : ℝ) : ℂ) ^ (shift(t) + s)) = _
    rw [hn, one_mul]
    change (Real.exp x : ℂ) ^ (shift(t) + s) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, ← Complex.exp_add]
    congr 1
    ring
  apply (globalConverse_normTwist_log_integral (fun x ↦ Complex.exp (shift(t) * x) * θ x) s).trans
  apply Eq.trans _ (globalConverse_normTwist_log_haar v).symm
  apply integral_congr_ae
  filter_upwards with x
  change Complex.exp (s * x) * (Complex.exp (shift(t) * x) * θ x) = θ x * ideleClassNormTwist χ s (q x)
  rw [hweight]
  ac_rfl

/-- The Fourier–Mellin isomorphism applied to the logarithmic theta profile
gives the Schwartz bounds on all vertical strips for each polar test. -/
private theorem globalConverse_normTwist_bergman (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (f : P) :
    ∃ b : B, ∀ s, b.val s = Z(f.val, χ, s) := by
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let q (x : ℝ) : C𝔽 := QuotientGroup.mk (τ (e x))
  let θ (x : ℝ) := homogeneousAdelicTheta 1 f.val (q x)
  let p (x : ℝ) := Complex.exp (shift(t) * x) * θ x
  have hp : p ∈ logExponentialDecaySubmodule univ := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    obtain ⟨g, hg⟩ := globalConverse_normTwist_weighted τ hτ f ((a.val : ℂ) + shift(t))
    refine ⟨g, funext fun x ↦ ?_⟩
    change g x = (Real.exp (a.val * x) : ℂ) * (Complex.exp (shift(t) * x) * θ x)
    rw [hg, add_mul, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul, mul_assoc]
  let g : PositiveRealExponentialDecay (univ : Set ℝ) := ⟨p, hp⟩
  let b := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty g
  have hchar (u : C₁) : χ u.val = 1 := by
    apply Subtype.ext
    have hu := DFunLike.congr_fun ht u.val
    change (χ u.val : ℂ) * _ ^ (0 : ℂ) = 1 * ((((ideleClassNorm F u.val).val : ℝ) : ℂ) ^ shift(t)) at hu
    simpa [MonoidHom.mem_ker.mp u.property] using hu
  refine ⟨b, congrFun ((homogeneousThetaMellinIntegral_meromorphicContinuation τ 1 f.val hτ χ
    hchar b.val).mp ⟨fun z _ ↦ (b.property.2.1.analyticAt (by simp)).meromorphicNFAt, ?_⟩)⟩
  intro s _
  exact (positiveRealFourierMellin_apply _ _ _ _ g s (mem_univ _)).trans
    (globalConverse_normTwist_section_integral χ t ht τ hτ f.val s)

/-- Tate's entire normalized eigendistribution gives the divisor inequality away from
the shifted poles. At the poles the regularized completion has order zero. -/
private theorem globalConverse_normTwist_divides (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (f : P) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, Z(f.val, χ, s) = regularizedL(χ, t) s * u s := by
  let Zf (s : ℂ) := Z(f.val, χ, s)
  let L := continuedCompletedHeckeL χ
  let p := polePolynomial(t)
  let G := regularizedL(χ, t)
  let k : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  let H (s : ℂ) := k * (adelicEigendistribution_normalized χ).choose s f.val
  have hH (s : ℂ) : AnalyticAt ℂ H s := analyticAt_const.mul
    (analytic_eval_normalized (adelicEigendistribution_normalized χ).choose_spec.1 f.val s (mem_univ s))
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hp (s : ℂ) : AnalyticAt ℂ p s := by dsimp only [p]; fun_prop
  have hprod : MeromorphicOn (L * H) univ := fun s hs ↦ (hL hs).meromorphicAt.mul (hH s).meromorphicAt
  have hZ := globalIdelicZFunction_entire_of_vanishing f.val f.property χ
  have he : toMeromorphicNFOn Zf univ = toMeromorphicNFOn (L * H) univ := by
    apply heckeEulerProductOutside_eq_finite_nf_eq _ _ (globalIdelicZFunction_meromorphic f.val χ).meromorphicOn hprod
    intro s hs
    change Z(f.val, χ, s) = continuedCompletedHeckeL χ s * (k * _)
    rw [globalIdelicZFunction_eq_integral _ (globalTwist_mem_rightHalf χ hs),
      globalIntegral_normalized_ratio χ hs, gaussianCompletedHeckeL_eq_completedHeckeL χ s hs,
      hEq ⟨s, hs⟩]
    ring
  obtain ⟨hG, hcancel⟩ := globalConverse_normTwist_regular χ t ht
  apply (globalConverse_normTwist_factor hZ hG).mpr
  intro z
  have hle : meromorphicOrderAt G z ≤ meromorphicOrderAt Zf z := by
    by_cases hz : p z = 0
    · exact (hcancel z hz) ▸ (hZ.analyticAt z).meromorphicOrderAt_nonneg
    rw [← meromorphicOrderAt_toMeromorphicNFOn (globalIdelicZFunction_meromorphic f.val χ).meromorphicOn (mem_univ z),
      he, meromorphicOrderAt_toMeromorphicNFOn hprod (mem_univ z),
      meromorphicOrderAt_mul (hL (mem_univ z)).meromorphicAt (hH z).meromorphicAt]
    change meromorphicOrderAt (toMeromorphicNFOn (p * L) univ) z ≤ _
    rw [meromorphicOrderAt_toMeromorphicNFOn (fun s hs ↦ (hp s).meromorphicAt.mul (hL hs).meromorphicAt) (mem_univ z),
      meromorphicOrderAt_mul (hp z).meromorphicAt (hL (mem_univ z)).meromorphicAt,
      (hp z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hz, zero_add]
    exact le_add_of_nonneg_right (hH z).meromorphicOrderAt_nonneg
  rw [(hG.analyticAt z).meromorphicOrderAt_eq, (hZ.analyticAt z).meromorphicOrderAt_eq] at hle
  generalize analyticOrderAt G z = m at hle ⊢
  generalize analyticOrderAt Zf z = n at hle ⊢
  cases m using ENat.recTopCoe <;> cases n using ENat.recTopCoe <;> simp_all

/-- The closed subspace topology of a Fréchet space is Fréchet (as in §5.4). -/
private theorem globalConverse_normTwist_frechet_subspace {X : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] (hX : IsFrechetTVS X) (D : Submodule ℂ X)
    (hD : IsClosed (D : Set X)) : IsFrechetTVS D := by
  obtain ⟨_, _, _, hc⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := hc
  let : IsUniformAddGroup D := D.toAddSubgroup.isUniformAddGroup
  refine ⟨inferInstance, inferInstance, TopologicalSpace.MetrizableSpace.subtype _, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact hD.completeSpace_coe

/-- A product of Fréchet spaces is Fréchet (as in §5.4). -/
private theorem globalConverse_normTwist_frechet_prod {X Y : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsFrechetTVS X) (hY : IsFrechetTVS Y) : IsFrechetTVS (X × Y) := by
  obtain ⟨_, _, _, hcX⟩ := hX
  obtain ⟨_, _, _, hcY⟩ := hY
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := hcX
  let : CompleteSpace Y := hcY
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- For a surjective linear map from a strict LF-space to a Fréchet space, closedness of
the graph implies continuity and openness. Both graph projections are open by C.1.5.5,
using the closed graphs over the Fréchet stages as a common exhaustion. -/
private theorem globalConverse_normTwist_graph {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    (hX : IsStrictLFSpace X) (hY : IsFrechetTVS Y) (T : X →ₗ[ℂ] Y)
    (hs : Surjective T) (hc : IsClosed (T.graph : Set (X × Y))) :
    Continuous T ∧ IsOpenMap T := by
  have hLF := (lfSpace_quotient_properties (E := X)).1 hX
  obtain ⟨_, S, hmono, hstage, hcover, _⟩ := hX
  let : TopologicalSpace.MetrizableSpace Y := hY.choose_spec.2.1
  let j (n : ℕ) := ((S n).subtypeL).prodMap (ContinuousLinearMap.id ℂ Y)
  let D (n : ℕ) := T.graph.comap (j n).toLinearMap
  let i (n : ℕ) : D n →L[ℂ] T.graph :=
    ((j n).comp (D n).subtypeL).codRestrict T.graph fun p ↦ p.property
  have hD (n : ℕ) : IsFrechetTVS (D n) :=
    globalConverse_normTwist_frechet_subspace (globalConverse_normTwist_frechet_prod
      (hstage n) hY) _ (hc.preimage (j n).continuous)
  have hi (n : ℕ) : range (i n) ⊆ range (i (n+1)) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨(⟨p.val.1.val, hmono n.le_succ p.val.1.property⟩, p.val.2), p.property⟩, rfl⟩
  have hcov (p : T.graph) : ∃ n, p ∈ range (i n) := by
    obtain ⟨n, hn⟩ := hcover p.val.1
    exact ⟨n, ⟨(⟨p.val.1, hn⟩, p.val.2), p.property⟩, rfl⟩
  let p := (ContinuousLinearMap.fst ℂ X Y).comp T.graph.subtypeL
  let q := (ContinuousLinearMap.snd ℂ X Y).comp T.graph.subtypeL
  let e : X ≃ T.graph :=
    { toFun x := ⟨(x, T x), (T.mem_graph_iff _).mpr rfl⟩
      invFun := p
      left_inv _ := rfl
      right_inv x := Subtype.ext (Prod.ext rfl ((T.mem_graph_iff _).mp x.property).symm) }
  have hop : IsOpenMap p := isOpenMap_of_surjective_toLF hLF hD i hi hcov p e.symm.surjective
  have hoq : IsOpenMap q := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hY)
    hD i hi hcov q (fun y ↦ (hs y).elim fun x hx ↦ ⟨e x, hx⟩)
  exact ⟨q.continuous.comp (e.symm.continuous_symm_iff.mpr hop),
    hoq.comp (e.continuous_symm_iff.mp p.continuous)⟩

/-- The norm-one mass in the residue formulas is nonzero, by the class number formula (§7.2). -/
private theorem globalConverse_normTwist_mass_ne_zero :
    ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ) ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have h0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hfin : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨h0, hfin⟩)

/-- An entire chart on the trivial norm-one component forces both polar evaluations
of the test to vanish, by the residue argument also used in §7.2. -/
private theorem globalConverse_normTwist_polar (χ : U)
    (t : ℝ) (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t)))
    (g : ℬ) (hg : Continuous (fun s ↦ Z(g, χ, s))) :
    g ∈ adelePolarSubspace F := by
  let b := (t : ℂ) * Complex.I
  have he : (fun z : ℂ ↦ Z(g, (1 : U), z)) = fun s ↦ Z(g, χ, s-b) := by
    funext s
    have h := ideleClassNormTwist_add_of_eq ht (s - b)
    have hb : b + (s - b) = s := by ring
    change ideleClassNormTwist χ (0 + (s - b)) =
      ideleClassNormTwist (1 : U) (b + (s - b)) at h
    rw [zero_add, hb] at h
    exact congrArg (globalIdelicZFunction g) h.symm
  have hc : Continuous ((fun z : ℂ ↦ Z(g, (1 : U), z))) := by
    rw [he]
    exact hg.comp (continuous_id.sub continuous_const)
  have hmass := globalConverse_normTwist_mass_ne_zero (F := F)
  have h0 : Tendsto (fun s : ℂ ↦ s * (fun z : ℂ ↦ Z(g, (1 : U), z)) s)
      (𝓝[≠] 0) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ ↦ s * (fun z : ℂ ↦ Z(g, (1 : U), z)) s) 0 :=
      continuousAt_id.mul hc.continuousAt
    simpa only [zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s : ℂ ↦ (s - 1) * (fun z : ℂ ↦ Z(g, (1 : U), z)) s)
      (𝓝[≠] 1) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ ↦ (s - 1) * (fun z : ℂ ↦ Z(g, (1 : U), z)) s) 1 :=
      (continuousAt_id.sub (continuousAt_const (y := (1 : ℂ)))).mul hc.continuousAt
    simpa only [sub_self, zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
  refine (mem_adelePolarSubspace g).mpr ⟨?_, ?_⟩
  · exact (mul_eq_zero.mp (tendsto_nhds_unique (globalIdelicZFunction_residue_zero g) h0)).resolve_left
      (neg_ne_zero.mpr hmass)
  · exact (mul_eq_zero.mp (tendsto_nhds_unique (globalIdelicZFunction_residue_one g) h1)).resolve_left hmass

/-- A global norm twist is unramified on every finite integer-unit group. The
unitary restriction to an S-idele quotient therefore gives the whole local chart. -/
private theorem globalConverse_normTwist_local_chart (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (S : Finset V) :
    ∃ (h : ∀ s, ideleClassNormTwist χ s ∈ unramifiedOutside F S)
      (η : PontryaginDual (SIdeleQuotient F S)), ∀ s,
      sIdeleRestriction F S ⟨ideleClassNormTwist χ s, h s⟩ = normChartₛ(η) s := by
  have h (s : ℂ) : ideleClassNormTwist χ s ∈ unramifiedOutside F S := by
    rw [show ideleClassNormTwist χ s = ideleClassNormTwist (1 : U) (shift(t) + s) by
      simpa only [zero_add] using ideleClassNormTwist_add_of_eq ht s]
    apply (mem_unramifiedOutside_iff F S _).mpr
    intro v _ x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    have hn : ‖(u : v.adicCompletion F)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩))
    change ideleClassNormTwist (1 : U) (shift(t) + s) (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1
    change 1 * (((((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)).val : ℝ) : ℂ) ^
      (shift(t) + s))) = 1
    rw [ideleClassNorm_ofAdicCompletion]
    change 1 * ((‖(u : v.adicCompletion F)‖ : ℂ) ^ _) = 1
    rw [hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
  let c := sIdeleRestriction F S ⟨χ₀(χ), h 0⟩
  have hc (g : SIdeleQuotient F S) : ‖c g‖ = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    change ‖(χ (QuotientGroup.mk (sIdeleInsertion F S a)) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  let η : PontryaginDual (SIdeleQuotient F S) :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hc g)⟩
      map_one' := Circle.ext (map_one c)
      map_mul' := fun u v ↦ Circle.ext (map_mul c u v)
      continuous_toFun := c.continuous.subtype_mk _ }
  refine ⟨h, η, fun s ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  change (χ (QuotientGroup.mk (sIdeleInsertion F S a)) : ℂ) *
      ((((ideleNorm F (sIdeleInsertion F S a)).val : ℝ) : ℂ) ^ s) =
    ((χ (QuotientGroup.mk (sIdeleInsertion F S a)) : ℂ) * _ ^ (0 : ℂ)) *
      ((((sIdeleQuotientNorm F S (QuotientGroup.mk a)).val : ℝ) : ℂ) ^ s)
  rw [Complex.cpow_zero, mul_one, sIdeleQuotientNorm_mk, ideleNorm_sIdeleInsertion]

/-- Multiplying both coordinates of a matching zeta pair by the same entire function
preserves its overlap equation. Once the two strip bounds hold, the local converse
theorem supplies a test with the prescribed first coordinate. -/
private theorem globalConverse_normTwist_local_lift {S : Finset V}
    (η : PontryaginDual (SIdeleQuotient F S)) (g : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (m : ℂ → ℂ) (hm : Differentiable ℂ m)
    (h : let p := sLocalZetaPair η (Submodule.Quotient.mk g)
      let bounded (I : Set ℝ) (v : ℂ → ℂ) := ∀ a b : ℝ, a ≤ b → Icc a b ⊆ I → ∀ n : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ n * (m z * v z)‖) '' (Complex.re ⁻¹' Icc a b))
      bounded (Ioi 0) p.1.val ∧ bounded (Iio 1) p.2.val) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)), ∀ z : ℂ, 0 < z.re →
      sLocalIdelicZFunction f (normChartₛ(η) z) = m z * sLocalIdelicZFunction g (normChartₛ(η) z) := by
  let p := sLocalZetaPair η (Submodule.Quotient.mk g)
  have mem (I : Set ℝ) (v : SchwartzBergman I)
      (hv : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ I → ∀ n : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ n * (m z * v.val z)‖) '' (Complex.re ⁻¹' Icc a b))) :
      (fun z ↦ m z * v.val z) ∈ schwartzBergmanSubmodule I :=
    ⟨fun _ hz ↦ (congrArg (_ * ·) (v.property.1 hz)).trans (mul_zero _),
      hm.differentiableOn.mul v.property.2.1, hv⟩
  let q : SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ)) :=
    (⟨_, mem _ p.1 h.1⟩, ⟨_, mem _ p.2 h.2⟩)
  have hp : p ∈ sLocalZetaMatching η := sLocalZetaPair_range η ▸ LinearMap.mem_range_self _ _
  have hq : q ∈ (sLocalZetaPair (F := F) (S := S) η).range := by
    rw [sLocalZetaPair_range, mem_sLocalZetaMatching]
    intro z hz
    change m z * p.1.val z = _ * (m z * p.2.val z)
    rw [(mem_sLocalZetaMatching η p).mp hp hz, mul_left_comm]
  obtain ⟨x, hx⟩ := hq
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨f, fun z hz ↦ ?_⟩
  exact ((sLocalZetaPair_mk η f).1 hz).symm.trans ((congrArg (fun y ↦ y.1.val z) hx).trans
    (congrArg (m z * ·) ((sLocalZetaPair_mk η g).1 hz)))

/-- Lagrange denominators on the integer grid, with the node itself omitted. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds_grid (N i : ℕ) (hi : i ≤ N) :
    ∏ j ∈ (Finset.range (N + 1)).erase i, |(i : ℝ) - j| =
      (i.factorial : ℝ) * (N - i).factorial := by
  induction N generalizing i with
  | zero => obtain rfl : i = 0 := by omega
            simp
  | succ N ih =>
    rcases eq_or_lt_of_le hi with rfl | hi
    · rw [Finset.range_add_one, Finset.erase_insert (Finset.notMem_range_self)]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      calc
        (∏ j ∈ Finset.range (N + 1), |((N + 1 : ℕ) : ℝ) - j|) = ∏ j ∈ Finset.range (N + 1), (((N + 1 - 1 - j) + 1 : ℕ) : ℝ) := by
          apply Finset.prod_congr rfl
          intro j hj
          have hj' : j ≤ N := by simpa using hj
          rw [abs_of_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ (N + 1 : ℕ) - (j : ℤ) by omega))]
          simp [Nat.cast_sub hj']; ring
        _ = _ := by
          rw [Finset.prod_range_reflect (fun j ↦ ((j + 1 : ℕ) : ℝ)) (N + 1)]
          exact_mod_cast Finset.prod_range_add_one_eq_factorial (N + 1)
    · have hi' : i ≤ N := by omega
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (by omega : N + 1 ≠ i),
        Finset.prod_insert (fun h ↦ Finset.notMem_range_self (Finset.mem_of_mem_erase h)), ih _ hi']
      have hsub : N + 1 - i = (N - i) + 1 := by omega
      rw [abs_of_nonpos (by exact_mod_cast (show (i : ℤ) - (N + 1 : ℕ) ≤ 0 by omega)), hsub, Nat.factorial_succ]
      push_cast
      rw [Nat.cast_sub hi']
      ring

/-- Remove a finite set of distinct zeros from an analytic function by divided
differences. This keeps the quotient analytic even at the interpolation nodes. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds_zeros (A : Finset ℂ)
    (D : Set ℂ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f D) (hz : ∀ v ∈ A, f v = 0) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q D ∧ ∀ w, f w = q w * ∏ v ∈ A, (w - v) := by
  classical
  induction A using Finset.induction_on generalizing f with
  | empty => exact ⟨f, hf, by simp⟩
  | @insert v A hmem ih =>
    have hv := hz v (Finset.mem_insert_self _ _)
    have he (w : ℂ) : (w - v) * dslope f v w = f w := by
      simpa only [smul_eq_mul, hv, sub_zero] using sub_smul_dslope f v w
    obtain ⟨q, hq, hval⟩ := ih (dslope f v) (fun w hw ↦ (hf w hw).dslope v) (fun w hw ↦ by
      have hn : w - v ≠ 0 := sub_ne_zero.mpr (fun h ↦ hmem (h ▸ hw))
      exact (mul_eq_zero.mp ((he w).trans (hz w (Finset.mem_insert_of_mem hw)))).resolve_left hn)
    refine ⟨q, hq, fun w ↦ ?_⟩
    rw [← he, hval, Finset.prod_insert hmem]
    ring

/-- Equispaced radii control the Lagrange basis even when each complex interpolation
node has an arbitrary angle on its circle. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds_interpolate
    (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (N : ℕ) (v : ℕ → ℂ) (z c : ℂ)
    (hzc : dist z c ≤ 2)
    (hv : ∀ i ∈ Finset.range (N + 1), dist (v i) z = ε / (N + 1) * (i + 1))
    (f : ℂ → ℂ) (s : ℝ) (hs : 0 ≤ s) (hf : ∀ i ∈ Finset.range (N + 1), ‖f (v i)‖ ≤ s) :
    ∃ p : ℂ → ℂ, Differentiable ℂ p ∧ (∀ i ∈ Finset.range (N + 1), p (v i) = f (v i)) ∧
      ∀ w ∈ Metric.closedBall c 8, ‖p w‖ ≤ s * (44 * Real.exp 1 / ε) ^ (N + 1) := by
  classical
  let A := Finset.range (N + 1)
  let h := ε / (N + 1)
  have hpos : 0 < h := by dsimp [h]; positivity
  have hrad (i : ℕ) (hi : i ∈ A) : dist (v i) z ≤ 1 := by
    rw [hv i hi, div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)]
    have hin : i ≤ N := by simpa [A] using hi
    rw [one_mul]
    calc ε * (i + 1) ≤ 1 * (i + 1) := by gcongr
         _ ≤ (N : ℝ) + 1 := by simpa using (show (i : ℝ) ≤ N by exact_mod_cast hin)
  have hsep (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) :
      h * |(i : ℝ) - j| ≤ ‖v i - v j‖ := by
    have he := abs_dist_sub_le (v i) (v j) z
    rw [hv i hi, hv j hj, ← mul_sub, add_sub_add_right_eq_sub, abs_mul, abs_of_pos hpos] at he
    simpa only [dist_eq_norm] using he
  have hne (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (hij : i ≠ j) : v i - v j ≠ 0 := by
    have hcast : (i : ℝ) ≠ j := by exact_mod_cast hij
    exact norm_pos_iff.mp ((mul_pos hpos (abs_pos.mpr (sub_ne_zero.mpr hcast))).trans_le (hsep i j hi hj))
  let num (i : ℕ) (w : ℂ) := ∏ j ∈ A.erase i, (w - v j)
  let p (w : ℂ) := ∑ i ∈ A, f (v i) * num i w / num i (v i)
  have hp (i : ℕ) (hi : i ∈ A) : num i (v i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj ↦ hne i j hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
  refine ⟨p, Differentiable.fun_sum fun i _ ↦ ((Differentiable.fun_finsetProd
    (fun j (_ : j ∈ A.erase i) ↦ differentiable_id.sub_const (v j))).const_mul _).div_const _, fun i hi ↦ ?_, fun w hw ↦ ?_⟩
  · dsimp only [p]
    rw [Finset.sum_eq_single_of_mem i hi]
    · exact mul_div_cancel_right₀ _ (hp i hi)
    · intro j hj hji
      have hzero : num j (v i) = 0 := Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, hi⟩) (sub_self _)
      simp [hzero]
  have hterm (i : ℕ) (hi : i ∈ A) : ‖f (v i) * num i w / num i (v i)‖ ≤
      s * (22 / ε) ^ N * Real.exp (N + 1) := by
    have hin : i ≤ N := by simpa [A] using hi
    have hcard : (A.erase i).card = N := by simp [Finset.card_erase_of_mem hi, A]
    have hnum : ‖num i w‖ ≤ (11 : ℝ) ^ N := by
      dsimp only [num]
      rw [norm_prod, ← hcard, ← Finset.prod_const]
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro j hj
      rw [← dist_eq_norm]
      linarith [dist_triangle w c (v j), dist_triangle (v j) z c,
        dist_comm c (v j), Metric.mem_closedBall.mp hw, hrad j (Finset.mem_of_mem_erase hj)]
    have hden : h ^ N * ((i.factorial : ℝ) * (N - i).factorial) ≤ ‖num i (v i)‖ := by
      dsimp only [num]
      rw [← globalConverse_normTwist_gaussian_strip_bounds_grid N i hin, norm_prod,
        show h ^ N = ∏ _j ∈ A.erase i, h by rw [Finset.prod_const, hcard], ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun j _ ↦ mul_nonneg hpos.le (abs_nonneg _))
        (fun j hj ↦ hsep i j hi (Finset.mem_of_mem_erase hj))
    have hc : (N.factorial : ℝ) ≤ (2 : ℝ) ^ N * ((i.factorial : ℝ) * (N - i).factorial) := by
      have hchoose := Nat.choose_mul_factorial_mul_factorial hin
      calc
        (N.factorial : ℝ) = (N.choose i : ℝ) * ((i.factorial : ℝ) * (N - i).factorial) := by
          exact_mod_cast (by simpa only [mul_assoc] using hchoose.symm)
        _ ≤ _ := by gcongr; exact_mod_cast Nat.choose_le_two_pow N i
    have hfac : (N + 1 : ℝ) ^ N ≤ Real.exp (N + 1) * N.factorial :=
      (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp ((N : ℝ) + 1) (by positivity) N)
    have hcoef : (11 : ℝ) ^ N ≤ ((22 / ε) ^ N * Real.exp (N + 1)) * ‖num i (v i)‖ := by
      apply le_trans _ (mul_le_mul_of_nonneg_left hden (by positivity))
      have he : (22 / ε) ^ N * h ^ N = (22 : ℝ) ^ N / (N + 1) ^ N := by
        rw [← mul_pow, ← div_pow]; congr 1; dsimp [h]; field_simp
      calc
        (11 : ℝ) ^ N = (11 : ℝ) ^ N / (N + 1) ^ N * (N + 1) ^ N := by field_simp
        _ ≤ (11 : ℝ) ^ N / (N + 1) ^ N * (Real.exp (N + 1) * ((2 : ℝ) ^ N * ((i.factorial : ℝ) * (N - i).factorial))) :=
          mul_le_mul_of_nonneg_left (hfac.trans (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le)) (by positivity)
        _ = _ := by
          have h22 : (22 : ℝ) ^ N = 11 ^ N * 2 ^ N := by rw [← mul_pow]; norm_num
          rw [show (22 / ε) ^ N * Real.exp (N + 1) * (h ^ N * _) =
            ((22 / ε) ^ N * h ^ N) * Real.exp (N + 1) * ((i.factorial : ℝ) * (N - i).factorial) by ring, he, h22]
          ring
    rw [norm_div, norm_mul, div_le_iff₀ (norm_pos_iff.mpr (hp i hi))]
    have h := mul_le_mul (hf i hi) (hnum.trans hcoef) (norm_nonneg _) hs
    linarith only [h, show s * ((22 / ε) ^ N * Real.exp (N + 1) * ‖num i (v i)‖) =
      s * (22 / ε) ^ N * Real.exp (N + 1) * ‖num i (v i)‖ by ring]
  have h22 : 1 ≤ 22 / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hsize : (N + 1 : ℝ) ≤ 2 ^ (N + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := N + 1)).le
  calc
    ‖p w‖ ≤ ∑ i ∈ A, ‖f (v i) * num i w / num i (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ A, s * (22 / ε) ^ N * Real.exp (N + 1) := Finset.sum_le_sum hterm
    _ = (N + 1 : ℝ) * (s * (22 / ε) ^ N * (Real.exp 1) ^ (N + 1)) := by
      simp [A, nsmul_eq_mul, ← Real.exp_nat_mul]
    _ ≤ 2 ^ (N + 1) * (s * (22 / ε) ^ (N + 1) * (Real.exp 1) ^ (N + 1)) := by gcongr; omega
    _ = _ := by rw [show 44 * Real.exp 1 / ε = 2 * (22 / ε) * Real.exp 1 by ring, mul_pow, mul_pow]; ring

/-- If an analytic function is bounded by `X` on the disk and has norm at least
`1 / X` at the center, its norm stays above a fixed inverse power of `X` on a circle
around `z`. The exponent depends only on the maximum permitted radius. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds_minimum (ε : ℝ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ K : ℕ, ∀ (f : ℂ → ℂ) (c z : ℂ) (X : ℝ), 2 ≤ X → dist z c ≤ 2 →
      AnalyticOnNhd ℂ f (Metric.closedBall c 8) →
      (∀ u ∈ Metric.closedBall c 8, ‖f u‖ ≤ X) → 1 ≤ X * ‖f c‖ →
      ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ ∀ w ∈ Metric.sphere z r, 1 ≤ X ^ K * ‖f w‖ := by
  classical
  let D := 44 * Real.exp 1 / ε
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt D (by norm_num : (1 : ℝ) < 2)
  refine ⟨17 * p + 2, fun f c z X hX hzc hhol hub hcenter ↦ ?_⟩
  obtain ⟨m, hm, hm'⟩ := exists_nat_pow_near (by linarith : 1 ≤ X) (by norm_num : (1 : ℝ) < 2)
  have hm1 : 0 < m := by
    by_contra! h
    have : m = 0 := by omega
    norm_num [this] at hm'
    linarith
  -- Use a number of nodes proportional to log X, so exponential costs are polynomial in X.
  let N := 8 * (m + 1)
  let A := Finset.range (N + 1)
  let s := (X ^ (17 * p + 2))⁻¹
  have hx : 0 < X := by linarith
  by_contra! hbad
  -- If every radius fails, interpolate a small value from each of these circles.
  have hnodes (i : ℕ) (hi : i ∈ A) : ∃ w : ℂ,
      dist w z = ε / (N + 1) * (i + 1) ∧ ‖f w‖ ≤ s := by
    have hin : i ≤ N := by simpa [A] using hi
    have hrad : ε / (N + 1) * (i + 1) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)]
      gcongr
    obtain ⟨w, hw, hsmall⟩ := hbad _ (by positivity) hrad
    refine ⟨w, Metric.mem_sphere.mp hw, ?_⟩
    change ‖f w‖ ≤ (X ^ (17 * p + 2))⁻¹
    rw [← one_div]
    apply (le_div_iff₀ (pow_pos hx _)).mpr
    simpa only [mul_comm] using hsmall.le
  choose! v hv hsmall using hnodes
  obtain ⟨q, hq, heq, hqb⟩ := globalConverse_normTwist_gaussian_strip_bounds_interpolate
    ε hε hε₁ N v z c hzc hv f s (by dsimp [s]; positivity) hsmall
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hpow : D ^ (N + 1) ≤ X ^ (17 * p) := calc
    _ ≤ ((2 : ℝ) ^ p) ^ (N + 1) := pow_le_pow_left₀ hD0 hp.le _
    _ = (2 : ℝ) ^ (p * (N + 1)) := (pow_mul _ _ _).symm
    _ ≤ (2 : ℝ) ^ (m * (17 * p)) := by
      apply pow_le_pow_right₀ (by norm_num)
      have hN : N + 1 ≤ m * 17 := by dsimp [N]; omega
      simpa only [mul_left_comm, mul_comm, mul_assoc] using Nat.mul_le_mul_left p hN
    _ ≤ X ^ (17 * p) := by rw [pow_mul]; gcongr
  have hqbd (w : ℂ) (hw : w ∈ Metric.closedBall c 8) : ‖q w‖ ≤ (X ^ 2)⁻¹ := by
    apply (hqb w hw).trans
    apply (mul_le_mul_of_nonneg_left hpow (by dsimp [s]; positivity)).trans_eq
    dsimp only [s]; rw [pow_add]; field_simp
  have hrad (i : ℕ) (hi : i ∈ A) : dist (v i) c ≤ 3 := by
    have hin : i ≤ N := by simpa [A] using hi
    have hεi : dist (v i) z ≤ ε := by
      rw [hv i hi, div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)]
      gcongr
    linarith [dist_triangle (v i) z c]
  have hinj : Set.InjOn v A := by
    intro i hi j hj he
    have hh := (hv i hi).symm.trans ((congrArg (dist · z) he).trans (hv j hj))
    have := mul_left_cancel₀ (ne_of_gt (div_pos hε (by positivity))) hh
    exact_mod_cast (add_right_cancel this)
  let V₀ := A.image v
  obtain ⟨g, hg, hge⟩ := globalConverse_normTwist_gaussian_strip_bounds_zeros V₀
    (Metric.closedBall c 8) (fun w ↦ f w - q w) (fun w hw ↦ (hhol w hw).sub (hq.analyticAt w))
    (by rintro _ hw; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw; exact sub_eq_zero.mpr (heq i hi).symm)
  have hcard : V₀.card = N + 1 := (Finset.card_image_of_injOn hinj).trans (Finset.card_range _)
  have hvc (w : ℂ) (hw : w ∈ V₀) : dist w c ≤ 3 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw; exact hrad i hi
  have hdiff (w : ℂ) : ‖f w - q w‖ = ‖g w‖ * ∏ u ∈ V₀, ‖w - u‖ := by
    rw [hge w, norm_mul, norm_prod]
  have hunit : (X ^ 2)⁻¹ ≤ X := (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))).trans (by linarith)
  -- The nodes lie within radius 3 of c, hence at least 5 from the boundary of radius 8.
  have hgb : ‖g c‖ ≤ (2 * X) / 5 ^ (N + 1) := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      (hg.differentiableOn.diffContOnCl_ball subset_rfl) _ (subset_closure (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 8)))
    intro w hw
    have hw' := Metric.frontier_ball_subset_sphere hw
    have hwc := Metric.sphere_subset_closedBall hw'
    have hdist : (5 : ℝ) ^ (N + 1) ≤ ∏ u ∈ V₀, ‖w - u‖ := by
      rw [← hcard, ← Finset.prod_const]
      apply Finset.prod_le_prod₀ (by intros; norm_num)
      intro u hu
      rw [← dist_eq_norm]
      linarith [dist_triangle w u c, Metric.mem_sphere.mp hw', hvc u hu]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ‖g w‖ * ∏ u ∈ V₀, ‖w - u‖ := mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
      _ = ‖f w - q w‖ := (hdiff _).symm
      _ ≤ 2 * X := (norm_sub_le _ _).trans (by linarith [hub w hwc, hqbd w hwc])
  have htail : ‖f c - q c‖ ≤ 2 * X * (3 / 5 : ℝ) ^ (N + 1) := by
    rw [hdiff]
    have hp₃ : (∏ u ∈ V₀, ‖c - u‖) ≤ (3 : ℝ) ^ (N + 1) := by
      rw [← hcard, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
        (fun u hu ↦ by simpa [dist_eq_norm, norm_sub_rev] using hvc u hu)
    exact (mul_le_mul hgb hp₃ (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (by positivity)).trans_eq (by rw [div_pow]; ring)
  -- At the center the interpolation remainder therefore gains a factor (3/5) per node.
  have hsmall' : 4 * X ^ 2 * (3 / 5 : ℝ) ^ (N + 1) < 1 := by
    have hX₂ : 4 * X ^ 2 < (16 : ℝ) ^ (m + 1) := calc
      _ < 4 * ((2 : ℝ) ^ (m + 1)) ^ 2 := by gcongr
      _ ≤ ((4 : ℝ) ^ (m + 1)) * ((4 : ℝ) ^ (m + 1)) := by
        rw [← pow_mul, Nat.mul_comm (m + 1) 2, pow_mul]
        norm_num
        exact le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega : m + 1 ≠ 0)
      _ = _ := by rw [← mul_pow]; norm_num
    have hlarge : (16 : ℝ) ^ (m + 1) ≤ (5 / 3 : ℝ) ^ (N + 1) := calc
      _ ≤ ((5 / 3 : ℝ) ^ 8) ^ (m + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (5 / 3 : ℝ) ^ N := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    have h := mul_lt_mul_of_pos_right (hX₂.trans_le hlarge) (by positivity : 0 < (3 / 5 : ℝ) ^ (N + 1))
    simpa only [← mul_pow, show (5 / 3 : ℝ) * (3 / 5) = 1 by norm_num, one_pow] using h
  have hcq := hqbd c (Metric.mem_closedBall_self (by norm_num))
  have hxc : X * ‖f c‖ ≤ X * ((X ^ 2)⁻¹ + 2 * X * (3 / 5 : ℝ) ^ (N + 1)) :=
    mul_le_mul_of_nonneg_left ((norm_le_norm_add_norm_sub' (f c) (q c)).trans (by linarith)) hx.le
  have hi : X * (X ^ 2)⁻¹ ≤ 1 / 2 := by
    field_simp
    nlinarith
  nlinarith

/-- The finite Euler polynomial is continuous and bounded away from zero on each
half-plane strictly to the right of zero. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds_factors (χ : U) (S : Finset V)
    (a : ℝ) (ha : 0 < a) :
    Continuous (reciprocalPartialHeckeEulerProduct χ S) ∧
    ∃ δ > (0 : ℝ), ∀ w : ℂ, a ≤ w.re → δ ≤ ‖reciprocalPartialHeckeEulerProduct χ S w‖ := by
  classical
  let q (v : V) := (v.asIdeal.absNorm : ℝ)
  have hq (v : V) : 1 < q v := by
    dsimp only [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hp (v : V) : 0 < 1 - q v ^ (-a) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (hq v) (neg_lt_zero.mpr ha))
  have hf (v : V) : Continuous (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) ∧
      ∀ w : ℂ, a ≤ w.re → 1 - q v ^ (-a) ≤ ‖(finiteHeckeEulerFactor χ v w)⁻¹‖ := by
    have hq0 := zero_lt_one.trans (hq v)
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp only [inv_inv]
      have hd : Differentiable ℂ (fun z : ℂ ↦ (v.asIdeal.absNorm : ℂ) ^ (-z)) :=
        differentiable_neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)))
      refine ⟨(hd.const_mul _ |>.const_sub 1).continuous, fun w hw ↦ ?_⟩
      apply le_trans _ (norm_sub_norm_le (1 : ℂ) _)
      rw [norm_one, norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
        ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
      exact sub_le_sub_left (Real.rpow_le_rpow_of_exponent_le (hq v).le (neg_le_neg hw)) _
    · simp only [inv_one, norm_one]
      exact ⟨continuous_const, fun _ _ ↦ sub_le_self _ (Real.rpow_nonneg hq0.le _)⟩
  refine ⟨continuous_finsetProd _ fun v _ ↦ (hf v).1,
    ∏ v ∈ S, (1 - q v ^ (-a)), Finset.prod_pos (fun v _ ↦ hp v), fun w hw ↦ ?_⟩
  change _ ≤ ‖∏ v ∈ S, (finiteHeckeEulerFactor χ v w)⁻¹‖
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun v _ ↦ (hp v).le) (fun v _ ↦ (hf v).2 w hw)

/-- On each high disc centered in a fixed positive strip, the outside Euler product
has a polynomial lower bound on a circle inside the right half-plane. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds_circles (χ : U) (S : Finset V)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hs : ∀ z : halfPlane, L z = finiteHeckeL χ z)
    (a d : ℝ) (ha : 0 < a) (had : a ≤ d) :
    let D := fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z
    ∃ (k : ℕ) (T : ℝ), ∀ z : ℂ, z.re ∈ Icc a d → T ≤ |z.im| →
      ∃ r : ℝ, 0 < r ∧ r ≤ a / 2 ∧ ∀ w ∈ Metric.sphere z r,
        ContinuousAt D w ∧ 1 ≤ |w.im| ^ k * ‖D w‖ := by
  obtain ⟨E, hE, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hs (a - 8) (d + 12) (by linarith)
  obtain ⟨C, hC, hup⟩ := Asymptotics.isBigO_iff'.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hup
  obtain ⟨T, hup⟩ := hup
  obtain ⟨j, hj⟩ := exists_nat_gt E
  let T₀ := max (max T C) 1
  have bound (w : ℂ) (hw : w.re ∈ Icc (a - 8) (d + 12)) (ht : T₀ ≤ |w.im|) :
      ‖L w‖ ≤ |w.im| ^ (j + 1) := by
    have ht' : max T C ≤ |w.im| := (le_max_left _ _).trans ht
    have h1 : 1 ≤ |w.im| := (le_max_right _ _).trans ht
    have hval := hup _ ((le_max_left _ _).trans ht') w rfl hw
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hval
    rw [pow_succ, mul_comm]
    exact hval.trans (mul_le_mul ((le_max_right _ _).trans ht')
      (by simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le h1 hj.le)
      (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _))
  obtain ⟨hcP, δ, hδ, hP⟩ := globalConverse_normTwist_gaussian_strip_bounds_factors χ S (a / 2) (half_pos ha)
  let ε := min (a / 2) 1
  obtain ⟨K, hK⟩ := globalConverse_normTwist_gaussian_strip_bounds_minimum ε
    (lt_min (half_pos ha) zero_lt_one) (min_le_right _ _)
  let ζ := ‖dedekindZeta F 2‖
  refine ⟨(2 * (j + 1)) * K + 1, max (T₀ + 10) (max (2 * ζ + 10) (2 * δ⁻¹ + 10)), fun z hz ht ↦ ?_⟩
  -- Moving the center two units right gives an Euler-product lower bound at the center.
  let c := z + 2
  let y := |z.im| / 2
  have htB : T₀ + 10 ≤ |z.im| := (le_max_left _ _).trans ht
  have htζ : 2 * ζ + 10 ≤ |z.im| := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htδ : 2 * δ⁻¹ + 10 ≤ |z.im| := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hB : 1 ≤ T₀ := le_max_right _ _
  have hy : 2 ≤ y := by dsimp [y]; linarith
  have hyζ : ζ ≤ y := by dsimp [y]; linarith
  have hyδ : δ⁻¹ ≤ y := by dsimp [y]; linarith
  let X := y ^ (2 * (j + 1))
  have hyX : y ≤ X := le_self_pow₀ (by linarith) (by omega)
  have hdist : dist z c ≤ 2 := by simp [c, dist_eq_norm]
  have hdisc (w : ℂ) (hw : w ∈ Metric.closedBall c 9) :
      w.re ∈ Icc (a - 8) (d + 12) ∧ T₀ ≤ |w.im| ∧ |w.im| ≤ y ^ 2 := by
    have hre := (Complex.abs_re_le_norm (w - c)).trans (mem_closedBall_iff_norm.mp hw)
    have him := (Complex.abs_im_le_norm (w - c)).trans (mem_closedBall_iff_norm.mp hw)
    norm_num [c, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im] at hre him
    have hlo := (abs_sub_abs_le_abs_sub z.im w.im).trans (by simpa only [abs_sub_comm z.im w.im] using him : |z.im - w.im| ≤ 9)
    have hhi := (abs_sub_abs_le_abs_sub w.im z.im).trans him
    obtain ⟨hl, hu⟩ := abs_le.mp hre
    refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, by linarith, ?_⟩
    have h5 : 5 ≤ y := by dsimp [y]; linarith
    have ht' : |z.im| = 2 * y := by dsimp [y]; ring
    nlinarith [mul_nonneg (show 0 ≤ y - 5 by linarith) (show 0 ≤ y + 3 by linarith)]
  have hbd (w : ℂ) (hw : w ∈ Metric.closedBall c 9) : ‖L w‖ ≤ X := by
    obtain ⟨hre, hlo, hhi⟩ := hdisc w hw
    exact (bound _ hre hlo).trans ((pow_le_pow_left₀ (abs_nonneg _) hhi _).trans_eq (pow_mul _ _ _).symm)
  -- Polynomial growth rules out poles throughout the smaller closed disk at this height.
  have han : AnalyticOnNhd ℂ L (Metric.closedBall c 8) := by
    intro w hw
    apply (hL (mem_univ w)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hn
    have hne : ∀ᶠ v in 𝓝 w, v ∈ Metric.ball c 9 := Metric.isOpen_ball.mem_nhds ((Metric.closedBall_subset_ball (by norm_num : (8 : ℝ) < 9)) hw)
    have hp := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hn)).eventually_gt_atTop X
    obtain ⟨v, hv, hv'⟩ := (hp.and (hne.filter_mono nhdsWithin_le_nhds)).exists
    exact hv.not_ge (hbd v (Metric.ball_subset_closedBall hv'))
  have hcr : 2 ≤ c.re := by simp [c]; linarith [hz.1]
  have hc : c ∈ halfPlane := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hcr
  have hcenter : 1 ≤ X * ‖L c‖ := by
    rw [hs ⟨c, hc⟩, mul_comm]
    exact (finiteHeckeL_zeroFreeRegion_euler F χ ⟨c, hc⟩ (y := 2) (by norm_num) hcr).2.trans
      (mul_le_mul_of_nonneg_left (hyζ.trans hyX) (norm_nonneg _))
  obtain ⟨r, hr, hrε, hgood⟩ := hK L c z X (hy.trans hyX) hdist han
    (fun w hw ↦ hbd _ (Metric.closedBall_subset_closedBall (by norm_num : (8 : ℝ) ≤ 9) hw)) hcenter
  refine ⟨r, hr, hrε.trans (min_le_left _ _), fun w hw ↦ ?_⟩
  have hwr := mem_sphere_iff_norm.mp hw
  have h1 : r ≤ 1 := hrε.trans (min_le_right _ _)
  have hwc : w ∈ Metric.closedBall c 8 := by
    apply Metric.mem_closedBall.mpr
    linarith [dist_triangle w z c, Metric.mem_sphere.mp hw]
  have hre := (Complex.abs_re_le_norm (w - z)).trans hwr.le
  have him := (Complex.abs_im_le_norm (w - z)).trans hwr.le
  have hwre : a / 2 ≤ w.re := by
    have h := (abs_le.mp hre).1
    simp only [Complex.sub_re] at h
    linarith [hz.1, hrε.trans (min_le_left (a / 2) 1)]
  have hyw : y ≤ |w.im| := by
    have h := (abs_sub_abs_le_abs_sub z.im w.im).trans (show |z.im - w.im| ≤ r by
      rwa [abs_sub_comm, ← Complex.sub_im])
    dsimp [y]; linarith
  refine ⟨hcP.continuousAt.mul (han w hwc).continuousAt, ?_⟩
  have hδw : 1 ≤ |w.im| * ‖reciprocalPartialHeckeEulerProduct χ S w‖ :=
    ((inv_le_iff_one_le_mul₀ hδ).mp (hyδ.trans hyw)).trans (by
      exact mul_le_mul_of_nonneg_left (hP w hwre) (abs_nonneg _))
  have hXw : X ^ K ≤ |w.im| ^ ((2 * (j + 1)) * K) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by linarith) hyw _) _
  have hLw := (hgood w hw).trans (mul_le_mul_of_nonneg_right hXw (norm_nonneg _))
  dsimp only
  rw [norm_mul, pow_succ]
  calc
    1 = 1 * 1 := by ring
    _ ≤ (|w.im| ^ (2 * (j + 1) * K) * ‖L w‖) *
        (|w.im| * ‖reciprocalPartialHeckeEulerProduct χ S w‖) :=
      mul_le_mul hLw hδw zero_le_one (zero_le_one.trans hLw)
    _ = _ := by ring

/-- Apply maximum modulus on a good circle to the holomorphic local product, including
its polynomial weight. The same argument applies in the reflected variable. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds_local (χ : U) (S : Finset V)
    (hD : ∀ v : V, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (g : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (η : PontryaginDual (SIdeleQuotient F S)) (hχ : χ₀(χ) ∈ unramifiedOutside F S)
    (hη : sIdeleRestriction F S ⟨χ₀(χ), hχ⟩ = normChartₛ(η) 0)
    (b : B) (m e : ℂ → ℂ) (hm : Differentiable ℂ m) (he : Differentiable ℂ e)
    (hIm : ∀ z : ℂ, |z.im| ≤ ‖e z‖)
    (hZ : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z,
      b.val (e w) = m (e w) * Z(sAdeleSchwartzToGlobal F S g, χ, w))
    (a d : ℝ) (ha : 0 < a) (had : a ≤ d)
    (l u : ℝ) (hlu : l ≤ u)
    (hstrip : ∀ w : ℂ, w.re ∈ Icc (a / 2) (d + a / 2) → (e w).re ∈ Icc l u) (n : ℕ) :
    BddAbove ((fun z : ℂ ↦ ‖(e z) ^ n * (m (e z) *
      sLocalIdelicZFunction g (normChartₛ(η) z))‖) '' (Complex.re ⁻¹' Icc a d)) := by
  classical
  obtain ⟨L, hL, hs⟩ := finiteHeckeL_exists_continuation χ
  obtain ⟨k, T, hcircle⟩ := globalConverse_normTwist_gaussian_strip_bounds_circles χ S L hL hs a d ha had
  let p := (sLocalZetaPair η (Submodule.Quotient.mk g)).1
  let H := fun z ↦ (e z) ^ n * (m (e z) * p.val z)
  have hH : DifferentiableOn ℂ H (Complex.re ⁻¹' Ioi 0) :=
    (he.pow n).differentiableOn.mul ((hm.comp he).differentiableOn.mul p.property.2.1)
  have hbase : sIdeleRestriction F S ⟨χ₀(χ), hχ⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η := by
    ext1 x
    have hx := DFunLike.congr_fun hη x
    change _ = (η x : ℂ) * _ ^ (0 : ℂ) at hx
    change _ = (η x : ℂ)
    simpa only [Complex.cpow_zero, mul_one] using hx
  have hmass : (∏ᶠ v : {v : V // v ∉ S},
      (((finiteLocalMultiplicativeTamagawaMeasure F v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv : ¬v.val.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h ↦ v.property (hD _ h)
    simp [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, multiplicity_eq_zero_of_not_dvd hv]
  have hW := weilIdentity_unramifiedOutside_meromorphic S g χ hχ L hL (fun z hz ↦ hs ⟨z, hz⟩)
  dsimp only at hW
  rw [hmass, hbase] at hW
  obtain ⟨C, hC⟩ := b.property.2.2 l u hlu (subset_univ _) (n + k)
  let K := Complex.reProdIm (Icc a d) (Icc (-T) T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := H)
    (hH.continuousOn.mono (fun z hz ↦ ha.trans_le hz.1.1))
  refine ⟨max C M, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  dsimp only
  have hpz : p.val z = sLocalIdelicZFunction g (normChartₛ(η) z) :=
    (sLocalZetaPair_mk η g).1 (ha.trans_le hz.1)
  rw [← hpz]
  change ‖H z‖ ≤ _
  by_cases ht : |z.im| ≤ T
  · exact (hM z ⟨hz, abs_le.mp ht⟩).trans (le_max_right _ _)
  obtain ⟨r, hr, hra, hgood⟩ := hcircle z hz (le_of_not_ge ht)
  have hwr (w : ℂ) (hw : w ∈ Metric.closedBall z r) : w.re ∈ Icc (a / 2) (d + a / 2) := by
    have h := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.mp hw)
    obtain ⟨h₁, h₂⟩ := abs_le.mp h
    simp only [Complex.sub_re] at h₁ h₂
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hball : Metric.closedBall z r ⊆ Complex.re ⁻¹' Ioi (0 : ℝ) :=
    fun w hw ↦ (half_pos ha).trans_le (hwr w hw).1
  apply le_trans _ (le_max_left C M)
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
    ((hH.mono hball).diffContOnCl_ball subset_rfl) _ (subset_closure (Metric.mem_ball_self hr))
  intro w hw
  have hw' := Metric.frontier_ball_subset_sphere hw
  have hwc := Metric.sphere_subset_closedBall hw'
  obtain ⟨hcont, hlow⟩ := hgood w hw'
  have hpos : 0 < w.re := hball hwc
  let D := fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z
  have hright : Complex.re ⁻¹' Ioi (0 : ℝ) ∈ 𝓝 w :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hpos
  -- On this circle the meromorphic identity gives an equality of continuous values.
  have hEq : (e w) ^ n * b.val (e w) = H w * D w := by
    have hbc : Continuous b.val :=
      continuous_iff_continuousAt.mpr fun s ↦ b.property.2.1.continuousOn.continuousAt (by simp)
    apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] w)
      ((((he.pow n).continuous.mul (hbc.comp he.continuous)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (((hH.continuousOn.continuousAt hright).mul hcont).tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [hZ w, nhdsNE_le_codiscrete w hW, nhdsWithin_le_nhds hright] with v hv hwv hp
    change (e v) ^ n * b.val (e v) = (e v) ^ n * (m (e v) * p.val v) *
      ((∏ u ∈ S, (finiteHeckeEulerFactor χ u v)⁻¹) * L v)
    have hpv : p.val v = sLocalIdelicZFunction g (normChartₛ(η) v) := (sLocalZetaPair_mk η g).1 hp
    rw [hv, hwv, hpv]
    ring
  calc
    ‖H w‖ ≤ ‖H w‖ * (|w.im| ^ k * ‖D w‖) := le_mul_of_one_le_right (norm_nonneg _) hlow
    _ = |w.im| ^ k * ‖(e w) ^ n * b.val (e w)‖ := by rw [hEq, norm_mul (H w) (D w)]; ring
    _ ≤ ‖e w‖ ^ k * ‖(e w) ^ n * b.val (e w)‖ := by gcongr; exact hIm w
    _ = ‖(e w) ^ (n + k) * b.val (e w)‖ := by simp only [norm_mul, norm_pow, pow_add]; ring
    _ ≤ C := hC (mem_image_of_mem _ (hstrip w (hwr w hwc)))
/-- Paper: Theorem 6.3.2.1(1), p. 309. Let an entire multiplier times the
global Gaussian zeta function extend to a Schwartz–Bergman function. Choose a finite
stage representing the Gaussian at which the multiplier times each of the two local
zeta coordinates decays rapidly on closed substrips of its half-plane. The reciprocal of
the outside Euler product can have poles on the strips used on p. 308 (I200). Bounds on
the boundaries of rectangles for the two holomorphic products would suffice by maximum
modulus. -/
private theorem globalConverse_normTwist_gaussian_strip_bounds (χ : U) (t : ℝ)
    (_ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (b : B)
    (m : ℂ → ℂ) (_hm : Differentiable ℂ m)
    (_hb : ∀ s : halfPlane, b.val s = m s * gaussianCompletedHeckeL χ s) :
    ∃ (S : Finset V) (g : SchwartzBruhat (Multiplicative (SAdeleRing F S))),
      sAdeleSchwartzToGlobal F S g = adelicStandardGaussian χ ∧
      ∀ (η : PontryaginDual (SIdeleQuotient F S)) (h : χ₀(χ) ∈ unramifiedOutside F S),
      sIdeleRestriction F S ⟨χ₀(χ), h⟩ = normChartₛ(η) 0 →
      let p := sLocalZetaPair η (Submodule.Quotient.mk g)
      let bounded (I : Set ℝ) (v : ℂ → ℂ) := ∀ a b : ℝ, a ≤ b → Icc a b ⊆ I → ∀ n : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ n * (m z * v z)‖) '' (Complex.re ⁻¹' Icc a b))
      bounded (Ioi 0) p.1.val ∧ bounded (Iio 1) p.2.val := by
  classical
  obtain ⟨A, f, hf⟩ := sAdeleSchwartzToGlobal_exhaustive F (adelicStandardGaussian χ)
  -- Including the different makes the omitted unit masses one and identifies the Fourier transform.
  let S := A ∪ (Ideal.finite_factors (differentIdeal_ne_bot : differentIdeal ℤ (𝓞 F) ≠ ⊥)).toFinset
  have hA : A ⊆ S := Finset.subset_union_left
  have hD (v : V) (hv : v.asIdeal ∣ differentIdeal ℤ (𝓞 F)) : v ∈ S :=
    Finset.mem_union_right _ (by simpa using hv)
  let g := sAdeleSchwartzTransition F hA f
  have hg : sAdeleSchwartzToGlobal F S g = adelicStandardGaussian χ :=
    (LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp F hA) f).trans hf
  refine ⟨S, g, hg, fun η hχ hη ↦ ?_⟩
  let G := sAdeleSchwartzToGlobal F S g
  have hbm : MeromorphicOn b.val univ := fun z _ ↦
    (b.property.2.1.analyticAt (by simp : Complex.re ⁻¹' (univ : Set ℝ) ∈ 𝓝 z)).meromorphicAt
  have hgm : MeromorphicOn (fun z ↦ m z * Z(G, χ, z)) univ :=
    fun z hz ↦ (_hm.analyticAt z).meromorphicAt.mul ((globalIdelicZFunction_meromorphic G χ) hz).meromorphicAt
  have hn := heckeEulerProductOutside_eq_finite_nf_eq _ _ hbm hgm (fun z hz ↦ by
    simpa only [G, hg, gaussianCompletedHeckeL] using _hb ⟨z, hz⟩)
  have hZ (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, b.val w = m w * Z(G, χ, w) := by
    exact (hbm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)).symm.trans
      (hn ▸ hgm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z))
  constructor
  · intro a d had hsub n
    have ha : 0 < a := hsub (left_mem_Icc.mpr had)
    obtain ⟨C, hC⟩ := globalConverse_normTwist_gaussian_strip_bounds_local χ S hD g η hχ hη b m id
      _hm differentiable_id Complex.abs_im_le_norm hZ a d ha had (a / 2) (d + a / 2) (by linarith)
      (fun _ h ↦ h) n
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact ((congrArg (fun v : ℂ ↦ ‖z ^ n * (m z * v)‖)
      ((sLocalZetaPair_mk η g).1 (ha.trans_le hz.1)))).le.trans (hC (mem_image_of_mem _ hz))
  · intro a d had hsub n
    have hd : d < 1 := hsub (right_mem_Icc.mpr had)
    have hinv (x : C𝔽) : χ₀(χ⁻¹) x = (χ₀(χ) x)⁻¹ := by
      change ((χ x)⁻¹ : Circle) * _ ^ (0 : ℂ) = ((_ : ℂ) * _ ^ (0 : ℂ))⁻¹
      simp
      rfl
    have hχ' : χ₀(χ⁻¹) ∈ unramifiedOutside F S := by
      apply (mem_unramifiedOutside_iff F S _).mpr
      intro v hv x
      have hx := (mem_unramifiedOutside_iff F S _).mp hχ v hv x
      change χ₀(χ) _ = 1 at hx
      change χ₀(χ⁻¹) _ = 1
      rw [hinv, hx, inv_one]
    have hη' : sIdeleRestriction F S ⟨χ₀(χ⁻¹), hχ'⟩ = normChartₛ(η⁻¹) 0 := by
      ext1 x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      have hy := DFunLike.congr_fun hη (QuotientGroup.mk y)
      rw [sIdeleRestriction_mk] at hy ⊢
      rw [hinv, hy]
      change ((_ : ℂ) * _ ^ (0 : ℂ))⁻¹ = ((η (QuotientGroup.mk y))⁻¹ : Circle) * _ ^ (0 : ℂ)
      simp
      rfl
    have hdual (z : ℂ) : Z(G, χ, 1 - z) =
        Z(sAdeleSchwartzToGlobal F S (sAdeleSchwartzFourier g), χ⁻¹, z) := by
      rw [globalIdelicZFunction_functionalEquation, show adeleSchwartzFourier G = _ from
        adeleSchwartzFourier_sAdeleSchwartzToGlobal_of_different F S hD g (sAdeleSchwartzFourier g) rfl]
      congr 1
      ext1 x
      let N : ℂ := (((ideleClassNorm F x).val : ℝ) : ℂ)
      have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F x).ne_zero)
      change N * ideleClassNormTwist χ (1 - z) x⁻¹ = _
      rw [map_inv]
      change N * ((χ x : ℂ) * N ^ (1 - z))⁻¹ = (χ x : ℂ)⁻¹ * N ^ z
      rw [Complex.cpow_sub _ _ hN, Complex.cpow_one]
      field_simp
    have hZ' (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, b.val (1 - w) = m (1 - w) *
        Z(sAdeleSchwartzToGlobal F S (sAdeleSchwartzFourier g), χ⁻¹, w) := by
      have hmap : Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[≠] z) (𝓝[≠] (1 - z)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact fun h ↦ hw (sub_right_inj.mp h)
      filter_upwards [hmap.eventually (hZ (1 - z))] with w hw
      exact hw.trans (congrArg (_ * ·) (hdual w))
    obtain ⟨C, hC⟩ := globalConverse_normTwist_gaussian_strip_bounds_local χ⁻¹ S hD
      (sAdeleSchwartzFourier g) η⁻¹ hχ' hη' b m (fun w ↦ 1 - w) _hm (differentiable_const _ |>.sub differentiable_id)
      (fun w ↦ by simpa using Complex.abs_im_le_norm (1 - w)) hZ'
      (1 - d) (1 - a) (by linarith) (by linarith) (a - (1 - d) / 2) (1 - (1 - d) / 2) (by linarith)
      (fun w hw ↦ by
        simp only [Complex.sub_re, Complex.one_re]
        exact ⟨by linarith [hw.2], by linarith [hw.1]⟩) n
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzr : (1 - z).re ∈ Icc (1 - d) (1 - a) :=
      ⟨sub_le_sub_left hz.2 _, sub_le_sub_left hz.1 _⟩
    have hh := hC (mem_image_of_mem _ hzr)
    dsimp only at hh ⊢
    rw [sub_sub_cancel] at hh
    exact ((congrArg (fun v : ℂ ↦ ‖z ^ n * (m z * v)‖)
      ((sLocalZetaPair_mk η g).2 (hz.2.trans_lt hd)))).le.trans hh

/-- On the right half-plane the pole-cancelled completion reduces to the usual
Euler product times the pole polynomial, including the Gaussian normalization. -/
private theorem globalConverse_normTwist_multiplier (χ : U) (t : ℝ) (b : B)
    (hb : b ∈ bergmanIdeal(regularizedL(χ, t))) :
    ∃ m : ℂ → ℂ, Differentiable ℂ m ∧ ∀ s : halfPlane,
      b.val s = m s * gaussianCompletedHeckeL χ s := by
  obtain ⟨u, hu, he⟩ := hb
  let k : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  have hk : k ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F))))
  let p := polePolynomial(t)
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  refine ⟨fun z ↦ (p z * u z) / k, (hp.mul hu).div_const k, fun s ↦ ?_⟩
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hn : continuedCompletedHeckeL χ s ≠ 0 := (hEq s).trans_ne (mul_ne_zero
    (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property))
    (finiteHeckeL_ne_zero_of_one_lt_re χ s))
  have ha := (hL (mem_univ s.val)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((hL (mem_univ s.val)).meromorphicOrderAt_eq_zero_iff.mpr hn).ge
  have hprod : MeromorphicOn (p * continuedCompletedHeckeL χ) univ :=
    fun z hz ↦ (hp.analyticAt z).meromorphicAt.mul (hL hz).meromorphicAt
  rw [he, gaussianCompletedHeckeL_eq_completedHeckeL χ _ s.property]
  change toMeromorphicNFOn (p * continuedCompletedHeckeL χ) univ s * u s =
    _ * (k * completedHeckeL χ s)
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hprod (mem_univ s.val),
    toMeromorphicNFAt_eq_self.mpr ((hp.analyticAt s.val).mul ha).meromorphicNFAt]
  change p s * continuedCompletedHeckeL χ s * u s = _
  rw [hEq s]
  field_simp

/-- Agreement on the convergence half-plane uniquely determines a Schwartz–Bergman function. -/
private theorem globalConverse_normTwist_ext (b b' : B)
    (h : ∀ s : halfPlane, b.val s = b'.val s) : b = b' := by
  have hnf (v : B) : MeromorphicNFOn v.val univ := fun z _ ↦
    ((v.property.2.1.analyticAt (by simp : Complex.re ⁻¹' (univ : Set ℝ) ∈ 𝓝 z))).meromorphicNFAt
  exact Subtype.ext (eq_of_agree_rightHalf (hnf b) (hnf b') 1 fun z hz ↦ h ⟨z, hz⟩)

/-- Globalize the test supplied by the local converse. Weil's identity has the same
outside Euler product and Tamagawa masses for this test and the Gaussian. -/
private theorem globalConverse_normTwist_lift (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (b : B)
    (hb : b ∈ bergmanIdeal(regularizedL(χ, t))) :
    ∃ f : ℬ, ∀ s : halfPlane, Z(f, χ, (s : ℂ)) = b.val s := by
  obtain ⟨m, hm, hb⟩ := globalConverse_normTwist_multiplier χ t b hb
  obtain ⟨S, g, hg, hbounds⟩ := globalConverse_normTwist_gaussian_strip_bounds χ t ht b m hm hb
  obtain ⟨h, η, hη⟩ := globalConverse_normTwist_local_chart χ t ht S
  obtain ⟨f, hf⟩ := globalConverse_normTwist_local_lift η g m hm
    (hbounds η (h 0) (hη 0))
  refine ⟨sAdeleSchwartzToGlobal F S f, fun s ↦ ?_⟩
  have hz : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  have hi (v : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :=
    sLocalIdelicZFunction_eq_integral v ⟨η, (s : ℂ), hz, rfl⟩
  have he := hf s hz
  rw [hi f, hi g, ← hη] at he
  rw [hb, globalIdelicZFunction_eq_integral _ (globalTwist_mem_rightHalf χ s.property),
    gaussianCompletedHeckeL_eq_integral χ s s.property, ← hg,
    weilIdentity_unramifiedOutside S f χ _ s.property (h s),
    weilIdentity_unramifiedOutside S g χ _ s.property (h s), he]
  ring

/-- The polar transform is linear, and continuation identifies its exact range
once the inverse Tate integral problem is solved on the convergence half-plane. -/
private theorem globalConverse_normTwist_linear (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    ∃ M : P →ₗ[ℂ] B, (∀ (f : P) s, (M f).val s = Z(f.val, χ, s)) ∧
      Set.range M = bergmanIdeal(regularizedL(χ, t)) := by
  classical
  choose m hval using globalConverse_normTwist_bergman χ t ht
  let M : P →ₗ[ℂ] B :=
    { toFun := m
      map_add' f g := globalConverse_normTwist_ext _ _ fun s ↦ by
        change (m (f + g)).val s = (m f).val s + (m g).val s
        rw [hval, hval, hval]
        let c : {c : HeckeCharacter (𝓞 F) F // 0 ≤ globalIdelicOrderBound c} :=
          ⟨ideleClassNormTwist χ (s : ℂ), globalOrderBound_rightHalf χ s.property⟩
        exact congrArg (fun H ↦ H.val c) ((globalIdelicMellin (F := F)).map_add f.val g.val)
      map_smul' a f := globalConverse_normTwist_ext _ _ fun s ↦ by
        change (m (a • f)).val s = a • (m f).val s
        rw [hval, hval]
        let c : {c : HeckeCharacter (𝓞 F) F // 0 ≤ globalIdelicOrderBound c} :=
          ⟨ideleClassNormTwist χ (s : ℂ), globalOrderBound_rightHalf χ s.property⟩
        exact congrArg (fun H ↦ H.val c) ((globalIdelicMellin (F := F)).map_smul a f.val) }
  refine ⟨M, hval, Set.Subset.antisymm (Set.range_subset_iff.mpr fun f ↦ ?_) ?_⟩
  · obtain ⟨u, hu, he⟩ := globalConverse_normTwist_divides χ t ht f
    exact ⟨u, hu, fun z ↦ (hval f z).trans (he z)⟩
  · intro b hb
    obtain ⟨f, hf⟩ := globalConverse_normTwist_lift χ t ht b hb
    have hd : Differentiable ℂ b.val := fun z ↦ (b.property.2.1.analyticAt (by simp)).differentiableAt
    have he := eq_of_agree_rightHalf (globalIdelicZFunction_meromorphic f χ)
      (fun z _ ↦ (hd.analyticAt z).meromorphicNFAt) 1 (fun z hz ↦ hf ⟨z, hz⟩)
    let v : P := ⟨f, globalConverse_normTwist_polar χ t ht f (he ▸ hd.continuous)⟩
    exact ⟨v, Subtype.ext (funext fun z ↦ (hval v z).trans (congrFun he z))⟩

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
  classical
  obtain ⟨M, hval, hrange⟩ := globalConverse_normTwist_linear χ t _hχ
  have hclosed : IsClosed (Set.range M) := hrange ▸ globalConverse_normTwist_closed
    (globalConverse_normTwist_regular χ t _hχ).1
  have hB := schwartzBergman_frechet _ isOpen_univ ordConnected_univ univ_nonempty
  have hR := globalConverse_normTwist_frechet_subspace hB M.range hclosed
  let v : ℬ →L[ℂ] ℂ × ℂ := ⟨adelePolarValues, adelePolarValues_continuous⟩
  obtain ⟨j, hj⟩ := v.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (adelePolarValues_surjective (F := F)))
  let r : ℬ →L[ℂ] P := v.projKerOfRightInverse j fun y ↦ DFunLike.congr_fun hj y
  have hr (f : P) : r f.val = f := v.projKerOfRightInverse_apply_idem _ _ f
  let T := M.rangeRestrict.comp r.toLinearMap
  have hs : Surjective T := fun b ↦ (M.surjective_rangeRestrict b).elim fun f hf ↦
    ⟨f.val, (congrArg M.rangeRestrict (hr f)).trans hf⟩
  have hgraph : IsClosed (T.graph : Set (ℬ × M.range)) := by
    let E (s : halfPlane) (p : ℬ × M.range) := globalIdelicZetaIntegral (r p.1).val
      (ideleClassNormTwist χ (s : ℂ))
    have he (x : ℬ) (s : halfPlane) : (T x).val.val s =
        globalIdelicZetaIntegral (r x).val (ideleClassNormTwist χ (s : ℂ)) :=
      (hval _ s).trans (globalIdelicZFunction_eq_integral _ (globalTwist_mem_rightHalf χ s.property))
    have hh : (T.graph : Set (ℬ × M.range)) =
        ⋂ s : halfPlane, {p | p.2.val.val s = E s p} := by
      ext p
      rw [Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_graph_iff]
      exact ⟨fun h s ↦ (congrArg (fun b : M.range ↦ b.val.val s) h).trans (he _ s),
        fun h ↦ Subtype.ext (globalConverse_normTwist_ext _ _ fun s ↦ (h s).trans (he _ s).symm)⟩
    rw [hh]
    apply isClosed_iInter
    intro s
    have hc : Continuous (fun b : B ↦ b.val (s : ℂ)) := by
      simpa only [iteratedDeriv_zero] using globalConverse_normTwist_continuous_jet s 0
    exact isClosed_eq (hc.comp (continuous_subtype_val.comp continuous_snd))
      ((continuous_globalIdelicZetaIntegral _ (globalTwist_mem_rightHalf χ s.property)).comp
        (continuous_subtype_val.comp (r.continuous.comp continuous_fst)))
  obtain ⟨hc, ho⟩ := globalConverse_normTwist_graph (adeleSchwartz_strictLF (F := F)).2 hR T hs hgraph
  have hMr (f : P) : T f.val = M.rangeRestrict f := congrArg M.rangeRestrict (hr f)
  let A : P →L[ℂ] B := ⟨M, continuous_subtype_val.comp
    ((hc.comp continuous_subtype_val).congr hMr)⟩
  refine ⟨A, ?_, hclosed, hval, hrange, ?_⟩
  · intro W hW
    have hsurj : Surjective r := fun f ↦ ⟨f.val, hr f⟩
    change IsOpen (M.rangeRestrict '' W)
    rw [← Set.image_preimage_eq W hsurj, Set.image_image]
    exact ho _ (hW.preimage r.continuous)
  · ext f
    rw [LinearMap.mem_ker, Submodule.mem_comap, globalConverse_normTwist_kernel χ t _hχ]
    exact ⟨fun h s _ ↦ (hval f s).symm.trans (congrArg (fun b : B ↦ b.val s) h),
      fun h ↦ globalConverse_normTwist_ext _ _ fun s ↦ (hval f s).trans (h s s.property)⟩

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

/-- Unit translation scales the homogeneous adelic theta linear map by the character value. -/
theorem globalConverse_nontrivial_exact_theta_translate (ω : PontryaginDual C₁)
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

/-- A zero homogeneous theta function has zero Mellin continuation on the trivial
component. The residue formulas at zero and one then force both polar values to vanish. -/
private theorem globalConverse_normTwist_exact_kernel (hm : mass ≠ 0) : K(1) ≤ P := by
  intro f hf
  have hθ : homogeneousAdelicTheta 1 f = 0 := hf
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hZ := (homogeneousThetaMellinIntegral_meromorphicContinuation τ 1 f
    (canonicalIdeleNormSection_rightInverse F) (1 : U) (fun _ ↦ rfl) 0).mp
    ⟨fun _ _ ↦ analyticAt_const.meromorphicNFAt, fun s _ ↦ by
      change 0 = ∫ t, homogeneousAdelicTheta 1 f (QuotientGroup.mk (τ t)) *
        ideleClassNormTwist (1 : U) s (QuotientGroup.mk (τ t)) ∂positiveRealHaar
      simp only [hθ, ContinuousMap.zero_apply, zero_mul, integral_zero]⟩
  have hz (s : ℂ) : globalIdelicZFunction f (ideleClassNormTwist (1 : U) s) = 0 :=
    (congrFun hZ s).symm
  have h₀ := globalIdelicZFunction_residue_zero f
  have h₁ := globalIdelicZFunction_residue_one f
  simp only [hz, mul_zero] at h₀ h₁
  exact (mem_adelePolarSubspace f).mpr
    ⟨(mul_eq_zero.mp (tendsto_nhds_unique h₀ tendsto_const_nhds)).resolve_left (neg_ne_zero.mpr hm),
     (mul_eq_zero.mp (tendsto_nhds_unique h₁ tendsto_const_nhds)).resolve_left hm⟩

/-- The signed polar values descend through a quotient by a submodule of their common kernel.
The polar subspace is the full preimage of its image, so the open quotient
map restricts to an open quotient map on that subspace. -/
private theorem globalConverse_normTwist_exact_quotient.{u} {E : Type u}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (p : E →ₗ[ℂ] ℂ × ℂ) (hp : Continuous p) (hs : Surjective p)
    (K : Submodule ℂ E) (hk : K ≤ p.ker) (m : ℂ) (hm : m ≠ 0) :
    ∃ R : (E ⧸ K) →L[ℂ] ℂ × ℂ,
      (∀ f, R (K.mkQ f) = (-m * (p f).1, m * (p f).2)) ∧
      R.ker = p.ker.map K.mkQ ∧ IsOpenQuotientMap R ∧
      IsOpenQuotientMap ((K.mkQ.comp p.ker.subtype).rangeRestrict) := by
  let q := K.liftQL (⟨p, hp⟩ : E →L[ℂ] ℂ × ℂ) hk
  let scale (u : ℂˣ) : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft u
  let d := (scale (Units.mk0 (-m) (neg_ne_zero.mpr hm))).prodCongr (scale (Units.mk0 m hm))
  let R := d.toContinuousLinearMap.comp q
  have hsur : Surjective R := by
    intro z
    obtain ⟨f, hf⟩ := hs (d.symm z)
    exact ⟨K.mkQ f, (congrArg d hf).trans (d.apply_symm_apply z)⟩
  refine ⟨R, fun _ ↦ rfl, (d.toLinearEquiv.ker_comp q.toLinearMap).trans (K.ker_liftQ p hk),
    ⟨hsur, R.continuous, R.toLinearMap.isOpenMap_of_finiteDimensional hsur⟩, ?_⟩
  let W := (K.mkQ.comp p.ker.subtype).range
  have hpre : W.comap K.mkQ = p.ker := by
    simp only [W, LinearMap.range_comp, Submodule.range_subtype, Submodule.comap_map_mkQ,
      sup_of_le_right hk]
  let e : p.ker ≃ₜ (K.mkQ ⁻¹' (W : Set (E ⧸ K))) :=
    Homeomorph.setCongr (congrArg SetLike.coe hpre.symm)
  exact (K.isOpenQuotientMap_mkQ.restrictPreimage W).comp e.isOpenQuotientMap

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
  let μ := normOneIdeleClassTamagawaMeasure F
  let : MeasurableSpace C𝔽 := borel _
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hm : mass ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ)).ne'
  exact globalConverse_normTwist_exact_quotient (E := ℬ) (adelePolarValues (F := F))
    adelePolarValues_continuous adelePolarValues_surjective (K(1))
    (globalConverse_normTwist_exact_kernel hm) _ hm

-- TODO(paper-gap): In (6.3.2.8), the middle ideal contains functions with
-- poles, so intersection with the entire Schwartz–Bergman space kills both
-- residues. The first pole-cancelling factor must be s + it₀.

/-- The norm parametrizes all quasi-characters trivial on norm-one classes. -/
private theorem globalConverse_normTwist_meromorphic_exact_parameter
    (c : QuasiCharacter C𝔽) (hc : ∀ h : C₁, c h.val = 1) :
    ∃! z : ℂ, c = ideleClassNormTwist (1 : U) z := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨z, hz, hu⟩ := existsUnique_complexPower (c.comp σ)
  have hval (w : ℂ) (g : C𝔽) : ideleClassNormTwist (1 : U) w g =
      (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ w := one_mul _
  refine ⟨z, ?_, fun w hw ↦ hu w (fun r ↦ ?_)⟩
  · ext1 g
    have hk : g * (σ (ideleClassNorm F g))⁻¹ ∈ C₁ := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    have he := hc ⟨_, hk⟩
    change c (g * (σ (ideleClassNorm F g))⁻¹) = 1 at he
    have hn : c (σ (ideleClassNorm F g)) ≠ 0 := ((Group.isUnit _).map c.toMonoidHom).ne_zero
    rw [map_mul, map_inv, ← div_eq_mul_inv, div_eq_one_iff_eq hn] at he
    exact he.trans ((hz _).trans (hval _ _).symm)
  · change c (σ r) = _
    rw [hw, hval, hσ r]

/-- The two exceptional parameters are exactly the nonregular characters in this chart. -/
private theorem globalConverse_normTwist_meromorphic_exact_regular (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (s : ℂ) :
    0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ s) ↔
      s ∈ ({-shift(t), 1 - shift(t)} : Set ℂ)ᶜ := by
  have oneTw : ideleClassNormTwist (1 : U) 0 = 1 := by
    ext1 g
    change (1 : ℂ) * (((((ideleClassNorm F g).val : ℝ) : ℂ)) ^ (0 : ℂ)) = 1
    simp
  have inj : Injective (ideleClassNormTwist (1 : U)) := by
    intro v w he
    have hc (h : C₁) : ideleClassNormTwist (1 : U) v h.val = 1 := by
      change 1 * ((((ideleClassNorm F h.val).val : ℝ) : ℂ) ^ v) = 1
      simp [MonoidHom.mem_ker.mp h.property]
    exact (globalConverse_normTwist_meromorphic_exact_parameter _ hc).unique rfl he
  have hs : ideleClassNormTwist χ s = ideleClassNormTwist (1 : U) (shift(t) + s) := by
    simpa only [zero_add] using ideleClassNormTwist_add_of_eq ht s
  rw [globalIdelicOrderBound, hs, ← oneTw]
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, inj.eq_iff]
  split_ifs with h
  · simp only [not_le_of_gt (show (-1 : WithTop ℤ) < 0 by decide), false_iff, not_not]
    rcases h with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · simp only [le_refl, true_iff]
    rintro (rfl | rfl) <;> apply h <;> simp

/-- Reindexing regular values along a surjection preserves injectivity. -/
private theorem globalConverse_normTwist_meromorphic_exact_reindex
    {X A D : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace D]
    (Y : Submodule ℂ C(D, ℂ)) (Z : X →ₗ[ℂ] Y) (hZ : Injective Z) (i : A → D) (hi : Surjective i) :
    ∃ M : X →ₗ[ℂ] A → ℂ, Injective M ∧ ∀ x s, M x s = (Z x).val (i s) := by
  let M : X →ₗ[ℂ] A → ℂ := LinearMap.pi fun s ↦
    ((ContinuousMap.evalCLM ℂ (i s)).toLinearMap.comp Y.subtype).comp Z
  refine ⟨M, fun x y he ↦ hZ (Subtype.ext (ContinuousMap.ext fun d ↦ ?_)), fun _ _ ↦ rfl⟩
  obtain ⟨s, rfl⟩ := hi d
  exact congrFun he s

/-- Restriction of the injective homogeneous Mellin transform to the punctured norm chart. -/
private theorem globalConverse_normTwist_meromorphic_exact_chart (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    let regular := ({-shift(t), 1 - shift(t)} : Set ℂ)ᶜ
    ∃ M : Θ(1) →ₗ[ℂ] regular → ℂ, Injective M ∧
      ∀ (f : ℬ) (s : regular), M ((K(1)).mkQ f) s = Z(f, χ, s.val) := by
  intro regular
  obtain ⟨Z, hZ, hrep⟩ := exists_globalHomogeneousThetaMellin (F := F) 1
  have htw (s : ℂ) : ideleClassNormTwist χ s = ideleClassNormTwist (1 : U) (shift(t) + s) := by
    simpa only [zero_add] using ideleClassNormTwist_add_of_eq ht s
  let Ω : Type _ := {c : QuasiCharacter C𝔽 // ∀ h : C₁, c h.val = ((1 : PontryaginDual C₁) h : ℂ)}
  let tw (s : regular) : {c : Ω // 0 ≤ globalIdelicOrderBound c.val} :=
    ⟨⟨ideleClassNormTwist χ s.val, fun h ↦ by
        rw [htw]
        change (1 : ℂ) * ((((ideleClassNorm F h.val).val : ℝ) : ℂ) ^ (shift(t) + s.val)) = 1
        simp [MonoidHom.mem_ker.mp h.property]⟩,
      (globalConverse_normTwist_meromorphic_exact_regular χ t ht s.val).2 s.property⟩
  have hsur : Surjective tw := by
    intro c
    obtain ⟨w, hw, -⟩ := globalConverse_normTwist_meromorphic_exact_parameter c.val.val
      (fun h ↦ c.val.property h)
    have he : ideleClassNormTwist χ (w - shift(t)) = c.val.val := by
      rw [htw, add_sub_cancel, ← hw]
    exact ⟨⟨_, (globalConverse_normTwist_meromorphic_exact_regular χ t ht _).1
      (he.symm ▸ c.property)⟩, Subtype.ext (Subtype.ext he)⟩
  obtain ⟨M, hinj, hM⟩ := globalConverse_normTwist_meromorphic_exact_reindex
    _ Z.toLinearMap hZ tw hsur
  exact ⟨M, hinj, fun f s ↦ (hM _ s).trans (hrep f (tw s))⟩

/-- As in the principal-value residue calculation below, a finite limit of the pole-cancelled transform gives its contour residue. -/
private theorem globalConverse_normTwist_meromorphic_exact_residue (M : ℂ → ℂ) (r c : ℂ)
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

/-- Tate's limits persist after shifting the chart and changing the values at either pole. -/
private theorem globalConverse_normTwist_meromorphic_exact_limits (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (f : ℬ) (g : ℂ → ℂ)
    (hg : ∀ s ∈ ({-shift(t), 1 - shift(t)} : Set ℂ)ᶜ, g s = Z(f, χ, s)) :
    Tendsto (fun z ↦ (z - -shift(t)) * g z) (𝓝[≠] (-shift(t))) (𝓝 (-mass * f zeroAdele)) ∧
    Tendsto (fun z ↦ (z - (1 - shift(t))) * g z) (𝓝[≠] (1 - shift(t)))
      (𝓝 (mass * adeleSchwartzFourier f zeroAdele)) := by
  have tw (z : ℂ) : ideleClassNormTwist χ z = ideleClassNormTwist (1 : U) (z + shift(t)) := by
    simpa only [zero_add, add_comm (shift(t))] using ideleClassNormTwist_add_of_eq ht z
  have shiftLimit (r c : ℂ) (hr : Tendsto (fun z ↦ (z - r) * Z(f, 1, z)) (𝓝[≠] r) (𝓝 c)) :
      Tendsto (fun z ↦ (z - (r - shift(t))) * g z) (𝓝[≠] (r - shift(t))) (𝓝 c) := by
    have hadd : Tendsto (fun z : ℂ ↦ z + shift(t)) (𝓝[≠] (r - shift(t))) (𝓝[≠] r) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun z : ℂ ↦ z + shift(t)) := continuous_id.add continuous_const
        simpa only [sub_add_cancel] using
          (hc.continuousAt (x := r - shift(t))).tendsto.mono_left (nhdsWithin_le_nhds (s := {r - shift(t)}ᶜ))
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact fun h ↦ hz (eq_sub_iff_add_eq.mpr h)
    apply (hr.comp hadd).congr'
    filter_upwards [nhdsNE_le_codiscrete _ (Set.toFinite {-shift(t), 1 - shift(t)}).compl_mem_codiscrete]
      with z hz
    change (z + shift(t) - r) * Z(f, 1, z + shift(t)) = _
    rw [hg z hz, tw]
    ring
  exact ⟨by simpa only [zero_sub] using shiftLimit 0 _ (by
            simpa only [sub_zero] using globalIdelicZFunction_residue_zero f),
    shiftLimit 1 _ (globalIdelicZFunction_residue_one f)⟩

/-- The shifted poles are simple, so the regularized completion is entire and
is nonzero at both canceled poles. -/
private theorem globalConverse_normTwist_meromorphic_exact_generator (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    let G := regularizedL(χ, t)
    Differentiable ℂ G ∧ G (-shift(t)) ≠ 0 ∧ G (1 - shift(t)) ≠ 0 ∧
      ∀ z ∈ ({-shift(t), 1 - shift(t)} : Set ℂ)ᶜ,
        G z = polePolynomial(t) z * continuedCompletedHeckeL χ z := by
  let b := shift(t)
  let p := polePolynomial(t)
  let L := continuedCompletedHeckeL χ
  let G := toMeromorphicNFOn (p * L) univ
  have hL := (continuedCompletedHeckeL_spec χ).1
  have hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext x
    have he := DFunLike.congr_fun ht x.val
    change (χ x.val : ℂ) * _ ^ (0 : ℂ) = 1 * ((((ideleClassNorm F x.val).val : ℝ) : ℂ) ^ b) at he
    change (χ x.val : ℂ) = 1
    simpa only [Complex.cpow_zero, mul_one, MonoidHom.mem_ker.mp x.property, Units.val_one,
      NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul] using he
  have hω : χ₁(χ) = 1 := PontryaginDual.ext fun x ↦ DFunLike.congr_fun hk x
  obtain ⟨u, ⟨hu, h₀, h₁, haway⟩, -⟩ := completedHeckeL_continuation_simplePoles χ L hL
    (continuedCompletedHeckeL_spec χ).2 hk
  have htu : t = -u := (globalConverse_existsUnique_normTwist χ hω).unique ht (by
    convert hu using 2; push_cast; ring)
  have hb : Complex.I * (u : ℂ) = -b := by dsimp [b]; rw [htu]; push_cast; ring
  rw [hb] at h₀ h₁ haway
  simp only [← sub_eq_add_neg] at h₁ haway
  have hp (s : ℂ) : AnalyticAt ℂ p s := by dsimp [p]; fun_prop
  have hmer : MeromorphicOn (p * L) univ := fun z hz ↦ (hp z).meromorphicAt.mul (hL hz).meromorphicAt
  have hn (z : ℂ) : MeromorphicNFAt G z := meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ z)
  have cancel (z : ℂ) (hz : p z = 0) (hd : (1 - z - b) - (z + b) ≠ 0)
      (ho : meromorphicOrderAt L z = -1) : meromorphicOrderAt G z = 0 := by
    have hder : HasDerivAt p ((1 - z - b) - (z + b)) z := by
      simpa [p, b, sub_eq_add_neg] using ((hasDerivAt_id z).add_const b).fun_mul
        (((hasDerivAt_const z (1 : ℂ)).fun_sub (hasDerivAt_id z)).sub_const b)
    have h1 := (hp z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz (by rwa [hder.deriv])
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z),
      meromorphicOrderAt_mul (hp z).meromorphicAt (hL (mem_univ z)).meromorphicAt,
      (hp z).meromorphicOrderAt_eq, h1, ho]
    norm_num
  have ha := cancel (-b) (by dsimp [p, b]; ring) (by ring_nf; norm_num) h₀
  have hc := cancel (1 - b) (by dsimp [p, b]; ring) (by ring_nf; norm_num) h₁
  refine ⟨fun z ↦ ((hn z).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_).differentiableAt,
    (hn _).meromorphicOrderAt_eq_zero_iff.mp ha, (hn _).meromorphicOrderAt_eq_zero_iff.mp hc, ?_⟩
  · by_cases hz : z ∈ ({-b, 1 - b} : Set ℂ)ᶜ
    · rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z)]
      exact ((hp z).mul (haway z hz)).meromorphicOrderAt_nonneg
    · simp only [mem_compl_iff, not_not, mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      exacts [ha.ge, hc.ge]
  · intro z hz
    exact (toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (mem_univ z)).trans
      (congrFun (toMeromorphicNFAt_eq_self.mpr ((hp z).mul (haway z hz)).meromorphicNFAt) z)

/-- A normalized adelic Hecke test and translation by an idèle of norm exp(1)
realize the completion and multiplication by the exponential on the regular chart. -/
private theorem globalConverse_normTwist_meromorphic_exact_translates (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    (∃ f : ℬ, ∀ s : ℂ, Z(f, χ, s) = continuedCompletedHeckeL χ s) ∧
    ∀ f : ℬ, ∃ g : ℬ, ∀ s ∈ ({-shift(t), 1 - shift(t)} : Set ℂ)ᶜ,
      Z(g, χ, s) = Complex.exp (s + shift(t)) * Z(f, χ, s) := by
  constructor
  · obtain ⟨f, hf⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL χ
    refine ⟨f, congrFun ?_⟩
    have hZ := globalIdelicZFunction_meromorphic f χ
    obtain ⟨hL, hLhalf⟩ := continuedCompletedHeckeL_spec χ
    rw [← toMeromorphicNFOn_eq_self.mpr hZ, ← toMeromorphicNFOn_eq_self.mpr hL]
    apply heckeEulerProductOutside_eq_finite_nf_eq _ _ hZ.meromorphicOn hL.meromorphicOn
    intro z hz
    have habs := quasiCharacterAbscissa_ideleClassNormTwist χ z
    exact (globalIdelicZFunction_eq_integral f (show 1 < quasiCharacterAbscissa _ _ _ _ by rwa [habs])).trans
      ((hf ⟨z, hz⟩).trans (hLhalf ⟨z, hz⟩).symm)
  · let r := Units.mk0 (⟨Real.exp 1, (Real.exp_pos 1).le⟩ : ℝ≥0)
      (fun he ↦ (Real.exp_pos 1).ne' (congrArg NNReal.toReal he))
    let u := canonicalIdeleNormSection F r
    have hu : ideleClassNorm F (QuotientGroup.mk u) = r := canonicalIdeleNormSection_rightInverse F r
    intro f
    refine ⟨schwartzBruhatUnitTranslate u f, fun z hz ↦ ?_⟩
    have he := globalIdelicMellin_unitTranslate u f ⟨_, (globalConverse_normTwist_meromorphic_exact_regular χ t ht z).2 hz⟩
    refine he.trans (congrArg (· * Z(f, χ, z)) ?_)
    have htw : ideleClassNormTwist χ z = ideleClassNormTwist (1 : U) (z + shift(t)) := by
      simpa only [zero_add, add_comm (shift(t))] using ideleClassNormTwist_add_of_eq ht z
    change ideleClassNormTwist χ z (QuotientGroup.mk u) = _
    rw [htw]
    change (1 : ℂ) * ((((ideleClassNorm F (QuotientGroup.mk u)).val : ℝ) : ℂ) ^ (z + shift(t))) = _
    rw [hu, one_mul]
    change (Real.exp 1 : ℂ) ^ (z + shift(t)) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_one, one_mul]

/-- Two open quotients of the polar tests by the same kernel have canonically
linearly homeomorphic ranges. -/
private theorem globalConverse_normTwist_meromorphic_exact_equiv {X Y W : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (q : X →ₗ[ℂ] Y) (z : X →ₗ[ℂ] W) (hq : IsOpenQuotientMap q)
    (hz : IsOpenQuotientMap z) (hk : q.ker = z.ker) :
    ∃ e : Y ≃L[ℂ] W, ∀ x, e (q x) = z x := by
  let e := (q.quotKerEquivOfSurjective hq.surjective).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (z.quotKerEquivOfSurjective hz.surjective))
  have he (x : X) : e (q x) = z x := by
    simp only [e, LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have he' (x : X) : e.symm (z x) = q x := by rw [← he, e.symm_apply_apply]
  have hcont : Continuous e := hq.isQuotientMap.continuous_iff.mpr
    ((show e ∘ q = z from funext he).symm ▸ hz.continuous)
  have hinv : Continuous e.symm := hz.isQuotientMap.continuous_iff.mpr
    ((show e.symm ∘ z = q from funext he').symm ▸ hq.continuous)
  exact ⟨{e with continuous_toFun := hcont, continuous_invFun := hinv}, he⟩

/-- Multiplication by a linear factor preserves Schwartz bounds on strips.
The converse follows by bounding the quotient on the unit disk around the root. -/
private theorem globalConverse_normTwist_meromorphic_exact_linearFactor
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (a : ℂ) :
    (fun z ↦ (z - a) * f z) ∈ schwartzBergmanSubmodule univ ↔
      f ∈ schwartzBergmanSubmodule univ := by
  constructor
  · intro h
    refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hf.differentiableOn, fun l r hlr hI n ↦ ?_⟩
    obtain ⟨A, hA⟩ := h.2.2 l r hlr hI n
    obtain ⟨C, hC⟩ := (isCompact_closedBall a 1).exists_bound_of_continuousOn
      (f := fun z : ℂ ↦ z ^ n * f z) ((continuous_pow n).mul hf.continuous).continuousOn
    refine ⟨max A C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    by_cases hza : z ∈ Metric.closedBall a 1
    · exact (hC z hza).trans (le_max_right _ _)
    · have h1 : 1 ≤ ‖z - a‖ := (lt_of_not_ge (by simpa [Metric.mem_closedBall, dist_eq_norm] using hza)).le
      have hh : ‖z ^ n * ((z - a) * f z)‖ ≤ A := hA ⟨z, hz, rfl⟩
      rw [mul_left_comm, norm_mul] at hh
      exact (le_mul_of_one_le_left (norm_nonneg _) h1).trans (hh.trans (le_max_left _ _))
  · intro h
    have hz : (fun z ↦ z * f z) ∈ schwartzBergmanSubmodule univ := by
      refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, (differentiable_id.mul hf).differentiableOn,
        fun l r hlr hI n ↦ ?_⟩
      simpa only [pow_succ, mul_assoc] using h.2.2 l r hlr hI (n + 1)
    convert (schwartzBergmanSubmodule univ).sub_mem hz ((schwartzBergmanSubmodule univ).smul_mem a h) using 1
    ext z
    exact sub_mul z a (f z)

/-- Multiplication by the exponential of a shifted coordinate is bounded on every vertical strip. -/
private theorem globalConverse_normTwist_meromorphic_exact_exp (f : B) (a : ℂ) :
    (fun z ↦ Complex.exp (z - a) * f.val z) ∈ schwartzBergmanSubmodule univ := by
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, ?_, fun l r hlr hI n ↦ ?_⟩
  · exact (differentiable_id.sub_const a).cexp.differentiableOn.mul f.property.2.1
  · obtain ⟨A, hA⟩ := f.property.2.2 l r hlr hI n
    refine ⟨Real.exp (r - a.re) * A, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ n * (Complex.exp (z - a) * f.val z)‖ ≤ _
    rw [mul_left_comm, norm_mul, Complex.norm_exp, Complex.sub_re]
    exact mul_le_mul (Real.exp_le_exp.mpr (sub_le_sub_right hz.2 _)) (hA ⟨z, hz, rfl⟩)
      (norm_nonneg _) (Real.exp_pos _).le

/-- Entire interpolation at two distinct points makes the difference divisible by both factors. -/
private theorem globalConverse_normTwist_meromorphic_exact_divide (a b : ℂ) (hab : a ≠ b)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (ha : f a = 0) (hb : f b = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = (z - a) * (b - z) * g z := by
  let v := dslope f a
  have hv : Differentiable ℂ v := fun z ↦ ((hf.analyticAt z).dslope a).differentiableAt
  have h (z : ℂ) : (z - a) * v z = f z := sub_smul_dslope_of_zero ha z
  have hvb : v b = 0 := (mul_eq_zero.mp ((h b).trans hb)).resolve_left (sub_ne_zero.mpr hab.symm)
  have hd : Differentiable ℂ (dslope v b) := fun z ↦ ((hv.analyticAt z).dslope b).differentiableAt
  refine ⟨-dslope v b, hd.neg, fun z ↦ ?_⟩
  have he : (z - b) * dslope v b z = v z := sub_smul_dslope_of_zero hvb z
  rw [← h, ← he]
  change _ = _ * -_
  ring

/-- Recover the meromorphic range from the pole-free range. The Hecke test and its
translate interpolate the two residues. A second translation gives a periodic
multiple with both residues zero, which supplies the strip bounds for the generator. -/
private theorem globalConverse_normTwist_meromorphic_exact_image {X : Type*}
    [AddCommGroup X] [Module ℂ X] (a b : ℂ) (hba : b - a = 1)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G) (ha : G a ≠ 0) (hb : G b ≠ 0)
    (M : X →ₗ[ℂ] (({a, b}ᶜ : Set ℂ) → ℂ)) (R : X →ₗ[ℂ] ℂ × ℂ)
    (hzero : ∀ x, R x = 0 → ∃ v : B, v ∈ bergmanIdeal(G) ∧ ∀ z, M x z = v.val z.val)
    (hlift : ∀ v : B, v ∈ bergmanIdeal(G) → ∃ x, ∀ z, M x z = v.val z.val)
    (hvalues : ∀ (x : X) (v : ℂ → ℂ), Continuous v →
      (∀ z : ({a, b}ᶜ : Set ℂ), v z.val = (z.val - a) * (b - z.val) * M x z) → R x = (v a, -v b))
    (x₀ : X) (hx₀ : ∀ z : ({a, b}ᶜ : Set ℂ), G z.val = (z.val - a) * (b - z.val) * M x₀ z)
    (htranslate : ∀ x, ∃ y, ∀ z, M y z = Complex.exp (z.val - a) * M x z) :
    ∀ h, h ∈ M.range ↔ ∃ v : B, v ∈ bergmanIdeal(G) ∧
      ∀ z : ({a, b}ᶜ : Set ℂ), v.val z.val = (z.val - a) * (b - z.val) * h z := by
  let E (z : ℂ) := Complex.exp (z - a)
  let p (z : ℂ) := (z - a) * (b - z)
  have hE : Differentiable ℂ E := (differentiable_id.sub_const a).cexp
  have hp : Differentiable ℂ p := by dsimp [p]; fun_prop
  have hab : a ≠ b := by rintro rfl; simp at hba
  have he₀ : E a = 1 := by simp [E]
  have he₁ : E b ≠ 1 := by
    change Complex.exp (b - a) ≠ 1
    rw [hba, ← Complex.ofReal_one, ← Complex.ofReal_exp]
    exact Complex.ofReal_injective.ne (Real.one_lt_exp_iff.mpr zero_lt_one).ne'
  have entire (v : B) : Differentiable ℂ v.val :=
    fun z ↦ (v.property.2.1 z (by simp)).differentiableAt (by simp)
  have hpoly (v : ℂ → ℂ) (hv : Differentiable ℂ v) :
      (fun z ↦ p z * v z) ∈ schwartzBergmanSubmodule univ ↔ v ∈ schwartzBergmanSubmodule univ := by
    have he : (fun z ↦ p z * v z) = -(fun z ↦ (z - a) * ((z - b) * v z)) := by
      funext z; change (z - a) * (b - z) * v z = -_; ring
    rw [he, Submodule.neg_mem_iff, globalConverse_normTwist_meromorphic_exact_linearFactor
      (fun z ↦ (z - b) * v z) ((differentiable_id.sub_const b).mul hv) a,
      globalConverse_normTwist_meromorphic_exact_linearFactor _ hv b]
  obtain ⟨x₁, hx₁⟩ := htranslate x₀
  obtain ⟨x₂, hx₂⟩ := htranslate x₁
  let u (A C z : ℂ) := A + C * E z
  let x (A C : ℂ) := A • x₀ + C • x₁
  have hu (A C : ℂ) : Differentiable ℂ (u A C) := (differentiable_const A).add (hE.const_mul C)
  have hx (A C : ℂ) (z : ({a, b}ᶜ : Set ℂ)) :
      G z.val * u A C z.val = p z.val * M (x A C) z := by
    simp only [x, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx₁]
    rw [hx₀ z]
    change _ * (A + C * E z.val) = _
    ring
  have chooseCoeffs (v w : ℂ) : ∃ A C, u A C a = v ∧ u A C b = w := by
    let C := (w - v) / (E b - 1)
    refine ⟨v - C, C, ?_, ?_⟩
    · simp [u, he₀]
    · change v - C + C * E b = w
      have hc : C * (E b - 1) = w - v := div_mul_cancel₀ _ (sub_ne_zero.mpr he₁)
      linear_combination hc
  -- The double difference clears both residues and has a periodic Mellin multiplier.
  let D (z : ℂ) := (E z - 1) * (E z - E b)
  let y := x₂ - x (-(E b)) (1 + E b)
  have hD : Differentiable ℂ D := (hE.sub_const _).mul (hE.sub_const _)
  have hy (z : ({a, b}ᶜ : Set ℂ)) : D z.val * G z.val = p z.val * M y z := by
    rw [show M y z = M x₂ z - M (x (-(E b)) (1 + E b)) z from congrFun (map_sub M _ _) z,
      mul_sub, ← hx, hx₂, hx₁, hx₀]
    dsimp only [D, u, E, p]
    ring
  have hy₀ : R y = 0 := by
    rw [hvalues y (D * G) (hD.mul hG).continuous hy]
    simp [D, he₀]
  obtain ⟨v, -, hv⟩ := hzero y hy₀
  have heq : D * G = fun z ↦ p z * v.val z := by
    funext z
    apply tendsto_nhds_unique ((hD.mul hG).continuous.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {z}ᶜ)))
    apply ((hp.mul (entire v)).continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [nhdsNE_le_codiscrete z (Set.toFinite {a, b}).compl_mem_codiscrete] with w hw
    exact (congrArg (p w * ·) (hv ⟨w, hw⟩).symm).trans (hy ⟨w, hw⟩).symm
  have hB : G ∈ schwartzBergmanSubmodule univ := by
    have hne : D (b + 1) ≠ 0 := by
      have htwo : b + 1 - a = 2 := by linear_combination hba
      have h1 : (Real.exp 2 : ℂ) ≠ 1 := by
        exact_mod_cast (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      have h2 : (Real.exp 2 : ℂ) ≠ (Real.exp 1 : ℝ) := by
        exact_mod_cast Real.exp_injective.ne (by norm_num : (2 : ℝ) ≠ 1)
      dsimp only [D, E]
      rw [htwo, hba]
      simpa only [Complex.ofReal_exp, Complex.ofReal_ofNat, Complex.ofReal_one] using
        mul_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)
    apply schwartzBergman_of_periodic_mul hD ⟨_, hne⟩ Real.two_pi_pos (G := G) _ hG
    · change D * G ∈ _
      rw [heq]
      exact (hpoly v.val (entire v)).2 v.property
    · intro z
      have per : E (z + (↑(2 * Real.pi) : ℂ) * Complex.I) = E z := by
        change Complex.exp _ = Complex.exp _
        push_cast
        rw [show z + (2 * (Real.pi : ℂ)) * Complex.I - a = (z - a) + 2 * Real.pi * Complex.I by ring,
          Complex.exp_periodic]
      simp only [D, per]
  have hGu (A C : ℂ) : (fun z ↦ G z * u A C z) ∈ schwartzBergmanSubmodule univ := by
    let v : B := ⟨G, hB⟩
    have he : (fun z ↦ G z * u A C z) = A • G + C • (fun z ↦ Complex.exp (z - a) * v.val z) := by
      funext z; change G z * (A + C * E z) = A * G z + C * (E z * G z); ring
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ A hB)
      (Submodule.smul_mem _ C (globalConverse_normTwist_meromorphic_exact_exp v a))
  intro h
  constructor
  · -- Match the residues, then apply the pole-free range theorem to the difference.
    rintro ⟨w, rfl⟩
    obtain ⟨A, C, hA, hC⟩ := chooseCoeffs ((R w).1 / G a) (-(R w).2 / G b)
    have hRx : R (x A C) = R w := by
      rw [hvalues (x A C) _ (hG.mul (hu A C)).continuous (hx A C)]
      apply Prod.ext
      · change G a * u A C a = _
        rw [hA]; field_simp
      · change -(G b * u A C b) = _
        rw [hC]; field_simp
    obtain ⟨v, ⟨k, hk, hvk⟩, hv⟩ := hzero (w - x A C) (by rw [map_sub, hRx, sub_self])
    refine ⟨⟨_, (schwartzBergmanSubmodule univ).add_mem ((hpoly _ (entire v)).2 v.property) (hGu A C)⟩,
      ⟨fun z ↦ p z * k z + u A C z, (hp.mul hk).add (hu A C), fun z ↦ ?_⟩, fun z ↦ ?_⟩
    · change p z * v.val z + G z * u A C z = _
      rw [hvk]; ring
    · change p _ * v.val _ + G _ * u A C _ = _
      rw [← hv z, hx, map_sub, Pi.sub_apply]
      change _ = p _ * _
      ring
  · -- Interpolate the entire multiplier and divide the remainder by both linear factors.
    rintro ⟨v, ⟨k, hk, hvk⟩, hv⟩
    obtain ⟨A, C, hA, hC⟩ := chooseCoeffs (k a) (k b)
    obtain ⟨g, hg, hquot⟩ := globalConverse_normTwist_meromorphic_exact_divide a b hab (k - u A C)
      (hk.sub (hu A C)) (sub_eq_zero.mpr hA.symm) (sub_eq_zero.mpr hC.symm)
    have he : (fun z ↦ p z * (G z * g z)) = v.val - (fun z ↦ G z * u A C z) := by
      funext z
      change p z * (G z * g z) = v.val z - G z * u A C z
      rw [hvk, ← mul_sub, show k z - u A C z = p z * g z from hquot z]
      ring
    have hmem : G * g ∈ schwartzBergmanSubmodule univ := (hpoly _ (hG.mul hg)).1
      (he ▸ (schwartzBergmanSubmodule univ).sub_mem v.property (hGu A C))
    obtain ⟨w, hw⟩ := hlift ⟨G * g, hmem⟩ ⟨g, hg, fun _ ↦ rfl⟩
    refine ⟨w + x A C, funext fun z ↦ ?_⟩
    have hz : z.val ≠ a ∧ z.val ≠ b := by simpa only [mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or] using z.property
    apply mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr hz.1) (sub_ne_zero.mpr hz.2.symm) : p z.val ≠ 0)
    rw [map_add, Pi.add_apply, mul_add, hw, ← hx, ← hv z]
    change p _ * (G _ * g _) + G _ * u A C _ = v.val _
    exact (sub_eq_iff_eq_add.mp (congrFun he z.val).symm).symm

/-- The endpoint values of a continuous pole-cancelled multiple are its two
residues, with the second sign reversed because the polynomial uses b - z. -/
private theorem globalConverse_normTwist_meromorphic_exact_values (a b : ℂ) (hba : b - a = 1)
    (g v : ℂ → ℂ) (hv : Continuous v)
    (he : ∀ z ∈ ({a, b} : Set ℂ)ᶜ, v z = (z - a) * (b - z) * g z)
    (r s : ℂ) (hr : Tendsto (fun z ↦ (z - a) * g z) (𝓝[≠] a) (𝓝 r))
    (hs : Tendsto (fun z ↦ (z - b) * g z) (𝓝[≠] b) (𝓝 s)) :
    (r, s) = (v a, -v b) := by
  have hreg (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ∈ ({a, b} : Set ℂ)ᶜ := nhdsNE_le_codiscrete z (Set.toFinite {a, b}).compl_mem_codiscrete
  have hc : Continuous (fun z : ℂ ↦ b - z) := continuous_const.sub continuous_id
  have hd : Continuous (fun z : ℂ ↦ z - a) := continuous_id.sub continuous_const
  apply Prod.ext
  · have h := ((hc.tendsto a).mono_left nhdsWithin_le_nhds).mul hr
    have hv' : Tendsto v (𝓝[≠] a) (𝓝 ((b - a) * r)) := h.congr' <| (hreg a).mono fun z hz ↦ by
      rw [he z hz]; ring
    simpa only [hba, one_mul] using tendsto_nhds_unique hv' ((hv.tendsto a).mono_left nhdsWithin_le_nhds)
  · have h := ((hd.tendsto b).mono_left nhdsWithin_le_nhds).mul hs.neg
    have hv' : Tendsto v (𝓝[≠] b) (𝓝 ((b - a) * -s)) := h.congr' <| (hreg b).mono fun z hz ↦ by
      rw [he z hz]; ring
    have hh := tendsto_nhds_unique hv' ((hv.tendsto b).mono_left nhdsWithin_le_nhds)
    simpa only [hba, one_mul, neg_neg] using congrArg Neg.neg hh

/-- Transport strict exactness to the image with its coinduced topology. -/
private theorem globalConverse_normTwist_meromorphic_exact_transport {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y]
    (M : X →ₗ[ℂ] Y) (hM : Injective M) (A : Submodule ℂ X)
    (R₀ : X →L[ℂ] ℂ × ℂ) (hk : R₀.ker = A) (hop : IsOpenQuotientMap R₀) :
    letI : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
    ∃ R : M.range →ₗ[ℂ] ℂ × ℂ, IsHomeomorph M.rangeRestrict ∧
      (∀ x, R (M.rangeRestrict x) = R₀ x) ∧ R.ker = A.map M.rangeRestrict ∧
      IsOpenQuotientMap R ∧ IsClosedEmbedding (M.rangeRestrict.comp A.subtype) := by
  let : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
  let i := LinearEquiv.ofInjective M hM
  have hi : IsHomeomorph M.rangeRestrict := isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨⟨⟨rfl⟩, M.surjective_rangeRestrict⟩,
      fun _ _ h ↦ hM (congrArg Subtype.val h)⟩
  let R := R₀.toLinearMap.comp i.symm.toLinearMap
  have hR (x : X) : R (M.rangeRestrict x) = R₀ x := congrArg R₀ (i.symm_apply_apply x)
  have hInv : Continuous i.symm := hi.isQuotientMap.continuous_iff.mpr
    (show Continuous (fun x ↦ i.symm (i x)) from (by simpa only [i.symm_apply_apply, Function.id_def] using
      (continuous_id : Continuous (id : X → X))))
  have hInvOpen : IsOpenQuotientMap i.symm :=
    ⟨i.symm.surjective, hInv, fun s hs ↦ by
      rw [i.symm.image_eq_preimage_symm]; exact hi.continuous.isOpen_preimage _ hs⟩
  have hclosed : IsClosed (A : Set X) := hk ▸ R₀.isClosed_ker
  refine ⟨R, hi, hR, ?_, hop.comp hInvOpen, hi.isClosedEmbedding.comp hclosed.isClosedEmbedding_subtypeVal⟩
  ext y
  obtain ⟨x, rfl⟩ := M.surjective_rangeRestrict y
  change R (M.rangeRestrict x) = 0 ↔ _
  rw [hR]
  change x ∈ R₀.ker ↔ _
  rw [hk]
  exact ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨w, hw, heq⟩ ↦ hi.injective heq ▸ hw⟩

/-- The map from polar tests to their theta classes and their Bergman map
induce an equivalence of their ranges, computed on a common representative. -/
private theorem globalConverse_normTwist_meromorphic_exact_polar {X Y W : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (P₀ : Submodule ℂ X) (Q : X →ₗ[ℂ] Y) (ZB : P₀ →L[ℂ] W)
    (hZopen : IsOpenMap ZB.rangeRestrict) (hZker : ZB.ker = Q.ker.comap P₀.subtype)
    (hq : IsOpenQuotientMap (Q.comp P₀.subtype).rangeRestrict) :
    ∃ e : P₀.map Q ≃L[ℂ] ZB.range, ∀ x, ∃ f : P₀, x.val = Q f.val ∧ (e x).val = ZB f := by
  let q := Q.comp P₀.subtype
  have hrange : q.range = P₀.map Q := by rw [LinearMap.range_comp, Submodule.range_subtype]
  let j : q.range ≃L[ℂ] P₀.map Q :=
    { LinearEquiv.ofEq _ _ hrange with
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }
  have hk : q.rangeRestrict.ker = ZB.toLinearMap.rangeRestrict.ker := by
    rw [LinearMap.ker_rangeRestrict, LinearMap.ker_rangeRestrict, hZker, LinearMap.ker_comp]
  obtain ⟨e, he⟩ := globalConverse_normTwist_meromorphic_exact_equiv q.rangeRestrict
    ZB.toLinearMap.rangeRestrict hq
    ⟨ZB.toLinearMap.surjective_rangeRestrict, ZB.rangeRestrict.continuous, hZopen⟩ hk
  refine ⟨j.symm.trans e, fun x ↦ ?_⟩
  obtain ⟨f, hf⟩ := q.surjective_rangeRestrict (j.symm x)
  exact ⟨f, (congrArg Subtype.val hf).symm, congrArg Subtype.val ((congrArg e hf.symm).trans (he f))⟩

/-- Apply interpolation with the normalized Hecke test and the two Tate residue limits. -/
private theorem globalConverse_normTwist_meromorphic_exact_membership (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (ZB : P →L[ℂ] B)
    (hZ : ∀ (f : P) s, (ZB f).val s = Z(f.val, χ, s))
    (hIdeal : Set.range ZB = bergmanIdeal(regularizedL(χ, t)))
    (R₀ : Θ(1) →L[ℂ] ℂ × ℂ)
    (hR₀ : ∀ f : ℬ, R₀ ((K(1)).mkQ f) = (-mass * f zeroAdele, mass * adeleSchwartzFourier f zeroAdele))
    (hker : R₀.ker = globalPolarFreeThetaSubmodule (F := F) 1) :
    let regular := ({-shift(t), 1 - shift(t)} : Set ℂ)ᶜ
    let polarFree := globalPolarFreeThetaSubmodule (F := F) 1
    ∀ M : Θ(1) →ₗ[ℂ] regular → ℂ,
      (∀ (f : ℬ) (z : regular), M ((K(1)).mkQ f) z = Z(f, χ, z.val)) →
      ∀ e : polarFree ≃L[ℂ] ZB.range, (∀ (x : polarFree) (z : regular), M x.val z = (e x).val.val z) →
      ∀ h, h ∈ M.range ↔ ∃ b : B, b ∈ bergmanIdeal(regularizedL(χ, t)) ∧
        ∀ z : regular, b.val z.val = polePolynomial(t) z.val * h z := by
  intro regular polarFree M hrep e heval
  let a := -shift(t)
  let b := 1 - shift(t)
  have hba : b - a = 1 := by dsimp [b, a]; ring
  have hpoly (z : ℂ) : (z - a) * (b - z) = polePolynomial(t) z := by dsimp [a, b]; ring
  obtain ⟨hG, ha, hb, hg⟩ := globalConverse_normTwist_meromorphic_exact_generator χ t ht
  obtain ⟨⟨f₀, hf₀⟩, hT⟩ := globalConverse_normTwist_meromorphic_exact_translates χ t ht
  have him := globalConverse_normTwist_meromorphic_exact_image a b hba (regularizedL(χ, t))
    hG ha hb M R₀.toLinearMap (hzero := ?_) (hlift := ?_) (hvalues := ?_)
    ((K(1)).mkQ f₀) (hx₀ := ?_) (htranslate := ?_)
  · simpa only [hpoly] using him
  · intro x hx
    have hx' : x ∈ globalPolarFreeThetaSubmodule (F := F) 1 := hker ▸ (show x ∈ R₀.ker from hx)
    let y : polarFree := ⟨x, hx'⟩
    exact ⟨(e y).val, hIdeal ▸ (e y).property, heval y⟩
  · intro v hv
    obtain ⟨f, rfl⟩ := hIdeal.symm ▸ hv
    exact ⟨(K(1)).mkQ f.val, fun z ↦ (hrep f.val z).trans (hZ f z.val).symm⟩
  · intro x v hv hvx
    obtain ⟨f, rfl⟩ := (K(1)).mkQ_surjective x
    obtain ⟨hl, hr⟩ := globalConverse_normTwist_meromorphic_exact_limits χ t ht f
      (fun z ↦ Z(f, χ, z)) (fun _ _ ↦ rfl)
    exact (hR₀ f).trans (globalConverse_normTwist_meromorphic_exact_values a b hba _ v hv
      (fun z hz ↦ (hvx ⟨z, hz⟩).trans (congrArg (_ * ·) (hrep f ⟨z, hz⟩))) _ _ hl hr)
  · intro z
    rw [hpoly, hrep, hf₀, hg z.val z.property]
  · intro x
    obtain ⟨f, rfl⟩ := (K(1)).mkQ_surjective x
    obtain ⟨g, hg⟩ := hT f
    refine ⟨(K(1)).mkQ g, fun z ↦ ?_⟩
    simpa only [hrep, a, sub_neg_eq_add] using hg z.val z.property

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
  classical
  intro regular polarFree
  refine (globalConverse_normTwist_meromorphic_exact_chart χ t _hχ).elim fun M hMs ↦ ?_
  obtain ⟨hM, hrep⟩ := hMs
  refine (globalConverse_normTwist χ t _hχ).elim fun ZB hZs ↦ ?_
  obtain ⟨hZopen, -, hZ, hIdeal, hZker⟩ := hZs
  refine (globalConverse_normTwist_exact (F := F)).elim fun R₀ hRs ↦ ?_
  obtain ⟨hR₀, hker, hopen, hq⟩ := hRs
  have hk : ZB.ker = (K(1)).mkQ.ker.comap (P).subtype := by rw [Submodule.ker_mkQ]; exact hZker
  refine (globalConverse_normTwist_meromorphic_exact_polar (P) (K(1)).mkQ ZB hZopen hk hq).elim
    fun e he ↦ ?_
  have heval (x : polarFree) (s : regular) : M x.val s = (e x).val.val s.val := by
    obtain ⟨f, hx, hf⟩ := he x
    exact (congrArg (fun y : Θ(1) ↦ M y s) hx).trans ((hrep f.val s).trans
      ((hZ f s.val).symm.trans (congrArg (fun v : B ↦ v.val s.val) hf.symm)))
  let : TopologicalSpace M.range := TopologicalSpace.coinduced M.rangeRestrict inferInstance
  refine (globalConverse_normTwist_meromorphic_exact_transport M hM polarFree R₀ hker hopen).elim
    fun R hR ↦ ?_
  refine ⟨ZB, M, R, hR.1, hrep, hZ, hIdeal,
    globalConverse_normTwist_meromorphic_exact_membership χ t _hχ ZB hZ hIdeal R₀ hR₀ hker M hrep e heval,
    ?_, hR.2.2.1, hR.2.2.2.1, hR.2.2.2.2, e, heval⟩
  intro φ g hg heq
  obtain ⟨x, rfl⟩ := M.surjective_rangeRestrict φ
  obtain ⟨f, rfl⟩ := (K(1)).mkQ_surjective x
  obtain ⟨hl, hr⟩ := globalConverse_normTwist_meromorphic_exact_limits χ t _hχ f g
    (fun s hs ↦ (heq ⟨s, hs⟩).trans (hrep f ⟨s, hs⟩))
  exact (hR.2.1 _).trans ((hR₀ f).trans (Prod.ext
    (globalConverse_normTwist_meromorphic_exact_residue _ _ _ (hg _) hl).symm
    (globalConverse_normTwist_meromorphic_exact_residue _ _ _ (hg _) hr).symm))

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

-- TODO(paper-gap): Equation (6.3.2.20) uses the unshifted zeta generator and
-- omits the Schwartz–Bergman intersection. Even for S empty and trivial χ,
-- the entire multiple with multiplier exp(s^4) is not Schwartz on a vertical line.

-- TODO(paper-gap): In (6.3.2.21) the terminal space must be zero on a nontrivial
-- component, as in (6.3.2.23). In a pure norm-twist component with a nonempty
-- removal set, the first residue vanishes on the entire principal-value image.

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

/-- The real vertical trace differentiates by one factor of I at each step. -/
private theorem globalPrincipalValueConverse_nontrivial_vertical_deriv (b : B) (a : (univ : Set ℝ))
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ b.val ((a.val : ℂ) + (y : ℂ) * Complex.I)) x =
      Complex.I ^ n * iteratedDeriv n b.val ((a.val : ℂ) + (x : ℂ) * Complex.I) := by
  let L (z : ℂ) := (a.val : ℂ) + z * Complex.I
  have hL (z : ℂ) : HasDerivAt L Complex.I z := by
    change HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I z
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id z).mul_const Complex.I).const_add (a.val : ℂ)
  have ha : AnalyticOnNhd ℂ b.val univ :=
    fun z _ ↦ (show Differentiable ℂ b.val from fun w ↦
      (b.property.2.1 w (by simp)).differentiableAt (by simp)).analyticAt z
  have hn (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k b.val) univ := by
    rw [iteratedDeriv_eq_iterate]
    exact ha.iterated_deriv k
  change iteratedDeriv n (fun y : ℝ ↦ b.val (L y)) x = Complex.I ^ n * iteratedDeriv n b.val (L x)
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    have hx : L x ∈ univ := mem_univ _
    have hh : HasDerivAt (iteratedDeriv k b.val) (iteratedDeriv (k + 1) b.val (L x)) (L x) := by
      rw [iteratedDeriv_succ]
      exact (hn k (L x) hx).differentiableAt.hasDerivAt
    have he : (iteratedDeriv k (fun y : ℝ ↦ b.val (L y))) =
        fun y : ℝ ↦ Complex.I ^ k * iteratedDeriv k b.val (L y) := funext ih
    have hdiff : HasDerivAt (fun y : ℝ ↦ Complex.I ^ k * iteratedDeriv k b.val (L y))
        (Complex.I ^ k * (iteratedDeriv (k + 1) b.val (L x) * Complex.I)) x :=
      (((hh.comp (x : ℂ) (hL x)).comp_ofReal).const_mul (Complex.I ^ k))
    rw [iteratedDeriv_succ, he]
    exact hdiff.deriv.trans (by ring)

private theorem globalPrincipalValueConverse_nontrivial_schwartz_deriv_continuous (n : ℕ) :
    Continuous (fun f : SchwartzMap ℝ ℂ ↦ iteratedDeriv n (f : ℝ → ℂ)) := by
  have h (n : ℕ) : ∀ f : SchwartzMap ℝ ℂ,
      (⇑((SchwartzMap.derivCLM ℂ ℂ)^[n] f) : ℝ → ℂ) = iteratedDeriv n (f : ℝ → ℂ) := by
    induction n with
    | zero => intro f; simp [iteratedDeriv_zero]
    | succ k ih =>
      intro f
      rw [Function.iterate_succ_apply', iteratedDeriv_succ, ← ih f]
      exact funext (SchwartzMap.derivCLM_apply ℂ ((SchwartzMap.derivCLM ℂ ℂ)^[k] f))
  simp_rw [← h]
  have hc : Continuous (fun f : SchwartzMap ℝ ℂ ↦ (f : ℝ → ℂ)) :=
    continuous_pi fun x ↦ ((continuous_eval_const (F := BoundedContinuousFunction ℝ ℂ) x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous)
  exact hc.comp ((SchwartzMap.derivCLM ℂ ℂ).continuous.iterate n)

/-- The Schwartz-line realization of a Bergman function makes each complex jet continuous. -/
private theorem globalPrincipalValueConverse_nontrivial_continuous_jet (s : ℂ) (n : ℕ) :
    Continuous (fun b : B ↦ iteratedDeriv n b.val s) := by
  obtain ⟨T, hT, hE⟩ := schwartzBergman_schwartzLine_topology (univ : Set ℝ) isOpen_univ
    ordConnected_univ univ_nonempty
  let a : (univ : Set ℝ) := ⟨s.re, mem_univ _⟩
  have hL : (a.val : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  have hTeq (b : B) : ⇑(T b a) = fun y : ℝ ↦ b.val ((a.val : ℂ) + (y : ℂ) * Complex.I) := by
    funext y
    simpa only [weightedVerticalTrace, pow_zero, one_mul] using hT b a y
  have hC : Continuous (fun b : B ↦ iteratedDeriv n ((T b a : SchwartzMap ℝ ℂ) : ℝ → ℂ) s.im) :=
    (continuous_apply s.im).comp ((globalPrincipalValueConverse_nontrivial_schwartz_deriv_continuous n).comp
      ((continuous_apply a).comp hE.continuous))
  apply (hC.const_mul ((Complex.I ^ n)⁻¹)).congr
  intro b
  rw [hTeq, globalPrincipalValueConverse_nontrivial_vertical_deriv b a n, hL,
    inv_mul_cancel_left₀ (pow_ne_zero _ Complex.I_ne_zero)]

/-- The order inequalities remove all singularities of the quotient. -/
private theorem globalPrincipalValueConverse_nontrivial_factor {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ z, f z = g z * u z) ↔
      ∀ z, analyticOrderAt g z ≤ analyticOrderAt f z := by
  constructor
  · rintro ⟨u, hu, he⟩ z
    rw [show f = g * u from funext he, analyticOrderAt_mul (hg.analyticAt z) (hu.analyticAt z)]
    exact self_le_add_right _ _
  · intro hord
    let q := f / g
    have hq : MeromorphicOn q univ := fun z _ ↦ (hf.analyticAt z).meromorphicAt.div (hg.analyticAt z).meromorphicAt
    have hdiff : Differentiable ℂ (toMeromorphicNFOn q univ) := by
      intro z
      apply AnalyticAt.differentiableAt
      have hnf := meromorphicNFOn_toMeromorphicNFOn q univ (mem_univ z)
      apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      rw [meromorphicOrderAt_toMeromorphicNFOn hq (mem_univ z),
        meromorphicOrderAt_div (hf.analyticAt z).meromorphicAt (hg.analyticAt z).meromorphicAt,
        (hf.analyticAt z).meromorphicOrderAt_eq, (hg.analyticAt z).meromorphicOrderAt_eq]
      have hle := hord z
      generalize analyticOrderAt f z = m at hle ⊢
      generalize analyticOrderAt g z = n at hle ⊢
      cases m using ENat.recTopCoe with
      | top => simp
      | coe m =>
        cases n using ENat.recTopCoe with
        | top => simp at hle
        | coe n =>
          exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (by exact_mod_cast hle : (n : ℤ) ≤ m))
    refine ⟨_, hdiff, fun z ↦ ?_⟩
    by_cases hz : g z = 0
    · have hpos := lt_of_lt_of_le (pos_iff_ne_zero.mpr ((hg.analyticAt z).analyticOrderAt_ne_zero.mpr hz))
          (hord z)
      rw [hz, zero_mul]
      exact (hf.analyticAt z).analyticOrderAt_ne_zero.mp hpos.ne'
    · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hq (mem_univ z),
        toMeromorphicNFAt_eq_self.mpr ((hf.analyticAt z).div (hg.analyticAt z) hz).meromorphicNFAt]
      exact (mul_div_cancel₀ _ hz).symm

/-- Each vanishing jet is a closed condition in the Schwartz–Bergman topology. -/
private theorem globalPrincipalValueConverse_nontrivial_closed {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) : IsClosed bergmanIdeal(g) := by
  have hdiff (f : B) : Differentiable ℂ f.val := fun w ↦
    (f.property.2.1 w (by simp)).differentiableAt (by simp)
  have hset : bergmanIdeal(g) = ⋂ (z : ℂ) (n : ℕ) (_ : (n : ℕ∞) ≤ analyticOrderAt g z)
      (i : ℕ) (_ : i < n), {f : B | iteratedDeriv i f.val z = 0} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter, globalPrincipalValueConverse_nontrivial_factor (hdiff f) hg]
    apply forall_congr'
    intro z
    rw [← ENat.forall_natCast_le_iff_le]
    simp_rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hdiff f).analyticAt z)]
  rw [hset]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
      isClosed_eq (globalPrincipalValueConverse_nontrivial_continuous_jet z i) continuous_const

private theorem globalPrincipalValueConverse_nontrivial_euler_form (χ : PontryaginDual C𝔽) (v : V) :
    (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) = (1 : ℂ → ℂ) ∨
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ θ : ℝ,
      (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) =
        fun z ↦ 1 - Complex.exp (((-ℓ : ℝ) : ℂ) * z + (θ : ℂ) * Complex.I) := by
  classical
  by_cases hχ : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · right
    let hu := (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let π : (v.adicCompletion F)ˣ := Units.mk0 hu.choose hu.choose_spec.ne_zero
    obtain ⟨t, ⟨-, ht, -⟩, -⟩ :=
      unramifiedHeckeCharacter_existsUnique_phase χ v hχ π hu.choose_spec
    have hval := hχ.localValue_eq π.val hu.choose_spec
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at hval
    have ht' : (ideleClassNormTwist χ 0).localValue v =
        (v.asIdeal.absNorm : ℂ) ^ (-(t : ℂ) * Complex.I) := hval.trans ht
    have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    let ℓ := Real.log (v.asIdeal.absNorm : ℝ)
    refine ⟨ℓ, Real.log_pos hq, -ℓ * t, funext fun z ↦ ?_⟩
    rw [finiteHeckeEulerFactor_inv_eq_phase χ v hχ t ht']
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (zero_lt_one.trans hq).ne')]
    have hlog : Complex.log (v.asIdeal.absNorm : ℂ) = (ℓ : ℂ) := by
      simpa only [ℓ, Complex.ofReal_natCast] using (Complex.ofReal_log (zero_lt_one.trans hq).le).symm
    rw [hlog]
    congr 2
    push_cast
    dsimp [ℓ]
    ring
  · left
    funext z
    rw [finiteHeckeEulerFactor, ite_eq_right hχ, inv_one]
    rfl

private theorem globalPrincipalValueConverse_nontrivial_removal_differentiable
    (χ : U) (S : Finset V) : Differentiable ℂ (removal(χ, S)) := by
  apply Differentiable.fun_finsetProd
  intro v _
  rcases globalPrincipalValueConverse_nontrivial_euler_form χ v with h | ⟨_, _, _, h⟩
  all_goals rw [h]; fun_prop

open Complex in
/-- Division by one vertical periodic Euler factor preserves rapid decay on
closed strips once the quotient is entire. -/
private theorem globalPrincipalValueConverse_nontrivial_divide_exp (bfun : SchwartzBergman (univ : Set ℝ))
    (u : ℂ → ℂ) (hu : Differentiable ℂ u) {ℓ θ : ℝ} (hℓ : 0 < ℓ)
    (h : ∀ z, bfun.val z = (1 - Complex.exp (((-ℓ : ℝ) : ℂ) * z + (θ : ℂ) * Complex.I)) * u z) :
    u ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  refine ⟨fun _ hz ↦ (hz (mem_univ _)).elim, hu.differentiableOn, fun a b _ _ N ↦ ?_⟩
  let L := min a 0 - 1
  let R := max b 0 + 1
  have hL : L < 0 := by dsimp [L]; linarith [min_le_right a 0]
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right b 0]
  have hLR := hL.trans hR
  let T (j : ℤ) := (θ - Real.pi - (j : ℝ) * (2 * Real.pi)) / ℓ
  let e (w : ℂ) := ((-ℓ : ℝ) : ℂ) * w + (θ : ℂ) * Complex.I
  have hre (w : ℂ) : (e w).re = -ℓ * w.re := by simp [e, Complex.mul_re]
  have him (w : ℂ) : (e w).im = θ - ℓ * w.im := by simp [e, Complex.mul_im]; ring
  let δ := min 1 (min (Real.exp (-ℓ * L) - 1) (1 - Real.exp (-ℓ * R)))
  have hδ : 0 < δ := by
    refine lt_min zero_lt_one (lt_min (sub_pos.mpr (Real.one_lt_exp_iff.mpr ?_))
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr ?_)))
    · exact mul_pos_of_neg_of_neg (neg_neg_of_pos hℓ) hL
    · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hℓ) hR
  have hhor (w : ℂ) (j : ℤ) (hw : w.im = T j) : δ ≤ ‖1 - Complex.exp (e w)‖ := by
    have hphase : (e w).im = Real.pi + (j : ℝ) * (2 * Real.pi) := by
      rw [him, hw]
      dsimp [T]
      field_simp
      ring
    have hreal : (1 - Complex.exp (e w)).re = 1 + Real.exp ((e w).re) := by
      rw [Complex.sub_re, Complex.one_re, Complex.exp_re, hphase,
        Real.cos_add_int_mul_two_pi, Real.cos_pi]
      ring
    exact (min_le_left _ _).trans ((le_add_of_nonneg_right (Real.exp_pos _).le).trans
      (hreal ▸ Complex.re_le_norm (1 - Complex.exp (e w))))
  have hvert (w : ℂ) (hw : w.re = L ∨ w.re = R) : δ ≤ ‖1 - Complex.exp (e w)‖ := by
    rcases hw with hw | hw
    · have he := norm_sub_norm_le (Complex.exp (e w)) (1 : ℂ)
      rw [Complex.norm_exp, hre, hw, norm_one, norm_sub_rev] at he
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans he
    · have he := norm_sub_norm_le (1 : ℂ) (Complex.exp (e w))
      rw [Complex.norm_exp, hre, hw, norm_one] at he
      exact ((min_le_right _ _).trans (min_le_right _ _)).trans he
  obtain ⟨M, hM⟩ := bfun.property.2.2 L R hLR.le (subset_univ _) N
  refine ⟨M / δ, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hzRe : z.re ∈ Icc L R :=
    ⟨(by dsimp [L]; linarith [min_le_left a 0, hz.1]), (by dsimp [R]; linarith [le_max_left b 0, hz.2])⟩
  let q := (θ - Real.pi - ℓ * z.im) / (2 * Real.pi)
  obtain ⟨j, hj⟩ := exists_int_gt q
  obtain ⟨k, hk⟩ := exists_int_lt q
  have hπ : 0 < 2 * Real.pi := by positivity
  have hj' : T j < z.im := by
    have hj' := (div_lt_iff₀ hπ).mp hj
    exact (div_lt_iff₀ hℓ).mpr (by linarith)
  have hk' : z.im < T k := by
    have hk' := (lt_div_iff₀ hπ).mp hk
    exact (lt_div_iff₀ hℓ).mpr (by linarith)
  have hjk := hj'.trans hk'
  have hcl := Complex.closure_reProdIm (Ioo L R) (Ioo (T j) (T k))
  rw [closure_Ioo hLR.ne, closure_Ioo hjk.ne] at hcl
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo L R).reProdIm (Metric.isBounded_Ioo (T j) (T k)))
    (((differentiable_pow N).mul hu).diffContOnCl)
  · intro w hw
    have hwRe : w.re ∈ Icc L R := (hcl ▸ frontier_subset_closure hw).1
    rw [Complex.frontier_reProdIm, closure_Ioo hLR.ne, closure_Ioo hjk.ne,
      frontier_Ioo hLR, frontier_Ioo hjk] at hw
    have hden : δ ≤ ‖1 - Complex.exp (e w)‖ := by
      rcases hw with hw | hw
      · rcases show w.im = T j ∨ w.im = T k from hw.2 with hj | hk
        exacts [hhor w j hj, hhor w k hk]
      · exact hvert w hw.1
    have hprod : ‖w ^ N * u w‖ * ‖1 - Complex.exp (e w)‖ ≤ M := by
      have he := hM ⟨w, hwRe, rfl⟩
      change ‖w ^ N * bfun.val w‖ ≤ M at he
      have heq : w ^ N * bfun.val w = (w ^ N * u w) * (1 - Complex.exp (e w)) := by
        rw [h w]; dsimp [e]; ring
      rwa [heq, norm_mul] at he
    exact (le_div_iff₀ hδ).mpr ((mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans hprod)
  · rw [hcl]
    exact ⟨hzRe, hj'.le, hk'.le⟩

/-- An entire quotient of a Schwartz–Bergman function by a finite product of
vertical periodic Euler factors still decays rapidly on closed strips. -/
private theorem globalPrincipalValueConverse_nontrivial_divide_prod_exp {ι : Type*} (S : Finset ι) (A : ι → ℂ → ℂ)
    (hA : ∀ i ∈ S, A i = 1 ∨ ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ θ : ℝ,
      A i = fun z ↦ 1 - Complex.exp (((-ℓ : ℝ) : ℂ) * z + (θ : ℂ) * Complex.I))
    (bfun : SchwartzBergman (univ : Set ℝ)) (u : ℂ → ℂ)
    (hu : Differentiable ℂ u) (h : ∀ z, bfun.val z = (∏ i ∈ S, A i z) * u z) :
    u ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  classical
  induction S using Finset.induction_on generalizing bfun with
  | empty =>
    have he : bfun.val = u := funext fun z ↦ by simpa using h z
    exact he ▸ bfun.property
  | @insert i S hi ih =>
    have hAS := fun j (hj : j ∈ S) ↦ hA j (Finset.mem_insert_of_mem hj)
    let v (z : ℂ) := (∏ j ∈ S, A j z) * u z
    have hdiv (z : ℂ) : bfun.val z = A i z * v z := by
      simpa only [Finset.prod_insert hi, mul_assoc, v] using h z
    rcases hA i (Finset.mem_insert_self _ _) with hOne | ⟨ℓ, hℓ, θ, hθ⟩
    · apply ih hAS bfun
      simpa only [hOne, Pi.one_apply, one_mul, v] using hdiv
    · have hd (j : ι) (hj : j ∈ S) : Differentiable ℂ (A j) := by
        rcases hAS j hj with he | ⟨_, _, _, he⟩ <;> rw [he] <;> fun_prop
      have hv : Differentiable ℂ v := (Differentiable.fun_finsetProd hd).mul hu
      have hSB := globalPrincipalValueConverse_nontrivial_divide_exp bfun v hv hℓ (hθ ▸ hdiv)
      exact ih hAS (⟨v, hSB⟩ : SchwartzBergman (univ : Set ℝ)) (fun _ ↦ rfl)

/-- Paper: Theorem 6.3.2.2(1), pp. 309–310, equation (6.3.2.19).
On a nontrivial norm-one component, the principal-value image embeds as the
closed Schwartz–Bergman subspace divisible by the completed Hecke L-function
times the reciprocals of the removed Euler factors. The ramified factors are one. -/
theorem globalPrincipalValueConverse_nontrivial (S : Finset V) (χ : U) (_hχ : χ₁(χ) ≠ 1) :
    ∃ ZB : pvTheta(S, χ₁(χ)) →L[ℂ] B, IsClosedEmbedding ZB ∧
      (∀ (f : ℬ) s, (ZB ((pvMorphism(S, χ₁(χ))).rangeRestrict f)).val s = Z(PV(S) f, χ, s)) ∧
      Set.range ZB = bergmanIdeal(fun s ↦ removal(χ, S) s * continuedCompletedHeckeL χ s) := by
  classical
  obtain ⟨M, hM, hval, hMrange⟩ := globalConverse_nontrivial χ _hχ
  let E := removal(χ, S)
  let L := continuedCompletedHeckeL χ
  have hn : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 :=
    fun h ↦ _hχ (PontryaginDual.ext fun x ↦ DFunLike.congr_fun h x)
  have hL : Differentiable ℂ L := completedHeckeL_continuation_entire χ L
    (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2 hn
  have hE : Differentiable ℂ E :=
    globalPrincipalValueConverse_nontrivial_removal_differentiable χ S
  have hmul (f : ℬ) (z : ℂ) : Z(PV(S) f, χ, z) = E z * Z(f, χ, z) := by
    have H := nhdsNE_le_codiscrete z (globalPrincipalValueConverse_mellin S χ f)
    exact (((globalIdelicZFunction_meromorphic _ χ (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (((hE.mul (globalIdelicZFunction_entire_of_nontrivial f χ hn)).analyticAt z).meromorphicNFAt)).mp H).eq_of_nhds
  let ZB := M.comp (pvTheta(S, χ₁(χ))).subtypeL
  have hcomp (f : ℬ) (s : ℂ) :
      (ZB ((pvMorphism(S, χ₁(χ))).rangeRestrict f)).val s = Z(PV(S) f, χ, s) :=
    hval (PV(S) f) s
  have hrange : Set.range ZB = bergmanIdeal(E * L) := by
    ext b
    constructor
    · rintro ⟨⟨_, f, rfl⟩, rfl⟩
      have hm : M ((K(χ₁(χ))).mkQ f) ∈ Set.range M := ⟨_, rfl⟩
      rw [hMrange] at hm
      obtain ⟨u, hu, he⟩ := hm
      refine ⟨u, hu, fun z ↦ ?_⟩
      have hz := (hcomp f z).trans (hmul f z)
      rw [← hval f z, he z] at hz
      exact hz.trans (mul_assoc _ _ _).symm
    · rintro ⟨u, hu, he⟩
      have hfact (z : ℂ) : b.val z = E z * (L z * u z) := (he z).trans (mul_assoc _ _ _)
      let b' : B := ⟨L * u, globalPrincipalValueConverse_nontrivial_divide_prod_exp S
        (fun v z ↦ (finiteHeckeEulerFactor χ v z)⁻¹)
        (fun v _ ↦ globalPrincipalValueConverse_nontrivial_euler_form χ v)
        b (L * u) (hL.mul hu) hfact⟩
      have hb' : b' ∈ Set.range M := hMrange.symm ▸ ⟨u, hu, fun _ ↦ rfl⟩
      obtain ⟨x, hx⟩ := hb'
      obtain ⟨f, rfl⟩ := (K(χ₁(χ))).mkQ_surjective x
      refine ⟨(pvMorphism(S, χ₁(χ))).rangeRestrict f, Subtype.ext (funext fun z ↦ ?_)⟩
      rw [hcomp, hmul, ← hval, hx]
      exact (hfact z).symm
  exact ⟨ZB, ⟨hM.isEmbedding.comp IsEmbedding.subtypeVal,
    hrange.symm ▸ globalPrincipalValueConverse_nontrivial_closed (hE.mul hL)⟩, hcomp, hrange⟩

/-- On a homogeneous component the principal-value map is conjugate to the
restriction of the ordinary theta operator to its closed isotype. -/
private theorem globalPrincipalValueConverse_normTwist_divided_exact_transport (S : Finset V)
    (ω : PontryaginDual C₁) :
    ∃ e : Θ(ω) ≃L[ℂ] pvTheta(S, ω), ∀ f : ℬ,
      e ((K(ω)).mkQ f) = (pvMorphism(S, ω)).rangeRestrict f := by
  classical
  obtain ⟨hs, i, hi⟩ := globalThetaIsotypicAverage_equiv (F := F) ω
  let j := Subtype.val ∘ i
  have hj : IsClosedEmbedding j := hs.isClosedEmbedding_subtypeVal.comp i.toHomeomorph.isClosedEmbedding
  let W := globalThetaPrincipalValue F S
  have hW : IsClosedEmbedding W := by
    rcases S.eq_empty_or_nonempty with rfl | h
    · have he : ⇑W = id := by
        funext x
        obtain ⟨f, rfl⟩ := (LinearMap.ker (adelicThetaLinearMap F)).mkQ_surjective x
        exact congrArg (LinearMap.ker (adelicThetaLinearMap F)).mkQ
          (LinearMap.congr_fun (globalPrincipalValueConverse_mellin_emptyTest (F := F)) f)
      rw [he]
      exact IsClosedEmbedding.id
    · exact globalThetaPrincipalValue_isClosedEmbedding h
  have hjq (f : ℬ) : j ((pvMorphism(S, ω)) f) = W (j ((K(ω)).mkQ f)) := by
    exact (hi (PV(S) f)).trans ((globalThetaPrincipalValue_isotypicAverage S ω
      (Submodule.Quotient.mk f)).symm.trans (congrArg W (hi f).symm))
  let q := (pvMorphism(S, ω)).rangeRestrict
  have hk : K(ω) ≤ q.ker := by
    intro f hf
    apply Subtype.ext
    apply hj.injective
    change j ((pvMorphism(S, ω)) f) = j 0
    rw [hjq, show (K(ω)).mkQ f = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hf]
    simp [j]
  let T := (K(ω)).liftQ q hk
  have ht (f : ℬ) : T ((K(ω)).mkQ f) = q f := rfl
  have heq : (j ∘ Subtype.val) ∘ T = W ∘ j := by
    funext x
    obtain ⟨f, rfl⟩ := (K(ω)).mkQ_surjective x
    exact hjq f
  have hT : IsEmbedding T := (hj.isEmbedding.comp IsEmbedding.subtypeVal).of_comp_iff.mp
    (heq.symm ▸ (hW.isEmbedding.comp hj.isEmbedding))
  have hsurj : Surjective T := by
    rintro ⟨_, f, rfl⟩
    exact ⟨(K(ω)).mkQ f, rfl⟩
  let e := LinearEquiv.ofBijective T ⟨hT.injective, hsurj⟩
  have hInv : Continuous e.symm := hT.isInducing.continuous_iff.mpr (by
    change Continuous (fun y ↦ e (e.symm y))
    simp only [e.apply_symm_apply]
    exact continuous_id)
  exact ⟨{e with continuous_toFun := hT.continuous, continuous_invFun := hInv}, ht⟩

/-- Paper: Theorem 6.3.2.2(2), p. 310, equations (6.3.2.21) and (6.3.2.23).
On a nontrivial norm-one component, principal values of polar-free tests already
give the full homogeneous principal-value image with its subspace topology.
The inclusion corresponds to the identity on the range in (6.3.2.19).
Deviation: The terminal residue space is zero, as in (6.3.2.23). -/
theorem globalPrincipalValueConverse_nontrivial_exact (S : Finset V)
    (ω : PontryaginDual C₁) (_hω : ω ≠ 1) :
    IsOpenQuotientMap ((pvMorphism(S, ω)).rangeRestrict.comp (P).subtype) := by
  obtain ⟨e, he⟩ := globalPrincipalValueConverse_normTwist_divided_exact_transport S ω
  have hmap : ⇑((pvMorphism(S, ω)).rangeRestrict.comp (P).subtype) =
      e ∘ ((K(ω)).mkQ.comp (P).subtype) := funext fun f ↦ (he f.val).symm
  rw [hmap]
  exact e.toHomeomorph.isOpenQuotientMap.comp (globalConverse_nontrivial_exact ω _hω)

/-- The Euler product is nonzero away from a discrete set, since each nonconstant
factor has modulus strictly below one in its exponential term at the point 1. -/
private theorem globalPrincipalValueConverse_normTwist_divided_exact_germs (S : Finset V)
    (χ : U) (f : ℬ) : (fun s ↦ Z(PV(S) f, χ, s) / removal(χ, S) s) =ᶠ[codiscrete ℂ]
        (fun s ↦ Z(f, χ, s)) := by
  classical
  have hf (v : V) : Differentiable ℂ (fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹) ∧
      (finiteHeckeEulerFactor χ v 1)⁻¹ ≠ 0 := by
    rcases globalPrincipalValueConverse_nontrivial_euler_form χ v with h | ⟨ℓ, hℓ, θ, h⟩
    · exact ⟨h ▸ differentiable_const _, by simpa using (congrFun h 1).trans_ne one_ne_zero⟩
    · refine ⟨h ▸ (by fun_prop), (congrFun h 1).trans_ne (sub_ne_zero.mpr ?_)⟩
      have he : ‖Complex.exp (((-ℓ : ℝ) : ℂ) * 1 + (θ : ℂ) * Complex.I)‖ < 1 := by
        rw [Complex.norm_exp, Real.exp_lt_one_iff]
        simpa using hℓ
      exact fun heq ↦ (ne_of_lt he) (heq ▸ norm_one)
  have hE : Differentiable ℂ (removal(χ, S)) := Differentiable.fun_finsetProd fun v _ ↦ (hf v).1
  have h1 : removal(χ, S) 1 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ (hf v).2
  have ha : AnalyticOnNhd ℂ (removal(χ, S)) univ := fun z _ ↦ hE.analyticAt z
  have hn := ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
  have he : ∀ᶠ z in codiscrete ℂ, removal(χ, S) z ≠ 0 := by
    exact hn.resolve_left (fun h ↦ h1 (h (mem_univ 1)))
  filter_upwards [globalPrincipalValueConverse_mellin S χ f, he] with z hz hez
  rw [hz, mul_div_cancel_left₀ _ hez]

private theorem globalPrincipalValueConverse_normTwist_divided_exact_residue {f g : ℂ → ℂ} {ρ : ℂ}
    (h : f =ᶠ[𝓝[≠] ρ] g) : complexResidue f ρ = complexResidue g ρ := by
  obtain ⟨R, hR, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h
  unfold complexResidue Filter.limUnder
  apply congrArg Filter.lim
  apply Filter.map_congr
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  congr 1
  apply circleIntegral.integral_congr hr.1.le
  intro z hz
  have hdist := Metric.mem_sphere.mp hz
  refine hEq ⟨Metric.mem_ball.mpr (hdist.trans_lt hr.2), mem_compl_singleton_iff.mpr ?_⟩
  rintro rfl
  exact hr.1.ne (by simpa using hdist)

/-- Transport the residue sequence, including the relative openness of the
polar map, along a linear homeomorphism of its middle term. -/
private theorem globalPrincipalValueConverse_normTwist_divided_exact_sequence
    {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (A : Submodule ℂ X) (q₀ : X →ₗ[ℂ] Y) (q : X →ₗ[ℂ] Z)
    (e : Y ≃L[ℂ] Z) (he : ∀ x, e (q₀ x) = q x)
    (R₀ : Y →L[ℂ] ℂ × ℂ) (hker : R₀.ker = A.map q₀)
    (hopen : IsOpenQuotientMap R₀) (hpolar : IsOpenQuotientMap (q₀.comp A.subtype).rangeRestrict) :
    ∃ R : Z →L[ℂ] ℂ × ℂ, (∀ x, R (q x) = R₀ (q₀ x)) ∧ R.ker = A.map q ∧
      IsOpenQuotientMap R ∧ IsOpenQuotientMap (q.comp A.subtype).rangeRestrict := by
  let R := R₀.comp e.symm.toContinuousLinearMap
  refine ⟨R, fun x ↦ ?_, ?_, hopen.comp e.symm.toHomeomorph.isOpenQuotientMap, ?_⟩
  · change R₀ (e.symm (q x)) = _
    rw [← he, e.symm_apply_apply]
  · ext y
    change e.symm y ∈ R₀.ker ↔ _
    rw [hker]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, (he x).symm.trans ((congrArg e hxy).trans (e.apply_symm_apply y))⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [← he, e.symm_apply_apply]⟩
  · let T := q₀.comp A.subtype
    let polarMap := q.comp A.subtype
    have hset : e.toHomeomorph '' (T.range : Set Y) = (polarMap.range : Set Z) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, (he x.val).symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨T x, ⟨x, rfl⟩, he x.val⟩
    let h : T.range ≃ₜ polarMap.range := (e.toHomeomorph.image T.range).trans (.setCongr hset)
    have hh : (⇑polarMap.rangeRestrict) = h ∘ T.rangeRestrict :=
      funext fun x ↦ Subtype.ext (he x.val).symm
    change IsOpenQuotientMap polarMap.rangeRestrict
    rw [hh]
    exact h.isOpenQuotientMap.comp hpolar

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
  classical
  intro q
  refine (globalPrincipalValueConverse_normTwist_divided_exact_transport (F := F) S
    (1 : PontryaginDual C₁)).elim fun e he ↦ ?_
  refine (globalConverse_normTwist_exact (F := F)).elim fun R₀ hR₀ ↦ ?_
  have seq := globalPrincipalValueConverse_normTwist_divided_exact_sequence
    (P) (K(1)).mkQ q e he R₀ hR₀.2.1 hR₀.2.2.1 hR₀.2.2.2
  refine seq.elim fun R hR ↦ ?_
  have hval (f : ℬ) := (hR.1 f).trans (hR₀.1 f)
  refine ⟨R, ?_, hval, hR.2⟩
  intro f
  have h := globalPrincipalValueConverse_normTwist_residues ∅ χ t _hχ f
  simp only [globalPrincipalValueConverse_mellin_emptyTest, LinearMap.id_apply,
    reciprocalPartialHeckeEulerProduct, Finset.prod_empty, one_mul] at h
  have hg := globalPrincipalValueConverse_normTwist_divided_exact_germs S χ f
  rw [hval, ← h]
  exact Prod.ext (globalPrincipalValueConverse_normTwist_divided_exact_residue
    (nhdsNE_le_codiscrete _ hg)).symm (globalPrincipalValueConverse_normTwist_divided_exact_residue
    (nhdsNE_le_codiscrete _ hg)).symm

/-- The two residue identities force principal value to preserve both zero moments. -/
private theorem globalPrincipalValueConverse_normTwist_mellin_map_polar
    (S : Finset V) (f : P) : PV(S) f.val ∈ P := by
  let μ := normOneIdeleClassTamagawaMeasure F
  let : MeasurableSpace C𝔽 := borel _
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hm : mass ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ)).ne'
  have ht : χ₀((1 : U)) = ideleClassNormTwist (1 : U) (shift(0)) := by simp
  have h := globalPrincipalValueConverse_normTwist_residues S 1 0 ht f.val
  have h₀ := globalPrincipalValueConverse_normTwist_residues ∅ 1 0 ht (PV(S) f.val)
  simp only [globalPrincipalValueConverse_mellin_emptyTest, LinearMap.id_apply,
    reciprocalPartialHeckeEulerProduct, Finset.prod_empty, one_mul] at h₀
  obtain ⟨hz, hF⟩ := (mem_adelePolarSubspace f.val).mp f.property
  rw [hz, hF, mul_zero, mul_zero, mul_zero, mul_zero] at h
  have he := h₀.symm.trans h
  exact (mem_adelePolarSubspace _).mpr
    ⟨(mul_eq_zero.mp (congrArg Prod.fst he)).resolve_left (neg_ne_zero.mpr hm),
     (mul_eq_zero.mp (congrArg Prod.snd he)).resolve_left hm⟩

/-- Paper: Theorem 6.3.2.2(1), pp. 309–310, equation (6.3.2.20).
The Mellin transform of the principal value of a polar test is a continuous linear function of
that principal value: there is a continuous linear chart of `pvPolar(S)` in the
Schwartz–Bergman space taking `PV(S) f` to `Z(PV(S) f, χ, ·)`. Granting that the principal
value of a polar test is itself polar -- the content of Theorem 7.5.0.1, proved in this library
as `strongCoprimalityPrincipalValue_mem_polar`, which this chapter cannot import -- this is the
restriction to the principal-value image of the norm-twist chart of (6.3.2.4). -/
theorem globalPrincipalValueConverse_normTwist_mellin_map (S : Finset V) (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) :
    ∃ ZB : pvPolar(S) →L[ℂ] B, ∀ (f : pvPolar(S)) s, (ZB f).val s = Z(f.val, χ, s) := by
  refine (globalConverse_normTwist χ t _hχ).elim fun M hM ↦ ?_
  have hP : pvPolar(S) ≤ P := by
    rintro _ ⟨f, hf, rfl⟩
    exact globalPrincipalValueConverse_normTwist_mellin_map_polar S ⟨f, hf⟩
  let i : pvPolar(S) →L[ℂ] P := ⟨Submodule.inclusion hP,
    continuous_subtype_val.subtype_mk _⟩
  exact ⟨M.comp i, fun f z ↦ hM.2.2.1 (i f) z⟩

/-- The two zeros of the shifted pole polynomial cancel the simple poles of the completion. -/
private theorem globalPrincipalValueConverse_normTwist_range_regular (χ : U) (t : ℝ)
    (ht : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) : Differentiable ℂ (regularizedL(χ, t)) := by
  let b := shift(t)
  let p := polePolynomial(t)
  let L := continuedCompletedHeckeL χ
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext x
    have he := DFunLike.congr_fun ht x.val
    change (χ x.val : ℂ) * _ ^ (0 : ℂ) = 1 * ((((ideleClassNorm F x.val).val : ℝ) : ℂ) ^ b) at he
    rw [Complex.cpow_zero, mul_one, show ideleClassNorm F x.val = 1 from x.property,
      Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul] at he
    exact he
  have hω : χ₁(χ) = 1 := PontryaginDual.ext fun x ↦ DFunLike.congr_fun hk x
  obtain ⟨u, ⟨hchar, hzero, hone, haway⟩, -⟩ := completedHeckeL_continuation_simplePoles χ L hL hEq hk
  have hu : t = -u := (globalConverse_existsUnique_normTwist χ hω).unique ht (by
    convert hchar using 2
    push_cast
    ring)
  have hb : b = -(Complex.I * (u : ℂ)) := by dsimp [b]; rw [hu]; push_cast; ring
  have hp (s : ℂ) : AnalyticAt ℂ p s := by dsimp [p]; fun_prop
  have hmer : MeromorphicOn (p * L) univ := fun s hs ↦ (hp s).meromorphicAt.mul (hL hs).meromorphicAt
  have hcancel (s : ℂ) (hz : p s = 0) (hord : meromorphicOrderAt L s = -1) :
      0 ≤ meromorphicOrderAt (p * L) s := by
    rw [meromorphicOrderAt_mul (hp s).meromorphicAt (hL (mem_univ s)).meromorphicAt, hord]
    have hpos : 0 < meromorphicOrderAt p s := by
      apply (tendsto_zero_iff_meromorphicOrderAt_pos (hp s).meromorphicAt).mp
      rw [← hz]
      exact (hp s).continuousAt.continuousWithinAt
    generalize meromorphicOrderAt p s = w at hpos ⊢
    cases w with
    | top => simp
    | coe k =>
      have h : (0 : ℤ) < k := WithTop.coe_lt_coe.mp hpos
      exact WithTop.coe_le_coe.mpr (show (0 : ℤ) ≤ k + (-1) by omega)
  intro z
  apply AnalyticAt.differentiableAt
  apply (meromorphicNFOn_toMeromorphicNFOn (p * L) univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z)]
  by_cases hz : z = Complex.I * (u : ℂ)
  · subst z
    exact hcancel _ (by change (_ + b) * (1 - _ - b) = 0; rw [hb]; ring) hzero
  by_cases hz₁ : z = 1 + Complex.I * (u : ℂ)
  · subst z
    exact hcancel _ (by change (_ + b) * (1 - _ - b) = 0; rw [hb]; ring) hone
  exact ((hp z).mul (haway z (by simp [hz, hz₁]))).meromorphicOrderAt_nonneg

/-- Paper: Theorem 6.3.2.2(1), pp. 309–310, equation (6.3.2.20).
A continuous linear chart of the principal-value polar image that computes the transforms of
its elements has as its range exactly the Schwartz–Bergman functions divisible by the
reciprocal partial Euler product and the shifted, pole-cancelled completed Hecke function. The
hard inclusion is the division by the reciprocal Euler factors, which have zeros on the
critical line; the `TODO(paper-gap)` above this section and ERRATA I200 record the gap, and
`Sec3_Printed.lean` refutes the printed unshifted generator. -/
theorem globalPrincipalValueConverse_normTwist_range (S : Finset V) (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (ZB : pvPolar(S) →L[ℂ] B)
    (hZB : ∀ (f : pvPolar(S)) s, (ZB f).val s = Z(f.val, χ, s)) :
    Set.range ZB = bergmanIdeal(fun s ↦ removal(χ, S) s * regularizedL(χ, t) s) := by
  classical
  refine (globalConverse_normTwist χ t _hχ).elim fun M hM ↦ ?_
  let E := removal(χ, S)
  let G := regularizedL(χ, t)
  have hG : Differentiable ℂ G := globalPrincipalValueConverse_normTwist_range_regular χ t _hχ
  have hE : Differentiable ℂ E :=
    globalPrincipalValueConverse_nontrivial_removal_differentiable χ S
  let pv (f : P) : pvPolar(S) := ⟨PV(S) f.val, ⟨f.val, f.property, rfl⟩⟩
  have hdiff (b : B) : Differentiable ℂ b.val := fun w ↦
    (b.property.2.1 w (by simp)).differentiableAt (by simp)
  have hmul (f : P) (z : ℂ) : (ZB (pv f)).val z = E z * (M f).val z := by
    have h := globalPrincipalValueConverse_mellin S χ f.val
    have hg : (ZB (pv f)).val =ᶠ[codiscrete ℂ] E * (M f).val := by
      filter_upwards [h] with w hw
      exact (hZB _ w).trans (hw.trans (congrArg (E w * ·) (hM.2.2.1 f w).symm))
    exact ((((hdiff _).analyticAt z).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      ((hE.mul (hdiff _)).analyticAt z).meromorphicNFAt).mp (nhdsNE_le_codiscrete z hg)).eq_of_nhds
  ext b
  constructor
  · rintro ⟨⟨_, f, hf, rfl⟩, rfl⟩
    let g : P := ⟨f, hf⟩
    have hm : M g ∈ Set.range M := ⟨_, rfl⟩
    rw [hM.2.2.2.1] at hm
    obtain ⟨u, hu, h⟩ := hm
    refine ⟨u, hu, fun z ↦ ?_⟩
    exact (hmul g z).trans ((congrArg (E z * ·) (h z)).trans (mul_assoc _ _ _).symm)
  · rintro ⟨u, hu, h⟩
    have hfact (z : ℂ) : b.val z = E z * (G z * u z) := (h z).trans (mul_assoc _ _ _)
    let b' : B := ⟨G * u, globalPrincipalValueConverse_nontrivial_divide_prod_exp S
      (fun v z ↦ (finiteHeckeEulerFactor χ v z)⁻¹)
      (fun v _ ↦ globalPrincipalValueConverse_nontrivial_euler_form χ v)
      b (G * u) (hG.mul hu) hfact⟩
    have hb' : b' ∈ Set.range M := hM.2.2.2.1.symm ▸ ⟨u, hu, fun _ ↦ rfl⟩
    obtain ⟨g, hg⟩ := hb'
    refine ⟨pv g, Subtype.ext (funext fun z ↦ ?_)⟩
    rw [hmul, hg]
    exact (hfact z).symm

private theorem globalPrincipalValueConverse_normTwist_openMap_frechet_submodule {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsFrechetTVS E)
    (A : Submodule ℂ E) (hP : IsClosed (A : Set E)) : IsFrechetTVS A := by
  obtain ⟨hadd, hpoly, hmet, hcomp⟩ := hE
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomp
  let : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
  refine ⟨inferInstance, inferInstance, TopologicalSpace.MetrizableSpace.subtype _, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact hP.completeSpace_coe

/-- The closed intersections with the Fréchet stages of a strict LF-space
exhaust the source. A continuous surjection onto a closed Fréchet range is open. -/
private theorem globalPrincipalValueConverse_normTwist_openMap_stages
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsStrictLFSpace X) (hY : IsFrechetTVS Y) (A : Submodule ℂ X)
    (hA : IsClosed (A : Set X)) (M : A →L[ℂ] Y) (hM : IsClosed (Set.range M)) :
    IsOpenMap M.rangeRestrict := by
  obtain ⟨hT2, T, hmono, hstage, hcover, _⟩ := hX
  let D (k : ℕ) := A.comap (T k).subtype
  let d (k : ℕ) : D k →L[ℂ] A :=
    ((T k).subtypeL.comp (D k).subtypeL).codRestrict A fun x ↦ x.property
  have hD (k : ℕ) : IsFrechetTVS (D k) :=
    globalPrincipalValueConverse_normTwist_openMap_frechet_submodule (hstage k) _
      (hA.preimage continuous_subtype_val)
  have hinc (k : ℕ) : Set.range (d k) ⊆ Set.range (d (k + 1)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨⟨x.val.val, hmono k.le_succ x.val.property⟩, x.property⟩, rfl⟩
  have hcov (x : A) : ∃ k, x ∈ Set.range (d k) := by
    obtain ⟨k, hk⟩ := hcover x.val
    exact ⟨k, ⟨⟨⟨x.val, hk⟩, x.property⟩, rfl⟩⟩
  exact isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS
    (globalPrincipalValueConverse_normTwist_openMap_frechet_submodule hY M.range hM))
    hD d hinc hcov M.rangeRestrict M.surjective_rangeRestrict

/-- Paper: Theorem 6.3.2.2(1), pp. 309–310, equation (6.3.2.20).
The Mellin chart of the principal-value polar image is open onto a closed subspace of the
Schwartz–Bergman space. Closedness is the completeness of the image; openness is the open
mapping theorem for the nuclear Fréchet structure of the two spaces. -/
theorem globalPrincipalValueConverse_normTwist_openMap (S : Finset V) (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (ZB : pvPolar(S) →L[ℂ] B)
    (hZB : ∀ (f : pvPolar(S)) s, (ZB f).val s = Z(f.val, χ, s)) :
    IsOpenMap ZB.rangeRestrict ∧ IsClosed (Set.range ZB) := by
  have hE : Differentiable ℂ (removal(χ, S)) :=
    globalPrincipalValueConverse_nontrivial_removal_differentiable χ S
  have hR : IsClosed (Set.range ZB) := by
    rw [globalPrincipalValueConverse_normTwist_range S χ t _hχ ZB hZB]
    exact globalPrincipalValueConverse_nontrivial_closed
      (hE.mul (globalPrincipalValueConverse_normTwist_range_regular χ t _hχ))
  let vals : ℬ →L[ℂ] ℂ × ℂ := ⟨adelePolarValues, adelePolarValues_continuous⟩
  have hP : IsClosed (pvPolar(S) : Set ℬ) :=
    (adelePrincipalValue_isClosedEmbedding S).isClosedMap (P : Set ℬ) vals.isClosed_ker
  exact ⟨globalPrincipalValueConverse_normTwist_openMap_stages (adeleSchwartz_strictLF (F := F)).2
    (schwartzBergman_frechet _ isOpen_univ ordConnected_univ univ_nonempty) _ hP ZB hR, hR⟩

/-- Paper: Theorem 6.3.2.2(1), pp. 309–310, equation (6.3.2.20).
The kernel of the Mellin chart of the principal-value polar image is the principal-value image
of those polar tests that also lie in the kernel of the trivial homogeneous theta map. -/
theorem globalPrincipalValueConverse_normTwist_ker (S : Finset V) (χ : U) (t : ℝ)
    (_hχ : χ₀(χ) = ideleClassNormTwist (1 : U) (shift(t))) (ZB : pvPolar(S) →L[ℂ] B)
    (hZB : ∀ (f : pvPolar(S)) s, (ZB f).val s = Z(f.val, χ, s)) :
    ZB.ker = (((K(1) ⊓ (P)).map (PV(S))).comap (pvPolar(S)).subtype) := by
  classical
  refine (globalConverse_normTwist χ t _hχ).elim fun M hM ↦ ?_
  refine (globalPrincipalValueConverse_normTwist_divided_exact_transport (F := F) S
    (1 : PontryaginDual C₁)).elim fun e he ↦ ?_
  have hclass (f : ℬ) : PV(S) f ∈ K(1) ↔ f ∈ K(1) := by
    have hq : (pvMorphism(S, (1 : PontryaginDual C₁))).rangeRestrict f = 0 ↔
        (K(1)).mkQ (PV(S) f) = 0 := Subtype.ext_iff
    rw [← he, map_eq_zero_iff e e.injective] at hq
    exact (Submodule.Quotient.mk_eq_zero _).symm.trans
      (hq.symm.trans (Submodule.Quotient.mk_eq_zero _))
  apply Submodule.ext
  rintro ⟨_, f, hf, rfl⟩
  let y : pvPolar(S) := ⟨PV(S) f, ⟨f, hf, rfl⟩⟩
  let g : P := ⟨PV(S) f, globalPrincipalValueConverse_normTwist_mellin_map_polar S ⟨f, hf⟩⟩
  have hval : ZB y = M g := Subtype.ext (funext fun z ↦ (hZB y z).trans (hM.2.2.1 g z).symm)
  change ZB y = 0 ↔ PV(S) f ∈ (K(1) ⊓ P).map (PV(S))
  rw [hval]
  change g ∈ M.ker ↔ _
  rw [hM.2.2.2.2]
  change PV(S) f ∈ K(1) ↔ _
  rw [hclass]
  constructor
  · exact fun hk ↦ ⟨f, ⟨hk, hf⟩, rfl⟩
  · rintro ⟨f', hf', heq⟩
    exact (adelePrincipalValue_isClosedEmbedding S).injective heq ▸ hf'.1

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
  obtain ⟨ZB, hZB⟩ := globalPrincipalValueConverse_normTwist_mellin_map S χ t _hχ
  obtain ⟨hopen, hclosed⟩ := globalPrincipalValueConverse_normTwist_openMap S χ t _hχ ZB hZB
  exact ⟨ZB, hopen, hclosed, hZB,
    globalPrincipalValueConverse_normTwist_range S χ t _hχ ZB hZB,
    globalPrincipalValueConverse_normTwist_ker S χ t _hχ ZB hZB⟩

end PrincipalValue

end GlobalConverse

end RiemannMasullo
