module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import RiemannMasullo.AppB_AnalyticNT.Sec6

/-!
# Appendix B.6: statements that are false as printed

The printed claims are kept as propositions with separate refutation statements.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped Topology

namespace RiemannMasullo

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Proposition B.6.1.1, real-zero clause, p. 636. As printed: for every
number field and continuous character, any zero of its finite Hecke L-function at
a real point in `[1/2, 1]` forces the square of the character to be trivial.
Positive meromorphic order expresses a genuine zero. The repaired
`finiteHeckeL_zeroFreeRegion` omits the real-zero clause. See ERRATA F23. -/
def Printed.finiteHeckeL_quadratic_of_real_zero : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    MeromorphicNFOn L univ → (∀ s : halfPlane, L s = finiteHeckeL χ s) →
      ∀ σ ∈ Icc (1 / 2 : ℝ) 1, 0 < meromorphicOrderAt L (σ : ℂ) → χ ^ 2 = 1

/-- Paper: Proposition B.6.1.1, real-zero clause, p. 636. Choose a nonreal critical-line
zero `1/2 + iγ` of the Riemann zeta function by Hardy's theorem. Over the rational
field, the unitary character `χ = |·|^(iγ)` has finite L-function `ζ(s + iγ)` on `Re s > 1`.
Take its meromorphic normal form on the plane, setting the value at `1 - iγ` to zero.
At `σ = 1/2` it has positive order. The idelic norm is onto the positive reals, so `γ ≠ 0`
implies `χ ^ 2 ≠ 1`. -/
theorem Printed.finiteHeckeL_quadratic_of_real_zero_false :
    ¬ Printed.finiteHeckeL_quadratic_of_real_zero := by
  sorry

/-- Paper: Paragraph following Proposition B.6.1.1, p. 636. As printed: for every
number field and every continuous character whose square is nontrivial, the finite Hecke
L-function of its square is entire. The note after `finiteHeckeL_zeroFreeRegion`
records the shifted pole. See ERRATA F24. -/
def Printed.finiteHeckeL_sq_entire_of_not_quadratic : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    χ ^ 2 ≠ 1 → MeromorphicNFOn L univ →
      (∀ s : halfPlane, L s = finiteHeckeL (χ ^ 2) s) → Differentiable ℂ L

/-- A field isomorphic to the rationals is a number field. -/
private theorem finiteHeckeL_sq_entire_numberField (K : Type*) [Field K] (e : K ≃+* ℚ) :
    NumberField K := by
  let : CharZero K := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  let : FiniteDimensional ℚ K := Module.Finite.of_injective e.toRatAlgEquiv.toLinearMap e.injective
  exact ⟨⟩

/-- An imaginary power of the idelic norm gives a nonquadratic character whose square
is trivial on the norm-one subgroup. -/
private theorem finiteHeckeL_sq_entire_char_exists (F : Type*) [Field F] [NumberField F] :
    ∃ χ : U[F], χ ^ 2 ≠ 1 ∧
    (χ ^ 2).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  let c := ideleClassNormTwist (1 : U[F]) Complex.I
  have hnorm (g : IdeleClassGroup (𝓞 F) F) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _)), Complex.I_re, Real.rpow_zero]
  let χ : U[F] :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hc (g : IdeleClassGroup (𝓞 F) F) :
      (χ g : ℂ) = (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I := by
    change (1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I = _
    simp
  refine ⟨χ, ?_, ?_⟩
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
    let u : Units NNReal := Units.mk0 ⟨Real.exp (Real.pi / 2), (Real.exp_pos _).le⟩
      (by intro h; exact (Real.exp_ne_zero _) (congrArg (fun x : NNReal ↦ (x : ℝ)) h))
    obtain ⟨g, hg⟩ := hsurj u
    have hval := DFunLike.congr_fun h g
    have he : (χ g : ℂ) ^ 2 = 1 := by
      have hv := congrArg (fun x : Circle ↦ (x : ℂ)) hval
      change ((χ g ^ 2 : Circle) : ℂ) = ((1 : Circle) : ℂ) at hv
      simpa using hv
    rw [hc, ← Complex.cpow_nat_mul, hg] at he
    change ((Real.exp (Real.pi / 2) : ℝ) : ℂ) ^ (2 * Complex.I) = 1 at he
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp] at he
    have hx : ((Real.pi / 2 : ℝ) : ℂ) * (2 * Complex.I) = Real.pi * Complex.I := by push_cast; ring
    rw [hx, Complex.exp_pi_mul_I] at he
    norm_num at he
  · ext g
    change (χ g.1 : ℂ) ^ 2 = 1
    rw [hc]
    have hg : ideleClassNorm F g.1 = 1 := MonoidHom.mem_ker.mp g.2
    change (((↑(↑(ideleClassNorm F g.1) : NNReal) : ℝ) : ℂ) ^ Complex.I) ^ 2 = 1
    rw [hg]
    simp

/-- The completed L-function has a pole on the one-line when the character is
trivial on the norm-one subgroup, so its finite part cannot be entire. -/
private theorem finiteHeckeL_sq_entire_pole_contra (F : Type*) [Field F] [NumberField F] (ψ : U[F])
    (hψ : ψ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (heq : ∀ s : halfPlane, L s = finiteHeckeL ψ s) : False := by
  let P : ℂ → ℂ := fun s ↦ heckeGammaFactor ψ s * L s
  have hP : MeromorphicOn P univ := fun s _ ↦
    (meromorphic_heckeGammaFactor ψ s).mul (hL.analyticAt s).meromorphicAt
  let Q := toMeromorphicNFOn P univ
  have hQ : MeromorphicNFOn Q univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hEq : ∀ s : halfPlane, Q s = completedHeckeL ψ s := by
    intro s
    have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have ha : AnalyticAt ℂ (heckeGammaFactor ψ) s := by
      apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
        (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos ψ hz).differentiableWithinAt)
      exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    have hPa : AnalyticAt ℂ P s := ha.mul (hL.analyticAt s)
    change toMeromorphicNFOn P univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hP (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hPa.meromorphicNFAt]
    change heckeGammaFactor ψ s * L s = _
    rw [heq s]
    rfl
  obtain ⟨t, ⟨_, _, hpole, _⟩, _⟩ := completedHeckeL_continuation_simplePoles ψ Q hQ hEq hψ
  let p : ℂ := 1 + Complex.I * (t : ℂ)
  have hp : 0 < p.re := by simp [p, Complex.mul_re]
  have ha : AnalyticAt ℂ (heckeGammaFactor ψ) p := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos ψ hz).differentiableWithinAt)
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
  have hPa : AnalyticAt ℂ P p := ha.mul (hL.analyticAt p)
  have hord : meromorphicOrderAt Q p = meromorphicOrderAt P p :=
    meromorphicOrderAt_congr (hP.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ p))
  have hn := hPa.meromorphicOrderAt_nonneg
  rw [← hord, hpole] at hn
  exact (not_le_of_gt (show (-1 : WithTop ℤ) < 0 by decide)) hn

/-- Paper: Paragraph following Proposition B.6.1.1, p. 636. Over the rational
field take `χ = |·|^i`. Its square is nontrivial because the idelic norm is
onto. The finite L-function of its square equals `ζ(s + 2i)` on `Re s > 1`.
Use the meromorphic normal form on the plane, setting the value at `1 - 2i` to zero.
The germ there still has a simple pole, so this continuation is not entire. -/
theorem Printed.finiteHeckeL_sq_entire_of_not_quadratic_false :
    ¬ Printed.finiteHeckeL_sq_entire_of_not_quadratic := by
  intro h
  let : Field (ULift ℚ) := (Equiv.ulift : ULift ℚ ≃ ℚ).field
  let : NumberField (ULift ℚ) :=
    finiteHeckeL_sq_entire_numberField _ (Equiv.ulift : ULift ℚ ≃ ℚ).ringEquiv
  obtain ⟨χ, hχ, hk⟩ := finiteHeckeL_sq_entire_char_exists (ULift ℚ)
  obtain ⟨L, hL, heq⟩ := finiteHeckeL_exists_continuation (χ ^ 2)
  exact finiteHeckeL_sq_entire_pole_contra (ULift ℚ) (χ ^ 2) hk L
    (h (ULift ℚ) χ L hχ hL heq) heq

/-- Paper: Lemma B.6.1.2(1), p. 637. As printed: for every number field and
continuous character trivial on the norm-one classes, after undoing its imaginary
norm twist the ideal summatory function divided by its argument tends to the
norm-one Tamagawa volume times the inverse square root of the norm of the different.
This is the asymptotic in (B.6.1.7), for the character's norm parameter.
The repaired `heckeIdealSummatory_tendsto_of_trivial_on_normOne` uses the
Dedekind zeta residue, equal to the volume alone. See ERRATA F25. -/
def Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 →
      ∀ t₀ : ℝ,
        ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
          let d : ℝ := (differentIdeal ℤ (𝓞 F)).absNorm
          let μ := normOneIdeleClassTamagawaMeasure F
          Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ (Complex.I * t₀)) x / x)
            atTop (𝓝 (((Real.sqrt d)⁻¹ * μ.real univ : ℝ) : ℂ))

/-- A universe lift of `ℚ(i)` is a number field. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_numberField.{u} :
    NumberField (ULift.{u} (CyclotomicField 4 ℚ)) := by
  let e : ULift.{u} (CyclotomicField 4 ℚ) ≃+* CyclotomicField 4 ℚ := ULift.ringEquiv
  have : CharZero (ULift.{u} (CyclotomicField 4 ℚ)) :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  have : FiniteDimensional ℚ (ULift.{u} (CyclotomicField 4 ℚ)) :=
    Module.Finite.of_injective e.toRatAlgEquiv.toLinearMap e.injective
  exact ⟨⟩

/-- A universe lift of `ℚ(i)` has degree two over `ℚ`. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_finrank.{u} :
    1 < Module.finrank ℚ (ULift.{u} (CyclotomicField 4 ℚ)) := by
  let e : ULift.{u} (CyclotomicField 4 ℚ) ≃+* CyclotomicField 4 ℚ := ULift.ringEquiv
  have h := CyclotomicField.isCyclotomicExtension 4 ℚ
  have h4 := @IsCyclotomicExtension.finrank 4 _ ℚ (CyclotomicField 4 ℚ) _ _ _ _ (by exact h)
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))
  rw [e.toRatAlgEquiv.toLinearEquiv.finrank_eq]
  have h2 : Module.finrank ℚ (CyclotomicField 4 ℚ) = Nat.totient 4 := by convert h4
  rw [h2]
  decide

/-- The norm-one Tamagawa volume equals the residue of the Dedekind zeta function. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_volume
    (F : Type*) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F).real univ = dedekindZeta_residue F := by
  rw [Measure.real, normOneIdeleClassTamagawaMeasure_volume, dedekindZeta_residue_def]
  have := NumberField.classNumber_pos F
  have := NumberField.Units.regulator_pos F
  have := NumberField.Units.torsionOrder_pos F
  have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
  rw [ENNReal.toReal_ofReal (by positivity), Nat.cast_natAbs, Int.cast_abs]
  ring

/-- For a number field other than `ℚ` the printed limit differs from the residue. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_contra.{u}
    (F : Type u) [Field F] [NumberField F] (hF : 1 < Module.finrank ℚ F)
    (h : Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne.{u}) : False := by
  have h1 : (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)).toMonoidHom.comp
      (ideleClassNorm F).ker.subtype = 1 := by
    ext; rfl
  have h0 : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 =
      ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (-Complex.I * ((0 : ℝ) : ℂ)) := by
    simp
  have hp : Tendsto (fun x : ℝ ↦ heckeIdealSummatory
        (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
          (Complex.I * ((0 : ℝ) : ℂ))) x / x)
      atTop (𝓝 (((Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ))⁻¹ *
        (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ)) := h F 1 h1 0 h0
  have hr := (heckeIdealSummatory_tendsto_of_trivial_on_normOne _ h1).2 0 h0
  have he := tendsto_nhds_unique hr hp
  rw [heckeIdealSummatory_tendsto_of_trivial_on_normOne_volume, Complex.ofReal_inj,
    NumberField.absNorm_differentIdeal F (𝓞 F)] at he
  have hpos := NumberField.dedekindZeta_residue_pos F
  have hd := NumberField.abs_discr_gt_two hF
  have hs : Real.sqrt ((discr F).natAbs : ℝ) = 1 := by
    have hm : (Real.sqrt ((discr F).natAbs : ℝ))⁻¹ * dedekindZeta_residue F =
        1 * dedekindZeta_residue F := by
      rw [one_mul]; exact he.symm
    exact inv_eq_one.mp (mul_right_cancel₀ hpos.ne' hm)
  rw [Real.sqrt_eq_one, Nat.cast_natAbs, Int.cast_abs] at hs
  have : (2 : ℝ) < |(discr F : ℝ)| := by exact_mod_cast hd
  linarith

/-- Paper: Lemma B.6.1.2(1), p. 637. Take `F = ℚ(√5)`, `χ = 1`, and
`t₀ = 0`. With `φ = (1 + √5) / 2`, the ideal-counting limit is the zeta
residue `2 log φ / √5`, equal to the norm-one volume by (A.3.2.1). The
norm of the different is five, so the display instead gives `2 log φ / 5`. -/
theorem Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne_false :
    ¬ Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne := fun h ↦
  @heckeIdealSummatory_tendsto_of_trivial_on_normOne_contra _ _
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_numberField
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_finrank h

end RiemannMasullo
