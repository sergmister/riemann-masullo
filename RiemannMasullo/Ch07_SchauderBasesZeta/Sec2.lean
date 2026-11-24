module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
public import RiemannMasullo.Ch06_LocalGlobal.Sec2

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Tactic.TFAE
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# §7.2 Poles of the S-idelic zeta functions

The finite set `S` lists the finite places. Every archimedean place is included.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Places" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative (𝔸[F]))
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "m𝔽" => ideleClassNorm F
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "J₁" => (mₛ).ker
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ hmₛ
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction mₛ c = (circleToComplex).comp ω)
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "coeff(" c ", " k ")" => (fun f : ℬₛ ↦ sLocalZLaurentCoeff f c (-(k : ℤ)))

-- TODO(paper-gap): The inclusions in (7.2.0.1)–(7.2.0.2) require an effective divisor.
-- This section uses the earlier meromorphic model on the character components.
-- TODO(paper-gap): (7.2.1.3)–(7.2.1.5) repeat the asymptotic expansion with
-- the missing constant term and repeated poles of Theorem 7.1.2.3. Use its
-- pole-free contour cutoff and the corrected complex pole family in §7.1.
-- At finite places the periodic lattice occurs only for unramified characters.
-- TODO(paper-gap): In (7.2.1.8) the contour needs positive orientation and
-- must isolate the chosen pole. The coefficient uses the small-circle residue of §B.3.

/-- On a small punctured disc in the centered norm-twist chart every quasi-character is regular
for the correcting factor, and the chart is continuous on the disc. -/
private theorem sLocalZLaurentCoeff_continuous_linear_disc (c : Xₛ) :
    ∃ R > (0 : ℝ), (∀ z : ℂ, z ≠ 0 → ‖z‖ < R → 0 ≤ sLocalIdelicOrderBound (twistₛ c z)) ∧
      ContinuousOn (fun z : ℂ ↦ twistₛ c z) (Metric.ball 0 R) := by
  obtain ⟨χ, a, hca⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let ρ : ℂ → ℂ := fun w ↦ sLocalRhoFactor (twistₛ c w)
  have hρ : ρ = (fun s ↦ sLocalRhoFactor (twistₛ ((circleToComplex).comp χ) s)) ∘
      (fun t ↦ t + a) := by
    funext w
    change sLocalRhoFactor (twistₛ c w) = sLocalRhoFactor (twistₛ ((circleToComplex).comp χ) (w + a))
    rw [← hca, normTwist_normTwist]
  have hmer : MeromorphicAt ρ 0 := by
    have hm := sLocalRhoFactor_meromorphic (F := F) (S := S) χ
    have h2 := (hm (0 + a)).comp_analyticAt (g := fun t : ℂ ↦ t + a) (x := 0) (by fun_prop)
    rw [hρ]
    exact h2
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hmer.eventually_analyticAt
  obtain ⟨e, hc, he, hinv⟩ := sIdeleQuotient_hasNormTwistCharts F S c
  have h0 : (0 : ℂ) ∈ e.target := he ▸ e.map_source hc
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.mp e.open_target 0 h0
  have heq (z : ℂ) (hz : z ∈ e.target) : e.symm z = twistₛ c z :=
    ContinuousMonoidHom.ext fun g ↦ hinv z hz g
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz0 hz ↦ ?_, ?_⟩
  · have hA : AnalyticAt ℂ ρ z :=
      h₁ ⟨mem_ball_zero_iff.mpr (hz.trans_le (min_le_left _ _)), hz0⟩
    have e2 : (fun w ↦ sLocalRhoFactor (twistₛ (twistₛ c z) w)) = ρ ∘ (fun w ↦ w + z) := by
      funext w
      exact congrArg sLocalRhoFactor (normTwist_normTwist mₛ hmₛ c z w)
    have hA' : AnalyticAt ℂ (fun w ↦ sLocalRhoFactor (twistₛ (twistₛ c z) w)) 0 := by
      rw [e2]
      exact hA.comp_of_eq (by fun_prop) (zero_add z)
    exact le_min le_rfl hA'.meromorphicOrderAt_nonneg
  · have hsub : Metric.ball (0 : ℂ) (min ε₁ ε₂) ⊆ e.target := fun z hz ↦
      h₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact (e.continuousOn_symm.mono hsub).congr fun z hz ↦ (heq z (hsub hz)).symm

/-- At a regular point of the centered chart, the zeta germ of a test is analytic. -/
private theorem sLocalZLaurentCoeff_continuous_linear_analytic (f : ℬₛ) (c : Xₛ) (z : ℂ)
    (hz : 0 ≤ sLocalIdelicOrderBound (twistₛ c z)) :
    AnalyticAt ℂ (fun w ↦ sLocalIdelicZFunction f (twistₛ c w)) z := by
  have h := (sLocalZ_centered f (twistₛ c z)).2.2 hz
  have e : (fun w ↦ sLocalIdelicZFunction f (twistₛ c w)) =
      (fun w ↦ sLocalIdelicZFunction f (twistₛ (twistₛ c z) w)) ∘ (fun w ↦ w - z) := by
    funext w
    change sLocalIdelicZFunction f (twistₛ c w) =
      sLocalIdelicZFunction f (twistₛ (twistₛ c z) (w - z))
    rw [normTwist_normTwist, sub_add_cancel]
  rw [e]
  exact h.comp_of_eq (by fun_prop) (sub_self z)

/-- For a function analytic on a punctured disc, the residue at the center is the normalized
integral over any circle inside the disc. -/
private theorem sLocalZLaurentCoeff_continuous_linear_circle {g : ℂ → ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) (hg : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ g z) :
    complexResidue g 0 = circleIntegral g 0 r / (2 * (Real.pi : ℂ) * Complex.I) := by
  have key (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < R) :
      circleIntegral g 0 b = circleIntegral g 0 a := by
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable ha hab
      Set.countable_empty (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    · have hz1 : ‖z‖ ≤ b := mem_closedBall_zero_iff.mp hz.1
      have hz2 : a ≤ ‖z‖ := not_lt.mp fun h ↦ hz.2 (mem_ball_zero_iff.mpr h)
      have hz0 : z ≠ 0 := fun h ↦ by rw [h, norm_zero] at hz2; linarith
      exact (hg z hz0 (hz1.trans_lt hb)).continuousAt.continuousWithinAt
    · have hz1 : ‖z‖ < b := mem_ball_zero_iff.mp hz.1.1
      have hz2 : a < ‖z‖ := not_le.mp fun h ↦ hz.1.2 (mem_closedBall_zero_iff.mpr h)
      have hz0 : z ≠ 0 := fun h ↦ by rw [h, norm_zero] at hz2; linarith
      exact (hg z hz0 (hz1.trans hb)).differentiableAt
  unfold complexResidue
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT (hr.trans hrR)] with s hs
  congr 1
  rcases le_total r s with h | h
  · exact (key r s hr h hs.2).symm
  · exact key s r hs.1 h hrR

/-- A fixed additive, homogeneous and continuous functional, applied after a continuous linear
map and divided by a constant, is continuous and linear. -/
private theorem sLocalZLaurentCoeff_continuous_linear_abstract {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [AddCommGroup W] [Module ℂ W]
    [TopologicalSpace W] (M : V →ₗ[ℂ] W) (hM : Continuous M) (Φ : W → ℂ) (hΦ : Continuous Φ)
    (hadd : ∀ u v, Φ (u + v) = Φ u + Φ v) (hsmul : ∀ (b : ℂ) u, Φ (b • u) = b * Φ u) (K : ℂ)
    (a : V → ℂ) (h : ∀ f, a f = Φ (M f) / K) : Continuous a ∧ IsLinearMap ℂ a := by
  refine ⟨?_, ⟨fun f g ↦ ?_, fun b f ↦ ?_⟩⟩
  · rw [show a = fun f ↦ Φ (M f) / K from funext h]
    exact (hΦ.comp hM).div_const K
  · rw [h, h, h, map_add, hadd, add_div]
  · rw [h, h, map_smul, hsmul, smul_eq_mul, mul_div_assoc]

/-- Paper: Theorem 7.2.1.1(1), p. 334.
Taking a Laurent coefficient in the centered chart is continuous and complex linear.
Deviation: Integer exponents cover both the nonnegative indices of Definition 7.1.2.1
and the polar coefficients extracted by (7.2.1.8). -/
theorem sLocalZLaurentCoeff_continuous_linear (c : Xₛ) (j : ℤ) :
    let a := fun f : ℬₛ ↦ sLocalZLaurentCoeff f c j
    Continuous a ∧ IsLinearMap ℂ a := by
  intro a
  obtain ⟨R, hR, hreg, hcont⟩ := sLocalZLaurentCoeff_continuous_linear_disc (F := F) (S := S) c
  have hr : 0 < R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  have hθ (θ : ℝ) : circleMap 0 (R / 2) θ ≠ 0 := circleMap_ne_center hr.ne'
  have hθR (θ : ℝ) : ‖circleMap 0 (R / 2) θ‖ < R := by
    rw [norm_circleMap_zero, abs_of_pos hr]
    exact hrR
  let γ : C(ℝ, {d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}) :=
    ⟨fun θ ↦ ⟨twistₛ c (circleMap 0 (R / 2) θ), hreg _ (hθ θ) (hθR θ)⟩,
      (hcont.comp_continuous (continuous_circleMap 0 (R / 2))
        fun θ ↦ mem_ball_zero_iff.mpr (hθR θ)).subtype_mk _⟩
  let k : ℝ → ℂ := fun θ ↦ circleMap 0 (R / 2) θ * Complex.I / circleMap 0 (R / 2) θ ^ (j + 1)
  have hk : Continuous k :=
    ((continuous_circleMap 0 (R / 2)).mul continuous_const).div
      ((continuous_circleMap 0 (R / 2)).zpow₀ (j + 1) fun θ ↦ Or.inl (hθ θ))
      fun θ ↦ zpow_ne_zero _ (hθ θ)
  let Φ : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ) → ℂ :=
    fun u ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, k θ * u (γ θ)
  have hi (u : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) :
      IntervalIntegrable (fun θ ↦ k θ * u (γ θ)) MeasureTheory.volume 0 (2 * Real.pi) :=
    (hk.mul (u.continuous.comp γ.continuous)).intervalIntegrable _ _
  have hΦc : Continuous Φ := by
    have h2 : Continuous (fun p : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ) × ℝ ↦
        k p.2 * (p.1.comp γ) p.2) :=
      (hk.comp continuous_snd).mul (continuous_eval.comp
        (((ContinuousMap.continuous_precomp γ).comp continuous_fst).prodMk continuous_snd))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (u : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) (θ : ℝ) ↦ k θ * (u.comp γ) θ)
      h2 0 (2 * Real.pi)
  have hΦadd (u v : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) :
      Φ (u + v) = Φ u + Φ v := by
    simp only [Φ, ContinuousMap.add_apply, mul_add]
    exact intervalIntegral.integral_add (hi u) (hi v)
  have hΦsmul (b : ℂ) (u : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) :
      Φ (b • u) = b * Φ u := by
    simp only [Φ, ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (k _)]
    exact intervalIntegral.integral_const_mul b _
  have hformula (f : ℬₛ) :
      a f = Φ (sLocalIdelicMellin (F := F) (S := S) f).val / (2 * (Real.pi : ℂ) * Complex.I) := by
    change sLocalZLaurentCoeff f c j = _
    unfold sLocalZLaurentCoeff
    rw [sLocalZLaurentCoeff_continuous_linear_circle
      (g := fun z ↦ sLocalIdelicZFunction f (twistₛ c z) / z ^ (j + 1)) hr hrR fun z hz0 hzR ↦
      (sLocalZLaurentCoeff_continuous_linear_analytic f c z (hreg z hz0 hzR)).div
        (analyticAt_id.zpow hz0) (zpow_ne_zero _ hz0)]
    congr 1
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    change deriv (circleMap 0 (R / 2)) θ • (sLocalIdelicZFunction f
        (twistₛ c (circleMap 0 (R / 2) θ)) / circleMap 0 (R / 2) θ ^ (j + 1)) =
      k θ * sLocalIdelicZFunction f (twistₛ c (circleMap 0 (R / 2) θ))
    generalize sLocalIdelicZFunction f (twistₛ c (circleMap 0 (R / 2) θ)) = Y
    rw [deriv_circleMap, smul_eq_mul]
    simp only [k, zero_add]
    ring
  have hM : Continuous (fun f : ℬₛ ↦ ((sLocalIdelicMellin (F := F) (S := S) f) :
      C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ))) :=
    sLocalIdelicMellin_continuous.subtype_val
  exact sLocalZLaurentCoeff_continuous_linear_abstract
    ((Submodule.subtype _).comp (sLocalIdelicMellin (F := F) (S := S))) hM Φ hΦc hΦadd hΦsmul
    _ a hformula

/-- Paper: Theorem 7.2.1.1(1), p. 334.
Each Laurent coefficient of nonpositive exponent depends continuously and complex
linearly on the S-adelic test.
Deviation: The coefficient indexed by `k` here has exponent `-k`, as required by
the principal part formula and the Laurent convention of Definition 7.1.2.1. -/
theorem sLocalPrincipalPartCoeff_continuous_linear (c : Xₛ) (k : ℕ) :
    Continuous coeff(c, k) ∧ IsLinearMap ℂ coeff(c, k) :=
  sLocalZLaurentCoeff_continuous_linear c (-(k : ℤ))

/-- Paper: Theorem 7.2.1.1(1)–(2), p. 334.
The coefficient of exponent `-k` is a continuous linear functional on the test space. -/
def sLocalPrincipalPartCoeff (c : Xₛ) (k : ℕ) : StrongDual ℂ ℬₛ :=
  ⟨(sLocalPrincipalPartCoeff_continuous_linear c k).2.mk' coeff(c, k),
    (sLocalPrincipalPartCoeff_continuous_linear c k).1⟩

/-- Paper: Theorem 7.2.1.1(1), p. 334.
The bundled functional evaluates to the coefficient of the Laurent power `-k`. -/
theorem sLocalPrincipalPartCoeff_apply (c : Xₛ) (k : ℕ) (f : ℬₛ) :
    sLocalPrincipalPartCoeff c k f = sLocalZLaurentCoeff f c (-(k : ℤ)) := rfl

-- TODO(paper-gap): In Theorem 7.2.1.1(2), lower coefficients at a multiple
-- pole mix with higher ones under translation. The leading coefficient has
-- the claimed weight, as stated in Theorem 7.2.1.4(1).

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The coefficient annihilates the kernel of homogeneous theta on the component
of its center. This gives continuous descent through both theta quotients.
Deviation: The weight equation for the leading coefficient is stated in
Theorem 7.2.1.4(1). -/
theorem sLocalPrincipalPartCoeff_ker (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) :
    Kₛ(ω) ≤ (sLocalPrincipalPartCoeff c k).ker := by
  have residue (Z : ℂ → ℂ) (p : ℤ) (hZ : ∀ z, Z z = 0) :
      complexResidue (fun z : ℂ ↦ Z z / z ^ p) 0 = 0 := by
    simp [hZ, complexResidue, circleIntegral]
    exact tendsto_const_nhds.limUnder_eq
  intro f hf
  have hv := (mem_sLocalHomogeneousAdelicTheta_ker_iff (F := F) (S := S) ω f).mp hf
  refine (exists_sLocalNormTwist (F := F) (S := S) c).elim fun χ ha ↦ ha.elim fun a hca ↦ ?_
  let χ₀ : Xₛ := (circleToComplex).comp χ
  have hω := (congrArg (normOneRestriction mₛ) hca).trans hc
  have hr (z : ℂ) (g : J₁) : normOneRestriction mₛ (twistₛ χ₀ z) g = (ω g : ℂ) :=
    (normOneRestriction_unitaryChart mₛ hmₛ χ z g).trans
      ((normOneRestriction_unitaryChart mₛ hmₛ χ a g).symm.trans (DFunLike.congr_fun hω g))
  have hz : (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ χ₀ z)) = 0 := by
    refine eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f χ)
      (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0 fun z hz ↦ ?_
    let d := (⟨twistₛ χ₀ z, sLocalOrderBound_positive χ hz⟩ :
      {q : Xₛ // 0 ≤ sLocalIdelicOrderBound q})
    exact (sLocalIdelicMellin_apply f d).symm.trans (hv d (hr z))
  change complexResidue (fun z : ℂ ↦
    sLocalIdelicZFunction f (twistₛ c z) / z ^ (-(k : ℤ) + 1)) 0 = 0
  apply residue
  intro z
  have shift := (congrArg (fun b : Xₛ ↦ twistₛ b z) hca.symm).trans
    (normTwist_normTwist mₛ hmₛ χ₀ a z)
  exact (congrArg (sLocalIdelicZFunction f) shift).trans (congrFun hz (z + a))

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The coefficient acts on the homogeneous theta quotient of its norm-one character. -/
def sLocalThetaPrincipalPartCoeff (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) : StrongDual ℂ (Θₛ(ω)) :=
  (Kₛ(ω)).liftQL (sLocalPrincipalPartCoeff c k) (sLocalPrincipalPartCoeff_ker ω c hc k)

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The descended coefficient recovers the original coefficient on a test representative. -/
theorem sLocalThetaPrincipalPartCoeff_mk (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) (f : ℬₛ) :
    sLocalThetaPrincipalPartCoeff ω c hc k ((Kₛ(ω)).mkQL f) =
      sLocalZLaurentCoeff f c (-(k : ℤ)) := rfl

/-- Residues at `0` only depend on the germ on a punctured neighbourhood. -/
theorem sLocalPrincipalPartCoeff_translate_congr {g h : ℂ → ℂ}
    (he : g =ᶠ[𝓝[≠] (0 : ℂ)] h) : complexResidue g 0 = complexResidue h 0 := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- A germ agreeing off `0` with a function analytic at `0` has residue zero there. -/
private theorem sLocalPrincipalPartCoeff_translate_residue_zero {W H : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (he : W =ᶠ[𝓝[≠] (0 : ℂ)] H) : complexResidue W 0 = 0 := by
  have he' : W =ᶠ[𝓝[≠] (0 : ℂ)] (fun z ↦ (z * H z) / (z - 0)) := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, mul_div_cancel_left₀ _ hz0']
  rw [sLocalPrincipalPartCoeff_translate_congr he',
    complexResidue_div_sub (g := fun z ↦ z * H z) (analyticAt_id.mul hH), zero_mul]

/-- For functions analytic on a common punctured disc, the residue at the center is additive
and commutes with constant factors. -/
private theorem sLocalPrincipalPartCoeff_translate_add {F G : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ G z) (C : ℂ) :
    complexResidue (fun z ↦ C * F z + G z) 0 = C * complexResidue F 0 + complexResidue G 0 := by
  have hr : 0 < R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  have hc (H : ℂ → ℂ) (hH : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ H z) :
      CircleIntegrable H 0 (R / 2) := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz ↦ ?_
    have hz' : ‖z‖ = R / 2 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := fun h ↦ by rw [h, norm_zero] at hz'; linarith
    exact (hH z hz0 (by rw [hz']; exact hrR)).continuousAt.continuousWithinAt
  have hCF : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ (fun z ↦ C * F z) z :=
    fun z h0 h ↦ analyticAt_const.mul (hF z h0 h)
  rw [sLocalZLaurentCoeff_continuous_linear_circle (g := fun z ↦ C * F z + G z) hr hrR
      fun z h0 h ↦ (hCF z h0 h).add (hG z h0 h),
    sLocalZLaurentCoeff_continuous_linear_circle hr hrR hF,
    sLocalZLaurentCoeff_continuous_linear_circle hr hrR hG,
    circleIntegral.integral_add (hc _ hCF) (hc G hG), circleIntegral.integral_const_mul]
  ring

/-- For functions analytic on a common punctured disc, the residue at the center of a finite
linear combination is the linear combination of the residues. -/
private theorem sLocalPrincipalPartCoeff_translate_sum (n : ℕ) (C : ℕ → ℂ) (G : ℕ → ℂ → ℂ)
    {R : ℝ} (hR : 0 < R) (hG : ∀ j, ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ (G j) z) :
    complexResidue (fun z ↦ ∑ j ∈ Finset.range n, C j * G j z) 0 =
      ∑ j ∈ Finset.range n, C j * complexResidue (G j) 0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact sLocalPrincipalPartCoeff_translate_residue_zero (H := fun _ ↦ 0) analyticAt_const
      Filter.EventuallyEq.rfl
  | succ n ih =>
    have hS : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R →
        AnalyticAt ℂ (fun z ↦ ∑ j ∈ Finset.range n, C j * G j z) z := fun z h0 h ↦ by
      have := Finset.analyticAt_sum (Finset.range n) (f := fun j z ↦ C j * G j z) (c := z)
        fun j _ ↦ analyticAt_const.mul (hG j z h0 h)
      convert this using 1
      funext w
      rw [Finset.sum_apply]
    simp only [Finset.sum_range_succ]
    have e : (fun z ↦ ∑ j ∈ Finset.range n, C j * G j z + C n * G n z) =
        fun z ↦ C n * G n z + ∑ j ∈ Finset.range n, C j * G j z := funext fun z ↦ add_comm _ _
    rw [e, sLocalPrincipalPartCoeff_translate_add hR (hG n) hS, ih, add_comm]

/-- The derivatives at `0` of a polynomial `∑ c j * z ^ j` recover its coefficients. -/
private theorem sLocalPrincipalPartCoeff_translate_poly (c : ℕ → ℂ) (n i : ℕ) :
    iteratedDeriv i (fun z : ℂ ↦ ∑ j ∈ Finset.range n, c j * z ^ j) 0 =
      if i < n then c i * (i.factorial : ℂ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (fun z : ℂ ↦ ∑ j ∈ Finset.range (n + 1), c j * z ^ j) =
        (fun z : ℂ ↦ ∑ j ∈ Finset.range n, c j * z ^ j) + (fun z : ℂ ↦ c n * z ^ n) := by
      funext z
      simp [Finset.sum_range_succ]
    rw [e, iteratedDeriv_add (by fun_prop) (by fun_prop), ih,
      iteratedDeriv_const_mul _ (by fun_prop), iteratedDeriv_pow]
    rcases lt_trichotomy i n with h | rfl | h
    · rw [if_pos h, if_pos (by omega), zero_pow (by omega), mul_zero, mul_zero, add_zero]
    · rw [if_neg (lt_irrefl _), if_pos (by omega), Nat.sub_self, pow_zero, mul_one,
        Nat.descFactorial_self, zero_add]
    · rw [if_neg (by omega), if_neg (by omega), (Nat.descFactorial_eq_zero_iff_lt).mpr h]
      simp

/-- The Laurent coefficient of exponent `-k` of `exp (L z)` times a germ with a pole of order at
most `m ≥ k` is the convolution of the Taylor coefficients of the exponential with the
coefficients of exponents `-k, …, -m` of the germ. -/
theorem sLocalPrincipalPartCoeff_translate_laurent {Z : ℂ → ℂ} (hZ : MeromorphicAt Z 0)
    {m k : ℕ} (hk : k ≤ m) (hord : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z 0)
    (C L : ℂ) :
    complexResidue (fun z ↦ C * (Complex.exp (L * z) * Z z / z ^ (-(k : ℤ) + 1))) 0 =
      C * ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z ↦ Z z / z ^ (-((k + j : ℕ) : ℤ) + 1)) 0 * L ^ j /
          (j.factorial : ℂ) := by
  obtain ⟨R, hR, hRZ⟩ : ∃ R > (0 : ℝ), ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ Z z := by
    obtain ⟨ε, hε, h⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hZ.eventually_analyticAt
    exact ⟨ε, hε, fun z hz0 hz ↦ h ⟨mem_ball_zero_iff.mpr hz, hz0⟩⟩
  let N := m - k
  let c : ℕ → ℂ := fun j ↦ L ^ j / (j.factorial : ℂ)
  let P : ℂ → ℂ := fun z ↦ ∑ j ∈ Finset.range (N + 1), c j * z ^ j
  let D : ℂ → ℂ := fun z ↦ Complex.exp (L * z) - P z
  let G : ℕ → ℂ → ℂ := fun j z ↦ Z z / z ^ (-((k + j : ℕ) : ℤ) + 1)
  let Q : ℂ → ℂ := fun z ↦ D z * Z z / z ^ (-(k : ℤ) + 1)
  have hDa : Differentiable ℂ D := by
    have hP : Differentiable ℂ P := by
      have := Differentiable.sum (u := Finset.range (N + 1)) (A := fun j z ↦ c j * z ^ j)
        fun j _ ↦ by fun_prop
      convert this using 1
      funext w
      rw [Finset.sum_apply]
    exact (by fun_prop : Differentiable ℂ fun z : ℂ ↦ Complex.exp (L * z)).sub hP
  have hG : ∀ j, ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ (G j) z := fun j z hz0 hzR ↦
    (hRZ z hz0 hzR).div (analyticAt_id.zpow hz0) (zpow_ne_zero _ hz0)
  have hQ : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ Q z := fun z hz0 hzR ↦
    ((hDa.analyticAt z).mul (hRZ z hz0 hzR)).div (analyticAt_id.zpow hz0) (zpow_ne_zero _ hz0)
  have hsplit : (fun z ↦ Complex.exp (L * z) * Z z / z ^ (-(k : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z ↦ (1 : ℂ) * Q z + ∑ j ∈ Finset.range (N + 1), c j * G j z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz0
    have hz : z ≠ 0 := hz0
    have hterm (j : ℕ) : c j * G j z = c j * z ^ j * Z z / z ^ (-(k : ℤ) + 1) := by
      simp only [G]
      rw [show -((k + j : ℕ) : ℤ) + 1 = (-(k : ℤ) + 1) - (j : ℤ) by push_cast; ring,
        zpow_sub₀ hz, zpow_natCast, div_div_eq_mul_div]
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Finset.sum_div, ← Finset.sum_mul]
    simp only [Q, D, P]
    ring
  have hQ0 : complexResidue Q 0 = 0 := by
    have hD0 : ((N + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt D 0 := by
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hDa.analyticAt 0)).mpr
        fun i hi ↦ ?_
      have hsub := iteratedDeriv_sub (n := i) (x := (0 : ℂ))
        (f := fun z : ℂ ↦ Complex.exp (L * z)) (g := P) (by fun_prop)
        (by simp only [P]; fun_prop)
      change iteratedDeriv i ((fun z : ℂ ↦ Complex.exp (L * z)) - P) 0 = 0
      rw [hsub, iteratedDeriv_cexp_const_mul, sLocalPrincipalPartCoeff_translate_poly, if_pos hi]
      show L ^ i * Complex.exp (L * 0) - L ^ i / (i.factorial : ℂ) * (i.factorial : ℂ) = 0
      rw [mul_zero, Complex.exp_zero, mul_one, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)), sub_self]
    obtain ⟨g, hg, hgev⟩ := (natCast_le_analyticOrderAt (hDa.analyticAt 0)).mp hD0
    cases ho : meromorphicOrderAt Z 0 with
    | top =>
      refine sLocalPrincipalPartCoeff_translate_residue_zero (H := fun _ ↦ 0) analyticAt_const ?_
      filter_upwards [meromorphicOrderAt_eq_top_iff.mp ho] with z hz
      simp only [Q, hz, mul_zero, zero_div]
    | coe n =>
      rw [ho] at hord
      have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp hord
      obtain ⟨h, hh, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hZ).mp ho
      have he : 0 ≤ ((N + 1 : ℕ) : ℤ) + n - (-(k : ℤ) + 1) := by omega
      refine sLocalPrincipalPartCoeff_translate_residue_zero
        (H := fun z ↦ z ^ (((N + 1 : ℕ) : ℤ) + n - (-(k : ℤ) + 1)).toNat * (g z * h z))
        ((analyticAt_id.pow _).mul (hg.mul hh)) ?_
      filter_upwards [hev, hgev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with z hz1 hz2 hz0
      have hz : z ≠ 0 := hz0
      simp only [Q]
      have hpow : z ^ (((N + 1 : ℕ) : ℤ) + n - (-(k : ℤ) + 1)).toNat =
          z ^ (N + 1) * z ^ n / z ^ (-(k : ℤ) + 1) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg he, zpow_sub₀ hz, zpow_add₀ hz, zpow_natCast]
      rw [hz2, hz1, sub_zero, smul_eq_mul, smul_eq_mul, hpow]
      ring
  have hsplit' : (fun z ↦ C * (Complex.exp (L * z) * Z z / z ^ (-(k : ℤ) + 1))) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z ↦ C * Q z + ∑ j ∈ Finset.range (N + 1), (C * c j) * G j z) := by
    filter_upwards [hsplit] with z hz
    rw [hz, mul_add, one_mul, Finset.mul_sum]
    exact congrArg (C * Q z + ·) (Finset.sum_congr rfl fun j _ ↦ (mul_assoc _ _ _).symm)
  rw [sLocalPrincipalPartCoeff_translate_congr hsplit',
    sLocalPrincipalPartCoeff_translate_add hR hQ
      (fun z h0 h ↦ by
        have := Finset.analyticAt_sum (Finset.range (N + 1)) (f := fun j z ↦ C * c j * G j z)
          (c := z) fun j _ ↦ analyticAt_const.mul (hG j z h0 h)
        convert this using 1
        funext w
        rw [Finset.sum_apply]),
    hQ0, mul_zero, zero_add, sLocalPrincipalPartCoeff_translate_sum _ _ _ hR hG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [c, G]
  ring

/-- Translating a test by a unit multiplies its zeta function by the value of the
quasi-character at the class of the unit. -/
theorem sLocalPrincipalPartCoeff_translate_zeta (u : Aₛˣ) (f : ℬₛ) (d : Xₛ) :
    sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f) d =
      d (QuotientGroup.mk u) * sLocalIdelicZFunction f d := by
  obtain ⟨χ, s, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) d
  let A : ℂ → ℂ := fun z ↦ (twistₛ ((circleToComplex).comp χ) z) (QuotientGroup.mk u)
  have hM : (((mₛ (QuotientGroup.mk u : Jₛ) : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have hA (z : ℂ) : AnalyticAt ℂ A z ∧ A z ≠ 0 := by
    have e : A = fun z ↦ ((χ (QuotientGroup.mk u) : Circle) : ℂ) *
        (((mₛ (QuotientGroup.mk u : Jₛ) : ℝ≥0) : ℝ) : ℂ) ^ z := rfl
    rw [e]
    refine ⟨analyticAt_const.mul ((differentiable_id.const_cpow (Or.inl hM)).analyticAt z),
      mul_ne_zero (Circle.coe_ne_zero _) ?_⟩
    rw [Complex.cpow_def_of_ne_zero hM]
    exact Complex.exp_ne_zero _
  have key := eq_of_agree_rightHalf
    (U := fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f)
      (twistₛ ((circleToComplex).comp χ) z))
    (V := fun z ↦ A z * sLocalIdelicZFunction f (twistₛ ((circleToComplex).comp χ) z))
    (sLocalIdelicZFunction_meromorphic _ χ)
    (fun z _ ↦ (meromorphicNFAt_mul_iff_right (hA z).1 (hA z).2).mpr
      (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ z))) 0 fun z hz ↦ ?_
  · exact congrFun key s
  · rw [sLocalIdelicZFunction_eq_integral _ ⟨χ, z, hz, rfl⟩,
      sLocalIdelicZFunction_eq_integral _ ⟨χ, z, hz, rfl⟩]
    letI : MeasurableSpace (SAdeleRing F S) := instMeasurableSpaceSAdeleRing F S
    let : BorelSpace (SAdeleRing F S)ˣ := sIdeleGroup_borelSpace
    let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
    unfold sLocalIdelicZetaIntegral
    rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_mul_left_eq_self (μ := sMultiplicativeTamagawaMeasure F S) _ u]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change f (Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing F S) * (u * x).val)) *
        (twistₛ ((circleToComplex).comp χ) z) (QuotientGroup.mk (u * x)) =
      A z * (f (Multiplicative.ofAdd x.val) *
        (twistₛ ((circleToComplex).comp χ) z) (QuotientGroup.mk x))
    rw [Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul, QuotientGroup.mk_mul, map_mul]
    simp only [A]
    ring

/-- Paper: Theorem 7.2.1.1(2), p. 334.
Translation acts on coefficients of nonpositive exponent by an upper triangular formula.
Deviation: Lower coefficients also receive terms from the higher polar coefficients.
The extra terms vanish on norm-one translations. -/
theorem sLocalPrincipalPartCoeff_translate (c : Xₛ) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (u : Aₛˣ) (f : ℬₛ) :
    let g : Jₛ := QuotientGroup.mk u
    let logNorm : ℂ := Real.log (((mₛ g : ℝ≥0) : ℝ))
    sLocalPrincipalPartCoeff c k (schwartzBruhatUnitTranslate u f) =
      c g * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c - k + 1),
        sLocalPrincipalPartCoeff c (k + j) f * logNorm ^ j / (j.factorial : ℂ) := by
  intro g logNorm
  have hZ := sLocalZ_centered f c
  have hord : ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 :=
    (sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans hZ.2.1
  have hM : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have hval (z : ℂ) : (twistₛ c z) g = c g * Complex.exp (logNorm * z) := by
    change c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ z = _
    rw [Complex.cpow_def_of_ne_zero hM, ← Complex.ofReal_log (NNReal.coe_nonneg _)]
  rw [sLocalPrincipalPartCoeff_apply]
  change complexResidue (fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f)
    (twistₛ c z) / z ^ (-(k : ℤ) + 1)) 0 = _
  have e : (fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f) (twistₛ c z) /
      z ^ (-(k : ℤ) + 1)) = fun z ↦ c g * (Complex.exp (logNorm * z) *
        sLocalIdelicZFunction f (twistₛ c z) / z ^ (-(k : ℤ) + 1)) := by
    funext z
    rw [sLocalPrincipalPartCoeff_translate_zeta, hval]
    ring
  rw [e, sLocalPrincipalPartCoeff_translate_laurent hZ.1 hk hord]
  rfl

-- TODO(paper-gap): The universal inequality in Theorem 7.2.1.1(3)
-- fails on the zero test whenever the functional is nonzero and k > 0.

/-- A function agreeing near `0`, off `0`, with a function analytic at `0` has residue zero. -/
private theorem sLocalPrincipalPartCoeff_ne_zero_imp_pole_residue {W H : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (he : W =ᶠ[𝓝[≠] (0 : ℂ)] H) : complexResidue W 0 = 0 := by
  have he' : W =ᶠ[𝓝[≠] (0 : ℂ)] (fun z ↦ (z * H z) / (z - 0)) := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, mul_div_cancel_left₀ _ hz0']
  have hcongr : complexResidue W 0 = complexResidue (fun z ↦ (z * H z) / (z - 0)) 0 := by
    obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he'
    unfold complexResidue limUnder
    refine congrArg lim (Filter.map_congr ?_)
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
    · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
      exact hr.2
    · rintro rfl
      exact hr.1.ne (by simpa using hz)
  rw [hcongr, complexResidue_div_sub (g := fun z ↦ z * H z) (analyticAt_id.mul hH), zero_mul]

/-- If the polar multiplicity is below `k`, the Laurent coefficient of exponent `-k` vanishes. -/
private theorem sLocalPrincipalPartCoeff_ne_zero_imp_pole_vanish {Z : ℂ → ℂ}
    (hZ : MeromorphicAt Z 0) (k : ℕ) (hk : 0 < k)
    (hlt : (-(meromorphicOrderAt Z 0).untop₀).toNat < k) :
    complexResidue (fun z ↦ Z z / z ^ (-(k : ℤ) + 1)) 0 = 0 := by
  cases ho : meromorphicOrderAt Z 0 with
  | top =>
    refine sLocalPrincipalPartCoeff_ne_zero_imp_pole_residue (H := fun _ ↦ 0) analyticAt_const ?_
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp ho] with z hz
    rw [hz, zero_div]
  | coe n =>
    rw [ho] at hlt
    simp only [WithTop.untop₀_coe] at hlt
    obtain ⟨g, hg, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hZ).mp ho
    have hn : 0 ≤ n + (k : ℤ) - 1 := by omega
    refine sLocalPrincipalPartCoeff_ne_zero_imp_pole_residue
      (H := fun z ↦ z ^ (n + (k : ℤ) - 1).toNat * g z) ((analyticAt_id.pow _).mul hg) ?_
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, ← zpow_natCast, Int.toNat_of_nonneg hn,
      show n + (k : ℤ) - 1 = n - (-(k : ℤ) + 1) by ring, zpow_sub₀ hz0']
    ring

/-- Paper: Theorem 7.2.1.1(3), p. 334.
A nonvanishing polar coefficient forces a pole of the test's zeta function of at
least the indicated order, at an allowed pole of the correcting factor.
Deviation: The inequality holds for the test on which the coefficient is nonzero,
and a polar coefficient has strictly negative Laurent exponent. -/
theorem sLocalPrincipalPartCoeff_ne_zero_imp_pole (c : Xₛ) (k : ℕ) (hk : 0 < k)
    (f : ℬₛ) (hf : sLocalPrincipalPartCoeff c k f ≠ 0) :
    0 < sLocalRhoPoleOrder c ∧ k ≤ sLocalPolarMultiplicity f c := by
  have count (m : ℕ) (o : WithTop ℤ) (ho : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
      (-o.untop₀).toNat ≤ m := by
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp ho
      simp only [WithTop.untop₀_coe]
      omega
  have hbound : sLocalPolarMultiplicity f c ≤ sLocalRhoPoleOrder c :=
    count _ _ ((sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans (sLocalZ_centered f c).2.1)
  have hkN : k ≤ sLocalPolarMultiplicity f c := by
    refine Nat.le_of_not_lt fun hlt ↦ hf ?_
    rw [sLocalPrincipalPartCoeff_apply]
    exact sLocalPrincipalPartCoeff_ne_zero_imp_pole_vanish (sLocalZ_centered f c).1 k hk hlt
  exact ⟨by omega, hkN⟩

/-- Paper: Equation (7.2.1.6), p. 334.
The subspace is spanned by homogeneous theta classes whose pole orders on the
chosen component satisfy the given bound.
Deviation: The bound is extended to all quasi-characters. Its values off the
allowed pole divisor do not affect the subspace. -/
def sLocalThetaPoleBound (ω : PontryaginDual J₁) (m : Xₛ → ℕ) : Submodule ℂ (Θₛ(ω)) :=
  Submodule.span ℂ {x | ∃ f : ℬₛ, (Kₛ(ω)).mkQ f = x ∧
    ∀ c : Xₛ, onComponent(c, ω) → sLocalPolarMultiplicity f c ≤ m c}

/-- Residues only depend on the germ on a punctured neighbourhood. -/
theorem mem_sLocalThetaPoleBound_iff_residue_congr {g h : ℂ → ℂ}
    (he : g =ᶠ[𝓝[≠] (0 : ℂ)] h) : complexResidue g 0 = complexResidue h 0 := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- The leading polar coefficient of a meromorphic germ with a pole of order `N` is nonzero. -/
theorem mem_sLocalThetaPoleBound_iff_leading {Z : ℂ → ℂ} (hZ : MeromorphicAt Z 0)
    {N : ℕ} (hN : 0 < N) (ho : (-(meromorphicOrderAt Z 0).untop₀).toNat = N) :
    complexResidue (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) 0 ≠ 0 := by
  have hord : meromorphicOrderAt Z 0 = ((-(N : ℤ) : ℤ) : WithTop ℤ) := by
    generalize meromorphicOrderAt Z 0 = o at ho ⊢
    induction o using WithTop.recTopCoe with
    | top => simp at ho; omega
    | coe n =>
      simp only [WithTop.untop₀_coe] at ho
      congr 1
      omega
  obtain ⟨g, hg, hg0, hev⟩ := (meromorphicOrderAt_eq_int_iff hZ).mp hord
  have he : (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z ↦ g z / (z - 0)) := by
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, zpow_add₀ hz0', zpow_one, zpow_neg, zpow_natCast]
    field_simp
  rw [mem_sLocalThetaPoleBound_iff_residue_congr he, complexResidue_div_sub hg]
  exact hg0

/-- Paper: Equation (7.2.1.9), p. 334.
Membership in the pole-bound subspace is equivalent to vanishing of every coefficient
on the component above its allowed pole order. -/
theorem mem_sLocalThetaPoleBound_iff (ω : PontryaginDual J₁) (m : Xₛ → ℕ) (x : Θₛ(ω)) :
    x ∈ sLocalThetaPoleBound ω m ↔
      ∀ (c : Xₛ) (hc : onComponent(c, ω)), 0 < sLocalRhoPoleOrder c →
        ∀ k : ℕ, m c < k → sLocalThetaPrincipalPartCoeff ω c hc k x = 0 := by
  constructor
  · intro hx c hc _ k hk
    have hle : sLocalThetaPoleBound ω m ≤ (sLocalThetaPrincipalPartCoeff ω c hc k).ker := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨f, rfl, hf⟩
      have e : sLocalThetaPrincipalPartCoeff ω c hc k ((Kₛ(ω)).mkQ f) =
          sLocalZLaurentCoeff f c (-(k : ℤ)) := sLocalThetaPrincipalPartCoeff_mk ω c hc k f
      have hz : sLocalZLaurentCoeff f c (-(k : ℤ)) = 0 := by
        by_contra hne
        have hne' : sLocalPrincipalPartCoeff c k f ≠ 0 := by
          exact fun h ↦ hne ((sLocalPrincipalPartCoeff_apply c k f).symm.trans h)
        have h := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k (by omega) f hne').2
        have := hf c hc
        omega
      exact e.trans hz
    exact hle hx
  · intro hx
    have count (m : ℕ) (o : WithTop ℤ) (ho : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
        (-o.untop₀).toNat ≤ m := by
      induction o using WithTop.recTopCoe with
      | top => simp
      | coe n =>
        have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp ho
        simp only [WithTop.untop₀_coe]
        omega
    refine ((Kₛ(ω)).mkQ_surjective x).elim fun f hf ↦ ?_
    refine Submodule.subset_span ⟨f, hf, fun c hc ↦ ?_⟩
    refine Nat.le_of_not_lt fun hlt ↦ ?_
    have hcount : sLocalPolarMultiplicity f c ≤ sLocalRhoPoleOrder c :=
      count _ _ ((sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans (sLocalZ_centered f c).2.1)
    have hmer : MeromorphicAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 :=
      (sLocalZ_centered f c).1
    have hpos : 0 < sLocalRhoPoleOrder c := by omega
    have h0 := hx c hc hpos (sLocalPolarMultiplicity f c) hlt
    rw [← hf] at h0
    have e : sLocalThetaPrincipalPartCoeff ω c hc (sLocalPolarMultiplicity f c) ((Kₛ(ω)).mkQ f) =
        sLocalZLaurentCoeff f c (-(sLocalPolarMultiplicity f c : ℤ)) :=
      sLocalThetaPrincipalPartCoeff_mk ω c hc (sLocalPolarMultiplicity f c) f
    have h1 := e.symm.trans h0
    have h2 : complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) /
        z ^ (-(sLocalPolarMultiplicity f c : ℤ) + 1)) 0 = 0 := h1
    exact mem_sLocalThetaPoleBound_iff_leading (N := sLocalPolarMultiplicity f c) hmer
      (by omega) rfl h2

/-- Paper: Theorem 7.2.1.1(4), p. 334.
The homogeneous theta classes with the prescribed bounds on pole order form a closed subspace. -/
theorem sLocalThetaPoleBound_isClosed (ω : PontryaginDual J₁) (m : Xₛ → ℕ) :
    IsClosed (sLocalThetaPoleBound ω m : Set (Θₛ(ω))) := by
  let I := {i : Xₛ × ℕ // onComponent(i.1, ω) ∧ 0 < sLocalRhoPoleOrder i.1 ∧ m i.1 < i.2}
  let T (i : I) : StrongDual ℂ (Θₛ(ω)) :=
    sLocalThetaPrincipalPartCoeff (F := F) (S := S) ω i.val.1 i.property.1 i.val.2
  let Z (i : I) : Set (Θₛ(ω)) := {x | T i x = 0}
  have h : (sLocalThetaPoleBound ω m : Set (Θₛ(ω))) = ⋂ i, Z i := by
    refine Set.ext fun x ↦ (mem_sLocalThetaPoleBound_iff (F := F) (S := S) ω m x).trans ?_
    refine Iff.trans ?_ (Set.mem_iInter (s := Z) (x := x)).symm
    exact ⟨fun hx i ↦ hx i.val.1 i.property.1 i.property.2.1 i.val.2 i.property.2.2,
      fun hx c hc hp k hk ↦ hx ⟨(c, k), hc, hp, hk⟩⟩
  exact (congrArg IsClosed h).mpr (isClosed_iInter fun i ↦ (T i).isClosed_ker)

/-- In a Hausdorff polynormable Montel space, the annihilator of the common kernel
of a family of functionals is their closed linear span in the strong dual. -/
theorem strongDual_annihilator_eq_closedSpan_of_kernels {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [T2Space E] [PolynormableSpace ℂ E] [MontelSpace ℂ E] (P : Submodule ℂ E)
    (A : Set (StrongDual ℂ E)) (hP : ∀ x : E, x ∈ P ↔ ∀ T ∈ A, T x = 0) :
    P.dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) = (Submodule.span ℂ A).topologicalClosure := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  apply le_antisymm
  · intro T hT
    change T.toLinearMap ∈ P.dualAnnihilator at hT
    by_contra hn
    obtain ⟨φ, hne, hz⟩ := exists_dual_eq_zero_on_submodule_of_notMem
      (Submodule.span ℂ A).topologicalClosure (Submodule.span ℂ A).isClosed_topologicalClosure hn
    obtain ⟨x, rfl⟩ := surjective_strongBidual_eval (E := E) φ
    have hx : x ∈ P := (hP x).2 fun t ht ↦
      hz t ((Submodule.span ℂ A).le_topologicalClosure (Submodule.subset_span ht))
    exact hne ((Submodule.mem_dualAnnihilator T.toLinearMap).mp hT x hx)
  · intro T hT
    change T.toLinearMap ∈ P.dualAnnihilator
    apply (Submodule.mem_dualAnnihilator _).2
    intro x hx
    let ev := ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ) x
    have hA : Submodule.span ℂ A ≤ ev.ker := Submodule.span_le.mpr fun t ht ↦ (hP x).1 hx t ht
    exact (Submodule.span ℂ A).topologicalClosure_minimal hA ev.isClosed_ker hT

/-- Paper: Theorem 7.2.1.1(4), p. 334.
The annihilator of the pole-bound subspace is the strong closure of the span of the
descended coefficients above the bound.
Deviation: Uses the indices in (7.2.1.7). Lower coefficients can fail the weight
equation, and spanning here means closed linear span in the strong dual. -/
theorem sLocalThetaPoleBound_annihilator (ω : PontryaginDual J₁) (m : Xₛ → ℕ) :
    (sLocalThetaPoleBound ω m).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ {T : StrongDual ℂ (Θₛ(ω)) |
        ∃ (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ),
          0 < sLocalRhoPoleOrder c ∧ m c < k ∧ sLocalThetaPrincipalPartCoeff ω c hc k = T
      }).topologicalClosure := by
  have hN : IsNuclearTVS.{0} (Θₛ(ω)) := sLocalHomogeneousThetaSpace_nuclear (F := F) (S := S) ω
  let : T2Space (Θₛ(ω)) := hN.1
  let : PolynormableSpace ℂ (Θₛ(ω)) := hN.2.1
  let : MontelSpace ℂ (Θₛ(ω)) := (sLocalHomogeneousThetaSpace_montel (F := F) (S := S) ω).2
  apply strongDual_annihilator_eq_closedSpan_of_kernels
  intro x
  rw [mem_sLocalThetaPoleBound_iff]
  constructor
  · rintro h T ⟨c, hc, k, hp, hk, rfl⟩
    exact h c hc hp k hk
  · intro h c hc hp k hk
    exact h _ ⟨c, hc, k, hp, hk, rfl⟩

local notation "archEuler(" w ", " c ")" =>
  (fun z : ℂ ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ c z)))
local notation "finEuler(" v ", " c ")" =>
  (fun z : ℂ ↦ finiteLocalEulerFactor (v).val (sLocalFiniteRestriction v (twistₛ c z)))

-- TODO(paper-gap): The coordinate homomorphism into Jₛ can have a kernel.
-- For ℚ with only the real place it kills -1. Restriction uses the
-- homomorphisms of §3.3 without an injectivity condition.

open Classical in
/-- Paper: Equation (7.2.1.11), p. 335.
The archimedean places contributing a pole at a given character are those whose
restricted local Euler factors have a pole in the norm coordinate. -/
def sLocalArchPolePlaces (c : Xₛ) : Finset (InfinitePlace F) :=
  Finset.univ.filter (fun w ↦ meromorphicOrderAt (archEuler(w, c)) 0 < 0)

open Classical in
/-- Paper: Equation (7.2.1.11), p. 335.
The finite places contributing a pole at a given character are those whose
restricted local Euler factors have a pole in the norm coordinate. -/
def sLocalFinitePolePlaces (c : Xₛ) : Finset S :=
  Finset.univ.filter (fun v : S ↦ meromorphicOrderAt (finEuler(v, c)) 0 < 0)

/-- The norm twist of the trivial quasi-character is the chart of the trivial unitary character. -/
private theorem sLocalPolePlaces_one_twist_eq (z : ℂ) :
    twistₛ (1 : Xₛ) z = quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
      ((circleToComplex).comp (1 : PontryaginDual Jₛ)) z := by
  congr 1

/-- At a real place the twisted trivial character has Euler factor `Γℝ`. -/
private theorem sLocalPolePlaces_one_arch_real (w : InfinitePlace F) (hw : w.IsReal) (z : ℂ) :
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)) =
      Complex.Gammaℝ z := by
  have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z) g =
      (((((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
        (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
    rw [sLocalPolePlaces_one_twist_eq]
    exact sLocalInfiniteRestriction_normTwist w z g
  have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) =
      (‖(x : ℝ)‖ : ℂ) ^ (z : ℂ) *
        (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ ((0 : Fin 2) : Fin 2).val := by
    intro x
    have hn : ‖((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (x : ℝ) :
        w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) (x : ℝ)
    rw [hval]
    simp [InfinitePlace.mult, hw, hn]
  have h := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z))).unique
    (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (z, 0)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, h, Fin.val_zero,
    Nat.cast_zero, add_zero]

/-- At a complex place the twisted trivial character has Euler factor `Γℂ / 2`. -/
private theorem sLocalPolePlaces_one_arch_complex (w : InfinitePlace F) (hw : ¬ w.IsReal)
    (z : ℂ) :
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)) =
      Complex.Gammaℂ z / 2 := by
  have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z) g =
      (((((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
        (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
    rw [sLocalPolePlaces_one_twist_eq]
    exact sLocalInfiniteRestriction_normTwist w z g
  have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
  have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toMonoidHom x) =
      ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z : ℂ) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ ((0 : ℤ) : ℤ) := by
    intro x
    have hn : ‖((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (x : ℂ) :
        w.Completion)‖ = ‖(x : ℂ)‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm) (x : ℂ)
    rw [hval]
    simp [InfinitePlace.mult, hw, hn]
  have h := (complexLocalEulerParameters w hc (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z))).unique
    (complexLocalEulerParameters w hc _).exists.choose_spec (y₂ := (z, 0)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, h, Int.natAbs_zero,
    Nat.cast_zero, zero_div, add_zero]

/-- The twisted trivial character restricts at a finite place to a power of the norm. -/
private theorem sLocalPolePlaces_one_fin_val (v : S) (z : ℂ) (g : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z) g = ((‖g.val‖ : ℝ) : ℂ) ^ z := by
  obtain ⟨y, hy⟩ : ∃ y : Jₛ, ∀ c : Xₛ, sLocalFiniteRestriction v c g = c y := ⟨_, fun c ↦ rfl⟩
  have h1 := sLocalFiniteRestriction_norm v g
  rw [hy] at h1
  rw [hy, sLocalPolePlaces_one_twist_eq]
  change (((1 : PontryaginDual Jₛ) y : Circle) : ℂ) * ((((mₛ y : ℝ≥0) : ℝ) : ℂ)) ^ z = _
  change (((1 : PontryaginDual Jₛ) y : Circle) : ℂ) * ((((mₛ y : ℝ≥0) : ℝ) : ℂ)) ^ (1 : ℂ) = _
    at h1
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul] at h1 ⊢
  rw [Complex.cpow_one] at h1
  rw [h1]
  rfl

/-- At a finite place the twisted trivial character has Euler factor `(1 - q ^ (-z))⁻¹`. -/
private theorem sLocalPolePlaces_one_fin (v : S) (z : ℂ) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z)) =
      (1 - ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹ := by
  have hunr : ∀ u : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
      sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom u) =
        1 := by
    intro u
    rw [sLocalPolePlaces_one_fin_val]
    have hu : ‖(Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom
        u : (v.val.adicCompletion F)ˣ).val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow]
  unfold finiteLocalEulerFactor
  rw [ite_eq_left hunr]
  dsimp only
  have harg : (((Ideal.absNorm v.val.asIdeal : ℕ) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  rw [sLocalPolePlaces_one_fin_val, Units.val_mk0, norm_uniformizer_adicCompletion v.val _
    (Valued.v : Valuation (v.val.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]

/-- The reciprocal of an analytic function vanishing at `0`, but not on the positive reals,
has a pole at `0`. -/
private theorem sLocalPolePlaces_one_order (f h : ℂ → ℂ) (hf : ∀ z, f z = (h z)⁻¹)
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 0) (hpos : ∀ x : ℝ, 0 < x → h x ≠ 0) :
    meromorphicOrderAt f 0 < 0 := by
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), h z = 0 := by
    intro hev
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine hpos (ε / 2) (by linarith) (hball ?_)
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  rw [show f = fun z ↦ (h z)⁻¹ from funext hf,
    show meromorphicOrderAt (fun z ↦ (h z)⁻¹) 0 = -meromorphicOrderAt h 0 from
      meromorphicOrderAt_inv, hh.meromorphicOrderAt_eq]
  have h1 : analyticOrderAt h 0 ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    simp [hh, h0]
  have h2 : analyticOrderAt h 0 ≠ ⊤ := by rwa [Ne, analyticOrderAt_eq_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h2
  rw [← hn] at h1 ⊢
  have : (0 : ℕ) < n := Nat.pos_of_ne_zero (by exact_mod_cast h1)
  simp only [ENat.map_natCast]
  exact_mod_cast (by omega : -(n : ℤ) < 0)

/-- Every archimedean Euler factor of the twisted trivial character has a pole at `0`. -/
private theorem sLocalPolePlaces_one_arch (w : InfinitePlace F) :
    meromorphicOrderAt (fun z : ℂ ↦
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z))) 0 < 0 := by
  by_cases hw : w.IsReal
  · refine sLocalPolePlaces_one_order _ (fun z ↦ (Complex.Gammaℝ z)⁻¹)
      (fun z ↦ by rw [sLocalPolePlaces_one_arch_real w hw z, inv_inv])
      (Complex.differentiable_Gammaℝ_inv.analyticAt 0) (by simp [Complex.Gammaℝ])
      fun x hx ↦ inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hx))
  · refine sLocalPolePlaces_one_order _ (fun z ↦ 2 * (Complex.Gammaℂ z)⁻¹)
      (fun z ↦ by rw [sLocalPolePlaces_one_arch_complex w hw z, mul_inv, inv_inv]; ring)
      (analyticAt_const.mul (Complex.differentiable_Gammaℂ_inv.analyticAt 0))
      (by simp [Complex.Gammaℂ]) fun x hx ↦ ?_
    have hr : 0 < (x : ℂ).re := by simpa using hx
    rw [Complex.Gammaℂ]
    exact mul_ne_zero two_ne_zero (inv_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (by simp [Real.pi_ne_zero])) (Complex.Gamma_ne_zero_of_re_pos hr)))

/-- Every finite Euler factor of the twisted trivial character has a pole at `0`. -/
private theorem sLocalPolePlaces_one_finite (v : S) :
    meromorphicOrderAt (fun z : ℂ ↦
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z))) 0 < 0 := by
  have hq : 1 < Ideal.absNorm v.val.asIdeal := by
    have h1 : Ideal.absNorm v.val.asIdeal ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr v.val.isPrime.ne_top
    have h0 : Ideal.absNorm v.val.asIdeal ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr v.val.ne_bot
    omega
  have hq' : (1 : ℝ) < (Ideal.absNorm v.val.asIdeal : ℝ) := by exact_mod_cast hq
  have hq0 : ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega)
  refine sLocalPolePlaces_one_order _
    (fun z ↦ 1 - Complex.exp (Complex.log ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) * (-z)))
    (fun z ↦ by rw [sLocalPolePlaces_one_fin v z, Complex.cpow_def_of_ne_zero hq0])
    ((by fun_prop : Differentiable ℂ fun z : ℂ ↦
      1 - Complex.exp (Complex.log ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) * (-z))).analyticAt 0)
    (by simp) fun x hx ↦ ?_
  rw [← Complex.cpow_def_of_ne_zero hq0]
  rw [sub_ne_zero, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow (by positivity)]
  intro h
  have h' : (Ideal.absNorm v.val.asIdeal : ℝ) ^ (-x) = 1 := by exact_mod_cast h.symm
  have := Real.rpow_lt_one_of_one_lt_of_neg hq' (by linarith : -x < 0)
  linarith

/-- Paper: Equation (7.2.1.11), p. 335.
At the trivial quasi-character every archimedean and every selected finite place
contributes a pole. -/
theorem sLocalPolePlaces_one :
    sLocalArchPolePlaces (1 : Xₛ) = Finset.univ ∧
      sLocalFinitePolePlaces (1 : Xₛ) = Finset.univ :=
  ⟨Finset.filter_true_of_mem fun w _ ↦ sLocalPolePlaces_one_arch w,
    Finset.filter_true_of_mem fun v _ ↦ sLocalPolePlaces_one_finite v⟩

/-- The reciprocal of an entire function that is not identically zero has a pole exactly at
the zeros of the function. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_inv {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {y : ℂ} (hy : G y ≠ 0) (s : ℂ) :
    meromorphicOrderAt (fun z ↦ (G z)⁻¹) s < 0 ↔ G s = 0 := by
  have hA : AnalyticAt ℂ G s := hG.analyticAt s
  change meromorphicOrderAt G⁻¹ s < 0 ↔ _
  rw [meromorphicOrderAt_inv, hA.meromorphicOrderAt_eq]
  have htop : analyticOrderAt G s ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    exact hy (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ ↦ hG.analyticAt z) isPreconnected_univ (Set.mem_univ s) h (Set.mem_univ y))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have h0 : G s = 0 ↔ n ≠ 0 := by
    have e : analyticOrderAt G s = 0 ↔ n = 0 := by
      rw [← hn]
      exact_mod_cast Iff.rfl
    rw [Ne, ← e, analyticOrderAt_eq_zero]
    simp [hA]
  rw [h0, ← hn]
  simp only [ENat.map_natCast]
  constructor
  · intro h hn0
    subst hn0
    simp at h
  · intro h
    have : 0 < n := Nat.pos_of_ne_zero h
    exact_mod_cast (by omega : -(n : ℤ) < 0)

/-- At a real place the restricted Euler factor has a pole exactly where the restricted Tate
factor has one. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_real (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsReal) (s : ℂ) :
    meromorphicOrderAt (archEuler(w, (circleToComplex).comp χ)) s < 0 ↔
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w
        (sLocalInfiniteRestriction w (twistₛ ((circleToComplex).comp χ) z))) s < 0 := by
  rw [(sLocalRhoFactor_poles_iff_real χ w hw s).2.1]
  obtain ⟨η, ha, -⟩ := sLocalInfinite_charts χ w
  obtain ⟨t, a, -, hbase⟩ := realPlaceUnitary_shape w hw η
  have hsh := realChart_shape w hw η t a hbase
  have hp (z : ℂ) : (realLocalEulerParameters w hw (sLocalInfiniteRestriction w
      (twistₛ ((circleToComplex).comp χ) z))).exists.choose = (z + t, a) := by
    have h0 := hsh z
    rw [← ha z] at h0
    exact (realLocalEulerParameters w hw _).unique
      (realLocalEulerParameters w hw _).exists.choose_spec h0
  have hE : archEuler(w, (circleToComplex).comp χ) =
      fun z ↦ ((Complex.Gammaℝ (z + t + (a.val : ℂ)))⁻¹)⁻¹ := by
    funext z
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, inv_inv]
  have hG : Differentiable ℂ (fun z ↦ (Complex.Gammaℝ (z + t + (a.val : ℂ)))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (by fun_prop)
  have hy : (Complex.Gammaℝ ((1 - t) + t + (a.val : ℂ)))⁻¹ ≠ 0 := by
    refine inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
    simp only [sub_add_cancel, Complex.add_re, Complex.one_re, Complex.natCast_re]
    positivity
  rw [hE, sLocalRhoPoleOrder_eq_card_polePlaces_inv hG hy s, inv_eq_zero,
    Complex.Gammaℝ_eq_zero_iff, hp 0]
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩ <;> push_cast at hn ⊢ <;> linear_combination hn

/-- The complex Gamma factor vanishes exactly at the nonpositive integers. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_Gammaℂ (x : ℂ) :
    Complex.Gammaℂ x = 0 ↔ ∃ m : ℕ, x = -(m : ℂ) := by
  rw [Complex.Gammaℂ_def, mul_eq_zero, mul_eq_zero, Complex.cpow_eq_zero_iff,
    ← Complex.Gamma_eq_zero_iff]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp [h2, hpi]

/-- At a complex place the restricted Euler factor has a pole exactly where the restricted Tate
factor has one. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_complex (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsComplex) (s : ℂ) :
    meromorphicOrderAt (archEuler(w, (circleToComplex).comp χ)) s < 0 ↔
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w
        (sLocalInfiniteRestriction w (twistₛ ((circleToComplex).comp χ) z))) s < 0 := by
  rw [(sLocalRhoFactor_poles_iff_complex χ w hw s).2.1]
  obtain ⟨η, ha, -⟩ := sLocalInfinite_charts χ w
  obtain ⟨t, r, -, hbase⟩ := complexPlaceUnitary_shape w hw η
  have hsh := complexChart_shape w hw η t r hbase
  have hp (z : ℂ) : (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w
      (twistₛ ((circleToComplex).comp χ) z))).exists.choose = (z + t, r) := by
    have h0 := hsh z
    rw [← ha z] at h0
    exact (complexLocalEulerParameters w hw _).unique
      (complexLocalEulerParameters w hw _).exists.choose_spec h0
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
  have hE : archEuler(w, (circleToComplex).comp χ) =
      fun z ↦ (2 * (Complex.Gammaℂ (z + t + (r.natAbs : ℂ) / 2))⁻¹)⁻¹ := by
    funext z
    simp only [infiniteLocalEulerFactor, hnr, ↓reduceDIte, hp, mul_inv, inv_inv]
    ring
  have hG : Differentiable ℂ (fun z ↦ 2 * (Complex.Gammaℂ (z + t + (r.natAbs : ℂ) / 2))⁻¹) :=
    (differentiable_const _).mul (Complex.differentiable_Gammaℂ_inv.comp (by fun_prop))
  have hy : 2 * (Complex.Gammaℂ ((1 - t - (r.natAbs : ℂ) / 2) + t + (r.natAbs : ℂ) / 2))⁻¹ ≠ 0 := by
    refine mul_ne_zero two_ne_zero (inv_ne_zero ?_)
    rw [Ne, sLocalRhoPoleOrder_eq_card_polePlaces_Gammaℂ]
    rintro ⟨m, hm⟩
    rw [show 1 - t - (r.natAbs : ℂ) / 2 + t + (r.natAbs : ℂ) / 2 = 1 by ring] at hm
    have h := congrArg Complex.re hm
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at h
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [hE, sLocalRhoPoleOrder_eq_card_polePlaces_inv hG hy s, mul_eq_zero, inv_eq_zero,
    or_iff_right two_ne_zero, sLocalRhoPoleOrder_eq_card_polePlaces_Gammaℂ, hp 0]
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩ <;> push_cast at hn ⊢ <;> linear_combination hn

/-- On a unitary chart, the restriction at a finite place is the restriction at the center
times the corresponding power of the local norm. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_fin_val (χ : PontryaginDual Jₛ) (v : S)
    (z : ℂ) (x : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z) x =
      sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) 0) x *
        ((‖x.val‖ : ℝ) : ℂ) ^ z := by
  have h1 := sLocalPolePlaces_one_fin_val v z x
  obtain ⟨y, hy⟩ : ∃ y : Jₛ, ∀ c : Xₛ, sLocalFiniteRestriction v c x = c y := ⟨_, fun c ↦ rfl⟩
  rw [← h1, hy, hy, hy]
  change ((χ y : Circle) : ℂ) * (((mₛ y : ℝ≥0) : ℝ) : ℂ) ^ z =
    (((χ y : Circle) : ℂ) * (((mₛ y : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)) *
      (((1 : PontryaginDual Jₛ) y : Circle) * (((mₛ y : ℝ≥0) : ℝ) : ℂ) ^ z)
  rw [Complex.cpow_zero, mul_one, PontryaginDual.one_apply, Circle.coe_one, one_mul]

/-- At a finite place the restricted Euler factor has a pole exactly where the restricted Tate
factor has one. -/
theorem sLocalRhoPoleOrder_eq_card_polePlaces_finite (χ : PontryaginDual Jₛ) (v : S)
    (s : ℂ) :
    meromorphicOrderAt (finEuler(v, (circleToComplex).comp χ)) s < 0 ↔
      meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val
        (sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z))) s < 0 := by
  obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
  rw [(h s).2.1]
  let ψ := sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) 0)
  have hψ1 (x : (v.val.adicCompletion F)ˣ) : ‖ψ x‖ = 1 := by
    change ‖((χ _ : Circle) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  let hπ₀ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π₀ : (v.val.adicCompletion F)ˣ := Units.mk0 hπ₀.choose hπ₀.choose_spec.ne_zero
  have hπ₀n : ‖π₀.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v.val _ hπ₀.choose_spec
  rw [(sLocalRhoFactor_poles_iff_finite_explicit v.val ψ hψ1 π hπ s).trans
    (sLocalRhoFactor_poles_iff_finite_explicit v.val ψ hψ1 π₀ hπ₀n s).symm]
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  by_cases hu : ∀ u : (v.val.adicCompletionIntegers F)ˣ,
      ψ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1
  · have hunr (z : ℂ) : ∀ u : (v.val.adicCompletionIntegers F)ˣ,
        sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z)
          (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 := by
      intro u
      have hn : ‖(Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
          u : (v.val.adicCompletion F)ˣ).val‖ = 1 :=
        Valued.toNormedField.norm_eq_one_iff.mpr
          ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
            (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
            ⟨u.val.property, u.inv.property⟩)
      rw [sLocalRhoPoleOrder_eq_card_polePlaces_fin_val χ v z, hn, Complex.ofReal_one,
        Complex.one_cpow, mul_one]
      exact hu u
    let G : ℂ → ℂ := fun z ↦ 1 - ψ π₀ * ((‖π₀.val‖ : ℝ) : ℂ) ^ z
    have hE : finEuler(v, (circleToComplex).comp χ) = fun z ↦ (G z)⁻¹ := by
      funext z
      unfold finiteLocalEulerFactor
      rw [if_pos (hunr z)]
      show (1 - sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z) π₀)⁻¹ = (G z)⁻¹
      rw [sLocalRhoPoleOrder_eq_card_polePlaces_fin_val χ v z π₀]
    have hnorm0 : ((‖π₀.val‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π₀.ne_zero)
    have hG : Differentiable ℂ G :=
      (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_id.const_cpow (Or.inl hnorm0)))
    have hy : G 1 ≠ 0 := by
      intro h0
      have h1 : ψ π₀ * ((‖π₀.val‖ : ℝ) : ℂ) = 1 := by
        have := sub_eq_zero.mp h0
        rw [Complex.cpow_one] at this
        exact this.symm
      have h2 := congrArg norm h1
      rw [norm_mul, hψ1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, hπ₀n,
        norm_one] at h2
      have : (v.val.asIdeal.absNorm : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
      linarith
    rw [hE, sLocalRhoPoleOrder_eq_card_polePlaces_inv hG hy s, and_iff_right hu]
    exact sub_eq_zero.trans eq_comm
  · have hE : finEuler(v, (circleToComplex).comp χ) = fun _ ↦ 1 := by
      funext z
      unfold finiteLocalEulerFactor
      refine if_neg fun hz ↦ hu fun u ↦ ?_
      have hn : ‖(Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
          u : (v.val.adicCompletion F)ˣ).val‖ = 1 :=
        Valued.toNormedField.norm_eq_one_iff.mpr
          ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
            (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
            ⟨u.val.property, u.inv.property⟩)
      have := hz u
      rwa [sLocalRhoPoleOrder_eq_card_polePlaces_fin_val χ v z, hn, Complex.ofReal_one,
        Complex.one_cpow, mul_one] at this
    rw [hE, iff_false_intro (not_lt.mpr analyticAt_const.meromorphicOrderAt_nonneg),
      false_iff, not_and]
    exact fun h ↦ absurd h hu

/-- Paper: Theorem 7.2.1.4, p. 336.
The allowed pole multiplicity at a character counts the contributing places,
each of which contributes a simple pole. -/
theorem sLocalRhoPoleOrder_eq_card_polePlaces (c : Xₛ) :
    sLocalRhoPoleOrder c = (sLocalArchPolePlaces c).card + (sLocalFinitePolePlaces c).card := by
  classical
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have H := sLocalRhoFactor_poles_iff_count χ a
  dsimp only at H
  have harch : sLocalArchPolePlaces (twistₛ ((circleToComplex).comp χ) a) =
      Finset.univ.filter (fun w : InfinitePlace F ↦ meromorphicOrderAt (fun z ↦
        infiniteLocalTateFactor w (sLocalInfiniteRestriction w
          (twistₛ ((circleToComplex).comp χ) z))) a < 0) := by
    unfold sLocalArchPolePlaces
    refine Finset.filter_congr fun w _ ↦ ?_
    have e : archEuler(w, twistₛ ((circleToComplex).comp χ) a) =
        archEuler(w, (circleToComplex).comp χ) ∘ (· + a) := by
      funext z
      simp only [Function.comp_apply, normTwist_normTwist]
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
    by_cases hw : w.IsReal
    · exact sLocalRhoPoleOrder_eq_card_polePlaces_real χ w hw a
    · exact sLocalRhoPoleOrder_eq_card_polePlaces_complex χ w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw) a
  have hfin : sLocalFinitePolePlaces (twistₛ ((circleToComplex).comp χ) a) =
      Finset.univ.filter (fun v : S ↦ meromorphicOrderAt (fun z ↦
        finiteLocalTateFactor v.val (sLocalFiniteRestriction v
          (twistₛ ((circleToComplex).comp χ) z))) a < 0) := by
    unfold sLocalFinitePolePlaces
    refine Finset.filter_congr fun v _ ↦ ?_
    have e : finEuler(v, twistₛ ((circleToComplex).comp χ) a) =
        finEuler(v, (circleToComplex).comp χ) ∘ (· + a) := by
      funext z
      simp only [Function.comp_apply, normTwist_normTwist]
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
    exact sLocalRhoPoleOrder_eq_card_polePlaces_finite χ v a
  unfold sLocalRhoPoleOrder
  rw [harch, hfin, sLocalOrderBound_chart]
  generalize hN : (Finset.univ.filter (fun w : InfinitePlace F ↦ meromorphicOrderAt (fun z ↦
        infiniteLocalTateFactor w (sLocalInfiniteRestriction w
          (twistₛ ((circleToComplex).comp χ) z))) a < 0)).card +
      (Finset.univ.filter (fun v : S ↦ meromorphicOrderAt (fun z ↦
        finiteLocalTateFactor v.val (sLocalFiniteRestriction v
          (twistₛ ((circleToComplex).comp χ) z))) a < 0)).card = N at H ⊢
  have hmin : min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor
      (twistₛ ((circleToComplex).comp χ) z)) a) = ((-(N : ℤ) : ℤ) : WithTop ℤ) := by
    by_cases hre : a.re ≤ 0
    · rw [H.2.1 hre]
      exact min_eq_right (by exact_mod_cast (by omega : -(N : ℤ) ≤ 0))
    · have hN0 : N = 0 := by
        by_contra hN0
        exact hre (H.1 (Or.inr (Nat.pos_of_ne_zero hN0)))
      have hρ : ¬ meromorphicOrderAt (fun z ↦ sLocalRhoFactor
          (twistₛ ((circleToComplex).comp χ) z)) a < 0 := fun h ↦ hre (H.1 (Or.inl h))
      rw [hN0, min_eq_left (not_lt.mp hρ)]
      rfl
  rw [hmin, WithTop.untop₀_coe]
  omega

open Classical in
/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The multiplicity counts poles contributed by the selected finite places. The
selected pole locus consists of the points of positive multiplicity.
Deviation: Extends the multiplicity by zero outside the selected pole locus. -/
def sLocalFinitePoleMultiplicity (S₀ : Finset Places) (c : Xₛ) : ℕ :=
  ((sLocalFinitePolePlaces c).filter (fun v ↦ v.val ∈ S₀)).card

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The selected divisor at the trivial character has multiplicity equal to the number
of selected finite places. -/
theorem sLocalFinitePoleMultiplicity_one (S₀ : Finset Places) (h₀ : S₀ ⊆ S) :
    sLocalFinitePoleMultiplicity S₀ (1 : Xₛ) = S₀.card := by
  classical
  unfold sLocalFinitePoleMultiplicity
  rw [(sLocalPolePlaces_one (F := F) (S := S)).2]
  apply Finset.card_bij (fun v _ ↦ v.val)
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro v hv
    exact ⟨⟨v, h₀ hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

open Classical in
/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The selected divisor counts the contributing places from both the archimedean and the
finite selections. The multiplicity is zero off the selected pole locus. -/
def sLocalSelectedPoleMultiplicity (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places)
    (c : Xₛ) : ℕ :=
  (sLocalArchPolePlaces c ∩ SArch).card + sLocalFinitePoleMultiplicity S₀ c

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
Selecting just the finite places gives the multiplicity used for principal values. -/
theorem sLocalSelectedPoleMultiplicity_finite (S₀ : Finset Places) (c : Xₛ) :
    sLocalSelectedPoleMultiplicity ∅ S₀ c = sLocalFinitePoleMultiplicity S₀ c := by
  classical
  rw [sLocalSelectedPoleMultiplicity, Finset.inter_empty, Finset.card_empty, zero_add]

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
Selecting every place recovers the full pole order. -/
theorem sLocalSelectedPoleMultiplicity_full (c : Xₛ) :
    sLocalSelectedPoleMultiplicity Finset.univ S c = sLocalRhoPoleOrder c := by
  classical
  simp [sLocalSelectedPoleMultiplicity, sLocalFinitePoleMultiplicity,
    sLocalRhoPoleOrder_eq_card_polePlaces]

-- TODO(paper-gap): For D = U_S and E = U_{S₀}, the sheaf target in Remark 7.2.1.2
-- is O(D)/O(D-E), with stalk length mult(E), whereas the printed P_{X,D-E} has
-- stalk length mult(D-E). The Mellin image imposes strip decay. We use the
-- coefficient map on that image, with the highest coefficients on one component.
-- Already for ℚ and S = {∞, p}, residues along the nonzero points of the p-lattice
-- decay rapidly. A constant nonzero residue sequence is outside the attained range.

local notation "remainingBound(" SArch ", " S₀ ")" =>
  (fun c : Xₛ ↦ sLocalRhoPoleOrder c - sLocalSelectedPoleMultiplicity SArch S₀ c)

local notation "removedIndices(" ω ", " SArch ", " S₀ ")" =>
  {i : Xₛ × ℕ // onComponent(i.1, ω) ∧
    remainingBound(SArch, S₀) i.1 < i.2 ∧ i.2 ≤ sLocalRhoPoleOrder i.1}

/-- Paper: Remark 7.2.1.2, p. 335.
On the chosen component, collect the coefficients removed when the pole bound
is lowered by the multiplicity of the selected divisor.
Deviation: At multiplicities `m` and `n`, the index runs over `m - n < k ≤ m`. -/
def sLocalThetaRemovedPrincipalParts (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    Θₛ(ω) →ₗ[ℂ] (removedIndices(ω, SArch, S₀) → ℂ) :=
  LinearMap.pi fun i ↦ (sLocalThetaPrincipalPartCoeff ω i.val.1 i.property.1 i.val.2).toLinearMap

/-- Paper: Remark 7.2.1.2, p. 335.
On a theta representative the removed principal parts evaluate to the corresponding
Laurent coefficients. -/
theorem sLocalThetaRemovedPrincipalParts_mk (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) (f : ℬₛ)
    (i : removedIndices(ω, SArch, S₀)) :
    sLocalThetaRemovedPrincipalParts ω SArch S₀ ((Kₛ(ω)).mkQ f) i =
      sLocalZLaurentCoeff f i.val.1 (-(i.val.2 : ℤ)) :=
  sLocalThetaPrincipalPartCoeff_mk ω i.val.1 i.property.1 i.val.2 f

/-- Paper: Remark 7.2.1.2, p. 335.
On the Mellin image, the classes with the remaining pole bound are exactly the
kernel of the removed-coefficient map.
Deviation: The remaining bound is `m_S - m_{S₀}`. -/
theorem sLocalThetaRemovedPrincipalParts_ker (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    (sLocalThetaRemovedPrincipalParts ω SArch S₀).ker =
      sLocalThetaPoleBound ω remainingBound(SArch, S₀) := by
  have count (m : ℕ) (o : WithTop ℤ) (ho : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
      (-o.untop₀).toNat ≤ m := by
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp ho
      simp only [WithTop.untop₀_coe]
      omega
  have bound (f : ℬₛ) (c : Xₛ) : sLocalPolarMultiplicity f c ≤ sLocalRhoPoleOrder c :=
    count _ _ ((sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans (sLocalZ_centered f c).2.1)
  let ord (c : Xₛ) := sLocalRhoPoleOrder c
  have full (x : Θₛ(ω)) : x ∈ sLocalThetaPoleBound ω ord := by
    refine ((Kₛ(ω)).mkQ_surjective x).elim fun f hf ↦ ?_
    exact Submodule.subset_span ⟨f, hf, fun c _ ↦ bound f c⟩
  let A := sLocalThetaRemovedPrincipalParts (F := F) (S := S) ω SArch S₀
  let m := remainingBound(SArch, S₀)
  refine Submodule.ext fun x ↦ Iff.trans ?_ (mem_sLocalThetaPoleBound_iff (F := F) (S := S) ω m x).symm
  constructor
  · intro hx c hc hp k hk
    by_cases hle : k ≤ sLocalRhoPoleOrder c
    · have hA : A x = 0 := hx
      exact congrFun hA ⟨(c, k), hc, hk, hle⟩
    · exact (mem_sLocalThetaPoleBound_iff (F := F) (S := S) ω ord x).mp (full x)
        c hc hp k (Nat.lt_of_not_ge hle)
  · intro hx
    change A x = 0
    funext i
    exact hx i.val.1 i.property.1 ((Nat.zero_lt_of_lt i.property.2.1).trans_le i.property.2.2)
      i.val.2 i.property.2.1

/-- A coefficient map identifies the quotient by its kernel with the attained values. -/
private theorem sLocalThetaRemovedPrincipalParts_quotient_of_ker {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (A : V →ₗ[ℂ] W)
    (H : Submodule ℂ V) (h : A.ker = H) :
    ∃ e : (V ⧸ H) ≃ₗ[ℂ] A.range, ∀ x, (e (H.mkQ x)).val = A x := by
  subst H
  exact ⟨A.quotKerEquivRange, fun x ↦ A.quotKerEquivRange_apply_mk x⟩

/-- Paper: Remark 7.2.1.2, p. 335.
The quotient by the remaining pole bound is identified by the coefficient map
with the principal parts attained on the chosen Mellin component.
Deviation: The surjective target is the range of the coefficient map. -/
theorem sLocalThetaRemovedPrincipalParts_quotient (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    let H := sLocalThetaPoleBound ω remainingBound(SArch, S₀)
    let A := sLocalThetaRemovedPrincipalParts ω SArch S₀
    ∃ e : (Θₛ(ω) ⧸ H) ≃ₗ[ℂ] A.range, ∀ x : Θₛ(ω), (e (H.mkQ x)).val = A x := by
  intro H A
  have h := sLocalThetaRemovedPrincipalParts_ker (F := F) (S := S) ω SArch S₀
  let I := removedIndices(ω, SArch, S₀)
  with_reducible
    exact sLocalThetaRemovedPrincipalParts_quotient_of_ker (V := Θₛ(ω)) (W := I → ℂ) A H h

-- TODO(paper-gap): In Remark 7.2.1.3 the full bound H_{m_S} permits all poles.
-- The image of S₀₀ has no poles and corresponds to H with bound zero.
-- TODO(later): needs §7.3.1 for the claimed application of Theorem 7.3.1.2.
-- Theorem 7.3.1.2 includes the archimedean places in S₀, whereas §5.3.1
-- supplies principal values at finite places.

private theorem sLocalThetaPoleBound_zero_chart (ω : PontryaginDual J₁) :
    ∃ χ : PontryaginDual Jₛ,
      (∀ z : ℂ, onComponent(twistₛ ((circleToComplex).comp χ) z, ω)) ∧
      ∀ d : Xₛ, onComponent(d, ω) → ∃ z : ℂ, twistₛ ((circleToComplex).comp χ) z = d := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, hu, ht⟩ := exists_character_on_split mₛ hmₛ σ hσ ω 1
  refine ⟨χ, fun z ↦ ContinuousMonoidHom.ext fun u ↦
    (normOneRestriction_unitaryChart mₛ hmₛ χ z u).trans (congrArg Subtype.val (hu u)), ?_⟩
  intro d hd
  obtain ⟨z, hz, -⟩ := existsUnique_complexPower (d.comp σ)
  refine ⟨z, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  let t := mₛ g
  let k : J₁ := ⟨g / σ t, by change mₛ (g / σ t) = 1; rw [map_div, hσ]; exact div_self' _⟩
  have hg : k.val * σ t = g := div_mul_cancel _ _
  have hχg : χ g = ω k := by
    calc χ g = χ k.val * χ (σ t) := (congrArg χ hg.symm).trans (map_mul χ _ _)
         _ = ω k := by rw [hu, ht]; exact mul_one _
  have hdk : d k.val = (ω k : ℂ) := DFunLike.congr_fun hd k
  have hdt : d (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ z := hz t
  change (χ g : ℂ) * (((t : ℝ≥0) : ℝ) : ℂ) ^ z = d g
  rw [hχg, ← hdk, ← hdt, ← map_mul, hg]

/-- Paper: Remark 7.2.1.3, p. 335.
The theta image of the coordinatewise polar-free tests is the subspace with
entire Mellin transform.
Deviation: The bound is zero. This is the quotient form of Proposition 5.3.4.4. -/
theorem sLocalThetaPoleBound_zero (ω : PontryaginDual J₁)
    (r : (w : {w : InfinitePlace F // w.IsReal}) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : {w : InfinitePlace F // w.IsComplex}) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}) :
    sLocalThetaPoleBound ω (fun _ ↦ 0) = (sAdelePolarFree S r c).map (Kₛ(ω)).mkQ := by
  obtain ⟨χ, hcomp, hcover⟩ := sLocalThetaPoleBound_zero_chart (F := F) (S := S) ω
  let chart := twistₛ ((circleToComplex).comp χ)
  have analytic (f : ℬₛ) (s : ℂ) : sLocalPolarMultiplicity f (chart s) = 0 ↔
      AnalyticAt ℂ (fun z ↦ sLocalIdelicZFunction f (chart z)) s := by
    rw [sLocalPolarMultiplicity_eq_zero_iff]
    let Z : ℂ → ℂ := fun z ↦ sLocalIdelicZFunction f (chart z)
    have shift : (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ (chart s) z)) =
        fun z ↦ Z (z + s) := funext fun z ↦ congrArg (sLocalIdelicZFunction f)
          (normTwist_normTwist mₛ hmₛ ((circleToComplex).comp χ) s z)
    rw [shift, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, zero_add]
    exact (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl, hf⟩
    have ha : AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chart s)) univ :=
      fun s _ ↦ (analytic f s).mp (Nat.le_zero.mp (hf (chart s) (hcomp s)))
    obtain ⟨g, he⟩ := (sLocalIdelicZFunction_entire_iff_eq_polarFree r c χ f).mp ha
    refine ⟨g.val, g.property, (Submodule.Quotient.eq (Kₛ(ω))).mpr ?_⟩
    apply (mem_sLocalHomogeneousAdelicTheta_ker_iff ω (g.val - f)).mpr
    intro d hd
    obtain ⟨z, hz⟩ := hcover d.val (ContinuousMonoidHom.ext hd)
    rw [map_sub]
    change sLocalIdelicZFunction g.val d.val - sLocalIdelicZFunction f d.val = 0
    rw [← hz]
    exact sub_eq_zero.mpr (he z).symm
  · rintro _ ⟨f, hf, rfl⟩
    refine Submodule.subset_span ⟨f, rfl, fun d hd ↦ ?_⟩
    obtain ⟨z, rfl⟩ := hcover d hd
    have ha := (sLocalIdelicZFunction_entire_iff_eq_polarFree r c χ f).2
      ⟨⟨f, hf⟩, fun _ ↦ rfl⟩
    exact ((analytic f z).mpr (ha z (Set.mem_univ z))).le

/-- The theta function of a representative with zero pole bound decays at every real exponent.
A polar-free representative furnished by Remark 7.2.1.3 has the same theta function. -/
private theorem sLocalThetaPoleBound_zero_equiv_decay_mem (ω : PontryaginDual J₁)
    (f : ℬₛ) (hf : (Kₛ(ω)).mkQ f ∈ sLocalThetaPoleBound ω (fun _ ↦ 0)) :
    (⇑(sLocalHomogeneousAdelicThetaLinearMap F S ω f) : Jₛ → ℂ) ∈
      modulatedExponentialDecaySubmodule ⟨mₛ, hmₛ⟩ univ := by
  let r (w : {w : InfinitePlace F // w.IsReal}) :
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.property,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal w.property).toHomeomorph.isHomeomorph⟩
  let c (w : {w : InfinitePlace F // w.IsComplex}) :
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.property).toHomeomorph.isHomeomorph⟩
  rw [sLocalThetaPoleBound_zero ω r c] at hf
  obtain ⟨f₀, hf₀, heq⟩ := hf
  have htheta := (sLocalHomogeneousThetaSpace_mk_eq_iff ω f₀ f).mp heq
  rw [← htheta]
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, ⟨hχ, _⟩, _⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  rw [← hχ]
  exact (sLocalIdelicZFunction_entire_iff_theta_exponentialDecay χ f₀).mp
    (sLocalIdelicZFunction_entire_of_polarFree r c f₀ hf₀ χ)

/-- In split coordinates the compact character average extracts the scalar profile of an
isotypic function. The normalization on the compact kernel makes the average equal to
evaluation on the norm section. -/
private theorem sLocalThetaPoleBound_zero_equiv_decay_profile (ω : PontryaginDual J₁)
    (χ : PontryaginDual Jₛ) (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : Function.RightInverse τ mₛ)
    (hχ : ∀ k : J₁, χ k.val = ω k) (ht : ∀ t, χ (τ t) = 1)
    (y : sLocalDecayIsotype (F := F) (S := S) univ ω) :
    ∃ p : PositiveRealExponentialDecay univ, ∀ g : Jₛ,
      p.val (Real.log ((mₛ g).val : ℝ)) = (χ g : ℂ) * y.val.val g := by
  classical
  let m : Jₛ →ₜ* ℝ≥0ˣ := ⟨mₛ, hmₛ⟩
  obtain ⟨t₀, ht₀⟩ := exists_ne (1 : ℝ≥0ˣ)
  have hm : IsModulation m :=
    ⟨isProperMap_sIdeleQuotientNorm F S, τ t₀, (hτ t₀).trans_ne ht₀⟩
  letI (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  letI (v : S) : SecondCountableTopology (v.val.adicCompletion F) := secondCountable_of_proper
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  letI : SecondCountableTopology ((v : S) → v.val.adicCompletion F) := inferInstance
  letI : SecondCountableTopology Aₛ := inferInstanceAs
    (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  letI : SecondCountableTopology Aₛˣ := (sIdeleGroup_description F S).1.secondCountableTopology
  letI : LocallyCompactSpace Aₛˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  letI : T2Space Jₛ := inferInstance
  letI : SecondCountableTopology Jₛ := inferInstance
  letI : LocallyCompactSpace Jₛ := inferInstance
  letI : MeasurableSpace Jₛ := borel _
  letI : BorelSpace Jₛ := ⟨rfl⟩
  letI : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  let K : TopologicalSpace.PositiveCompacts J₁ := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let μ := MeasureTheory.Measure.haarMeasure K
  letI : MeasureTheory.IsProbabilityMeasure μ := ⟨MeasureTheory.Measure.haarMeasure_self⟩
  obtain ⟨A, _, _, hA⟩ := compactAverage_split m hm univ ordConnected_univ univ_nonempty τ hτ μ χ
  have hcov := (mem_sLocalDecayIsotype univ ω y.val).mp y.property
  have hsplit (g : Jₛ) : (χ g : ℂ) * y.val.val g = y.val.val (τ (mₛ g)) := by
    let k : J₁ := ⟨g / τ (mₛ g), by simp [MonoidHom.mem_ker, hτ (mₛ g)]⟩
    have hk : k.val⁻¹ * g = τ (mₛ g) := by
      change (g / τ (mₛ g))⁻¹ * g = τ (mₛ g)
      rw [inv_div, div_mul_cancel]
    have hchar : χ k.val = χ g := by change χ (g / τ (mₛ g)) = _; rw [map_div, ht, div_one]
    simpa only [hk, ← hχ k, hchar] using (hcov k g).symm
  refine ⟨A y.val, fun g ↦ ?_⟩
  rw [hA, hsplit g]
  let t := mₛ g
  have havg (k : J₁) : (χ k.val : ℂ) * y.val.val (k.val * τ t) = y.val.val (τ t) := by
    have ht' : mₛ (k.val * τ t) = t := by rw [map_mul, k.property, hτ, one_mul]
    have hχ' : χ (k.val * τ t) = χ k.val := by rw [map_mul, ht, mul_one]
    simpa only [ht', hχ'] using hsplit (k.val * τ t)
  have hm1 : μ.real univ = 1 := by
    change (μ univ).toReal = 1
    rw [MeasureTheory.measure_univ, ENNReal.toReal_one]
  exact (MeasureTheory.integral_congr_ae (μ := μ) (.of_forall havg)).trans
    ((MeasureTheory.integral_const (μ := μ) (y.val.val (τ t))).trans
      ((congrArg (fun a : ℝ ↦ a • y.val.val (τ t)) hm1).trans (one_smul ℝ _)))

/-- Multiplication of a test by a character of the idele quotient factors that character
out of the S-unit sum, since every projected diagonal S-unit has class one. -/
private theorem sLocalThetaPoleBound_zero_equiv_decay_twist_sum (b : Xₛ)
    (f f' : ℬₛ) (h : ∀ z : Aₛˣ, f' (Multiplicative.ofAdd z.val) =
      b (QuotientGroup.mk z) * f (Multiplicative.ofAdd z.val)) (x : Jₛ) :
    sLocalAdelicThetaOnClasses F S f' x = b x * sLocalAdelicThetaOnClasses F S f x := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicThetaOnClasses_mk,
    sLocalAdelicTheta_apply, sLocalAdelicTheta_apply, ← tsum_mul_left]
  let d := (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  apply tsum_congr
  intro u
  have hu : (QuotientGroup.mk (d u) : Jₛ) = 1 := (sIdeleQuotient_mk_eq_one F S _).mpr ⟨u, rfl⟩
  have hz : (QuotientGroup.mk (d u * z) : Jₛ) = QuotientGroup.mk z := by
    rw [QuotientGroup.mk_mul, hu, one_mul]
  exact (h (d u * z)).trans (congrArg (fun a : Jₛ ↦ b a * f (Multiplicative.ofAdd (d u * z).val)) hz)

/-- Twisting a test by the inverse of a unitary character transports its trivial homogeneous
theta function to the restricted character isotype. -/
private theorem sLocalThetaPoleBound_zero_equiv_decay_twist (ω : PontryaginDual J₁)
    (χ : PontryaginDual Jₛ) (hχ : ∀ u : J₁, χ u.val = ω u) (f f' : ℬₛ)
    (h : ∀ z : Aₛˣ, f' (Multiplicative.ofAdd z.val) =
      ((circleToComplex).comp χ⁻¹) (QuotientGroup.mk z) * f (Multiplicative.ofAdd z.val))
    (g : Jₛ) : sLocalHomogeneousAdelicThetaLinearMap F S ω f' g =
      (χ g : ℂ)⁻¹ * sLocalHomogeneousAdelicThetaLinearMap F S 1 f g := by
  letI : MeasurableSpace J₁ := borel _
  let μ := sLocalNormOneQuotientMeasure F S
  let b := (circleToComplex).comp χ⁻¹
  have hfactor (u : J₁) : b (g * u.val) * (ω u : ℂ) = (χ g : ℂ)⁻¹ := by
    change (((χ (g * u.val))⁻¹ : Circle) : ℂ) * (ω u : ℂ) = _
    rw [map_mul, Circle.coe_inv, Circle.coe_mul, hχ]
    field_simp [Circle.coe_ne_zero]
  have hint (u : J₁) :
      sLocalAdelicThetaOnClasses F S f' (g * u.val) * (ω u : ℂ) =
      (χ g : ℂ)⁻¹ * (sLocalAdelicThetaOnClasses F S f (g * u.val) * ((1 : PontryaginDual J₁) u : ℂ)) := by
    rw [sLocalThetaPoleBound_zero_equiv_decay_twist_sum b f f' h, mul_right_comm, hfactor]
    change _ = _ * (_ * ((1 : Circle) : ℂ))
    rw [Circle.coe_one, mul_one]
  exact (sLocalHomogeneousAdelicThetaLinearMap_apply ω f' g).trans
    ((MeasureTheory.integral_congr_ae (μ := μ) (.of_forall hint)).trans
      ((MeasureTheory.integral_const_mul _ _).trans
        (congrArg ((χ g : ℂ)⁻¹ * ·) (sLocalHomogeneousAdelicThetaLinearMap_apply (F := F) (S := S) (1 : PontryaginDual J₁) f g).symm)))

/-- In the norm-one isotype, every function decaying at all real exponents admits a theta
representative of pole bound zero. Twist the radial lift of Lemma 5.3.4.3 by the inverse
of the unitary character trivial on the chosen norm section. -/
private theorem sLocalThetaPoleBound_zero_equiv_decay_lift (ω : PontryaginDual J₁)
    (y : sLocalDecayIsotype (F := F) (S := S) univ ω) :
    ∃ f : ℬₛ, (Kₛ(ω)).mkQ f ∈ sLocalThetaPoleBound ω (fun _ ↦ 0) ∧
      ∀ g : Jₛ, sLocalHomogeneousAdelicThetaLinearMap F S ω f g = y.val.val g := by
  let r (w : {w : InfinitePlace F // w.IsReal}) :
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.property,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal w.property).toHomeomorph.isHomeomorph⟩
  let c (w : {w : InfinitePlace F // w.IsComplex}) :
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.property).toHomeomorph.isHomeomorph⟩
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, ⟨hχ, ht⟩, _⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  have hres (u : J₁) : χ u.val = ω u := DFunLike.congr_fun hχ u
  obtain ⟨p, hp⟩ := sLocalThetaPoleBound_zero_equiv_decay_profile ω χ τ hτ hres ht y
  obtain ⟨f, hf⟩ := sLocalHomogeneousTheta_trivial_exists_polarFree (F := F) (S := S) r c p
  obtain ⟨M, hM⟩ := sAdelePolarFree_quasiCharacter_mul r c ((circleToComplex).comp χ⁻¹)
  refine ⟨(M f).val, ?_, fun g ↦ ?_⟩
  · rw [sLocalThetaPoleBound_zero ω r c]
    exact ⟨(M f).val, (M f).property, rfl⟩
  · rw [sLocalThetaPoleBound_zero_equiv_decay_twist ω χ hres f.val (M f).val (hM f), hf, hp]
    exact inv_mul_cancel_left₀ (Circle.coe_ne_zero _) _

private theorem sLocalThetaPoleBound_zero_equiv_decay_pointEval (ω : PontryaginDual J₁)
    (I : Set ℝ) (hI : I.Nonempty) (g : Jₛ) :
    Continuous (fun y : sLocalDecayIsotype I ω ↦ y.val.val g) := by
  letI (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  letI (v : S) : SecondCountableTopology (v.val.adicCompletion F) := secondCountable_of_proper
  letI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  letI : SecondCountableTopology ((v : S) → v.val.adicCompletion F) := inferInstance
  letI : SecondCountableTopology Aₛ := inferInstanceAs
    (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  letI : SecondCountableTopology Aₛˣ := (sIdeleGroup_description F S).1.secondCountableTopology
  letI : LocallyCompactSpace Aₛˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  letI : T2Space Jₛ := inferInstance
  letI : SecondCountableTopology Jₛ := inferInstance
  letI : LocallyCompactSpace Jₛ := inferInstance
  exact (continuous_modulatedExponentialDecay_eval ⟨mₛ, hmₛ⟩ I hI g).comp continuous_subtype_val

/-- A homogeneous theta class has continuous point evaluations by the first coordinate
of the Čech theta pair. -/
private theorem sLocalThetaPoleBound_zero_equiv_decay_eval (ω : PontryaginDual J₁) (g : Jₛ) :
    ∃ p : Θₛ(ω) → ℂ, Continuous p ∧ ∀ f : ℬₛ,
      p ((Kₛ(ω)).mkQ f) = sLocalHomogeneousAdelicThetaLinearMap F S ω f g := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, ⟨hχ, _⟩, _⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  rw [← hχ]
  obtain ⟨U, hU, _⟩ := existsUnique_sLocalCechThetaPair (F := F) (S := S) χ
  refine ⟨fun x ↦ (U x).1.val.val g, ?_, fun f ↦ congrFun (hU f).1 g⟩
  have hpos : (Ioi (0 : ℝ)).Nonempty := ⟨1, zero_lt_one⟩
  exact (sLocalThetaPoleBound_zero_equiv_decay_pointEval _ (Ioi 0) hpos g).comp
    (continuous_fst.comp U.continuous)

/-- A surjection from a closed subspace of a Fréchet space to a Fréchet space
is a quotient map if its graph is closed. -/
private theorem sLocalThetaPoleBound_quotientMap_of_closedGraph {E Y : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (hE : IsFrechetTVS E) (hY : IsFrechetTVS Y) (P : Submodule ℂ E)
    (hP : IsClosed (P : Set E)) (A : P →ₗ[ℂ] Y) (hs : Function.Surjective A)
    (hgraph : IsClosed (A.graph : Set (P × Y))) : IsQuotientMap A := by
  obtain ⟨_, hpolE, hmetE, hcompE⟩ := hE
  obtain ⟨_, hpolY, hmetY, hcompY⟩ := hY
  have : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  have : ContinuousSMul ℂ Y := PolynormableSpace.continuousSMul ℂ Y
  have hc := weilTest_continuous_of_isClosed_graph
    ⟨inferInstance, hpolE, hmetE, hcompE⟩ ⟨inferInstance, hpolY, hmetY, hcompY⟩ P hP A hgraph
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hcompE
  have : CompleteSpace Y := hcompY
  have : CompleteSpace P := completeSpace_coe_iff_isComplete.mpr hP.isComplete
  have : IsUniformAddGroup P := P.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace P :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (P : Set E))
  have : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  let T : P →L[ℂ] Y := ⟨A, hc⟩
  have hopen : IsOpenMap T := by
    apply isOpenMap_of_not_isMeagre_range
    change ¬ IsMeagre (range A)
    rw [hs.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  exact hopen.isQuotientMap hc hs

private theorem sLocalThetaPoleBound_zero_equiv_decay_closedGraph {X Y ι : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (A : X →ₗ[ℂ] Y) (e : ι → Y → ℂ)
    (hsep : ∀ y z : Y, (∀ i, e i y = e i z) → y = z)
    (he : ∀ i, Continuous (e i)) (hs : ∀ i, Continuous (fun x ↦ e i (A x))) :
    IsClosed (A.graph : Set (X × Y)) := by
  have hset : (A.graph : Set (X × Y)) = ⋂ i, {p : X × Y | e i p.2 = e i (A p.1)} := by
    ext p
    refine ⟨fun h ↦ mem_iInter.mpr fun i ↦ congrArg (e i) ((LinearMap.mem_graph_iff A p).mp h), ?_⟩
    exact fun h ↦ (LinearMap.mem_graph_iff A p).mpr (hsep _ _ fun i ↦ mem_iInter.mp h i)
  rw [hset]
  exact isClosed_iInter fun i ↦ isClosed_eq ((he i).comp continuous_snd) ((hs i).comp continuous_fst)

private theorem sLocalThetaPoleBound_zero_equiv_decay_frechet (ω : PontryaginDual J₁) :
    IsFrechetTVS ↥(sLocalDecayIsotype (F := F) (S := S) univ ω) := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨M, _, _⟩ := existsUnique_sLocalDecayMellin τ hτ univ isOpen_univ
    (by infer_instance) univ_nonempty ω 0
  exact frechet_of_equiv M.symm
    (schwartzBergman_frechet univ isOpen_univ (by infer_instance) univ_nonempty)

private theorem sLocalThetaPoleBound_zero_equiv_decay_continuous_of_representatives
    {B Q X : Type*} [TopologicalSpace Q] [TopologicalSpace X]
    (q : B → Q) (hq : Function.Surjective q) (v : X → Q) (hv : Continuous v)
    (p : Q → ℂ) (hp : Continuous p) (a : X → ℂ) (t : B → ℂ)
    (ht : ∀ f, p (q f) = t f) (ha : ∀ x f, v x = q f → a x = t f) :
    Continuous a := by
  refine (hp.comp hv).congr fun x ↦ ?_
  obtain ⟨f, hf⟩ := hq (v x)
  exact (congrArg p hf.symm).trans ((ht f).trans (ha x f hf.symm).symm)

/-- The surjective pointwise theta realization is a quotient map for the two Fréchet
topologies. Its graph is the intersection of the closed pointwise equalizers. -/
private theorem sLocalThetaPoleBound_zero_equiv_decay_quotientMap (ω : PontryaginDual J₁)
    (A : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0)) →ₗ[ℂ]
      ↥(sLocalDecayIsotype (F := F) (S := S) univ ω))
    (hA : ∀ (x : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0))) (f : ℬₛ),
      x.val = (Kₛ(ω)).mkQ f → ∀ g : Jₛ,
      (A x).val.val g = sLocalHomogeneousAdelicThetaLinearMap F S ω f g)
    (hs : Function.Surjective A) : IsQuotientMap A := by
  let P := sLocalThetaPoleBound ω (fun _ ↦ 0)
  let Y := ↥(sLocalDecayIsotype (F := F) (S := S) univ ω)
  have hY := sLocalThetaPoleBound_zero_equiv_decay_frechet ω
  have heval (g : Jₛ) : Continuous (fun y : Y ↦ y.val.val g) :=
    sLocalThetaPoleBound_zero_equiv_decay_pointEval ω univ univ_nonempty g
  have hsrc (g : Jₛ) : Continuous (fun x : P ↦ (A x).val.val g) := by
    obtain ⟨p, hp, hval⟩ := sLocalThetaPoleBound_zero_equiv_decay_eval ω g
    exact sLocalThetaPoleBound_zero_equiv_decay_continuous_of_representatives
      (B := ℬₛ) (Q := Θₛ(ω)) (X := ↥P) (Kₛ(ω)).mkQ (Kₛ(ω)).mkQ_surjective
      (fun x : P ↦ x.val) continuous_subtype_val p hp (fun x : P ↦ (A x).val.val g)
      (fun f : ℬₛ ↦ sLocalHomogeneousAdelicThetaLinearMap F S ω f g) hval
      (fun x f hf ↦ hA x f hf g)
  apply sLocalThetaPoleBound_quotientMap_of_closedGraph (E := Θₛ(ω)) (Y := Y)
    (sLocalHomogeneousThetaSpace_frechet ω)
    hY P (sLocalThetaPoleBound_isClosed ω _) A hs
  exact sLocalThetaPoleBound_zero_equiv_decay_closedGraph (X := P) (Y := Y) A
    (fun (g : Jₛ) (y : Y) ↦ y.val.val g) (fun _ _ h ↦ Subtype.ext (Subtype.ext (funext h))) heval hsrc

/-- Paper: Remark 7.2.1.3, p. 335.
Interpreting a polar-free theta class as its theta function identifies the entire
subspace with the exponentially decreasing norm-one isotype, with its topology.
Deviation: The entire subspace is written as the zero pole bound. -/
theorem sLocalThetaPoleBound_zero_equiv_decay (ω : PontryaginDual J₁) :
    ∃ e : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0)) ≃L[ℂ]
        ↥(sLocalDecayIsotype (F := F) (S := S) univ ω),
      ∀ (x : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0))) (f : ℬₛ),
        x.val = (Kₛ(ω)).mkQ f →
          ∀ g : Jₛ, (e x).val.val g = sLocalHomogeneousAdelicThetaLinearMap F S ω f g := by
  classical
  let P := sLocalThetaPoleBound ω (fun _ ↦ 0)
  let Y := sLocalDecayIsotype (F := F) (S := S) univ ω
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω
  let L : P →ₗ[ℂ] C(Jₛ, ℂ) :=
    θ.range.subtype.comp (θ.quotKerEquivRange.toLinearMap.comp P.subtype)
  have hL (x : P) (f : ℬₛ) (h : x.val = θ.ker.mkQ f) : L x = θ f := by
    change (θ.quotKerEquivRange x.val).val = θ f
    exact (congrArg (fun z ↦ (θ.quotKerEquivRange z).val) h).trans
      (θ.quotKerEquivRange_apply_mk f)
  have hm (x : P) : (⇑(L x) : Jₛ → ℂ) ∈
      modulatedExponentialDecaySubmodule ⟨mₛ, hmₛ⟩ univ := by
    obtain ⟨f, hf⟩ := θ.ker.mkQ_surjective x.val
    rw [hL x f hf.symm]
    exact sLocalThetaPoleBound_zero_equiv_decay_mem ω f (hf.symm ▸ x.property)
  let V (x : P) : Y := ⟨⟨⇑(L x), hm x⟩, by
    apply (mem_sLocalDecayIsotype univ ω _).mpr
    intro u g
    obtain ⟨f, hf⟩ := θ.ker.mkQ_surjective x.val
    change L x (u.val⁻¹ * g) = (ω u : ℂ) * L x g
    rw [hL x f hf.symm]
    let : MeasurableSpace J₁ := borel _
    have := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
    exact sLocalHomogeneousAdelicTheta_homogeneous F S (sLocalNormOneQuotientMeasure F S) ω f u g⟩
  let A : P →ₗ[ℂ] Y :=
    { toFun := V
      map_add' := fun x y ↦ Subtype.ext (Subtype.ext (funext fun g ↦
        congrArg (fun v : C(Jₛ, ℂ) ↦ v g) (L.map_add x y)))
      map_smul' := fun t x ↦ Subtype.ext (Subtype.ext (funext fun g ↦
        congrArg (fun v : C(Jₛ, ℂ) ↦ v g) (L.map_smul t x))) }
  have hA (x : P) (f : ℬₛ) (h : x.val = θ.ker.mkQ f) (g : Jₛ) :
      (A x).val.val g = θ f g := congrArg (fun v : C(Jₛ, ℂ) ↦ v g) (hL x f h)
  have hi : Function.Injective A := by
    intro x y h
    apply Subtype.ext
    apply θ.quotKerEquivRange.injective
    apply Subtype.ext
    exact ContinuousMap.ext fun g ↦ congrArg (fun v : Y ↦ v.val.val g) h
  have hs : Function.Surjective A := by
    intro y
    obtain ⟨f, hf, he⟩ := sLocalThetaPoleBound_zero_equiv_decay_lift ω y
    let x : P := ⟨θ.ker.mkQ f, hf⟩
    exact ⟨x, Subtype.ext (Subtype.ext (funext fun g ↦ (hA x f rfl g).trans (he g)))⟩
  let e := LinearEquiv.ofBijective A ⟨hi, hs⟩
  have hq := sLocalThetaPoleBound_zero_equiv_decay_quotientMap ω A hA hs
  exact ⟨ContinuousLinearEquiv.ofIsHomeomorph e
    (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hi⟩), hA⟩

/-- Paper: Equation (7.2.1.12), p. 336.
The Fourier-transformed Euler product is the Euler product at the dual character
divided by the local epsilon factor.
Deviation: The local tests are normalized so that their original zeta product is
the Euler product. This uses the epsilon normalization of (3.3.1.32). -/
def sLocalFourierEulerProduct (c : Xₛ) : ℂ :=
  sLocalHeckeL (dualₛ c) / sLocalEpsilonFactor c

private theorem sLocalFourierEulerProduct_eq_zeta_factorization (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    let c := twistₛ ((circleToComplex).comp χ)
    ∀ᶠ z : ℂ in codiscrete ℂ,
      sLocalIdelicZFunction f (c z) = sLocalNormalizedZFunction f (c z) * sLocalHeckeL (c z) := by
  intro c
  have hL : Meromorphic (fun z ↦ sLocalHeckeL (c z)) := by
    intro z
    have h := ((differentiable_inv_sLocalHeckeL χ).analyticAt z).meromorphicAt.inv
    change MeromorphicAt (fun t : ℂ ↦ ((sLocalHeckeL (c t))⁻¹)⁻¹) z at h
    simpa only [inv_inv] using h
  apply meromorphic_eq_of_germ (fun z ↦ (sLocalIdelicZFunction_meromorphic f χ).meromorphicOn z trivial)
    (fun z ↦ ((sLocalNormalizedZFunction_entire f χ) z trivial).meromorphicAt.mul (hL z)) (z := 1)
  have hpos : ∀ᶠ z in 𝓝[≠] (1 : ℂ), 0 < z.re := nhdsWithin_le_nhds
    ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (show (1 : ℂ) ∈ Complex.re ⁻¹' Ioi 0 by simp))
  filter_upwards [hpos, nhdsNE_le_codiscrete _ (sLocalNormalizedEigendistribution_gaussian_heckeL_ne_zero χ)]
    with z hz hne
  change sLocalIdelicZFunction f (c z) = sLocalNormalizedZFunction f (c z) * sLocalHeckeL (c z)
  calc
    _ = sLocalIdelicZetaIntegral f (c z) := sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩
    _ = _ := ((div_mul_cancel₀ _ hne).symm).trans
      (congrArg (· * sLocalHeckeL (c z)) (sLocalNormalizedZFunction_eq_div f χ hz).symm)

private theorem sLocalFourierEulerProduct_eq_zeta_of_normalized (χ : PontryaginDual Jₛ)
    (f : ℬₛ) (M : ℂ) :
    let c := twistₛ ((circleToComplex).comp χ)
    ∀ᶠ z : ℂ in codiscrete ℂ, sLocalNormalizedZFunction f (c z) = M →
      sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (c z)) =
        M * sLocalFourierEulerProduct (c z) := by
  intro c
  apply eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
  intro s
  have ht : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] s) (𝓝[≠] (1 - s)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using fun h ↦ hz (sub_right_inj.mp h)
  filter_upwards [ht.eventually (nhdsNE_le_codiscrete _
    (sLocalFourierEulerProduct_eq_zeta_factorization χ⁻¹ (sAdeleSchwartzFourier f)))] with z hz
  intro hM
  have hz' := (congrArg (fun d : Xₛ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) d =
    sLocalNormalizedZFunction (sAdeleSchwartzFourier f) d * sLocalHeckeL d)
    (sLocal_dual_chart χ z)).mpr hz
  apply hz'.trans
  have hFE := (sLocalNormalizedZFunction_functionalEquation f (c z)).symm.trans hM
  rw [← hFE, sLocalFourierEulerProduct]
  field_simp [sLocalEpsilonFactor_ne_zero (c z)]
  ring

/-- Paper: Equation (7.2.1.12), p. 336.
If an S-adelic test has the Euler product as its zeta transform on a component,
its Fourier transform on the reflected component gives the Fourier Euler product.
The equality is between meromorphic functions in the norm coordinate. -/
theorem sLocalFourierEulerProduct_eq_zeta (c : Xₛ) (f : ℬₛ)
    (hf : (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ c z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalHeckeL (twistₛ c z))) :
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z)))
      =ᶠ[codiscrete ℂ] (fun z ↦ sLocalFourierEulerProduct (twistₛ c z)) := by
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  simp only [normTwist_normTwist] at hf ⊢
  apply eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
  intro s
  have ht : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] s) (𝓝[≠] (s + a)) :=
    ((Homeomorph.addRight a).map_punctured_nhds_eq s).le
  filter_upwards [nhdsNE_le_codiscrete s hf,
    ht.eventually (nhdsNE_le_codiscrete _ (sLocalFourierEulerProduct_eq_zeta_factorization χ f)),
    ht.eventually (nhdsNE_le_codiscrete _ (sLocalNormalizedEigendistribution_gaussian_heckeL_ne_zero χ)),
    ht.eventually (nhdsNE_le_codiscrete _ (sLocalFourierEulerProduct_eq_zeta_of_normalized χ f 1))]
    with z hZ hfactor hne hFourier
  simpa only [one_mul] using hFourier
    (mul_right_cancel₀ hne (hfactor.symm.trans (hZ.trans (one_mul _).symm)))

local notation "finiteUnitMass" => (∏ v : S,
  (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
    (v.val.adicCompletionIntegers F).units).toReal : ℂ))

/-- Paper: Equation (7.2.1.12), p. 336.
The Fourier transform of the tensor of the standard archimedean and finite tests
has the reflected Fourier Euler product as its Mellin transform, scaled by the
product of the integer-unit masses.
Deviation: The test is the unscaled tensor of §3.4, with its Tamagawa masses. -/
theorem sLocalFourierEulerProduct_eq_zeta_standardGaussian
    (χ : PontryaginDual Jₛ) (χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ)
    (hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ))
    (g : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    (hg : ∀ x : InfiniteAdeleRing F, g (Multiplicative.ofAdd x) =
      ∏ w, infiniteStandardGaussian w (χArch w) (Multiplicative.ofAdd (x w))) :
    let c : Xₛ := (circleToComplex).comp χ
    let f := sLocalStandardThetaTensor c g
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z)))
      =ᶠ[codiscrete ℂ] (fun z ↦ finiteUnitMass * sLocalFourierEulerProduct (twistₛ c z)) := by
  classical
  intro c f
  have h0 : twistₛ c 0 = c := by
    ext1 u
    change c u * _ ^ (0 : ℂ) = c u
    rw [Complex.cpow_zero, mul_one]
  filter_upwards [sLocalFourierEulerProduct_eq_zeta_of_normalized χ f finiteUnitMass] with z hz
  apply hz
  have hfin (v : S) : finiteStandardGaussian v.val (sLocalFiniteRestriction v c) =
      finiteStandardGaussian v.val (sLocalFiniteRestriction v (twistₛ c z)) := by
    obtain ⟨η, he⟩ := sLocalNormalizedEigendistribution_gaussian_finChart χ v
    have hbase := he 0
    change sLocalFiniteRestriction v (twistₛ c 0) = _ at hbase
    rw [h0] at hbase
    rw [hbase, he z]
    exact sLocalNormalizedEigendistribution_gaussian_finTest v.val η 0 z
  have hG := sLocalNormalizedEigendistribution_gaussian χ z χArch hχ f (fun x ↦ by
    dsimp only [f]
    rw [sLocalStandardThetaTensor_apply, hg]
    apply congrArg (_ * ·)
    exact Finset.prod_congr rfl fun v _ ↦ congrArg
      (fun q : SchwartzBruhat (Multiplicative (v.val.adicCompletion F)) ↦ q (Multiplicative.ofAdd (x.2 v)))
      (hfin v))
  have hspec : finiteUnitMass * sLocalNormalizedEigendistribution (twistₛ c z) f =
      sLocalNormalizedZFunction f (twistₛ c z) := by
    simpa only [Complex.ofReal_prod, sLocalNormalizedEigendistribution] using
      (existsUnique_sLocalNormalizedEigendistribution (twistₛ c z)).exists.choose_spec f
  rw [← hspec, hG, mul_one]

/-- Paper: Equations (7.2.1.12) and (7.2.1.17), pp. 336–337.
The ratio of the original Euler product to the Fourier Euler product gives the
local correcting factor as a meromorphic identity.
Deviation: The Fourier Euler product already incorporates the epsilon factor. -/
theorem sLocalRhoFactor_eq_div_fourierEulerProduct (c : Xₛ) :
    (fun z : ℂ ↦ sLocalRhoFactor (twistₛ c z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalHeckeL (twistₛ c z) / sLocalFourierEulerProduct (twistₛ c z)) := by
  have quotient (e x y : ℂ) : e * (x / y) = x / (y / e) := by
    simp [div_eq_mul_inv, mul_left_comm]
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  simp only [normTwist_normTwist]
  apply eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
  intro z
  have ht : Tendsto (fun w : ℂ ↦ w + a) (𝓝[≠] z) (𝓝[≠] (z + a)) :=
    ((Homeomorph.addRight a).map_punctured_nhds_eq z).le
  filter_upwards [ht.eventually (nhdsNE_le_codiscrete _ (sLocalRhoFactor_eq_epsilon_mul χ))] with w hw
  exact hw.trans (quotient _ _ _)

-- TODO(paper-gap): The change of unitary base point on p. 336 is
-- χ' = χ |·|^(it₀). The printed identity omits the original base point χ.

/-- The geometric denominator of a finite Euler factor has only simple zeros.
Ramified finite Euler factors are identically one. -/
theorem sLocalPrincipalPartCoeff_leading_formula_fin_factor (c : Xₛ) (v : S) :
    MeromorphicNFAt (finEuler(v, c)) 0 ∧
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (finEuler(v, c)) 0 := by
  classical
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  obtain ⟨η, hη, -⟩ := sLocalFinite_charts χ v
  let C := quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom :
    (v.val.adicCompletion F)ˣ →* ℝ≥0ˣ) (continuous_finiteLocalModule v.val) ((circleToComplex).comp η)
  let E : ℂ → ℂ := fun z ↦ finiteLocalEulerFactor v.val (C z)
  have hshift : finEuler(v, twistₛ ((circleToComplex).comp χ) a) = E ∘ (· + a) := by
    funext z
    dsimp only [Function.comp_apply, E]
    rw [normTwist_normTwist, hη]
  rw [hshift, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt,
    meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  suffices h : ∀ s, MeromorphicNFAt E s ∧ ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt E s by
    exact h (0 + a)
  intro s
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hu (z : ℂ) (u : (v.val.adicCompletionIntegers F)ˣ) : C z (ι u) = (η (ι u) : ℂ) := by
    change (η _ : ℂ) * (‖(ι u).val‖ : ℂ) ^ z = _
    rw [show ‖(ι u).val‖ = 1 from finite_integer_unit_norm v.val u,
      Complex.ofReal_one, Complex.one_cpow, mul_one]
  have hram (z : ℂ) : (∀ u, C z (ι u) = 1) ↔ (∀ u, (η (ι u) : ℂ) = 1) :=
    ⟨fun h u ↦ (hu z u).symm.trans (h u), fun h u ↦ (hu z u).trans (h u)⟩
  have hneg : ((-1 : ℤ) : WithTop ℤ) ≤ 0 := WithTop.coe_le_coe.mpr (by decide : (-1 : ℤ) ≤ 0)
  by_cases h : ∀ u, (η (ι u) : ℂ) = 1
  · let hp := (Valued.v : Valuation (v.val.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let p : (v.val.adicCompletion F)ˣ := Units.mk0 hp.choose hp.choose_spec.ne_zero
    have hpn : ‖p.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ :=
      norm_uniformizer_adicCompletion v.val _ hp.choose_spec
    let D : ℂ → ℂ := fun z ↦ 1 - C z p
    have he : E = D⁻¹ := by
      funext z
      dsimp only [E, finiteLocalEulerFactor]
      rw [ite_eq_left ((hram z).mpr h)]
      rfl
    have hD : Differentiable ℂ D := fun z ↦ (finite_den_hasDerivAt v.val η p hpn z).differentiableAt
    rw [he]
    refine ⟨(hD.analyticAt s).meromorphicNFAt.inv, ?_⟩
    by_cases hz : D s = 0
    · have hval : C s p = 1 := (sub_eq_zero.mp hz).symm
      have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
      have hder : deriv D s ≠ 0 := by
        rw [show deriv D s = C s p * (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) from
          (finite_den_hasDerivAt v.val η p hpn s).deriv, hval, one_mul]
        exact Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
      rw [meromorphicOrderAt_inv, (hD.analyticAt s).meromorphicOrderAt_eq,
        (hD.analyticAt s).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hder]
      exact le_rfl
    · exact hneg.trans ((hD.analyticAt s).inv hz).meromorphicOrderAt_nonneg
  · have he : E = fun _ ↦ 1 := by
      funext z
      exact ite_eq_right (fun h' ↦ h ((hram z).mp h'))
    rw [he]
    exact ⟨analyticAt_const.meromorphicNFAt, hneg.trans analyticAt_const.meromorphicOrderAt_nonneg⟩

/-- In the centered norm chart the archimedean factors are in meromorphic normal
form, and their poles have order at most one. -/
theorem sLocalPrincipalPartCoeff_leading_formula_arch_factor (c : Xₛ) (w : InfinitePlace F) :
    MeromorphicNFAt (archEuler(w, c)) 0 ∧
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (archEuler(w, c)) 0 := by
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have shift : archEuler(w, twistₛ ((circleToComplex).comp χ) a) =
      archEuler(w, (circleToComplex).comp χ) ∘ (· + a) := by
    funext z
    simp only [Function.comp_apply, normTwist_normTwist]
  rw [shift, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt,
    meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
  refine ⟨?_, neg_one_le_meromorphicOrderAt_infiniteLocalEulerFactor_chart χ w a⟩
  apply meromorphicNFAt_inv.mp
  by_cases hw : w.IsReal
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hw
    have he : (archEuler(w, (circleToComplex).comp χ))⁻¹ =
        fun z ↦ (Complex.Gammaℝ (z + b))⁻¹ := funext fun z ↦ congrArg Inv.inv (hb z)
    rw [he]
    exact ((Complex.differentiable_Gammaℝ_inv.comp
      (show Differentiable ℂ (fun z : ℂ ↦ z + b) by fun_prop)).analyticAt a).meromorphicNFAt
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    have he : (archEuler(w, (circleToComplex).comp χ))⁻¹ =
        fun z ↦ 2 * (Complex.Gammaℂ (z + b))⁻¹ := by
      funext z
      rw [Pi.inv_apply, hb, inv_div, div_eq_mul_inv]
    rw [he]
    exact (analyticAt_const.mul ((Complex.differentiable_Gammaℂ_inv.comp
      (show Differentiable ℂ (fun z : ℂ ↦ z + b) by fun_prop)).analyticAt a)).meromorphicNFAt

/-- Remove each simple pole at zero from a finite product. The resulting center
value multiplies the residues at poles and the original values at regular factors. -/
private theorem sLocalPrincipalPartCoeff_leading_formula_finite_product
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ι) (L : ι → ℂ → ℂ)
    (hP : ∀ i, i ∈ P ↔ meromorphicOrderAt (L i) 0 < 0)
    (hL : ∀ i, MeromorphicNFAt (L i) 0 ∧
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (L i) 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      H 0 = (∏ i ∈ P, complexResidue (L i) 0) * (∏ i ∈ Finset.univ \ P, L i 0) ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), H z = z ^ P.card * ∏ i, L i z := by
  classical
  have regularize (i : ι) : ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      G 0 = (if i ∈ P then complexResidue (L i) 0 else L i 0) ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), G z = (if i ∈ P then z else 1) * L i z := by
    by_cases hi : i ∈ P
    · have hp := (hP i).mp hi
      have ho : meromorphicOrderAt (L i) 0 = ((-1 : ℤ) : WithTop ℤ) := by
        apply le_antisymm _ (hL i).2
        generalize he : meromorphicOrderAt (L i) 0 = o at hp ⊢
        induction o using WithTop.recTopCoe with
        | top => simp at hp
        | coe n =>
          have hn : n < 0 := by exact_mod_cast hp
          exact_mod_cast (by omega : n ≤ -1)
      obtain ⟨G, hG, _, he⟩ := (meromorphicOrderAt_eq_int_iff (hL i).1.meromorphicAt).mp ho
      have hdiv : L i =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ G z / (z - 0) := by
        filter_upwards [he] with z hz
        rw [hz, smul_eq_mul, zpow_neg_one, div_eq_mul_inv, mul_comm]
      refine ⟨G, hG, ?_, ?_⟩
      · rw [ite_eq_left hi, mem_sLocalThetaPoleBound_iff_residue_congr hdiv, complexResidue_div_sub hG]
      · filter_upwards [hdiv, self_mem_nhdsWithin] with z hz hz0
        have hne : z ≠ 0 := hz0
        rw [ite_eq_left hi, hz, sub_zero]
        field_simp
    · refine ⟨L i, (hL i).1.meromorphicOrderAt_nonneg_iff_analyticAt.mp
        (not_lt.mp (mt (hP i).mpr hi)), by simp [hi], .of_forall fun z ↦ by simp [hi]⟩
  choose G hA h0 he using regularize
  refine ⟨fun z ↦ ∏ i, G i z, Finset.univ.analyticAt_fun_prod (fun i _ ↦ hA i), ?_, ?_⟩
  · change (∏ i, G i 0) = _
    rw [← Finset.prod_sdiff (f := fun i ↦ G i 0) (Finset.subset_univ P)]
    rw [Finset.prod_congr (s₁ := Finset.univ \ P) rfl
      (fun i hi ↦ (h0 i).trans (ite_eq_right (Finset.mem_sdiff.mp hi).2)),
      Finset.prod_congr (s₁ := P) rfl (fun i hi ↦ (h0 i).trans (ite_eq_left hi))]
    exact mul_comm _ _
  · filter_upwards [eventually_all.mpr he] with z hz
    simp only [hz, Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const]

open Classical in
/-- Multiplying the centered Euler product by its pole power gives an analytic germ.
Its value at the center is the product of the residues at the polar places and
the ordinary Euler values at the remaining places, as in (7.2.1.23), p. 338. -/
private theorem sLocalPrincipalPartCoeff_leading_formula_euler_germ (c : Xₛ) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      H 0 = (∏ w ∈ sLocalArchPolePlaces c, complexResidue (archEuler(w, c)) 0) *
        (∏ w ∈ Finset.univ \ sLocalArchPolePlaces c, archEuler(w, c) 0) *
        (∏ v ∈ sLocalFinitePolePlaces c, complexResidue (finEuler(v, c)) 0) *
        (∏ v ∈ Finset.univ \ sLocalFinitePolePlaces c, finEuler(v, c) 0) ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), H z = z ^ sLocalRhoPoleOrder c * sLocalHeckeL (twistₛ c z) := by
  classical
  obtain ⟨A, hAa, hA0, hAe⟩ := sLocalPrincipalPartCoeff_leading_formula_finite_product
    (sLocalArchPolePlaces c) (fun w ↦ archEuler(w, c)) (fun w ↦ by simp [sLocalArchPolePlaces])
    (sLocalPrincipalPartCoeff_leading_formula_arch_factor c)
  obtain ⟨B, hBa, hB0, hBe⟩ := sLocalPrincipalPartCoeff_leading_formula_finite_product
    (sLocalFinitePolePlaces c) (fun v ↦ finEuler(v, c)) (fun v ↦ by simp [sLocalFinitePolePlaces])
    (sLocalPrincipalPartCoeff_leading_formula_fin_factor c)
  refine ⟨A * B, hAa.mul hBa, ?_, ?_⟩
  · rw [Pi.mul_apply, hA0, hB0]
    ring
  · filter_upwards [hAe, hBe] with z hz hz'
    rw [Pi.mul_apply, hz, hz', sLocalRhoPoleOrder_eq_card_polePlaces, pow_add, sLocalHeckeL]
    ring

open Classical in
/-- Paper: Theorem 7.2.1.4(1), p. 336.
The coefficient of the highest allowed polar order is the product of local residues
and regular local Euler values times the Fourier-transformed dual eigendistribution.
Deviation: Uses the Laurent exponent `-m`. The epsilon factor and the finite
integer-unit masses account for the normalizations of §3.3 and §5.5. -/
theorem sLocalPrincipalPartCoeff_leading_formula (c : Xₛ) (hc : 0 < sLocalRhoPoleOrder c)
    (f : ℬₛ) :
    let arch := sLocalArchPolePlaces c
    let fin := sLocalFinitePolePlaces c
    sLocalPrincipalPartCoeff c (sLocalRhoPoleOrder c) f =
      (∏ w ∈ arch, complexResidue (archEuler(w, c)) 0) *
      (∏ w ∈ Finset.univ \ arch, archEuler(w, c) 0) *
      (∏ v ∈ fin, complexResidue (finEuler(v, c)) 0) *
      (∏ v ∈ Finset.univ \ fin, finEuler(v, c) 0) *
      (finiteUnitMass * sLocalEpsilonFactor c *
        sLocalNormalizedEigendistribution (dualₛ c) (sAdeleSchwartzFourier f)) := by
  classical
  dsimp only
  obtain ⟨H, hH, hvalue, hEuler⟩ := sLocalPrincipalPartCoeff_leading_formula_euler_germ c
  obtain ⟨χ, a, hca⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let N : ℂ → ℂ := fun z ↦ sLocalNormalizedZFunction f (twistₛ c z)
  have hN : AnalyticAt ℂ N 0 := by
    have he : N = (fun s ↦ sLocalNormalizedZFunction f (twistₛ ((circleToComplex).comp χ) s)) ∘
        (fun t ↦ t + a) := by
      funext t
      dsimp only [N, Function.comp_apply]
      rw [← hca, normTwist_normTwist]
    rw [he]
    apply AnalyticAt.comp (f := fun z : ℂ ↦ z + a)
    · exact sLocalNormalizedZFunction_entire f χ (0 + a) trivial
    · exact analyticAt_id.add analyticAt_const
  have hfactor : ∀ᶠ z in 𝓝[≠] (0 : ℂ), sLocalIdelicZFunction f (twistₛ c z) =
      N z * sLocalHeckeL (twistₛ c z) := by
    have ht : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] (0 + a)) :=
      ((Homeomorph.addRight a).map_punctured_nhds_eq 0).le
    filter_upwards [ht.eventually (nhdsNE_le_codiscrete _
      (sLocalFourierEulerProduct_eq_zeta_factorization χ f))] with z hz
    simpa only [N, ← hca, normTwist_normTwist] using hz
  have hzero : twistₛ c 0 = c := by
    ext1 u
    change c u * _ ^ (0 : ℂ) = c u
    rw [Complex.cpow_zero, mul_one]
  have hmass : finiteUnitMass * sLocalNormalizedEigendistribution (dualₛ c)
      (sAdeleSchwartzFourier f) = sLocalNormalizedZFunction (sAdeleSchwartzFourier f) (dualₛ c) := by
    simpa only [Complex.ofReal_prod, sLocalNormalizedEigendistribution] using
      (existsUnique_sLocalNormalizedEigendistribution (dualₛ c)).exists.choose_spec (sAdeleSchwartzFourier f)
  have hN0 : N 0 = finiteUnitMass * sLocalEpsilonFactor c *
      sLocalNormalizedEigendistribution (dualₛ c) (sAdeleSchwartzFourier f) := by
    dsimp only [N]
    rw [hzero, sLocalNormalizedZFunction_functionalEquation, ← hmass]
    ring
  change complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) /
    z ^ (-(sLocalRhoPoleOrder c : ℤ) + 1)) 0 = _
  have he : (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) /
      z ^ (-(sLocalRhoPoleOrder c : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z ↦ (H z * N z) / (z - 0)) := by
    filter_upwards [hfactor, hEuler, self_mem_nhdsWithin] with z hz hL hn
    have hn' : z ≠ 0 := hn
    rw [hz, hL, sub_zero, zpow_add₀ hn', zpow_one, zpow_neg, zpow_natCast]
    field_simp [hn']
  rw [mem_sLocalThetaPoleBound_iff_residue_congr he,
    complexResidue_div_sub (g := fun z ↦ H z * N z) (hH.mul hN), hvalue, hN0]

/-- Paper: Theorem 7.2.1.4(1), p. 337.
The leading principal-part functional transforms with weight given by the center. -/
theorem sLocalPrincipalPartCoeff_leading_eigendistribution (c : Xₛ)
    (hc : 0 < sLocalRhoPoleOrder c) :
    sLocalPrincipalPartCoeff c (sLocalRhoPoleOrder c) ∈ sLocalEigendistributions c := by
  have leading (m : ℕ) (hm : 0 < m) (a : ℕ → ℂ) (t : ℂ) :
      (∑ j ∈ Finset.range (m - m + 1), a (m + j) * t ^ j / (j.factorial : ℂ)) = a m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp
  apply (mem_sLocalEigendistributions (F := F) (S := S) c _).2
  intro u f
  have h := sLocalPrincipalPartCoeff_translate (F := F) (S := S) c (sLocalRhoPoleOrder c) le_rfl u f
  exact h.trans (congrArg (c (QuotientGroup.mk u) * ·)
    (leading _ hc (fun k ↦ sLocalPrincipalPartCoeff c k f) _))

/-- Cauchy's derivative formula identifies a Taylor coefficient with its shifted residue. -/
private theorem sLocalPrincipalPartCoeff_lower_formula_cauchy {A : ℂ → ℂ}
    (hA : AnalyticAt ℂ A 0) (j : ℕ) :
    complexResidue (fun z : ℂ ↦ A z / z ^ (j + 1)) 0 =
      iteratedDeriv j A 0 / (j.factorial : ℂ) := by
  obtain ⟨R, hR, hball⟩ := hA.exists_ball_analyticOnNhd
  unfold complexResidue
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hd : DifferentiableOn ℂ A (Metric.closedBall 0 r) :=
    (hball.mono (Metric.closedBall_subset_ball hr.2)).differentiableOn
  have he : circleIntegral (fun z : ℂ ↦ A z / z ^ (j + 1)) 0 r =
      (2 * (Real.pi : ℂ) * Complex.I / (j.factorial : ℂ)) * iteratedDeriv j A 0 := by
    simpa only [sub_zero, one_div, smul_eq_mul, div_eq_inv_mul, mul_one] using
      hd.circleIntegral_one_div_sub_center_pow_smul hr.1 j
  rw [he]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Apply Leibniz's formula to the analytic numerator after removing a pole of order m.
The two Cauchy coefficient identities use only the punctured germs. -/
private theorem sLocalPrincipalPartCoeff_lower_formula_product {Z ρ H : ℂ → ℂ}
    {m k : ℕ} (hk : k < m) (hρ : MeromorphicAt ρ 0)
    (hord : meromorphicOrderAt ρ 0 = ((-(m : ℤ) : ℤ) : WithTop ℤ))
    (hH : AnalyticAt ℂ H 0) (hZ : Z =ᶠ[𝓝[≠] (0 : ℂ)] ρ * H) :
    complexResidue (fun z : ℂ ↦ Z z / z ^ (-(k : ℤ) + 1)) 0 =
      ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z : ℂ ↦ ρ z * z ^ ((m : ℤ) - (j : ℤ) - 1)) 0 *
          (iteratedDeriv (m - k - j) H 0 / ((m - k - j).factorial : ℂ)) := by
  obtain ⟨A, hA, -, hrep⟩ := (meromorphicOrderAt_eq_int_iff hρ).mp hord
  let n := m - k
  have hmain : (fun z : ℂ ↦ Z z / z ^ (-(k : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z ↦ (A * H) z / z ^ (n + 1)) := by
    filter_upwards [hZ, hrep, self_mem_nhdsWithin] with z h₁ h₂ hz
    have h0 : z ≠ 0 := hz
    have hex : -(m : ℤ) - (-(k : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by dsimp [n]; omega
    rw [h₁, Pi.mul_apply, h₂, sub_zero, smul_eq_mul, Pi.mul_apply]
    calc
      _ = (z ^ (-(m : ℤ)) / z ^ (-(k : ℤ) + 1)) * (A z * H z) := by ring
      _ = _ := by rw [← zpow_sub₀ h0, hex, zpow_neg, zpow_natCast]; ring
  have hcoeff (j : ℕ) : complexResidue (fun z : ℂ ↦ ρ z * z ^ ((m : ℤ) - (j : ℤ) - 1)) 0 =
      iteratedDeriv j A 0 / (j.factorial : ℂ) := by
    refine (mem_sLocalThetaPoleBound_iff_residue_congr (h := fun z : ℂ ↦ A z / z ^ (j + 1)) ?_).trans
      (sLocalPrincipalPartCoeff_lower_formula_cauchy hA j)
    filter_upwards [hrep, self_mem_nhdsWithin] with z h₂ hz
    have h0 : z ≠ 0 := hz
    rw [h₂, sub_zero, smul_eq_mul, mul_right_comm, ← zpow_add₀ h0,
      show -(m : ℤ) + ((m : ℤ) - (j : ℤ) - 1) = -((j + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
    ring
  rw [sLocalPrincipalPartCoeff_translate_congr hmain,
    sLocalPrincipalPartCoeff_lower_formula_cauchy (hA.mul hH),
    iteratedDeriv_mul hA.contDiffAt hH.contDiffAt, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [hcoeff, Nat.cast_choose ℂ hjn]
  change _ = (iteratedDeriv j A 0 / (j.factorial : ℂ)) *
    (iteratedDeriv (n - j) H 0 / ((n - j).factorial : ℂ))
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hj' : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hd : ((n - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
  field_simp [hn, hj', hd]

/-- The unnormalized Fourier functional equation continued along a unitary norm chart. -/
private theorem sLocalPrincipalPartCoeff_lower_formula_fe (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    let c := twistₛ ((circleToComplex).comp χ)
    (fun z ↦ sLocalIdelicZFunction f (c z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalRhoFactor (c z) * sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (c z))) := by
  intro c
  let g := sAdeleSchwartzFourier f
  let d := twistₛ ((circleToComplex).comp χ⁻¹)
  have hd (z : ℂ) : dualₛ (c z) = d (1 - z) := sLocal_dual_chart χ z
  simp only [hd]
  apply meromorphic_eq_of_germ (fun z ↦ (sLocalIdelicZFunction_meromorphic f χ).meromorphicOn z trivial)
    (fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
      (((sLocalIdelicZFunction_meromorphic g χ⁻¹).meromorphicOn (1 - z) trivial).comp_analyticAt
        (g := fun u : ℂ ↦ 1 - u) (by fun_prop))) (z := 1 / 2)
  have hs : ∀ᶠ z : ℂ in 𝓝[≠] (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 := nhdsWithin_le_nhds
    ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by norm_num [mem_preimage, mem_Ioo]))
  filter_upwards [hs] with z hz
  have hpos : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
  change sLocalIdelicZFunction f (c z) = sLocalRhoFactor (c z) * sLocalIdelicZFunction g (d (1 - z))
  exact (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz.1, rfl⟩).trans <|
    (sLocalIdelicZetaIntegral_functionalEquation f χ z hz).trans <|
      congrArg (sLocalRhoFactor (c z) * ·) ((congrArg (sLocalIdelicZetaIntegral g) (hd z)).trans
        (sLocalIdelicZFunction_eq_integral g ⟨χ⁻¹, 1 - z, hpos, rfl⟩).symm)

/-- Paper: Theorem 7.2.1.4(2), p. 337.
Each lower coefficient is a convolution of Laurent coefficients of the correcting
factor with Taylor coefficients of the reflected zeta function of the Fourier test.
Deviation: The coefficient indexed by `k` has exponent `-k`. At `k = 0`, the last
summand of (7.2.1.14) uses the constant Laurent coefficient of the correcting
factor. Differentiation in the original chart includes the sign from reflection. -/
theorem sLocalPrincipalPartCoeff_lower_formula (c : Xₛ) (f : ℬₛ) (k : ℕ)
    (hk : k < sLocalRhoPoleOrder c) :
    let m := sLocalRhoPoleOrder c
    sLocalPrincipalPartCoeff c k f =
      ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ c z) *
          z ^ ((m : ℤ) - (j : ℤ) - 1)) 0 *
        (iteratedDeriv (m - k - j)
          (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z))) 0 /
          ((m - k - j).factorial : ℂ)) := by
  intro m
  let ρ : ℂ → ℂ := fun z ↦ sLocalRhoFactor (twistₛ c z)
  let H : ℂ → ℂ := fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z))
  let Z : ℂ → ℂ := fun z ↦ sLocalIdelicZFunction f (twistₛ c z)
  have hb := sLocalIdelicOrderBound_eq_neg_poleOrder c
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hk
  have hneg : sLocalIdelicOrderBound c < 0 := by
    rw [hb]
    exact_mod_cast (show -(m : ℤ) < 0 by omega)
  have hord : meromorphicOrderAt ρ 0 = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
    change min 0 (meromorphicOrderAt ρ 0) = _ at hb
    change min 0 (meromorphicOrderAt ρ 0) < 0 at hneg
    have hlt := (min_lt_iff.mp hneg).resolve_left (lt_irrefl _)
    simpa only [min_eq_right hlt.le] using hb
  obtain ⟨χ, a, hca⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let b := twistₛ ((circleToComplex).comp χ)
  have shift (z : ℂ) : twistₛ c z = b (z + a) := by
    rw [← hca]
    exact normTwist_normTwist mₛ hmₛ ((circleToComplex).comp χ) a z
  have hρ : MeromorphicAt ρ 0 := by
    have e : ρ = (fun u ↦ sLocalRhoFactor (b u)) ∘ (fun z ↦ z + a) :=
      funext fun z ↦ congrArg sLocalRhoFactor (shift z)
    rw [e]
    exact (sLocalRhoFactor_meromorphic χ (0 + a)).comp_analyticAt (g := fun z : ℂ ↦ z + a) (by fun_prop)
  have hnonpos : a.re ≤ 0 := le_of_not_gt fun h ↦ (not_le_of_gt hneg) (hca ▸ sLocalOrderBound_positive χ h)
  have hpos : 0 < (1 - a).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hH : AnalyticAt ℂ H 0 := by
    let d := twistₛ ((circleToComplex).comp χ⁻¹)
    let Y : ℂ → ℂ := fun u ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (d u)
    have hY : AnalyticAt ℂ Y (1 - a) :=
      sLocalZLaurentCoeff_continuous_linear_analytic (sAdeleSchwartzFourier f)
        ((circleToComplex).comp χ⁻¹) (1 - a) (sLocalOrderBound_positive χ⁻¹ hpos)
    have e : H = Y ∘ (fun z ↦ 1 - (z + a)) := by
      funext z
      change sLocalIdelicZFunction _ (dualₛ (twistₛ c z)) = _
      rw [shift]
      exact congrArg (sLocalIdelicZFunction (sAdeleSchwartzFourier f)) (sLocal_dual_chart χ (z + a))
    rw [e]
    exact hY.comp_of_eq (by fun_prop) (by simp)
  have hZ : Z =ᶠ[𝓝[≠] (0 : ℂ)] ρ * H := by
    have ht : Tendsto (fun z : ℂ ↦ z + a) (𝓝[≠] 0) (𝓝[≠] (0 + a)) :=
      ((Homeomorph.addRight a).map_punctured_nhds_eq 0).le
    filter_upwards [ht.eventually (nhdsNE_le_codiscrete _ (sLocalPrincipalPartCoeff_lower_formula_fe χ f))]
      with z hz
    change sLocalIdelicZFunction f (twistₛ c z) = sLocalRhoFactor (twistₛ c z) * H z
    dsimp only [H]
    rw [shift]
    exact hz
  exact sLocalPrincipalPartCoeff_lower_formula_product (ρ := ρ) (H := H) (Z := Z) hk hρ hord hH hZ

section LocalPolesGlobalZeros

local notation "K𝔽(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "globalUnitary(" χ ")" => ((circleToComplex).comp χ : QuasiCharacter C𝔽)
local notation "globalNormOne(" χ ")" =>
  ((χ).comp (⟨(m𝔽).ker.subtype, continuous_subtype_val⟩ : (m𝔽).ker →ₜ* C𝔽)
    : PontryaginDual (m𝔽).ker)
local notation "localChart(" χ ", " h ")" =>
  twistₛ (sIdeleRestriction F S ⟨globalUnitary(χ), h⟩)
local notation "outsideS(" h₀ ", " hχ ")" => (fun v hv ↦ hχ v (fun hv₀ ↦ hv (h₀ hv₀)))

-- ERRATA.md I223–I225 describe the corrections used below. Use Weil's
-- insertion identity for the orders, the meromorphic converse for the global
-- range, and the isomorphism of §6.2.1.1(2) for the local range pullback.

local notation "chartₛ(" η ")" => twistₛ ((circleToComplex).comp η)
local notation "gChart(" χ ", " f ")" =>
  (fun z : ℂ ↦ globalIdelicZFunction (f : ℬ𝔽) (ideleClassNormTwist χ z))

/-- Selected top coefficients vanish exactly when the centered germ has the reduced pole bound. -/
private theorem sLocalPrincipalValue_coeff_order (f : ℬₛ) (c : Xₛ) (n : ℕ) :
    (∀ k : ℕ, sLocalRhoPoleOrder c - n < k → k ≤ sLocalRhoPoleOrder c →
      sLocalPrincipalPartCoeff c k f = 0) ↔
      (-(sLocalRhoPoleOrder c - n : ℕ) : ℤ) ≤
        meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 := by
  let Z (z : ℂ) := sLocalIdelicZFunction f (twistₛ c z)
  let m := sLocalRhoPoleOrder c
  let d := m - n
  have hmer : MeromorphicAt Z 0 := (sLocalZ_centered f c).1
  have hm : (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z 0 :=
    (sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans (sLocalZ_centered f c).2.1
  constructor
  · intro hz
    change ((-(d : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z 0
    by_contra! hbad
    have hN : d < (-(meromorphicOrderAt Z 0).untop₀).toNat := by
      cases h : meromorphicOrderAt Z 0 with
      | top => simp [h] at hbad
      | coe j =>
        have h' : j < -(d : ℤ) := WithTop.coe_lt_coe.mp (h ▸ hbad)
        rw [WithTop.untop₀_coe]
        omega
    let k := (-(meromorphicOrderAt Z 0).untop₀).toNat
    have hk : k ≤ m := by
      cases h : meromorphicOrderAt Z 0 with
      | top => simp [k, h]
      | coe j =>
        have h' : -(m : ℤ) ≤ j := WithTop.coe_le_coe.mp (h ▸ hm)
        simp only [k, h, WithTop.untop₀_coe]
        omega
    apply mem_sLocalThetaPoleBound_iff_leading hmer (show 0 < k from Nat.zero_lt_of_lt hN) rfl
    exact hz k hN hk
  · intro hz k hk _
    apply sLocalPrincipalPartCoeff_ne_zero_imp_pole_vanish hmer k (Nat.zero_lt_of_lt hk)
    cases h : meromorphicOrderAt Z 0 with
    | top => simpa [h] using Nat.zero_lt_of_lt hk
    | coe j =>
      have hj : -(d : ℤ) ≤ j := WithTop.coe_le_coe.mp (h ▸ hz)
      simp only [WithTop.untop₀_coe]
      omega

/-- The local restriction is a unitary base point, and its norm chart covers its component. -/
private theorem sLocalPrincipalValue_chart (χ : PontryaginDual C𝔽)
    (hS : globalUnitary(χ) ∈ unramifiedOutside F S) :
    let hω : NormOneCharacterUnramifiedOutside (globalNormOne(χ)) S :=
      ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S (globalNormOne(χ)) hω
    ∃ η : PontryaginDual Jₛ,
      (∀ z, localChart(χ, hS) z = chartₛ(η) z) ∧
      (∀ z, onComponent(localChart(χ, hS) z, ωₛ)) ∧
      (∀ c : Xₛ, onComponent(c, ωₛ) → ∃ z, localChart(χ, hS) z = c) := by
  intro hω ωₛ
  let c₀ := sIdeleRestriction F S ⟨globalUnitary(χ), hS⟩
  have hn (x : Jₛ) : ‖c₀ x‖ = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [show c₀ (QuotientGroup.mk g) =
      globalUnitary(χ) (QuotientGroup.mk (sIdeleInsertion F S g)) from sIdeleRestriction_mk F S _ g]
    exact Circle.norm_coe _
  let η : PontryaginDual Jₛ :=
    { toFun := fun x ↦ ⟨c₀ x, mem_sphere_zero_iff_norm.mpr (hn x)⟩
      map_one' := Subtype.ext (map_one c₀)
      map_mul' x y := Subtype.ext (map_mul c₀ x y)
      continuous_toFun := c₀.continuous.subtype_mk _ }
  have hη : c₀ = (circleToComplex).comp η := ContinuousMonoidHom.ext fun _ ↦ rfl
  have hrest (x : J₁) : c₀ x.val = (ωₛ x : ℂ) :=
    (sLocalNormOneCharacter_eq_sIdeleRestriction (globalNormOne(χ))
      ⟨globalUnitary(χ), hS⟩ (fun _ ↦ rfl) x).symm
  refine ⟨η, fun z ↦ congrArg (fun c : Xₛ ↦ twistₛ c z) hη, ?_, ?_⟩
  · intro z
    apply ContinuousMonoidHom.ext
    intro x
    change c₀ x.val * ((((mₛ x.val).val : ℝ) : ℂ) ^ z) = (ωₛ x : ℂ)
    rw [show mₛ x.val = 1 from x.property, Units.val_one, NNReal.coe_one,
      Complex.ofReal_one, Complex.one_cpow, mul_one, hrest]
  · intro c hc
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨z, hz, -⟩ := existsUnique_complexPower (c.comp σ)
    obtain ⟨w, hw, -⟩ := existsUnique_complexPower (c₀.comp σ)
    refine ⟨z - w, ContinuousMonoidHom.ext fun g ↦ ?_⟩
    let t := mₛ g
    let k : J₁ := ⟨g / σ t, by change mₛ (g / σ t) = 1; rw [map_div, hσ]; exact div_self' _⟩
    have hg : k.val * σ t = g := div_mul_cancel _ _
    have hk : c k.val = c₀ k.val := (DFunLike.congr_fun hc k).trans (hrest k).symm
    let N : ℂ := ((t.val : ℝ) : ℂ)
    have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)
    have hval : c₀ (σ t) * N ^ (z - w) = c (σ t) := by
      rw [show c₀ (σ t) = N ^ w from hw t, show c (σ t) = N ^ z from hz t,
        ← Complex.cpow_add _ _ hN, show w + (z - w) = z by ring]
    change c₀ g * N ^ (z - w) = c g
    calc
      c₀ g * N ^ (z - w) = c₀ k.val * (c₀ (σ t) * N ^ (z - w)) := by
        rw [← mul_assoc, ← map_mul, hg]
      _ = c g := by rw [hval, ← hk, ← map_mul, hg]


private theorem sLocalPrincipalValue_euler_form (χ : PontryaginDual C𝔽) (v : Places) :
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

/-- Euler multipliers have simple roots on the imaginary axis and no other zeros. -/
private theorem sLocalPrincipalValue_exp_order (ℓ θ : ℝ) (hℓ : 0 < ℓ) (s : ℂ) :
    let E := fun z : ℂ ↦ 1 - Complex.exp (((-ℓ : ℝ) : ℂ) * z + (θ : ℂ) * Complex.I)
    AnalyticAt ℂ E s ∧ meromorphicOrderAt E s = (if E s = 0 then 1 else 0) ∧ (E s = 0 → s.re = 0) := by
  classical
  intro E
  let g (z : ℂ) := ((-ℓ : ℝ) : ℂ) * z + (θ : ℂ) * Complex.I
  have hg : HasDerivAt g ((-ℓ : ℝ) : ℂ) s := by
    simpa only [g, id_eq, mul_one] using
      (((hasDerivAt_id s).const_mul ((-ℓ : ℝ) : ℂ)).add_const ((θ : ℂ) * Complex.I))
  have hE : HasDerivAt E (-(Complex.exp (g s) * ((-ℓ : ℝ) : ℂ))) s := by
    change HasDerivAt ((fun _ : ℂ ↦ (1 : ℂ)) - fun z ↦ Complex.exp (g z)) _ s
    simpa only [zero_sub] using (hasDerivAt_const s (1 : ℂ)).sub hg.cexp
  have he : AnalyticAt ℂ E s := by dsimp [E]; fun_prop
  refine ⟨he, ?_, ?_⟩
  · by_cases hz : E s = 0
    · rw [ite_eq_left hz, he.meromorphicOrderAt_eq,
        he.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz]
      · rfl
      · rw [hE.deriv]
        exact neg_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero _) (by exact_mod_cast (neg_ne_zero.mpr hℓ.ne')))
    · rw [ite_eq_right hz, he.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hz]
  · intro hz
    have h := congrArg norm ((sub_eq_zero.mp (show 1 - Complex.exp (g s) = 0 from hz)).symm)
    rw [Complex.norm_exp, norm_one, ← Real.exp_zero] at h
    have hn := Real.exp_injective h
    simp [g, Complex.mul_re, Complex.add_re] at hn
    exact hn.resolve_left hℓ.ne'

open Classical in
/-- On the imaginary axis the completed global factor is a meromorphic unit,
except for its simple pole at the trivial quasi-character. -/
private theorem sLocalPrincipalValue_global_euler_order (χ : PontryaginDual C𝔽)
    (s : ℂ) (hs : s.re = 0) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s =
      ((if ideleClassNormTwist χ s = 1 then (-1 : ℤ) else 0) : WithTop ℤ) := by
  classical
  let L := continuedCompletedHeckeL χ
  let D := continuedCompletedHeckeL χ⁻¹
  obtain ⟨hL, hLe⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hDe⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hε0, hFE⟩ := completedHeckeL_continuation_functionalEquation χ L D hL hLe hD hDe
  have hrefl : meromorphicOrderAt L s = meromorphicOrderAt D (1 - s) := by
    rw [← meromorphicOrderAt_comp_of_deriv_ne_zero (f := D) (g := fun z : ℂ ↦ 1 - z)
      (x := s) (by fun_prop) (by simp)]
    rw [show D ∘ (fun z : ℂ ↦ 1 - z) = ε * L from funext hFE]
    exact (meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hε0 s)).symm
  have hnonpos : meromorphicOrderAt L s ≤ 0 := by
    rw [hrefl]
    by_contra! hbad
    have hre : (1 - s).re = 1 := by simp [hs]
    simpa only [hre, lt_self_iff_false] using
      completedHeckeL_continuation_zeros χ⁻¹ D hD hDe (by rw [hre]; exact zero_lt_one) hbad
  have hone : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext x
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  by_cases hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨ht, h0, -, hhol⟩, -⟩ := completedHeckeL_continuation_simplePoles χ L hL hLe hk
    let b := Complex.I * (t : ℂ)
    have hbχ : ideleClassNormTwist χ b = 1 := by
      have h := ideleClassNormTwist_add_of_eq ht b
      simpa [b, hone] using h
    by_cases hsb : s = b
    · rw [hsb, ite_eq_left hbχ]
      exact h0
    · have htriv : ideleClassNormTwist χ s ≠ 1 :=
        fun h ↦ hsb (globalUnitaryChart_injective χ (h.trans hbχ.symm))
      rw [ite_eq_right htriv]
      apply le_antisymm hnonpos
      have hsb1 : s ≠ 1 + b := by
        intro he
        have := congrArg Complex.re he
        simp [hs, b, Complex.mul_re] at this
      exact (hhol s (by simp [b] at hsb hsb1 ⊢; exact ⟨hsb, hsb1⟩)).meromorphicOrderAt_nonneg
  · have htriv : ideleClassNormTwist χ s ≠ 1 := by
      intro hc
      apply hk
      ext x
      have h := DFunLike.congr_fun hc x.val
      change (χ x.val : ℂ) * (((m𝔽 x.val).val : ℝ) : ℂ) ^ s = 1 at h
      rw [show m𝔽 x.val = 1 from x.property, Units.val_one, NNReal.coe_one,
        Complex.ofReal_one, Complex.one_cpow, mul_one] at h
      exact h
    rw [ite_eq_right htriv]
    exact le_antisymm hnonpos ((completedHeckeL_continuation_entire χ L hL hLe hk).analyticAt s).meromorphicOrderAt_nonneg

private theorem sLocalPrincipalValue_centered_order (χ : PontryaginDual C𝔽)
    (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (s : ℂ) (H : Xₛ → ℂ) :
    meromorphicOrderAt (fun w ↦ H (twistₛ (localChart(χ, hS) s) w)) 0 =
      meromorphicOrderAt (fun w ↦ H (localChart(χ, hS) w)) s := by
  have h : (fun w ↦ H (twistₛ (localChart(χ, hS) s) w)) =
      (fun w ↦ H (localChart(χ, hS) w)) ∘ (· + s) := by
    funext z
    dsimp only [Function.comp_apply]
    rw [normTwist_normTwist]
  rw [h, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]

private theorem sLocalPrincipalValue_chart_apply (χ : PontryaginDual C𝔽)
    (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (s : ℂ) (g : (SAdeleRing F S)ˣ) :
    localChart(χ, hS) s (QuotientGroup.mk g) =
      ideleClassNormTwist χ s (QuotientGroup.mk (sIdeleInsertion F S g)) := by
  change sIdeleRestriction F S ⟨globalUnitary(χ), hS⟩ (QuotientGroup.mk g) *
      _ ^ s = _
  rw [sIdeleRestriction_mk]
  simp only [sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
  rfl

private theorem sLocalPrincipalValue_chart_finite (χ : PontryaginDual C𝔽)
    (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (s : ℂ) (v : S) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (localChart(χ, hS) s)) =
      finiteHeckeEulerFactor χ v.val s := by
  classical
  rw [← finiteLocalEulerFactor_eq_finiteHeckeEulerFactor]
  congr 1
  apply ContinuousMonoidHom.ext
  intro x
  let g := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)).symm
    (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))
  change localChart(χ, hS) s (QuotientGroup.mk g) =
    ideleClassNormTwist χ s (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x))
  rw [sLocalPrincipalValue_chart_apply, show sIdeleInsertion F S g = _ from sIdeleInsertion_finiteUnit v x]

private theorem sLocalPrincipalValue_factor_order (χ : PontryaginDual C𝔽)
    (v : Places) (s : ℂ) :
    let E := fun z ↦ (finiteHeckeEulerFactor χ v z)⁻¹
    AnalyticAt ℂ E s ∧
      meromorphicOrderAt E s = (if E s = 0 then 1 else 0) ∧ (E s = 0 → s.re = 0) := by
  classical
  rcases sLocalPrincipalValue_euler_form χ v with h | ⟨ℓ, hℓ, θ, h⟩
  · rw [h]
    refine ⟨analyticAt_const, ?_, ?_⟩
    · have h1 : (1 : ℂ → ℂ) s ≠ 0 := one_ne_zero
      rw [ite_eq_right h1]
      exact analyticAt_const.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h1
    · exact fun he ↦ (one_ne_zero he).elim
  · rw [h]
    exact sLocalPrincipalValue_exp_order ℓ θ hℓ s

open Classical in
private theorem sLocalPrincipalValue_multiplier_order {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (s : ℂ) :
    let E := reciprocalPartialHeckeEulerProduct χ T
    let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
    AnalyticAt ℂ E s ∧ meromorphicOrderAt E s = (n : WithTop ℤ) ∧
      (0 < n → s.re = 0) := by
  intro E n
  let e (v : Places) (z : ℂ) := (finiteHeckeEulerFactor χ v z)⁻¹
  let U := T.filter fun v ↦ e v s = 0
  have hU : U.card = n := by
    change U.card = ((sLocalFinitePolePlaces (localChart(χ, hS) s)).filter fun v ↦ v.val ∈ T).card
    rw [Finset.card_bij (fun (v : S) _ ↦ v.val) (t := U)]
    · intro v hv
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2, ?_⟩
      have hp := (Finset.mem_filter.mp
        (show v ∈ sLocalFinitePolePlaces (localChart(χ, hS) s) from (Finset.mem_filter.mp hv).1)).2
      rw [sLocalPrincipalValue_centered_order χ hS s
          (fun c ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c))] at hp
      have eq : (fun z ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (localChart(χ, hS) z))) =
          (e v.val)⁻¹ := funext fun z ↦ (sLocalPrincipalValue_chart_finite χ hS z v).trans (inv_inv _).symm
      rw [eq, meromorphicOrderAt_inv, (sLocalPrincipalValue_factor_order χ v.val s).2.1] at hp
      by_contra hp0
      simp [e, hp0] at hp
    · intro _ _ _ _ huv
      exact Subtype.ext huv
    · intro v hv
      obtain ⟨hvT, hv0⟩ := Finset.mem_filter.mp hv
      let w : S := ⟨v, hT hvT⟩
      refine ⟨w, Finset.mem_filter.mpr ⟨?_, hvT⟩, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [sLocalPrincipalValue_centered_order χ hS s
        (fun c ↦ finiteLocalEulerFactor w.val (sLocalFiniteRestriction w c))]
      have eq : (fun z ↦ finiteLocalEulerFactor w.val (sLocalFiniteRestriction w (localChart(χ, hS) z))) =
          (e v)⁻¹ := funext fun z ↦ (sLocalPrincipalValue_chart_finite χ hS z w).trans (inv_inv _).symm
      rw [eq, meromorphicOrderAt_inv, (sLocalPrincipalValue_factor_order χ v s).2.1]
      simp [e, hv0]
      decide
  have he (v : Places) : AnalyticAt ℂ (e v) s := (sLocalPrincipalValue_factor_order χ v s).1
  have ho : meromorphicOrderAt E s = (n : WithTop ℤ) := by
    change meromorphicOrderAt (fun z ↦ ∏ v ∈ T, e v z) s = (n : WithTop ℤ)
    rw [meromorphicOrderAt_fun_prod (fun v _ ↦ (he v).meromorphicAt), ← hU, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro v _
    simpa [e] using (sLocalPrincipalValue_factor_order χ v s).2.1
  refine ⟨T.analyticAt_fun_prod (fun v _ ↦ he v), ho, fun hn ↦ ?_⟩
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (hU.symm ▸ hn)
  exact (sLocalPrincipalValue_factor_order χ v s).2.2 (Finset.mem_filter.mp hv).2

private theorem sLocalPrincipalValue_global_chart_zero (χ : PontryaginDual C𝔽) :
    ideleClassNormTwist χ 0 = globalUnitary(χ) := by
  ext x
  change (χ x : ℂ) * _ ^ (0 : ℂ) = (χ x : ℂ)
  simp

private theorem sLocalPrincipalValue_multiplicity_le (T : Finset Places) (c : Xₛ) :
    sLocalFinitePoleMultiplicity T c ≤ sLocalRhoPoleOrder c := by
  classical
  rw [sLocalRhoPoleOrder_eq_card_polePlaces]
  exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)

private theorem sLocalPrincipalValue_chart_hecke_meromorphic (χ : PontryaginDual C𝔽)
    (hS : globalUnitary(χ) ∈ unramifiedOutside F S) :
    Meromorphic (fun s ↦ sLocalHeckeL (localChart(χ, hS) s)) := by
  classical
  have hS₀ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S :=
    sLocalPrincipalValue_global_chart_zero χ ▸ hS
  have heq : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS₀⟩ =
      sIdeleRestriction F S ⟨globalUnitary(χ), hS⟩ :=
    congrArg (sIdeleRestriction F S) (Subtype.ext (sLocalPrincipalValue_global_chart_zero χ))
  obtain ⟨η, hη, -, -⟩ := sLocalPrincipalValue_chart χ hS
  have h₀ : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS₀⟩ = chartₛ(η) 0 := by
    rw [heq, ← hη 0]
    ext x
    change sIdeleRestriction F S ⟨globalUnitary(χ), hS⟩ x =
      sIdeleRestriction F S ⟨globalUnitary(χ), hS⟩ x * ((((mₛ x).val : ℝ) : ℂ) ^ (0 : ℂ))
    simp
  have hfun : (fun s ↦ sLocalHeckeL (localChart(χ, hS) s)) =
      fun s ↦ heckeGammaFactor χ s * ∏ v : S, finiteHeckeEulerFactor χ v.val s := by
    funext s
    rw [hη]
    exact sLocalHeckeL_eq_partialEulerProduct η χ hS₀ h₀ s
  rw [hfun]
  intro s
  apply (meromorphic_heckeGammaFactor χ s).mul
  apply MeromorphicAt.fun_prod
  intro v _
  have h := (sLocalPrincipalValue_factor_order χ v.val s).1.meromorphicAt.inv
  have he : (fun z ↦ (finiteHeckeEulerFactor χ v.val z)⁻¹)⁻¹ = finiteHeckeEulerFactor χ v.val :=
    funext fun z ↦ inv_inv _
  exact he ▸ h

private theorem sLocalPrincipalValue_inserted_factor (χ : PontryaginDual C𝔽)
    (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (f : ℬₛ) :
    ∃ A : ℂ, A ≠ 0 ∧
      gChart(χ, sAdeleSchwartzToGlobal F S f) =ᶠ[codiscrete ℂ] (fun s ↦
        A * sLocalIdelicZFunction f (localChart(χ, hS) s) *
          (continuedCompletedHeckeL χ s / sLocalHeckeL (localChart(χ, hS) s))) := by
  classical
  let A := ∏ᶠ v : {v : Places // v ∉ S},
    (((finiteLocalMultiplicativeTamagawaMeasure F v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)
  refine ⟨A, ?_, ?_⟩
  · apply finprod_ne_zero
    intro v
    apply Complex.ofReal_ne_zero.mpr
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    apply (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.val).trans' zero_lt_one
  · have hS₀ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S :=
      sLocalPrincipalValue_global_chart_zero χ ▸ hS
    have heq : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hS₀⟩ =
        sIdeleRestriction F S ⟨globalUnitary(χ), hS⟩ :=
      congrArg (sIdeleRestriction F S) (Subtype.ext (sLocalPrincipalValue_global_chart_zero χ))
    obtain ⟨L, hL, hLe⟩ := finiteHeckeL_exists_continuation χ
    have hW := weilIdentity_unramifiedOutside_meromorphic S f χ hS₀ L hL
      (fun z hz ↦ hLe ⟨z, hz⟩)
    dsimp only at hW
    rw [heq] at hW
    let Y (s : ℂ) := continuedCompletedHeckeL χ s / sLocalHeckeL (localChart(χ, hS) s)
    have hY : MeromorphicOn Y univ := (continuedCompletedHeckeL_spec χ).1.meromorphicOn.div
      (sLocalPrincipalValue_chart_hecke_meromorphic χ hS).meromorphicOn
    have hN : heckeEulerProductOutside S χ hS₀ = toMeromorphicNFOn Y univ := by
      unfold heckeEulerProductOutside
      dsimp only
      rw [heq]
    have hE : MeromorphicOn (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) univ := by
      intro s hs
      apply MeromorphicAt.mul _ ((hL hs).meromorphicAt)
      apply MeromorphicAt.fun_prod
      intro v _
      exact (sLocalPrincipalValue_factor_order χ v s).1.meromorphicAt
    have hYE : (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * L z) =ᶠ[codiscrete ℂ] Y := by
      refine (toMeromorphicNFOn_eqOn_codiscrete hE).trans ?_
      rw [← heckeEulerProductOutside_eq_finite S χ hS₀ L hL hLe, hN]
      exact (toMeromorphicNFOn_eqOn_codiscrete hY).symm
    filter_upwards [hW, hYE] with z hz hq
    change globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ z) =
      A * sLocalIdelicZFunction f (localChart(χ, hS) z) * Y z
    rw [hz, ← hq]
    dsimp only [A, reciprocalPartialHeckeEulerProduct]
    ring

private theorem sLocalPrincipalValue_insertion_order {T : Finset Places}
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (f : ℬₛ)
    (s : ℂ) (hn : 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)) :
    let m := sLocalRhoPoleOrder (localChart(χ, hS) s)
    meromorphicOrderAt (gChart(χ, sAdeleSchwartzToGlobal F S f)) s =
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (localChart(χ, hS) z)) s +
        (meromorphicOrderAt (continuedCompletedHeckeL χ) s + (m : WithTop ℤ)) := by
  intro m
  obtain ⟨η, hη, -, -⟩ := sLocalPrincipalValue_chart χ hS
  have hL := sLocalHeckeL_poleOrder_eq S η s
  simp_rw [← hη] at hL
  rw [← sLocalPrincipalValue_centered_order χ hS s sLocalRhoFactor] at hL
  have hm : (0 : ℕ) < m := hn.trans_le (sLocalPrincipalValue_multiplicity_le T _)
  have he : min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor
      (twistₛ (localChart(χ, hS) s) z)) 0) = ((-(m : ℤ) : ℤ) : WithTop ℤ) :=
    sLocalIdelicOrderBound_eq_neg_poleOrder _
  have hneg : (((-(m : ℤ) : ℤ) : WithTop ℤ)) < 0 := by exact_mod_cast neg_neg_of_pos (Int.natCast_pos.mpr hm)
  have hLL : meromorphicOrderAt (fun z ↦ sLocalHeckeL (localChart(χ, hS) z)) s =
      ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
    rw [he] at hL
    have ho : ¬ 0 ≤ meromorphicOrderAt (fun z ↦ sLocalHeckeL (localChart(χ, hS) z)) s := by
      intro ha
      rw [min_eq_left ha] at hL
      exact (ne_of_gt hneg) hL
    rwa [min_eq_right (le_of_not_ge ho)] at hL
  obtain ⟨A, ha, hA⟩ := sLocalPrincipalValue_inserted_factor χ hS f
  rw [meromorphicOrderAt_congr (nhdsNE_le_codiscrete _ hA)]
  have hZ : MeromorphicAt (fun z ↦ sLocalIdelicZFunction f (localChart(χ, hS) z)) s := by
    simp_rw [hη]
    exact (sLocalIdelicZFunction_meromorphic f η (mem_univ s)).meromorphicAt
  have hc := ((continuedCompletedHeckeL_spec χ).1 (mem_univ s)).meromorphicAt
  have hd := sLocalPrincipalValue_chart_hecke_meromorphic χ hS s
  change meromorphicOrderAt (((fun _ : ℂ ↦ A) * (fun z ↦ sLocalIdelicZFunction f (localChart(χ, hS) z))) *
    (continuedCompletedHeckeL χ / fun z ↦ sLocalHeckeL (localChart(χ, hS) z))) s = _
  rw [meromorphicOrderAt_mul (analyticAt_const.meromorphicAt.mul hZ) (hc.div hd),
    meromorphicOrderAt_mul_of_ne_zero analyticAt_const ha, meromorphicOrderAt_div hc hd, hLL]
  rw [sub_eq_add_neg]
  have hneg' : -((-(m : ℤ) : ℤ) : WithTop ℤ) = (m : WithTop ℤ) := by
    change ((-(-(m : ℤ)) : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ)
    rw [neg_neg]
  rw [hneg']

private theorem sLocalPrincipalValue_bound_shift (o : WithTop ℤ) (m n : ℕ)
    (hn : 0 < n) (hm : n ≤ m) (e : Prop) [Decidable e] :
    ((-(m - n : ℕ) : ℤ) : WithTop ℤ) ≤ o ↔
      ((if e then n - 1 else n : ℕ) : WithTop ℤ) ≤
        o + (((if e then (-1 : ℤ) else 0) : WithTop ℤ) + (m : WithTop ℤ)) := by
  cases o using WithTop.recTopCoe with
  | top => simp
  | coe j =>
    by_cases h : e
    · rw [ite_eq_left h, ite_eq_left h]
      change ((-(m - n : ℕ) : ℤ) : WithTop ℤ) ≤ (j : WithTop ℤ) ↔
        (((n - 1 : ℕ) : ℤ) : WithTop ℤ) ≤
          ((j : ℤ) : WithTop ℤ) + (((-1 : ℤ) : WithTop ℤ) + (((m : ℤ) : WithTop ℤ)))
      simp only [← WithTop.coe_add, WithTop.coe_le_coe]
      omega
    · rw [ite_eq_right h, ite_eq_right h, zero_add]
      change ((-(m - n : ℕ) : ℤ) : WithTop ℤ) ≤ (j : WithTop ℤ) ↔
        (((n : ℤ) : WithTop ℤ)) ≤ (j : WithTop ℤ) + (((m : ℤ) : WithTop ℤ))
      simp only [← WithTop.coe_add, WithTop.coe_le_coe]
      omega

open Classical in
private theorem sLocalPrincipalValue_tfae_one_two {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (f : ℬₛ) :
    let hω : NormOneCharacterUnramifiedOutside (globalNormOne(χ)) S :=
      ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S (globalNormOne(χ)) hω
    (∀ c : Xₛ, onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity T c →
      ∀ k : ℕ, sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c < k →
      k ≤ sLocalRhoPoleOrder c → sLocalPrincipalPartCoeff c k f = 0) ↔
    (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) →
      let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
      ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
        meromorphicOrderAt (gChart(χ, sAdeleSchwartzToGlobal F S f)) s) := by
  intro hω ωₛ
  obtain ⟨_, _, hcov, hsurj⟩ := sLocalPrincipalValue_chart χ hS
  have horder (s : ℂ) (hn : 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)) :
      let c := localChart(χ, hS) s
      let n := sLocalFinitePoleMultiplicity T c
      let m := sLocalRhoPoleOrder c
      (∀ k : ℕ, m - n < k → k ≤ m → sLocalPrincipalPartCoeff c k f = 0) ↔
        ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
          meromorphicOrderAt (gChart(χ, sAdeleSchwartzToGlobal F S f)) s := by
    intro c n m
    have hre := (sLocalPrincipalValue_multiplier_order hT χ hS s).2.2 hn
    rw [sLocalPrincipalValue_coeff_order, sLocalPrincipalValue_centered_order χ hS s (sLocalIdelicZFunction f),
      sLocalPrincipalValue_insertion_order χ hS f s hn,
      sLocalPrincipalValue_global_euler_order χ s hre]
    exact sLocalPrincipalValue_bound_shift _ m n hn (sLocalPrincipalValue_multiplicity_le T c) _
  constructor
  · intro h s hn
    exact (horder s hn).mp (h _ (hcov s) hn)
  · intro h c hc hn
    obtain ⟨s, rfl⟩ := hsurj c hc
    exact (horder s hn).mpr (h s hn)

/-- Equality on the chart's half-plane of convergence determines the entire meromorphic chart. -/
private theorem sLocalPrincipalValue_chart_unique {Z W : ℂ → ℂ}
    (hZ : MeromorphicNFOn Z univ) (hW : MeromorphicNFOn W univ)
    (h : ∀ s : ℂ, 1 < s.re → Z s = W s) : Z = W := by
  have htop : meromorphicOrderAt (Z - W) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ sub_eq_zero.mpr (h s hs)
  funext s
  have ho := (hZ.meromorphicOn.sub hW.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ s) htop
  have hEq : Z =ᶠ[𝓝[≠] s] W := (meromorphicOrderAt_eq_top_iff.mp ho).mono fun _ h ↦ sub_eq_zero.mp h
  exact (((hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hW (mem_univ s))).mp hEq).eq_of_nhds

/-- A homogeneous class determines its entire meromorphic chart. -/
private theorem sLocalPrincipalValue_chart_eq_of_class (χ : PontryaginDual C𝔽)
    (f g : ℬ𝔽) (h : (K𝔽(globalNormOne(χ))).mkQ f = (K𝔽(globalNormOne(χ))).mkQ g) :
    gChart(χ, f) = gChart(χ, g) := by
  apply sLocalPrincipalValue_chart_unique (globalIdelicZFunction_meromorphic f χ)
    (globalIdelicZFunction_meromorphic g χ)
  intro s hs
  let z : {c : QuasiCharacter C𝔽 // 0 ≤ globalIdelicOrderBound c} :=
    ⟨ideleClassNormTwist χ s, globalOrderBound_rightHalf χ hs⟩
  have hk : f - g ∈ K𝔽(globalNormOne(χ)) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (K𝔽(globalNormOne(χ))).mkQ (f - g) = 0
    rw [map_sub, h, sub_self]
  have hrest (u : (m𝔽).ker) :
      normOneRestriction m𝔽 z.val u = (globalNormOne(χ) u : ℂ) := by
    change (χ u.val : ℂ) * ((((m𝔽 u.val).val : ℝ) : ℂ) ^ s) = (χ u.val : ℂ)
    rw [show m𝔽 u.val = 1 from u.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
  have hz := (mem_homogeneousAdelicTheta_ker_iff (globalNormOne(χ)) (f - g)).mp hk z hrest
  rw [map_sub] at hz
  change gChart(χ, f) s - gChart(χ, g) s = 0 at hz
  exact sub_eq_zero.mp hz

private theorem sLocalPrincipalValue_chart_ne_norm (χ : PontryaginDual C𝔽) (s : ℂ)
    (hs : s.re = 0) : ideleClassNormTwist χ s ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 := by
  intro h
  let t : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F t)
  have hg : m𝔽 g = t := canonicalIdeleNormSection_rightInverse F t
  have he := congrArg norm (DFunLike.congr_fun h g)
  rw [ideleClassNormTwist_one_one] at he
  change ‖(χ g : ℂ) * ((((m𝔽 g).val : ℝ) : ℂ) ^ s)‖ = ‖(((m𝔽 g).val : ℝ) : ℂ)‖ at he
  rw [hg, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr t.zero_lt), hs, Real.rpow_zero] at he
  norm_num [t] at he

open Classical in
private theorem sLocalPrincipalValue_four_two {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (f : ℬ𝔽)
    (hg : ∃ g : ℬ𝔽, (K𝔽(globalNormOne(χ))).mkQ (adelePrincipalValue F T g) =
      (K𝔽(globalNormOne(χ))).mkQ f) (s : ℂ) :
    let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
    0 < n → ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
      meromorphicOrderAt (gChart(χ, f)) s := by
  intro n hn
  obtain ⟨g, hg⟩ := hg
  obtain ⟨hE, hEord, haxis⟩ := sLocalPrincipalValue_multiplier_order hT χ hS s
  rw [← sLocalPrincipalValue_chart_eq_of_class χ _ _ hg]
  rw [meromorphicOrderAt_congr (nhdsNE_le_codiscrete s (globalPrincipalValueConverse_mellin T χ g))]
  change _ ≤ meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ T * gChart(χ, g)) s
  rw [meromorphicOrderAt_mul hE.meromorphicAt
    ((globalIdelicZFunction_meromorphic g χ (mem_univ s)).meromorphicAt), hEord]
  by_cases htriv : ideleClassNormTwist χ s = 1
  · rw [ite_eq_left htriv]
    have he : ((n - 1 : ℕ) : WithTop ℤ) = (n : WithTop ℤ) + (-1 : WithTop ℤ) := by
      change (((n - 1 : ℕ) : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
      omega
    rw [he]
    exact add_le_add_right ((globalIdelicZFunction_poles g χ).2 s) (n : WithTop ℤ)
  · rw [ite_eq_right htriv]
    have hA := (globalIdelicZFunction_poles g χ).1 s
      ⟨htriv, sLocalPrincipalValue_chart_ne_norm χ s (haxis hn)⟩
    simpa only [add_zero] using
      add_le_add_right hA.meromorphicOrderAt_nonneg (n : WithTop ℤ)


section
open Complex
/-- Division by one vertical periodic Euler factor preserves rapid decay on
closed strips once the quotient is entire. -/
private theorem schwartzBergman_univ_div_exp (B : SchwartzBergman (univ : Set ℝ))
    (u : ℂ → ℂ) (hu : Differentiable ℂ u) {ℓ θ : ℝ} (hℓ : 0 < ℓ)
    (h : ∀ z, B.val z = (1 - Complex.exp (((-ℓ : ℝ) : ℂ) * z + (θ : ℂ) * Complex.I)) * u z) :
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
  obtain ⟨M, hM⟩ := B.property.2.2 L R hLR.le (subset_univ _) N
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
      change ‖w ^ N * B.val w‖ ≤ M at he
      have heq : w ^ N * B.val w = (w ^ N * u w) * (1 - Complex.exp (e w)) := by
        rw [h w]; dsimp [e]; ring
      rwa [heq, norm_mul] at he
    exact (le_div_iff₀ hδ).mpr ((mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans hprod)
  · rw [hcl]
    exact ⟨hzRe, hj'.le, hk'.le⟩

/-- An entire quotient of a Schwartz–Bergman function by a finite product of
vertical periodic Euler factors still decays rapidly on closed strips. -/
private theorem schwartzBergman_univ_div_prod_exp {ι : Type*} (S : Finset ι) (A : ι → ℂ → ℂ)
    (hA : ∀ i ∈ S, A i = 1 ∨ ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ θ : ℝ,
      A i = fun z ↦ 1 - Complex.exp (((-ℓ : ℝ) : ℂ) * z + (θ : ℂ) * Complex.I))
    (B : SchwartzBergman (univ : Set ℝ)) (u : ℂ → ℂ)
    (hu : Differentiable ℂ u) (h : ∀ z, B.val z = (∏ i ∈ S, A i z) * u z) :
    u ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  classical
  induction S using Finset.induction_on generalizing B with
  | empty =>
    have he : B.val = u := funext fun z ↦ by simpa using h z
    exact he ▸ B.property
  | @insert i S hi ih =>
    have hAS := fun j (hj : j ∈ S) ↦ hA j (Finset.mem_insert_of_mem hj)
    let v (z : ℂ) := (∏ j ∈ S, A j z) * u z
    have hdiv (z : ℂ) : B.val z = A i z * v z := by
      simpa only [Finset.prod_insert hi, mul_assoc, v] using h z
    rcases hA i (Finset.mem_insert_self _ _) with hOne | ⟨ℓ, hℓ, θ, hθ⟩
    · apply ih hAS B
      simpa only [hOne, Pi.one_apply, one_mul, v] using hdiv
    · have hd (j : ι) (hj : j ∈ S) : Differentiable ℂ (A j) := by
        rcases hAS j hj with he | ⟨_, _, _, he⟩ <;> rw [he] <;> fun_prop
      have hv : Differentiable ℂ v := (Differentiable.fun_finsetProd hd).mul hu
      have hSB := schwartzBergman_univ_div_exp B v hv hℓ (hθ ▸ hdiv)
      exact ih hAS (⟨v, hSB⟩ : SchwartzBergman (univ : Set ℝ)) (fun _ ↦ rfl)


end

open Classical in
private theorem sLocalPrincipalValue_regularized_global (χ : PontryaginDual C𝔽) (t : ℝ)
    (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist 1 ((t : ℂ) * Complex.I))
    (haxis : ∀ s : ℂ, s.re = 0 → meromorphicOrderAt (continuedCompletedHeckeL χ) s =
      ((if ideleClassNormTwist χ s = 1 then (-1 : ℤ) else 0) : WithTop ℤ)) :
    let b := (t : ℂ) * Complex.I
    let p (s : ℂ) := (s + b) * (1 - s - b)
    let G := toMeromorphicNFOn (p * continuedCompletedHeckeL χ) univ
    Differentiable ℂ G ∧
      (∀ s : ℂ, s.re = 0 → meromorphicOrderAt p s =
        if ideleClassNormTwist χ s = 1 then (1 : WithTop ℤ) else 0) ∧
      ∀ s : ℂ, s.re = 0 → meromorphicOrderAt G s = 0 := by
  classical
  let b := (t : ℂ) * Complex.I
  let p (s : ℂ) := (s + b) * (1 - s - b)
  let L := continuedCompletedHeckeL χ
  let G := toMeromorphicNFOn (p * L) univ
  change Differentiable ℂ G ∧ (∀ s : ℂ, s.re = 0 → meromorphicOrderAt p s = _) ∧ _
  obtain ⟨hL, hLe⟩ := continuedCompletedHeckeL_spec χ
  have hone : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext x
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hbχ : ideleClassNormTwist χ (-b) = 1 := by
    simpa [b, hone] using ideleClassNormTwist_add_of_eq ht (-b)
  have hp (s : ℂ) : AnalyticAt ℂ p s := by dsimp [p]; fun_prop
  constructor
  · let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    have hτ : Function.RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
    have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
    have hx : hphase.exists.choose = t := by
      refine hphase.unique hphase.exists.choose_spec ?_
      intro u
      have he := DFunLike.congr_fun ht (QuotientGroup.mk (τ u))
      change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
        1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) at he
      rwa [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    have hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
      ext x
      have he := DFunLike.congr_fun hbχ x.val
      change (χ x.val : ℂ) * ((((ideleClassNorm F x.val).val : ℝ) : ℂ) ^ (-b)) = 1 at he
      rw [show ideleClassNorm F x.val = 1 from x.property, Units.val_one, NNReal.coe_one,
        Complex.ofReal_one, Complex.one_cpow, mul_one] at he
      exact he
    have h := regularizedCompletedHeckeL_differentiable χ τ hτ L hL hLe
    simpa only [G, p, b, Pi.mul_def, hx, ite_eq_left hk, pow_one] using h
  have horder (s : ℂ) (hs : s.re = 0) : meromorphicOrderAt p s =
      if ideleClassNormTwist χ s = 1 then (1 : WithTop ℤ) else 0 := by
    by_cases hs₀ : s = -b
    · subst s
      rw [ite_eq_left hbχ, (hp _).meromorphicOrderAt_eq]
      have hd (z : ℂ) : HasDerivAt p ((1 - z - b) - (z + b)) z := by
        simpa [p, sub_eq_add_neg] using ((hasDerivAt_id z).add_const b).fun_mul
          (((hasDerivAt_const z (1 : ℂ)).fun_sub (hasDerivAt_id z)).sub_const b)
      rw [(hp _).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [p])
        (by rw [(hd _).deriv]; ring_nf; norm_num)]
      norm_num
    · have hχ : ideleClassNormTwist χ s ≠ 1 :=
        fun h ↦ hs₀ (globalUnitaryChart_injective χ (h.trans hbχ.symm))
      rw [ite_eq_right hχ]
      apply (hp s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      refine mul_ne_zero (fun he ↦ hs₀ (eq_neg_of_add_eq_zero_left he)) ?_
      intro he
      have h := congrArg Complex.re he
      simp [hs, b, Complex.mul_re] at h
  refine ⟨horder, ?_⟩
  intro s hs
  have hmer : MeromorphicOn (p * L) univ :=
    fun z hz ↦ (hp z).meromorphicAt.mul (hL hz).meromorphicAt
  rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ s),
    meromorphicOrderAt_mul (hp s).meromorphicAt (hL (mem_univ s)).meromorphicAt,
    horder s hs, haxis s hs]
  split_ifs <;> norm_num

/-- Meromorphic normal form gives an entire quotient when the denominator has
finite order everywhere and the numerator has at least that order. -/
private theorem sLocalPrincipalValue_divide_entire {u E : ℂ → ℂ}
    (hu : Differentiable ℂ u) (hE : Differentiable ℂ E)
    (hfin : ∀ s, meromorphicOrderAt E s ≠ ⊤)
    (hord : ∀ s, meromorphicOrderAt E s ≤ meromorphicOrderAt u s) :
    ∃ v : ℂ → ℂ, Differentiable ℂ v ∧ ∀ s, u s = E s * v s := by
  let Q := u / E
  have hQ : MeromorphicOn Q univ := fun s _ ↦
    (hu.analyticAt s).meromorphicAt.div (hE.analyticAt s).meromorphicAt
  let v := toMeromorphicNFOn Q univ
  have hv : Differentiable ℂ v := by
    intro s
    apply AnalyticAt.differentiableAt
    apply (meromorphicNFOn_toMeromorphicNFOn Q univ (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hQ (mem_univ s),
      meromorphicOrderAt_div (hu.analyticAt s).meromorphicAt (hE.analyticAt s).meromorphicAt]
    have hle := hord s
    have ht := hfin s
    generalize meromorphicOrderAt E s = a at hle ht ⊢
    cases a using WithTop.recTopCoe with
    | top => contradiction
    | coe a =>
      cases b : meromorphicOrderAt u s using WithTop.recTopCoe with
      | top => simp
      | coe b =>
        rw [b] at hle
        exact WithTop.coe_le_coe.mpr (sub_nonneg.mpr (WithTop.coe_le_coe.mp hle))
  refine ⟨v, hv, fun s ↦ ?_⟩
  by_cases h : E s = 0
  · have hne : meromorphicOrderAt E s ≠ 0 :=
      fun ho ↦ ((hE.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp ho) h
    have hp : 0 < meromorphicOrderAt u s :=
      (lt_of_le_of_ne (hE.analyticAt s).meromorphicOrderAt_nonneg hne.symm).trans_le (hord s)
    have hzero : u s = 0 := by
      by_contra h'
      exact hp.ne' ((hu.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h')
    rw [h, hzero, zero_mul]
  · dsimp only [v]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQ (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr ((hu.analyticAt s).div (hE.analyticAt s) h).meromorphicNFAt]
    exact (mul_div_cancel₀ _ h).symm

private theorem sLocalPrincipalValue_chart_unit_normOne (χ : PontryaginDual C𝔽) (s : ℂ)
    (hs : ideleClassNormTwist χ s = 1) : globalNormOne(χ) = 1 := by
  apply PontryaginDual.ext
  intro u
  apply Subtype.ext
  have he := DFunLike.congr_fun hs u.val
  change (χ u.val : ℂ) * ((((m𝔽 u.val).val : ℝ) : ℂ) ^ s) = 1 at he
  rw [show m𝔽 u.val = 1 from u.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one,
    Complex.one_cpow, mul_one] at he
  exact he

private theorem sLocalPrincipalValue_nontrivial_range {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S)
    (hω : globalNormOne(χ) ≠ 1) (f : ℬ𝔽)
    (hf : ∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) →
      (sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) : WithTop ℤ) ≤
        meromorphicOrderAt (gChart(χ, f)) s) :
    ∃ g : ℬ𝔽, (K𝔽(globalNormOne(χ))).mkQ (adelePrincipalValue F T g) =
      (K𝔽(globalNormOne(χ))).mkQ f := by
  obtain ⟨M, hM, hev, hrange⟩ := globalConverse_nontrivial χ hω
  obtain ⟨P, _, hpval, hPrange⟩ := globalPrincipalValueConverse_nontrivial T χ hω
  let q := (K𝔽(globalNormOne(χ))).mkQ
  have hr : M (q f) ∈ range M := ⟨q f, rfl⟩
  rw [hrange] at hr
  obtain ⟨u, hu, he⟩ := hr
  let L := continuedCompletedHeckeL χ
  let E := reciprocalPartialHeckeEulerProduct χ T
  have H (s : ℂ) := sLocalPrincipalValue_multiplier_order hT χ hS s
  have hchart : gChart(χ, f) = L * u := funext fun s ↦ (hev f s).symm.trans (he s)
  have hord (s : ℂ) : meromorphicOrderAt E s ≤ meromorphicOrderAt u s := by
    let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
    rw [(H s).2.1]
    by_cases hn : 0 < n
    · have hunit := sLocalPrincipalValue_global_euler_order χ s ((H s).2.2 hn)
      have hx : ideleClassNormTwist χ s ≠ 1 :=
        fun h ↦ hω (sLocalPrincipalValue_chart_unit_normOne χ s h)
      rw [ite_eq_right hx] at hunit
      have hm := hf s hn
      rw [hchart, meromorphicOrderAt_mul ((continuedCompletedHeckeL_spec χ).1 (mem_univ s)).meromorphicAt
        (hu.analyticAt s).meromorphicAt, hunit, zero_add] at hm
      exact hm
    · simpa [n, Nat.eq_zero_of_not_pos hn] using (hu.analyticAt s).meromorphicOrderAt_nonneg
  obtain ⟨v, hv, hdiv⟩ := sLocalPrincipalValue_divide_entire hu (fun s ↦ (H s).1.differentiableAt)
    (fun s ↦ by rw [(H s).2.1]; simp) hord
  have hP : M (q f) ∈ range P := by
    rw [hPrange]
    refine ⟨v, hv, fun s ↦ ?_⟩
    rw [he, hdiv]
    exact (mul_left_comm _ _ _).symm.trans (mul_assoc _ _ _).symm
  obtain ⟨⟨_, ⟨g, rfl⟩⟩, hg⟩ := hP
  refine ⟨g, hM.injective ?_⟩
  apply Subtype.ext
  funext s
  exact (hev _ s).trans ((hpval g s).symm.trans (congrArg (fun b : SchwartzBergman (univ : Set ℝ) ↦ b.val s) hg))

private theorem sLocalPrincipalValue_normal_form_eq {Z W : ℂ → ℂ}
    (hZ : MeromorphicNFOn Z univ) (hW : MeromorphicNFOn W univ)
    (h : Z =ᶠ[codiscrete ℂ] W) : Z = W := by
  funext s
  exact (((hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hW (mem_univ s))).mp
    (nhdsNE_le_codiscrete s h)).eq_of_nhds

local notation "PVPoly(" t ")" =>
  (fun z : ℂ ↦ (z + (t : ℂ) * Complex.I) * (1 - z - (t : ℂ) * Complex.I))
local notation "PVGen(" χ ", " t ")" =>
  toMeromorphicNFOn (PVPoly(t) * continuedCompletedHeckeL χ) univ

open Classical in
private theorem sLocalPrincipalValue_trivial_range {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S)
    (t : ℝ) (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual C𝔽) ((t : ℂ) * Complex.I))
    (hGdiff : Differentiable ℂ (PVGen(χ, t)))
    (hGord : ∀ s : ℂ, s.re = 0 → meromorphicOrderAt (PVGen(χ, t)) s = 0)
    (hpord : ∀ s : ℂ, s.re = 0 → meromorphicOrderAt (PVPoly(t)) s =
      (if ideleClassNormTwist χ s = 1 then 1 else 0))
    (f : ℬ𝔽)
    (hf : ∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) →
      let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
      ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
        meromorphicOrderAt (gChart(χ, f)) s) :
    ∃ g : ℬ𝔽, (K𝔽(1)).mkQ (adelePrincipalValue F T g) = (K𝔽(1)).mkQ f := by
  obtain ⟨_, M, _, hM_homeo, hM_eval, -, -, hM_range, -⟩ :=
    globalConverse_normTwist_meromorphic_exact χ t ht
  let q := (K𝔽(1)).mkQ
  let a : ℂ := (t : ℂ) * Complex.I
  let regular := ({-a, 1 - a} : Set ℂ)ᶜ
  let p : ℂ → ℂ := PVPoly(t)
  let G : ℂ → ℂ := PVGen(χ, t)
  let E := reciprocalPartialHeckeEulerProduct χ T
  have hM : M (q f) ∈ range M := ⟨q f, rfl⟩
  obtain ⟨B, ⟨u, hu, huval⟩, hBval⟩ := (hM_range _).mp hM
  have hB (s : regular) : B.val s.val = p s.val * gChart(χ, f) s.val :=
    (hBval s).trans (congrArg (p s.val * ·) (hM_eval f s))
  have hregular : regular ∈ codiscrete ℂ :=
    ((finite_singleton (1 - a)).insert (-a)).compl_mem_codiscrete
  have hB_eq : B.val =ᶠ[codiscrete ℂ] p * gChart(χ, f) := by
    filter_upwards [hregular] with s hs using hB ⟨s, hs⟩
  have hpdiff : Differentiable ℂ p := by dsimp [p]; fun_prop
  have H (s : ℂ) := sLocalPrincipalValue_multiplier_order hT χ hS s
  have hord (s : ℂ) : meromorphicOrderAt E s ≤ meromorphicOrderAt u s := by
    let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
    rw [(H s).2.1]
    by_cases hn : 0 < n
    · have hs := (H s).2.2 hn
      have hbo : meromorphicOrderAt B.val s = meromorphicOrderAt p s +
          meromorphicOrderAt (gChart(χ, f)) s := by
        rw [meromorphicOrderAt_congr (nhdsNE_le_codiscrete s hB_eq),
          meromorphicOrderAt_mul (hpdiff.analyticAt s).meromorphicAt
            ((globalIdelicZFunction_meromorphic f χ (mem_univ s)).meromorphicAt)]
      have huord : meromorphicOrderAt B.val s = meromorphicOrderAt u s := by
        rw [show B.val = G * u from funext huval,
          meromorphicOrderAt_mul (hGdiff.analyticAt s).meromorphicAt (hu.analyticAt s).meromorphicAt,
          hGord s hs, zero_add]
      rw [← huord, hbo, hpord s hs]
      have hbound : ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
          meromorphicOrderAt (gChart(χ, f)) s := hf s hn
      by_cases htriv : ideleClassNormTwist χ s = 1
      · rw [ite_eq_left htriv]
        rw [ite_eq_left htriv] at hbound
        have he : (n : WithTop ℤ) = (1 : WithTop ℤ) + ((n - 1 : ℕ) : WithTop ℤ) := by
          change ((n : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) + (((n - 1 : ℕ) : ℤ) : WithTop ℤ)
          rw [← WithTop.coe_add]
          congr 1
          omega
        rw [he]
        exact add_le_add_right hbound _
      · rw [ite_eq_right htriv, zero_add]
        simpa only [ite_eq_right htriv] using hbound
    · simpa [n, Nat.eq_zero_of_not_pos hn] using (hu.analyticAt s).meromorphicOrderAt_nonneg
  obtain ⟨v, hv, huv⟩ := sLocalPrincipalValue_divide_entire hu (fun s ↦ (H s).1.differentiableAt)
    (fun s ↦ by rw [(H s).2.1]; simp) hord
  have hfact (s : ℂ) : B.val s = E s * (G s * v s) := by
    have he : B.val s = G s * u s := huval s
    have he' : u s = E s * v s := huv s
    rw [he, he', mul_left_comm]
  let B' : SchwartzBergman (univ : Set ℝ) :=
    ⟨G * v, schwartzBergman_univ_div_prod_exp T
      (fun w z ↦ (finiteHeckeEulerFactor χ w z)⁻¹) (fun w _ ↦ sLocalPrincipalValue_euler_form χ w)
      B (G * v) (hGdiff.mul hv) hfact⟩
  have hp_ne (z : regular) : p z.val ≠ 0 := by
    have hz : z.val ≠ -a ∧ z.val ≠ 1 - a := by
      simpa only [regular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using z.property
    apply mul_ne_zero
    · intro h
      apply hz.1
      change z.val + a = 0 at h
      linear_combination h
    · intro h
      apply hz.2
      change 1 - z.val - a = 0 at h
      linear_combination -h
  let W (z : regular) := B'.val z.val / p z.val
  have hW : W ∈ range M := by
    apply (hM_range W).mpr
    refine ⟨B', ⟨v, hv, fun _ ↦ rfl⟩, fun z ↦ ?_⟩
    exact (mul_div_cancel₀ _ (hp_ne z)).symm
  obtain ⟨x, hx⟩ := hW
  obtain ⟨g, rfl⟩ := (K𝔽(1)).mkQ_surjective x
  have hZ_eq : gChart(χ, adelePrincipalValue F T g) = gChart(χ, f) := by
    apply sLocalPrincipalValue_normal_form_eq (globalIdelicZFunction_meromorphic _ χ)
      (globalIdelicZFunction_meromorphic f χ)
    filter_upwards [globalPrincipalValueConverse_mellin T χ g, hregular] with s hs hr
    let z : regular := ⟨s, hr⟩
    have hgv : gChart(χ, g) s = B'.val s / p s :=
      (hM_eval g z).symm.trans (congrFun hx z)
    have hB' : B'.val s = p s * gChart(χ, g) s := by
      rw [hgv, mul_div_cancel₀ _ (hp_ne z)]
    refine hs.trans (mul_left_cancel₀ (hp_ne z) ?_)
    change p s * (E s * gChart(χ, g) s) = p s * gChart(χ, f) s
    calc
      _ = E s * B'.val s := by rw [hB']; ring
      _ = B.val s := (hfact s).symm
      _ = _ := hB z
  have hM_inj : Function.Injective M := by
    let : TopologicalSpace M.range := TopologicalSpace.coinduced (⇑M.rangeRestrict) inferInstance
    intro x y hxy
    exact hM_homeo.injective (Subtype.ext hxy)
  refine ⟨g, hM_inj ?_⟩
  funext z
  exact (hM_eval _ z).trans ((congrFun hZ_eq z.val).trans (hM_eval f z).symm)

open Classical in
private theorem sLocalPrincipalValue_two_four {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S)
    (f : ℬ𝔽) :
    (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) →
      let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
      ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
        meromorphicOrderAt (gChart(χ, f)) s) ↔
    ∃ g : ℬ𝔽, (K𝔽(globalNormOne(χ))).mkQ (adelePrincipalValue F T g) =
      (K𝔽(globalNormOne(χ))).mkQ f := by
  constructor
  · intro hf
    by_cases hω : globalNormOne(χ) = 1
    · obtain ⟨t, ht, -⟩ := globalConverse_existsUnique_normTwist χ hω
      obtain ⟨hGdiff, hpord, hGord⟩ := sLocalPrincipalValue_regularized_global χ t ht
        (sLocalPrincipalValue_global_euler_order χ)
      generalize globalNormOne(χ) = ω at hω ⊢
      subst ω
      exact sLocalPrincipalValue_trivial_range hT χ hS t ht hGdiff hGord hpord f hf
    · refine sLocalPrincipalValue_nontrivial_range hT χ hS hω f fun s hn ↦ ?_
      have hn1 : ideleClassNormTwist χ s ≠ 1 := fun h ↦ hω
        (sLocalPrincipalValue_chart_unit_normOne χ s h)
      simpa only [ite_eq_right hn1] using hf s hn
  · exact sLocalPrincipalValue_four_two hT χ hS f

/-- Principal value depends only on the global homogeneous theta class of its input. -/
private theorem sLocalPrincipalValue_global_congr {S₀ : Finset Places}
    (ω : PontryaginDual (m𝔽).ker) (a b : ℬ𝔽) (hab : (K𝔽(ω)).mkQ a = (K𝔽(ω)).mkQ b) :
    (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ a) = (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ b) := by
  obtain ⟨e, he⟩ := (globalThetaIsotypicAverage_equiv (F := F) ω).2
  let Q := (LinearMap.ker (adelicThetaLinearMap F)).mkQ
  let A := (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
  have hA : A (Q a) = A (Q b) := (he a).symm.trans
    ((congrArg (fun z => (e z).val) hab).trans (he b))
  apply e.injective
  apply Subtype.ext
  refine (he _).trans (Eq.trans ?_ (he _).symm)
  exact (globalThetaPrincipalValue_isotypicAverage (F := F) S₀ ω (Q a)).symm.trans
    ((congrArg (globalThetaPrincipalValue F S₀) hA).trans
      (globalThetaPrincipalValue_isotypicAverage (F := F) S₀ ω (Q b)))

/-- Inserting a local principal value and applying principal value after insertion
give equal homogeneous classes. -/
private theorem sLocalPrincipalValue_homogeneous_comm {S₀ : Finset Places}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) (ω : PontryaginDual (m𝔽).ker) (g : ℬₛ) :
    (K𝔽(ω)).mkQ (sAdeleSchwartzToGlobal F S (sAdelePrincipalValue F h₀ g)) =
      (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ (sAdeleSchwartzToGlobal F S g)) := by
  let Q := (LinearMap.ker (sLocalAdelicTheta F S)).mkQ
  let P := (exists_globalThetaToHomogeneousProduct (F := F)).choose
  have h := LinearMap.congr_fun (sLocalThetaPrincipalValue_toGlobal (F := F) h₀ hn) (Q g)
  exact ((exists_globalThetaToHomogeneousProduct (F := F)).choose_spec.2 _ ω).symm.trans
    ((congrArg (fun z => P z ω) h).trans
      ((exists_globalThetaToHomogeneousProduct (F := F)).choose_spec.2 _ ω))

private theorem sLocalPrincipalValue_tfae_three_four {S₀ : Finset Places}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty)
    (hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (f : ℬₛ) :
    let ω := globalNormOne(χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(ωₛ)).mkQ f
    let π := sLocalHomogeneousThetaToGlobal hω
    x ∈ (sLocalHomogeneousThetaPrincipalValue h₀ ωₛ).range ↔
      ∃ g : ℬ𝔽, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g) = π x := by
  intro ω hω ωₛ x π
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified hPic hω
  have heπ (z) : e z = π z := LinearMap.congr_fun he z
  let L := sAdeleSchwartzToGlobal F S
  let Q := (Kₛ(ωₛ)).mkQ
  have hcomm (g : ℬₛ) :
      π (sLocalHomogeneousThetaPrincipalValue h₀ ωₛ (Q g)) =
        (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ (L g)) :=
    sLocalPrincipalValue_homogeneous_comm h₀ hn ω g
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨g, rfl⟩ := (Kₛ(ωₛ)).mkQ_surjective z
    exact ⟨L g, (hcomm g).symm.trans (congrArg π hz)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨z, hz⟩ := e.surjective ((K𝔽(ω)).mkQ g)
    obtain ⟨u, rfl⟩ := (Kₛ(ωₛ)).mkQ_surjective z
    have hu : (K𝔽(ω)).mkQ (L u) = (K𝔽(ω)).mkQ g :=
      (heπ (Q u)).symm.trans hz
    refine ⟨Q u, e.injective ?_⟩
    exact (heπ _).trans ((hcomm u).trans
      ((sLocalPrincipalValue_global_congr ω (L u) g hu).trans (hg.trans (heπ x).symm)))

/-- Vanishing of the selected highest coefficients gives a principal-value preimage
on the component of a character unramified outside the ambient set of places. -/
theorem sLocalPrincipalValue_mem_range_of_coeff_eq_zero {T : Finset Places}
    (hT : T ⊆ S) (hn : T.Nonempty)
    (hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (f : ℬₛ) :
    let hω : NormOneCharacterUnramifiedOutside (globalNormOne(χ)) S :=
      ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S (globalNormOne(χ)) hω
    (∀ c : Xₛ, onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity T c →
      ∀ k : ℕ, sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity T c < k →
      k ≤ sLocalRhoPoleOrder c → sLocalPrincipalPartCoeff c k f = 0) →
    (Kₛ(ωₛ)).mkQ f ∈ (sLocalHomogeneousThetaPrincipalValue hT ωₛ).range := by
  intro hω ωₛ hf
  apply (sLocalPrincipalValue_tfae_three_four hT hn hPic χ hS f).mpr
  rw [sLocalHomogeneousThetaToGlobal_mk hω f]
  exact (sLocalPrincipalValue_two_four hT χ hS (sAdeleSchwartzToGlobal F S f)).mp
    ((sLocalPrincipalValue_tfae_one_two hT χ hS f).mp hf)

open Classical in
/-- Paper: Proposition 7.2.2.1, p. 339.
Eliminating the selected highest local coefficients is equivalent to the global
zero-order bound and to membership in either homogeneous principal-value image.
Deviation: Zero orders are lower bounds on the meromorphic order. The bound drops
by one at the trivial quasi-character when it lies on the selected divisor. -/
theorem sLocalPrincipalValue_tfae {S₀ : Finset Places} (h₀ : S₀ ⊆ S) (_hn : S₀.Nonempty)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hχ : globalUnitary(χ) ∈ unramifiedOutside F S₀)
    (f : ℬₛ) :
    let hS : globalUnitary(χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(ωₛ)).mkQ f
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ), onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        ∀ k : ℕ, sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity S₀ c < k →
          k ≤ sLocalRhoPoleOrder c → sLocalPrincipalPartCoeff c k f = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) →
        let n := sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s)
        ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
          meromorphicOrderAt Z s),
      x ∈ (sLocalHomogeneousThetaPrincipalValue h₀ ωₛ).range,
      (∃ g : ℬ𝔽, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g) = π x)
    ] := by
  intro hS ω hω ωₛ x π Z
  tfae_have 1 ↔ 2 := sLocalPrincipalValue_tfae_one_two h₀ χ hS f
  tfae_have 3 ↔ 4 := sLocalPrincipalValue_tfae_three_four h₀ _hn _hPic χ hS f
  tfae_have 2 ↔ 4 := by
    have hπ : π x = (K𝔽(ω)).mkQ (sAdeleSchwartzToGlobal F S f) :=
      sLocalHomogeneousThetaToGlobal_mk hω f
    rw [hπ]
    exact sLocalPrincipalValue_two_four h₀ χ hS (sAdeleSchwartzToGlobal F S f)
  tfae_finish

local notation "polarValuesₛ" =>
  (fun f : ℬₛ ↦ (f (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)))

/-- Paper: Equation (7.2.2.3), p. 340.
Evaluation at zero before and after S-adelic Fourier transform is complex linear. -/
theorem sAdelePolarValues_isLinear : IsLinearMap ℂ polarValuesₛ := by
  obtain ⟨T, hT⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  constructor
  · intro f g
    refine Prod.ext rfl ?_
    rw [← hT, map_add, hT, hT]
    rfl
  · intro c f
    refine Prod.ext rfl ?_
    rw [← hT, map_smul, hT]
    rfl

variable (F S) in
/-- Paper: Equation (7.2.2.3), p. 340.
The S-adelic polar subspace is the common kernel of evaluation at zero
and evaluation at zero after Fourier transform. -/
def sAdelePolarSubspace : Submodule ℂ ℬₛ :=
  LinearMap.ker ((sAdelePolarValues_isLinear (F := F) (S := S)).mk' polarValuesₛ)

/-- Paper: Equation (7.2.2.3), p. 340.
Membership requires both the test and its Fourier transform to vanish at zero. -/
theorem mem_sAdelePolarSubspace (f : ℬₛ) :
    f ∈ sAdelePolarSubspace F S ↔
      f (Multiplicative.ofAdd 0) = 0 ∧ sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 := by
  change (f (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)) = 0 ↔ _
  exact Prod.mk_eq_zero

/-- Paper: Corollary 7.2.2.2, p. 340.
Insertion with integer indicators outside S preserves the two zero evaluations
that define the polar subspaces. -/
theorem sAdeleSchwartzToGlobal_mem_polarSubspace (f : sAdelePolarSubspace F S) :
    sAdeleSchwartzToGlobal F S f.val ∈ adelePolarSubspace F := by
  classical
  let : MeasurableSpace 𝔸[F] := borel _
  let : MeasurableSpace Aₛ := instMeasurableSpaceSAdeleRing F S
  obtain ⟨hf, hFourier⟩ := (mem_sAdelePolarSubspace f.val).mp f.property
  apply (mem_adelePolarSubspace _).mpr
  constructor
  · rw [sAdeleSchwartzToGlobal_apply]
    simp only [map_zero, hf, ite_self]
  · obtain ⟨c, _, _, hm, _⟩ := sAdeleProjection_dual_masses F S
    have hLift : (fun x ↦ sAdeleSchwartzToGlobal F S f.val (Multiplicative.ofAdd x)) =
        (integralAdelesOutside F S : Set 𝔸[F]).indicator
          ((fun x ↦ f.val (Multiplicative.ofAdd x)) ∘ adeleProjection F S) := by
      funext x
      rw [sAdeleSchwartzToGlobal_apply]
      simp only [Set.indicator, SetLike.mem_coe, integralTail_iff, Function.comp_apply]
    have h := congrFun (tamagawaFourier_sAdeleLift F S c hm
      (fun x ↦ f.val (Multiplicative.ofAdd x)) (partialTensor_integrable F S f.val)) 0
    change tamagawaFourier _ _ _ 0 = 0
    rw [hLift, h]
    change (sAdeleTailDual F S).indicator
      (fun x ↦ (c : ℝ) • sAdeleSchwartzFourier f.val
        (Multiplicative.ofAdd (adeleProjection F S x))) 0 = 0
    simp only [Set.indicator, map_zero, hFourier, smul_zero, ite_self]

local notation "C₁" => (m𝔽).ker
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set Places).integer F))
local notation "LocalChar(" ω ", " hω ")" => sLocalNormOneCharacter S ω hω

/-- A character unramified outside S is determined by its local restriction when
the S-integer Picard group is trivial. -/
private theorem sLocalPolarPrincipalValue_character_eq_one (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial)
    (h : LocalChar(ω, hω) = 1) : ω = 1 := by
  let := hPic
  obtain ⟨e, he, -⟩ := sIdeleClassGroup_equiv_of_classNumberOne F S
  apply PontryaginDual.ext
  intro x
  obtain ⟨x', hx⟩ := e.surjective x.val
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x'
  rw [he] at hx
  let g := Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u)
  have hn : sIdeleQuotientNorm F S (QuotientGroup.mk g) = 1 := by
    rw [sIdeleQuotientNorm_mk]
    exact ((sIdeleNorm_spec F S).1 u).symm.trans ((congrArg m𝔽 hx).trans x.property)
  let y : J₁ := ⟨QuotientGroup.mk g, hn⟩
  have hh := sLocalNormOneCharacter_apply ω hω u x y hx.symm rfl
  rw [h] at hh
  exact hh.symm

private theorem sLocalPolarPrincipalValue_chart_eq_one
    [Subsingleton (CommRing.Pic ((S : Set Places).integer F))]
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S) (s : ℂ) :
    localChart(χ, hS) s = 1 ↔ ideleClassNormTwist χ s = 1 := by
  constructor
  · intro h
    let hω : NormOneCharacterUnramifiedOutside (globalNormOne(χ)) S :=
      ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    obtain ⟨_, _, hcov, _⟩ := sLocalPrincipalValue_chart χ hS
    have hlocal : LocalChar(globalNormOne(χ), hω) = 1 := by
      apply PontryaginDual.ext
      intro y
      apply Subtype.ext
      have hy := DFunLike.congr_fun (hcov s) y
      change localChart(χ, hS) s y.val = (LocalChar(globalNormOne(χ), hω) y : ℂ) at hy
      rw [h] at hy
      exact hy.symm
    have hw := sLocalPolarPrincipalValue_character_eq_one _ hω inferInstance hlocal
    have hunit (x : (m𝔽).ker) : (χ x.val : ℂ) = 1 :=
      congrArg (fun c : PontryaginDual C₁ ↦ (c x : ℂ)) hw
    ext1 x
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (σ (m𝔽 x))
    let y : C𝔽 := QuotientGroup.mk (sIdeleInsertion F S g)
    have hy : m𝔽 y = m𝔽 x := by
      change ideleNorm F (sIdeleInsertion F S g) = _
      rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk, hg, hσ]
    have hn : m𝔽 (x / y) = 1 := by rw [map_div, hy, div_self']
    have hz : ideleClassNormTwist χ s (x / y) = 1 := by
      change (χ (x / y) : ℂ) * ((((m𝔽 (x / y)).val : ℝ) : ℂ) ^ s) = 1
      rw [hunit ⟨_, hn⟩, hn, Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
    have hy' : ideleClassNormTwist χ s y = 1 :=
      (sLocalPrincipalValue_chart_apply χ hS s g).symm.trans (DFunLike.congr_fun h _)
    rwa [map_div, hy', div_one] at hz
  · intro h
    ext1 x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [sLocalPrincipalValue_chart_apply, h]
    rfl

open Classical in
private theorem sLocalPolarPrincipalValue_one_two {T : Finset Places} (hT : T ⊆ S)
    [Subsingleton (CommRing.Pic ((S : Set Places).integer F))]
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S)
    (f : sAdelePolarSubspace F S) :
    let hω : NormOneCharacterUnramifiedOutside (globalNormOne(χ)) S :=
      ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S (globalNormOne(χ)) hω
    (∀ c : Xₛ, onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity T c →
      let m := sLocalRhoPoleOrder c
      let n := sLocalFinitePoleMultiplicity T c
      ∀ k : ℕ, (if c = 1 then m - n ≤ k ∧ k ≤ m - 1 else m - n < k ∧ k ≤ m) →
        sLocalPrincipalPartCoeff c k f.val = 0) ↔
    (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) →
      (sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) : WithTop ℤ) ≤
        meromorphicOrderAt (gChart(χ, sAdeleSchwartzToGlobal F S f.val)) s) := by
  intro hω ωₛ
  obtain ⟨_, _, hcov, hsurj⟩ := sLocalPrincipalValue_chart χ hS
  have horder (s : ℂ) (hn : 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)) :
      let c := localChart(χ, hS) s
      let n := sLocalFinitePoleMultiplicity T c
      let m := sLocalRhoPoleOrder c
      (∀ k : ℕ, (if c = 1 then m - n ≤ k ∧ k ≤ m - 1 else m - n < k ∧ k ≤ m) →
        sLocalPrincipalPartCoeff c k f.val = 0) ↔
        (n : WithTop ℤ) ≤ meromorphicOrderAt (gChart(χ, sAdeleSchwartzToGlobal F S f.val)) s := by
    intro c n m
    have hbound (p : ℕ) (hp : 0 < p) (hpm : p ≤ m) :
        (∀ k : ℕ, m - p < k → k ≤ m → sLocalPrincipalPartCoeff c k f.val = 0) ↔
          ((if ideleClassNormTwist χ s = 1 then p - 1 else p : ℕ) : WithTop ℤ) ≤
            meromorphicOrderAt (gChart(χ, sAdeleSchwartzToGlobal F S f.val)) s := by
      have hre := (sLocalPrincipalValue_multiplier_order hT χ hS s).2.2 hn
      rw [sLocalPrincipalValue_coeff_order, sLocalPrincipalValue_centered_order χ hS s (sLocalIdelicZFunction f.val),
        sLocalPrincipalValue_insertion_order χ hS f.val s hn,
        sLocalPrincipalValue_global_euler_order χ s hre]
      exact sLocalPrincipalValue_bound_shift _ m p hp hpm _
    have he := sLocalPolarPrincipalValue_chart_eq_one χ hS s
    change c = 1 ↔ _ at he
    by_cases hc : c = 1
    · have hg := he.mp hc
      have hm : n < m := by
        change sLocalFinitePoleMultiplicity T c < sLocalRhoPoleOrder c
        rw [hc, sLocalRhoPoleOrder_eq_card_polePlaces, (sLocalPolePlaces_one (F := F) (S := S)).1]
        have ha : 0 < (Finset.univ : Finset (InfinitePlace F)).card := Finset.card_pos.mpr Finset.univ_nonempty
        exact lt_of_le_of_lt (Finset.card_filter_le _ _) (Nat.lt_add_of_pos_left ha)
      have hZ := globalIdelicZFunction_entire_of_vanishing _ (sAdeleSchwartzToGlobal_mem_polarSubspace f) χ
      -- Entireness kills the top coefficient and leaves the next n coefficients.
      have htop := (hbound 1 (by decide) (by omega)).mpr (by
        simpa [hg] using (hZ.analyticAt s).meromorphicOrderAt_nonneg)
      have h := hbound (n + 1) (by omega) (by omega)
      simp only [ite_eq_left hg, Nat.add_sub_cancel] at h
      simp only [ite_eq_left hc]
      rw [← h]
      constructor
      · intro H k hk hk'
        by_cases hk'' : k = m
        · exact htop k (by omega) hk'
        · exact H k ⟨by omega, by omega⟩
      · intro H k hk
        exact H k (by omega) (by omega)
    · have hg := he.not.mp hc
      simpa only [ite_eq_right hc, ite_eq_right hg, and_imp] using
        hbound n hn (sLocalPrincipalValue_multiplicity_le T c)
  constructor
  · intro h s hn
    exact (horder s hn).mp (h _ (hcov s) hn)
  · intro h c hc hn
    obtain ⟨s, rfl⟩ := hsurj c hc
    exact (horder s hn).mpr (h s hn)

/-- The norm-one mass in the residue formulas is nonzero, by the volume
formula as in `grh_classVolume_ne_zero` in Chapter 12. -/
private theorem sLocalPolarPrincipalValue_mass_ne_zero :
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
of the test to vanish. -/
private theorem sLocalPolarPrincipalValue_mem_of_entire_chart (χ : PontryaginDual C𝔽)
    (hω : globalNormOne(χ) = 1) (g : ℬ𝔽) (hg : Differentiable ℂ (gChart(χ, g))) :
    g ∈ adelePolarSubspace F := by
  obtain ⟨t, ht, -⟩ := globalConverse_existsUnique_normTwist χ hω
  let b := (t : ℂ) * Complex.I
  have he : gChart((1 : PontryaginDual C𝔽), g) = fun s ↦ gChart(χ, g) (s - b) := by
    funext s
    have h := ideleClassNormTwist_add_of_eq ht (s - b)
    have hb : b + (s - b) = s := by ring
    change ideleClassNormTwist χ (0 + (s - b)) =
      ideleClassNormTwist (1 : PontryaginDual C𝔽) (b + (s - b)) at h
    rw [zero_add, hb] at h
    exact congrArg (globalIdelicZFunction g) h.symm
  have hc : Continuous (gChart((1 : PontryaginDual C𝔽), g)) := by
    rw [he]
    exact hg.continuous.comp (continuous_id.sub continuous_const)
  have hmass := sLocalPolarPrincipalValue_mass_ne_zero (F := F)
  have h0 : Tendsto (fun s : ℂ ↦ s * gChart((1 : PontryaginDual C𝔽), g) s)
      (𝓝[≠] 0) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ ↦ s * gChart((1 : PontryaginDual C𝔽), g) s) 0 :=
      continuousAt_id.mul hc.continuousAt
    simpa only [zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s : ℂ ↦ (s - 1) * gChart((1 : PontryaginDual C𝔽), g) s)
      (𝓝[≠] 1) (𝓝 0) := by
    have h : ContinuousAt (fun s : ℂ ↦ (s - 1) * gChart((1 : PontryaginDual C𝔽), g) s) 1 :=
      (continuousAt_id.sub (continuousAt_const (y := (1 : ℂ)))).mul hc.continuousAt
    simpa only [sub_self, zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
  refine (mem_adelePolarSubspace g).mpr ⟨?_, ?_⟩
  · exact (mul_eq_zero.mp (tendsto_nhds_unique (globalIdelicZFunction_residue_zero g) h0)).resolve_left
      (neg_ne_zero.mpr hmass)
  · exact (mul_eq_zero.mp (tendsto_nhds_unique (globalIdelicZFunction_residue_one g) h1)).resolve_left hmass

/-- Equality in the homogeneous principal-value image determines the order of the
output in the global chart by adding the order of the Euler multiplier. -/
private theorem sLocalPolarPrincipalValue_image_order {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S)
    (f g : ℬ𝔽) (he : (K𝔽(globalNormOne(χ))).mkQ (adelePrincipalValue F T g) =
      (K𝔽(globalNormOne(χ))).mkQ f) (s : ℂ) :
    meromorphicOrderAt (gChart(χ, f)) s =
      (sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) : WithTop ℤ) +
        meromorphicOrderAt (gChart(χ, g)) s := by
  obtain ⟨hE, hEord, -⟩ := sLocalPrincipalValue_multiplier_order hT χ hS s
  rw [← sLocalPrincipalValue_chart_eq_of_class χ _ _ he]
  rw [meromorphicOrderAt_congr (nhdsNE_le_codiscrete s (globalPrincipalValueConverse_mellin T χ g))]
  change meromorphicOrderAt (reciprocalPartialHeckeEulerProduct χ T * gChart(χ, g)) s = _
  rw [meromorphicOrderAt_mul hE.meromorphicAt
    ((globalIdelicZFunction_meromorphic g χ (mem_univ s)).meromorphicAt), hEord]

/-- The global chart of an ambient principal-value preimage is entire when a polar
output satisfies the unshifted order bound. -/
private theorem sLocalPolarPrincipalValue_divided_entire {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S)
    (f : adelePolarSubspace F) (g : ℬ𝔽)
    (he : (K𝔽(globalNormOne(χ))).mkQ (adelePrincipalValue F T g) =
      (K𝔽(globalNormOne(χ))).mkQ f.val)
    (hf : ∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) →
      (sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) : WithTop ℤ) ≤
        meromorphicOrderAt (gChart(χ, f.val)) s) :
    Differentiable ℂ (gChart(χ, g)) := by
  intro s
  apply AnalyticAt.differentiableAt
  apply ((globalIdelicZFunction_meromorphic g χ (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt).mp
  let n := sLocalFinitePoleMultiplicity T (localChart(χ, hS) s)
  have hbound : (n : WithTop ℤ) ≤ meromorphicOrderAt (gChart(χ, f.val)) s := by
    by_cases hp : 0 < n
    · exact hf s hp
    · simpa only [Nat.eq_zero_of_not_pos hp, Nat.cast_zero] using
        ((globalIdelicZFunction_entire_of_vanishing f.val f.property χ).analyticAt s).meromorphicOrderAt_nonneg
  rw [sLocalPolarPrincipalValue_image_order hT χ hS f.val g he s] at hbound
  change (n : WithTop ℤ) ≤ (n : WithTop ℤ) + meromorphicOrderAt (gChart(χ, g)) s at hbound
  generalize meromorphicOrderAt (gChart(χ, g)) s = a at hbound ⊢
  cases a using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    change ((n : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) + (a : WithTop ℤ) at hbound
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at hbound
    exact WithTop.coe_le_coe.mpr (le_of_add_le_add_left (by simpa only [add_zero] using hbound))

open Classical in
private theorem sLocalPolarPrincipalValue_two_four {T : Finset Places} (hT : T ⊆ S)
    (χ : PontryaginDual C𝔽) (hS : globalUnitary(χ) ∈ unramifiedOutside F S)
    (f : adelePolarSubspace F) :
    (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) →
      (sLocalFinitePoleMultiplicity T (localChart(χ, hS) s) : WithTop ℤ) ≤
        meromorphicOrderAt (gChart(χ, f.val)) s) ↔
    ∃ g : adelePolarSubspace F, (K𝔽(globalNormOne(χ))).mkQ (adelePrincipalValue F T g.val) =
      (K𝔽(globalNormOne(χ))).mkQ f.val := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (sLocalPrincipalValue_two_four hT χ hS f.val).mp (fun s hn ↦ by
      refine le_trans ?_ (hf s hn)
      split_ifs
      · exact_mod_cast Nat.sub_le _ _
      · exact le_rfl)
    by_cases hω : globalNormOne(χ) = 1
    · exact ⟨⟨g, sLocalPolarPrincipalValue_mem_of_entire_chart χ hω g
        (sLocalPolarPrincipalValue_divided_entire hT χ hS f g hg hf)⟩, hg⟩
    · obtain ⟨u, hu⟩ := (globalConverse_nontrivial_exact (globalNormOne(χ)) hω).surjective
        ((K𝔽(globalNormOne(χ))).mkQ g)
      exact ⟨u, (sLocalPrincipalValue_global_congr (globalNormOne(χ)) u.val g hu).trans hg⟩
  · rintro ⟨g, hg⟩ s -
    rw [sLocalPolarPrincipalValue_image_order hT χ hS f.val g.val hg s]
    exact le_add_of_nonneg_right
      ((globalIdelicZFunction_entire_of_vanishing g.val g.property χ).analyticAt s).meromorphicOrderAt_nonneg

/-- The two polar evaluations are determined by the untwisted global Mellin chart. -/
private theorem sLocalPolarPrincipalValue_polarValues_congr (f g : ℬ𝔽)
    (he : gChart((1 : PontryaginDual C𝔽), f) = gChart((1 : PontryaginDual C𝔽), g)) :
    adelePolarValues (F := F) f = adelePolarValues (F := F) g := by
  have hm := sLocalPolarPrincipalValue_mass_ne_zero (F := F)
  apply Prod.ext
  · change f (Multiplicative.ofAdd 0) = g (Multiplicative.ofAdd 0)
    exact mul_left_cancel₀ (neg_ne_zero.mpr hm)
      (tendsto_nhds_unique ((globalIdelicZFunction_residue_zero f).congr
        (fun s ↦ congrArg (s * ·) (congrFun he s))) (globalIdelicZFunction_residue_zero g))
  · change adeleSchwartzFourier f (Multiplicative.ofAdd 0) =
      adeleSchwartzFourier g (Multiplicative.ofAdd 0)
    exact mul_left_cancel₀ hm (tendsto_nhds_unique
      ((globalIdelicZFunction_residue_one f).congr
        (fun s ↦ congrArg ((s - 1) * ·) (congrFun he s))) (globalIdelicZFunction_residue_one g))

/-- Equal finite-dimensional targets force equality of kernels once the larger
kernel belongs to a surjection. -/
private theorem polarEvaluation_ker_eq_of_surjective {E D : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D]
    (p d : E →ₗ[ℂ] D) (hs : Function.Surjective d) (h : p.ker ≤ d.ker) : p.ker = d.ker := by
  obtain ⟨r, hr⟩ := d.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  have hdr (z : D) : d (r z) = z := LinearMap.congr_fun hr z
  have hin : Function.Injective (p.comp r) := by
    intro a b hab
    have hh : r a - r b ∈ p.ker := by
      change p (r a - r b) = 0
      exact (p.map_sub _ _).trans (sub_eq_zero.mpr hab)
    have hz := LinearMap.mem_ker.mp (h hh)
    rwa [map_sub, hdr, hdr, sub_eq_zero] at hz
  have hout := LinearMap.injective_iff_surjective.mp hin
  refine le_antisymm h fun x hx ↦ ?_
  obtain ⟨z, hz⟩ := hout (p x)
  change p (r z) = p x at hz
  have hh : r z - x ∈ p.ker := by
    change p (r z - x) = 0
    rw [map_sub, hz, sub_self]
  have hd := LinearMap.mem_ker.mp (h hh)
  rw [map_sub, hdr, LinearMap.mem_ker.mp hx, sub_zero] at hd
  change p x = 0
  simpa only [hd, map_zero] using hz.symm

/-- Inserting preserves polar tests, and the two global polar values are
already independent on inserted tests when the S-integer Picard group is trivial. -/
private theorem sLocalPolarPrincipalValue_reflect (hPic : PicTrivial)
    (u : ℬₛ) (g : adelePolarSubspace F)
    (hu : (K𝔽(1)).mkQ (sAdeleSchwartzToGlobal F S u) = (K𝔽(1)).mkQ g.val) :
    u ∈ sAdelePolarSubspace F S := by
  let L := sAdeleSchwartzToGlobal F S
  let G := (K𝔽(1)).mkQ
  have h₁ : NormOneCharacterUnramifiedOutside (1 : PontryaginDual C₁) S :=
    ⟨⟨1, (mem_unramifiedOutside_iff F S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  let η := LocalChar(1, h₁)
  let Q := (Kₛ(η)).mkQ
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) hPic h₁
  have hin (u : ℬₛ) : e (Q u) = G (L u) :=
    (LinearMap.congr_fun he (Q u)).trans (sLocalHomogeneousThetaToGlobal_mk h₁ u)
  have hval (v w : ℬ𝔽) (h : G v = G w) : adelePolarValues (F := F) v = adelePolarValues w := by
    apply sLocalPolarPrincipalValue_polarValues_congr
    exact sLocalPrincipalValue_chart_eq_of_class (1 : PontryaginDual C𝔽) v w h
  let d := (adelePolarValues (F := F)).comp L
  let p := (sAdelePolarValues_isLinear (F := F) (S := S)).mk' _
  have hsur : Function.Surjective d := by
    intro z
    obtain ⟨w, hw⟩ := (adelePolarValues_surjective (F := F)) z
    obtain ⟨v, hv⟩ := (Kₛ(η)).mkQ_surjective (e.symm (G w))
    exact ⟨v, (hval _ _ ((hin v).symm.trans ((congrArg e hv).trans (e.apply_symm_apply _)))).trans hw⟩
  have hk : p.ker ≤ d.ker := fun v hv ↦
    sAdeleSchwartzToGlobal_mem_polarSubspace (⟨v, hv⟩ : sAdelePolarSubspace F S)
  have heq := polarEvaluation_ker_eq_of_surjective p d hsur hk
  have hx : u ∈ d.ker := (hval _ _ hu).trans (show adelePolarValues g.val = 0 from g.property)
  exact (show u ∈ p.ker from heq.symm ▸ hx)

/-- A norm-one translation difference kills the trivial homogeneous class.
When the translating character value is nontrivial, its normalized difference
represents the original class in that character's component. -/
private theorem sLocalPolarPrincipalValue_translate_sub (hPic : PicTrivial) (η : PontryaginDual J₁)
    (hη : η ≠ 1) (u : ℬₛ) : ∃ f : sAdelePolarSubspace F S, (Kₛ(η)).mkQ f.val = (Kₛ(η)).mkQ u := by
  obtain ⟨h, hh⟩ : ∃ h : J₁, (η h : ℂ) ≠ 1 :=
    not_forall.mp fun hall ↦ hη (PontryaginDual.ext fun x ↦ Subtype.ext (hall x))
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective h.val
  let t := schwartzBruhatUnitTranslate v u - u
  have h₁ : NormOneCharacterUnramifiedOutside (1 : PontryaginDual C₁) S :=
    ⟨⟨1, (mem_unramifiedOutside_iff F S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  have hone : LocalChar(1, h₁) = 1 :=
    ((normOneCharacterUnramifiedOutside_iff (F := F) (S := S) 1).mp h₁).unique
      (sLocalNormOneCharacter_apply 1 h₁) (fun _ _ _ _ _ ↦ rfl)
  have ht : t ∈ Kₛ(LocalChar(1, h₁)) := by
    rw [hone]
    change (sLocalHomogeneousAdelicThetaLinearMap F S 1) (schwartzBruhatUnitTranslate v u - u) = 0
    rw [map_sub, sLocalHomogeneousTheta_unitTranslate (F := F) (S := S) (1 : PontryaginDual J₁) h v hv]
    simp
  have hp : t ∈ sAdelePolarSubspace F S := by
    apply sLocalPolarPrincipalValue_reflect hPic t 0
    change (K𝔽(1)).mkQ (sAdeleSchwartzToGlobal F S t) = (K𝔽(1)).mkQ 0
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (sLocalHomogeneousThetaToGlobal_preserves_kernel h₁ ht)
  let a := (η h : ℂ) - 1
  have ha : a ≠ 0 := sub_ne_zero.mpr hh
  refine ⟨⟨a⁻¹ • t, (sAdelePolarSubspace F S).smul_mem _ hp⟩, ?_⟩
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
  change (sLocalHomogeneousAdelicThetaLinearMap F S η) (a⁻¹ • t - u) = 0
  rw [map_sub, map_smul]
  have htheta : (sLocalHomogeneousAdelicThetaLinearMap F S η) t =
      a • (sLocalHomogeneousAdelicThetaLinearMap F S η) u := by
    rw [show t = schwartzBruhatUnitTranslate v u - u from rfl, map_sub,
      sLocalHomogeneousTheta_unitTranslate η h v hv, sub_smul, one_smul]
  rw [htheta, inv_smul_smul₀ ha, sub_self]

/-- Insertion of polar local tests surjects onto each polar homogeneous component. -/
private theorem sLocalPolarPrincipalValue_lift (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial)
    (g : adelePolarSubspace F) :
    ∃ f : sAdelePolarSubspace F S, (K𝔽(ω)).mkQ (sAdeleSchwartzToGlobal F S f.val) = (K𝔽(ω)).mkQ g.val := by
  let η := LocalChar(ω, hω)
  let Q := (Kₛ(η)).mkQ
  let G := (K𝔽(ω)).mkQ
  let L := sAdeleSchwartzToGlobal F S
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) hPic hω
  have hin (u : ℬₛ) : e (Q u) = G (L u) :=
    (LinearMap.congr_fun he (Q u)).trans (sLocalHomogeneousThetaToGlobal_mk hω u)
  obtain ⟨u, hu⟩ := (Kₛ(η)).mkQ_surjective (e.symm (G g.val))
  have hre : G (L u) = G g.val := (hin u).symm.trans ((congrArg e hu).trans (e.apply_symm_apply _))
  by_cases hw : ω = 1
  · subst ω
    exact ⟨⟨u, sLocalPolarPrincipalValue_reflect hPic u g hre⟩, hre⟩
  · have hη : η ≠ 1 := fun h ↦ hw (sLocalPolarPrincipalValue_character_eq_one ω hω hPic h)
    obtain ⟨v, hv⟩ := sLocalPolarPrincipalValue_translate_sub hPic η hη u
    exact ⟨v, (hin v.val).symm.trans ((congrArg e hv).trans ((hin u).trans hre))⟩

private theorem sLocalPolarPrincipalValue_three_four {S₀ : Finset Places}
    (h₀ : S₀ ⊆ S) (hn : S₀.Nonempty) (hPic : PicTrivial)
    (ω : PontryaginDual C₁) (hω : NormOneCharacterUnramifiedOutside ω S)
    (x : SLocalHomogeneousThetaSpace F S (LocalChar(ω, hω))) :
    let η := LocalChar(ω, hω)
    let π := sLocalHomogeneousThetaToGlobal hω
    (∃ f : sAdelePolarSubspace F S, (Kₛ(η)).mkQ (sAdelePrincipalValue F h₀ f.val) = x) ↔
      ∃ g : adelePolarSubspace F, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g.val) = π x := by
  intro η π
  let L := sAdeleSchwartzToGlobal F S
  let Q := (Kₛ(η)).mkQ
  let G := (K𝔽(ω)).mkQ
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) hPic hω
  have heπ (z) : e z = π z := LinearMap.congr_fun he z
  have hcomm (f : ℬₛ) : π (Q (sAdelePrincipalValue F h₀ f)) = G (adelePrincipalValue F S₀ (L f)) :=
    (sLocalHomogeneousThetaToGlobal_mk hω _).trans
      (sLocalPrincipalValue_homogeneous_comm h₀ hn ω f)
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨L f.val, sAdeleSchwartzToGlobal_mem_polarSubspace f⟩, (hcomm f.val).symm.trans (congrArg π hf)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨f, hf⟩ := sLocalPolarPrincipalValue_lift ω hω hPic g
    refine ⟨f, e.injective ?_⟩
    exact (heπ _).trans ((hcomm f.val).trans ((sLocalPrincipalValue_global_congr ω (L f.val) g.val hf).trans
      (hg.trans (heπ x).symm)))

open Classical in
/-- Paper: Corollary 7.2.2.2, p. 340.
On tests in the common kernel of the two zero evaluations, the global bound has
no exception. At the trivial character the local coefficient range shifts down
by one. The two principal-value images use inputs in the respective polar subspaces.
Deviation: The zero-order condition is a lower bound on meromorphic order. The
homogeneous theta classes of the restricted tests are represented in the ambient quotients. -/
theorem sLocalPolarPrincipalValue_tfae {S₀ : Finset Places} (h₀ : S₀ ⊆ S) (_hn : S₀.Nonempty)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hχ : globalUnitary(χ) ∈ unramifiedOutside F S₀)
    (f : sAdelePolarSubspace F S) :
    let hS : globalUnitary(χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(ωₛ)).mkQ f.val
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f.val) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ), onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        let m := sLocalRhoPoleOrder c
        let n := sLocalFinitePoleMultiplicity S₀ c
        ∀ k : ℕ, (if c = 1 then m - n ≤ k ∧ k ≤ m - 1 else m - n < k ∧ k ≤ m) →
          sLocalPrincipalPartCoeff c k f.val = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) →
        (sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) : WithTop ℤ) ≤ meromorphicOrderAt Z s),
      (∃ g : sAdelePolarSubspace F S, (Kₛ(ωₛ)).mkQ (sAdelePrincipalValue F h₀ g.val) = x),
      (∃ g : adelePolarSubspace F, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g.val) = π x)
    ] := by
  intro hS ω hω ωₛ x π Z
  let : Subsingleton (CommRing.Pic ((S : Set Places).integer F)) := _hPic
  tfae_have 1 ↔ 2 := sLocalPolarPrincipalValue_one_two h₀ χ hS f
  tfae_have 2 ↔ 4 := by
    have hπ : π x = (K𝔽(ω)).mkQ (sAdeleSchwartzToGlobal F S f.val) :=
      sLocalHomogeneousThetaToGlobal_mk hω f.val
    rw [hπ]
    let f𝔽 : adelePolarSubspace F :=
      ⟨sAdeleSchwartzToGlobal F S f.val, sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
    exact sLocalPolarPrincipalValue_two_four h₀ χ hS f𝔽
  tfae_have 3 ↔ 4 := sLocalPolarPrincipalValue_three_four h₀ _hn _hPic ω hω x
  tfae_finish

end LocalPolesGlobalZeros

end RiemannMasullo
