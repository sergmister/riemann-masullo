module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b

import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Third Structure Theorem: strong duals and eigendistributions

Masullo, §5.5, pp. 277–285. The finite set in the S-local notation lists only
the finite places. The archimedean places are included in every S-local space.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Aₛ" => SAdeleRing F S
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "m𝔽" => ideleClassNorm F
local notation "Kₛ" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)
local notation "Kₛω(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "D(" V ")" => StrongDual ℂ V
local notation "pull(" K ")" =>
  ContinuousLinearMap.precomp (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) ℂ (Submodule.mkQL K)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartₛ(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S).continuous
    ((circleToComplex).comp χ)
local notation "restricts(" c ", " m ", " ω ")" =>
  (normOneRestriction m c = (circleToComplex).comp ω)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

section Eigendistributions

/-- Paper: Definition 5.5.1.1(1), p. 277.
The S-local weight space pulls the weight on S-idele classes back to the S-ideles
acting on Schwartz–Bruhat tests. The submodule carries its strong-dual subspace topology. -/
def sLocalEigendistributions (c : QuasiCharacter Jₛ) : Submodule ℂ D(ℬ(Aₛ)) :=
  schwartzBruhatEigendistributions
    (c.comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ : QuasiCharacter Aₛˣ)

/-- Paper: Definition 5.5.1.1(1), p. 277.
Membership is the weight equation after translating a test by an S-idele. -/
theorem mem_sLocalEigendistributions (c : QuasiCharacter Jₛ) (T : D(ℬ(Aₛ))) :
    T ∈ sLocalEigendistributions c ↔ ∀ (u : Aₛˣ) (f : ℬ(Aₛ)),
      T (schwartzBruhatUnitTranslate u f) = c (QuotientGroup.mk u) * T f := by
  exact Iff.rfl

/-- Paper: Definition 5.5.1.1(1), p. 277.
The S-local weight subspace is closed for the strong topology. -/
theorem sLocalEigendistributions_isClosed (c : QuasiCharacter Jₛ) :
    IsClosed (sLocalEigendistributions c : Set D(ℬ(Aₛ))) :=
  schwartzBruhatEigendistributions_isClosed _

/-- Paper: Definition 5.5.1.1(2), p. 278.
The global weight subspace of §3.4 is closed for the strong topology. -/
theorem adelicEigendistributions_isClosed (c : QuasiCharacter C𝔽) :
    IsClosed (adelicEigendistributions c : Set D(ℬ(𝔸[F]))) :=
  schwartzBruhatEigendistributions_isClosed _

end Eigendistributions

section SLocal

local notation "unitMass(" v ")" =>
  ((finiteLocalMultiplicativeTamagawaMeasure F v) (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal

private theorem sLocalNormalizedEigendistribution_mass_ne_zero :
    (↑(∏ v : S, unitMass(v.val)) : ℂ) ≠ 0 := by
  classical
  apply Complex.ofReal_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
  refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
  refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
  exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).trans' zero_lt_one

private theorem sLocalNormalizedEigendistribution_chart (c : QuasiCharacter Jₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), chartₛ(χ) s = c := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hne : ∃ g, mₛ g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa mₛ (isProperMap_sIdeleQuotientNorm F S) hne c
  let d := quasiCharacterNormTwist mₛ (isProperMap_sIdeleQuotientNorm F S).continuous c (-(a : ℂ))
  have hrad (g : Jₛ) : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa mₛ (isProperMap_sIdeleQuotientNorm F S) hne]
  have hd (g : Jₛ) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : Jₛ) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), ?_⟩
  ·
    ext1 g
    change d g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = c g
    rw [hd, hrad, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hn g))]


private theorem sLocalNormalizedEigendistribution_combine {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (Z : E →L[ℂ] ℂ) (I N : E → ℂ) (a : ℂ)
    (hZ : ∀ f, Z f = I f) (hN : ∀ f, N f = I f / a) :
    ∃ L : E →L[ℂ] ℂ, ∀ f, L f = N f := by
  refine ⟨a⁻¹ • Z, fun f ↦ ?_⟩
  change a⁻¹ * Z f = N f
  rw [hN f, ← hZ f, div_eq_mul_inv, mul_comm]

private theorem sLocalNormalizedEigendistribution_base (χ : PontryaginDual Jₛ) {z : ℂ} (hz : 0 < z.re) :
    ∃ L : ℬ(Aₛ) →L[ℂ] ℂ, ∀ f, L f = sLocalNormalizedZFunction f (chartₛ(χ) z) := by
  let d := chartₛ(χ) z
  have hd : ∃ (ψ : PontryaginDual Jₛ) (t : ℂ), 0 < t.re ∧ d = chartₛ(ψ) t := ⟨χ, z, hz, rfl⟩
  have h := sLocalIdelicZetaIntegral_tempered d hd
  have hz' : z ∈ Complex.re ⁻¹' Set.Ioi 0 := hz
  with_reducible_and_instances
    exact sLocalNormalizedEigendistribution_combine (E := ℬ(Aₛ)) h.choose (fun f ↦ sLocalIdelicZetaIntegral f d)
      (fun f ↦ sLocalNormalizedZFunction f d) (sLocalHeckeL d) h.choose_spec
      (fun f ↦ sLocalNormalizedZFunction_eq_div (F := F) (S := S) f χ hz')
private theorem sLocalNormalizedEigendistribution_taylor {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hz : z ∈ Metric.ball c r) :
    HasSum (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) := by
  obtain ⟨r', hr', hr'₀, hzr'⟩ : ∃ r' < r, 0 < r' ∧ z ∈ Metric.ball c r' := by
    obtain ⟨r', h₁, h₂⟩ := exists_between (Metric.mem_ball'.mp hz)
    exact ⟨r', h₂, Metric.pos_of_mem_ball h₁, Metric.mem_ball'.mpr h₁⟩
  lift r' to NNReal using hr'₀.le
  have hz' : z - c ∈ Metric.eball 0 r' := by
    rw [Metric.eball_coe]
    simpa only [mem_ball_iff_norm, sub_zero] using hzr'
  grw [← hr'] at hf
  have H := hf.hasFPowerSeriesOnBall hr'₀ |>.hasSum_iteratedFDeriv hz'
  simp only [add_sub_cancel] at H
  convert H with n
  simpa only [iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul, mul_one, Finset.prod_const,
    Finset.card_fin]
    using ((iteratedFDeriv ℂ n f c).map_smul_univ (fun _ ↦ z - c) (fun _ ↦ 1)).symm


/-- A pointwise holomorphic family of functionals on a barrelled space consists of continuous
linear functionals throughout a connected open set if it does so in a neighborhood of one point. -/
private theorem sLocalNormalizedEigendistribution_continuation
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hΦ : ∀ f, AnalyticOnNhd ℂ (Φ f) U)
    {b : ℂ} (hb : b ∈ U) (hbase : ∀ᶠ z in 𝓝 b, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z)
    {z : ℂ} (hz : z ∈ U) : ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z := by
  classical
  let P := {z : ℂ | ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z}
  let V := interior P ∩ U
  have hV : IsOpen V := isOpen_interior.inter hU
  have analyticDeriv (f : E) {x : ℂ} (hx : x ∈ U) (n : ℕ) : AnalyticAt ℂ (iteratedDeriv n (Φ f)) x := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hΦ f x hx
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  -- Difference quotients recover the Taylor coefficients wherever the evaluations are continuous.
  have hcoeff (n : ℕ) : ∀ y ∈ V, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n (Φ f) y := by
    induction n with
    | zero => exact fun y hy ↦ by simp only [iteratedDeriv_zero]; exact (interior_subset hy.1 : y ∈ P)
    | succ n ih =>
      intro x hx
      let A (y : ℂ) : E →L[ℂ] ℂ := if hy : y ∈ V then (ih y hy).choose else 0
      have hA {y : ℂ} (hy : y ∈ V) (f : E) : A y f = iteratedDeriv n (Φ f) y := by
        simpa only [A, dite_eq_left hy] using (ih y hy).choose_spec f
      let D (y : ℂ) := (y - x)⁻¹ • (A y - A x)
      have hlim : Filter.Tendsto (fun y f ↦ D y f) (𝓝[≠] x) (𝓝 fun f ↦ iteratedDeriv (n + 1) (Φ f) x) := by
        refine tendsto_pi_nhds.mpr fun f ↦ ?_
        have hd := analyticDeriv f hx.2 n
        rw [iteratedDeriv_succ]
        refine hd.differentiableAt.hasDerivAt.tendsto_slope.congr' ?_
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hx)] with y hy
        simp only [D, smul_apply, sub_apply, hA hy, hA hx, slope, vsub_eq_sub]
      exact ⟨continuousLinearMapOfTendsto D hlim, fun _ ↦ rfl⟩
  -- The Taylor series propagates continuity across every ball contained in the domain.
  have hball (y : ℂ) (hy : y ∈ V) {r : ℝ} (hr : Metric.ball y r ⊆ U) : Metric.ball y r ⊆ P := by
    choose A hA using fun n ↦ hcoeff n y hy
    intro x hx
    let T (s : Finset ℕ) : E →L[ℂ] ℂ := ∑ n ∈ s, (n.factorial : ℂ)⁻¹ • (x - y) ^ n • A n
    have hlim : Filter.Tendsto (fun s f ↦ T s f) Filter.atTop (𝓝 fun f ↦ Φ f x) := by
      refine tendsto_pi_nhds.mpr fun f ↦ ?_
      have h := sLocalNormalizedEigendistribution_taylor ((hΦ f).differentiableOn.mono hr) hx
      simp only [T, sum_apply, smul_apply, hA]
      exact h
    exact ⟨continuousLinearMapOfTendsto T hlim, fun _ ↦ rfl⟩
  apply interior_subset (s := P)
  suffices h : U ⊆ V from (h hz).1
  refine hconn.subset_of_closure_inter_subset hV ⟨b, hb, mem_interior_iff_mem_nhds.mpr hbase, hb⟩ ?_
  rintro x ⟨hx, hxU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (r / 2) (half_pos hr)
  have hballU : Metric.ball y (r / 2) ⊆ U := (Metric.ball_subset_ball' (by
    rw [dist_comm y x]; linarith : r / 2 + dist y x ≤ r)).trans hsub
  exact ⟨interior_maximal (hball y hy hballU) Metric.isOpen_ball hxy, hxU⟩

private theorem sLocalNormalizedEigendistribution_chart_continuous (χ : PontryaginDual Jₛ) (s : ℂ) :
    ∃ L : ℬ(Aₛ) →L[ℂ] ℂ, ∀ f, L f = sLocalNormalizedZFunction f (chartₛ(χ) s) := by
  let : BarrelledSpace ℂ ℬ(Aₛ) := (sAdeleSchwartz_montel (F := F) S).1
  have hpos : ∀ᶠ z : ℂ in 𝓝 1, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact sLocalNormalizedEigendistribution_continuation
    (fun f : ℬ(Aₛ) ↦ fun z ↦ sLocalNormalizedZFunction f (chartₛ(χ) z))
    isOpen_univ isPreconnected_univ (fun f ↦ sLocalNormalizedZFunction_entire f χ)
    (b := 1) (mem_univ _) (hpos.mono fun _ ↦ sLocalNormalizedEigendistribution_base χ) (mem_univ s)


private theorem sLocalNormalizedEigendistribution_unique {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (m : ℂ) (hm : m ≠ 0)
    (L : E →L[ℂ] ℂ) (N : E → ℂ) (hL : ∀ f, L f = N f) :
    ∃! T : E →L[ℂ] ℂ, ∀ f, m * T f = N f := by
  refine ⟨m⁻¹ • L, ?_, ?_⟩
  · intro f
    change m * (m⁻¹ * L f) = N f
    rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul, hL f]
  · intro T hT
    apply ContinuousLinearMap.ext
    intro f
    apply mul_left_cancel₀ hm
    change m * T f = m * (m⁻¹ * L f)
    rw [hT f, ← mul_assoc, mul_inv_cancel₀ hm, one_mul, hL f]

private theorem sLocalNormalizedEigendistribution_unique' {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (m : ℂ) (hm : m ≠ 0)
    (N : E → ℂ) (h : ∃ L : E →L[ℂ] ℂ, ∀ f, L f = N f) :
    ∃! T : E →L[ℂ] ℂ, ∀ f, m * T f = N f := by
  obtain ⟨L, hL⟩ := h
  exact sLocalNormalizedEigendistribution_unique m hm L N hL

private theorem sLocalNormalizedEigendistribution_propagate {E C I J : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (Z : E → C → ℂ)
    (chart : I → J → C) (hchart : ∀ c, ∃ i j, chart i j = c)
    (hZ : ∀ i j, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Z f (chart i j)) (c : C) :
    ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Z f c := by
  obtain ⟨i, j, rfl⟩ := hchart c
  exact hZ i j

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The continued normalized S-local zeta values give the tensor generator as a
continuous linear functional.
Deviation: The product of the finite integer-unit masses accounts for the
Tamagawa normalization of the local factors, as in §3.4. -/
theorem existsUnique_sLocalNormalizedEigendistribution (c : QuasiCharacter Jₛ) :
    ∃! T : D(ℬ(Aₛ)), ∀ f : ℬ(Aₛ),
      (↑(∏ v : S, unitMass(v.val)) : ℂ) * T f = sLocalNormalizedZFunction f c := by
  let Z : ℬ(Aₛ) → QuasiCharacter Jₛ → ℂ := fun f d ↦ sLocalNormalizedZFunction f d
  let chart : PontryaginDual Jₛ → ℂ → QuasiCharacter Jₛ := fun χ z ↦ chartₛ(χ) z
  have hc : ∀ d, ∃ χ z, chart χ z = d := sLocalNormalizedEigendistribution_chart (F := F) (S := S)
  have hz : ∀ χ z, ∃ L : ℬ(Aₛ) →L[ℂ] ℂ, ∀ f, L f = Z f (chart χ z) :=
    sLocalNormalizedEigendistribution_chart_continuous (F := F) (S := S)
  have h : ∃ L : ℬ(Aₛ) →L[ℂ] ℂ, ∀ f, L f = Z f c := by
    with_reducible_and_instances
      exact sLocalNormalizedEigendistribution_propagate (E := ℬ(Aₛ)) Z chart hc hz c
  have hm := sLocalNormalizedEigendistribution_mass_ne_zero (F := F) (S := S)
  with_reducible_and_instances
    exact sLocalNormalizedEigendistribution_unique' (E := ℬ(Aₛ)) _ hm (fun f ↦ Z f c) h

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The S-local generator is the functional given by the continued normalized zeta values.
Deviation: The normalization incorporates the finite integer-unit masses. -/
def sLocalNormalizedEigendistribution (c : QuasiCharacter Jₛ) : D(ℬ(Aₛ)) :=
  (existsUnique_sLocalNormalizedEigendistribution c).exists.choose

private theorem sLocalNormalizedEigendistribution_gaussian_arch
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) (η : PontryaginDual w.Completionˣ)
    (hη : (circleToComplex).comp η = sLocalInfiniteRestriction w ((circleToComplex).comp χ)) :
    letI : MeasurableSpace w.Completion := borel _
    ∀ᶠ z : ℂ in Filter.codiscrete ℂ, 0 < z.re →
      localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w)
        (fun x ↦ infiniteStandardGaussian w η (Multiplicative.ofAdd x))
        (sLocalInfiniteRestriction w (chartₛ(χ) z)) =
          infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z)) := by
  let : MeasurableSpace w.Completion := borel _
  let twist := quasiCharacterNormTwist _ (continuous_infiniteLocalModule w) ((circleToComplex).comp η)
  have he (z : ℂ) : sLocalInfiniteRestriction w (chartₛ(χ) z) = twist z := by
    ext1 g
    have hn := sLocalInfiniteRestriction_normTwist (S := S) w z g
    change (1 : ℂ) * _ = _ at hn
    rw [one_mul] at hn
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hη.symm g) hn
  obtain ⟨D, -, hD, hZ⟩ := infiniteEigendistribution_normalized w η
  filter_upwards [hZ] with z hz hpos
  rw [he, ← infiniteLocalIdelicZFunction_eq_integral w _ η hpos, hz,
    ((hD z (D z)).mp rfl).2, mul_one]

private theorem sLocalNormalizedEigendistribution_gaussian_finChart
    (χ : PontryaginDual Jₛ) (v : S) :
    ∃ η : PontryaginDual (v.val.adicCompletion F)ˣ, ∀ z,
      sLocalFiniteRestriction v (chartₛ(χ) z) =
        quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) ((circleToComplex).comp η) z := by
  let h := sLocalFiniteInsertion_properties v
  let i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ :=
    ⟨{ toFun := fun g ↦ QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
          ((v : S) → v.val.adicCompletion F)).symm (1, ContinuousMulEquiv.piUnits.symm
            (@Pi.mulSingle _ _ _ (Classical.decEq _) v g))),
       map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  refine ⟨χ.comp i, fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hn := sLocalFiniteRestriction_norm v g
  change ((1 : PontryaginDual Jₛ) (i g) : ℂ) *
    (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at hn
  simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] at hn
  exact congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ z) hn

private theorem sLocalNormalizedEigendistribution_gaussian_finTest
    (v : HeightOneSpectrum (𝓞 F)) (η : PontryaginDual (v.adicCompletion F)ˣ) (s z : ℂ) :
    let twist := quasiCharacterNormTwist _ (continuous_finiteLocalModule v) ((circleToComplex).comp η)
    finiteStandardGaussian v (twist s) = finiteStandardGaussian v (twist z) := by
  intro twist
  let U := (v.adicCompletionIntegers F).units
  have hu (u : (v.adicCompletion F)ˣ) (h : u ∈ U) : twist s u = twist z u := by
    have hn := Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp h)
    change (η u : ℂ) * (‖u.val‖ : ℂ) ^ s = (η u : ℂ) * (‖u.val‖ : ℂ) ^ z
    simp [hn]
  have h1 : (∀ u ∈ U, twist s u = 1) ↔ ∀ u ∈ U, twist z u = 1 :=
    forall₂_congr fun u h ↦ by rw [hu u h]
  apply Subtype.ext
  funext x
  change finiteStandardGaussianValue v (twist s) x.toAdd = finiteStandardGaussianValue v (twist z) x.toAdd
  rw [finiteStandardGaussianValue, finiteStandardGaussianValue]
  by_cases h0 : ∀ u ∈ U, twist s u = 1
  · rw [ite_eq_left h0, ite_eq_left (h1.mp h0)]
  · rw [ite_eq_right h0, ite_eq_right (mt h1.mpr h0)]
    by_cases hx : x.toAdd ∈ Units.val '' (U : Set (v.adicCompletion F)ˣ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      obtain ⟨u, hu', he⟩ := hx
      rw [← he, dite_eq_left u.ne_zero, dite_eq_left u.ne_zero, Units.mk0_val, hu u hu']
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

private theorem sLocalNormalizedEigendistribution_gaussian_fin
    (χ : PontryaginDual Jₛ) (v : S) (s z : ℂ) (hz : 0 < z.re)
    (hL : finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)) ≠ 0) :
    letI : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
    localIdelicZetaIntegral (finiteLocalMultiplicativeTamagawaMeasure F v.val)
      (fun x ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v (chartₛ(χ) s))
        (Multiplicative.ofAdd x)) (sLocalFiniteRestriction v (chartₛ(χ) z)) =
      unitMass(v.val) * finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)) := by
  obtain ⟨η, he⟩ := sLocalNormalizedEigendistribution_gaussian_finChart χ v
  let twist := quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) ((circleToComplex).comp η)
  have hne : twist z ≠ 1 := by
    intro h
    apply hL
    rw [(he z).trans h]
    simp [finiteLocalEulerFactor]
  obtain ⟨D, -, hD, hZ⟩ := finiteEigendistribution_normalized v.val η
  rw [he s, he z, sLocalNormalizedEigendistribution_gaussian_finTest v.val η s z,
    ← finiteLocalIdelicZFunction_eq_integral v.val _ η hz, hZ z hne,
    ((hD z (D z)).mp rfl).2, mul_one]

private theorem sLocalNormalizedEigendistribution_gaussian_heckeL_ne_zero (χ : PontryaginDual Jₛ) :
    ∀ᶠ z : ℂ in Filter.codiscrete ℂ, sLocalHeckeL (chartₛ(χ) z) ≠ 0 := by
  filter_upwards [sLocalRhoFactor_mul_dual χ, sLocalRhoFactor_eq_epsilon_mul χ] with z hprod hρ
  let c := chartₛ(χ) z
  have hr : sLocalRhoFactor c ≠ 0 := left_ne_zero_of_mul
    (hprod.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : Aₛˣ) : Jₛ)).map c).ne_zero)
  intro h
  apply hr
  exact hρ.trans (by rw [show sLocalHeckeL c = 0 from h, zero_div, mul_zero])

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The normalized S-local generator takes the value one on the pure tensor of the
local standard Gaussians of §3.4. -/
theorem sLocalNormalizedEigendistribution_gaussian (χ : PontryaginDual Jₛ) (s : ℂ)
    (χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ)
    (hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ))
    (f : ℬ(Aₛ))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w, infiniteStandardGaussian w (χArch w) (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, finiteStandardGaussian v.val (sLocalFiniteRestriction v (chartₛ(χ) s))
          (Multiplicative.ofAdd (x.2 v))) :
    sLocalNormalizedEigendistribution (chartₛ(χ) s) f = 1 := by
  classical
  let M : ℂ := ↑(∏ v : S, unitMass(v.val))
  let Z (z : ℂ) := sLocalNormalizedZFunction f (chartₛ(χ) z)
  have ha : AnalyticOnNhd ℂ Z univ := sLocalNormalizedZFunction_entire f χ
  have hpos : ∀ᶠ z in 𝓝[≠] (1 : ℂ), 0 < z.re := nhdsWithin_le_nhds
    ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (show (1 : ℂ) ∈ Complex.re ⁻¹' Ioi 0 by simp))
  have harch := Filter.eventually_all.mpr (fun w ↦
    sLocalNormalizedEigendistribution_gaussian_arch χ w (χArch w) (hχ w))
  -- On the convergence half-plane the zeta integral factors, and the Euler factors cancel.
  have hZ : ∀ᶠ z in 𝓝[≠] (1 : ℂ), Z z = M := by
    filter_upwards [hpos, nhdsNE_le_codiscrete _ harch,
      nhdsNE_le_codiscrete _ (sLocalNormalizedEigendistribution_gaussian_heckeL_ne_zero χ)] with z hz hA hL
    let c := chartₛ(χ) z
    have hF : ∏ v : S, finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) ≠ 0 :=
      right_ne_zero_of_mul hL
    change sLocalNormalizedZFunction f c = M
    rw [sLocalNormalizedZFunction_eq_div f χ hz, div_eq_iff hL,
      sLocalIdelicZetaIntegral_pureTensor c ⟨χ, z, hz, rfl⟩ f
        (fun w ↦ infiniteStandardGaussian w (χArch w))
        (fun v ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v (chartₛ(χ) s))) hf]
    rw [Finset.prod_congr (s₁ := Finset.univ) rfl (fun w _ ↦ hA w hz),
      Finset.prod_congr (s₁ := Finset.univ) rfl (fun v _ ↦
        sLocalNormalizedEigendistribution_gaussian_fin χ v s z hz
          (Finset.prod_ne_zero_iff.mp hF v (Finset.mem_univ v)))]
    simp only [M, Complex.ofReal_prod, Finset.prod_mul_distrib, sLocalHeckeL]
    exact mul_left_comm _ _ _
  -- Continue this constant value along the whole norm chart.
  have hAll : Z = fun _ ↦ M := ha.eq_of_frequently_eq (z₀ := 1) analyticOnNhd_const hZ.frequently
  have hM : M ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    refine Finset.prod_ne_zero_iff.mpr fun v _ ↦ ?_
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    apply inv_ne_zero
    refine (Real.sqrt_pos.mpr (pow_pos ?_ _)).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v.val).trans' zero_lt_one
  have hspec : M * sLocalNormalizedEigendistribution (chartₛ(χ) s) f = Z s :=
    (existsUnique_sLocalNormalizedEigendistribution (chartₛ(χ) s)).exists.choose_spec f
  exact mul_left_cancel₀ hM (hspec.trans ((congrFun hAll s).trans (mul_one M).symm))

/-- Paper: Theorem 5.5.1.2(1), p. 278.
On a pure tensor the S-local generator is the product of the local Gaussian-normalized
eigendistributions. The restrictions of the weight specify the local eigen equations. -/
theorem sLocalNormalizedEigendistribution_apply_pureTensor (χ : PontryaginDual Jₛ) (s : ℂ)
    (χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ)
    (hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ))
    (TArch : (w : InfinitePlace F) → D(ℬ(w.Completion)))
    (TFin : (v : S) → D(ℬ(v.val.adicCompletion F)))
    (hArch : ∀ w, TArch w ∈
      schwartzBruhatEigendistributions (sLocalInfiniteRestriction w (chartₛ(χ) s)) ∧
      TArch w (infiniteStandardGaussian w (χArch w)) = 1)
    (hFin : ∀ v, TFin v ∈
      schwartzBruhatEigendistributions (sLocalFiniteRestriction v (chartₛ(χ) s)) ∧
      TFin v (finiteStandardGaussian v.val (sLocalFiniteRestriction v (chartₛ(χ) s))) = 1)
    (f : ℬ(Aₛ)) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
    (fFin : (v : S) → ℬ(v.val.adicCompletion F))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w, fArch w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, fFin v (Multiplicative.ofAdd (x.2 v))) :
    sLocalNormalizedEigendistribution (chartₛ(χ) s) f =
      (∏ w, TArch w (fArch w)) * ∏ v : S, TFin v (fFin v) := by sorry

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The normalized S-local distribution spans the eigenspace of its weight. -/
theorem sLocalEigendistributions_eq_span (c : QuasiCharacter Jₛ) :
    sLocalEigendistributions c =
      Submodule.span ℂ {sLocalNormalizedEigendistribution c} := by sorry

/-- On a Montel space, pointwise holomorphy of a family in the complete strong dual
implies strong holomorphy, since every bidual functional is an evaluation. -/
private theorem sLocalNormalizedEigendistribution_holomorphic_pointwise
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    [MontelSpace ℂ E] [CompleteSpace (StrongDual ℂ E)]
    [PolynormableSpace ℂ (StrongDual ℂ E)]
    (T : ℂ → StrongDual ℂ E)
    (hT : ∀ x : E, DifferentiableOn ℂ (fun z ↦ T z x) univ) :
    VectorHolomorphicOn T univ := by
  have : @QuasiCompleteSpace ℂ (StrongDual ℂ E) _
      (IsTopologicalAddGroup.rightUniformSpace _) _ _ := by
    convert (inferInstance : QuasiCompleteSpace ℂ (StrongDual ℂ E)) using 1
    exact IsUniformAddGroup.rightUniformSpace_eq
  apply WeaklyHolomorphicOn.vectorHolomorphicOn isOpen_univ isConnected_univ
  intro φ
  obtain ⟨x, rfl⟩ := surjective_strongBidual_eval (E := E) φ
  exact hT x

/-- Paper: Theorem 5.5.1.2(1), p. 278.
The normalized S-local distributions form a holomorphic family on each norm chart. -/
theorem sLocalNormalizedEigendistribution_holomorphic (χ : PontryaginDual Jₛ) :
    VectorHolomorphicOn (fun s ↦ sLocalNormalizedEigendistribution (chartₛ(χ) s)) univ := by
  let : UniformSpace ℬ(Aₛ) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup ℬ(Aₛ) := isUniformAddGroup_of_addCommGroup
  let : T2Space ℬ(Aₛ) := (sAdeleSchwartz_nuclear.{_, 0} F S).1
  let : PolynormableSpace ℂ ℬ(Aₛ) := (sAdeleSchwartz_nuclear.{_, 0} F S).2.1
  let : MontelSpace ℂ ℬ(Aₛ) := (sAdeleSchwartz_montel F S).2
  let : CompleteSpace D(ℬ(Aₛ)) := sAdeleSchwartz_strongDual_complete F S
  let : PolynormableSpace ℂ D(ℬ(Aₛ)) := (sAdeleSchwartz_strongDual_nuclear.{_, 0} F S).2.1
  apply sLocalNormalizedEigendistribution_holomorphic_pointwise
  intro f
  let M : ℂ := ↑(∏ v : S, unitMass(v.val))
  have hM : M ≠ 0 := sLocalNormalizedEigendistribution_mass_ne_zero
  have he : (fun z ↦ sLocalNormalizedEigendistribution (chartₛ(χ) z) f) =
      (fun z ↦ M⁻¹ * sLocalNormalizedZFunction f (chartₛ(χ) z)) := by
    funext z
    have h := (existsUnique_sLocalNormalizedEigendistribution (chartₛ(χ) z)).exists.choose_spec f
    change M * sLocalNormalizedEigendistribution (chartₛ(χ) z) f = _ at h
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hM, one_mul]
  rw [he]
  exact (sLocalNormalizedZFunction_entire f χ).differentiableOn.const_mul M⁻¹

/-- Paper: Theorem 5.5.1.2(2), pp. 278–279.
Each S-local eigendistribution has a unique continuous descent to the theta space.
On quotient representatives, its descended weight equation follows the same convention
as Definition 5.5.1.1. -/
theorem sLocalEigendistribution_descends (c : QuasiCharacter Jₛ) (T : D(ℬ(Aₛ)))
    (hT : T ∈ sLocalEigendistributions c) :
    ∃! U : D(SLocalAdelicThetaSpace F S), pull(Kₛ) U = T := by sorry

/-- Paper: Equation (5.5.1.12), p. 279.
The normalized S-local eigendistribution annihilates the theta kernel. -/
theorem sLocalThetaKernel_le_eigendistribution (c : QuasiCharacter Jₛ) :
    Kₛ ≤ (sLocalNormalizedEigendistribution c).ker := by
  have annihilates {M : Type _} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
      (K : Submodule ℂ M) (W : Submodule ℂ (StrongDual ℂ M)) (T : StrongDual ℂ M)
      (hW : W = Submodule.span ℂ {T})
      (hd : ∀ D ∈ W, ∃! U : StrongDual ℂ (M ⧸ K), pull(K) U = D) : K ≤ T.ker := by
    have hT : T ∈ W := hW ▸ Submodule.subset_span (Set.mem_singleton T)
    obtain ⟨U, rfl⟩ := (hd T hT).exists
    intro f hf
    change U (Submodule.Quotient.mk f) = 0
    exact (congrArg U ((Submodule.Quotient.mk_eq_zero K).mpr hf)).trans (map_zero U)
  with_reducible_and_instances
    exact annihilates (M := ℬ(Aₛ)) (Kₛ) (sLocalEigendistributions (F := F) (S := S) c)
      (sLocalNormalizedEigendistribution (F := F) (S := S) c)
      (sLocalEigendistributions_eq_span (F := F) (S := S) c)
      (sLocalEigendistribution_descends (F := F) (S := S) c)

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The generator on the S-local theta quotient is the continuous descent of the
normalized eigendistribution. -/
def sLocalThetaEigendistribution (c : QuasiCharacter Jₛ) : D(SLocalAdelicThetaSpace F S) :=
  (Kₛ).liftQL (sLocalNormalizedEigendistribution c) (sLocalThetaKernel_le_eigendistribution c)

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The descended generator evaluates on a theta class by acting on its Schwartz–Bruhat
representative. -/
theorem sLocalThetaEigendistribution_mk (c : QuasiCharacter Jₛ) (f : ℬ(Aₛ)) :
    sLocalThetaEigendistribution c ((Kₛ).mkQL f) = sLocalNormalizedEigendistribution c f := by
  rfl

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The eigenspace in the S-local theta dual is the line through the descended generator.
The weight condition is tested after pullback to Schwartz–Bruhat functions. -/
theorem sLocalThetaEigendistributions_eq_span (c : QuasiCharacter Jₛ) :
    (sLocalEigendistributions c).comap (pull(Kₛ)).toLinearMap =
      Submodule.span ℂ {sLocalThetaEigendistribution c} := by
  -- Pullback along the quotient map is injective and sends the descended generator to
  -- the generator of the eigenline upstairs.
  have quotientLine {M : Type _} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
      (K : Submodule ℂ M) (W : Submodule ℂ (StrongDual ℂ M))
      (T : StrongDual ℂ M) (U : StrongDual ℂ (M ⧸ K)) (hW : W = Submodule.span ℂ {T})
      (hU : ∀ f, U (K.mkQL f) = T f) :
      W.comap (pull(K)).toLinearMap = Submodule.span ℂ {U} := by
    let L := (pull(K)).toLinearMap
    have hinj : Injective L := by
      intro a b h
      apply ContinuousLinearMap.ext
      intro x
      obtain ⟨f, rfl⟩ := K.mkQ_surjective x
      exact congrArg (fun t : StrongDual ℂ M ↦ t f) h
    have he : L U = T := ContinuousLinearMap.ext hU
    have hm : (Submodule.span ℂ {U}).map L = W := by
      rw [Submodule.map_span, Set.image_singleton, he, hW]
    exact (congrArg (fun p : Submodule ℂ (StrongDual ℂ M) ↦ p.comap L) hm.symm).trans
      (Submodule.comap_map_eq_of_injective hinj _)
  exact quotientLine (M := ℬ(Aₛ)) (Kₛ) (sLocalEigendistributions (F := F) (S := S) c)
    (sLocalNormalizedEigendistribution (F := F) (S := S) c)
    (sLocalThetaEigendistribution (F := F) (S := S) c)
    (sLocalEigendistributions_eq_span (F := F) (S := S) c)
    (sLocalThetaEigendistribution_mk (F := F) (S := S) c)

/-- Paper: Theorem 5.5.1.2(2), p. 278.
The normalized S-local family in the strong dual of the theta quotient is holomorphic. -/
theorem sLocalThetaEigendistribution_holomorphic (χ : PontryaginDual Jₛ) :
    VectorHolomorphicOn (fun s ↦ sLocalThetaEigendistribution (chartₛ(χ) s)) univ := by sorry

end SLocal

section Global

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The global normalized generator from §3.4 is uniquely specified by its
weight and by its value on the standard Gaussian in any chart. -/
theorem existsUnique_adelicNormalizedEigendistribution (c : QuasiCharacter C𝔽) :
    ∃! T : D(ℬ(𝔸[F])), T ∈ adelicEigendistributions c ∧
      ∀ (χ : PontryaginDual C𝔽) (s : ℂ), ideleClassNormTwist χ s = c →
        T (adelicStandardGaussian χ) = 1 := by sorry

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The global generator is the Gaussian-normalized eigendistribution.
Its restricted tensor evaluations are given by `adelicEigendistribution_apply_pureTensor`. -/
def adelicNormalizedEigendistribution (c : QuasiCharacter C𝔽) : D(ℬ(𝔸[F])) :=
  (existsUnique_adelicNormalizedEigendistribution c).exists.choose

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The global normalized generator takes the value one on the Gaussian for its weight. -/
theorem adelicNormalizedEigendistribution_gaussian (χ : PontryaginDual C𝔽) (s : ℂ) :
    adelicNormalizedEigendistribution (ideleClassNormTwist χ s) (adelicStandardGaussian χ) =
      1 := by
  exact (existsUnique_adelicNormalizedEigendistribution
    (ideleClassNormTwist χ s)).exists.choose_spec.2 χ s rfl

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The normalized global distribution spans the eigenspace of its weight. -/
theorem adelicEigendistributions_eq_span (c : QuasiCharacter C𝔽) :
    adelicEigendistributions c = Submodule.span ℂ {adelicNormalizedEigendistribution c} := by
  have spans {V : Type _} {I : Type _} [AddCommGroup V] [Module ℂ V]
      (E : Submodule ℂ V) (T : V) (test : I → V → ℂ) (hzero : ∀ i, test i 0 = 0)
      (hr : Module.finrank ℂ E = 1) (hT : T ∈ E) (hn : ∀ i, test i T = 1)
      (unique : ∀ U ∈ E, (∀ i, test i U = 1) → U = T) : E = Submodule.span ℂ {T} := by
    apply eq_span_singleton_of_mem_of_finrank_eq_one hr hT
    intro hz
    -- If zero were normalized, there could be no tests, so every vector would qualify.
    have noTest (i : I) : False :=
      zero_ne_one (((hzero i).symm.trans (congrArg (test i) hz).symm).trans (hn i))
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hr
    obtain ⟨U, hU⟩ := exists_ne (0 : E)
    exact hU (Subtype.ext ((unique U U.property (fun i ↦ (noTest i).elim)).trans hz))
  let Charts := {p : PontryaginDual C𝔽 × ℂ // ideleClassNormTwist p.1 p.2 = c}
  have hT := (existsUnique_adelicNormalizedEigendistribution (F := F) c).exists.choose_spec
  refine spans (V := D(ℬ(𝔸[F]))) (I := Charts) (adelicEigendistributions (F := F) c)
    (adelicNormalizedEigendistribution (F := F) c)
    (fun (p : Charts) (U : D(ℬ(𝔸[F]))) ↦ U (adelicStandardGaussian (F := F) p.val.1)) (fun _ ↦ rfl)
    (Module.rank_eq_one_iff_finrank_eq_one.mp (adelicEigendistributions_rank (F := F) c)) hT.1
    (fun p ↦ hT.2 p.val.1 p.val.2 p.property) ?_
  intro U hU hn
  exact (existsUnique_adelicNormalizedEigendistribution (F := F) c).unique
    ⟨hU, fun χ s hc ↦ hn ⟨(χ, s), hc⟩⟩ hT

/-- Paper: Theorem 5.5.1.3(1), p. 279.
The normalized global distributions form a holomorphic family on each norm chart. -/
theorem adelicNormalizedEigendistribution_holomorphic (χ : PontryaginDual C𝔽) :
    VectorHolomorphicOn (fun s ↦ adelicNormalizedEigendistribution (ideleClassNormTwist χ s))
      univ := by
  let D := (adelicEigendistribution_normalized χ).choose
  have h := (adelicEigendistribution_normalized χ).choose_spec
  have he (s : ℂ) : adelicNormalizedEigendistribution (ideleClassNormTwist χ s) = D s := by
    have hs := (existsUnique_adelicNormalizedEigendistribution (ideleClassNormTwist χ s)).exists.choose_spec
    exact (h.2.1 s _).mpr ⟨hs.1, hs.2 χ s rfl⟩
  exact (congrArg (fun G : ℂ → D(ℬ(𝔸[F])) ↦ VectorHolomorphicOn G univ) (funext he)).mpr h.1

/-- Paper: Theorem 5.5.1.3(2), p. 279.
Each global eigendistribution descends uniquely to the theta quotient. The pullback
equation identifies the descended distribution and encodes its weight on representatives. -/
theorem adelicEigendistribution_descends (c : QuasiCharacter C𝔽) (T : D(ℬ(𝔸[F])))
    (hT : T ∈ adelicEigendistributions c) :
    ∃! U : D(GlobalAdelicThetaSpace F), pull(K𝔽) U = T := by sorry

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The normalized adelic eigendistribution annihilates the global theta kernel,
so its descent is a continuous linear quotient lift. -/
theorem globalThetaKernel_le_eigendistribution (c : QuasiCharacter C𝔽) :
    K𝔽 ≤ (adelicNormalizedEigendistribution c).ker := by
  have annihilates {M : Type _} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
      (K : Submodule ℂ M) (T : StrongDual ℂ M)
      (h : ∃ U : StrongDual ℂ (M ⧸ K), pull(K) U = T) : K ≤ T.ker := by
    obtain ⟨U, rfl⟩ := h
    intro f hf
    change U (Submodule.Quotient.mk f) = 0
    exact (congrArg U ((Submodule.Quotient.mk_eq_zero K).mpr hf)).trans (map_zero U)
  exact annihilates (M := ℬ(𝔸[F])) (K𝔽) (adelicNormalizedEigendistribution (F := F) c)
    (adelicEigendistribution_descends (F := F) c _
      (existsUnique_adelicNormalizedEigendistribution (F := F) c).exists.choose_spec.1).exists

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The generator on the global theta quotient is the continuous descent of the
normalized adelic eigendistribution. -/
def globalThetaEigendistribution (c : QuasiCharacter C𝔽) : D(GlobalAdelicThetaSpace F) :=
  Submodule.liftQL (σ := RingHom.id ℂ) (M := ℬ(𝔸[F])) (M₂ := ℂ) (K𝔽)
    (adelicNormalizedEigendistribution (F := F) c) (globalThetaKernel_le_eigendistribution (F := F) c)

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The descended global generator evaluates on a theta class by acting on its representative. -/
theorem globalThetaEigendistribution_mk (c : QuasiCharacter C𝔽) (f : ℬ(𝔸[F])) :
    globalThetaEigendistribution c ((K𝔽).mkQL f) = adelicNormalizedEigendistribution c f := by
  rfl

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The eigenspace in the global theta dual is the line through the descended generator,
with the weight condition tested on the pullback. -/
theorem globalThetaEigendistributions_eq_span (c : QuasiCharacter C𝔽) :
    (adelicEigendistributions c).comap (pull(K𝔽)).toLinearMap =
      Submodule.span ℂ {globalThetaEigendistribution c} := by
  have quotientLine {M : Type _} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
      (K : Submodule ℂ M) (W : Submodule ℂ (StrongDual ℂ M))
      (T : StrongDual ℂ M) (U : StrongDual ℂ (M ⧸ K)) (hW : W = Submodule.span ℂ {T})
      (hU : ∀ f, U (K.mkQL f) = T f) :
      W.comap (pull(K)).toLinearMap = Submodule.span ℂ {U} := by
    let L := (pull(K)).toLinearMap
    have hinj : Injective L := by
      intro a b h
      apply ContinuousLinearMap.ext
      intro x
      obtain ⟨f, rfl⟩ := K.mkQ_surjective x
      exact congrArg (fun t : StrongDual ℂ M ↦ t f) h
    have he : L U = T := ContinuousLinearMap.ext hU
    have hm : (Submodule.span ℂ {U}).map L = W := by
      rw [Submodule.map_span, Set.image_singleton, he, hW]
    exact (congrArg (fun p : Submodule ℂ (StrongDual ℂ M) ↦ p.comap L) hm.symm).trans
      (Submodule.comap_map_eq_of_injective hinj _)
  exact quotientLine (M := ℬ(𝔸[F])) (K𝔽) (adelicEigendistributions (F := F) c)
    (adelicNormalizedEigendistribution (F := F) c) (globalThetaEigendistribution (F := F) c)
    (adelicEigendistributions_eq_span (F := F) c) (globalThetaEigendistribution_mk (F := F) c)

/-- Paper: Theorem 5.5.1.3(2), p. 279.
The normalized global family in the strong dual of the theta quotient is holomorphic. -/
theorem globalThetaEigendistribution_holomorphic (χ : PontryaginDual C𝔽) :
    VectorHolomorphicOn (fun s ↦ globalThetaEigendistribution (ideleClassNormTwist χ s))
      univ := by sorry

/-- Paper: Remark 5.5.1.4, p. 280.
The descended S-local eigendistributions span a strongly dense subspace of the theta dual. -/
theorem sLocalThetaEigendistributions_dense_span :
    Dense (Submodule.span ℂ (Set.range (sLocalThetaEigendistribution (F := F) (S := S))) :
      Set D(SLocalAdelicThetaSpace F S)) := by sorry

end Global

section PolarValues

local notation "Θ" => GlobalAdelicThetaSpace F
local notation "unitaryOne" => (1 : PontryaginDual C𝔽)
local notation "normWeight" => ideleClassNormTwist unitaryOne 1
local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose
local notation "normℂ(" g ")" => (((m𝔽 g : ℝ≥0) : ℝ) : ℂ)

/-- Paper: Lemma 5.5.2.1, p. 280.
The theta kernel is contained in the common polar kernel from §2.2.4, so both
continuous polar functionals vanish on it. -/
theorem globalThetaKernel_le_adelePolarSubspace :
    K𝔽 ≤ LinearMap.ker (adelePolarValues (F := F)) := by
  intro f hf
  have hθ (g : C𝔽) : adelicTheta f g = 0 := DFunLike.congr_fun (LinearMap.mem_ker.1 hf) g
  obtain ⟨C, T, -, hT, hsmall⟩ := adelicTheta_decay_small f 1
  set a := adeleSchwartzFourier f zeroAdele
  set b := f zeroAdele
  -- Every positive real is the norm of an idele class.
  have key (t : ℝ) (ht : 0 < t) (htT : t < T) : ‖b - t⁻¹ • a‖ ≤ C * t := by
    let u : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ fun h0 ↦ ht.ne' (congrArg Subtype.val h0)
    let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F u)
    have hg : ((m𝔽 g : ℝ≥0) : ℝ) = t := by
      change ((ideleNorm F (canonicalIdeleNormSection F u) : ℝ≥0) : ℝ) = t
      rw [canonicalIdeleNormSection_rightInverse F u]
      rfl
    have h := hsmall g (by beta_reduce; rw [hg]; exact htT)
    beta_reduce at h
    rw [hθ, hg, pow_one] at h
    rwa [zero_sub, neg_add_eq_sub] at h
  have hid : Filter.Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Filter.Tendsto (fun t : ℝ ↦ b - t⁻¹ • a) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hid.const_mul C)
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    exact key t ht.1 ht.2
  have h2 : Filter.Tendsto (fun t : ℝ ↦ t • (b - t⁻¹ • a)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hid.smul hlim
  have h3 : Filter.Tendsto (fun t : ℝ ↦ t • (b - t⁻¹ • a)) (𝓝[>] 0) (𝓝 (-a)) := by
    have he : (fun t : ℝ ↦ t • b - a) =ᶠ[𝓝[>] 0] fun t : ℝ ↦ t • (b - t⁻¹ • a) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
    refine Filter.Tendsto.congr' he ?_
    have hc : Filter.Tendsto (fun t : ℝ ↦ t • b - a) (𝓝 0) (𝓝 ((0 : ℝ) • b - a)) :=
      ((continuous_id.smul continuous_const).sub continuous_const).tendsto 0
    simpa using hc.mono_left nhdsWithin_le_nhds
  have ha : a = 0 := neg_eq_zero.mp (tendsto_nhds_unique h2 h3).symm
  have hb : b = 0 := by
    simp only [ha, smul_zero, sub_zero] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  rw [LinearMap.mem_ker, adelePolarValues_apply]
  exact Prod.ext hb ha

/-- Paper: Lemma 5.5.2.1, p. 280.
Evaluation at zero and Fourier evaluation at zero descend as a pair of
continuous linear functionals on the global theta quotient. -/
def globalThetaPolarValues : Θ →L[ℂ] ℂ × ℂ :=
  ⟨Submodule.liftQ (τ₁₂ := RingHom.id ℂ) (K𝔽) (adelePolarValues (F := F))
      (globalThetaKernel_le_adelePolarSubspace (F := F)),
    continuous_quot_lift _ (adelePolarValues_continuous (F := F))⟩

/-- Paper: Lemma 5.5.2.1, p. 280.
The two descended values on a theta class are the evaluations at zero of its
representative and of the Fourier transform of that representative. -/
theorem globalThetaPolarValues_mk (f : ℬ(𝔸[F])) :
    globalThetaPolarValues (F := F) ((K𝔽).mkQL f) =
      (f zeroAdele, adeleSchwartzFourier f zeroAdele) := by
  rfl

/-- Two continuous linear maps on a quotient module are equal when they agree on the classes
of all representatives. -/
private theorem globalThetaPolarValues_unique_aux {E G : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (K : Submodule ℂ E) (P Q : (E ⧸ K) →L[ℂ] G) (h : ∀ f, P (K.mkQL f) = Q (K.mkQL f)) :
    P = Q := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  obtain ⟨f, rfl⟩ := K.mkQ_surjective x
  exact h f

/-- Paper: Lemma 5.5.2.1, p. 280.
The evaluations on test representatives uniquely determine the descended pair. -/
theorem globalThetaPolarValues_unique (P : Θ →L[ℂ] ℂ × ℂ)
    (hP : ∀ f : ℬ(𝔸[F]), P ((K𝔽).mkQL f) = (f zeroAdele, adeleSchwartzFourier f zeroAdele)) :
    P = globalThetaPolarValues (F := F) := by
  exact globalThetaPolarValues_unique_aux _ P _ fun f ↦ (hP f).trans
    (globalThetaPolarValues_mk f).symm

/-- A functional component on a quotient scales by `c` under an action given on
representatives by `t`, when it does so on representatives. -/
private theorem globalThetaPolarValues_translate_aux {E H G : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (K : Submodule ℂ E) (π : H → G) (hπ : Surjective π)
    (ρ : G → (E ⧸ K) → (E ⧸ K)) (t : H → E → E)
    (hρ : ∀ g f, ρ (π g) (Submodule.Quotient.mk f) = Submodule.Quotient.mk (t g f))
    (P : (E ⧸ K) →L[ℂ] ℂ × ℂ) (c : G → ℂ) (pr : ℂ × ℂ → ℂ)
    (hP : ∀ g f, pr (P (K.mkQL (t g f))) = c (π g) * pr (P (K.mkQL f))) (g : G) (x : E ⧸ K) :
    pr (P (ρ g x)) = c g * pr (P x) := by
  obtain ⟨g, rfl⟩ := hπ g
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective K x
  rw [hρ g f]
  exact hP g f

/-- On representatives, evaluation at zero is unchanged by unit translation. -/
private theorem globalThetaPolarValues_fst_translate_rep (g : IdeleGroup (𝓞 F) F)
    (f : ℬ(𝔸[F])) :
    (globalThetaPolarValues (F := F) ((K𝔽).mkQL (schwartzBruhatUnitTranslate g f))).1 =
      (fun _ : C𝔽 ↦ (1 : ℂ)) (QuotientGroup.mk g) *
        (globalThetaPolarValues (F := F) ((K𝔽).mkQL f)).1 := by
  refine (congrArg Prod.fst (globalThetaPolarValues_mk (F := F)
    (schwartzBruhatUnitTranslate g f))).trans (Eq.trans ?_ (congrArg (fun z ↦ (1 : ℂ) * z)
      (congrArg Prod.fst (globalThetaPolarValues_mk (F := F) f))).symm)
  change schwartzBruhatUnitTranslate g f zeroAdele = 1 * f zeroAdele
  rw [schwartzBruhatUnitTranslate_apply, mul_zero, one_mul]

/-- Paper: Lemma 5.5.2.1, p. 280.
Evaluation at zero on the global theta quotient has weight one. -/
theorem globalThetaPolarValues_fst_translate (g : C𝔽) (x : Θ) :
    (globalThetaPolarValues (F := F) (ρ𝔽 g x)).1 = (globalThetaPolarValues (F := F) x).1 := by
  have hρ := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
  have h := globalThetaPolarValues_translate_aux (E := ℬ(𝔸[F])) (K𝔽) QuotientGroup.mk
    QuotientGroup.mk_surjective (fun g x ↦ ρ𝔽 g x) schwartzBruhatUnitTranslate hρ
    (globalThetaPolarValues (F := F)) (fun _ ↦ 1) Prod.fst
    globalThetaPolarValues_fst_translate_rep g x
  with_reducible_and_instances exact h.trans (one_mul _)

open MeasureTheory in
/-- Integration against the additive Tamagawa measure scales by the idelic norm under
multiplication by an inverse idele. -/
private theorem adeleSchwartzFourier_zero_unitTranslate_integral (u : IdeleGroup (𝓞 F) F)
    (k : 𝔸[F] → ℂ) :
    ∫ x, k ((↑u⁻¹ : 𝔸[F]) * x) ∂additiveTamagawaMeasure F =
      (((ideleNorm F u).val : ℝ) : ℂ) * ∫ x, k x ∂additiveTamagawaMeasure F := by
  let : MeasurableSpace 𝔸[F] := borel _
  have : BorelSpace 𝔸[F] := ⟨rfl⟩
  have hH : (additiveTamagawaMeasure F).IsAddHaarMeasure :=
    (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let d : 𝔸[F] ≃ₜ 𝔸[F] := Homeomorph.smul (u⁻¹ : IdeleGroup (𝓞 F) F)
  have hset (s : Set 𝔸[F]) :
      d ⁻¹' s = (fun a : 𝔸[F] ↦ (u : 𝔸[F]) * a) '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨(↑u⁻¹ : 𝔸[F]) * y, hy, Units.mul_inv_cancel_left u y⟩
    · rintro ⟨a, ha, rfl⟩
      change (↑u⁻¹ : 𝔸[F]) * ((u : 𝔸[F]) * a) ∈ s
      rwa [Units.inv_mul_cancel_left]
  have hmap : (additiveTamagawaMeasure F).map d =
      ((ideleNorm F u).val : ENNReal) • additiveTamagawaMeasure F := by
    refine Measure.ext fun s hs ↦ ?_
    rw [Measure.map_apply d.continuous.measurable hs, hset s]
    exact adeleHaar_mul_image F (additiveTamagawaMeasure F) u s hs
  have h1 : ∫ x, k (d.toMeasurableEquiv x) ∂additiveTamagawaMeasure F =
      ∫ y, k y ∂((additiveTamagawaMeasure F).map d.toMeasurableEquiv) :=
    (integral_map_equiv d.toMeasurableEquiv k).symm
  have h2 : ((additiveTamagawaMeasure F).map d.toMeasurableEquiv) =
      ((ideleNorm F u).val : ENNReal) • additiveTamagawaMeasure F := hmap
  rw [h2, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul] at h1
  exact h1

/-- Fourier evaluation at zero scales by the idelic norm under unit translation. -/
private theorem adeleSchwartzFourier_zero_unitTranslate (u : IdeleGroup (𝓞 F) F)
    (f : ℬ(𝔸[F])) :
    adeleSchwartzFourier (schwartzBruhatUnitTranslate u f) zeroAdele =
      (((ideleNorm F u).val : ℝ) : ℂ) * adeleSchwartzFourier f zeroAdele := by
  have hA := (adeleSchwartzFourier_apply_zero (schwartzBruhatUnitTranslate u f)).2
  have hB := (adeleSchwartzFourier_apply_zero f).2
  have hI := adeleSchwartzFourier_zero_unitTranslate_integral u
    (fun z : 𝔸[F] ↦ f (Multiplicative.ofAdd z))
  exact hA.trans (hI.trans (congrArg _ hB.symm))

/-- On representatives, Fourier evaluation at zero scales by the idelic norm under unit
translation. -/
private theorem globalThetaPolarValues_snd_translate_rep (g : IdeleGroup (𝓞 F) F)
    (f : ℬ(𝔸[F])) :
    (globalThetaPolarValues (F := F) ((K𝔽).mkQL (schwartzBruhatUnitTranslate g f))).2 =
      (fun g : C𝔽 ↦ normℂ(g)) (QuotientGroup.mk g) *
        (globalThetaPolarValues (F := F) ((K𝔽).mkQL f)).2 := by
  have hn : normℂ((QuotientGroup.mk g : C𝔽)) = (((ideleNorm F g).val : ℝ) : ℂ) := rfl
  refine (congrArg Prod.snd (globalThetaPolarValues_mk (F := F)
    (schwartzBruhatUnitTranslate g f))).trans (Eq.trans ?_ (congrArg (fun z ↦ normℂ((QuotientGroup.mk g : C𝔽)) * z)
      (congrArg Prod.snd (globalThetaPolarValues_mk (F := F) f))).symm)
  exact (adeleSchwartzFourier_zero_unitTranslate g f).trans (congrArg (· * _) hn.symm)

/-- Paper: Lemma 5.5.2.1, p. 280.
Fourier evaluation at zero on the global theta quotient has weight equal to the idelic norm. -/
theorem globalThetaPolarValues_snd_translate (g : C𝔽) (x : Θ) :
    (globalThetaPolarValues (F := F) (ρ𝔽 g x)).2 = normℂ(g) * (globalThetaPolarValues (F := F) x).2 := by
  have hρ := (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2
  have h := globalThetaPolarValues_translate_aux (E := ℬ(𝔸[F])) (K𝔽) QuotientGroup.mk
    QuotientGroup.mk_surjective (fun g x ↦ ρ𝔽 g x) schwartzBruhatUnitTranslate hρ
    (globalThetaPolarValues (F := F)) (fun g ↦ normℂ(g)) Prod.snd
    globalThetaPolarValues_snd_translate_rep g x
  with_reducible_and_instances exact h

/-- An invariant surjection to two scalars stays surjective on the fixed subspace,
by dividing the compact average by its nonzero Haar mass. -/
private theorem globalThetaPolarValues_surjective_on_trivial_isotype_aux
    {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (A : E →L[ℂ] E) (hA : IsPettisIsotypicAverageOn μ univ ρ 1 A)
    (P : E →L[ℂ] ℂ × ℂ) (hs : Surjective P) (hi : ∀ g x, P (ρ g x) = P x) :
    Surjective (fun x : actionIsotype ρ 1 ↦ P x.val) := by
  have hm : (μ.real univ : ℂ) ≠ 0 := by
    exact_mod_cast (MeasureTheory.measureReal_univ_pos (μ := μ)).ne'
  have hP (x : E) : P (A x) = (μ.real univ : ℂ) • P x := by
    apply Prod.ext
    · have h := compactActionAverage_dual_apply μ ρ 1 A hA x
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp P)
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul, hi,
        MeasureTheory.integral_const, Complex.real_smul, Prod.smul_fst, smul_eq_mul] using h
    · have h := compactActionAverage_dual_apply μ ρ 1 A hA x
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp P)
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
        PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul, hi,
        MeasureTheory.integral_const, Complex.real_smul, Prod.smul_snd, smul_eq_mul] using h
  intro y
  obtain ⟨x, hx⟩ := hs ((μ.real univ : ℂ)⁻¹ • y)
  refine ⟨⟨A x, compactActionAverage_mem_isotype μ ρ 1 A hA x⟩, ?_⟩
  change P (A x) = y
  rw [hP, hx, smul_smul, mul_inv_cancel₀ hm, one_smul]

/-- Paper: Lemma 5.5.2.1, p. 280.
On the trivial norm-one isotype the two polar values can be prescribed independently.
Deviation: This records the range needed in (6.3.2.5)–(6.3.2.6) on p. 304. -/
theorem globalThetaPolarValues_surjective_on_trivial_isotype :
    Surjective (fun x : actionIsotype ((ρ𝔽).comp (m𝔽).ker.subtype) 1 ↦
      globalThetaPolarValues (F := F) x.val) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space (m𝔽).ker := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace (m𝔽).ker := (ideleClassGroup_finiteness F).2.1
  let μ := normOneIdeleClassTamagawaMeasure F
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ := globalAdelicThetaSpace_t2_of_isClosed (F := F) adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ Θ := globalAdelicThetaSpace_polynormable (F := F)
  let : Module ℝ Θ := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ Θ := IsScalarTower.restrictScalars ℝ ℂ _
  let : LocallyConvexSpace ℝ Θ := (PolynormableSpace.withSeminorms ℂ Θ).toLocallyConvexSpace
  let A := (existsUnique_globalThetaIsotypicAverage (F := F) 1).exists.choose
  have hA := (existsUnique_globalThetaIsotypicAverage (F := F) 1).exists.choose_spec
  have hs : Surjective (globalThetaPolarValues (F := F)) := by
    intro y
    obtain ⟨f, hf⟩ := adelePolarValues_surjective (F := F) y
    exact ⟨(K𝔽).mkQL f, hf⟩
  have hi (g : (m𝔽).ker) (x : Θ) :
      globalThetaPolarValues (F := F) (ρ𝔽 g.val x) = globalThetaPolarValues (F := F) x := by
    apply Prod.ext
    · exact globalThetaPolarValues_fst_translate g.val x
    · rw [globalThetaPolarValues_snd_translate]
      have hg : m𝔽 g.val = 1 := g.property
      simp [hg]
  with_reducible_and_instances
    exact globalThetaPolarValues_surjective_on_trivial_isotype_aux μ
      ((ρ𝔽).comp (m𝔽).ker.subtype) A hA (globalThetaPolarValues (F := F)) hs (by
        simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply] using hi)

/-- The vanishing criterion on norm-one isotypes, for any action and pair of functionals with
the weights of Lemma 5.5.2.1 and the range on the trivial isotype. -/
private theorem globalThetaPolarValues_vanish_on_isotype_iff_aux {E G : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [CommGroup G] [TopologicalSpace G]
    (N : Subgroup G) (ρ : G →* (E →L[ℂ] E)) (P : E →L[ℂ] ℂ × ℂ) (n : G → ℂ)
    (hn : ∀ g ∈ N, n g = 1) (hfst : ∀ (g : G) (x : E), (P (ρ g x)).1 = (P x).1)
    (hsnd : ∀ (g : G) (x : E), (P (ρ g x)).2 = n g * (P x).2)
    (hsurj : Surjective (fun x : actionIsotype (ρ.comp N.subtype) 1 ↦ P x.val))
    (ω : PontryaginDual N) :
    (∀ x : E, (∀ g : N, ρ g.val x = (ω g : ℂ) • x) → P x = 0) ↔ ω ≠ 1 := by
  constructor
  · intro h hω
    obtain ⟨⟨x, hx⟩, hxv⟩ := hsurj (1, 0)
    have hx' := (mem_actionIsotype _ _ x).mp hx
    have h0 := h x (fun g ↦ by rw [hω]; simpa using hx' g)
    have h1 : ((1 : ℂ), (0 : ℂ)) = 0 := hxv.symm.trans h0
    simpa using congrArg Prod.fst h1
  · intro hω x hx
    obtain ⟨g0, hg0⟩ : ∃ g, ω g ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hω (ContinuousMonoidHom.ext fun g ↦ (hcon g).trans rfl)
    have hc : (ω g0 : ℂ) ≠ 1 := fun h ↦ hg0 (Circle.ext (by simpa using h))
    have h1 := hfst g0.val x
    have h2 := hsnd g0.val x
    rw [hx g0] at h1 h2
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    rw [hn g0.val g0.2, one_mul] at h2
    refine Prod.ext ?_ ?_
    · have : ((ω g0 : ℂ) - 1) * (P x).1 = 0 := by
        rw [sub_mul, h1, one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc)
    · have : ((ω g0 : ℂ) - 1) * (P x).2 = 0 := by
        rw [sub_mul, h2, one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc)

/-- Paper: Lemma 5.5.2.1, p. 280.
Both polar functionals vanish on the norm-one isotype precisely when its character
is nontrivial. The isotype is viewed inside the ordinary theta quotient. -/
theorem globalThetaPolarValues_vanish_on_isotype_iff (ω : PontryaginDual (m𝔽).ker) :
    (∀ x : Θ, (∀ g : (m𝔽).ker, ρ𝔽 g.val x = (ω g : ℂ) • x) →
      globalThetaPolarValues (F := F) x = 0) ↔ ω ≠ 1 := by
  have hn : ∀ g ∈ (m𝔽).ker, normℂ(g) = 1 := fun g hg ↦ by simp [MonoidHom.mem_ker.mp hg]
  have h1 := globalThetaPolarValues_fst_translate (F := F)
  have h2 := globalThetaPolarValues_snd_translate (F := F)
  have h3 := globalThetaPolarValues_surjective_on_trivial_isotype (F := F)
  with_reducible_and_instances
    exact globalThetaPolarValues_vanish_on_isotype_iff_aux (E := Θ) (m𝔽).ker ρ𝔽
      (globalThetaPolarValues (F := F)) (fun g ↦ normℂ(g)) hn h1 h2 h3 ω

-- TODO(paper-gap): In (5.5.2.3) each equality loses the value of the polar
-- functional on the normalized Gaussian. For ℚ(i) the first value is 1/(2π).

private theorem globalThetaPolarValues_eq_eigendistributions_scalar
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (W : Submodule ℂ (StrongDual ℂ E)) (T U : StrongDual ℂ E)
    (hW : W = Submodule.span ℂ {U}) (hT : T ∈ W) (f : E) (hf : U f = 1) (y : E) :
    T y = T f * U y := by
  rw [hW, Submodule.mem_span_singleton] at hT
  obtain ⟨a, rfl⟩ := hT
  simp [hf]

/-- Paper: Equation (5.5.2.3), p. 280.
The two polar functionals are multiples of the descended normalized generators.
Deviation: The multipliers are the values of the polar functionals on the standard
Gaussian, which need not equal one. -/
theorem globalThetaPolarValues_eq_eigendistributions (x : Θ) :
    let f := adelicStandardGaussian unitaryOne
    globalThetaPolarValues (F := F) x =
      (f zeroAdele * globalThetaEigendistribution (F := F) (1 : QuasiCharacter C𝔽) x,
        adeleSchwartzFourier f zeroAdele * globalThetaEigendistribution (F := F) normWeight x) := by
  let P := globalThetaPolarValues (F := F)
  let T₁ : D(ℬ(𝔸[F])) := (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (P.comp (K𝔽).mkQL)
  let T₂ : D(ℬ(𝔸[F])) := (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (P.comp (K𝔽).mkQL)
  have h₁ : T₁ ∈ adelicEigendistributions (1 : QuasiCharacter C𝔽) := by
    intro u f
    exact globalThetaPolarValues_fst_translate_rep u f
  have h₂ : T₂ ∈ adelicEigendistributions normWeight := by
    intro u f
    change T₂ (schwartzBruhatUnitTranslate u f) =
      ((1 : ℂ) * normℂ((QuotientGroup.mk u : C𝔽)) ^ (1 : ℂ)) * T₂ f
    rw [Complex.cpow_one, one_mul]
    exact globalThetaPolarValues_snd_translate_rep u f
  have hzero : ideleClassNormTwist (F := F) unitaryOne 0 = 1 := by
    ext g
    change (1 : ℂ) * normℂ(g) ^ (0 : ℂ) = 1
    simp
  have hn₁ : adelicNormalizedEigendistribution (F := F) (1 : QuasiCharacter C𝔽)
      (adelicStandardGaussian unitaryOne) = 1 := by
    rw [← hzero]
    exact adelicNormalizedEigendistribution_gaussian unitaryOne 0
  have hn₂ := adelicNormalizedEigendistribution_gaussian (F := F) unitaryOne 1
  obtain ⟨y, rfl⟩ := (K𝔽).mkQ_surjective x
  exact Prod.ext
    (globalThetaPolarValues_eq_eigendistributions_scalar _ T₁ _
      (adelicEigendistributions_eq_span _) h₁ _ hn₁ y)
    (globalThetaPolarValues_eq_eigendistributions_scalar _ T₂ _
      (adelicEigendistributions_eq_span _) h₂ _ hn₂ y)

/-- Paper: Remark 5.5.2.2, p. 281.
The putative orbit sum for evaluation at zero is summable exactly when the test
vanishes at zero, since each translated summand is the same value.
Deviation: The printed divergence claim requires a nonzero value at zero. -/
theorem summable_globalZeroEval_orbit_iff (f : ℬ(𝔸[F])) :
    Summable (fun a : Fˣ ↦ f (Multiplicative.ofAdd
      ((algebraMap F 𝔸[F]) ((a⁻¹ : Fˣ) : F) * 0))) ↔ f zeroAdele = 0 := by
  have : Infinite Fˣ := Infinite.of_injective
    (fun n : ℕ ↦ Units.mk0 ((n : F) + 1) (Nat.cast_add_one_ne_zero n))
    fun _ _ h ↦ Nat.cast_injective (add_right_cancel (congrArg Units.val h))
  simp only [mul_zero, summable_const_iff]

end PolarValues

section LocalGeneration

local notation "finiteModule(" v ")" =>
  (Units.map nnNormHom.toMonoidHom : (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "infiniteModule(" w ")" =>
  ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w : (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)

-- TODO(paper-gap): The proof of Proposition 5.5.3.1 identifies the weak and
-- strong dual topologies. The needed claim is equality of closures of linear subspaces.

/-- Paper: Proposition 5.5.3.1, p. 281.
At a finite place the eigendistributions span a strongly dense subspace of the dual.
The set of all eigenvectors gives the same span as the normalized generators of §3.4. -/
theorem finiteEigendistributions_dense_span (v : HeightOneSpectrum (𝓞 F)) :
    Dense (Submodule.span ℂ {T : D(ℬ(v.adicCompletion F)) |
      ∃ c : QuasiCharacter (v.adicCompletion F)ˣ, T ∈ schwartzBruhatEigendistributions c} :
      Set D(ℬ(v.adicCompletion F))) := by sorry

/-- Paper: Proposition 5.5.3.1, p. 281.
At an infinite place the eigendistributions span a strongly dense subspace of the dual.
The set of all eigenvectors gives the same span as the normalized generators of §3.4. -/
theorem infiniteEigendistributions_dense_span (w : InfinitePlace F) :
    Dense (Submodule.span ℂ {T : D(ℬ(w.Completion)) |
      ∃ c : QuasiCharacter w.Completionˣ, T ∈ schwartzBruhatEigendistributions c} :
      Set D(ℬ(w.Completion))) := by sorry

/-- Paper: Proposition 5.5.3.1, p. 281.
At a finite place the closed span of eigendistributions with prescribed norm-one
restriction is the corresponding homogeneous subspace of the strong dual.
Only the restriction of the unitary character to the local norm-one units matters. -/
theorem finiteEigendistributions_component_closedSpan (v : HeightOneSpectrum (𝓞 F))
    (ω : PontryaginDual (v.adicCompletion F)ˣ) :
    closure (Submodule.span ℂ {T : D(ℬ(v.adicCompletion F)) |
      ∃ c : QuasiCharacter (v.adicCompletion F)ˣ,
        (∀ u : (finiteModule(v)).ker, c u.val = (ω u.val : ℂ)) ∧
          T ∈ schwartzBruhatEigendistributions c} : Set D(ℬ(v.adicCompletion F))) =
      {T | ∀ (u : (finiteModule(v)).ker) (f : ℬ(v.adicCompletion F)),
        T (schwartzBruhatUnitTranslate u.val f) = (ω u.val : ℂ) * T f} := by sorry

/-- Paper: Proposition 5.5.3.1, p. 281.
At an infinite place the closed span of eigendistributions with prescribed norm-one
restriction is the corresponding homogeneous subspace of the strong dual.
Only the restriction of the unitary character to the local norm-one units matters. -/
theorem infiniteEigendistributions_component_closedSpan (w : InfinitePlace F)
    (ω : PontryaginDual w.Completionˣ) :
    closure (Submodule.span ℂ {T : D(ℬ(w.Completion)) |
      ∃ c : QuasiCharacter w.Completionˣ,
        (∀ u : (infiniteModule(w)).ker, c u.val = (ω u.val : ℂ)) ∧
          T ∈ schwartzBruhatEigendistributions c} : Set D(ℬ(w.Completion))) =
      {T | ∀ (u : (infiniteModule(w)).ker) (f : ℬ(w.Completion)),
        T (schwartzBruhatUnitTranslate u.val f) = (ω u.val : ℂ) * T f} := by sorry

end LocalGeneration

section StructureTheorem

-- TODO(paper-gap): In the proof of Theorem 5.5.3.2 on pp. 283–284,
-- vectors in a spectral interval need not be eigenvectors at a point of that interval.
-- On L²(ℝ, dx), multiplication by x ↦ exp(itx) has no nonzero common eigenvectors.

/-- Pullback along a quotient map of topological vector spaces is injective on continuous
linear functionals, because the quotient map is surjective. -/
private theorem sLocalHomogeneousThetaTranspose_injective_aux {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (K : Submodule ℂ E) :
    Injective (pull(K)) :=
  fun U V h ↦ globalThetaPolarValues_unique_aux K U V fun f ↦ DFunLike.congr_fun h f

/-- Paper: Theorem 5.5.3.2(1), p. 282.
Pullback along the homogeneous S-local theta quotient is injective on strong duals. -/
theorem sLocalHomogeneousThetaTranspose_injective (ω : PontryaginDual (mₛ).ker) :
    Injective (pull(Kₛω(ω))) := by
  exact sLocalHomogeneousThetaTranspose_injective_aux _

/-- Pullback values along a quotient map are related by `c` when the representatives are
related by `c` modulo the kernel. -/
private theorem pull_eq_smul_of_sub_mem {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (K : Submodule ℂ E) (T : StrongDual ℂ (E ⧸ K)) (c : ℂ) {a b : E}
    (h : a - c • b ∈ K) :
    pull(K) T a = c * pull(K) T b := by
  have hq : (Submodule.Quotient.mk a : E ⧸ K) = Submodule.Quotient.mk (c • b) :=
    (Submodule.Quotient.eq K).mpr h
  change T (Submodule.Quotient.mk a) = c * T (Submodule.Quotient.mk b)
  rw [hq, Submodule.Quotient.mk_smul, map_smul, smul_eq_mul]

/-- Pullback along the quotient by the kernel of a linear map `θ` multiplies by `c` when
`θ` does. -/
private theorem pull_ker_eq_smul_of_map_eq {E G : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] (θ : E →ₗ[ℂ] G)
    (T : StrongDual ℂ (E ⧸ LinearMap.ker θ)) (c : ℂ) {a b : E} (h : θ a = c • θ b) :
    pull(LinearMap.ker θ) T a = c * pull(LinearMap.ker θ) T b :=
  pull_eq_smul_of_sub_mem _ T c (LinearMap.sub_mem_ker_iff.mpr (h.trans (map_smul θ c b).symm))

/-- Pullback along the quotient by the kernel of a linear map `θ` takes equal values on
representatives with equal images under `θ`. -/
private theorem pull_ker_eq_of_map_eq {E G : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] (θ : E →ₗ[ℂ] G)
    (T : StrongDual ℂ (E ⧸ LinearMap.ker θ)) {a b : E} (h : θ a = θ b) :
    pull(LinearMap.ker θ) T a = pull(LinearMap.ker θ) T b :=
  (pull_ker_eq_smul_of_map_eq θ T 1 (h.trans (one_smul ℂ (θ b)).symm)).trans (one_mul _)

/-- S-local theta of a unit translate is theta at the inversely translated S-idele. -/
private theorem sLocalTheta_unitTranslate_apply (g x : Aₛˣ) (f : ℬ(Aₛ)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g f) x =
      sLocalAdelicTheta F S f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (d t).val x.val)

/-- The S-local theta function on classes of a unit translate is the theta function on
classes at the inversely translated class. -/
private theorem sLocalThetaOnClasses_unitTranslate_apply (u : Aₛˣ) (f : ℬ(Aₛ)) (x : Jₛ) :
    sLocalAdelicThetaOnClasses F S (schwartzBruhatUnitTranslate u f) x =
      sLocalAdelicThetaOnClasses F S f ((QuotientGroup.mk u)⁻¹ * x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 := sLocalAdelicThetaOnClasses_mk F S (schwartzBruhatUnitTranslate u f) x
  have h2 := sLocalAdelicThetaOnClasses_mk F S f (u⁻¹ * x)
  have h3 := sLocalTheta_unitTranslate_apply u x f
  have h4 : (QuotientGroup.mk (u⁻¹ * x) : Jₛ) = (QuotientGroup.mk u)⁻¹ * QuotientGroup.mk x := rfl
  with_reducible_and_instances
    exact (h1.trans (h3.trans h2.symm)).trans (congrArg (sLocalAdelicThetaOnClasses F S f) h4)

/-- The homogeneous S-local theta transform multiplies by `ω g` under a unit translate
representing `g`. -/
private theorem sLocalHomogeneousTheta_unitTranslate (ω : PontryaginDual (mₛ).ker)
    (g : (mₛ).ker) (u : Aₛˣ) (hu : QuotientGroup.mk u = g.val) (f : ℬ(Aₛ)) :
    sLocalHomogeneousAdelicThetaLinearMap F S ω (schwartzBruhatUnitTranslate u f) =
      (ω g : ℂ) • sLocalHomogeneousAdelicThetaLinearMap F S ω f := by
  have := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  refine ContinuousMap.ext fun x ↦ ?_
  refine (sLocalHomogeneousAdelicThetaLinearMap_apply ω _ x).trans (Eq.trans ?_
    ((sLocalHomogeneousAdelicTheta_homogeneous F S _ ω f g x).trans
      ((ContinuousMap.smul_apply (ω g : ℂ) (sLocalHomogeneousAdelicThetaLinearMap F S ω f) x).trans
        (smul_eq_mul _ _)).symm))
  refine Eq.trans ?_ (sLocalHomogeneousAdelicThetaLinearMap_apply ω f _).symm
  refine congrArg (MeasureTheory.integral _) (funext fun h ↦ ?_)
  refine congrArg (· * (ω h : ℂ)) ((sLocalThetaOnClasses_unitTranslate_apply u f _).trans ?_)
  rw [hu, mul_assoc]

/-- Paper: Theorem 5.5.3.2(1), p. 282.
Distributions pulled back from the homogeneous S-local theta quotient have weight
`ω` on the norm-one classes.
Deviation: The weight uses the transpose convention of (5.5.1.1) and the
homogeneous theta transform of §5.2. The proof on p. 284 also uses a contragredient. -/
theorem sLocalHomogeneousThetaTranspose_homogeneous (ω : PontryaginDual (mₛ).ker)
    (T : D(SLocalHomogeneousThetaSpace F S ω)) (g : (mₛ).ker) (u : Aₛˣ)
    (hu : QuotientGroup.mk u = g.val) (f : ℬ(Aₛ)) :
    pull(Kₛω(ω)) T (schwartzBruhatUnitTranslate u f) =
      (ω g : ℂ) * pull(Kₛω(ω)) T f := by
  have h := sLocalHomogeneousTheta_unitTranslate ω g u hu f
  with_reducible_and_instances
    exact pull_ker_eq_smul_of_map_eq (E := ℬ(Aₛ)) (sLocalHomogeneousAdelicThetaLinearMap F S ω)
      T (ω g : ℂ) h

/-- Paper: Theorem 5.5.3.2(1), p. 282.
The strong closure of the homogeneous S-local theta transpose range is the closed
span of the normalized eigendistributions whose weights restrict to the given character.
The generators are expressed by their pullbacks to the test space. -/
theorem sLocalHomogeneousThetaTranspose_closure_range (ω : PontryaginDual (mₛ).ker) :
    closure (Set.range (pull(Kₛω(ω)))) =
      closure (Submodule.span ℂ
        (sLocalNormalizedEigendistribution '' {c : QuasiCharacter Jₛ | restricts(c, mₛ, ω)}) :
          Set D(ℬ(Aₛ))) := by sorry

/-- Paper: Theorem 5.5.3.2(2), p. 282.
Pullback along the ordinary S-local theta quotient is injective on strong duals. -/
theorem sLocalThetaTranspose_injective :
    Injective (pull(Kₛ)) := by
  exact sLocalHomogeneousThetaTranspose_injective_aux _

/-- Paper: Theorem 5.5.3.2(2), p. 282.
Distributions pulled back from the S-local theta quotient are invariant under the
projected diagonal S-units, the kernel of the map to S-idele classes. -/
theorem sLocalThetaTranspose_invariant (T : D(SLocalAdelicThetaSpace F S)) (u : Aₛˣ)
    (hu : (QuotientGroup.mk u : Jₛ) = 1) (f : ℬ(Aₛ)) :
    pull(Kₛ) T (schwartzBruhatUnitTranslate u f) = pull(Kₛ) T f := by
  have h : sLocalAdelicTheta F S (schwartzBruhatUnitTranslate u f) = sLocalAdelicTheta F S f := by
    refine ContinuousMap.ext fun x ↦ (sLocalTheta_unitTranslate_apply u x f).trans ?_
    refine sLocalAdelicTheta_factorsThrough F S f ?_
    change (QuotientGroup.mk' _ (u⁻¹ * x) : Jₛ) = QuotientGroup.mk' _ x
    rw [map_mul, map_inv]
    change (QuotientGroup.mk u : Jₛ)⁻¹ * _ = _
    rw [hu, inv_one, one_mul]
  with_reducible_and_instances
    exact pull_ker_eq_of_map_eq (E := ℬ(Aₛ)) (sLocalAdelicTheta F S) T h

/-- Paper: Theorem 5.5.3.2(2), p. 282.
The strong closure of the ordinary S-local theta transpose range is the closed span
of all normalized S-local eigendistributions pulled back from the theta quotient. -/
theorem sLocalThetaTranspose_closure_range :
    closure (Set.range (pull(Kₛ))) =
      closure (Submodule.span ℂ (Set.range (sLocalNormalizedEigendistribution (F := F) (S := S))) :
        Set D(ℬ(Aₛ))) := by
  have denseImage {X Y I : Type _} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
      [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (L : X →L[ℂ] Y)
      (D : I → X) (G : I → Y) (hd : Dense (Submodule.span ℂ (range D) : Set X))
      (hG : ∀ i, L (D i) = G i) :
      closure (range L) = closure (Submodule.span ℂ (range G) : Set Y) := by
    have hs : L.toLinearMap '' range D = range G :=
      (Set.range_comp L.toLinearMap D).symm.trans (congrArg Set.range (funext hG))
    have hi := congrArg (fun p : Submodule ℂ Y ↦ (p : Set Y))
      ((Submodule.map_span L.toLinearMap (range D)).trans (congrArg (Submodule.span ℂ) hs))
    change L '' (Submodule.span ℂ (range D) : Set X) = _ at hi
    rw [← hi]
    exact le_antisymm (closure_minimal (L.continuous.range_subset_closure_image_dense hd) isClosed_closure)
      (closure_mono (Set.image_subset_range _ _))
  have pullEq {M : Type _} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
      (K : Submodule ℂ M) (U : StrongDual ℂ (M ⧸ K)) (T : StrongDual ℂ M)
      (h : ∀ f, U (K.mkQL f) = T f) : pull(K) U = T :=
    ContinuousLinearMap.ext h
  with_reducible_and_instances
    exact denseImage (X := D(SLocalAdelicThetaSpace F S)) (Y := D(ℬ(Aₛ))) (I := QuasiCharacter Jₛ)
      (pull(Kₛ)) (sLocalThetaEigendistribution (F := F) (S := S))
      (sLocalNormalizedEigendistribution (F := F) (S := S)) (sLocalThetaEigendistributions_dense_span (F := F) (S := S))
      (fun c ↦ pullEq (M := ℬ(Aₛ)) (Kₛ) _ _ (sLocalThetaEigendistribution_mk (F := F) (S := S) c))

-- TODO(paper-gap): Remark 5.5.3.3, p. 285, claims that one connected subset of weights
-- with an interval in it detects the whole theta space. A subset of a single component
-- cannot see the other norm-one isotypes.

/-- Paper: Remark 5.5.3.3, p. 285.
The S-local eigendistributions over all weights separate points of the S-local theta space.
Deviation: Weights range over all components of the character space. -/
theorem sLocalThetaEigendistributions_separate (x : SLocalAdelicThetaSpace F S)
    (hx : ∀ c : QuasiCharacter Jₛ, sLocalThetaEigendistribution c x = 0) : x = 0 := by
  have detect {E I : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [SeparatingDual ℂ E]
      (D : I → StrongDual ℂ E) (hd : Dense (Submodule.span ℂ (range D) : Set (StrongDual ℂ E)))
      (y : E) (hy : ∀ i, D i y = 0) : y = 0 := by
    let ev : StrongDual ℂ E →L[ℂ] ℂ :=
      { toFun := fun T ↦ T y
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl
        cont := continuous_eval_const y }
    have hs : Submodule.span ℂ (range D) ≤ ev.ker :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy i)
    exact SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
      (fun T ↦ closure_minimal hs ev.isClosed_ker (hd T))
  let : T2Space (SLocalAdelicThetaSpace F S) := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ (SLocalAdelicThetaSpace F S) :=
    sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let : IsTopologicalAddGroup (SLocalAdelicThetaSpace F S) := PolynormableSpace.isTopologicalAddGroup ℂ _
  let : SeparatingDual ℂ (SLocalAdelicThetaSpace F S) := polynormableSpace_separatingDual ℂ _
  with_reducible_and_instances
    exact detect (E := SLocalAdelicThetaSpace F S) (I := QuasiCharacter Jₛ)
      (sLocalThetaEigendistribution (F := F) (S := S))
      (sLocalThetaEigendistributions_dense_span (F := F) (S := S)) x hx

/-- Removing the real power prescribed by the abscissa leaves a unitary character. -/
private theorem exists_unitary_normTwist_eq {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (m : G →* ℝ≥0ˣ)
    (hp : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    ∃ (χ : PontryaginDual G) (s : ℂ),
      c = quasiCharacterNormTwist m hp.continuous ((circleToComplex).comp χ) s := by
  let a := quasiCharacterAbscissa m hp hne c
  let d := quasiCharacterNormTwist m hp.continuous c (-(a : ℂ))
  have hrad (g : G) : (((m g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa m hp hne]
  have hd (g : G) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : G) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual G :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change c g = d g * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ)
  rw [hd, hrad, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hn g))]

/-- Every S-local quasi-character lies on the norm-twist chart of a unitary character. -/
private theorem exists_sLocal_chart_eq (c : QuasiCharacter Jₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), c = chartₛ(χ) s := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hne : ∃ g, mₛ g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  exact exists_unitary_normTwist_eq mₛ (isProperMap_sIdeleQuotientNorm F S) hne c

/-- Evaluating a holomorphic family of continuous functionals at a point gives an entire
function. -/
private theorem differentiable_strongDual_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℂ M]
    {G : ℂ → StrongDual ℂ M} (hG : VectorHolomorphicOn G univ) (x : M) :
    Differentiable ℂ (fun z : ℂ ↦ G z x) := by
  let ev : StrongDual ℂ M →L[ℂ] ℂ :=
    ⟨⟨⟨fun T ↦ T x, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩, continuous_eval_const x⟩
  intro z
  have h := hG.hasFDerivAt (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 z)
  have hj : HasFDerivAt (ev ∘ G) (ev.comp (fderiv ℂ G z)) z := by
    apply HasFDerivAt.of_isLittleOTVS
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using ev.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS
  exact hj.differentiableAt

/-- An entire function vanishing on a set with an accumulation point vanishes identically. -/
private theorem eq_zero_of_accumulation_of_differentiable {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    {A : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ closure (A \ {z₀})) (hA : ∀ w ∈ A, φ w = 0) (s : ℂ) :
    φ s = 0 := by
  have hfreq : ∃ᶠ w in 𝓝[≠] z₀, φ w = 0 := by
    rw [frequently_nhdsWithin_iff]
    exact (mem_closure_iff_frequently.mp hz₀).mono fun w hw ↦ ⟨hA w hw.1, hw.2⟩
  exact (AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun z _ ↦ hφ.analyticAt z) isPreconnected_univ (mem_univ z₀) hfreq) (mem_univ s)

/-- Paper: Remark 5.5.3.3, p. 285.
The eigendistributions with weights in a set that has an accumulation point in every
norm chart separate points of ordinary theta space.
Deviation: The identity theorem applies on each connected component separately. -/
theorem sLocalThetaEigendistributions_separate_of_accumulation
    (W : Set (QuasiCharacter Jₛ))
    (hW : ∀ χ : PontryaginDual Jₛ, ∃ z : ℂ,
      z ∈ closure ((chartₛ(χ) ⁻¹' W) \ {z}))
    (x : SLocalAdelicThetaSpace F S)
    (hx : ∀ c ∈ W, sLocalThetaEigendistribution c x = 0) : x = 0 := by
  refine sLocalThetaEigendistributions_separate x fun c ↦ ?_
  refine (exists_sLocal_chart_eq (F := F) (S := S) c).elim fun χ hs ↦ hs.elim fun s hc ↦ ?_
  rw [hc]
  -- The values along a chart form an entire function whose zeros accumulate.
  have hφ := differentiable_strongDual_apply
    (sLocalThetaEigendistribution_holomorphic (F := F) (S := S) χ) x
  have hA : ∀ w ∈ chartₛ(χ) ⁻¹' W,
      sLocalThetaEigendistribution (F := F) (S := S) (chartₛ(χ) w) x = 0 :=
    fun w hw ↦ hx (chartₛ(χ) w) (Set.mem_preimage.mp hw)
  exact (hW χ).elim fun z₀ hz₀ ↦ eq_zero_of_accumulation_of_differentiable
    (φ := fun z : ℂ ↦ sLocalThetaEigendistribution (F := F) (S := S) (chartₛ(χ) z) x)
    (A := chartₛ(χ) ⁻¹' W) hφ hz₀ hA s

/-- A split quotient has an embedded strong transpose; composing with an already
embedded transpose preserves this property. -/
private theorem globalHomogeneousThetaTranspose_isEmbedding_split
    {E X Y : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (q : E →L[ℂ] X) (r : E →L[ℂ] Y) (S : Submodule ℂ X)
    (e : Y ≃L[ℂ] S) (P : X →L[ℂ] X) (c : ℂ) (hc : c ≠ 0)
    (hmem : ∀ x, P x ∈ S) (hfix : ∀ x : S, P x.val = c • x.val)
    (he : ∀ f, (e (r f) : X) = P (q f))
    (hq : IsEmbedding (fun l : StrongDual ℂ X ↦ l.comp q)) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) ℂ r) := by
  let Q : X →L[ℂ] Y := e.symm.toContinuousLinearMap.comp (P.codRestrict S hmem)
  let J : Y →L[ℂ] X := c⁻¹ • (S.subtypeL.comp e.toContinuousLinearMap)
  have hQJ (y : Y) : Q (J y) = y := by
    apply e.injective
    apply Subtype.ext
    change (e (e.symm _)).val = (e y).val
    rw [e.apply_symm_apply]
    change P (c⁻¹ • (e y).val) = (e y).val
    rw [map_smul, hfix, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hQr (f : E) : Q (q f) = r f := by
    apply e.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (e.apply_symm_apply _)).trans (he f).symm
  let A : StrongDual ℂ Y →L[ℂ] StrongDual ℂ X := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) ℂ Q
  let B : StrongDual ℂ X →L[ℂ] StrongDual ℂ Y := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) ℂ J
  have hBA : (B : _ → _) ∘ A = id := by
    funext l
    ext y
    exact congrArg l (hQJ y)
  have hA : IsEmbedding A := IsEmbedding.of_comp A.continuous B.continuous
    (hBA ▸ IsEmbedding.id)
  have hr : (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) ℂ r : _ → _) =
      (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) ℂ q : _ → _) ∘ A := by
    funext l
    ext f
    exact congrArg l (hQr f).symm
  rw [hr]
  exact hq.comp hA

/-- Paper: Theorem 5.5.3.4(1), p. 285.
Pullback from the homogeneous global theta quotient is a topological embedding
for the strong dual topologies. -/
theorem globalHomogeneousThetaTranspose_isEmbedding (ω : PontryaginDual (m𝔽).ker) :
    IsEmbedding (pull(K𝔽ω(ω))) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space (m𝔽).ker := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace (m𝔽).ker := (ideleClassGroup_finiteness F).2.1
  let μ := normOneIdeleClassTamagawaMeasure F
  let : μ.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let X := GlobalAdelicThetaSpace F
  let : T2Space X := globalAdelicThetaSpace_t2_of_isClosed (F := F) adelicTheta_ker_isClosed
  let : PolynormableSpace ℂ X := globalAdelicThetaSpace_polynormable (F := F)
  let : Module ℝ X := Module.restrictScalars ℝ ℂ _
  let : IsScalarTower ℝ ℂ X := IsScalarTower.restrictScalars ℝ ℂ _
  let : LocallyConvexSpace ℝ X := (PolynormableSpace.withSeminorms ℂ X).toLocallyConvexSpace
  let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
  let A := (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose
  have hA := (existsUnique_globalThetaIsotypicAverage (F := F) ω).exists.choose_spec
  obtain ⟨e, he⟩ := (globalThetaIsotypicAverage_equiv (F := F) ω).2
  have hm : (μ.real univ : ℂ) ≠ 0 := by
    exact_mod_cast (MeasureTheory.measureReal_univ_pos (μ := μ)).ne'
  with_reducible_and_instances
    exact globalHomogeneousThetaTranspose_isEmbedding_split
      (K𝔽).mkQL (K𝔽ω(ω)).mkQL (actionIsotype (ρ.comp (m𝔽).ker.subtype) ω)
      e A (μ.real univ) hm
      (compactActionAverage_mem_isotype μ (ρ.comp (m𝔽).ker.subtype) ω A hA)
      (fun x ↦ compactActionAverage_apply_isotype μ (ρ.comp (m𝔽).ker.subtype) ω A hA x.property)
      (by simpa only [Submodule.mkQL_apply] using he)
      (globalThetaQuotient_transpose_isEmbedding (F := F))

/-- Global theta of a unit translate is theta at the inversely translated idele class. -/
private theorem globalTheta_unitTranslate_apply (g : IdeleGroup (𝓞 F) F) (f : ℬ(𝔸[F]))
    (a : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate g f) a = adelicTheta f ((QuotientGroup.mk g)⁻¹ * a) := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  change _ = adelicTheta f (QuotientGroup.mk (g⁻¹ * x))
  rw [adelicTheta_mk (schwartzBruhatUnitTranslate g f) x, adelicTheta_mk f (g⁻¹ * x)]
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (algebraMap F 𝔸[F] (t : F)) x.val)

/-- The homogeneous global theta transform multiplies by `ω g` under a unit translate
representing `g`. -/
private theorem homogeneousTheta_unitTranslate (ω : PontryaginDual (m𝔽).ker) (g : (m𝔽).ker)
    (u : IdeleGroup (𝓞 F) F) (hu : QuotientGroup.mk u = g.val) (f : ℬ(𝔸[F])) :
    homogeneousAdelicThetaLinearMap F ω (schwartzBruhatUnitTranslate u f) =
      (ω g : ℂ) • homogeneousAdelicThetaLinearMap F ω f := by
  refine ContinuousMap.ext fun x ↦ ?_
  refine Eq.trans ?_ ((homogeneousAdelicTheta_homogeneous ω f g x).trans
    ((ContinuousMap.smul_apply (ω g : ℂ) (homogeneousAdelicThetaLinearMap F ω f) x).trans
      (smul_eq_mul _ _)).symm)
  change homogeneousAdelicTheta ω (schwartzBruhatUnitTranslate u f) x =
    homogeneousAdelicTheta ω f (g.val⁻¹ * x)
  refine congrArg (MeasureTheory.integral _) (funext fun h ↦ ?_)
  refine congrArg (· * (ω h : ℂ)) ((globalTheta_unitTranslate_apply u f _).trans ?_)
  rw [hu, mul_left_comm]

/-- Paper: Theorem 5.5.3.4(1), p. 285.
The global homogeneous theta transpose takes values in the distributions that
transform by the specified character on the norm-one classes. -/
theorem globalHomogeneousThetaTranspose_homogeneous (ω : PontryaginDual (m𝔽).ker)
    (T : D(GlobalHomogeneousThetaSpace F ω)) (g : (m𝔽).ker)
    (u : IdeleGroup (𝓞 F) F) (hu : QuotientGroup.mk u = g.val) (f : ℬ(𝔸[F])) :
    pull(K𝔽ω(ω)) T (schwartzBruhatUnitTranslate u f) =
      (ω g : ℂ) * pull(K𝔽ω(ω)) T f := by
  have h := homogeneousTheta_unitTranslate ω g u hu f
  with_reducible_and_instances
    exact pull_ker_eq_smul_of_map_eq (E := ℬ(𝔸[F])) (homogeneousAdelicThetaLinearMap F ω)
      T (ω g : ℂ) h

/-- Paper: Theorem 5.5.3.4(1), p. 285.
The range of the global homogeneous theta transpose is strongly generated by
the normalized eigendistributions whose weights restrict to the given character.
The generators are expressed by their pullbacks to the test space. -/
theorem globalHomogeneousThetaTranspose_range (ω : PontryaginDual (m𝔽).ker) :
    Set.range (pull(K𝔽ω(ω))) =
      closure (Submodule.span ℂ
        (adelicNormalizedEigendistribution (F := F) '' {c : QuasiCharacter C𝔽 | restricts(c, m𝔽, ω)}) :
          Set D(ℬ(𝔸[F]))) := by sorry

-- The global embedding in Theorem 5.5.3.4(2) is already stated as
-- `globalThetaQuotient_transpose_isEmbedding` in §5.2.

/-- Global theta is invariant under translation by a principal-class unit. -/
private theorem globalTheta_unitTranslate_of_mk_eq_one (u : IdeleGroup (𝓞 F) F)
    (hu : (QuotientGroup.mk u : C𝔽) = 1) (f : ℬ(𝔸[F])) :
    adelicThetaLinearMap F (schwartzBruhatUnitTranslate u f) = adelicThetaLinearMap F f := by
  refine ContinuousMap.ext fun a ↦ ?_
  change adelicTheta (schwartzBruhatUnitTranslate u f) a = adelicTheta f a
  refine (globalTheta_unitTranslate_apply u f a).trans ?_
  have ha : (QuotientGroup.mk u : C𝔽)⁻¹ * a = a := by rw [hu, inv_one, one_mul]
  exact congrArg (adelicTheta f) ha

/-- Paper: Theorem 5.5.3.4(2), p. 285.
Distributions pulled back from the ordinary global theta quotient are invariant under
principal ideles, the kernel of the map to idele classes. -/
theorem globalThetaTranspose_invariant (T : D(GlobalAdelicThetaSpace F))
    (u : IdeleGroup (𝓞 F) F) (hu : (QuotientGroup.mk u : C𝔽) = 1) (f : ℬ(𝔸[F])) :
    pull(K𝔽) T (schwartzBruhatUnitTranslate u f) = pull(K𝔽) T f := by
  have h := globalTheta_unitTranslate_of_mk_eq_one u hu f
  with_reducible_and_instances
    exact pull_ker_eq_of_map_eq (E := ℬ(𝔸[F])) (adelicThetaLinearMap F) T h

/-- Paper: Theorem 5.5.3.4(2), p. 285.
The range of the ordinary global theta transpose is the strongly closed span of
all normalized adelic eigendistributions pulled back from the theta quotient. -/
theorem globalThetaTranspose_range :
    Set.range (pull(K𝔽)) =
      closure (Submodule.span ℂ (Set.range (adelicNormalizedEigendistribution (F := F))) :
        Set D(ℬ(𝔸[F]))) := by sorry

end StructureTheorem

end RiemannMasullo
