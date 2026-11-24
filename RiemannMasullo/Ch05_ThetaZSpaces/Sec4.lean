module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Extend
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1

/-! # Second Structure Theorem and the S-local Čech sequence

Masullo, §5.4, pp. 265–277. The set S in Lean lists the finite places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped MeasureTheory NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "normℝ(" t ")" => (((t : ℝ≥0ˣ).val : ℝ))
local notation "normChart(" χ ")" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ))
local notation "restrict₁(" χ ")" => ((χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ))
local notation "Θω(" ω ")" => SLocalHomogeneousThetaSpace F S (ω)
local notation "φω(" ω ")" => sLocalHomogeneousAdelicThetaLinearMap F S (ω)
local notation "Fourierₛ" => sAdeleSchwartzFourier (F := F) (S := S)
local notation "Zₛ" => sLocalIdelicZFunction (F := F) (S := S)
local notation "ρₛ(" χ ", " s ")" => sLocalRhoFactor (F := F) (S := S) (normChart(χ) (s))

local notation "rightInterval" => Ioi (0 : ℝ)
local notation "leftInterval" => Iio (1 : ℝ)
local notation "overlapInterval" => Ioo (0 : ℝ) 1
local notation "rightHalf" => Complex.re ⁻¹' rightInterval
local notation "leftHalf" => Complex.re ⁻¹' leftInterval
local notation "overlap" => Complex.re ⁻¹' overlapInterval
local notation "B⁺" => SchwartzBergman rightInterval
local notation "B⁻" => SchwartzBergman leftInterval
local notation "B⁰" => SchwartzBergman overlapInterval

section SecondStructure

-- The injectivity assertion in (5.4.1.1) is `sLocalThetaMellin_injective` from §5.1.

/-- Paper: (5.4.1.1), p. 265.
The Mellin map on the S-local theta quotient is continuous for compact convergence
on the regular locus of the meromorphic target. -/
theorem continuous_sLocalThetaMellin :
    Continuous (sLocalThetaMellin (F := F) (S := S)) := by
  exact (LinearMap.ker (sLocalAdelicTheta F S)).isQuotientMap_mkQ.continuous_iff.mpr
    (sLocalIdelicMellin_continuous (F := F) (S := S))

/-- Paper: Theorem 5.4.1.1(1), p. 265.
Every norm-one character has a unique unitary lift trivial on the chosen norm section.
Its norm twists give the coordinates used for the Second Structure Theorem. -/
theorem existsUnique_sLocalNormSectionCharacter (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (_hτ : RightInverse τ mₛ) (ω : PontryaginDual J₁) :
    ∃! χ : PontryaginDual Jₛ, restrict₁(χ) = ω ∧ ∀ t, χ (τ t) = 1 := by
  have hk (g : Jₛ) : g / τ (mₛ g) ∈ (mₛ).ker := by
    simp [MonoidHom.mem_ker, _hτ (mₛ g)]
  let p : Jₛ →ₜ* J₁ :=
    { toFun := fun g ↦ ⟨g / τ (mₛ g), hk g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by simp [mul_div_mul_comm])
      continuous_toFun := (continuous_id.div' (τ.continuous.comp hmₛ)).subtype_mk hk }
  have hp (u : J₁) : p u = u := by
    apply Subtype.ext
    change u.val / τ (mₛ u.val) = u.val
    rw [u.property, map_one, div_one]
  have hτp (t : ℝ≥0ˣ) : p (τ t) = 1 := by
    apply Subtype.ext
    change τ t / τ (mₛ (τ t)) = 1
    simp [_hτ t]
  refine ⟨ω.comp p, ⟨?_, ?_⟩, ?_⟩
  · ext1 u
    exact congrArg ω (hp u)
  · intro t
    change ω (p (τ t)) = 1
    rw [hτp, map_one]
  · rintro χ ⟨hker, hsec⟩
    ext1 g
    change χ g = ω (p g)
    have he := DFunLike.congr_fun hker (p g)
    change χ (g / τ (mₛ g)) = ω (p g) at he
    simpa only [map_div, hsec, div_one] using he

/-- On a closed positive strip, rapid decay controls the tails and continuity controls
the remaining compact rectangle. -/
private theorem existsUnique_sLocalZetaPair_right (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    ∃ u : B⁺, EqOn u.val (fun z ↦ Zₛ f (normChart(χ) z)) rightHalf := by
  let G := fun z ↦ Zₛ f (normChart(χ) z)
  have hG : DifferentiableOn ℂ G rightHalf :=
    (sLocalIdelicZetaIntegral_analyticOn f χ).differentiableOn.congr fun z hz ↦
      sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩
  refine ⟨⟨(rightHalf).indicator G, fun z hz ↦ indicator_of_notMem hz _,
    hG.congr (fun z hz ↦ indicator_of_mem hz _), ?_⟩, fun z hz ↦ indicator_of_mem hz _⟩
  intro a b hab hsub N
  have ha : 0 < a := hsub (left_mem_Icc.mpr hab)
  have hstrip : UniformlySchwartzOnStrip G (a / 2) (b + a) := by
    simpa only [iteratedDeriv_zero] using
      sLocalIdelicZFunction_schwartzOnStrip f χ (a / 2) (b + a) (by linarith) (by linarith) 0
  obtain ⟨C, hC, htail⟩ := hstrip.2.2 (a / 2) (by linarith) (by linarith) (N+1) (by omega)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp htail)
  let M := max T (max 1 b)
  let K := Complex.reProdIm (Icc a b) (Icc (-M) M)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun z : ℂ ↦ ‖z ^ N * G z‖) K :=
    ((continuous_id.pow N).continuousOn.mul (hG.continuousOn.mono (show K ⊆ rightHalf from fun _ hz ↦ hsub hz.1))).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc
  refine ⟨max B (2 ^ N * C), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖z ^ N * (rightHalf).indicator G z‖ ≤ _
  rw [indicator_of_mem (show z ∈ rightHalf from hsub hz)]
  by_cases hy : |z.im| ≤ M
  · exact (hB ⟨z, ⟨hz, abs_le.mp hy⟩, rfl⟩).trans (le_max_left _ _)
  have hy' := (lt_of_not_ge hy).le
  have hy1 : 1 ≤ |z.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hy')
  have hy0 : 0 < |z.im| := zero_lt_one.trans_le hy1
  have hz' : z.re ∈ Icc a b := hz
  have hdec := hT |z.im| ((le_max_left _ _).trans hy') z.im rfl z.re
    (show z.re ∈ Icc (a / 2 + a / 2) (b + a - a / 2) from ⟨by linarith [hz'.1], by linarith [hz'.2]⟩)
  simp only [Complex.re_add_im] at hdec
  have hnorm : ‖z‖ ≤ 2 * |z.im| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    rw [abs_of_nonneg (ha.le.trans hz'.1)]
    linarith [hz'.2.trans ((le_max_right 1 b).trans ((le_max_right T _).trans hy'))]
  have hpow : |z.im| ^ N ≤ |z.im| ^ (N + 1) := pow_le_pow_right₀ hy1 (by omega)
  apply le_trans _ (le_max_right _ _)
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 * |z.im|) ^ N * (C / |z.im| ^ N) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (hdec.trans
        (div_le_div_of_nonneg_left hC.le (pow_pos hy0 _) hpow)) (norm_nonneg _) (by positivity)
    _ = 2 ^ N * C := by rw [mul_pow]; field_simp

/-- Reflecting a closed substrip preserves rapid decay since the polynomial weights at
`z` and `1 - z` bound each other up to a constant and a weight of degree zero. -/
private theorem existsUnique_sLocalZetaPair_reflect_mem {I J : Set ℝ}
    (hIJ : ∀ x : ℝ, 1 - x ∈ I ↔ x ∈ J) (u : SchwartzBergman I) :
    (fun z ↦ u.val (1 - z)) ∈ schwartzBergmanSubmodule J := by
  have href (z : ℂ) : 1 - z ∈ Complex.re ⁻¹' I ↔ z ∈ Complex.re ⁻¹' J := by
    simpa only [mem_preimage, Complex.sub_re, Complex.one_re] using hIJ z.re
  refine ⟨fun z hz ↦ u.property.1 (mt (href z).mp hz),
    u.property.2.1.comp (by fun_prop) (fun z hz ↦ (href z).mpr hz), ?_⟩
  intro a b hab hsub N
  have hi : Icc (1-b) (1-a) ⊆ I := by
    intro x hx
    have h : 1 - x ∈ J := hsub ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa only [sub_sub_cancel] using (hIJ (1-x)).mpr h
  obtain ⟨A, hA⟩ := u.property.2.2 (1-b) (1-a) (by linarith) hi 0
  obtain ⟨B, hB⟩ := u.property.2.2 (1-b) (1-a) (by linarith) hi N
  refine ⟨2 ^ N * max A B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  let w := 1 - z
  have hw : w ∈ Complex.re ⁻¹' Icc (1-b) (1-a) := by
    change 1-b ≤ (1-z).re ∧ (1-z).re ≤ 1-a
    simp only [Complex.sub_re, Complex.one_re]
    exact ⟨sub_le_sub_left hz.2 _, sub_le_sub_left hz.1 _⟩
  have hbound : ‖z‖ ≤ 1 + ‖w‖ := by simpa [w] using norm_sub_le (1 : ℂ) w
  change ‖z ^ N * u.val w‖ ≤ _
  rw [norm_mul, norm_pow]
  rcases le_total ‖w‖ 1 with h | h
  · have hA' : ‖u.val w‖ ≤ A := by simpa using hA (mem_image_of_mem _ hw)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖z‖ ≤ 2) N)
      (hA'.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  · have hB' := hB (mem_image_of_mem _ hw)
    rw [norm_mul, norm_pow] at hB'
    calc
      _ ≤ (2 * ‖w‖) ^ N * ‖u.val w‖ := by gcongr; linarith
      _ = 2 ^ N * (‖w‖ ^ N * ‖u.val w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hB'.trans (le_max_right _ _)) (by positivity)

private theorem existsUnique_sLocalZetaPair_reflect (u : B⁺) :
    ∃ v : B⁻, ∀ z, v.val z = u.val (1 - z) := by
  exact ⟨⟨_, existsUnique_sLocalZetaPair_reflect_mem (I := rightInterval) (J := leftInterval)
    (fun x ↦ by simp [mem_Ioi, mem_Iio]) u⟩, fun _ ↦ rfl⟩

private theorem existsUnique_sLocalZetaPair_eval (χ : PontryaginDual Jₛ) (s : ℂ)
    (hs : s ∈ rightHalf) : ∃ E : Θω(restrict₁(χ)) →ₗ[ℂ] ℂ,
      ∀ f : ℬₛ, E (Submodule.Quotient.mk f) = Zₛ f (normChart(χ) s) := by
  let c := normChart(χ) s
  have htwist (z : ℂ) : quasiCharacterNormTwist mₛ hmₛ c z = normChart(χ) (z + s) := by
    ext1 g
    let N : ℂ := (normℝ(mₛ g) : ℂ)
    change (χ g : ℂ) * N ^ s * N ^ z = (χ g : ℂ) * N ^ (z + s)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)), mul_assoc]
  have hc : 0 ≤ sLocalIdelicOrderBound c := by
    simp only [sLocalIdelicOrderBound, htwist, le_min_iff]
    have hρ := sLocalRhoFactor_iteratedDeriv_analyticOn χ 0 s hs
    rw [iteratedDeriv_zero] at hρ
    exact ⟨le_rfl, ((show AnalyticAt ℂ (fun w ↦ ρₛ(χ, w)) (0 + s) by simpa using hρ).comp
      (f := fun z : ℂ ↦ z + s) (by fun_prop)).meromorphicOrderAt_nonneg⟩
  let x : {d // 0 ≤ sLocalIdelicOrderBound (F := F) (S := S) d} := ⟨c, hc⟩
  let E : ℬₛ →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ Zₛ f c
      map_add' := fun f g ↦ congrArg (fun h ↦ DFunLike.coe h x)
        (sLocalIdelicZFunction_isLinear.map_add f g)
      map_smul' := fun a f ↦ congrArg (fun h ↦ DFunLike.coe h x)
        (sLocalIdelicZFunction_isLinear.map_smul a f) }
  refine ⟨(LinearMap.ker (φω(restrict₁(χ)))).liftQ E ?_, fun _ ↦ rfl⟩
  intro f hf
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (restrict₁(χ)) f).mp hf x
  intro u
  change (χ u.val : ℂ) * (normℝ(mₛ u.val) : ℂ) ^ s = (χ u.val : ℂ)
  rw [u.prop]
  simp

/-- The S-local zeta function satisfies the functional equation in the overlap strip. -/
theorem existsUnique_sLocalZetaPair_equation (χ : PontryaginDual Jₛ) (f : ℬₛ)
    (s : ℂ) (hs : s ∈ overlap) :
    Zₛ f (normChart(χ) s) = ρₛ(χ, s) * Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s)) := by
  have ht : 1 - s ∈ rightHalf := by simpa [mem_preimage, mem_Ioi] using sub_pos.mpr hs.2
  have hd : dualQuasiCharacter mₛ hmₛ (normChart(χ) s) = normChart(χ⁻¹) (1 - s) := by
    ext1 g
    let N : ℂ := (normℝ(mₛ g) : ℂ)
    have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
    change N * normChart(χ) s g⁻¹ = ((χ g : ℂ)⁻¹ * N ^ (1-s))
    rw [map_inv]
    change N * ((χ g : ℂ) * N ^ s)⁻¹ = (χ g : ℂ)⁻¹ * N ^ (1-s)
    rw [Complex.cpow_sub _ _ hN, Complex.cpow_one, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have he := sLocalIdelicZetaIntegral_functionalEquation f χ s hs
  exact (sLocalIdelicZFunction_eq_integral f ⟨χ, s, hs.1, rfl⟩).trans <| he.trans <|
    congrArg (ρₛ(χ, s) * ·) ((congrArg (sLocalIdelicZetaIntegral (Fourierₛ f)) hd).trans
      (sLocalIdelicZFunction_eq_integral (Fourierₛ f) ⟨χ⁻¹, 1-s, ht, rfl⟩).symm)

private theorem existsUnique_sLocalZetaPair_ext {I : Set ℝ} {u v : SchwartzBergman I}
    (h : EqOn u.val v.val (Complex.re ⁻¹' I)) : u = v := by
  apply Subtype.ext
  funext z
  by_cases hz : z ∈ Complex.re ⁻¹' I
  · exact h hz
  · exact (u.property.1 hz).trans (v.property.1 hz).symm

/-- Multiplication by the functional-equation factor and restriction to the overlap
still detect a left component, by the holomorphic identity theorem. -/
private theorem existsUnique_sLocalZetaPair_left_ext (χ : PontryaginDual Jₛ) (u v : B⁻)
    (h : ∀ z ∈ overlap, ρₛ(χ, z) * u.val z = ρₛ(χ, z) * v.val z) : u = v := by
  have hol (w : B⁻) : AnalyticOnNhd ℂ w.val leftHalf :=
    w.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re)
  have hband : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2 : ℂ), s ∈ overlap :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by
      norm_num [mem_preimage, mem_Ioo]))
  apply existsUnique_sLocalZetaPair_ext
  apply (hol u).eqOn_of_preconnected_of_frequently_eq (hol v)
    (convex_halfSpace_re_lt 1).isPreconnected (z₀ := 1/2) (by norm_num [mem_preimage])
  apply Filter.Eventually.frequently
  filter_upwards [hband, nhdsNE_le_codiscrete _ (sLocalRhoFactor_mul_dual χ)] with z hz hprod
  have hne : ρₛ(χ, z) ≠ 0 := left_ne_zero_of_mul
    (hprod.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : Aₛˣ) : Jₛ)).map (normChart(χ) z)).ne_zero)
  exact mul_left_cancel₀ hne (h z hz)

/-- Paper: (5.4.1.2), p. 265.
The two zeta restrictions descend uniquely as a linear map on homogeneous theta classes.
Deviation: We use the unitary-lift coordinates of Remark 5.4.1.2. The normalized lift
for a chosen section recovers the coordinates of Theorem 5.4.1.1. If the lift
has frequency x on the section, both entries, as functions of s here, shift by +ix.
The unreflected Fourier Mellin transform separately has frequency -x. -/
theorem existsUnique_sLocalZetaPair (χ : PontryaginDual Jₛ) :
    ∃! U : Θω(restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻, ∀ (f : ℬₛ),
      EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (U (Submodule.Quotient.mk f)).2.val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by
  classical
  choose E hE using fun s : rightHalf ↦ existsUnique_sLocalZetaPair_eval χ s.val s.property
  -- The right evaluations descend individually to the quotient. On the overlap they
  -- are also the evaluations of the reflected component multiplied by the Tate factor.
  let T : B⁺ →ₗ[ℂ] (rightHalf → ℂ) :=
    LinearMap.pi fun s ↦ (LinearMap.proj s.val).comp (schwartzBergmanSubmodule rightInterval).subtype
  let D : B⁻ →ₗ[ℂ] (overlap → ℂ) :=
    LinearMap.pi fun s ↦ ρₛ(χ, s.val) •
      ((LinearMap.proj s.val).comp (schwartzBergmanSubmodule leftInterval).subtype)
  have hT : Injective T := fun _ _ he ↦ existsUnique_sLocalZetaPair_ext
    (fun z hz ↦ congrFun he ⟨z, hz⟩)
  have hD : Injective D := fun u v he ↦ existsUnique_sLocalZetaPair_left_ext χ u v
    (fun z hz ↦ congrFun he ⟨z, hz⟩)
  let A := T.leftInverse.comp (LinearMap.pi E)
  let B := D.leftInverse.comp (LinearMap.pi fun s : overlap ↦ E ⟨s.val, s.property.1⟩)
  have spec (f : ℬₛ) : EqOn (A (Submodule.Quotient.mk f)).val
        (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (B (Submodule.Quotient.mk f)).val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by
    refine (existsUnique_sLocalZetaPair_right (F := F) (S := S) χ f).elim fun u hu ↦ ?_
    refine (existsUnique_sLocalZetaPair_right (F := F) (S := S) χ⁻¹ (Fourierₛ f)).elim fun w hw ↦ ?_
    refine (existsUnique_sLocalZetaPair_reflect w).elim fun v hv ↦ ?_
    have hv' : EqOn v.val (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1-s))) leftHalf :=
      fun s hs ↦ (hv s).trans (hw (show 1 - s ∈ rightHalf by
        simpa [mem_preimage, mem_Ioi] using sub_pos.mpr hs))
    have eA : (LinearMap.pi E) (Submodule.Quotient.mk f) = T u :=
      funext fun s ↦ (hE s f).trans (hu s.property).symm
    have eB : (LinearMap.pi fun s : overlap ↦ E ⟨s.val, s.property.1⟩) (Submodule.Quotient.mk f) = D v :=
      funext fun s ↦ (hE ⟨s.val, s.property.1⟩ f).trans
        ((existsUnique_sLocalZetaPair_equation χ f s s.property).trans
          (congrArg (ρₛ(χ, s.val) * ·) (hv' s.property.2).symm))
    have hA : A (Submodule.Quotient.mk f) = u :=
      (congrArg T.leftInverse eA).trans (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hT) u)
    have hB : B (Submodule.Quotient.mk f) = v :=
      (congrArg D.leftInverse eB).trans (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hD) v)
    exact ⟨fun s hs ↦ (congrArg (fun g : B⁺ ↦ g.val s) hA).trans (hu hs),
      fun s hs ↦ (congrArg (fun g : B⁻ ↦ g.val s) hB).trans (hv' hs)⟩
  refine ⟨A.prod B, spec, ?_⟩
  intro V hV
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro f
  exact Prod.ext (existsUnique_sLocalZetaPair_ext ((hV f).1.trans (spec f).1.symm))
    (existsUnique_sLocalZetaPair_ext ((hV f).2.trans (spec f).2.symm))

/-- Paper: (5.4.1.2), p. 265.
The map pairs the zeta transform with the reflected zeta transform of the Fourier transform.
Deviation: The chart is the unitary-lift chart of Remark 5.4.1.2. -/
def sLocalZetaPair (χ : PontryaginDual Jₛ) : Θω(restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻ :=
  (existsUnique_sLocalZetaPair (F := F) (S := S) χ).exists.choose

/-- Paper: (5.4.1.2), p. 265.
On test functions the two components evaluate to their respective zeta integrals
on their half-planes of convergence. -/
theorem sLocalZetaPair_mk (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    EqOn (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).1.val
      (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
    EqOn (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2.val
      (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by
  have h := (existsUnique_sLocalZetaPair (F := F) (S := S) χ).exists.choose_spec f
  exact h

/-- Holomorphic multipliers with polynomial bounds on closed substrips give
continuous maps into the Schwartz–Bergman space of the overlap. -/
private theorem existsUnique_sLocalZetaMatchingDifference_multiplier
    (I : Set ℝ) (hI : overlapInterval ⊆ I) (R : ℂ → ℂ)
    (hR : DifferentiableOn ℂ R overlap)
    (hg : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ overlapInterval →
      ∃ C ≥ (0 : ℝ), ∃ m : ℕ, ∀ z ∈ Complex.re ⁻¹' Icc a b, ‖R z‖ ≤ C * ‖z‖ ^ m) :
    ∃ L : SchwartzBergman I →L[ℂ] B⁰, ∀ f, EqOn (L f).val (fun z ↦ R z * f.val z) overlap := by
  classical
  have hbound (C : ℝ) (m N : ℕ) (f : SchwartzBergman I) (z : ℂ)
      (hz : ‖R z‖ ≤ C * ‖z‖ ^ m) :
      ‖z ^ N * (R z * f.val z)‖ ≤ C * ‖z ^ (N + m) * f.val z‖ := by
    simp only [norm_mul, norm_pow, pow_add]
    calc
      ‖z‖ ^ N * (‖R z‖ * ‖f.val z‖) = ‖R z‖ * (‖z‖ ^ N * ‖f.val z‖) := by ring
      _ ≤ (C * ‖z‖ ^ m) * (‖z‖ ^ N * ‖f.val z‖) := by gcongr
      _ = C * (‖z‖ ^ N * ‖z‖ ^ m * ‖f.val z‖) := by ring
  have hmem (f : SchwartzBergman I) :
      (overlap).indicator (fun z ↦ R z * f.val z) ∈ schwartzBergmanSubmodule overlapInterval := by
    refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
    · exact (hR.mul (f.property.2.1.mono (preimage_mono hI))).congr
        (fun z hz ↦ indicator_of_mem hz _)
    · intro a b hab hsub N
      obtain ⟨C, hC, m, hm⟩ := hg a b hab hsub
      obtain ⟨B, hB⟩ := f.property.2.2 a b hab (hsub.trans hI) (N + m)
      refine ⟨C * B, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      change ‖z ^ N * (overlap).indicator (fun w ↦ R w * f.val w) z‖ ≤ C * B
      have hz' : z ∈ overlap := hsub hz
      rw [indicator_of_mem hz']
      exact (hbound C m N f z (hm z hz)).trans
        (mul_le_mul_of_nonneg_left (hB ⟨z, hz, rfl⟩) hC)
  let T (f : SchwartzBergman I) : B⁰ :=
    ⟨(overlap).indicator (fun z ↦ R z * f.val z), hmem f⟩
  have hT (f : SchwartzBergman I) : EqOn (T f).val (fun z ↦ R z * f.val z) overlap := by
    intro z hz
    change (overlap).indicator (fun w ↦ R w * f.val w) z = R z * f.val z
    exact indicator_of_mem hz _
  let L : SchwartzBergman I →ₗ[ℂ] B⁰ :=
    { toFun := T
      map_add' := fun f g ↦ existsUnique_sLocalZetaPair_ext (fun z hz ↦ by
        change (T (f + g)).val z = (T f).val z + (T g).val z
        rw [hT (f + g) hz, hT f hz, hT g hz]
        exact mul_add _ _ _)
      map_smul' := fun c f ↦ existsUnique_sLocalZetaPair_ext (fun z hz ↦ by
        change (T (c • f)).val z = c * (T f).val z
        rw [hT (c • f) hz, hT f hz]
        change R z * (c * f.val z) = c * (R z * f.val z)
        exact mul_left_comm _ _ _) }
  let P (J : Set ℝ) (i : J × ℕ) : Seminorm ℂ (SchwartzBergman J) :=
    Seminorm.of (fun f ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm J i).1 (schwartzBergman_l2_seminorm J i).2
  have hP (J : Set ℝ) : WithSeminorms (P J) :=
    withGeneratingSeminorms_spec (schwartzBergmanSubmodule J) (P J)
  refine ⟨⟨L, ?_⟩, hT⟩
  apply (hP overlapInterval).continuous_of_continuous_comp L
  rintro ⟨a, N⟩
  have ha : Icc (a : ℝ) a ⊆ overlapInterval := by
    simpa only [Icc_self, singleton_subset_iff] using a.property
  obtain ⟨C, hC, m, hm⟩ := hg a a le_rfl ha
  let b : I := ⟨a, hI a.property⟩
  let c : ℝ≥0 := ⟨C, hC⟩
  apply Seminorm.continuous_of_le (q := c • P I (b, N + m))
    (((hP I).continuous_seminorm (b, N + m)).const_smul c)
  intro f
  let u := weightedVerticalTrace a N (T f).val
  let v := weightedVerticalTrace b (N + m) f.val
  have hu : MemLp u 2 volume :=
    schwartzBergman_trace_memLp overlapInterval a 2 (by norm_num) (by norm_num) N (T f)
  have hv : MemLp v 2 volume :=
    schwartzBergman_trace_memLp I b 2 (by norm_num) (by norm_num) (N + m) f
  have hle (t : ℝ) : ‖u t‖ ≤ ‖(C • v) t‖ := by
    let z : ℂ := (a : ℝ) + (t : ℂ) * Complex.I
    have hz : z ∈ Complex.re ⁻¹' Icc (a : ℝ) a := by simp [z]
    change ‖z ^ N * (T f).val z‖ ≤ ‖C • (z ^ (N + m) * f.val z)‖
    rw [hT f (ha hz), norm_smul, Real.norm_of_nonneg hC]
    exact hbound C m N f z (hm z hz)
  change lpNorm u 2 volume ≤ C * lpNorm v 2 volume
  have hnorm : (‖C‖₊ : ℝ) = C := Real.norm_of_nonneg hC
  rw [← hnorm, ← lpNorm_const_smul]
  exact ENNReal.toReal_mono (hv.const_smul C).eLpNorm_ne_top
    (eLpNorm_mono hu.aestronglyMeasurable hle)

-- The periodicity and epsilon estimates are adapted from Ch03 Sec3b.
/-- The norm powers of a nonarchimedean local character are periodic in height. -/
private theorem rhoGrowth_finite_periodic (v : HeightOneSpectrum (𝓞 F))
    (η : PontryaginDual (v.adicCompletion F)ˣ) :
    ∃ T : ℝ, 0 < T ∧ Periodic (quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom) (continuous_finiteLocalModule v)
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η)) ((T : ℂ) * Complex.I) := by
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  let T := 2 * Real.pi / Real.log q
  refine ⟨T, div_pos (by positivity) (Real.log_pos hq), fun z ↦ ?_⟩
  ext1 u
  let k := WithZero.log (Valued.v u.val)
  have hnorm : ‖u.val‖ = q ^ k := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
      ((Valuation.ne_zero_iff _).mpr u.ne_zero)]
    push_cast
    rfl
  have hu : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have hlog : Complex.log (‖u.val‖ : ℂ) = (k : ℂ) * (Real.log q : ℂ) := by
    rw [← Complex.ofReal_log hu.le, hnorm, Real.log_zpow, Complex.ofReal_mul,
      Complex.ofReal_intCast]
  have hprod : (Real.log q : ℂ) * ((T : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I := by
    dsimp only [T]
    push_cast
    field_simp [(Real.log_pos hq).ne']
  have hpow : (‖u.val‖ : ℂ) ^ ((T : ℂ) * Complex.I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), hlog, mul_assoc, hprod,
      Complex.exp_int_mul_two_pi_mul_I]
  change (η u : ℂ) * (‖u.val‖ : ℂ) ^ (z + (T : ℂ) * Complex.I) =
    (η u : ℂ) * (‖u.val‖ : ℂ) ^ z
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne'), hpow, mul_one]

/-- A continuous function periodic in the imaginary direction is bounded on closed strips. -/
private theorem rhoGrowth_periodic_bound {p : ℂ → ℂ} {T : ℝ}
    (hT : 0 < T) (hperiod : Periodic p ((T : ℂ) * Complex.I))
    (hp : Continuous p) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖p z‖ ≤ C := by
  let K := Complex.reProdIm (Icc a b) (Icc 0 T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hK.bddAbove_image hp.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ ?_⟩
  let n := ⌊z.im / T⌋
  let v := (n : ℂ) * ((T : ℂ) * Complex.I)
  have hvre : v.re = 0 := by simp [v, Complex.mul_re, Complex.mul_im]
  have hvim : v.im = (n : ℝ) * T := by simp [v, Complex.mul_re, Complex.mul_im]
  have hzK : z - v ∈ K := by
    have hfloor := (le_div_iff₀ hT).mp (Int.floor_le (z.im / T))
    have hceil := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (z.im / T))
    change (z - v).re ∈ Icc a b ∧ (z - v).im ∈ Icc 0 T
    rw [Complex.sub_re, hvre, sub_zero, Complex.sub_im, hvim]
    exact ⟨hz, ⟨by dsimp [n]; linarith, by dsimp [n]; linarith⟩⟩
  have hper : p z = p (z - v) := by
    simpa only [v, zsmul_eq_mul, sub_add_cancel] using (hperiod.zsmul n (z - v))
  rw [hper]
  exact (hC ⟨z - v, hzK, rfl⟩).trans (le_max_left _ _)

/-- The archimedean epsilon factors have norm one, and periodicity of each finite factor
gives a bound for their product on every closed strip. -/
private theorem rhoGrowth_epsilon_bound (χ : PontryaginDual Jₛ) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖sLocalEpsilonFactor (normChart(χ) z)‖ ≤ C := by
  classical
  have hfinite (v : S) : ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b →
      ‖finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (normChart(χ) z))‖ ≤ C := by
    obtain ⟨η, hη, _⟩ := sLocalFiniteRestriction_exists_normTwistChart χ v
    obtain ⟨T, hT, hperiod⟩ := rhoGrowth_finite_periodic v.val η
    have hE : Periodic (finiteLocalEpsilonFactor v.val ∘ (quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom) (continuous_finiteLocalModule v.val)
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η)))
        ((T : ℂ) * Complex.I) := fun z ↦ congrArg (finiteLocalEpsilonFactor v.val) (hperiod z)
    simpa only [hη, Function.comp_apply] using
      rhoGrowth_periodic_bound hT hE
        (continuous_iff_continuousAt.mpr fun z ↦
          ((finiteLocalEpsilonFactor_entire v.val η) z (mem_univ z)).continuousAt) a b
  choose C hC hbound using hfinite
  refine ⟨∏ v : S, C v, Finset.prod_nonneg fun v _ ↦ hC v, fun z hz ↦ ?_⟩
  have harch (w : InfinitePlace F) :
      ‖infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w (normChart(χ) z))‖ = 1 := by
    unfold infiniteLocalEpsilonFactor
    split <;> rw [norm_pow, Complex.norm_I, one_pow]
  rw [sLocalEpsilonFactor, norm_mul, norm_prod, norm_prod]
  simp only [harch, Finset.prod_const_one, one_mul]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hbound v z hz)

-- The inverse lift restricts to the inverse character (Ch03 Sec3b, cleared_inverse_factors).
private theorem rhoGrowth_dual_lift (χ : PontryaginDual Jₛ) (η : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (h : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist η 0,h⟩ = normChart(χ) 0) (w : ℂ) :
    sLocalHeckeL (normChart(χ⁻¹) w) = heckeGammaFactor η⁻¹ w * ∏ v : S, finiteHeckeEulerFactor η⁻¹ v.val w := by
  have hη (g : IdeleClassGroup (𝓞 F) F) :
      ideleClassNormTwist η⁻¹ 0 g = (ideleClassNormTwist η 0 g)⁻¹ := by
    change (((η g)⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ) = ((η g : ℂ) * _ ^ (0 : ℂ))⁻¹
    simp
  have hr : ideleClassNormTwist η⁻¹ 0 ∈ unramifiedOutside F S := by
    rw [mem_unramifiedOutside_iff] at h ⊢
    intro v hv u
    have hu := h v hv u
    exact (hη _).trans ((congrArg Inv.inv hu).trans inv_one)
  apply sLocalHeckeL_eq_partialEulerProduct _ _ hr
  ext1 x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
  have hbase := DFunLike.congr_fun he (QuotientGroup.mk g)
  rw [sIdeleRestriction_mk] at hbase ⊢
  rw [hη, hbase]
  change ((χ _ : ℂ) * _ ^ (0 : ℂ))⁻¹ = (((χ _)⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ)
  simp

/-- On a positive half-plane both the finite Euler product and its reciprocal are bounded. -/
private theorem rhoGrowth_finite_bound (η : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (a : ℝ) (ha : 0 < a) :
    ∃ C ≥ (1 : ℝ), ∀ z : ℂ, a ≤ z.re →
      ‖∏ v : S, finiteHeckeEulerFactor η v.val z‖ ≤ C ∧
      ‖(∏ v : S, finiteHeckeEulerFactor η v.val z)⁻¹‖ ≤ C := by
  classical
  let D (v : S) := max 2 (1 - (v.val.asIdeal.absNorm : ℝ) ^ (-a))⁻¹
  have hD (v : S) : 1 ≤ D v := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
  refine ⟨∏ v, D v, Finset.one_le_prod₀ (fun v _ ↦ hD v), fun z hz ↦ ?_⟩
  have hl (v : S) : ‖finiteHeckeEulerFactor η v.val z‖ ≤ D v ∧
      ‖(finiteHeckeEulerFactor η v.val z)⁻¹‖ ≤ D v := by
    let q := (v.val.asIdeal.absNorm : ℝ)
    have hq : 1 < q := by dsimp only [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    have hr : q ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr ha)
    let w := (ideleClassNormTwist η 0).localValue v.val * (q : ℂ) ^ (-z)
    have hw : ‖w‖ ≤ q ^ (-a) := by
      rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hz)
    rw [finiteHeckeEulerFactor]
    split_ifs
    · change ‖(1 - w)⁻¹‖ ≤ D v ∧ ‖((1 - w)⁻¹)⁻¹‖ ≤ D v
      have hlow : 1 - q ^ (-a) ≤ ‖1-w‖ := by
        have h := norm_sub_norm_le (1 : ℂ) w
        rw [norm_one] at h
        linarith
      rw [norm_inv, inv_inv]
      exact ⟨(inv_anti₀ (sub_pos.mpr hr) hlow).trans (le_max_right _ _),
        ((norm_sub_le _ _).trans (by rw [norm_one]; linarith [hw.trans hr.le] :
          ‖(1 : ℂ)‖ + ‖w‖ ≤ 2)).trans (le_max_left _ _)⟩
    · simpa using hD v
  rw [← Finset.prod_inv_distrib, norm_prod, norm_prod]
  exact ⟨Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ (hl v).1),
    Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ (hl v).2)⟩

/-- The S-local correcting factor has polynomial growth on every closed substrip
of the overlap. The degree may depend on the substrip and the character. -/
private theorem existsUnique_sLocalZetaMatchingDifference_rhoGrowth (χ : PontryaginDual Jₛ)
    (a b : ℝ) (hab : a ≤ b) (hsub : Icc a b ⊆ overlapInterval) :
    ∃ C ≥ (0 : ℝ), ∃ m : ℕ, ∀ z ∈ Complex.re ⁻¹' Icc a b, ‖ρₛ(χ, z)‖ ≤ C * ‖z‖ ^ m := by
  classical
  let l := a / 2
  let r := (1 + b) / 2
  have ha := (hsub (left_mem_Icc.mpr hab)).1
  have hb := (hsub (right_mem_Icc.mpr hab)).2
  have hl : 0 < l := half_pos ha
  have hal : l < a := half_lt_self ha
  have hbr : b < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  obtain ⟨η, hη, he, _⟩ := sLocal_character_extension χ
  obtain ⟨E, hE, hε⟩ := rhoGrowth_epsilon_bound χ l r
  obtain ⟨G, T, hG, _, hΓ⟩ := heckeGamma_reflection_bound η⁻¹ (1-r) (1-l)
  obtain ⟨A, hA, h₁⟩ := rhoGrowth_finite_bound (S := S) η l hl
  obtain ⟨B, hB, h₂⟩ := rhoGrowth_finite_bound (S := S) η⁻¹ (1-r) (sub_pos.mpr hr)
  let n := Module.finrank ℚ F
  let C := E * G * (A * B)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hE hG.le) (mul_nonneg (by linarith) (by linarith))
  let R (z : ℂ) := ρₛ(χ,z)
  have hc {z : ℂ} (hz : 0 < z.re) : ContinuousAt R z := by
    have h := sLocalRhoFactor_iteratedDeriv_analyticOn (F := F) (S := S) χ 0 z hz
    rw [iteratedDeriv_zero] at h
    exact h.continuousAt
  have high : ∀ᶠ z : ℂ in codiscrete ℂ, z.re ∈ Icc l r → max T 1 ≤ |z.im| →
      ‖R z‖ ≤ C * ‖z‖ ^ n := by
    filter_upwards [sLocalRhoFactor_eq_epsilon_mul χ] with z hz hs ht
    have hy : 1 ≤ |z.im| := (le_max_right T 1).trans ht
    have hy' : |(1-z).im| = |z.im| := by simp
    have hx' : (1-z).re = 1-z.re := by simp
    have hg := hΓ (1-z) (by rw [hx']; linarith [hs.2]) (by rw [hx']; linarith [hs.1])
      (hy' ▸ (le_max_left _ _).trans ht)
    rw [inv_inv, sub_sub_cancel, hx', hy'] at hg
    have hn : (n : ℝ) * (1/2 - (1-z.re)) ≤ n := by
      apply mul_le_of_le_one_right (Nat.cast_nonneg _)
      linarith [hs.2]
    have hp := Real.rpow_le_rpow_of_exponent_le hy hn
    rw [Real.rpow_natCast] at hp
    have hΓ' : ‖heckeGammaFactor η z / heckeGammaFactor η⁻¹ (1-z)‖ ≤ G * ‖z‖ ^ n :=
      hg.trans (mul_le_mul_of_nonneg_left (hp.trans (pow_le_pow_left₀ (abs_nonneg _)
        (Complex.abs_im_le_norm z) n)) hG.le)
    dsimp only at hz
    rw [sLocalNormTwistChart_dual, sLocalHeckeL_eq_partialEulerProduct χ η hη he,
      rhoGrowth_dual_lift χ η hη he, mul_div_mul_comm] at hz
    change ‖ρₛ(χ,z)‖ ≤ _
    rw [hz, norm_mul, norm_mul, div_eq_mul_inv (∏ v : S, _) _, norm_mul]
    have heul := mul_le_mul (h₁ z hs.1).1 ((h₂ (1-z) (by rw [hx']; linarith [hs.2])).2)
      (norm_nonneg _) (by linarith : 0 ≤ A)
    calc
      _ ≤ E * ((G * ‖z‖ ^ n) * (A * B)) := by gcongr; exact hε z hs
      _ = _ := by dsimp [C]; ring
  let K := Complex.reProdIm (Icc a b) (Icc (-(max T 1)) (max T 1))
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (f := fun z ↦ R z / z ^ n)
    (fun z hz ↦ ((hc (lt_of_lt_of_le ha hz.1.1)).div (continuousAt_id.pow n)
      (pow_ne_zero _ (fun h ↦ (lt_of_lt_of_le ha hz.1.1).ne' (congrArg Complex.re h)))).continuousWithinAt)
  refine ⟨max C D, hC.trans (le_max_left _ _), n, fun z hz ↦ ?_⟩
  have hz0 : 0 < z.re := lt_of_lt_of_le ha hz.1
  by_cases ht : |z.im| ≤ max T 1
  · have hd := hD z ⟨hz, abs_le.mp ht⟩
    rw [norm_div, norm_pow] at hd
    have hnz : z ≠ 0 := fun h ↦ hz0.ne' (congrArg Complex.re h)
    exact ((div_le_iff₀ (pow_pos (norm_pos_iff.mpr hnz) _)).mp hd).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hnear := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hal.trans_le hz.1)
    have hnear' := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (hz.2.trans_lt hbr)
    have ht' := (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)).mem_nhds
      (lt_of_not_ge ht)
    have hbound : ∀ᶠ y in 𝓝[≠] z, ‖R y‖ ≤ C * ‖y‖ ^ n := by
      filter_upwards [nhdsNE_le_codiscrete z high, nhdsWithin_le_nhds hnear,
        nhdsWithin_le_nhds hnear', nhdsWithin_le_nhds ht'] with y h h₁ h₂ h₃
      exact h ⟨le_of_lt h₁, le_of_lt h₂⟩ (le_of_lt h₃)
    exact (le_of_tendsto_of_tendsto (hc hz0).norm.continuousWithinAt
      ((continuous_const.mul (continuous_norm.pow n)).continuousAt.continuousWithinAt) hbound).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg z) n))

/-- Paper: (5.4.1.3), p. 266.
Subtracting the corrected second component from the first on the overlap is a
continuous linear map into the Schwartz–Bergman space of the overlap. -/
theorem existsUnique_sLocalZetaMatchingDifference (χ : PontryaginDual Jₛ) :
    ∃! D : B⁺ × B⁻ →L[ℂ] B⁰, ∀ p : B⁺ × B⁻,
      EqOn (D p).val (fun s ↦ p.1.val s - ρₛ(χ, s) * p.2.val s) overlap := by
  obtain ⟨L, hL⟩ := existsUnique_sLocalZetaMatchingDifference_multiplier rightInterval
    (fun _ h ↦ h.1) (fun _ ↦ 1) (differentiableOn_const 1)
    (fun _ _ _ _ ↦ ⟨1, by norm_num, 0, by simp⟩)
  have hρ := sLocalRhoFactor_iteratedDeriv_analyticOn χ 0
  rw [iteratedDeriv_zero] at hρ
  obtain ⟨R, hR⟩ := existsUnique_sLocalZetaMatchingDifference_multiplier leftInterval
    (fun _ h ↦ h.2) (fun z ↦ ρₛ(χ, z))
    (hρ.differentiableOn.mono (fun _ h ↦ h.1))
    (existsUnique_sLocalZetaMatchingDifference_rhoGrowth χ)
  let D := L.comp (ContinuousLinearMap.fst ℂ B⁺ B⁻) - R.comp (ContinuousLinearMap.snd ℂ B⁺ B⁻)
  have hD (p : B⁺ × B⁻) : EqOn (D p).val (fun z ↦ p.1.val z - ρₛ(χ, z) * p.2.val z) overlap := by
    intro z hz
    change (L p.1).val z - (R p.2).val z = _
    simp only [hL p.1 hz, hR p.2 hz, one_mul]
  refine ⟨D, hD, fun E hE ↦ ?_⟩
  exact ContinuousLinearMap.ext fun p ↦ existsUnique_sLocalZetaPair_ext ((hE p).trans (hD p).symm)

/-- Paper: (5.4.1.3), p. 266.
The space W is the kernel of the difference of the two restrictions, with the
second restriction multiplied by the local functional-equation factor. -/
def sLocalZetaMatching (χ : PontryaginDual Jₛ) : Submodule ℂ (B⁺ × B⁻) :=
  let difference : B⁺ × B⁻ →L[ℂ] B⁰ :=
    (existsUnique_sLocalZetaMatchingDifference (F := F) (S := S) χ).exists.choose
  LinearMap.ker difference.toLinearMap

/-- A continuous linear map into a Schwartz–Bergman space given pointwise on the strip by a
difference vanishes exactly where the two terms agree on the strip. -/
private theorem mem_sLocalZetaMatching_aux {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] {I : Set ℝ} (D : X →L[ℂ] SchwartzBergman I) (a b : X → ℂ → ℂ)
    (hD : ∀ p, EqOn (D p).val (fun s ↦ a p s - b p s) (Complex.re ⁻¹' I)) (p : X) :
    p ∈ LinearMap.ker D.toLinearMap ↔ EqOn (a p) (b p) (Complex.re ⁻¹' I) := by
  have h0 : ((0 : SchwartzBergman I) : schwartzBergmanSubmodule I).val = 0 := rfl
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h s hs
    have hs' := hD p hs
    rw [h, h0] at hs'
    exact sub_eq_zero.mp hs'.symm
  · intro h
    have hval : ((D p : SchwartzBergman I) : schwartzBergmanSubmodule I).val = 0 := by
      funext s
      by_cases hs : s ∈ Complex.re ⁻¹' I
      · exact (hD p hs).trans (sub_eq_zero.mpr (h hs))
      · exact (D p).property.1 hs
    exact Subtype.ext (hval.trans h0.symm)

/-- Paper: (5.4.1.3), p. 266.
A pair belongs to W exactly when its components satisfy the functional equation
at each point in the overlap strip. -/
theorem mem_sLocalZetaMatching (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻) :
    p ∈ sLocalZetaMatching (F := F) (S := S) χ ↔
      EqOn p.1.val (fun s ↦ ρₛ(χ, s) * p.2.val s) overlap := by
  have h := (existsUnique_sLocalZetaMatchingDifference (F := F) (S := S) χ).exists.choose_spec
  have key := mem_sLocalZetaMatching_aux (I := overlapInterval) _
    (fun p : B⁺ × B⁻ ↦ p.1.val) (fun p s ↦ ρₛ(χ, s) * p.2.val s) h p
  exact key

/-- The zeta pair lands in the matching space: on the overlap strip the two components
satisfy the local functional equation of (5.4.1.3), by the equation proved for the
integral representation on test functions. -/
private theorem sLocalZetaPair_range_le_matching (χ : PontryaginDual Jₛ) :
    LinearMap.range (sLocalZetaPair (F := F) (S := S) χ) ≤
      sLocalZetaMatching (F := F) (S := S) χ := by
  rintro p ⟨x, rfl⟩
  obtain ⟨f, rfl⟩ : ∃ f : ℬₛ, Submodule.Quotient.mk f = x := by
    exact Submodule.Quotient.mk_surjective
      (p := LinearMap.ker (φω(restrict₁(χ)))) x
  rw [mem_sLocalZetaMatching]
  obtain ⟨h₁, h₂⟩ := sLocalZetaPair_mk (F := F) (S := S) χ f
  intro s hs
  calc (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).1.val s
      = Zₛ f (normChart(χ) s) := h₁ hs.1
    _ = ρₛ(χ, s) * Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s)) :=
        existsUnique_sLocalZetaPair_equation χ f s hs
    _ = ρₛ(χ, s) * (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2.val s :=
        congrArg _ (h₂ hs.2).symm

/-- Fourier–Mellin inversion and the radial lift of Lemma 5.3.4.3 realize an entire
Schwartz–Bergman datum on any unitary chart. The radial integral calculation is from
`polarFree_zeta_of_radial` and `polarFree_zeta_twist` in §5.3. -/
private theorem sLocalZetaPair_first_component_attained_entire (χ : PontryaginDual Jₛ)
    (H : SchwartzBergman univ) :
    ∃ f : ℬₛ, EqOn H.val (fun z ↦ Zₛ f (normChart(χ) z)) rightHalf := by
  let r (w : {w : InfinitePlace F // w.IsReal}) :=
    (⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.property,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal w.property).toHomeomorph.isHomeomorph⟩ :
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
  let c (w : {w : InfinitePlace F // w.IsComplex}) :=
    (⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.property).toHomeomorph.isHomeomorph⟩ :
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
  let M := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  let φ := M.symm H
  obtain ⟨g, hg⟩ := sLocalHomogeneousTheta_trivial_exists_polarFree (S := S) r c φ
  obtain ⟨A, hA⟩ := sAdelePolarFree_quasiCharacter_mul (S := S) r c
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ⁻¹)
  refine ⟨(A g).val, fun z hz ↦ ?_⟩
  let π := Units.map (adeleProjection F S).toMonoidHom
  have hπ : Continuous π := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Aₛˣ := ⟨π.comp (canonicalIdeleNormSection F),
    hπ.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := sIdeleNorm_project_canonicalSection F S
  have hM := positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty φ z trivial
  change (M φ).val z = _ at hM
  rw [M.apply_symm_apply H] at hM
  refine hM.trans <| Eq.trans ?_ ((sLocalRadialMellinIntegral_eq_theta τ hτ g.val 1 z hz).trans
    ((sLocalThetaMellinIntegral_eq_zeta g.val ⟨1, z, hz, rfl⟩).trans ?_))
  · let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
    have hμ : positiveRealHaar = volume.map e := by
      apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
      funext x
      exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos x).le))
    rw [sLocalRadialMellinIntegral, hμ, e.measurableEmbedding.integral_map, mellin, ← integral_comp_exp]
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    let u : Jₛ := QuotientGroup.mk (τ (e x))
    change _ = φω((1 : PontryaginDual J₁)) g.val u * (1 * (normℝ(mₛ u) : ℂ) ^ z)
    rw [hg, show mₛ u = e x from hτ _, one_mul]
    change _ = φ.val (Real.log (Real.exp x)) * (Real.exp x : ℂ) ^ z
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
    simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    rw [mul_comm (φ.val x)]
    congr 2
    ring
  · refine Eq.trans ?_ (sLocalIdelicZFunction_eq_integral (A g).val ⟨χ, z, hz, rfl⟩).symm
    unfold sLocalIdelicZetaIntegral
    apply integral_congr_ae (.of_forall fun u ↦ ?_)
    rw [hA g u]
    let x : Jₛ := QuotientGroup.mk u
    change g.val _ * (1 * (normℝ(mₛ x) : ℂ) ^ z) =
      (((χ x)⁻¹ : Circle) : ℂ) * g.val _ * ((χ x : ℂ) * (normℝ(mₛ x) : ℂ) ^ z)
    rw [Circle.coe_inv, one_mul]
    field_simp [Circle.coe_ne_zero]

/-- The finite Euler denominators used to estimate a pole-free remainder have imaginary
periods. This is the periodicity calculation of §5.3, `finiteEulerInverse_periodic`. -/
private theorem sLocalZetaPair_first_component_attained_euler
    (η : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)) :
    let D := fun z ↦ (finiteHeckeEulerFactor η v z)⁻¹
    Differentiable ℂ D ∧ (∃ z, D z ≠ 0) ∧ ∃ T : ℝ, 0 < T ∧ Periodic D ((T : ℂ) * Complex.I) := by
  classical
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hq).ne'
  let T := 2 * Real.pi / Real.log q
  have hT : (q : ℂ) ^ ((T : ℂ) * Complex.I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hq₀, ← Complex.ofReal_log (zero_lt_one.trans hq).le]
    have h : (Real.log q : ℂ) * ((T : ℂ) * Complex.I) = 2 * Real.pi * Complex.I := by
      dsimp [T]
      push_cast
      field_simp [(Real.log_pos hq).ne']
    rw [h, Complex.exp_two_pi_mul_I]
  dsimp only
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp only [inv_inv]
    let c := (ideleClassNormTwist η 0).localValue v
    change Differentiable ℂ (fun z : ℂ ↦ 1 - c * (q : ℂ) ^ (-z)) ∧ _
    refine ⟨((differentiable_neg.const_cpow (Or.inl hq₀)).const_mul c).const_sub 1,
      ⟨1, ?_⟩, T, div_pos (by positivity) (Real.log_pos hq), fun z ↦ ?_⟩
    · apply sub_ne_zero.mpr
      intro he
      have hn := congrArg norm he
      change ‖(1 : ℂ)‖ = ‖c * (q : ℂ) ^ (-(1 : ℂ))‖ at hn
      rw [norm_one, norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
        Complex.cpow_neg, Complex.cpow_one, norm_inv, Complex.norm_real, Real.norm_of_nonneg (zero_lt_one.trans hq).le] at hn
      exact (inv_lt_one_of_one_lt₀ hq).ne' hn
    · change 1 - c * (q : ℂ) ^ (-(z + _)) = 1 - c * (q : ℂ) ^ (-z)
      rw [neg_add, Complex.cpow_add _ _ hq₀, Complex.cpow_neg _ ((T : ℂ) * Complex.I), hT, inv_one, mul_one]
  · simp only [inv_one]
    exact ⟨differentiable_const _, ⟨0, one_ne_zero⟩, 1, zero_lt_one, fun _ ↦ rfl⟩

/-- At large height on the left of the critical line, clearing the finite Euler
denominators bounds the Tate factor. The reflected gamma ratio has nonpositive
growth exponent there. The estimate holds away from its discrete exceptional set. -/
private theorem sLocalZetaPair_first_component_attained_cleared_bound
    (χ : PontryaginDual Jₛ) (η : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hr : ideleClassNormTwist η 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist η 0, hr⟩ = normChart(χ) 0) (a : ℝ) :
    ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ᶠ z in codiscrete ℂ, z.re ∈ Icc a (1 / 2) → T ≤ |z.im| →
      ‖(∏ v : S, (finiteHeckeEulerFactor η v.val z)⁻¹) * ρₛ(χ, z)‖ ≤ C := by
  obtain ⟨A, T, hA, _, hΓ⟩ := heckeGamma_reflection_bound η⁻¹ (1 / 2) (1 - a)
  obtain ⟨E, hE, hε⟩ := rhoGrowth_epsilon_bound χ a (1 / 2)
  obtain ⟨B, hB, hD⟩ := rhoGrowth_finite_bound (S := S) η⁻¹ (1 / 2) (by norm_num)
  refine ⟨E * A * B, by positivity, max T 1, ?_⟩
  filter_upwards [sLocalRhoFactor_eq_epsilon_mul χ] with z hρ
  intro hz ht
  have hre : (1 - z).re = 1 - z.re := by simp
  have him : |(1 - z).im| = |z.im| := by simp
  have hw : 1 / 2 ≤ (1 - z).re := by rw [hre]; linarith [hz.2]
  have hg := hΓ (1 - z) hw (by rw [hre]; linarith [hz.1]) (him ▸ (le_max_left _ _).trans ht)
  rw [inv_inv, sub_sub_cancel, him] at hg
  have hb := hg.trans (mul_le_of_le_one_right hA.le (Real.rpow_le_one_of_one_le_of_nonpos
    ((le_max_right _ _).trans ht) (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr hw))))
  dsimp only at hρ
  rw [sLocalNormTwistChart_dual, sLocalHeckeL_eq_partialEulerProduct χ η hr he,
    rhoGrowth_dual_lift χ η hr he, mul_div_mul_comm] at hρ
  rw [Finset.prod_inv_distrib, hρ]
  by_cases hzero : (∏ v : S, finiteHeckeEulerFactor η v.val z) = 0
  · simp only [hzero, inv_zero, zero_mul, norm_zero]
    positivity
  · rw [show (∏ v : S, finiteHeckeEulerFactor η v.val z)⁻¹ * _ =
        sLocalEpsilonFactor (normChart(χ) z) *
          (heckeGammaFactor η z / heckeGammaFactor η⁻¹ (1 - z)) *
          (∏ v : S, finiteHeckeEulerFactor η⁻¹ v.val (1 - z))⁻¹ by
        simp only [div_eq_mul_inv]; field_simp [hzero]]
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hε z hz) hb (norm_nonneg _) hE) (hD _ hw).2
      (norm_nonneg _) (mul_nonneg hE hA.le)

/-- An entire continuation of a matching pair decays rapidly even on strips crossing
the poles of the Tate factor. Estimate the cleared product, then divide out each
periodic denominator by the maximum modulus principle of §5.3. -/
private theorem sLocalZetaPair_first_component_attained_strips (χ : PontryaginDual Jₛ)
    (p : B⁺ × B⁻) (H : ℂ → ℂ) (hd : Differentiable ℂ H) (hR : EqOn H p.1.val rightHalf)
    (hL : ∀ z ∈ leftHalf, H =ᶠ[𝓝[≠] z] fun w ↦ ρₛ(χ, w) * p.2.val w) :
    H ∈ schwartzBergmanSubmodule univ := by
  classical
  obtain ⟨η, hr, he, _⟩ := sLocal_character_extension χ
  let D (v : S) (z : ℂ) := (finiteHeckeEulerFactor η v.val z)⁻¹
  have hD (v : S) := sLocalZetaPair_first_component_attained_euler η v.val
  apply schwartzBergman_of_periodic_prod (Finset.univ : Finset S) D hd (fun v _ ↦ hD v)
  have hprod : Differentiable ℂ (fun z ↦ ∏ v : S, D v z) :=
    Differentiable.fun_finsetProd fun v _ ↦ (hD v).1
  refine ⟨fun z hz ↦ (hz trivial).elim, (hprod.mul hd).differentiableOn, ?_⟩
  intro a b hab _ N
  obtain ⟨C, hC, T, hleft⟩ := sLocalZetaPair_first_component_attained_cleared_bound χ η hr he (min a 0 - 1)
  obtain ⟨B, hB, hpos⟩ := rhoGrowth_finite_bound (S := S) η (1 / 3) (by norm_num)
  obtain ⟨P, hP⟩ := p.1.property.2.2 (1 / 3) (max b 1) (by linarith [le_max_right b 1])
    (fun x hx ↦ lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hx.1) N
  obtain ⟨Q, hQ⟩ := p.2.property.2.2 (min a 0 - 1) (1 / 2) (by linarith [min_le_right a 0])
    (fun x hx ↦ lt_of_le_of_lt hx.2 (by norm_num : (1 : ℝ) / 2 < 1)) N
  let W (z : ℂ) := z ^ N * ((∏ v : S, D v z) * H z)
  have hc : Continuous W := (continuous_id.pow N).mul (hprod.continuous.mul hd.continuous)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b) |>.reProdIm
    (isCompact_Icc (a := -T) (b := T))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M (max (B * max P 0) (C * max Q 0)), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖W z‖ ≤ _
  by_cases ht : |z.im| ≤ T
  · exact (hM z ⟨hz, abs_le.mp ht⟩).trans (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  by_cases hx : 1 / 3 ≤ z.re
  · apply le_trans _ (le_max_left _ _)
    have hPz := hP (mem_image_of_mem _ (show z ∈ Complex.re ⁻¹' Icc (1 / 3) (max b 1) from
      ⟨hx, hz.2.trans (le_max_left _ _)⟩))
    have hDz := (hpos z hx).2
    rw [← Finset.prod_inv_distrib] at hDz
    change ‖z ^ N * ((∏ v : S, D v z) * H z)‖ ≤ _
    rw [mul_left_comm, hR (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hx), norm_mul]
    exact mul_le_mul hDz (hPz.trans (le_max_left _ _)) (norm_nonneg _) (by linarith)
  · apply le_trans _ (le_max_right _ _)
    have hzL : z ∈ leftHalf := lt_trans (lt_of_not_ge hx) (by norm_num)
    have hnear : ∀ᶠ w in 𝓝 z, min a 0 - 1 < w.re ∧ w.re < 1 / 2 ∧ T < |w.im| := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show min a 0 - 1 < z.re by linarith [min_le_left a 0, hz.1]),
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show z.re < 1 / 2 by linarith [lt_of_not_ge hx]),
        (isOpen_lt continuous_const Complex.continuous_im.abs).mem_nhds (lt_of_not_ge ht)]
        with w h₁ h₂ h₃ using ⟨h₁, h₂, h₃⟩
    apply le_of_tendsto (hc.norm.continuousAt.continuousWithinAt (s := {z}ᶜ))
    filter_upwards [nhdsNE_le_codiscrete z hleft, hL z hzL, nhdsWithin_le_nhds hnear] with w h hw hstrip
    have hs : w.re ∈ Icc (min a 0 - 1) (1 / 2) := ⟨hstrip.1.le, hstrip.2.1.le⟩
    have hQw := hQ (mem_image_of_mem _ (show w ∈ Complex.re ⁻¹' Icc (min a 0 - 1) (1 / 2) from hs))
    change ‖w ^ N * ((∏ v : S, D v w) * H w)‖ ≤ _
    rw [hw, show w ^ N * ((∏ v : S, D v w) * (ρₛ(χ, w) * p.2.val w)) =
      ((∏ v : S, D v w) * ρₛ(χ, w)) * (w ^ N * p.2.val w) by ring, norm_mul]
    exact mul_le_mul (h hs hstrip.2.2.le) (hQw.trans (le_max_left _ _)) (norm_nonneg _) hC

/-- Glue the right component to the corrected left component. Removing the poles in
meromorphic normal form produces an entire function with the original right restriction. -/
private theorem sLocalZetaPair_first_component_attained_remove_poles (χ : PontryaginDual Jₛ)
    (p : B⁺ × B⁻) (hp : p ∈ sLocalZetaMatching (F := F) (S := S) χ)
    (hord : ∀ z : ℂ, z ∈ leftHalf →
      0 ≤ meromorphicOrderAt (fun w ↦ ρₛ(χ, w) * p.2.val w) z) :
    ∃ H : SchwartzBergman univ, EqOn H.val p.1.val rightHalf := by
  classical
  let L := fun w ↦ ρₛ(χ, w) * p.2.val w
  let G := (rightHalf).piecewise p.1.val L
  have hright : IsOpen rightHalf := isOpen_Ioi.preimage Complex.continuous_re
  have hleft : IsOpen leftHalf := isOpen_Iio.preimage Complex.continuous_re
  have hR {z : ℂ} (hz : z ∈ rightHalf) : G =ᶠ[𝓝 z] p.1.val :=
    Filter.eventually_of_mem (hright.mem_nhds hz) fun _ hw ↦ piecewise_eq_of_mem _ _ _ hw
  have hL {z : ℂ} (hz : z ∈ leftHalf) : G =ᶠ[𝓝 z] L := by
    filter_upwards [hleft.mem_nhds hz] with w hw
    by_cases hw' : w ∈ rightHalf
    · exact (piecewise_eq_of_mem _ _ _ hw').trans ((mem_sLocalZetaMatching χ p).mp hp ⟨hw', hw⟩)
    · exact piecewise_eq_of_notMem _ _ _ hw'
  have ha := p.1.property.2.1.analyticOnNhd hright
  have hb := p.2.property.2.1.analyticOnNhd hleft
  have hρ := sLocalRhoFactor_meromorphic χ
  have hm : MeromorphicOn G univ := by
    intro z _
    by_cases hz : 0 < z.re
    · exact (ha z hz).meromorphicAt.congr ((hR hz).symm.filter_mono nhdsWithin_le_nhds)
    · have hz' : z ∈ leftHalf := lt_of_le_of_lt (le_of_not_gt hz) zero_lt_one
      exact ((hρ z).mul (hb z hz').meromorphicAt).congr ((hL hz').filter_mono nhdsWithin_le_nhds).symm
  let H := toMeromorphicNFOn G univ
  have hHG (z : ℂ) : H =ᶠ[𝓝[≠] z] G := hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have hH (z : ℂ) : AnalyticAt ℂ H z := by
    apply (meromorphicNFOn_toMeromorphicNFOn G univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_congr (hHG z)]
    by_cases hz : 0 < z.re
    · rw [meromorphicOrderAt_congr ((hR hz).filter_mono nhdsWithin_le_nhds)]
      exact (ha z hz).meromorphicOrderAt_nonneg
    · have hz' : z ∈ leftHalf := lt_of_le_of_lt (le_of_not_gt hz) zero_lt_one
      rw [meromorphicOrderAt_congr ((hL hz').filter_mono nhdsWithin_le_nhds)]
      exact hord z hz'
  have hHR : EqOn H p.1.val rightHalf := by
    intro z hz
    exact (((hH z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (ha z hz).continuousAt).mp ((hHG z).trans ((hR hz).filter_mono nhdsWithin_le_nhds))).eq_of_nhds
  exact ⟨⟨H, sLocalZetaPair_first_component_attained_strips χ p H (fun z ↦ (hH z).differentiableAt)
    hHR (fun z hz ↦ (hHG z).trans ((hL hz).filter_mono nhdsWithin_le_nhds))⟩, hHR⟩

/-- Outside a compact transition interval, each weighted smooth cutoff is either zero
or a decaying exponential. All its derivatives are bounded. -/
private theorem sLocalZetaPair_first_component_attained_cutoff (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (t : ℝ)
    (htail : ∀ x ∉ Icc (0 : ℝ) 1, θ =ᶠ[𝓝 x] (fun _ ↦ 0) ∨
      (θ =ᶠ[𝓝 x] (fun _ ↦ 1) ∧ t * x ≤ 0)) :
    (fun x ↦ Real.exp (t * x) * θ x).HasTemperateGrowth := by
  let h (x : ℝ) := Real.exp (t * x) * θ x
  have hd : ContDiff ℝ (⊤ : ℕ∞) h := ((contDiff_const.mul contDiff_id).exp).mul hθ
  refine ⟨hd, fun n ↦ ?_⟩
  obtain ⟨C, hC⟩ := isCompact_Icc (a := (0 : ℝ)) (b := 1) |>.exists_bound_of_continuousOn
    (hd.continuous_iteratedFDeriv (m := n) (by simp)).continuousOn
  refine ⟨0, max C (|t| ^ n), fun x ↦ ?_⟩
  simp only [pow_zero, mul_one]
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hC x hx).trans (le_max_left _ _)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply le_trans _ (le_max_right _ _)
  rcases htail x hx with hzero | ⟨hone, htx⟩
  · have hh : h =ᶠ[𝓝 x] (fun _ ↦ 0) := hzero.mono fun y hy ↦ by simp [h, hy]
    rw [hh.iteratedDeriv_eq n]
    change ‖iteratedDeriv n (0 : ℝ → ℝ) x‖ ≤ _
    rw [iteratedDeriv_const_zero, norm_zero]
    positivity
  · have hh : h =ᶠ[𝓝 x] (fun y ↦ Real.exp (t*y)) := hone.mono fun y hy ↦ by simp [h, hy]
    rw [hh.iteratedDeriv_eq n, iteratedDeriv_exp_const_mul, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr htx)

/-- Split the inverse Mellin profile by a smooth partition of unity in log norm.
The negative tail has all positive weights and the positive tail has all weights below one. -/
private theorem sLocalZetaPair_first_component_attained_strip_split (b : B⁰) :
    ∃ (u : B⁺) (v : B⁻), EqOn b.val (fun z ↦ u.val z + v.val z) overlap := by
  let M := positiveRealFourierMellin overlapInterval isOpen_Ioo ordConnected_Ioo
    (Set.nonempty_Ioo.mpr zero_lt_one)
  let p := M.symm b
  let θ := Real.smoothTransition
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := Real.smoothTransition.contDiff
  have hweights (I : Set ℝ) (k : ℝ → ℝ) (hk : ∀ a ∈ I, ∃ d ∈ overlapInterval,
      (fun x ↦ Real.exp ((a - d) * x) * k x).HasTemperateGrowth) :
      (fun x ↦ (k x : ℂ) * p.val x) ∈ logExponentialDecaySubmodule I := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    obtain ⟨d, hd, hkd⟩ := hk a a.property
    let w := fun x : ℝ ↦ ((Real.exp ((a.val - d) * x) * k x : ℝ) : ℂ)
    have hw : w.HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.comp hkd
    let g := logExponentialDecayTwist overlapInterval ⟨d, hd⟩ p
    refine ⟨SchwartzMap.smulLeftCLM ℂ w g, funext fun x ↦ ?_⟩
    change SchwartzMap.smulLeftCLM ℂ w g x = (Real.exp (a.val * x) : ℂ) * ((k x : ℂ) * p.val x)
    rw [SchwartzMap.smulLeftCLM_apply_apply hw, smul_eq_mul,
      show g x = _ from logExponentialDecayTwist_apply overlapInterval ⟨d, hd⟩ p x]
    dsimp only [w]
    push_cast
    rw [show (a.val : ℂ) * x = ((a.val : ℂ) - d) * x + d * x by ring, Complex.exp_add]
    ring
  have hneg (x : ℝ) (hx : x < 0) : θ =ᶠ[𝓝 x] (fun _ ↦ 0) :=
    (eventually_lt_nhds hx).mono fun _ hy ↦ Real.smoothTransition.zero_of_nonpos hy.le
  have hpos (x : ℝ) (hx : 1 < x) : θ =ᶠ[𝓝 x] (fun _ ↦ 1) :=
    (eventually_gt_nhds hx).mono fun _ hy ↦ Real.smoothTransition.one_of_one_le hy.le
  let r : PositiveRealExponentialDecay rightInterval := ⟨_, hweights rightInterval (fun x ↦ 1 - θ x) (by
    intro a ha
    let d := min a (1 / 2)
    have hd : d ∈ overlapInterval := ⟨lt_min ha (by norm_num), (min_le_right ..).trans_lt (by norm_num)⟩
    refine ⟨d, hd, sLocalZetaPair_first_component_attained_cutoff _ (contDiff_const.sub hθ) _ ?_⟩
    intro x hx
    rcases not_and_or.mp hx with h | h
    · have h' := lt_of_not_ge h
      exact Or.inr ⟨(hneg x h').mono (fun y hy ↦ by simp [hy]),
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (min_le_left ..)) h'.le⟩
    · exact Or.inl ((hpos x (lt_of_not_ge h)).mono fun y hy ↦ by simp [hy]))⟩
  let l : PositiveRealExponentialDecay leftInterval := ⟨_, hweights leftInterval θ (by
    intro a ha
    let d := max a (1 / 2)
    have hd : d ∈ overlapInterval := ⟨lt_of_lt_of_le (by norm_num) (le_max_right ..), max_lt ha (by norm_num)⟩
    refine ⟨d, hd, sLocalZetaPair_first_component_attained_cutoff _ hθ _ ?_⟩
    intro x hx
    rcases not_and_or.mp hx with h | h
    · exact Or.inl (hneg x (lt_of_not_ge h))
    · have h' := lt_of_not_ge h
      exact Or.inr ⟨hpos x h', mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_max_left ..)) (zero_le_one.trans h'.le)⟩)⟩
  let U := positiveRealFourierMellin rightInterval isOpen_Ioi ordConnected_Ioi (nonempty_Ioi)
  let V := positiveRealFourierMellin leftInterval isOpen_Iio ordConnected_Iio (nonempty_Iio)
  refine ⟨U r, V l, fun z hz ↦ ?_⟩
  have hM := positiveRealFourierMellin_apply overlapInterval isOpen_Ioo ordConnected_Ioo
    (Set.nonempty_Ioo.mpr zero_lt_one) p z hz
  change (M p).val z = _ at hM
  rw [M.apply_symm_apply b] at hM
  have hs := (hasMellin_add (positiveRealExponentialDecay_mellinConvergent rightInterval r z hz.1)
    (positiveRealExponentialDecay_mellinConvergent leftInterval l z hz.2)).2
  have hsum (x : ℝ) : p.val x = r.val x + l.val x := by
    change _ = ((1 - θ x : ℝ) : ℂ) * p.val x + (θ x : ℂ) * p.val x
    push_cast
    ring
  exact hM.trans ((congrArg (fun f ↦ mellin f z) (funext fun t ↦ hsum (Real.log t))).trans
    (hs.trans (congrArg₂ (· + ·) (positiveRealFourierMellin_apply _ _ _ _ r z hz.1).symm
      (positiveRealFourierMellin_apply _ _ _ _ l z hz.2).symm)))

/-- A bounded entire multiplier without small values on closed positive strips allows
one to interpolate left data modulo that multiplier. Split the quotient on the overlap,
multiply both pieces back, and glue the two expressions for the interpolant. -/
private theorem sLocalZetaPair_first_component_attained_interpolate (b : B⁻) (D : ℂ → ℂ)
    (hd : Differentiable ℂ D) (hB : ∀ a c : ℝ, ∃ M ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a c → ‖D z‖ ≤ M)
    (hm : ∀ a c : ℝ, 0 < a → ∃ m > (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a c → m ≤ ‖D z‖) :
    ∃ (G : SchwartzBergman univ) (v : B⁻),
      EqOn (fun z ↦ b.val z - G.val z) (fun z ↦ D z * v.val z) leftHalf := by
  classical
  have hn {z : ℂ} (hz : 0 < z.re) : D z ≠ 0 := by
    obtain ⟨m, hm₀, h⟩ := hm z.re z.re hz
    exact norm_pos_iff.mp (hm₀.trans_le (h z ⟨le_rfl, le_rfl⟩))
  obtain ⟨Q, hQ⟩ := existsUnique_sLocalZetaMatchingDifference_multiplier leftInterval
    (fun _ hz ↦ hz.2) (fun z ↦ (D z)⁻¹) (hd.differentiableOn.inv (fun _ hz ↦ hn hz.1)) (by
      intro a c hac hsub
      obtain ⟨m, hm₀, h⟩ := hm a c (hsub (left_mem_Icc.mpr hac)).1
      exact ⟨m⁻¹, inv_nonneg.mpr hm₀.le, 0, fun z hz ↦ by
        simpa only [norm_inv, pow_zero, mul_one] using inv_anti₀ hm₀ (h z hz)⟩)
  obtain ⟨u, v, huv⟩ := sLocalZetaPair_first_component_attained_strip_split (Q b)
  have mult {I : Set ℝ} (f : SchwartzBergman I) :
      (fun z ↦ D z * f.val z) ∈ schwartzBergmanSubmodule I := by
    refine ⟨fun z hz ↦ by change D z * f.val z = 0; rw [f.property.1 hz]; exact mul_zero _, hd.differentiableOn.mul f.property.2.1, ?_⟩
    intro a c hac hsub N
    obtain ⟨A, hA, hD⟩ := hB a c
    obtain ⟨B, h⟩ := f.property.2.2 a c hac hsub N
    refine ⟨A * max B 0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ N * (D z * f.val z)‖ ≤ _
    rw [mul_left_comm, norm_mul]
    exact mul_le_mul (hD z hz) ((h ⟨z, hz, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _) hA
  let R : B⁺ := ⟨_, mult u⟩
  let V : B⁻ := ⟨_, mult v⟩
  let L : B⁻ := b - V
  have hmatch : EqOn R.val L.val overlap := by
    intro z hz
    have h : (D z)⁻¹ * b.val z = u.val z + v.val z := ((hQ b hz).symm.trans (huv hz))
    change D z * u.val z = b.val z - D z * v.val z
    have := congrArg (D z * ·) h
    rw [mul_inv_cancel_left₀ (hn hz.1), mul_add] at this
    exact eq_sub_of_add_eq this.symm
  let G := (rightHalf).piecewise R.val L.val
  have hR : EqOn G R.val rightHalf := fun z hz ↦ piecewise_eq_of_mem _ _ _ hz
  have hL : EqOn G L.val leftHalf := by
    intro z hz
    by_cases hr : z ∈ rightHalf
    · exact (hR hr).trans (hmatch ⟨hr, hz⟩)
    · exact piecewise_eq_of_notMem _ _ _ hr
  have hdiff : Differentiable ℂ G := by
    intro z
    by_cases hr : z ∈ rightHalf
    · exact ((R.property.2.1 z hr).differentiableAt ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hr)).congr_of_eventuallyEq
        (eventuallyEq_of_mem ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hr) hR)
    · have hl : z ∈ leftHalf := lt_of_le_of_lt (not_lt.mp hr) zero_lt_one
      exact ((L.property.2.1 z hl).differentiableAt ((isOpen_Iio.preimage Complex.continuous_re).mem_nhds hl)).congr_of_eventuallyEq
        (eventuallyEq_of_mem ((isOpen_Iio.preimage Complex.continuous_re).mem_nhds hl) hL)
  have hG : G ∈ schwartzBergmanSubmodule univ := by
    refine ⟨fun _ hz ↦ (hz trivial).elim, hdiff.differentiableOn, ?_⟩
    intro a c _ _ N
    obtain ⟨A, hA⟩ := R.property.2.2 (1 / 2) (max c 1) (by linarith [le_max_right c 1])
      (fun _ h ↦ lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) h.1) N
    obtain ⟨B, hB'⟩ := L.property.2.2 (min a 0) (1 / 2) (by linarith [min_le_right a 0])
      (fun _ h ↦ h.2.trans_lt (by norm_num : (1 : ℝ) / 2 < 1)) N
    refine ⟨max A B, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ N * G z‖ ≤ _
    by_cases h : 1 / 2 ≤ z.re
    · rw [hR (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) h)]
      exact (hA ⟨z, ⟨h, hz.2.trans (le_max_left _ _)⟩, rfl⟩).trans (le_max_left _ _)
    · rw [hL ((lt_of_not_ge h).trans (by norm_num : (1 : ℝ) / 2 < 1))]
      exact (hB' ⟨z, ⟨(min_le_left _ _).trans hz.1, (lt_of_not_ge h).le⟩, rfl⟩).trans (le_max_right _ _)
  refine ⟨⟨G, hG⟩, v, fun z hz ↦ ?_⟩
  change b.val z - G z = D z * v.val z
  rw [hL hz]
  exact sub_sub_cancel _ _

/-- At every nonpositive integer the gamma recurrence removes the pole after
multiplication by the local coordinate. -/
private theorem sLocalZetaPair_first_component_attained_gamma_germ (n : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (-(n : ℂ)) ∧
      (fun z : ℂ ↦ (z + n) * Complex.Gamma z) =ᶠ[𝓝[≠] (-(n : ℂ))] g := by
  have hΓ (z : ℂ) (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gamma z := by
    have h := Complex.differentiable_one_div_Gamma.analyticAt z
    change AnalyticAt ℂ (Complex.Gamma)⁻¹ z at h
    simpa only [inv_inv] using h.inv (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hz))
  induction n with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, add_zero]
    refine ⟨fun z ↦ Complex.Gamma (z + 1), (hΓ 1 (by simp)).comp_of_eq (f := fun w : ℂ ↦ w + 1) (by fun_prop) (by simp), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw using (Complex.Gamma_add_one w hw).symm
  | succ n ih =>
    obtain ⟨g, hg, he⟩ := ih
    let z : ℂ := -((n + 1 : ℕ) : ℂ)
    have hz : z ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
    have hs : z + 1 = -(n : ℂ) := by dsimp [z]; push_cast; ring
    have ht : Tendsto (fun w : ℂ ↦ w + 1) (𝓝[≠] z) (𝓝[≠] (-(n : ℂ))) := by
      rw [← hs]
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuousAt_id.add continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw using fun eq ↦ hw (add_right_cancel eq)
    refine ⟨fun w ↦ g (w + 1) / w, (hg.comp_of_eq (f := fun w : ℂ ↦ w + 1) (by fun_prop) hs).div analyticAt_id hz, ?_⟩
    filter_upwards [ht.eventually he, nhdsWithin_le_nhds (eventually_ne_nhds hz)] with w hw hw₀
    change (w + 1 + (n : ℂ)) * Complex.Gamma (w + 1) = g (w + 1) at hw
    rw [← hw, Complex.Gamma_add_one _ hw₀]
    push_cast
    field_simp
    ring

/-- The entire function `1/Γ(1-2⁻ᵘ)` clears every gamma pole. At `u = -n` its
argument is the nonpositive integer `1-2ⁿ`. In the positive half-plane `|2⁻ᵘ| < 1`,
so it has no zeros there. Its imaginary period supplies bounds on vertical strips. -/
private theorem sLocalZetaPair_first_component_attained_gamma_multiplier :
    ∃ d W : ℂ → ℂ, Differentiable ℂ d ∧ Differentiable ℂ W ∧
      (∃ T : ℝ, 0 < T ∧ Periodic d ((T : ℂ) * Complex.I)) ∧
      (∀ z : ℂ, 0 < z.re → d z ≠ 0 ∧ d z * Complex.Gamma z = W z) := by
  let d (z : ℂ) := (Complex.Gamma (1 - (2 : ℂ) ^ (-z)))⁻¹
  have hd : Differentiable ℂ d := Complex.differentiable_one_div_Gamma.comp
    ((differentiable_neg.const_cpow (Or.inl (two_ne_zero : (2 : ℂ) ≠ 0))).const_sub 1)
  have hΓ (z : ℂ) : MeromorphicAt Complex.Gamma z := by
    have hh : MeromorphicAt (Complex.Gamma)⁻¹ z := (Complex.differentiable_one_div_Gamma.analyticAt z).meromorphicAt
    simpa only [inv_inv] using hh.inv
  let P (z : ℂ) := d z * Complex.Gamma z
  have hm : MeromorphicOn P univ := fun z _ ↦ (hd.analyticAt z).meromorphicAt.mul (hΓ z)
  let W := toMeromorphicNFOn P univ
  have hreg (z : ℂ) (hz : Complex.Gamma z ≠ 0) : AnalyticAt ℂ P z := by
    have hh : AnalyticAt ℂ (Complex.Gamma)⁻¹ z := Complex.differentiable_one_div_Gamma.analyticAt z
    exact (hd.analyticAt z).mul (by simpa only [inv_inv] using hh.inv (inv_ne_zero hz))
  have hW (z : ℂ) : AnalyticAt ℂ W z := by
    apply (meromorphicNFOn_toMeromorphicNFOn P univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ z)]
    by_cases hz : Complex.Gamma z ≠ 0
    · exact (hreg z hz).meromorphicOrderAt_nonneg
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, z = -n := by
      by_contra! h
      exact hz (Complex.Gamma_ne_zero h)
    have hdz : d (-(n : ℂ)) = 0 := by
      have hpow : (1 : ℂ) - (2 : ℂ) ^ n = -((2^n - 1 : ℕ) : ℂ) := by
        rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
        push_cast
        ring
      simp only [d, neg_neg, Complex.cpow_natCast, hpow, Complex.Gamma_neg_nat_eq_zero, inv_zero]
    obtain ⟨g, hg, he⟩ := sLocalZetaPair_first_component_attained_gamma_germ n
    apply (hm _ trivial).meromorphicOrderAt_nonneg_iff.mpr
    refine ⟨fun w ↦ dslope d (-(n : ℂ)) w * g w, ((hd.analyticAt _).dslope _).mul hg, ?_⟩
    filter_upwards [he] with w hw
    have h₁ := sub_smul_dslope_of_zero hdz w
    rw [smul_eq_mul, sub_neg_eq_add] at h₁
    change d w * Complex.Gamma w = _
    rw [← hw, ← h₁]
    ring
  let T := 2 * Real.pi / Real.log 2
  have hper : (2 : ℂ)^((T : ℂ) * Complex.I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero two_ne_zero]
    rw [show Complex.log 2 = (Real.log 2 : ℂ) from (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm]
    dsimp [T]
    push_cast
    rw [show (Real.log 2 : ℂ) * (2 * (Real.pi : ℂ) / Real.log 2 * Complex.I) =
      2 * Real.pi * Complex.I by
        field_simp
        exact div_self (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne')]
    exact Complex.exp_two_pi_mul_I
  refine ⟨d, W, hd, fun z ↦ (hW z).differentiableAt,
    ⟨T, div_pos (by positivity) (Real.log_pos (by norm_num)), fun z ↦ ?_⟩, fun z hz ↦ ⟨?_, ?_⟩⟩
  · simp only [d, neg_add, Complex.cpow_add _ _ (two_ne_zero : (2 : ℂ) ≠ 0),
      Complex.cpow_neg _ ((T : ℂ) * Complex.I), hper, inv_one, mul_one]
  · apply inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos ?_)
    have hnorm : ‖(2 : ℂ) ^ (-z)‖ < 1 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hz)
    rw [Complex.sub_re, Complex.one_re]
    exact sub_pos.mpr ((Complex.re_le_norm _).trans_lt hnorm)
  · exact (((hW z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hreg z (Complex.Gamma_ne_zero_of_re_pos hz)).continuousAt).mp
      (hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z))).eq_of_nhds.symm

/-- Rescale the gamma multiplier for the affine argument of a real or complex Euler factor. -/
private theorem sLocalZetaPair_first_component_attained_arch_factor
    (L : ℂ → ℂ) (b : ℂ) (hb : 0 ≤ b.re) (k c : ℝ) (hk : 0 < k) (hc : 0 < c)
    (hL : ∀ z : ℂ, L z = (c : ℂ) ^ (-((z + b) / k)) * Complex.Gamma ((z + b) / k)) :
    ∃ D W : ℂ → ℂ, Differentiable ℂ D ∧ Differentiable ℂ W ∧
      (∃ T : ℝ, 0 < T ∧ Periodic D ((T : ℂ) * Complex.I)) ∧
      ∀ z : ℂ, 0 < z.re → D z ≠ 0 ∧ D z * L z = W z := by
  obtain ⟨d, w, hd, hw, ⟨T, hT, hper⟩, h⟩ := sLocalZetaPair_first_component_attained_gamma_multiplier
  let u (z : ℂ) := (z + b) / (k : ℂ)
  have hu : Differentiable ℂ u := (differentiable_id.add_const b).div_const _
  let P (z : ℂ) := (c : ℂ) ^ (-u z)
  have hP : Differentiable ℂ P := hu.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  refine ⟨d ∘ u, fun z ↦ P z * w (u z), hd.comp hu, hP.mul (hw.comp hu),
    ⟨k * T, mul_pos hk hT, fun z ↦ ?_⟩, fun z hz ↦ ?_⟩
  · have he : u (z + ((k * T : ℝ) : ℂ) * Complex.I) = u z + (T : ℂ) * Complex.I := by
      dsimp [u]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hk.ne']
      ring
    exact (congrArg d he).trans (hper (u z))
  · have hpos : 0 < (u z).re := by
      simpa only [u, Complex.div_ofReal_re, Complex.add_re] using div_pos (add_pos_of_pos_of_nonneg hz hb) hk
    refine ⟨(h _ hpos).1, ?_⟩
    change d (u z) * L z = P z * w (u z)
    rw [hL, ← (h _ hpos).2, mul_left_comm]

/-- Bounds for a single periodic denominator. Above a positive abscissa, clamp the real
part before taking its reciprocal to obtain a continuous periodic function on the plane. -/
private theorem sLocalZetaPair_first_component_attained_periodic_bounds
    (D : ℂ → ℂ) (hd : Continuous D) {T : ℝ} (hT : 0 < T) (hper : Periodic D ((T : ℂ) * Complex.I))
    (hne : ∀ z : ℂ, 0 < z.re → D z ≠ 0) (a b : ℝ) :
    (∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖D z‖ ≤ C) ∧
    (0 < a → ∃ m > (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → m ≤ ‖D z‖) := by
  refine ⟨rhoGrowth_periodic_bound hT hper hd a b, fun ha ↦ ?_⟩
  let r (z : ℂ) : ℂ := ⟨max a z.re, z.im⟩
  have hc : Continuous r := by
    have he : r = fun z ↦ ((max a z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I := by
      exact funext fun z ↦ Complex.mk_eq_add_mul_I _ _
    rw [he]
    fun_prop
  have hn (z : ℂ) := hne (r z) (ha.trans_le (le_max_left _ _))
  have hp : Periodic (fun z ↦ (D (r z))⁻¹) ((T : ℂ) * Complex.I) := by
    intro z
    have he : r (z + (T : ℂ) * Complex.I) = r z + (T : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [r, Complex.add_re, Complex.add_im]
    change (D (r (z + _)))⁻¹ = _
    rw [he, hper]
  obtain ⟨C, hC, h⟩ := rhoGrowth_periodic_bound hT hp ((hd.comp hc).inv₀ hn) a b
  refine ⟨(max C 1)⁻¹, inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _)), fun z hz ↦ ?_⟩
  have he : r z = z := Complex.ext (max_eq_right hz.1) rfl
  have h' := h z hz
  change ‖(D (r z))⁻¹‖ ≤ C at h'
  rw [he, norm_inv] at h'
  simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (norm_pos_iff.mpr (hne z (ha.trans_le hz.1))))
    (h'.trans (le_max_left _ 1))

/-- Assemble the finitely many periodic multipliers and their holomorphic products
with the local Euler factors. Bounds multiply even for incommensurable periods. -/
private theorem sLocalZetaPair_first_component_attained_factor_product {ι : Type*} [Fintype ι]
    (L : ι → ℂ → ℂ) (h : ∀ i, ∃ D W : ℂ → ℂ, Differentiable ℂ D ∧ Differentiable ℂ W ∧
      (∃ T : ℝ, 0 < T ∧ Periodic D ((T : ℂ) * Complex.I)) ∧
      ∀ z : ℂ, 0 < z.re → D z ≠ 0 ∧ D z * L i z = W z) :
    ∃ D W : ℂ → ℂ, Differentiable ℂ D ∧ Differentiable ℂ W ∧
      (∀ a b : ℝ, ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖D z‖ ≤ C) ∧
      (∀ a b : ℝ, 0 < a → ∃ m > (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → m ≤ ‖D z‖) ∧
      ∀ z : ℂ, 0 < z.re → D z * ∏ i, L i z = W z := by
  classical
  choose d w hd hw hp hloc using h
  choose T hT hper using hp
  have bounds (i : ι) := sLocalZetaPair_first_component_attained_periodic_bounds (d i)
    (hd i).continuous (hT i) (hper i) (fun z hz ↦ (hloc i z hz).1)
  refine ⟨fun z ↦ ∏ i, d i z, fun z ↦ ∏ i, w i z, Differentiable.fun_finsetProd (fun i _ ↦ hd i),
    Differentiable.fun_finsetProd (fun i _ ↦ hw i), fun a b ↦ ?_, fun a b ha ↦ ?_, fun z hz ↦ ?_⟩
  · choose C hC hc using fun i ↦ (bounds i a b).1
    refine ⟨∏ i, C i, Finset.prod_nonneg (fun i _ ↦ hC i), fun z hz ↦ ?_⟩
    exact (norm_prod ..).le.trans (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hc i z hz))
  · choose m hm hlow using fun i ↦ (bounds i a b).2 ha
    refine ⟨∏ i, m i, Finset.prod_pos (fun i _ ↦ hm i), fun z hz ↦ ?_⟩
    exact (Finset.prod_le_prod₀ (fun i _ ↦ (hm i).le) (fun i _ ↦ hlow i z hz)).trans_eq (norm_prod ..).symm
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ ↦ (hloc i z hz).2)

/-- Clear the archimedean factors with the periodic gamma multipliers and the finite
factors with their Euler polynomials. The resulting multiplier is bounded on strips,
bounded away from zero on positive strips, and cancels the full pole divisor of ρ. -/
private theorem sLocalZetaPair_first_component_attained_denominator (χ : PontryaginDual Jₛ) :
    ∃ D : ℂ → ℂ, Differentiable ℂ D ∧
      (∀ a b : ℝ, ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖D z‖ ≤ C) ∧
      (∀ a b : ℝ, 0 < a → ∃ m > (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → m ≤ ‖D z‖) ∧
      ∀ z : ℂ, 0 ≤ meromorphicOrderAt (fun w ↦ ρₛ(χ, w) * D w) z := by
  classical
  obtain ⟨η, hr, he, _⟩ := sLocal_character_extension χ
  let arch (v : InfinitePlace F) (s : ℂ) :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters η v hv).exists.choose
      Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
    else
      let a := (complexHeckeCharacter_parameters η v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2
  let L : InfinitePlace F ⊕ S → ℂ → ℂ := Sum.elim arch (fun v z ↦ finiteHeckeEulerFactor η v.val z)
  obtain ⟨D, W,hd, hw, hupper, hlower, hprod⟩ := sLocalZetaPair_first_component_attained_factor_product L (by
    rintro (v | v)
    · change ∃ _ _, _ ∧ _ ∧ _ ∧ ∀ z : ℂ, 0 < z.re → _ ∧ _ * arch v z = _
      by_cases hv : v.IsReal
      · let a := (realHeckeCharacter_parameters η v hv).exists.choose
        have ha : a.1.re = 0 := (realHeckeCharacter_parameters η v hv).exists.choose_spec.1
        apply sLocalZetaPair_first_component_attained_arch_factor _ (a.1 + (a.2.val : ℂ)) (by simp [ha]) 2 Real.pi
          (by norm_num) Real.pi_pos
        intro z
        simp only [arch, dite_eq_left hv, Complex.Gammaℝ_def, a, add_assoc, neg_div, Complex.ofReal_ofNat]
      · let a := (complexHeckeCharacter_parameters η v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
        have ha : a.1.re = 0 := (complexHeckeCharacter_parameters η v _).exists.choose_spec.1
        apply sLocalZetaPair_first_component_attained_arch_factor _ (a.1 + (a.2.natAbs : ℂ) / 2) (by simp [ha]; positivity) 1 (2 * Real.pi)
          zero_lt_one (by positivity)
        intro z
        simp [arch, hv, a, Complex.Gammaℂ_def, add_assoc]
        ring
    · let d (z : ℂ) := (finiteHeckeEulerFactor η v.val z)⁻¹
      obtain ⟨hd, _, hp⟩ := sLocalZetaPair_first_component_attained_euler η v.val
      refine ⟨d, fun _ ↦ 1, hd, differentiable_const _, hp, fun z hz ↦ ?_⟩
      suffices hn : finiteHeckeEulerFactor η v.val z ≠ 0 from ⟨inv_ne_zero hn, inv_mul_cancel₀ hn⟩
      unfold finiteHeckeEulerFactor
      split_ifs
      · refine inv_ne_zero (sub_ne_zero.mpr ?_)
        intro h
        have hh := congrArg norm h
        have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
        rw [norm_one, norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re] at hh
        exact (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr hz)).ne' hh
      · exact one_ne_zero)
  have hDL {z : ℂ} (hz : 0 < z.re) : D z * sLocalHeckeL (normChart(χ) z) = W z := by
    rw [sLocalHeckeL_eq_partialEulerProduct χ η hr he]
    change D z * ((∏ v, arch v z) * ∏ v : S, finiteHeckeEulerFactor η v.val z) = W z
    simpa only [Fintype.prod_sum_type, L, Sum.elim_inl, Sum.elim_inr] using hprod z hz
  let A := fun w ↦ D w * sLocalHeckeL (normChart(χ) w)
  have hA : Meromorphic A := by
    intro z
    apply (hd.analyticAt z).meromorphicAt.mul
    have h : MeromorphicAt (fun w ↦ sLocalHeckeL (normChart(χ) w))⁻¹ z :=
      ((sLocalHeckeL_inv_differentiable χ).analyticAt z).meromorphicAt
    simpa only [inv_inv] using h.inv
  have hΔ : MeromorphicOn (A - W) univ := fun z _ ↦ (hA z).sub (hw.analyticAt z).meromorphicAt
  have h₁ : meromorphicOrderAt (A - W) 1 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hr₁ : (1 : ℂ) ∈ rightHalf := by simp
    filter_upwards [nhdsWithin_le_nhds ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hr₁)]
      with w hw' using sub_eq_zero.mpr (hDL hw')
  refine ⟨D, hd, hupper, hlower, fun z ↦ ?_⟩
  have hnear := meromorphicOrderAt_eq_top_iff.mp (hΔ.meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ z) h₁)
  let B := fun w ↦ sLocalEpsilonFactor (normChart(χ) w) * W w *
    (sLocalHeckeL (normChart(χ⁻¹) (1 - w)))⁻¹
  have hB : AnalyticAt ℂ B z := (((sLocalEpsilonFactor_entire χ) z trivial).mul (hw.analyticAt z)).mul
    (((sLocalHeckeL_inv_differentiable χ⁻¹).analyticAt (1 - z)).comp (f := fun w : ℂ ↦ 1 - w) (by fun_prop))
  have hlocal : (fun w ↦ ρₛ(χ, w) * D w) =ᶠ[𝓝[≠] z] B := by
    filter_upwards [hnear, nhdsNE_le_codiscrete z (sLocalRhoFactor_eq_epsilon_mul χ)] with w h hρ
    have heq : D w * sLocalHeckeL (normChart(χ) w) = W w := sub_eq_zero.mp h
    dsimp only at hρ
    rw [hρ, sLocalNormTwistChart_dual]
    dsimp [B]
    rw [← heq, div_eq_mul_inv]
    ring
  rw [meromorphicOrderAt_congr hlocal]
  exact hB.meromorphicOrderAt_nonneg

/-- Interpolate the reflected Fourier datum modulo a multiplier clearing all Tate poles.
Fourier inversion of the test realizing this entire interpolant matches the principal parts
at every pole simultaneously. -/
private theorem sLocalZetaPair_first_component_attained_principal_parts (χ : PontryaginDual Jₛ)
    (p : B⁺ × B⁻) :
    ∃ f : ℬₛ, ∀ z : ℂ, z ∈ leftHalf →
      0 ≤ meromorphicOrderAt (fun w ↦ ρₛ(χ, w) * (p.2.val w -
        (sLocalZetaPair χ (Submodule.Quotient.mk f)).2.val w)) z := by
  obtain ⟨D, hd, hupper, hlower, hord⟩ := sLocalZetaPair_first_component_attained_denominator χ
  obtain ⟨G, v, hG⟩ := sLocalZetaPair_first_component_attained_interpolate p.2 D hd hupper hlower
  let R : SchwartzBergman univ := ⟨_, existsUnique_sLocalZetaPair_reflect_mem
    (I := univ) (J := univ) (fun _ ↦ iff_of_true trivial trivial) G⟩
  obtain ⟨g, hg⟩ := sLocalZetaPair_first_component_attained_entire (F := F) (S := S) χ⁻¹ R
  let f := Fourierₛ (Fourierₛ (Fourierₛ g))
  have hf : Fourierₛ f = g := by
    apply Subtype.ext
    funext x
    exact (sLocal_fourier_inversion (Fourierₛ (Fourierₛ g)) x.toAdd).trans
      ((sLocal_fourier_inversion g (-x.toAdd)).trans (congrArg (fun y ↦ g (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))
  let u := sLocalZetaPair χ (Submodule.Quotient.mk f)
  have hu : EqOn u.2.val G.val leftHalf := by
    intro z hz
    have h₁ := (sLocalZetaPair_mk χ f).2 hz
    have h₂ := hg (show 1 - z ∈ rightHalf by simpa using sub_pos.mpr hz)
    change G.val (1-(1 - z)) = _ at h₂
    rw [sub_sub_cancel] at h₂
    exact h₁.trans ((congrArg (fun h ↦ Zₛ h (normChart(χ⁻¹) (1 - z))) hf).trans h₂.symm)
  refine ⟨f, fun z hl ↦ ?_⟩
  have hloc : (fun w ↦ ρₛ(χ, w) * (p.2.val w - u.2.val w)) =ᶠ[𝓝[≠] z]
      (fun w ↦ (ρₛ(χ, w) * D w) * v.val w) := by
    filter_upwards [nhdsWithin_le_nhds ((isOpen_Iio.preimage Complex.continuous_re).mem_nhds hl)] with w hw
    have heq : p.2.val w - G.val w = D w * v.val w := hG hw
    rw [hu hw, heq, mul_assoc]
  have hv := v.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re) z hl
  rw [meromorphicOrderAt_congr hloc]
  exact (meromorphicOrderAt_mul ((sLocalRhoFactor_meromorphic χ z).mul (hd.analyticAt z).meromorphicAt)
    hv.meromorphicAt).symm ▸ add_nonneg (hord z) hv.meromorphicOrderAt_nonneg

/-- Paper: Theorem 5.4.1.1(1), p. 266. Every matching pair has its first Bergman
datum realized by an S-local test. Realize the principal parts using the reflected Fourier
datum, then lift the entire remainder by Fourier–Mellin inversion. -/
private theorem sLocalZetaPair_first_component_attained (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻)
    (_hp : p ∈ sLocalZetaMatching (F := F) (S := S) χ) :
    ∃ f : ℬₛ, EqOn p.1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf := by
  obtain ⟨f, hf⟩ := sLocalZetaPair_first_component_attained_principal_parts χ p
  let u := sLocalZetaPair χ (Submodule.Quotient.mk f)
  have hu : u ∈ sLocalZetaMatching χ := sLocalZetaPair_range_le_matching χ ⟨_, rfl⟩
  obtain ⟨H, hH⟩ := sLocalZetaPair_first_component_attained_remove_poles χ (p - u)
    ((sLocalZetaMatching χ).sub_mem _hp hu) hf
  obtain ⟨g, hg⟩ := sLocalZetaPair_first_component_attained_entire (F := F) (S := S) χ H
  refine ⟨f + g, fun z hz ↦ ?_⟩
  have hsub : p.1.val z - u.1.val z = Zₛ g (normChart(χ) z) := (hH hz).symm.trans (hg hz)
  obtain ⟨E, hE⟩ := existsUnique_sLocalZetaPair_eval χ z hz
  change p.1.val z = Zₛ (f + g) (normChart(χ) z)
  rw [← hE, show (Submodule.Quotient.mk (f + g) : Θω(restrict₁(χ))) =
    Submodule.Quotient.mk f + Submodule.Quotient.mk g from rfl, map_add, hE, hE]
  exact (sub_eq_iff_eq_add'.mp hsub).trans (congrArg (· + Zₛ g (normChart(χ) z))
    ((sLocalZetaPair_mk χ f).1 hz))

/-- Once the first Bergman datum of a matching pair is realized by a test, the pair is the
zeta pair of that test's theta class: the second component agrees with the reflected Fourier
datum on the overlap by the functional equation, hence on its whole half-plane. -/
private theorem sLocalZetaPair_mem_range_of_first (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻)
    (hp : p ∈ sLocalZetaMatching (F := F) (S := S) χ)
    (h : ∃ f : ℬₛ, EqOn p.1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf) :
    p ∈ LinearMap.range (sLocalZetaPair (F := F) (S := S) χ) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨Submodule.Quotient.mk f, ?_⟩
  obtain ⟨h₁, h₂⟩ := sLocalZetaPair_mk (F := F) (S := S) χ f
  have hmatch : EqOn p.1.val (fun s ↦ ρₛ(χ, s) * p.2.val s) overlap :=
    (mem_sLocalZetaMatching (F := F) (S := S) χ p).mp hp
  have hfirst : (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).1 = p.1 :=
    existsUnique_sLocalZetaPair_ext (I := rightInterval) (u := _) (v := p.1)
      (fun z hz ↦ (h₁ hz).trans (hf hz).symm)
  have hsecond : (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2 = p.2 :=
    existsUnique_sLocalZetaPair_left_ext χ _ p.2 (fun z hz ↦ by
      calc ρₛ(χ, z) * (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2.val z
          = ρₛ(χ, z) * Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - z)) := congrArg _ (h₂ hz.2)
        _ = Zₛ f (normChart(χ) z) := (existsUnique_sLocalZetaPair_equation χ f z hz).symm
        _ = p.1.val z := (hf hz.1).symm
        _ = ρₛ(χ, z) * p.2.val z := hmatch hz)
  exact Prod.ext hfirst hsecond

/-- Conversely, every matching pair is the zeta pair of a homogeneous theta class. -/
private theorem sLocalZetaPair_matching_le_range (χ : PontryaginDual Jₛ) :
    sLocalZetaMatching (F := F) (S := S) χ ≤
      LinearMap.range (sLocalZetaPair (F := F) (S := S) χ) :=
  fun p hp ↦
    sLocalZetaPair_mem_range_of_first (F := F) (S := S) χ p hp
      (sLocalZetaPair_first_component_attained (F := F) (S := S) χ p hp)

/-- Paper: Theorem 5.4.1.1(1), p. 266.
Every matching pair, and only a matching pair, comes from a homogeneous theta class. -/
theorem sLocalZetaPair_range (χ : PontryaginDual Jₛ) :
    (sLocalZetaPair (F := F) (S := S) χ).range = sLocalZetaMatching (F := F) (S := S) χ :=
  le_antisymm (sLocalZetaPair_range_le_matching (F := F) (S := S) χ)
    (sLocalZetaPair_matching_le_range (F := F) (S := S) χ)

/-- A norm twist of the chosen lift reaches every character with the same restriction.
This is the split-norm argument of `exists_normTwist_of_agree_on_ker` in §5.2b. -/
private theorem sLocalZetaPair_isEmbedding_chart (χ : PontryaginDual Jₛ)
    (c : QuasiCharacter Jₛ) (hc : ∀ u : J₁, c u.val = (χ u.val : ℂ)) :
    ∃ z, normChart(χ) z = c := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  let b := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  obtain ⟨u, hu, -⟩ := existsUnique_complexPower (b.comp σ)
  obtain ⟨v, hv, -⟩ := existsUnique_complexPower (c.comp σ)
  refine ⟨v - u, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  let t := mₛ x
  let y : J₁ := ⟨x / σ t, by simp [MonoidHom.mem_ker, t, hσ (mₛ x)]⟩
  have hxy : y.val * σ t = x := div_mul_cancel x _
  have split (d : QuasiCharacter Jₛ) : d x = d y.val * d (σ t) :=
    (congrArg d hxy).symm.trans (map_mul d _ _)
  change b x * (((t.val : ℝ) : ℂ)) ^ (v - u) = c x
  rw [split b, split c, show c y.val = b y.val from hc y,
    show b (σ t) = (((t.val : ℝ) : ℂ)) ^ u from hu t,
    show c (σ t) = (((t.val : ℝ) : ℂ)) ^ v from hv t, mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)),
    add_sub_cancel]

/-- Vanishing of the first component forces vanishing on the whole character component
by meromorphic uniqueness, and hence vanishing of the homogeneous theta class. -/
private theorem sLocalZetaPair_isEmbedding_injective (χ : PontryaginDual Jₛ) :
    Injective (sLocalZetaPair (F := F) (S := S) χ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  let K := LinearMap.ker (φω(restrict₁(χ)))
  obtain ⟨f, rfl⟩ := K.mkQ_surjective x
  have hz := eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f χ)
    (V := 0) (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0 (fun z h ↦
      ((sLocalZetaPair_mk χ f).1 h).symm.trans (congrArg (fun p : B⁺ × B⁻ ↦ p.1.val z) hx))
  apply (Submodule.Quotient.mk_eq_zero K).mpr
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (restrict₁(χ)) f).mpr
  intro c hc
  obtain ⟨z, he⟩ := sLocalZetaPair_isEmbedding_chart χ c.val hc
  change Zₛ f c.val = 0
  exact he ▸ congrFun hz z

/-- The range description identifies the image with a closed kernel in a product
of Fréchet spaces. -/
private theorem sLocalZetaPair_isEmbedding_range_frechet (χ : PontryaginDual Jₛ) :
    IsFrechetTVS (sLocalZetaPair (F := F) (S := S) χ).range := by
  rw [sLocalZetaPair_range]
  obtain ⟨_, _, hMp, hCp⟩ := schwartzBergman_frechet rightInterval isOpen_Ioi
    ordConnected_Ioi ⟨1, one_pos⟩
  obtain ⟨_, _, hMm, hCm⟩ := schwartzBergman_frechet leftInterval isOpen_Iio
    ordConnected_Iio ⟨0, zero_lt_one⟩
  let : MetrizableSpace B⁺ := hMp
  let : MetrizableSpace B⁻ := hMm
  let : CompleteSpace B⁺ := hCp
  let : CompleteSpace B⁻ := hCm
  let : MetrizableSpace B⁰ :=
    (schwartzBergman_frechet overlapInterval isOpen_Ioo ordConnected_Ioo ⟨1/2, by norm_num⟩).2.2.1
  have hclosed : IsClosed (sLocalZetaMatching (F := F) (S := S) χ : Set (B⁺ × B⁻)) :=
    ContinuousLinearMap.isClosed_ker _
  let : IsUniformAddGroup (sLocalZetaMatching (F := F) (S := S) χ) :=
    (sLocalZetaMatching χ).toAddSubgroup.isUniformAddGroup
  refine ⟨inferInstance, inferInstance, MetrizableSpace.subtype _, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact hclosed.completeSpace_coe

/-- A linear bijection from an LF-space to a Fréchet space is a homeomorphism if
a separating family of linear evaluations is continuous on both sides. Factor the
inverse through one LF stage in the space of evaluations, then use open mapping. -/
private theorem sLocalZetaPair_isEmbedding_of_evaluations {E W ι : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (hE : IsLFSpace E) (hW : IsFrechetTVS W) (e : E ≃ₗ[ℂ] W)
    (j : W →L[ℂ] (ι → ℂ)) (hj : Injective j) (hc : Continuous (j ∘ e)) :
    IsEmbedding e := by
  let R := j.toLinearMap.range
  let b := j.codRestrict R (LinearMap.mem_range_self j.toLinearMap)
  let a : E →L[ℂ] R := ⟨b.toLinearMap.comp e.toLinearMap, hc.subtype_mk _⟩
  have ha : Injective a := fun _ _ h ↦ e.injective (hj (congrArg Subtype.val h))
  obtain ⟨X, _, _, _, hX, u, i, h⟩ := hE.2
  let stage (n : ℕ) := a.comp (i n)
  have hcov (p : R) : ∃ n, p ∈ range (stage n) := by
    obtain ⟨w, hw⟩ := p.property
    obtain ⟨n, x, hx⟩ := h.exhaustive (e.symm w)
    refine ⟨n, x, Subtype.ext ?_⟩
    change j (e (i n x)) = p.val
    rw [hx, e.apply_symm_apply]
    exact hw
  obtain ⟨n, v, hv⟩ := frechet_factorization hX stage
    (fun k ↦ ha.comp (h.injective k))
    (fun k _ ⟨x, hx⟩ ↦ ⟨u k x, (congrArg a (DFunLike.congr_fun (h.compatible k) x)).trans hx⟩)
    hcov hW b
  have hinv : Continuous e.symm := by
    refine ((i n).continuous.comp v.continuous).congr fun w ↦ e.injective ?_
    exact (hj (congrArg Subtype.val (DFunLike.congr_fun hv w))).trans (e.apply_symm_apply w).symm
  let inv : W →L[ℂ] E := ⟨e.symm.toLinearMap, hinv⟩
  have hopen : IsOpenMap inv := by
    obtain ⟨hadd, hpoly, hmetr, hcomp⟩ := hW
    exact isOpenMap_of_surjective_toLF hE (X := fun _ ↦ W) (fun _ ↦ ⟨hadd, hpoly, hmetr, hcomp⟩)
      (fun _ ↦ ContinuousLinearMap.id ℂ W) (fun _ ↦ Subset.rfl) (fun w ↦ ⟨0, w, rfl⟩)
      inv e.symm.surjective
  exact (e.symm.toEquiv.toHomeomorphOfContinuousOpen hinv hopen).symm.isEmbedding

/-- Paper: Theorem 5.4.1.1(1), p. 266.
The zeta pair induces the topology of the homogeneous theta space: a theta class is close
to zero exactly when both of its zeta coordinates are close to zero on their half-planes. -/
theorem sLocalZetaPair_isEmbedding (χ : PontryaginDual Jₛ) :
    IsEmbedding (sLocalZetaPair (F := F) (S := S) χ) := by
  let Z := sLocalZetaPair (F := F) (S := S) χ
  let W := Z.range
  let e := LinearEquiv.ofInjective Z (sLocalZetaPair_isEmbedding_injective χ)
  let j : W →L[ℂ] (rightHalf → ℂ) :=
    { toFun := fun p z ↦ p.val.1.val z
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := by
        obtain ⟨T, hT, he⟩ := schwartzBergman_schwartzLine_topology rightInterval isOpen_Ioi
          ordConnected_Ioi ⟨1, one_pos⟩
        apply continuous_pi
        intro z
        let a : rightInterval := ⟨z.val.re, z.property⟩
        have ht : Continuous fun p : W ↦ T p.val.1 a z.val.im :=
          (continuous_eval_const (F := BoundedContinuousFunction ℝ ℂ) z.val.im).comp
            ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous.comp
              ((continuous_apply a).comp (he.continuous.comp (continuous_fst.comp continuous_subtype_val))))
        exact ht.congr fun p ↦ (hT p.val.1 a z.val.im).trans (by
          simp only [weightedVerticalTrace, pow_zero, one_mul, a, Complex.re_add_im]) }
  have hj : Injective j := by
    intro p q h
    have hpos : EqOn p.val.1.val q.val.1.val rightHalf := fun z hz ↦ congrFun h ⟨z, hz⟩
    have hmatch (w : W) := (mem_sLocalZetaMatching χ _).mp (sLocalZetaPair_range_le_matching χ w.property)
    exact Subtype.ext (Prod.ext (existsUnique_sLocalZetaPair_ext hpos)
      (existsUnique_sLocalZetaPair_left_ext χ _ _ fun z hz ↦
        (hmatch p hz).symm.trans ((hpos hz.1).trans (hmatch q hz))))
  apply IsEmbedding.subtypeVal.comp (f := e)
  apply sLocalZetaPair_isEmbedding_of_evaluations (sLocalHomogeneousThetaSpace_lf (restrict₁(χ)))
    (sLocalZetaPair_isEmbedding_range_frechet χ) e j hj
  apply (LinearMap.ker (φω(restrict₁(χ)))).isQuotientMap_mkQ.continuous_iff.mpr
  apply continuous_pi
  intro z
  have hd : ∃ (ψ : PontryaginDual Jₛ) (s : ℂ), 0 < s.re ∧ normChart(χ) z.val = normChart(ψ) s :=
    ⟨χ, z.val, z.property, rfl⟩
  obtain ⟨T, hT⟩ := sLocalIdelicZetaIntegral_tempered _ hd
  exact T.continuous.congr fun f ↦ (hT f).trans ((sLocalIdelicZFunction_eq_integral f hd).symm.trans
    ((sLocalZetaPair_mk χ f).1 z.property).symm)

/-- Paper: Theorem 5.4.1.1(1), p. 266.
The zeta pair has closed range. A pair is the zeta pair of a theta class exactly when its
two entries satisfy the functional equation on the overlap strip, and that condition is
closed because it is the kernel of the continuous difference map of (5.4.1.3). -/
theorem sLocalZetaPair_isClosed_range (χ : PontryaginDual Jₛ) :
    IsClosed (Set.range (sLocalZetaPair (F := F) (S := S) χ)) := by
  obtain ⟨-, -, hM, -⟩ := schwartzBergman_frechet overlapInterval isOpen_Ioo
    ordConnected_Ioo ⟨1 / 2, by norm_num⟩
  let : MetrizableSpace B⁰ := hM
  have hclosed : IsClosed (sLocalZetaMatching (F := F) (S := S) χ : Set (B⁺ × B⁻)) := by
    unfold sLocalZetaMatching
    exact ContinuousLinearMap.isClosed_ker _
  rw [← LinearMap.coe_range, sLocalZetaPair_range]
  exact hclosed

/-- Paper: Theorem 5.4.1.1(1), p. 266.
The zeta pair is a topological embedding with closed range. -/
theorem sLocalZetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ) :
    IsClosedEmbedding (sLocalZetaPair (F := F) (S := S) χ) :=
  ⟨sLocalZetaPair_isEmbedding χ, sLocalZetaPair_isClosed_range χ⟩

-- TODO(paper-gap): The two printed translation factors disagree on the overlap.
-- The functional equation and Fourier scaling both give the first factor on both entries.

/-- Paper: Theorem 5.4.1.1(1), p. 266, and Remark 5.4.1.2, p. 266.
Inverse left translation of a test induces multiplication of each zeta coordinate
by the first component's quasi-character evaluated at the translating idele class.
Deviation: Fourier scaling contributes the norm, and inversion of the Fourier
quasi-character gives the same multiplier as in the first coordinate. -/
theorem sLocalZetaPair_translate (χ : PontryaginDual Jₛ) (u : Aₛˣ) (f : ℬₛ) :
    let p : B⁺ × B⁻ := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
    let q : B⁺ × B⁻ := sLocalZetaPair (F := F) (S := S) χ
      (Submodule.Quotient.mk (schwartzBruhatUnitTranslate (R := Aₛ) u f))
    EqOn q.1.val (fun s ↦ normChart(χ) s (QuotientGroup.mk u) * p.1.val s) rightHalf ∧
    EqOn q.2.val (fun s ↦ normChart(χ) s (QuotientGroup.mk u) * p.2.val s) leftHalf :=
  by
  let p := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
  let q := sLocalZetaPair (F := F) (S := S) χ
    (Submodule.Quotient.mk (schwartzBruhatUnitTranslate u f))
  let L := fun s ↦ normChart(χ) s (QuotientGroup.mk u)
  have hp := sLocalZetaPair_mk χ f
  have hq := sLocalZetaPair_mk χ (schwartzBruhatUnitTranslate u f)
  have hright : EqOn q.1.val (fun s ↦ L s * p.1.val s) rightHalf := by
    intro s hs
    change q.1.val s = L s * p.1.val s
    refine (hq.1 hs).trans ?_
    refine Eq.trans (b := L s * Zₛ f (normChart(χ) s)) ?_
      (congrArg (L s * ·) (hp.1 hs).symm)
    have hr : ∃ (ψ : PontryaginDual Jₛ) (t : ℂ),
        0 < t.re ∧ normChart(χ) s = normChart(ψ) t := ⟨χ, s, hs, rfl⟩
    change Zₛ (schwartzBruhatUnitTranslate u f) (normChart(χ) s) =
      L s * Zₛ f (normChart(χ) s)
    rw [sLocalIdelicZFunction_eq_integral _ hr, sLocalIdelicZFunction_eq_integral _ hr]
    have := sIdeleGroup_borelSpace (F := F) (S := S)
    have := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
    exact integral_translate_character (sMultiplicativeTamagawaMeasure F S)
      (fun x ↦ f (Multiplicative.ofAdd x.val))
      ((normChart(χ) s).toMonoidHom.comp (QuotientGroup.mk' _)) u
  refine ⟨hright, ?_⟩
  have hol (w : B⁻) : AnalyticOnNhd ℂ w.val leftHalf :=
    w.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re)
  have hL : AnalyticOnNhd ℂ L leftHalf := fun s _ ↦
    normTwist_eval_analytic mₛ hmₛ _ _ s
  apply (hol q.2).eqOn_of_preconnected_of_frequently_eq (hL.mul (hol p.2))
    (convex_halfSpace_re_lt 1).isPreconnected (z₀ := 1/2) (by norm_num [mem_preimage])
  have hband : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2 : ℂ), s ∈ overlap :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by
      norm_num [mem_preimage, mem_Ioo]))
  apply Filter.Eventually.frequently
  filter_upwards [hband, nhdsNE_le_codiscrete _ (sLocalRhoFactor_mul_dual χ)] with s hs hprod
  have hne : ρₛ(χ, s) ≠ 0 := left_ne_zero_of_mul
    (hprod.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : Aₛˣ) : Jₛ)).map (normChart(χ) s)).ne_zero)
  apply mul_left_cancel₀ hne
  calc
    ρₛ(χ, s) * q.2.val s = q.1.val s := by
      rw [hq.1 hs.1, hq.2 hs.2]
      exact (existsUnique_sLocalZetaPair_equation χ _ s hs).symm
    _ = L s * p.1.val s := hright hs.1
    _ = ρₛ(χ, s) * (L s * p.2.val s) := by
      calc
        _ = L s * (ρₛ(χ, s) * p.2.val s) := congrArg (L s * ·)
          ((hp.1 hs.1).trans ((existsUnique_sLocalZetaPair_equation χ f s hs).trans
            (congrArg (ρₛ(χ, s) * ·) (hp.2 hs.2).symm)))
        _ = _ := by ring

private theorem exists_sLocalZetaPair_action_multiplier_mem (I : Set ℝ) (r : ℝ) (hr : 0 < r)
    (c : ℂ) (f : schwartzBergmanSubmodule I) :
    (fun z : ℂ ↦ c * (r : ℂ) ^ z * f.val z) ∈ schwartzBergmanSubmodule I := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change c * (r : ℂ) ^ z * f.val z = 0
    simp only [f.property.1 hz, Pi.zero_apply, mul_zero]
  · exact ((differentiable_const c).mul
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne')))).differentiableOn.mul
        f.property.2.1
  · intro a b hab hsub N
    obtain ⟨C, hC⟩ := f.property.2.2 a b hab hsub N
    have hc : ContinuousOn (fun x : ℝ ↦ r ^ x) (Icc a b) :=
      (Real.continuous_const_rpow hr.ne').continuousOn
    obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image hc
    refine ⟨‖c‖ * max D 0 * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hcz := hC (mem_image_of_mem _ hz)
    have hdz : r ^ z.re ≤ max D 0 := (hD (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    calc
      ‖z ^ N * (c * (r : ℂ) ^ z * f.val z)‖ =
          (‖c‖ * r ^ z.re) * ‖z ^ N * f.val z‖ := by
        rw [show z ^ N * (c * (r : ℂ) ^ z * f.val z) =
          (c * (r : ℂ) ^ z) * (z ^ N * f.val z) by ring]
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr]
      _ ≤ (‖c‖ * max D 0) * C :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdz (norm_nonneg _)) hcz
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_max_right _ _))

private theorem exists_sLocalZetaPair_action_multiplier_norm (I : Set ℝ) (r : ℝ) (hr : 0 < r)
    (c : ℂ) (f : schwartzBergmanSubmodule I) (a : I) (N : ℕ) :
    lpNorm (weightedVerticalTrace a N (fun z : ℂ ↦ c * (r : ℂ) ^ z * f.val z)) 2 volume =
      (‖c‖ * r ^ (a : ℝ)) * lpNorm (weightedVerticalTrace a N f.val) 2 volume := by
  let u : schwartzBergmanSubmodule I := ⟨_, exists_sLocalZetaPair_action_multiplier_mem I r hr c f⟩
  have hu := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N u
  have hf := schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) N f
  have hn : ∀ y : ℝ, ‖weightedVerticalTrace a N u.val y‖ =
      ‖((‖c‖ * r ^ (a : ℝ)) • weightedVerticalTrace a N f.val) y‖ := by
    intro y
    simp only [weightedVerticalTrace, u, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero, Pi.smul_apply,
      norm_smul, Real.norm_eq_abs]
    rw [abs_norm, abs_of_pos (Real.rpow_pos_of_pos hr _)]
    ring
  change lpNorm (weightedVerticalTrace a N u.val) 2 volume = _
  unfold lpNorm
  rw [eLpNorm_congr_norm_ae hu.aestronglyMeasurable
    (hf.const_smul (‖c‖ * r ^ (a : ℝ))).aestronglyMeasurable (Filter.Eventually.of_forall hn)]
  change lpNorm ((‖c‖ * r ^ (a : ℝ)) • weightedVerticalTrace a N f.val) 2 volume = _
  rw [lpNorm_const_smul]
  change |‖c‖ * r ^ (a : ℝ)| * _ = _
  rw [abs_of_nonneg (mul_nonneg (norm_nonneg c) (Real.rpow_pos_of_pos hr _).le)]
  rfl

private theorem exists_sLocalZetaPair_action_multiplier_clm (I : Set ℝ) (r : ℝ) (hr : 0 < r) (c : ℂ) :
    ∃ A : SchwartzBergman I →L[ℂ] SchwartzBergman I,
      ∀ f z, (A f).val z = c * (r : ℂ) ^ z * f.val z := by
  let A : SchwartzBergman I →ₗ[ℂ] SchwartzBergman I :=
    { toFun := fun f ↦ ⟨_, exists_sLocalZetaPair_action_multiplier_mem I r hr c f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun z ↦ mul_add _ _ _)
      map_smul' := fun d f ↦ Subtype.ext (funext fun z ↦ by
        change c * (r : ℂ) ^ z * (d * f.val z) = d * (c * (r : ℂ) ^ z * f.val z)
        ring) }
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦
      (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hP : WithSeminorms P := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P
  have hc : Continuous A := by
    apply hP.continuous_of_continuous_comp A
    intro i
    have he : (fun f ↦ P i (A f)) = (fun f ↦ (‖c‖ * r ^ (i.1 : ℝ)) * P i f) := by
      funext f
      exact exists_sLocalZetaPair_action_multiplier_norm I r hr c f i.1 i.2
    change Continuous (fun f ↦ P i (A f))
    rw [he]
    exact (hP.continuous_seminorm i).const_mul _
  exact ⟨⟨A, hc⟩, fun _ _ ↦ rfl⟩

private theorem exists_sLocalZetaPair_action_multiplier_action.{u} (G : Type u) [Group G] (I : Set ℝ)
    (r : G →* ℝ≥0ˣ) (c : G →* ℂ) :
    ∃ A : G →* (SchwartzBergman I →L[ℂ] SchwartzBergman I),
      ∀ g f z, (A g f).val z = c g * ((r g).val : ℂ) ^ z * f.val z := by
  have hp (g : G) : 0 < ((r g).val : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (r g).ne_zero)
  choose A hA using fun g ↦ exists_sLocalZetaPair_action_multiplier_clm I ((r g).val : ℝ) (hp g) (c g)
  refine ⟨{ toFun := A, map_one' := ?_, map_mul' := ?_ }, hA⟩
  · apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    funext z
    rw [hA]
    simp
  · intro g h
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    funext z
    change (A (g * h) f).val z = (A g (A h f)).val z
    rw [hA, hA, hA, map_mul, map_mul]
    simp only [Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (hp g).le (hp h).le]
    ring

private theorem exists_sLocalZetaPair_action_multiplier_l2_cont (X : Type) [TopologicalSpace X] [FirstCountableTopology X]
    (u : X → ℝ → ℂ) (x₀ : X) (b : ℝ → ℝ)
    (hu : ∀ x, MemLp (u x) 2 volume) (hb : MemLp b 2 volume)
    (hbound : ∀ᶠ x in nhds x₀, ∀ y, ‖u x y‖ ≤ b y)
    (hcont : ∀ y, ContinuousAt (fun x ↦ u x y) x₀) :
    ContinuousAt (fun x ↦ lpNorm (u x) 2 volume) x₀ := by
  have hc : ContinuousAt (fun x ↦ ∫ y, ‖u x y‖ ^ (2 : ℕ)) x₀ := by
    apply continuousAt_of_dominated (bound := fun y ↦ ‖b y‖ ^ (2 : ℕ))
    · exact Filter.Eventually.of_forall fun x ↦ (hu x).aestronglyMeasurable.norm.pow 2
    · filter_upwards [hbound] with x hx
      exact Filter.Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((hx y).trans (le_abs_self _)) 2
    · exact hb.integrable_norm_pow (by norm_num)
    · exact Filter.Eventually.of_forall fun y ↦ (hcont y).norm.pow 2
  have he (x : X) : lpNorm (u x) 2 volume = (∫ y, ‖u x y‖ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) (hu x).aestronglyMeasurable]
    norm_num
  simp_rw [he]
  exact hc.rpow_const (Or.inr (by norm_num))

private theorem exists_sLocalZetaPair_action_multiplier_orbit (X : Type) [TopologicalSpace X] [FirstCountableTopology X]
    (I : Set ℝ) (r : X → ℝ) (hr : ∀ x, 0 < r x) (hcR : Continuous r)
    (c : X → ℂ) (hcC : Continuous c)
    (A : X → SchwartzBergman I →L[ℂ] SchwartzBergman I)
    (hA : ∀ x f z, (A x f).val z = c x * (r x : ℂ) ^ z * f.val z)
    (f : SchwartzBergman I) : Continuous (fun x ↦ A x f) := by
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦
      (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hP : WithSeminorms P := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply (hP.tendsto_nhds _ _).mpr
  intro i ε hε
  let T := fun v : SchwartzBergman I ↦ weightedVerticalTrace i.1 i.2 v.val
  let u := fun x ↦ T (A x f - A x₀ f)
  let C := fun x ↦ ‖c x‖ * (r x) ^ (i.1 : ℝ)
  have hC : Continuous C := hcC.norm.mul (hcR.rpow_const fun x ↦ Or.inl (hr x).ne')
  have hT (v : SchwartzBergman I) : MemLp (T v) 2 volume :=
    schwartzBergman_trace_memLp I i.1 2 (by norm_num) (by norm_num) i.2 v
  have hnorm (x : X) (y : ℝ) : ‖T (A x f) y‖ = C x * ‖T f y‖ := by
    simp only [T, weightedVerticalTrace, hA, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hr x), Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
      zero_mul, sub_self, add_zero, C]
    ring
  have hsub (x : X) (y : ℝ) : u x y = T (A x f) y - T (A x₀ f) y := by
    change _ * ((A x f).val _ - (A x₀ f).val _) = _
    exact mul_sub _ _ _
  have hb : MemLp (fun y ↦ (2 * C x₀ + 1) * ‖T f y‖) 2 volume :=
    (hT f).norm.const_mul _
  have hbnd : ∀ᶠ x in nhds x₀, ∀ y, ‖u x y‖ ≤ (2 * C x₀ + 1) * ‖T f y‖ := by
    filter_upwards [hC.continuousAt.eventually (gt_mem_nhds (by linarith : C x₀ < C x₀ + 1))] with x hx
    intro y
    rw [hsub]
    calc
      _ ≤ ‖T (A x f) y‖ + ‖T (A x₀ f) y‖ := norm_sub_le _ _
      _ = (C x + C x₀) * ‖T f y‖ := by rw [hnorm, hnorm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have huc (y : ℝ) : ContinuousAt (fun x ↦ u x y) x₀ := by
    simp_rw [hsub]
    simp only [T, weightedVerticalTrace, hA]
    apply ContinuousAt.sub _ continuousAt_const
    apply ContinuousAt.const_mul
    apply ContinuousAt.mul _ continuousAt_const
    apply hcC.continuousAt.mul
    exact (Complex.continuous_ofReal.comp hcR).continuousAt.cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.mpr (hr x₀))
  have hu := exists_sLocalZetaPair_action_multiplier_l2_cont X u x₀ _ (fun x ↦ hT _) hb hbnd huc
  have hz : lpNorm (u x₀) 2 volume = 0 := by
    have he : u x₀ = 0 := by funext y; rw [hsub]; simp
    rw [he, lpNorm_zero]
  have he : ∀ x, P i (A x f - A x₀ f) = lpNorm (u x) 2 volume := fun _ ↦ rfl
  simp_rw [he]
  exact hu.eventually (gt_mem_nhds (by simpa only [hz] using hε))

private theorem exists_sLocalZetaPair_action_multiplier_joint (X : Type) [TopologicalSpace X] [FirstCountableTopology X]
    (I : Set ℝ) (r : X → ℝ) (hr : ∀ x, 0 < r x) (hcR : Continuous r)
    (c : X → ℂ) (hcC : Continuous c)
    (A : X → SchwartzBergman I →L[ℂ] SchwartzBergman I)
    (hA : ∀ x f z, (A x f).val z = c x * (r x : ℂ) ^ z * f.val z) :
    Continuous (fun p : X × SchwartzBergman I ↦ A p.1 p.2) := by
  let P : I × ℕ → Seminorm ℂ (SchwartzBergman I) := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦
      (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hP : WithSeminorms P := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P
  have hnorm (i : I × ℕ) (x : X) (f : SchwartzBergman I) :
      P i (A x f) = (‖c x‖ * (r x) ^ (i.1 : ℝ)) * P i f := by
    change lpNorm (weightedVerticalTrace i.1 i.2 (A x f).val) 2 volume = _
    have he : (A x f).val = fun z ↦ c x * (r x : ℂ) ^ z * f.val z := funext (hA x f)
    rw [he]
    exact exists_sLocalZetaPair_action_multiplier_norm I (r x) (hr x) (c x) f i.1 i.2
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply (hP.tendsto_nhds _ _).mpr
  intro i ε hε
  let B := fun p : X × SchwartzBergman I ↦
    (‖c p.1‖ * (r p.1) ^ (i.1 : ℝ)) * P i (p.2 - p₀.2) + P i (A p.1 p₀.2 - A p₀.1 p₀.2)
  have hb : Continuous B :=
    (((hcC.comp continuous_fst).norm.mul
      ((hcR.comp continuous_fst).rpow_const fun p ↦ Or.inl (hr p.1).ne')).mul
        ((hP.continuous_seminorm i).comp (continuous_snd.sub continuous_const))).add
      ((hP.continuous_seminorm i).comp
        (((exists_sLocalZetaPair_action_multiplier_orbit X I r hr hcR c hcC A hA p₀.2).comp continuous_fst).sub continuous_const))
  have hz : B p₀ = 0 := by simp [B]
  filter_upwards [hb.continuousAt.eventually (gt_mem_nhds (by simpa only [hz] using hε))] with p hp
  apply lt_of_le_of_lt _ hp
  have he : A p.1 p.2 - A p₀.1 p₀.2 =
      A p.1 (p.2 - p₀.2) + (A p.1 p₀.2 - A p₀.1 p₀.2) := by rw [map_sub]; abel
  rw [he]
  exact (map_add_le_add (P i) _ _).trans_eq (by rw [hnorm])

/-- Paper: Theorem 5.4.1.1(1), pp. 265–266.
For each class, multiplication by its norm-twisted character preserves one
Schwartz–Bergman space and is a continuous linear map. -/
private theorem exists_sLocalZetaPair_action_multiplier_maps (χ : PontryaginDual Jₛ)
    (I : Set ℝ) :
    ∃ A : Jₛ →* (SchwartzBergman I →L[ℂ] SchwartzBergman I),
      ∀ (g : Jₛ) (f : SchwartzBergman I),
        EqOn (A g f).val (fun s ↦ normChart(χ) s g * f.val s) (Complex.re ⁻¹' I) := by
  obtain ⟨A, hA⟩ := exists_sLocalZetaPair_action_multiplier_action Jₛ I mₛ (Circle.coeHom.comp χ.toMonoidHom)
  exact ⟨A, fun g f z _ ↦ hA g f z⟩

/-- Paper: Theorem 5.4.1.1(1), pp. 265–266.
The multiplier action on one Schwartz–Bergman space is jointly continuous. -/
private theorem exists_sLocalZetaPair_action_multiplier_continuous (χ : PontryaginDual Jₛ)
    (I : Set ℝ) (A : Jₛ →* (SchwartzBergman I →L[ℂ] SchwartzBergman I))
    (hA : ∀ (g : Jₛ) (f : SchwartzBergman I),
      EqOn (A g f).val (fun s ↦ normChart(χ) s g * f.val s) (Complex.re ⁻¹' I)) :
    Continuous (fun p : Jₛ × SchwartzBergman I ↦ A p.1 p.2) := by
  let X := ℂ × Set.Ioi (0 : ℝ)
  let r : X → ℝ := fun p ↦ p.2.val
  let c : X → ℂ := Prod.fst
  have hr (x : X) : 0 < r x := x.2.property
  choose B hB using fun x ↦ exists_sLocalZetaPair_action_multiplier_clm I (r x) (hr x) (c x)
  have hBc := exists_sLocalZetaPair_action_multiplier_joint X I r hr
    (continuous_subtype_val.comp continuous_snd)
    c continuous_fst B hB
  let p : Jₛ → X := fun g ↦
    (χ g, ⟨normℝ(mₛ g), NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (mₛ g).ne_zero)⟩)
  have hp : Continuous p := (continuous_subtype_val.comp χ.continuous).prodMk
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp hmₛ)).subtype_mk _)
  have he (g : Jₛ) (f : SchwartzBergman I) : A g f = B (p g) f := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ Complex.re ⁻¹' I
    · rw [hA g f hz, hB]
      rfl
    · rw [(A g f).property.1 hz, (B (p g) f).property.1 hz]
  have hc := hBc.comp ((hp.comp continuous_fst).prodMk continuous_snd)
  exact hc.congr (fun q ↦ (he q.1 q.2).symm)

private theorem exists_sLocalZetaPair_action_multiplier (χ : PontryaginDual Jₛ) (I : Set ℝ) :
    ∃ A : Jₛ →* (SchwartzBergman I →L[ℂ] SchwartzBergman I),
      Continuous (fun p : Jₛ × SchwartzBergman I ↦ A p.1 p.2) ∧
      ∀ (g : Jₛ) (f : SchwartzBergman I),
        EqOn (A g f).val (fun s ↦ normChart(χ) s g * f.val s) (Complex.re ⁻¹' I) := by
  obtain ⟨A, hA⟩ := exists_sLocalZetaPair_action_multiplier_maps (F := F) (S := S) χ I
  exact ⟨A, exists_sLocalZetaPair_action_multiplier_continuous (F := F) (S := S) χ I A hA,
    hA⟩

/-- Paper: Theorem 5.4.1.1(1), pp. 265–266.
The componentwise multipliers give a jointly continuous action on the ambient pair.
Deviation: Both coordinates in the reflected chart have the character of the test. -/
theorem exists_sLocalZetaPair_action (χ : PontryaginDual Jₛ) :
    ∃ A : Jₛ →* ((B⁺ × B⁻) →L[ℂ] (B⁺ × B⁻)),
      Continuous (fun p : Jₛ × (B⁺ × B⁻) ↦ A p.1 p.2) ∧
      ∀ (g : Jₛ) (p : B⁺ × B⁻),
        EqOn (A g p).1.val (fun s ↦ normChart(χ) s g * p.1.val s) rightHalf ∧
        EqOn (A g p).2.val (fun s ↦ normChart(χ) s g * p.2.val s) leftHalf := by
  obtain ⟨Aplus, hplus, eplus⟩ := exists_sLocalZetaPair_action_multiplier (F := F) (S := S) χ rightInterval
  obtain ⟨Aminus, hminus, eminus⟩ := exists_sLocalZetaPair_action_multiplier (F := F) (S := S) χ leftInterval
  let A : Jₛ →* ((B⁺ × B⁻) →L[ℂ] (B⁺ × B⁻)) :=
    { toFun := fun g ↦ (Aplus g).prodMap (Aminus g)
      map_one' := by
        ext p <;> simp [Aplus.map_one, Aminus.map_one]
      map_mul' := by
        intro g h
        ext p <;> simp [map_mul] }
  refine ⟨A, ?_, ?_⟩
  · exact (hplus.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (hminus.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  · intro g p
    exact ⟨eplus g p.1, eminus g p.2⟩

/-- Paper: Theorem 5.4.1.1(2), p. 266.
The quotient topology on every homogeneous S-local theta space is Fréchet. -/
theorem sLocalHomogeneousThetaSpace_frechet (ω : PontryaginDual J₁) :
    IsFrechetTVS (Θω(ω)) := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, hχ, _⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  rw [← hχ.1]
  obtain ⟨_, _, hMp, hCp⟩ := schwartzBergman_frechet rightInterval isOpen_Ioi
    ordConnected_Ioi ⟨1, by norm_num⟩
  obtain ⟨_, _, hMm, hCm⟩ := schwartzBergman_frechet leftInterval isOpen_Iio
    ordConnected_Iio ⟨0, by norm_num⟩
  let : MetrizableSpace B⁺ := hMp
  let : MetrizableSpace B⁻ := hMm
  let : CompleteSpace B⁺ := hCp
  let : CompleteSpace B⁻ := hCm
  let T := sLocalZetaPair (F := F) (S := S) χ
  have hT : IsClosedEmbedding T := sLocalZetaPair_isClosedEmbedding χ
  let : UniformSpace Θω(restrict₁(χ)) :=
    IsTopologicalAddGroup.rightUniformSpace Θω(restrict₁(χ))
  have : IsUniformAddGroup Θω(restrict₁(χ)) := isUniformAddGroup_of_addCommGroup
  have hU : IsUniformInducing T :=
    AddMonoidHom.isUniformInducing_of_isInducing (f := T.toAddMonoidHom) hT.isInducing
  exact ⟨inferInstance, hT.isInducing.polynormableSpace (f := T),
    hT.isEmbedding.metrizableSpace, hU.completeSpace hT.isClosed_range.isComplete⟩

/-- A nuclear space is separable for each of its continuous seminorms (as in the private
`seminorm_separable_of_nuclear` of Appendix D §1b): a totally bounded zero-neighbourhood
spans the space and has separable span. -/
private theorem sLocalHomogeneousThetaSpace_separable_seminorm.{w, x} {E : Type x}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (h : IsNuclearTVS.{w} E) (p : Seminorm ℂ E) (hp : Continuous p) :
    SeparableSpace (WithLocalSeminorm p) := by
  obtain ⟨V, hV, htot⟩ := (isSchwartzTVS_of_isNuclearTVS h).2 p hp
  let W : Set (WithLocalSeminorm p) := V
  have hW : TotallyBounded W := htot
  have hAbs : Absorbent ℂ W := by
    change Absorbent ℂ V
    exact absorbent_nhds_zero (𝕜 := ℂ) hV
  have hspan : Submodule.span ℂ W = ⊤ :=
    (hAbs.mono (Submodule.subset_span (R := ℂ))).submodule_eq_top
  have hS := hW.isSeparable.span (R := ℂ)
  rw [hspan, Submodule.top_coe] at hS
  exact isSeparable_univ_iff.mp hS

/-- A nuclear space with a countable neighbourhood basis at zero is separable: for each basic
neighbourhood pick a continuous seminorm ball inside it and a dense sequence for that seminorm. -/
private theorem sLocalHomogeneousThetaSpace_separable_aux.{w, x} {E : Type x} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [FirstCountableTopology E]
    (h : IsNuclearTVS.{w} E) : SeparableSpace E := by
  let := h.2.1
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  have hw := PolynormableSpace.withSeminorms ℂ E
  let : ContinuousSMul ℂ E := hw.continuousSMul
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have hex (n : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧ ∃ r > 0, q.ball 0 r ⊆ U n := by
    obtain ⟨s, r, hr, hsub⟩ := (hw.mem_nhds_iff 0 (U n)).mp (hU.mem n)
    refine ⟨s.sup fun p : {p : Seminorm ℂ E // Continuous p} ↦ p.1, ?_, r, hr, hsub⟩
    exact hw.continuous_finsetSup_seminorm s
  choose q hq r hr hsub using hex
  have hsep (n : ℕ) : SeparableSpace (WithLocalSeminorm (q n)) :=
    sLocalHomogeneousThetaSpace_separable_seminorm h (q n) (hq n)
  have hd (n : ℕ) : ∃ d : ℕ → E, ∀ x : E, ∃ m, q n (x - d m) < r n := by
    obtain ⟨d, hd⟩ := exists_dense_seq (WithLocalSeminorm (q n))
    refine ⟨d, fun x ↦ ?_⟩
    let x' : WithLocalSeminorm (q n) := x
    obtain ⟨m, hm⟩ := hd.exists_dist_lt x' (hr n)
    rw [dist_eq_norm] at hm
    exact ⟨m, hm⟩
  choose d hd using hd
  refine ⟨range fun m : ℕ × ℕ ↦ d m.1 m.2, countable_range _, ?_⟩
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  have hW0 : (fun y ↦ x + y) ⁻¹' W ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨n, -, hn⟩ := hU.1.mem_iff.mp hW0
  obtain ⟨m, hm⟩ := hd n x
  refine ⟨d n m, ?_, ⟨(n, m), rfl⟩⟩
  have : d n m - x ∈ U n := hsub n (by rw [Seminorm.mem_ball, sub_zero, map_sub_rev]; exact hm)
  simpa using hn this

/-- A nuclear Fréchet space is separable. The instances are implicit arguments, so that they are
read off the hypotheses instead of being unfolded through the quotient. -/
private theorem sLocalHomogeneousThetaSpace_separable_of_frechet.{w, x} {E : Type x}
    {_ : AddCommGroup E} {_ : Module ℂ E} {_ : TopologicalSpace E} (hf : IsFrechetTVS E)
    (h : IsNuclearTVS.{w} E) : SeparableSpace E := by
  obtain ⟨_, -, _, -⟩ := hf
  exact sLocalHomogeneousThetaSpace_separable_aux h

/-- Paper: Theorem 5.4.1.1(2), p. 266.
Every homogeneous S-local theta space is separable. -/
theorem sLocalHomogeneousThetaSpace_separable (ω : PontryaginDual J₁) :
    SeparableSpace (Θω(ω)) :=
  sLocalHomogeneousThetaSpace_separable_of_frechet.{0}
    (sLocalHomogeneousThetaSpace_frechet ω) (sLocalHomogeneousThetaSpace_nuclear ω)

-- The nuclearity assertion in (2) is `sLocalHomogeneousThetaSpace_nuclear` from §5.2.3.

private theorem sLocalPolarFreeZetaPair_frechet_submodule {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsFrechetTVS E)
    (P : Submodule ℂ E) (hP : IsClosed (P : Set E)) : IsFrechetTVS P := by
  obtain ⟨hadd, hpoly, hmet, hcomp⟩ := hE
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomp
  let : IsUniformAddGroup P := P.toAddSubgroup.isUniformAddGroup
  refine ⟨inferInstance, inferInstance, MetrizableSpace.subtype _, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact hP.completeSpace_coe

private theorem sLocalPolarFreeZetaPair_frechet_prod {E V : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (hE : IsFrechetTVS E) (hV : IsFrechetTVS V) : IsFrechetTVS (E × V) := by
  obtain ⟨haddE, hpolyE, hmetE, hcompE⟩ := hE
  obtain ⟨haddV, hpolyV, hmetV, hcompV⟩ := hV
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace V := IsTopologicalAddGroup.rightUniformSpace V
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup V := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcompE
  let : CompleteSpace V := hcompV
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- Evaluation is continuous by the Schwartz line description of Appendix D. -/
private theorem decayFourier_bergman_eval (I : Set ℝ) (ho : IsOpen I)
    (hi : OrdConnected I) (hn : I.Nonempty) (z : ℂ) :
    Continuous (fun f : SchwartzBergman I ↦ f.val z) := by
  by_cases hz : z.re ∈ I
  · obtain ⟨T, hT, hE⟩ := schwartzBergman_schwartzLine_topology I ho hi hn
    let a : I := ⟨z.re, hz⟩
    have hz' : (a.val : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
    have hc : Continuous (fun f : SchwartzBergman I ↦ T f a z.im) :=
      (continuous_eval_const (F := BoundedContinuousFunction ℝ ℂ) z.im).comp
        ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous.comp
          ((continuous_apply a).comp hE.continuous))
    refine hc.congr fun f ↦ (hT f a z.im).trans ?_
    simp only [weightedVerticalTrace, pow_zero, one_mul, hz']
  · exact continuous_const.congr fun f ↦ (f.property.1 hz).symm

/-- A linear map between Fréchet spaces is continuous if it is continuous after a
continuous linear injection into a Hausdorff function space. -/
private theorem sLocalZetaPair_continuous_of_eval {E V ι : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (hE : IsFrechetTVS E) (hV : IsFrechetTVS V)
    (i : V →L[ℂ] (ι → ℂ)) (hi : Injective i) (L : E →ₗ[ℂ] V)
    (hc : Continuous (fun x ↦ i (L x))) : Continuous L := by
  let R := i.toLinearMap.range
  let j : V →L[ℂ] R := i.codRestrict R (LinearMap.mem_range_self i.toLinearMap)
  let u : E →L[ℂ] R := ⟨j.toLinearMap.comp L, hc.subtype_mk _⟩
  obtain ⟨_, T, hT⟩ := frechet_factorization (X := fun _ ↦ V) (fun _ ↦ hV) (fun _ ↦ j)
    (fun _ _ _ h ↦ hi (congrArg Subtype.val h)) (fun _ ↦ Subset.rfl)
    (fun y ↦ ⟨0, y.property.choose, Subtype.ext y.property.choose_spec⟩) hE u
  exact T.continuous.congr fun x ↦ hi (congrArg Subtype.val (DFunLike.congr_fun hT x))

/-- The first component separates matching pairs by the functional equation and
holomorphic uniqueness on the left half-plane. -/
private theorem sLocalZetaPair_matching_fst_injective (χ : PontryaginDual Jₛ)
    (p q : sLocalZetaMatching (F := F) (S := S) χ) (h : p.val.1.val = q.val.1.val) : p = q := by
  have hp := (mem_sLocalZetaMatching χ _).mp p.property
  have hq := (mem_sLocalZetaMatching χ _).mp q.property
  exact Subtype.ext (Prod.ext (Subtype.ext h) (existsUnique_sLocalZetaPair_left_ext χ _ _ fun z hz ↦
    (hp hz).symm.trans ((congrFun h z).trans (hq hz))))

/-- Paper: Lemma 5.4.1.3, p. 266.
The quotient-to-pair map is continuous. -/
theorem continuous_sLocalZetaPair (χ : PontryaginDual Jₛ) : Continuous (sLocalZetaPair (F := F) (S := S) χ) := by
  let W := sLocalZetaMatching (F := F) (S := S) χ
  let : MetrizableSpace B⁰ :=
    (schwartzBergman_frechet overlapInterval isOpen_Ioo ordConnected_Ioo ⟨1/2, by norm_num⟩).2.2.1
  have hW : IsFrechetTVS W := sLocalPolarFreeZetaPair_frechet_submodule
    (sLocalPolarFreeZetaPair_frechet_prod
      (schwartzBergman_frechet rightInterval isOpen_Ioi ordConnected_Ioi ⟨1, one_pos⟩)
      (schwartzBergman_frechet leftInterval isOpen_Iio ordConnected_Iio ⟨0, zero_lt_one⟩))
    W (ContinuousLinearMap.isClosed_ker _)
  let i : W →L[ℂ] (ℂ → ℂ) :=
    { toFun := fun y ↦ y.val.1.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_pi fun z ↦
        (decayFourier_bergman_eval rightInterval isOpen_Ioi ordConnected_Ioi ⟨1, one_pos⟩ z).comp
          (continuous_fst.comp continuous_subtype_val) }
  let K := LinearMap.ker (φω(restrict₁(χ)))
  let Z := sLocalZetaPair (F := F) (S := S) χ
  let L := Z.codRestrict W (fun x ↦ sLocalZetaPair_range_le_matching χ ⟨x, rfl⟩)
  have he (z : ℂ) : Continuous fun f : ℬₛ ↦ i (L (K.mkQ f)) z := by
    by_cases hz : z ∈ rightHalf
    · have hd : ∃ (ψ : PontryaginDual Jₛ) (t : ℂ), 0 < t.re ∧ normChart(χ) z = normChart(ψ) t :=
        ⟨χ, z, hz, rfl⟩
      have h := sLocalIdelicZetaIntegral_tempered (normChart(χ) z) hd
      exact h.choose.continuous.congr fun f ↦ (h.choose_spec f).trans
        ((sLocalIdelicZFunction_eq_integral f hd).symm.trans ((sLocalZetaPair_mk χ f).1 hz).symm)
    · exact continuous_const.congr fun f ↦ ((Z (K.mkQ f)).1.property.1 hz).symm
  apply K.isQuotientMap_mkQ.continuous_iff.mpr
  suffices hc : Continuous (L.comp K.mkQ) from continuous_subtype_val.comp hc
  apply SchwartzBruhat.continuous_of_continuous_comp_ofStage
  intro a e
  exact sLocalZetaPair_continuous_of_eval elementarySchwartz_isFrechet hW i
    (sLocalZetaPair_matching_fst_injective χ) ((L.comp K.mkQ).comp (SchwartzBruhat.ofStage a e))
    (continuous_pi fun z ↦ (he z).comp (SchwartzBruhat.continuous_ofStage a e))

/-- Paper: Lemma 5.4.1.3, p. 266.
The two zeta restrictions determine the homogeneous theta class. -/
theorem injective_sLocalZetaPair (χ : PontryaginDual Jₛ) : Injective (sLocalZetaPair (F := F) (S := S) χ) := by
  exact (sLocalZetaPair_isClosedEmbedding (F := F) (S := S) χ).injective

-- Match the choice of archimedean coordinates in §5.3.4.
local notation "RealModels" => ((w : {v : InfinitePlace F // v.IsReal}) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels" => ((w : {v : InfinitePlace F // v.IsComplex}) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})

local notation "polarTests(" r ", " c ")" => sAdelePolarFree (F := F) S (r) (c)

local notation "polarKernel(" P ", " ω ")" => LinearMap.ker ((φω(ω)).comp (P).subtype)

/-- Paper: (5.4.1.7), p. 267.
The polar-free homogeneous theta space is the quotient of the polar-free subspace
by the kernel of its restricted homogeneous theta transform.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev SLocalPolarFreeThetaSpace (r : RealModels) (c : ComplexModels) (ω : PontryaginDual J₁) :=
  ↥(polarTests(r, c)) ⧸ polarKernel(polarTests(r, c), ω)

/-- Paper: (5.4.1.7), p. 267.
Two polar-free representatives define the same class exactly when their
homogeneous theta functions coincide. -/
theorem sLocalPolarFreeThetaSpace_mk_eq_iff (r : RealModels) (c : ComplexModels)
    (ω : PontryaginDual J₁) (f g : polarTests(r, c)) :
    (polarKernel(polarTests(r, c), ω)).mkQ f = (polarKernel(polarTests(r, c), ω)).mkQ g ↔
      φω(ω) f.val = φω(ω) g.val := by
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, LinearMap.comp_apply,
    Submodule.subtype_apply, Submodule.coe_sub, map_sub, sub_eq_zero]

local notation "polarInclusion(" P ", " ω ")" =>
  (polarKernel(P, ω)).mapQ (LinearMap.ker (φω(ω))) (P).subtype
    (le_of_eq (LinearMap.ker_comp (P).subtype (φω(ω))))

/-- Paper: (5.4.1.7), p. 267.
The zeta pair on the polar-free quotient is the full zeta pair applied to the
class of the same test function. -/
def sLocalPolarFreeZetaPair (χ : PontryaginDual Jₛ) (r : RealModels) (c : ComplexModels) :
    SLocalPolarFreeThetaSpace (F := F) (S := S) r c (restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻ :=
  (sLocalZetaPair (F := F) (S := S) χ).comp (polarInclusion(polarTests(r, c), restrict₁(χ)))

/-- Paper: (5.4.1.8), p. 267.
The matching pairs in V are those whose first component extends to an entire function. -/
def sLocalPolarFreeMatching (χ : PontryaginDual Jₛ) : Set (B⁺ × B⁻) :=
  {p | p ∈ sLocalZetaMatching (F := F) (S := S) χ ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧ EqOn H p.1.val rightHalf}

private theorem mem_sLocalPolarFreeMatching_iff_aux (ρ a b : ℂ → ℂ) (hρ : Meromorphic ρ)
    (ha : AnalyticOnNhd ℂ a (Complex.re ⁻¹' Ioi (0 : ℝ)))
    (hb : AnalyticOnNhd ℂ b (Complex.re ⁻¹' Iio (1 : ℝ)))
    (hab : EqOn a (fun s ↦ ρ s * b s) (Complex.re ⁻¹' Ioo (0 : ℝ) 1)) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧ EqOn H a (Complex.re ⁻¹' Ioi (0 : ℝ))) ↔
      ∀ s ∈ Complex.re ⁻¹' Iio (1 : ℝ), 0 ≤ meromorphicOrderAt (fun z ↦ ρ z * b z) s := by
  have hoL : IsOpen (Complex.re ⁻¹' Iio (1 : ℝ)) := isOpen_Iio.preimage Complex.continuous_re
  have hoR : IsOpen (Complex.re ⁻¹' Ioi (0 : ℝ)) := isOpen_Ioi.preimage Complex.continuous_re
  have hoO : IsOpen (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := isOpen_Ioo.preimage Complex.continuous_re
  have hmg : MeromorphicOn (fun z ↦ ρ z * b z) (Complex.re ⁻¹' Iio (1 : ℝ)) :=
    fun z hz => (hρ z).mul (hb z hz).meromorphicAt
  have hmid : (1 / 2 : ℂ) ∈ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    norm_num [mem_preimage, mem_Ioo]
  have hmidL : (1 / 2 : ℂ) ∈ Complex.re ⁻¹' Iio (1 : ℝ) := by
    norm_num [mem_preimage, mem_Iio]
  have hconn : IsConnected (Complex.re ⁻¹' Iio (1 : ℝ)) :=
    ⟨⟨_, hmidL⟩, (convex_halfSpace_re_lt 1).isPreconnected⟩
  constructor
  · rintro ⟨H, hH, hHa⟩ s hs
    have hdiff : MeromorphicOn (fun z ↦ ρ z * b z - H z) (Complex.re ⁻¹' Iio (1 : ℝ)) :=
      hmg.sub (fun z _ => (hH z (mem_univ _)).meromorphicAt)
    have htop : meromorphicOrderAt (fun z ↦ ρ z * b z - H z) (1 / 2 : ℂ) = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [hoO.mem_nhds hmid |> fun h => nhdsWithin_le_nhds h] with z hz
      have h1 := hab hz
      have h2 := hHa (show z ∈ Complex.re ⁻¹' Ioi (0 : ℝ) from hz.1)
      change ρ z * b z - H z = 0
      have h1' : a z = ρ z * b z := h1
      rw [← h1', h2]; ring
    have hall : meromorphicOrderAt (fun z ↦ ρ z * b z - H z) s = ⊤ := by
      by_contra hne
      have := (hdiff.exists_meromorphicOrderAt_ne_top_iff_forall_mem hconn).mp ⟨s, hs, hne⟩
        (1 / 2) hmidL
      exact this htop
    rw [meromorphicOrderAt_eq_top_iff] at hall
    have hev : (fun z ↦ ρ z * b z) =ᶠ[𝓝[≠] s] H := by
      filter_upwards [hall] with z hz
      simpa [sub_eq_zero] using hz
    rw [meromorphicOrderAt_congr hev]
    exact (hH s (mem_univ _)).meromorphicOrderAt_nonneg
  · intro hord
    set G := toMeromorphicNFOn (fun z ↦ ρ z * b z) (Complex.re ⁻¹' Iio (1 : ℝ)) with hG
    have hGan : ∀ z ∈ Complex.re ⁻¹' Iio (1 : ℝ), AnalyticAt ℂ G z := by
      intro z hz
      have hnf : MeromorphicNFAt G z := meromorphicNFOn_toMeromorphicNFOn _ _ hz
      refine hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
      rw [hG, meromorphicOrderAt_toMeromorphicNFOn hmg hz]
      exact hord z hz
    have hGa : ∀ z ∈ Complex.re ⁻¹' Ioo (0 : ℝ) 1, G z = a z := by
      intro z hz
      have hzL : z ∈ Complex.re ⁻¹' Iio (1 : ℝ) := hz.2
      have hev : G =ᶠ[𝓝[≠] z] a := by
        have h1 := hmg.toMeromorphicNFOn_eq_self_on_nhdsNE hzL
        have h2 : (fun z ↦ ρ z * b z) =ᶠ[𝓝[≠] z] a := by
          filter_upwards [nhdsWithin_le_nhds (hoO.mem_nhds hz)] with w hw using (hab hw).symm
        exact h1.trans h2
      have hca : ContinuousAt a z := (ha z hz.1).continuousAt
      have hcG : ContinuousAt G z := (hGan z hzL).continuousAt
      exact ((hcG.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hca).mp hev).self_of_nhds
    let H : ℂ → ℂ := fun z ↦ if 0 < z.re then a z else G z
    have hHa : EqOn H a (Complex.re ⁻¹' Ioi (0 : ℝ)) := fun z hz => if_pos hz
    have hHG : EqOn H G (Complex.re ⁻¹' Iio (1 : ℝ)) := by
      intro z hz
      by_cases h0 : 0 < z.re
      · exact (if_pos h0).trans (hGa z ⟨h0, hz⟩).symm
      · exact if_neg h0
    refine ⟨H, fun z _ => ?_, hHa⟩
    by_cases hz : z.re < 1
    · exact (hGan z hz).congr (Filter.eventuallyEq_of_mem (hoL.mem_nhds hz) hHG.symm)
    · have hz1 : z ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
        change 0 < z.re; linarith [not_lt.mp hz]
      exact (ha z hz1).congr (Filter.eventuallyEq_of_mem (hoR.mem_nhds hz1) hHa.symm)

/-- Paper: (5.4.1.8), p. 267.
In a matching pair the first component has an entire extension exactly when the
continued second component has no poles in the left half-plane. -/
theorem mem_sLocalPolarFreeMatching_iff (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻) :
    p ∈ sLocalPolarFreeMatching (F := F) (S := S) χ ↔ p ∈ sLocalZetaMatching (F := F) (S := S) χ ∧
      ∀ s ∈ leftHalf, 0 ≤ meromorphicOrderAt (fun z ↦ ρₛ(χ, z) * p.2.val z) s := by
  refine and_congr_right fun hp => ?_
  exact mem_sLocalPolarFreeMatching_iff_aux (fun z ↦ ρₛ(χ, z)) p.1.val p.2.val
    (sLocalRhoFactor_meromorphic χ)
    (p.1.property.2.1.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re))
    (p.2.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re))
    ((mem_sLocalZetaMatching χ p).mp hp)

/-- The real vertical trace differentiates by one factor of I at each step. -/
private theorem sLocalPolarFreeZetaPair_vertical_deriv (b : B⁻) (a : leftInterval)
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ ↦ b.val ((a.val : ℂ) + (y : ℂ) * Complex.I)) x =
      Complex.I ^ n * iteratedDeriv n b.val ((a.val : ℂ) + (x : ℂ) * Complex.I) := by
  let L (z : ℂ) := (a.val : ℂ) + z * Complex.I
  have hL (z : ℂ) : HasDerivAt L Complex.I z := by
    change HasDerivAt (fun w : ℂ ↦ (a.val : ℂ) + w * Complex.I) Complex.I z
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id z).mul_const Complex.I).const_add (a.val : ℂ)
  have ha : AnalyticOnNhd ℂ b.val leftHalf :=
    b.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re)
  have hn (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k b.val) leftHalf := by
    rw [iteratedDeriv_eq_iterate]
    exact ha.iterated_deriv k
  change iteratedDeriv n (fun y : ℝ ↦ b.val (L y)) x = Complex.I ^ n * iteratedDeriv n b.val (L x)
  induction n generalizing x with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    have hx : L x ∈ leftHalf := by simp [L, Complex.add_re, Complex.mul_re]
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

private theorem sLocalPolarFreeZetaPair_schwartz_deriv_continuous (n : ℕ) :
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
private theorem sLocalPolarFreeZetaPair_continuous_jet (s : ℂ) (hs : s ∈ leftHalf) (n : ℕ) :
    Continuous (fun b : B⁻ ↦ iteratedDeriv n b.val s) := by
  obtain ⟨T, hT, hE⟩ := schwartzBergman_schwartzLine_topology leftInterval isOpen_Iio
    ordConnected_Iio ⟨0, by norm_num⟩
  let a : leftInterval := ⟨s.re, hs⟩
  have hL : (a.val : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
  have hTeq (b : B⁻) : ⇑(T b a) = fun y : ℝ ↦ b.val ((a.val : ℂ) + (y : ℂ) * Complex.I) := by
    funext y
    simpa only [weightedVerticalTrace, pow_zero, one_mul] using hT b a y
  have hC : Continuous (fun b : B⁻ ↦ iteratedDeriv n ((T b a : SchwartzMap ℝ ℂ) : ℝ → ℂ) s.im) :=
    (continuous_apply s.im).comp ((sLocalPolarFreeZetaPair_schwartz_deriv_continuous n).comp
      ((continuous_apply a).comp hE.continuous))
  apply (hC.const_mul ((Complex.I ^ n)⁻¹)).congr
  intro b
  rw [hTeq, sLocalPolarFreeZetaPair_vertical_deriv b a n, hL,
    inv_mul_cancel_left₀ (pow_ne_zero _ Complex.I_ne_zero)]

private theorem sLocalPolarFreeZetaPair_closed_at (ρ : ℂ → ℂ) (s : ℂ) (hs : s ∈ leftHalf)
    (hρ : MeromorphicAt ρ s) :
    IsClosed {b : B⁻ | 0 ≤ meromorphicOrderAt (fun z ↦ ρ z * b.val z) s} := by
  have hb (b : B⁻) : AnalyticAt ℂ b.val s :=
    b.property.2.1.analyticAt ((isOpen_Iio.preimage Complex.continuous_re).mem_nhds hs)
  cases h : meromorphicOrderAt ρ s with
  | top =>
    convert isClosed_univ using 1
    ext b
    simp only [mem_univ, iff_true]
    change 0 ≤ meromorphicOrderAt (ρ * b.val) s
    simp [meromorphicOrderAt_mul hρ (hb b).meromorphicAt, h]
  | coe k =>
    by_cases hk : 0 ≤ k
    · convert isClosed_univ using 1
      ext b
      simp only [mem_univ, iff_true]
      change 0 ≤ meromorphicOrderAt (ρ * b.val) s
      rw [meromorphicOrderAt_mul hρ (hb b).meromorphicAt, h]
      exact add_nonneg (WithTop.coe_nonneg.mpr hk) (hb b).meromorphicOrderAt_nonneg
    · let N := (-k).toNat
      have hN : (N : ℤ) = -k := Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_not_ge hk))
      have he (b : B⁻) : (0 ≤ meromorphicOrderAt (fun z ↦ ρ z * b.val z) s) ↔
          ∀ n < N, iteratedDeriv n b.val s = 0 := by
        change (0 ≤ meromorphicOrderAt (ρ * b.val) s) ↔ _
        rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hb b),
          meromorphicOrderAt_mul hρ (hb b).meromorphicAt, h, (hb b).meromorphicOrderAt_eq]
        cases hord : analyticOrderAt b.val s with
        | top => simp
        | coe m =>
          rw [show (↑m : ℕ∞) = (m : ENat) from rfl, ENat.map_natCast, ← WithTop.coe_add]
          norm_cast
          omega
      have hset : {b : B⁻ | 0 ≤ meromorphicOrderAt (fun z ↦ ρ z * b.val z) s} =
          ⋂ (n : ℕ) (_ : n < N), {b : B⁻ | iteratedDeriv n b.val s = 0} := by
        ext b
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, he]
      rw [hset]
      exact isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
        isClosed_eq (sLocalPolarFreeZetaPair_continuous_jet s hs n) continuous_const

/-- On the left half-plane the pole cancellation conditions are closed in the
Bergman topology, since each is a finite collection of vanishing jets. -/
private theorem sLocalPolarFreeZetaPair_closed_poles (ρ : ℂ → ℂ) (hρ : Meromorphic ρ) :
    IsClosed {p : B⁺ × B⁻ | ∀ s ∈ leftHalf,
      0 ≤ meromorphicOrderAt (fun z ↦ ρ z * p.2.val z) s} := by
  have he : {p : B⁺ × B⁻ | ∀ s ∈ leftHalf, 0 ≤ meromorphicOrderAt (fun z ↦ ρ z * p.2.val z) s} =
      ⋂ (s : ℂ) (_ : s ∈ leftHalf), Prod.snd ⁻¹'
        {b : B⁻ | 0 ≤ meromorphicOrderAt (fun z ↦ ρ z * b.val z) s} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter fun s ↦ isClosed_iInter fun hs ↦
    (sLocalPolarFreeZetaPair_closed_at ρ s hs (hρ s)).preimage continuous_snd

/-- In normal form, agreeing on the right half-plane with an entire function
forces the meromorphic continuation to equal that function everywhere. -/
private theorem sLocalPolarFreeZetaPair_entire_of_extension (f H : ℂ → ℂ)
    (hf : MeromorphicNFOn f univ) (hH : AnalyticOnNhd ℂ H univ)
    (hEq : EqOn f H rightHalf) : AnalyticOnNhd ℂ f univ := by
  have hdiff : MeromorphicOn (fun z ↦ f z - H z) univ :=
    hf.meromorphicOn.sub (fun z hz ↦ (hH z hz).meromorphicAt)
  have h₁ : meromorphicOrderAt (fun z ↦ f z - H z) (1 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hright : (1 : ℂ) ∈ rightHalf := by norm_num [mem_preimage]
    filter_upwards [nhdsWithin_le_nhds ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hright)]
      with z hz using sub_eq_zero.mpr (hEq hz)
  have htop (s : ℂ) : meromorphicOrderAt (fun z ↦ f z - H z) s = ⊤ := by
    by_contra hnot
    exact (hdiff.exists_meromorphicOrderAt_ne_top_iff_forall_mem isConnected_univ).mp
      ⟨s, mem_univ s, hnot⟩ 1 (mem_univ _) h₁
  have he (s : ℂ) : f s = H s := by
    have hne : f =ᶠ[𝓝[≠] s] H := by
      filter_upwards [meromorphicOrderAt_eq_top_iff.mp (htop s)] with z hz
      exact sub_eq_zero.mp hz
    exact ((hf (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hH s (mem_univ s)).meromorphicNFAt).mp hne |>.self_of_nhds
  rwa [funext he]

/-- On a test the two ordinary zeta components agree by the Tate relation on the overlap. -/
private theorem sLocalPolarFreeZetaPair_test_matches (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    let p := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
    EqOn p.1.val (fun z ↦ ρₛ(χ,z) * p.2.val z) overlap := by
  intro p z hz
  have h := sLocalZetaPair_mk χ f
  exact (h.1 hz.1).trans ((existsUnique_sLocalZetaPair_equation χ f z hz).trans
    (congrArg (ρₛ(χ,z) * ·) (h.2 hz.2).symm))

private theorem sLocalPolarFreeZetaPair_test_entire_iff (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    let p := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
    (∀ s ∈ leftHalf, 0 ≤ meromorphicOrderAt (fun z ↦ ρₛ(χ,z) * p.2.val z) s) ↔
      AnalyticOnNhd ℂ (fun z ↦ Zₛ f (normChart(χ) z)) univ := by
  intro p
  have h := mem_sLocalPolarFreeMatching_iff_aux (fun z ↦ ρₛ(χ,z)) p.1.val p.2.val
    (sLocalRhoFactor_meromorphic χ)
    (p.1.property.2.1.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re))
    (p.2.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re))
    (sLocalPolarFreeZetaPair_test_matches χ f)
  have hright := (sLocalZetaPair_mk χ f).1
  constructor
  · intro horders
    obtain ⟨H, hH, hEq⟩ := h.mpr horders
    exact sLocalPolarFreeZetaPair_entire_of_extension _ H (sLocalIdelicZFunction_meromorphic f χ)
      hH (hright.symm.trans hEq.symm)
  · intro ha
    exact h.mp ⟨_, ha, hright.symm⟩

/-- The polar-free range is exactly the part of the ordinary zeta range with the
left pole cancellation conditions. This uses the polar-free representative theorem
of §5.3 for the entire normalized continuation. -/
private theorem sLocalPolarFreeZetaPair_range_inter (χ : PontryaginDual Jₛ)
    (r : RealModels) (c : ComplexModels) :
    range (sLocalPolarFreeZetaPair (F := F) (S := S) χ r c) =
      range (sLocalZetaPair (F := F) (S := S) χ) ∩
        {p : B⁺ × B⁻ | ∀ s ∈ leftHalf, 0 ≤ meromorphicOrderAt (fun z ↦ ρₛ(χ,z) * p.2.val z) s} := by
  let P := polarTests(r, c)
  let K := polarKernel(P, restrict₁(χ))
  let Z := sLocalZetaPair (F := F) (S := S) χ
  let T := sLocalPolarFreeZetaPair (F := F) (S := S) χ r c
  have hk (f : P) : T (K.mkQ f) = Z (Submodule.Quotient.mk f.val) := rfl
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨f, rfl⟩ := K.mkQ_surjective u
    rw [hk]
    exact ⟨⟨_, rfl⟩, (sLocalPolarFreeZetaPair_test_entire_iff χ f.val).mpr
      (sLocalIdelicZFunction_entire_of_polarFree r c f.val f.property χ)⟩
  · rintro ⟨⟨u, rfl⟩, hp⟩
    induction u using Submodule.Quotient.induction_on with
    | H f =>
      have hf := (sLocalPolarFreeZetaPair_test_entire_iff χ f).mp hp
      have hlift := (sLocalIdelicZFunction_entire_iff_eq_polarFree r c χ f).mp hf
      let g : P := hlift.choose
      let f' := g.val
      have he := hlift.choose_spec
      have hfirst : (Z (Submodule.Quotient.mk f')).1 = (Z (Submodule.Quotient.mk f)).1 := by
        apply existsUnique_sLocalZetaPair_ext
        intro z hz
        exact ((sLocalZetaPair_mk χ f').1 hz).trans
          ((he z).symm.trans ((sLocalZetaPair_mk χ f).1 hz).symm)
      have hsecond : (Z (Submodule.Quotient.mk f')).2 = (Z (Submodule.Quotient.mk f)).2 := by
        apply existsUnique_sLocalZetaPair_left_ext χ
        intro z hz
        exact ((sLocalPolarFreeZetaPair_test_matches χ f') hz).symm.trans
          ((congrArg (fun v : B⁺ ↦ v.val z) hfirst).trans (sLocalPolarFreeZetaPair_test_matches χ f hz))
      exact ⟨K.mkQ g, (hk _).trans (Prod.ext hfirst hsecond)⟩

/-- A continuous injection from the quotient of a closed submodule of a strict LF-space
into a Fréchet space is a closed embedding when its range is closed. The open mapping
theorem is applied using the closed intersections with the Fréchet stages. -/
private theorem sLocalPolarFreeZetaPair_embedding_aux {E V : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (hE : IsStrictLFSpace E) (hV : IsFrechetTVS V)
    (P : Submodule ℂ E) (hP : IsClosed (P : Set E)) (K : Submodule ℂ P)
    (T : P ⧸ K →ₗ[ℂ] V) (hc : Continuous T) (hi : Injective T)
    (hR : IsClosed (range T)) : IsClosedEmbedding T := by
  obtain ⟨hT2, S, hmono, hS, hcover, _⟩ := hE
  let R := T.range
  have hR' : IsClosed (R : Set V) := hR
  let Q : P ⧸ K →L[ℂ] R :=
    (⟨T, hc⟩ : (P ⧸ K) →L[ℂ] V).codRestrict R fun x ↦ ⟨x, rfl⟩
  let A : P →L[ℂ] R := Q.comp K.mkQL
  have hsurj : Surjective Q := by
    intro y
    obtain ⟨x, h⟩ := y.property
    exact ⟨x, Subtype.ext h⟩
  let D (k : ℕ) := P.comap (S k).subtype
  let d (k : ℕ) : D k →L[ℂ] P :=
    ((S k).subtypeL.comp (D k).subtypeL).codRestrict P fun x ↦ x.property
  have hD (k : ℕ) : IsFrechetTVS (D k) :=
    sLocalPolarFreeZetaPair_frechet_submodule (hS k) _ (hP.preimage continuous_subtype_val)
  have hinc (k : ℕ) : range (d k) ⊆ range (d (k + 1)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨⟨x.val.val, hmono k.le_succ x.val.property⟩, x.property⟩, rfl⟩
  have hcov (x : P) : ∃ k, x ∈ range (d k) := by
    obtain ⟨k, hk⟩ := hcover x.val
    exact ⟨k, ⟨⟨⟨x.val, hk⟩, x.property⟩, rfl⟩⟩
  have hAf : IsOpenMap A :=
    isOpenMap_of_surjective_toLF
      (isLFSpace_of_isFrechetTVS (sLocalPolarFreeZetaPair_frechet_submodule hV R hR'))
      hD d hinc hcov A (hsurj.comp K.mkQ_surjective)
  have hQf : IsOpenMap Q := by
    intro U hU
    have hU' := hAf (K.mkQ ⁻¹' U) (hU.preimage K.continuous_mkQ)
    have he : A '' (K.mkQ ⁻¹' U) = Q '' U := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨K.mkQ x, hx, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨x, rfl⟩ := K.mkQ_surjective v
        exact ⟨x, hv, rfl⟩
    exact he ▸ hU'
  have hQi : Injective Q := fun _ _ h ↦ hi (congrArg Subtype.val h)
  have hQe := IsOpenEmbedding.of_continuous_injective_isOpenMap Q.continuous hQi hQf
  exact hR'.isClosedEmbedding_subtypeVal.comp
    ⟨hQe.isEmbedding, (range_eq_univ.mpr hsurj).symm ▸ isClosed_univ⟩

/-- Paper: Proposition 5.4.1.4, p. 267.
The zeta pair on the polar-free quotient is a topological embedding with closed range. -/
theorem sLocalPolarFreeZetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ)
    (r : RealModels) (c : ComplexModels) :
    IsClosedEmbedding (sLocalPolarFreeZetaPair (F := F) (S := S) χ r c) := by
  let P := polarTests(r, c)
  let K := polarKernel(P, restrict₁(χ))
  let Q := LinearMap.ker (φω(restrict₁(χ)))
  let i := polarInclusion(P, restrict₁(χ))
  let Z := sLocalZetaPair (F := F) (S := S) χ
  let T := sLocalPolarFreeZetaPair (F := F) (S := S) χ r c
  have hmap (f : P) : i (K.mkQ f) = Q.mkQ f.val := rfl
  have hZ : IsClosedEmbedding Z := sLocalZetaPair_isClosedEmbedding χ
  have hc : Continuous i := by
    apply K.isQuotientMap_mkQ.continuous_iff.mpr
    exact (Q.continuous_mkQ.comp continuous_subtype_val).congr fun f ↦ (hmap f).symm
  have hi : Injective i := by
    apply LinearMap.ker_eq_bot.mp
    change LinearMap.ker (K.mapQ Q P.subtype _) = ⊥
    rw [Submodule.ker_mapQ]
    exact K.mkQ_map_self
  have hR : IsClosed (range T) := by
    show IsClosed (range (sLocalPolarFreeZetaPair (F := F) (S := S) χ r c))
    rw [sLocalPolarFreeZetaPair_range_inter χ r c]
    exact hZ.isClosed_range.inter (sLocalPolarFreeZetaPair_closed_poles _ (sLocalRhoFactor_meromorphic χ))
  have hplus := schwartzBergman_frechet rightInterval isOpen_Ioi ordConnected_Ioi ⟨1, by norm_num⟩
  have hminus := schwartzBergman_frechet leftInterval isOpen_Iio ordConnected_Iio ⟨0, by norm_num⟩
  have hV := sLocalPolarFreeZetaPair_frechet_prod hplus hminus
  have hP : IsClosed (P : Set ℬₛ) := sAdelePolarFree_isClosed r c
  have hE : IsStrictLFSpace ℬₛ := sAdeleSchwartz_strictLF F S
  exact sLocalPolarFreeZetaPair_embedding_aux hE hV P hP K T (hZ.continuous.comp hc)
    (hZ.injective.comp hi) hR

/-- Agreement on the convergence half-plane identifies an entire extension
with the zeta function in meromorphic normal form. -/
private theorem sLocalPolarFreeZetaPair_range_entire {Z H : ℂ → ℂ}
    (hZ : MeromorphicNFOn Z univ) (hH : AnalyticOnNhd ℂ H univ)
    (h : EqOn Z H rightHalf) : AnalyticOnNhd ℂ Z univ := by
  have hdiff := hZ.meromorphicOn.sub (fun z hz ↦ (hH z hz).meromorphicAt)
  have hhalf : ∀ᶠ z in 𝓝 (1 : ℂ), z ∈ rightHalf :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by simp)
  have hnear : Z =ᶠ[𝓝[≠] (1 : ℂ)] H :=
    (hhalf.filter_mono nhdsWithin_le_nhds).mono fun _ hz ↦ h hz
  have htop : meromorphicOrderAt (Z - H) (1 : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (hnear.mono fun _ hz ↦ sub_eq_zero.mpr hz)
  intro z hz
  have hz' := hdiff.meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (1 : ℂ)) hz htop
  have hzEq : Z =ᶠ[𝓝[≠] z] H :=
    (meromorphicOrderAt_eq_top_iff.mp hz').mono fun _ he ↦ sub_eq_zero.mp he
  exact (hH z hz).congr (((hZ hz).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hH z hz).meromorphicNFAt).mp hzEq).symm

/-- Paper: Proposition 5.4.1.4, p. 267.
The image of the polar-free quotient consists exactly of the matching pairs in V. -/
theorem sLocalPolarFreeZetaPair_range (χ : PontryaginDual Jₛ)
    (r : RealModels) (c : ComplexModels) :
    ((sLocalPolarFreeZetaPair (F := F) (S := S) χ r c).range : Set (B⁺ × B⁻)) =
      sLocalPolarFreeMatching (F := F) (S := S) χ := by
  let U := sLocalZetaPair (F := F) (S := S) χ
  let K := LinearMap.ker (φω(restrict₁(χ)))
  let P := polarTests(r, c)
  let A := U.comp K.mkQ
  have hP : (sLocalPolarFreeZetaPair (F := F) (S := S) χ r c).range = P.map A := by
    unfold sLocalPolarFreeZetaPair
    rw [LinearMap.range_comp, Submodule.range_mapQ, Submodule.range_subtype, ← Submodule.map_comp]
  have hA : A.range = sLocalZetaMatching (F := F) (S := S) χ :=
    (LinearMap.range_comp_of_range_eq_top U K.range_mkQ).trans (sLocalZetaPair_range χ)
  rw [hP]
  ext p
  change p ∈ P.map A ↔ p ∈ sLocalPolarFreeMatching (F := F) (S := S) χ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨hA.le (LinearMap.mem_range_self A f), fun s ↦ Zₛ f (normChart(χ) s),
      sLocalIdelicZFunction_entire_of_polarFree r c f hf χ, (sLocalZetaPair_mk χ f).1.symm⟩
  · rintro ⟨hp, H, hH, he⟩
    obtain ⟨f, rfl⟩ := hA.ge hp
    have hf := sLocalPolarFreeZetaPair_range_entire (sLocalIdelicZFunction_meromorphic f χ)
      hH ((sLocalZetaPair_mk χ f).1.symm.trans he.symm)
    obtain ⟨g, hg⟩ := (sLocalIdelicZFunction_entire_iff_eq_polarFree r c χ f).mp hf
    have hright : (A g.val).1 = (A f).1 :=
      existsUnique_sLocalZetaPair_ext ((sLocalZetaPair_mk χ g.val).1.trans
        (fun z hz ↦ (hg z).symm.trans ((sLocalZetaPair_mk χ f).1 hz).symm))
    refine ⟨g.val, g.property, Prod.ext hright ?_⟩
    apply existsUnique_sLocalZetaPair_left_ext χ
    intro z hz
    have hmatch (g : ℬₛ) := (mem_sLocalZetaMatching χ (A g)).mp
      (hA.le (LinearMap.mem_range_self A g)) hz
    exact (hmatch g.val).symm.trans
      ((congrArg (fun b : B⁺ ↦ b.val z) hright).trans (hmatch f))

-- The translation formula restricts by `sLocalZetaPair_translate` and
-- `sAdelePolarFree_translate`.

-- TODO(paper-gap): (5.4.1.11) on p. 270 loses the inverse on the different in the
-- last indicator. Boundedness of the multiplier in (5.4.1.10) alone does not
-- imply the closed-range assertion for (5.4.1.12).
-- TODO(paper-gap): The lexicographic order before (5.4.1.14) on p. 270 does not
-- give the claimed inclusions of the pole sets. The limit used for the Laurent
-- coefficient on p. 271 fails at poles of order greater than its exponent.
-- TODO(paper-gap): The proof of (5.4.1.22) on p. 273 needs a comparison of the
-- quotient topologies. The proposed family in (5.4.1.23) fails to span: at two
-- real places with trivial character and cutoff (0,0) it gives one test. The
-- product Gaussian has a double pole at zero. Dilating one factor by 2 adds
-- log(2) times its leading Laurent coefficient to its residue, giving two
-- independent principal parts. The range theorem needs another argument.

-- TODO(paper-gap): Remark 5.4.1.5 on p. 274 cites part (4) of a theorem with two parts.
-- The local Fréchet assertion is part (2). The global assertion is Corollary
-- 6.2.1.2, via Theorem 6.2.1.1 on isotypes for S with trivial S-class group
-- containing the character's ramification.

end SecondStructure

section Cech

-- The quotient measure in §3.3 is defined with this Borel measurable structure.
local instance instSIdeleQuotientMeasurableSpaceSec4 : MeasurableSpace Jₛ := borel _

local instance instSIdeleGroupLocallyCompactSec4 : LocallyCompactSpace Aₛˣ :=
  (sIdeleGroup_description F S).2.2.1

local instance instSIdeleQuotientT2Sec4 : T2Space Jₛ :=
  letI := isClosed_sProjectedDiagonal (F := F) (S := S)
  inferInstance

local notation "Θₛ" => SLocalAdelicThetaSpace F S
local notation "μₛ" => sLocalQuotientTamagawaMeasure F S
local notation "μweighted" => ((μₛ).withDensity (fun g : Jₛ ↦ ENNReal.ofReal (normℝ(mₛ g))))
local notation "L²ₛ" => MeasureTheory.Lp ℂ 2 μweighted
local notation "Ẽ(" I ")" => ModulatedExponentialDecay (⟨mₛ, hmₛ⟩ : Jₛ →ₜ* ℝ≥0ˣ) I
local notation "reflect(" I ")" => ((fun a : ℝ ↦ 1 - a) ⁻¹' I)

/-- A linear family of pointwise continuous evaluations gives a continuous map into L²
on a Fréchet stage whenever each representative belongs to L². Fatou's lemma makes
the norm lower semicontinuous, so barrelledness gives continuity. -/
private theorem thetaLp_stage {E X : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [FirstCountableTopology E] [BarrelledSpace ℂ E]
    [MeasurableSpace X] (μ : Measure X) (T : E →ₗ[ℂ] Lp ℂ 2 μ) (v : E → X → ℂ)
    (hv : ∀ f, ⇑(T f) =ᵐ[μ] v f) (hc : ∀ x, Continuous fun f ↦ v f x) :
    Continuous T := by
  let p := (normSeminorm ℂ (Lp ℂ 2 μ)).comp T
  have hnorm (f : E) : eLpNorm (v f) 2 μ = ENNReal.ofReal (p f) := by
    rw [← eLpNorm_congr_ae (hv f), ← Lp.eNorm_def]
    exact (ofReal_norm (T f)).symm
  have hm (f : E) := (Lp.aestronglyMeasurable (T f)).congr (hv f)
  have hp : LowerSemicontinuous p := by
    apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro r
    apply IsSeqClosed.isClosed
    intro u f hu huf
    have hr : 0 ≤ r := (norm_nonneg (T (u 0))).trans (hu 0)
    apply (ENNReal.ofReal_le_ofReal_iff hr).mp
    rw [← hnorm]
    exact Lp.eLpNorm_le_of_ae_tendsto (.of_forall fun n ↦ (hnorm (u n)).le.trans
      (ENNReal.ofReal_le_ofReal (hu n))) (fun n ↦ hm (u n)) (hm f)
      (.of_forall fun x ↦ ((hc x).tendsto f).comp huf)
  apply continuous_of_continuousAt_zero T
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto p _ _
  simpa only [map_zero] using (p.continuous_of_lowerSemicontinuous hp).tendsto 0

/-- The half-weight theta function is integrable by absolute convergence of its
Mellin integral. The two theta estimates bound it pointwise, hence it is also in L². -/
private theorem sLocalThetaWeightedL2_mem (f : ℬₛ) :
    MemLp (sLocalAdelicThetaOnClasses F S f) 2 μweighted := by
  let : BorelSpace Jₛ := ⟨rfl⟩
  let θ := sLocalAdelicThetaOnClasses F S f
  let w (g : Jₛ) := (mₛ g).val
  have hw (g : Jₛ) : 0 < (w g : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hm : Measurable w := (Units.continuous_val.comp hmₛ).measurable
  let V (g : Jₛ) := θ g * ((w g : ℝ) : ℂ) ^ (1/2 : ℂ)
  have hnorm (g : Jₛ) : ‖V g‖ = (w g : ℝ) ^ (1/2 : ℝ) * ‖θ g‖ := by
    dsimp only [V]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hw g),
      show (1/2 : ℂ).re = 1/2 by norm_num, mul_comm]
  have hI : Integrable V μₛ := by
    have h := sLocalThetaMellinIntegral_integrable f (normChart((1 : PontryaginDual Jₛ)) (1/2))
      ⟨1, 1/2, by norm_num, rfl⟩
    apply h.congr
    filter_upwards with g
    change θ g * (((1 : PontryaginDual Jₛ) g : ℂ) * ((w g : ℝ) : ℂ) ^ (1/2 : ℂ)) = V g
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, V, w]
  have hB := Bornology.isVonNBounded_singleton (𝕜 := ℂ) f
  obtain ⟨A, hA, hsmall⟩ := sLocalAdelicTheta_norm_pow_bounded_threshold_one F S
    (1/2) (by norm_num) {f} hB
  obtain ⟨B, hB', hlarge⟩ := sLocalAdelicTheta_decay_bounded_threshold_one F S {f} hB 1
  have hK := (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1))
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn θ.continuous.continuousOn
  have hbound (g : Jₛ) : ‖V g‖ ≤ max (max A B) D := by
    rw [hnorm]
    rcases lt_trichotomy (w g : ℝ) 1 with hl | he | hg
    · obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      have h : ‖((w (QuotientGroup.mk u) : ℝ) ^ (1/2 : ℝ)) • sLocalAdelicTheta F S f u‖ ≤ A := hsmall f rfl u hl
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (hw _).le _)] at h
      simpa only [θ, sLocalAdelicThetaOnClasses_mk] using
        h.trans ((le_max_left A B).trans (le_max_left _ D))
    · have he' : mₛ g = 1 := Units.ext (NNReal.eq he)
      rw [he, Real.one_rpow, one_mul]
      exact (hD g he').trans (le_max_right _ _)
    · obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      have h := hlarge f rfl u hg
      rw [pow_one] at h
      change (w _ : ℝ) ^ (1/2 : ℝ) * ‖sLocalAdelicThetaOnClasses F S f _‖ ≤ _
      rw [sLocalAdelicThetaOnClasses_mk]
      have hwle : (w (QuotientGroup.mk u) : ℝ) ^ (1/2 : ℝ) ≤ (w (QuotientGroup.mk u) : ℝ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hg.le
          (show (1/2 : ℝ) ≤ 1 by norm_num)
      refine (mul_le_mul hwle h (norm_nonneg _) (hw _).le).trans ?_
      change (w (QuotientGroup.mk u) : ℝ) * (B * (w (QuotientGroup.mk u) : ℝ)⁻¹) ≤ _
      rw [mul_left_comm, mul_inv_cancel₀ (hw _).ne', mul_one]
      exact (le_max_right A B).trans (le_max_left _ D)
  have hs := hI.norm.bdd_mul hI.norm.aestronglyMeasurable
    (.of_forall fun g ↦ (Real.norm_of_nonneg (norm_nonneg (V g))).le.trans (hbound g))
  apply (memLp_two_iff_integrable_sq_norm θ.continuous.aestronglyMeasurable).mpr
  simp only [ENNReal.ofReal_coe_nnreal]
  apply (integrable_withDensity_iff_integrable_coe_smul hm).mpr
  apply hs.congr (.of_forall fun g ↦ ?_)
  change ‖V g‖ * ‖V g‖ = (w g : ℝ) * ‖θ g‖ ^ 2
  rw [← sq, hnorm, mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (hw g).le]

/-- Paper: (5.4.2.1), p. 274.
The theta test map is continuous into the weighted L² space, and its class is the
almost-everywhere class of the theta function of the test. -/
private theorem sLocalThetaWeightedL2_testMap_continuous :
    ∃ L : ℬₛ →L[ℂ] L²ₛ, ∀ f : ℬₛ,
      ((L f : Jₛ → ℂ)) =ᵐ[μweighted] sLocalAdelicThetaOnClasses F S f := by
  let θ : ℬₛ →ₗ[ℂ] (Jₛ → ℂ) :=
    LinearMap.pi fun g ↦ (ContinuousMap.evalCLM ℂ (Quotient.out g)).toLinearMap.comp
      (sLocalAdelicTheta F S)
  have hθ (f : ℬₛ) (g : Jₛ) : θ f g = sLocalAdelicThetaOnClasses F S f g := by
    change sLocalAdelicTheta F S f g.out = _
    rw [← sLocalAdelicThetaOnClasses_mk, QuotientGroup.out_eq']
  have h (f : ℬₛ) : MemLp (θ f) 2 μweighted :=
    (sLocalThetaWeightedL2_mem f).ae_eq (.of_forall fun g ↦ (hθ f g).symm)
  let L : ℬₛ →ₗ[ℂ] L²ₛ :=
    { toFun := fun f ↦ (h f).toLp _
      map_add' := fun f g ↦ by simp only [map_add]; exact (h f).toLp_add (h g)
      map_smul' := fun c f ↦ by simp only [map_smul, RingHom.id_apply]; exact (h f).toLp_const_smul c }
  have hL (f : ℬₛ) : ⇑(L f) =ᵐ[μweighted] θ f := (h f).coeFn_toLp
  refine ⟨⟨L, ?_⟩, fun f ↦ (hL f).trans (.of_forall (hθ f))⟩
  apply SchwartzBruhat.continuous_of_continuous_comp_ofStage
  intro a e
  let : FirstCountableTopology (SchwartzBruhatStage e) :=
    elementarySchwartz_withSeminorms.firstCountableTopology
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  exact thetaLp_stage μweighted (L.comp (SchwartzBruhat.ofStage a e))
    (fun u ↦ θ (SchwartzBruhat.ofStage a e u)) (fun u ↦ hL _)
    (fun x ↦ (sLocalAdelicTheta_continuous_eval (F := F) (S := S) x.out).comp
      (SchwartzBruhat.continuous_ofStage a e))

/-- The S-local theta kernel is exactly the kernel of the theta class function. -/
private theorem sLocalThetaWeightedL2_theta_zero_iff (f : ℬₛ) :
    (sLocalAdelicTheta F S) f = 0 ↔ sLocalAdelicThetaOnClasses F S f = 0 := by
  constructor
  · intro h
    refine ContinuousMap.ext fun x ↦ ?_
    induction x using QuotientGroup.induction_on with
    | H g => rw [sLocalAdelicThetaOnClasses_mk, h]; rfl
  · intro h
    refine ContinuousMap.ext fun g ↦ ?_
    have := DFunLike.congr_fun h (QuotientGroup.mk g)
    rwa [sLocalAdelicThetaOnClasses_mk] at this

/-- A continuous function on the S-idele class group that vanishes almost everywhere for the
norm-weighted Tamagawa measure vanishes identically. -/
private theorem sLocalThetaWeightedL2_ae_zero (θ : Jₛ → ℂ) (hθ : Continuous θ)
    (h : θ =ᵐ[μweighted] 0) : θ = 0 := by
  let : BorelSpace Jₛ := ⟨rfl⟩
  have hμ : (μₛ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  have hpos : (μₛ).IsOpenPosMeasure := hμ.toIsOpenPosMeasure
  have hUopen : IsOpen {x : Jₛ | θ x ≠ 0} := isOpen_ne.preimage hθ
  by_contra hne
  have hUne : ({x : Jₛ | θ x ≠ 0} : Set Jₛ).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    apply hne
    funext x
    have hx : x ∉ ({y : Jₛ | θ y ≠ 0} : Set Jₛ) := by rw [hcon]; exact Set.notMem_empty x
    simpa using hx
  have hzero : μweighted {x : Jₛ | θ x ≠ 0} = 0 := MeasureTheory.ae_iff.mp h
  rw [withDensity_apply _ hUopen.measurableSet] at hzero
  have hw : Continuous fun x : Jₛ ↦ normℝ(mₛ x) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hmₛ)
  have hsupp : Function.support (fun x : Jₛ ↦ ENNReal.ofReal (normℝ(mₛ x))) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have h1 : (((mₛ x : ℝ≥0ˣ).val : ℝ≥0) : ℝ) ≠ 0 := by
      rw [NNReal.coe_ne_zero]
      exact (mₛ x).ne_zero
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm h1)
  have hpos' : 0 < ∫⁻ x in {x : Jₛ | θ x ≠ 0},
      ENNReal.ofReal (normℝ(mₛ x)) ∂(μₛ) := by
    refine (setLIntegral_pos_iff (f := fun x : Jₛ ↦ ENNReal.ofReal (normℝ(mₛ x)))
      hw.measurable.ennreal_ofReal (s := {x : Jₛ | θ x ≠ 0})).mpr ?_
    rw [hsupp, univ_inter]
    exact lt_of_le_of_ne bot_le (Ne.symm (hpos.open_pos _ hUopen hUne))
  rw [hzero] at hpos'
  exact lt_irrefl _ hpos'

/-- A continuous linear map into the weighted L² space that represents every theta class
kills the theta kernel. -/
private theorem sLocalThetaWeightedL2_ker_eq_zero (L : ℬₛ →L[ℂ] L²ₛ)
    (hL : ∀ f : ℬₛ, ((L f : Jₛ → ℂ)) =ᵐ[μweighted] sLocalAdelicThetaOnClasses F S f)
    {f : ℬₛ} (hf : sLocalAdelicThetaOnClasses F S f = 0) : L f = 0 := by
  refine Lp.ext ?_
  refine (hL f).trans ?_
  rw [hf]
  exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μweighted) |>.symm

/-- The continuous linear map induced on a quotient by a continuous linear map whose kernel
contains the subspace. -/
private def sLocalThetaWeightedL2_liftQCLM {M Y : Type*} [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace M] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (K : Submodule ℂ M) (T : M →L[ℂ] Y) (h : K ≤ LinearMap.ker T.toLinearMap) :
    (M ⧸ K) →L[ℂ] Y :=
  ⟨K.liftQ T.toLinearMap h, K.isQuotientMap_mkQ.continuous_iff.mpr T.continuous⟩

/-- The induced map agrees with the original one on representatives. -/
private theorem sLocalThetaWeightedL2_liftQCLM_apply {M Y : Type*} [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace M] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (K : Submodule ℂ M) (T : M →L[ℂ] Y) (h : K ≤ LinearMap.ker T.toLinearMap) (x : M) :
    sLocalThetaWeightedL2_liftQCLM K T h (Submodule.Quotient.mk x) = T x :=
  Submodule.liftQ_apply K T.toLinearMap x

/-- A continuous linear map out of a quotient is determined by its values on representatives. -/
private theorem sLocalThetaWeightedL2_liftQCLM_unique {M Y : Type*} [AddCommGroup M]
    [Module ℂ M] [TopologicalSpace M] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (K : Submodule ℂ M) (T : M →L[ℂ] Y) (h : K ≤ LinearMap.ker T.toLinearMap)
    (S' : (M ⧸ K) →L[ℂ] Y) (hS' : ∀ x : M, S' (Submodule.Quotient.mk x) = T x) :
    S' = sLocalThetaWeightedL2_liftQCLM K T h := by
  refine DFunLike.coe_injective (funext fun x ↦ ?_)
  obtain ⟨m, rfl⟩ := K.mkQ_surjective x
  rw [Submodule.mkQ_apply, hS' m, sLocalThetaWeightedL2_liftQCLM_apply]

/-- Paper: (5.4.2.1), p. 274.
The ordinary theta quotient injects continuously into L² for the norm-weighted
quotient Tamagawa measure. The map keeps the almost-everywhere class of the theta
function attached to a test representative. -/
theorem existsUnique_sLocalThetaWeightedL2 :
    ∃! j : Θₛ →L[ℂ] L²ₛ, Injective j ∧ ∀ f : ℬₛ,
      ((j (Submodule.Quotient.mk f)) : Jₛ → ℂ) =ᵐ[μweighted] sLocalAdelicThetaOnClasses F S f := by
  classical
  let L : ℬₛ →L[ℂ] L²ₛ :=
    (show ℬₛ →L[ℂ] L²ₛ from
      (sLocalThetaWeightedL2_testMap_continuous (F := F) (S := S)).choose)
  have hL : ∀ f : ℬₛ,
      ((L f : Jₛ → ℂ)) =ᵐ[μweighted] sLocalAdelicThetaOnClasses F S f :=
    (sLocalThetaWeightedL2_testMap_continuous (F := F) (S := S)).choose_spec
  have hker : LinearMap.ker (sLocalAdelicTheta F S) ≤ LinearMap.ker L.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    exact sLocalThetaWeightedL2_ker_eq_zero L hL ((sLocalThetaWeightedL2_theta_zero_iff f).mp hf)
  have hker' : LinearMap.ker L.toLinearMap ≤ LinearMap.ker (sLocalAdelicTheta F S) := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    refine (sLocalThetaWeightedL2_theta_zero_iff f).mpr (ContinuousMap.ext fun x => ?_)
    have h1 : ((L f : Jₛ → ℂ)) =ᵐ[μweighted] ((0 : L²ₛ) : Jₛ → ℂ) := by
      filter_upwards with y
      exact congrArg (fun u : L²ₛ => (u : Jₛ → ℂ) y) hf
    have h2 : ((L f : Jₛ → ℂ)) =ᵐ[μweighted] (0 : Jₛ → ℂ) :=
      h1.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μweighted))
    have h3 : (⇑(sLocalAdelicThetaOnClasses F S f) : Jₛ → ℂ) =ᵐ[μweighted] 0 :=
      (hL f).symm.trans h2
    have hz : (⇑(sLocalAdelicThetaOnClasses F S f) : Jₛ → ℂ) = 0 :=
      sLocalThetaWeightedL2_ae_zero (⇑(sLocalAdelicThetaOnClasses F S f))
        (sLocalAdelicThetaOnClasses F S f).continuous h3
    exact congrFun hz x
  let j : Θₛ →L[ℂ] L²ₛ :=
    { toLinearMap := (LinearMap.ker (sLocalAdelicTheta F S)).liftQ L.toLinearMap hker
      cont := (LinearMap.ker (sLocalAdelicTheta F S)).isQuotientMap_mkQ.continuous_iff.mpr L.continuous }
  have hj : ∀ f : ℬₛ, j (Submodule.Quotient.mk f) = L f := fun f ↦
    Submodule.liftQ_apply (p := LinearMap.ker (sLocalAdelicTheta F S)) L.toLinearMap f
  have hbot : LinearMap.ker j.toLinearMap = ⊥ :=
    Submodule.ker_liftQ_eq_bot (p := LinearMap.ker (sLocalAdelicTheta F S)) L.toLinearMap hker hker'
  refine ⟨j, ⟨?_, ?_⟩, ?_⟩
  · exact LinearMap.ker_eq_bot.mp hbot
  · intro f
    rw [hj f]
    exact hL f
  · intro j' hj'
    refine sLocalThetaWeightedL2_liftQCLM_unique (LinearMap.ker (sLocalAdelicTheta F S)) L hker j' fun f ↦ ?_
    refine Lp.ext ?_
    filter_upwards [hj'.2 f, hL f] with y h1 h2
    rw [h1, h2]

local notation "weightedTheta" =>
  (show Θₛ →L[ℂ] L²ₛ from (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose)

/-- The L² norm for a measure with a real density is the square root of the weighted
integral of the squared absolute value of any representative. -/
private theorem sLocalThetaWeightedL2_norm_aux {X : Type*} [MeasurableSpace X] (μ : Measure X) (w : X → ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (F : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))) (θ : X → ℂ)
    (hF : (F : X → ℂ) =ᵐ[μ.withDensity fun x ↦ ENNReal.ofReal (w x)] θ) :
    ‖F‖ = Real.sqrt (∫ x, ‖θ x‖ ^ 2 * w x ∂μ) := by
  rw [Lp.norm_def, (Lp.memLp F).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _),
    Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div]
  congr 1
  rw [integral_congr_ae (hF.mono fun x (hx : F x = θ x) ↦
      show ‖F x‖ ^ (2 : ℝ) = ‖θ x‖ ^ (2 : ℝ) by rw [hx]),
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [ENNReal.toReal_ofReal (hw0 x), Real.rpow_two, smul_eq_mul, mul_comm]

/-- Paper: (5.4.2.1), p. 274.
The norm of the embedded class equals the square root of the weighted integral
of the squared absolute value of its theta function. -/
theorem sLocalThetaWeightedL2_norm (f : ℬₛ) :
    ‖weightedTheta (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g : Jₛ, ‖sLocalAdelicThetaOnClasses F S f g‖ ^ 2 *
        normℝ(mₛ g) ∂μₛ) := by
  have h := (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose_spec.2 f
  have hc : Continuous fun g : Jₛ ↦ normℝ(mₛ g) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hmₛ)
  have : BorelSpace Jₛ := ⟨rfl⟩
  exact sLocalThetaWeightedL2_norm_aux μₛ (fun g ↦ normℝ(mₛ g)) hc.measurable
    (fun _ ↦ NNReal.coe_nonneg _) _ _ h

variable (F S) in
/-- Paper: (5.4.2.2), p. 274.
The weighted Hilbert completion is realized as the closure of the theta image
in the weighted L² space.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev SLocalThetaL2 :=
  ↥(LinearMap.range ((weightedTheta).toLinearMap)).topologicalClosure

local notation "completionMap" => (show Θₛ →ₗ[ℂ] SLocalThetaL2 F S from
  (weightedTheta).toLinearMap.codRestrict
    (LinearMap.range (weightedTheta).toLinearMap).topologicalClosure
    (fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)))

section DenseHelper
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul ℂ N]

private theorem denseRange_codRestrict_topologicalClosure (f : M →ₗ[ℂ] N)
    (h : ∀ x, f x ∈ (LinearMap.range f).topologicalClosure) :
    DenseRange (f.codRestrict (LinearMap.range f).topologicalClosure h) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  intro x
  rw [← Set.range_comp]
  exact x.2

end DenseHelper

/-- Paper: (5.4.2.2), p. 274.
The test-function image is dense in the chosen model of the completion. -/
theorem sLocalThetaL2_dense : DenseRange completionMap :=
  denseRange_codRestrict_topologicalClosure _ _

/-- The Fourier transform is a linear automorphism of the S-adelic tests.
Its fourth power is the identity by Fourier inversion. -/
private theorem existsUnique_sLocalThetaL2Fourier_testEquiv :
    ∃ T : ℬₛ ≃ₗ[ℂ] ℬₛ, ∀ f, T f = Fourierₛ f := by
  let G := Multiplicative Aₛ
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace Aₛ := inferInstanceAs
    (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space G := ‹T2Space Aₛ›
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace Aₛ)
  let : SigmaCompactSpace Aₛ := inferInstanceAs (SigmaCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let : BorelSpace Aₛ := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace G := ‹BorelSpace Aₛ›
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have hμ : (sAdditiveTamagawaMeasure F S).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace (sAdditiveTamagawaMeasure F S)
  obtain ⟨e, he, _⟩ := sAdditiveTamagawaMeasure_selfDual F S
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_comp_equivCLM e
  let T := P.comp fourier.toContinuousLinearMap
  have hT (f : ℬₛ) : T f = Fourierₛ f := by
    apply Subtype.ext
    funext y
    change P (fourier f) y = tamagawaFourier _ _ _ y.toAdd
    exact (hP _ y).trans (((hfourier f).2 (e y)).trans
      (tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ by
        rw [mul_comm x y.toAdd]
        exact he y.toAdd x)).symm)
  have hfour (f : ℬₛ) : T (T (T (T f))) = f := by
    simp only [hT]
    apply Subtype.ext
    funext y
    change Fourierₛ (Fourierₛ (Fourierₛ (Fourierₛ f))) (Multiplicative.ofAdd y.toAdd) = f y
    rw [sLocal_fourier_inversion, sLocal_fourier_inversion, neg_neg]
    rfl
  have hleft : LeftInverse (fun f ↦ T (T (T f))) T := hfour
  have hright : RightInverse (fun f ↦ T (T (T f))) T := hfour
  exact ⟨LinearEquiv.ofBijective T.toLinearMap ⟨hleft.injective, hright.surjective⟩, hT⟩

/-- Weighting the theta function by the square root of the idelic norm gives
an integrable function whose ordinary L² norm is the weighted theta norm. -/
private theorem existsUnique_sLocalThetaL2Fourier_weighted (u : ℬₛ) :
    let v := fun g : Jₛ ↦ sLocalAdelicThetaOnClasses F S u g *
      ((normℝ(mₛ g) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
    Integrable v μₛ ∧ MemLp v 2 μₛ ∧
      (eLpNorm v 2 μₛ).toReal = ‖weightedTheta (Submodule.Quotient.mk u)‖ := by
  let : BorelSpace Jₛ := ⟨rfl⟩
  let w (g : Jₛ) := (mₛ g).val
  let half : ℂ := 1 / 2
  let V (g : Jₛ) := sLocalAdelicThetaOnClasses F S u g * ((w g : ℝ) : ℂ) ^ half
  change Integrable V μₛ ∧ MemLp V 2 μₛ ∧ _
  have hh : half.re = 1 / 2 := by norm_num [half]
  have hhalf : 0 < half.re := by rw [hh]; norm_num
  have hI : Integrable V μₛ := by
    have h := sLocalThetaMellinIntegral_integrable u (normChart((1 : PontryaginDual Jₛ)) half)
      ⟨1, half, hhalf, rfl⟩
    apply h.congr
    filter_upwards with g
    change sLocalAdelicThetaOnClasses F S u g *
      (((1 : PontryaginDual Jₛ) g : ℂ) * ((w g : ℝ) : ℂ) ^ half) = V g
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, V]
  have hw : Measurable w := (Units.continuous_val.comp hmₛ).measurable
  have hsquare (g : Jₛ) :
      ‖V g‖ ^ 2 = (w g : ℝ) * ‖sLocalAdelicThetaOnClasses F S u g‖ ^ 2 := by
    have hwpos : 0 < (w g : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (mₛ g).ne_zero)
    dsimp only [V]
    rw [norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos hwpos, hh,
      ← Real.sqrt_eq_rpow, Real.sq_sqrt hwpos.le, mul_comm]
  have hL : MemLp V 2 μₛ := by
    have hae := (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose_spec.2 u
    have hweighted := MemLp.ae_eq hae (Lp.memLp (weightedTheta (Submodule.Quotient.mk u)))
    have hsq := (memLp_two_iff_integrable_sq_norm hweighted.aestronglyMeasurable).mp hweighted
    apply (memLp_two_iff_integrable_sq_norm hI.aestronglyMeasurable).mpr
    simp_rw [hsquare]
    exact (integrable_withDensity_iff_integrable_coe_smul hw).mp
      (by simpa only [ENNReal.ofReal_coe_nnreal] using hsq)
  refine ⟨hI, hL, ?_⟩
  change (eLpNorm V 2 μₛ).toReal = _
  rw [sLocalThetaWeightedL2_norm, hL.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _),
    Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div]
  simp_rw [Real.rpow_two, hsquare, mul_comm (w _ : ℝ), w]

/-- Fourier transforms with equal moduli after inversion have equal L² norms. -/
private theorem existsUnique_sLocalThetaL2Fourier_plancherel
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] {u v : G → ℂ}
    (hu : Integrable u μ) (hv : Integrable v μ) (hu₂ : MemLp u 2 μ) (hv₂ : MemLp v 2 μ)
    (h : ∀ χ : PontryaginDual G, ‖lcaFourier μ u χ‖ = ‖lcaFourier μ v χ⁻¹‖) :
    eLpNorm u 2 μ = eLpNorm v 2 μ := by
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨ν, hν, _⟩ := lcaPlancherelMeasure_existsUnique μ
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨hFu, hNu⟩ := hν.2.2 u hu hu₂
  obtain ⟨hFv, hNv⟩ := hν.2.2 v hv hv₂
  have hinv := Measure.measurePreserving_inv ν
  have hnorm := eLpNorm_congr_norm_ae (p := 2) hFu.aestronglyMeasurable
    (hFv.aestronglyMeasurable.comp_quasiMeasurePreserving hinv.quasiMeasurePreserving)
    (.of_forall h)
  calc
    _ = eLpNorm (lcaFourier μ u) 2 ν := hNu.symm
    _ = eLpNorm (lcaFourier μ v ∘ Inv.inv) 2 ν := hnorm
    _ = eLpNorm (lcaFourier μ v) 2 ν := eLpNorm_comp_measurePreserving hFv.aestronglyMeasurable hinv
    _ = _ := hNv

/-- Plancherel on the S-idele quotient identifies the norm in (5.4.2.1)
with the Mellin norm on the critical line. The correcting factor has modulus
one there, and dualizing the character preserves the Plancherel measure. -/
private theorem existsUnique_sLocalThetaL2Fourier_norm (f : ℬₛ) :
    ‖weightedTheta (Submodule.Quotient.mk (Fourierₛ f))‖ =
      ‖weightedTheta (Submodule.Quotient.mk f)‖ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Aₛˣ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : BorelSpace Jₛ := ⟨rfl⟩
  have hWeil := sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)
  let : (μₛ).IsHaarMeasure := hWeil.1
  let : (μₛ).Regular := hWeil.2.1
  let half : ℂ := 1 / 2
  let V (u : ℬₛ) (g : Jₛ) := sLocalAdelicThetaOnClasses F S u g * (normℝ(mₛ g) : ℂ) ^ half
  have hh : half.re = 1 / 2 := by norm_num [half]
  have hhalf : 0 < half.re := by rw [hh]; norm_num
  have hF (u : ℬₛ) (χ : PontryaginDual Jₛ) :
      lcaFourier μₛ (V u) χ = Zₛ u (normChart(χ⁻¹) half) := by
    have hZ : Zₛ u (normChart(χ⁻¹) half) =
        sLocalIdelicZetaIntegral u (normChart(χ⁻¹) half) :=
      sLocalIdelicZFunction_eq_integral u ⟨χ⁻¹, half, hhalf, rfl⟩
    have hM : sLocalThetaMellinIntegral u (normChart(χ⁻¹) half) =
        sLocalIdelicZetaIntegral u (normChart(χ⁻¹) half) :=
      sLocalThetaMellinIntegral_eq_zeta u ⟨χ⁻¹, half, hhalf, rfl⟩
    refine Eq.trans ?_ (hM.trans hZ.symm)
    apply integral_congr_ae
    filter_upwards with g
    change (sLocalAdelicThetaOnClasses F S u g * (normℝ(mₛ g) : ℂ) ^ half) * star (χ g : ℂ) =
      sLocalAdelicThetaOnClasses F S u g * (((χ⁻¹) g : ℂ) * (normℝ(mₛ g) : ℂ) ^ half)
    rw [show (χ⁻¹) g = (χ g)⁻¹ from rfl, Circle.coe_inv_eq_conj]
    change (sLocalAdelicThetaOnClasses F S u g * (normℝ(mₛ g) : ℂ) ^ half) * star (χ g : ℂ) =
      sLocalAdelicThetaOnClasses F S u g * (star (χ g : ℂ) * (normℝ(mₛ g) : ℂ) ^ half)
    simpa only [mul_assoc] using mul_right_comm (sLocalAdelicThetaOnClasses F S u g)
      ((normℝ(mₛ g) : ℂ) ^ half) (star (χ g : ℂ))
  have heq (χ : PontryaginDual Jₛ) :
      ‖lcaFourier μₛ (V f) χ‖ = ‖lcaFourier μₛ (V (Fourierₛ f)) χ⁻¹‖ := by
    have hFE := existsUnique_sLocalZetaPair_equation χ⁻¹ f half
      (show half.re ∈ overlapInterval by rw [hh]; norm_num)
    have hreflect : 1 - half = half := by dsimp [half]; ring
    simp only [hreflect] at hFE
    calc
      _ = ‖Zₛ f (normChart(χ⁻¹) half)‖ := congrArg norm (hF f χ)
      _ = ‖ρₛ(χ⁻¹, half) * Zₛ (Fourierₛ f) (normChart((χ⁻¹)⁻¹) half)‖ :=
        congrArg norm hFE
      _ = ‖Zₛ (Fourierₛ f) (normChart((χ⁻¹)⁻¹) half)‖ := by
        rw [norm_mul]
        have hrho : ‖ρₛ(χ⁻¹, half)‖ = 1 := sLocalRhoFactor_norm_criticalLine χ⁻¹ half hh
        exact (congrArg (· * _) hrho).trans (one_mul _)
      _ = _ := congrArg norm (hF (Fourierₛ f) χ⁻¹).symm
  have hf := existsUnique_sLocalThetaL2Fourier_weighted f
  have hFourier := existsUnique_sLocalThetaL2Fourier_weighted (Fourierₛ f)
  dsimp only at hf hFourier
  have hnorm := existsUnique_sLocalThetaL2Fourier_plancherel (G := Jₛ)
    μₛ (u := V f) (v := V (Fourierₛ f)) hf.1 hFourier.1 hf.2.1 hFourier.2.1 heq
  exact hFourier.2.2.symm.trans ((congrArg ENNReal.toReal hnorm).symm.trans hf.2.2)

/-- An automorphism preserving the norm of a dense linear image extends
uniquely to a linear isometry equivalence on the completion. -/
private theorem existsUnique_sLocalThetaL2Fourier_extend
    {E H : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (K : Submodule ℂ E) (M : (E ⧸ K) →ₗ[ℂ] H) (hd : DenseRange M)
    (T : E ≃ₗ[ℂ] E) (transform : E → E) (hT : ∀ x, T x = transform x)
    (hn : ∀ x, ‖M (K.mkQ (transform x))‖ = ‖M (K.mkQ x)‖) :
    ∃! e : H ≃ₗᵢ[ℂ] H, ∀ x, e (M (K.mkQ x)) = M (K.mkQ (transform x)) := by
  let j := M.comp K.mkQ
  have hj : DenseRange j := by
    apply hd.mono
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := K.mkQ_surjective y
    exact ⟨x, rfl⟩
  have hnorm (x : E) : ‖j (T x)‖ = ‖j x‖ :=
    (congrArg (fun z ↦ ‖j z‖) (hT x)).trans (hn x)
  let e := T.extendOfIsometry j j hj hj hnorm
  have he (x : E) : e (j x) = j (transform x) :=
    (T.extendOfIsometry_eq j j hj hj hnorm x).trans (congrArg j (hT x))
  refine ⟨e, he, fun e' he' ↦ ?_⟩
  apply LinearIsometryEquiv.ext
  exact congrFun (hj.equalizer e'.continuous e.continuous
    (funext fun x ↦ (he' x).trans (he x).symm))

/-- Paper: (5.4.2.1)–(5.4.2.2), p. 274.
S-local Fourier transform has a unique unitary extension to the weighted completion,
given on theta classes by Fourier transform of the test representative. -/
theorem existsUnique_sLocalThetaL2Fourier :
    ∃! e : SLocalThetaL2 F S ≃ₗᵢ[ℂ] SLocalThetaL2 F S, ∀ f : ℬₛ,
      e (completionMap (Submodule.Quotient.mk f)) =
        completionMap (Submodule.Quotient.mk (Fourierₛ f)) := by
  refine (existsUnique_sLocalThetaL2Fourier_testEquiv (F := F) (S := S)).elim fun T hT ↦ ?_
  let K := LinearMap.ker (sLocalAdelicTheta F S)
  exact existsUnique_sLocalThetaL2Fourier_extend (H := SLocalThetaL2 F S)
    K completionMap (sLocalThetaL2_dense (F := F) (S := S)) T Fourierₛ hT
    (fun f ↦ existsUnique_sLocalThetaL2Fourier_norm f)

local notation "weightedFourier" =>
  (show SLocalThetaL2 F S ≃ₗᵢ[ℂ] SLocalThetaL2 F S from
    (existsUnique_sLocalThetaL2Fourier (F := F) (S := S)).exists.choose)

local notation "decayEval(" I ", " g ")" =>
  (LinearMap.proj (g : Jₛ)).comp (modulatedExponentialDecaySubmodule
    (⟨mₛ, hmₛ⟩ : Jₛ →ₜ* ℝ≥0ˣ) (I)).subtype

/-- Paper: (5.4.2.3), p. 275.
The norm-one isotype in the weighted Schwartz–Bruhat space is the common
eigenspace for inverse left translation. -/
def sLocalDecayIsotype (I : Set ℝ) (ω : PontryaginDual J₁) : Submodule ℂ Ẽ(I) :=
  ⨅ u : J₁, ⨅ g : Jₛ, LinearMap.ker
    (decayEval(I, u.val⁻¹ * g) - (ω u : ℂ) • decayEval(I, g))

local notation "Eω(" I ", " ω ")" => ↥(sLocalDecayIsotype (F := F) (S := S) (I) (ω))

/-- Paper: (5.4.2.3), p. 275.
A weighted test function lies in the isotype exactly when it obeys the
norm-one translation law at every idele class. -/
theorem mem_sLocalDecayIsotype (I : Set ℝ) (ω : PontryaginDual J₁) (φ : Ẽ(I)) :
    φ ∈ sLocalDecayIsotype (F := F) (S := S) I ω ↔
      ∀ (u : J₁) (g : Jₛ), φ.val (u.val⁻¹ * g) = (ω u : ℂ) * φ.val g := by
  have criterion {U X E : Type _} [AddCommGroup E] [Module ℂ E]
      (ev : X → E →ₗ[ℂ] ℂ) (shift : U → X → X) (c : U → ℂ) (f : E) :
      f ∈ (⨅ u, ⨅ x, LinearMap.ker (ev (shift u x) - c u • ev x)) ↔
        ∀ u x, ev (shift u x) f = c u * ev x f := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]
  exact criterion (fun g : Jₛ ↦ decayEval(I, g)) (fun (u : J₁) g ↦ u.val⁻¹ * g)
    (fun u ↦ (ω u : ℂ)) φ

/-- A submodule cut out by the coordinate translation law is the isotype of any action
realizing inverse translation on coordinates. -/
private theorem sLocalDecayIsotype_eq_actionIsotype_aux {H E : Type*} [Group H]
    [TopologicalSpace H] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (K : Subgroup H)
    (val : E → H → ℂ) (hval : Injective val)
    (hsmul : ∀ (c : ℂ) (f : E), val (c • f) = c • val f) (P : Submodule ℂ E)
    (ω : PontryaginDual K)
    (hP : ∀ φ, φ ∈ P ↔ ∀ (u : K) (g : H), val φ (u.val⁻¹ * g) = (ω u : ℂ) * val φ g)
    (A : H →* (E →L[ℂ] E)) (hA : ∀ (g : H) (f : E) (x : H), val (A g f) x = val f (g⁻¹ * x)) :
    P = actionIsotype (A.comp K.subtype) ω := by
  ext φ
  rw [hP, mem_actionIsotype]
  refine forall_congr' fun u ↦ ⟨fun h ↦ hval (funext fun x ↦ ?_), fun h g ↦ ?_⟩
  · rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hA, h, hsmul, Pi.smul_apply,
      smul_eq_mul]
  · have hg := congrFun (congrArg val h) g
    rwa [MonoidHom.comp_apply, Subgroup.coe_subtype, hA, hsmul, Pi.smul_apply,
      smul_eq_mul] at hg

/-- Paper: (5.4.2.3), p. 275, and Proposition D.3.3.12, p. 811.
The coordinate equations give the Appendix D isotype for its translation action. -/
theorem sLocalDecayIsotype_eq_actionIsotype (I : Set ℝ) (ω : PontryaginDual J₁)
    (A : Jₛ →* (Ẽ(I) →L[ℂ] Ẽ(I)))
    (hA : ∀ (g : Jₛ) (f : Ẽ(I)) (x : Jₛ), (A g f).val x = f.val (g⁻¹ * x)) :
    sLocalDecayIsotype (F := F) (S := S) I ω = actionIsotype (A.comp (mₛ).ker.subtype) ω := by
  have hP := mem_sLocalDecayIsotype (F := F) (S := S) I ω
  have hsmul : ∀ (c : ℂ) (f : Ẽ(I)),
      (fun φ : Ẽ(I) ↦ φ.val) (c • f) = c • (fun φ : Ẽ(I) ↦ φ.val) f := fun _ _ ↦ rfl
  have hval : Injective (fun φ : Ẽ(I) ↦ φ.val) := fun _ _ h ↦ Subtype.ext h
  have key := sLocalDecayIsotype_eq_actionIsotype_aux (mₛ).ker (fun φ : Ẽ(I) ↦ φ.val) hval hsmul
  with_reducible_and_instances exact key _ ω hP A hA

/-- A modulated decay space with a norm section maps continuously to the decay space of the
positive reals by restriction to the section, and back by tensoring with the conjugate of a
compact-kernel character. -/
private theorem existsUnique_sLocalCechRadialReflection_section {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (I : Set ℝ)
    (hInt : OrdConnected I) (hne : I.Nonempty) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (ω : PontryaginDual m.toMonoidHom.ker) :
    ∃ (R : ModulatedExponentialDecay m I →L[ℂ] PositiveRealExponentialDecay I)
      (X : PositiveRealExponentialDecay I →L[ℂ] ModulatedExponentialDecay m I),
      (∀ f t, (R f).val (Real.log (t.val : ℝ)) = f.val (τ t)) ∧
      (∀ p (k : m.toMonoidHom.ker) t,
        (X p).val (k.val * τ t) = star (ω k : ℂ) * p.val (Real.log (t.val : ℝ))) := by
  let K := m.toMonoidHom.ker
  let P := PositiveRealExponentialDecay I
  let E := ModulatedExponentialDecay m I
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨e, he⟩ := modulatedExponentialDecay_tensor_equiv m I hm hInt hne τ hτ
  -- Point evaluations on the positive-real decay space.
  obtain ⟨a, ha⟩ := hne
  have hPE := positiveRealExponentialDecay_isEmbedding I ⟨a, ha⟩
  have hevP (x : ℝ) : Continuous (fun p : P ↦ p.val x) := by
    have h1 : Continuous (fun p : P ↦ logExponentialDecayTwist I ⟨a, ha⟩ p x) :=
      ((continuous_eval_const x).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous).comp
        ((continuous_apply _).comp hPE.continuous)
    refine (h1.const_mul ((Real.exp (a * x) : ℂ)⁻¹)).congr fun p ↦ ?_
    exact (congrArg ((Real.exp (a * x) : ℂ)⁻¹ * ·) (logExponentialDecayTwist_apply I ⟨a, ha⟩ p x)).trans
      (inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') _)
  let evP (t : ℝ≥0ˣ) : P →L[ℂ] ℂ :=
    { toFun := fun p ↦ p.val (Real.log (t.val : ℝ))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := hevP _ }
  let resE (t : ℝ≥0ˣ) : E →L[ℂ] ℂ :=
    { toFun := fun f ↦ f.val (τ t)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_modulatedExponentialDecay_eval m I ⟨a, ha⟩ (τ t) }
  let ev1 : SchwartzBruhat K →L[ℂ] ℂ :=
    { toFun := fun h ↦ h 1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := continuous_schwartzBruhat_eval (A := K) 1 }
  let T := InductiveTensor (SchwartzBruhat K) P
  let : T2Space P := hPE.t2Space
  let : CompleteSpace P := positiveRealExponentialDecay_complete I ⟨a, ha⟩
  let : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_eval_t2 (A := K)
  obtain ⟨R, hR⟩ := exists_tensor_restriction ev1 evP resE e (fun u v t ↦ by
    have h := he u v 1 t
    rw [OneMemClass.coe_one, one_mul] at h
    exact h)
  -- The conjugate character of the compact kernel as a test function.
  obtain ⟨one, hone⟩ := compact_schwartzBruhat_one (H := K)
  obtain ⟨M, hM⟩ := schwartzBruhat_mul_unitaryCharacter (A := K) ω⁻¹
  let hbar := M one
  have hhbar (k : K) : hbar k = star (ω k : ℂ) := by
    change M one k = _
    rw [hM, hone, mul_one]
    change (((ω k)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, Complex.star_def]
  let tm : P →ₗ[ℂ] T := TensorProduct.mk ℂ (SchwartzBruhat K) P hbar
  have htm : Continuous tm :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp tm fun q ↦ q.property.1 hbar
  let X : P →L[ℂ] E := e.toContinuousLinearMap.comp (((UniformSpace.Completion.toComplL : T →L[ℂ] UniformSpace.Completion T)).comp ⟨tm, htm⟩)
  refine ⟨R, X, fun f t ↦ hR f t, fun p k t ↦ ?_⟩
  have h := he hbar p k t
  rw [hhbar] at h
  exact h

/-- The positive real with logarithm `x`. -/
private theorem existsUnique_sLocalCechRadialReflection_exp (x : ℝ) :
    ∃ t : ℝ≥0ˣ, Real.log normℝ(t) = x := by
  refine ⟨Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne', ?_⟩
  change Real.log ((Real.exp x).toNNReal : ℝ) = x
  rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]

/-- Two continuous linear maps that are inverse to each other on a submodule give a
continuous linear equivalence of that submodule. -/
private theorem existsUnique_sLocalCechRadialReflection_equiv {E P : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup P] [Module ℂ P] [TopologicalSpace P]
    (V : Submodule ℂ E) (R : E →L[ℂ] P) (X : P →L[ℂ] E) (hX : ∀ p, X p ∈ V)
    (hRX : ∀ p, R (X p) = p) (hXR : ∀ f ∈ V, X (R f) = f) :
    ∃ Φ : V ≃L[ℂ] P, (∀ f, Φ f = R (f : E)) ∧ ∀ p, (Φ.symm p : E) = X p := by
  let Φ : V ≃L[ℂ] P :=
    { toFun := fun f ↦ R (f : E)
      invFun := fun p ↦ ⟨X p, hX p⟩
      map_add' := fun f g ↦ map_add R (f : E) g
      map_smul' := fun c f ↦ map_smul R c (f : E)
      left_inv := fun f ↦ Subtype.ext (hXR f f.property)
      right_inv := hRX
      continuous_toFun := R.continuous.comp continuous_subtype_val
      continuous_invFun := X.continuous.subtype_mk _ }
  exact ⟨Φ, fun _ ↦ rfl, fun _ ↦ rfl⟩

private theorem sLocalDecay_secondCountable : SecondCountableTopology Jₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Aₛˣ := (sIdeleGroup_description F S).1.secondCountableTopology
  infer_instance

private theorem sLocalDecay_isModulation (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ) :
    IsModulation (⟨mₛ, hmₛ⟩ : Jₛ →ₜ* ℝ≥0ˣ) := by
  refine ⟨isProperMap_sIdeleQuotientNorm F S, τ (Units.mk0 2 two_ne_zero), ?_⟩
  change mₛ (τ _) ≠ 1
  rw [hτ]
  intro h
  have := congrArg (fun u : ℝ≥0ˣ ↦ (u.val : ℝ)) h
  norm_num at this

/-- On the S-idele classes, restriction to a norm section and the conjugate-character lift
are continuous linear maps between the decay space and the decay space of the positive reals. -/
private theorem existsUnique_sLocalCechRadialReflection_maps (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (hτ : RightInverse τ mₛ) (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (ω : PontryaginDual J₁) :
    ∃ (R : Ẽ(I) →L[ℂ] PositiveRealExponentialDecay I) (X : PositiveRealExponentialDecay I →L[ℂ] Ẽ(I)),
      (∀ f t, (R f).val (Real.log normℝ(t)) = f.val (τ t)) ∧
      (∀ p t (k : J₁), (X p).val (τ t * k.val) = star (ω k : ℂ) * p.val (Real.log normℝ(t))) := by
  let : SecondCountableTopology Jₛ := sLocalDecay_secondCountable
  have h1 : IsTopologicalGroup Jₛ := inferInstance
  have h2 : T2Space Jₛ := inferInstance
  have h3 : LocallyCompactSpace Jₛ := inferInstance
  let m : Jₛ →ₜ* ℝ≥0ˣ := ⟨mₛ, hmₛ⟩
  have hτ' : RightInverse τ m := hτ
  have hm : IsModulation m := sLocalDecay_isModulation τ hτ
  obtain ⟨R, X, hR, hX⟩ :=
    existsUnique_sLocalCechRadialReflection_section m hm I hInt hne τ hτ' ω
  exact ⟨R, X, hR, fun p t k ↦ (congrArg (fun g : Jₛ ↦ (X p).val g) (mul_comm _ _)).trans
    (hX p k t)⟩

/-- Every idele class is a norm-one class times a point of the norm section. -/
private theorem existsUnique_sLocalCechRadialReflection_split (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (hτ : RightInverse τ mₛ) (g : Jₛ) : ∃ (k : J₁) (t : ℝ≥0ˣ), g = τ t * k.val :=
  ⟨⟨g / τ (mₛ g), by
    change mₛ (g / τ (mₛ g)) = 1
    rw [map_div, hτ (mₛ g), div_self']⟩, mₛ g, (mul_div_cancel _ _).symm⟩

private theorem existsUnique_sLocalCechRadialReflection_star (ω : PontryaginDual J₁) (u : J₁) :
    star (ω u⁻¹ : ℂ) = (ω u : ℂ) := by
  rw [map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]

/-- A function on the idele classes given on the section by the conjugate character lies
in the isotype. -/
private theorem existsUnique_sLocalCechRadialReflection_mem (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (hτ : RightInverse τ mₛ) (I : Set ℝ) (ω : PontryaginDual J₁) (φ : Ẽ(I)) (c : ℝ≥0ˣ → ℂ)
    (hφ : ∀ t (k : J₁), φ.val (τ t * k.val) = star (ω k : ℂ) * c t) :
    φ ∈ sLocalDecayIsotype (F := F) (S := S) I ω := by
  refine (mem_sLocalDecayIsotype I ω φ).mpr fun u g ↦ ?_
  obtain ⟨k, t, rfl⟩ := existsUnique_sLocalCechRadialReflection_split τ hτ g
  have hg : u.val⁻¹ * (τ t * k.val) = τ t * (u⁻¹ * k).val := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_left_comm]
  refine (congrArg (fun x : Jₛ ↦ φ.val x) hg).trans ?_
  refine (hφ t _).trans (Eq.trans ?_ (congrArg (fun z ↦ (ω u : ℂ) * z) (hφ t k)).symm)
  rw [map_mul, Circle.coe_mul, star_mul', existsUnique_sLocalCechRadialReflection_star]
  ring

/-- An isotypic function is determined by its values on the section. -/
private theorem existsUnique_sLocalCechRadialReflection_eq (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (hτ : RightInverse τ mₛ) (I : Set ℝ) (ω : PontryaginDual J₁) (φ ψ : Ẽ(I))
    (hφ : φ ∈ sLocalDecayIsotype (F := F) (S := S) I ω) (c : ℝ≥0ˣ → ℂ)
    (hc : ∀ t, φ.val (τ t) = c t)
    (hψ : ∀ t (k : J₁), ψ.val (τ t * k.val) = star (ω k : ℂ) * c t) : ψ = φ := by
  apply Subtype.ext
  funext g
  obtain ⟨k, t, rfl⟩ := existsUnique_sLocalCechRadialReflection_split τ hτ g
  have hiso := (mem_sLocalDecayIsotype I ω φ).mp hφ k⁻¹ (τ t)
  have hk : ((k⁻¹ : J₁) : Jₛ)⁻¹ * τ t = τ t * k.val := by
    rw [Subgroup.coe_inv, inv_inv]
    exact mul_comm _ _
  refine (hψ t k).trans (Eq.trans ?_ ((congrArg (fun x : Jₛ ↦ φ.val x) hk).symm.trans hiso).symm)
  rw [hc, map_inv, Circle.coe_inv_eq_conj, Complex.star_def]

/-- Restriction to a norm section identifies a norm-one isotype of the S-local decay space
with the decay space of the positive reals. -/
private theorem existsUnique_sLocalCechRadialReflection_isotypeEquiv (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (hτ : RightInverse τ mₛ) (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (ω : PontryaginDual J₁) :
    ∃ Φ : Eω(I, ω) ≃L[ℂ] PositiveRealExponentialDecay I,
      (∀ f t, (Φ f).val (Real.log normℝ(t)) = f.val.val (τ t)) ∧
      (∀ p t (k : J₁), (Φ.symm p).val.val (τ t * k.val) =
        star (ω k : ℂ) * p.val (Real.log normℝ(t))) := by
  have hmaps := existsUnique_sLocalCechRadialReflection_maps τ hτ I hInt hne ω
  obtain ⟨R, X, hR, hX⟩ := hmaps
  have hXmem (p : PositiveRealExponentialDecay I) :
      X p ∈ sLocalDecayIsotype (F := F) (S := S) I ω :=
    existsUnique_sLocalCechRadialReflection_mem τ hτ I ω (X p) _ (hX p)
  have hRX (p : PositiveRealExponentialDecay I) : R (X p) = p := by
    apply Subtype.ext
    funext x
    obtain ⟨t, rfl⟩ := existsUnique_sLocalCechRadialReflection_exp x
    refine (hR (X p) t).trans ?_
    have h := hX p t 1
    have h1 : τ t * ((1 : J₁) : Jₛ) = τ t := mul_one (τ t)
    refine (congrArg (fun g : Jₛ ↦ (X p).val g) h1.symm).trans (h.trans ?_)
    rw [map_one, Circle.coe_one, star_one, one_mul]
  have hXR (f : Ẽ(I)) (hf : f ∈ sLocalDecayIsotype (F := F) (S := S) I ω) : X (R f) = f :=
    existsUnique_sLocalCechRadialReflection_eq τ hτ I ω f (X (R f)) hf _ (fun t ↦ (hR f t).symm)
      (hX (R f))
  have hE := existsUnique_sLocalCechRadialReflection_equiv (E := Ẽ(I))
    (P := PositiveRealExponentialDecay I) (sLocalDecayIsotype (F := F) (S := S) I ω) R X hXmem hRX hXR
  obtain ⟨Φ, hΦ, hΦs⟩ := hE
  refine ⟨Φ, fun f t ↦ ?_, fun p t k ↦ ?_⟩
  · exact (congrArg (fun q : PositiveRealExponentialDecay I ↦ q.val (Real.log normℝ(t)))
      (hΦ f)).trans (hR f.val t)
  · exact (congrArg (fun q : Ẽ(I) ↦ q.val (τ t * k.val)) (hΦs p)).trans (hX p t k)

/-- Reflection `p ↦ (u ↦ exp(-u) p(-u))` between decay spaces whose exponent intervals are
exchanged by `a ↦ 1 - a`. -/
private theorem existsUnique_sLocalCechRadialReflection_refl (I J : Set ℝ) (hJ : J.Nonempty)
    (h : ∀ a ∈ J, 1 - a ∈ I) :
    ∃ T : PositiveRealExponentialDecay I →L[ℂ] PositiveRealExponentialDecay J,
      ∀ p u, (T p).val u = (Real.exp (-u) : ℂ) * p.val (-u) := by
  let N : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.neg ℝ
  let C : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ N
  have hI : I.Nonempty := ⟨1 - hJ.some, h _ hJ.some_mem⟩
  let a' (a : J) : I := ⟨1 - a, h a a.2⟩
  have hval (p : PositiveRealExponentialDecay I) (a : J) (u : ℝ) :
      C (logExponentialDecayTwist I (a' a) p) u =
        (Real.exp ((a : ℝ) * u) : ℂ) * ((Real.exp (-u) : ℂ) * p.val (-u)) := by
    refine (logExponentialDecayTwist_apply I (a' a) p (N u)).trans ?_
    change (Real.exp ((1 - (a : ℝ)) * -u) : ℂ) * p.val (-u) = _
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  have hmem (p : PositiveRealExponentialDecay I) :
      (fun u ↦ (Real.exp (-u) : ℂ) * p.val (-u)) ∈ logExponentialDecaySubmodule J := by
    apply (Submodule.mem_iInf _).2
    intro a
    exact ⟨C (logExponentialDecayTwist I (a' a) p), funext fun u ↦ hval p a u⟩
  let T : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay J :=
    { toFun := fun p ↦ (⟨_, hmem p⟩ : logExponentialDecaySubmodule J)
      map_add' := fun p q ↦ Subtype.ext (funext fun u ↦ by
        change (Real.exp (-u) : ℂ) * (p.val (-u) + q.val (-u)) =
          (Real.exp (-u) : ℂ) * p.val (-u) + (Real.exp (-u) : ℂ) * q.val (-u)
        ring)
      map_smul' := fun c p ↦ Subtype.ext (funext fun u ↦ by
        change (Real.exp (-u) : ℂ) * (c * p.val (-u)) = c * ((Real.exp (-u) : ℂ) * p.val (-u))
        ring) }
  have hIE := positiveRealExponentialDecay_isEmbedding I hI
  have hJE := positiveRealExponentialDecay_isEmbedding J hJ
  have htw (p : PositiveRealExponentialDecay I) (a : J) :
      logExponentialDecayTwist J a (T p) = C (logExponentialDecayTwist I (a' a) p) := by
    ext u
    refine (logExponentialDecayTwist_apply J a (T p) u).trans (hval p a u).symm
  have hT : Continuous T := by
    apply hJE.continuous_iff.mpr
    apply continuous_pi
    intro a
    exact (C.continuous.comp ((continuous_apply (a' a)).comp hIE.continuous)).congr
      fun p ↦ (htw p a).symm
  exact ⟨⟨T, hT⟩, fun _ _ ↦ rfl⟩

/-- An isotypic function on the S-idele classes, on the norm-one translate of a section point. -/
private theorem existsUnique_sLocalCechRadialReflection_iso (I : Set ℝ) (ω : PontryaginDual J₁)
    (φ : Ẽ(I)) (hφ : φ ∈ sLocalDecayIsotype (F := F) (S := S) I ω) (g : Jₛ) (k : J₁) :
    φ.val (g * k.val) = star (ω k : ℂ) * φ.val g := by
  have hiso := (mem_sLocalDecayIsotype I ω φ).mp hφ k⁻¹ g
  have hk : ((k⁻¹ : J₁) : Jₛ)⁻¹ * g = g * k.val := by
    rw [Subgroup.coe_inv, inv_inv]
    exact mul_comm _ _
  refine (congrArg (fun x : Jₛ ↦ φ.val x) hk).symm.trans (hiso.trans ?_)
  rw [map_inv, Circle.coe_inv_eq_conj, Complex.star_def]

/-- Two functions on the S-idele classes that agree on every norm-one translate of the section
agree. -/
private theorem existsUnique_sLocalCechRadialReflection_ext (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (hτ : RightInverse τ mₛ) (I : Set ℝ) (ω : PontryaginDual J₁) (φ ψ : Eω(I, ω))
    (h : ∀ t (k : J₁), φ.val.val (τ t * k.val) = ψ.val.val (τ t * k.val)) : φ = ψ := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨k, t, rfl⟩ := existsUnique_sLocalCechRadialReflection_split τ hτ g
  exact h t k

/-- The value of the composite of the section equivalences and the profile reflection. -/
private theorem existsUnique_sLocalCechRadialReflection_value (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (ω : PontryaginDual J₁)
    (Φp : Eω(rightInterval, ω) ≃L[ℂ] PositiveRealExponentialDecay rightInterval)
    (hΦp : ∀ f t, (Φp f).val (Real.log normℝ(t)) = f.val.val (τ t))
    (Φm : Eω(leftInterval, ω) ≃L[ℂ] PositiveRealExponentialDecay leftInterval)
    (hΦm : ∀ p t (k : J₁), (Φm.symm p).val.val (τ t * k.val) =
      star (ω k : ℂ) * p.val (Real.log normℝ(t)))
    (R : PositiveRealExponentialDecay rightInterval ≃L[ℂ] PositiveRealExponentialDecay leftInterval)
    (hR : ∀ p u, (R p).val u = (Real.exp (-u) : ℂ) * p.val (-u))
    (f : Eω(rightInterval, ω)) (t : ℝ≥0ˣ) (k : J₁) :
    (Φm.symm (R (Φp f))).val.val (τ t * k.val) =
      ((normℝ(t) : ℂ)⁻¹) * f.val.val (τ t⁻¹ * k.val) := by
  have hpos : 0 < normℝ(t) := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hlog : -Real.log normℝ(t) = Real.log normℝ(t⁻¹) := by
    rw [Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  refine (hΦm _ t k).trans ?_
  refine (congrArg (star (ω k : ℂ) * ·) (hR (Φp f) _)).trans ?_
  refine Eq.trans ?_ (congrArg ((normℝ(t) : ℂ)⁻¹ * ·)
    (existsUnique_sLocalCechRadialReflection_iso rightInterval ω f.val f.property (τ t⁻¹) k)).symm
  have h1 : (Φp f).val (-Real.log normℝ(t)) = f.val.val (τ t⁻¹) :=
    (congrArg (fun u : ℝ ↦ (Φp f).val u) hlog).trans (hΦp f t⁻¹)
  have h2 : (Real.exp (-Real.log normℝ(t)) : ℂ) = (normℝ(t) : ℂ)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hpos, Complex.ofReal_inv]
  refine (congrArg (fun z : ℂ ↦ star (ω k : ℂ) * ((Real.exp (-Real.log normℝ(t)) : ℂ) * z))
    h1).trans ?_
  rw [h2]
  ring

-- TODO(paper-gap): Theorem 5.4.2.2(2) prints incompatible intervals for J_τ.
-- In (3) the asserted half-plane map has poles, already at zero for the trivial
-- character over ℚ with no finite places. In (4) the printed operator omits
-- reflection and applies this multiplier on the entire positive half-plane.
-- Restriction to the overlap gives the continuous difference in the diagram below.
-- In (1), the conjugate character requires the opposite shift when x₀ ≠ 0.

/-- Paper: Theorem 5.4.2.2(2), p. 276.
Radial inversion, with the compact coordinate fixed, exchanges the two weight intervals.
Deviation: The target exponent interval is the reflection of the source interval. -/
theorem existsUnique_sLocalCechRadialReflection (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (_hτ : RightInverse τ mₛ) (ω : PontryaginDual J₁) :
    ∃! J : Eω(rightInterval, ω) ≃L[ℂ] Eω(leftInterval, ω),
      ∀ (f : Eω(rightInterval, ω)) (t : ℝ≥0ˣ) (k : J₁),
        (J f).val.val (τ t * k.val) =
          ((normℝ(t) : ℂ)⁻¹) * f.val.val (τ t⁻¹ * k.val) := by
  have hp := existsUnique_sLocalCechRadialReflection_isotypeEquiv τ _hτ rightInterval
    ordConnected_Ioi ⟨1, one_pos⟩ ω
  obtain ⟨Φp, hΦp, -⟩ := hp
  have hm := existsUnique_sLocalCechRadialReflection_isotypeEquiv τ _hτ leftInterval
    ordConnected_Iio ⟨0, zero_lt_one⟩ ω
  obtain ⟨Φm, -, hΦm⟩ := hm
  have hT := existsUnique_sLocalCechRadialReflection_refl rightInterval leftInterval
    ⟨0, zero_lt_one⟩ fun a (ha : a < 1) ↦ show (0 : ℝ) < 1 - a by linarith
  obtain ⟨T, hT⟩ := hT
  have hT' := existsUnique_sLocalCechRadialReflection_refl leftInterval rightInterval
    ⟨1, one_pos⟩ fun a (ha : 0 < a) ↦ show 1 - a < (1 : ℝ) by linarith
  obtain ⟨T', hT'⟩ := hT'
  have hback (u : ℝ) (z : ℂ) : (Real.exp (-u) : ℂ) * ((Real.exp u : ℂ) * z) = z := by
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  have h1 (p : PositiveRealExponentialDecay rightInterval) : T' (T p) = p :=
    Subtype.ext (funext fun u ↦ by rw [hT', hT, neg_neg, hback])
  have h2 (p : PositiveRealExponentialDecay leftInterval) : T (T' p) = p :=
    Subtype.ext (funext fun u ↦ by rw [hT, hT', neg_neg, hback])
  let R := ContinuousLinearEquiv.equivOfInverse T T' h1 h2
  have hR (p : PositiveRealExponentialDecay rightInterval) (u : ℝ) :
      (R p).val u = (Real.exp (-u) : ℂ) * p.val (-u) := hT p u
  have hval (f : Eω(rightInterval, ω)) (t : ℝ≥0ˣ) (k : J₁) :=
    existsUnique_sLocalCechRadialReflection_value τ ω Φp hΦp Φm hΦm R hR f t k
  have happ (f : Eω(rightInterval, ω)) :
      (Φp.trans (R.trans Φm.symm)) f = Φm.symm (R (Φp f)) :=
    (ContinuousLinearEquiv.trans_apply _ _ f).trans (ContinuousLinearEquiv.trans_apply _ _ _)
  refine ⟨Φp.trans (R.trans Φm.symm), fun f t k ↦ ?_, fun J hJ ↦ ?_⟩
  · exact (congrArg (fun q : Eω(leftInterval, ω) ↦ q.val.val (τ t * k.val)) (happ f)).trans
      (hval f t k)
  · apply ContinuousLinearEquiv.ext
    funext f
    refine existsUnique_sLocalCechRadialReflection_ext τ _hτ leftInterval ω _ _ fun t k ↦ ?_
    exact (hJ f t k).trans ((congrArg (fun q : Eω(leftInterval, ω) ↦ q.val.val (τ t * k.val))
      (happ f)).trans (hval f t k)).symm

local notation "upperMiddle(" χ ")" => Eω(rightInterval, restrict₁(χ)) × Eω(rightInterval, restrict₁(χ⁻¹))

/-- On each vertical trace the strip reflection is the continuous Schwartz pullback by negation. -/
private theorem sLocalCechBergman_exact_reflect_continuous {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) (cI : OrdConnected I) (cJ : OrdConnected J)
    (nI : I.Nonempty) (nJ : J.Nonempty) (hIJ : ∀ x ∈ J, 1 - x ∈ I)
    (R : SchwartzBergman I → SchwartzBergman J)
    (hR : ∀ f z, (R f).val z = f.val (1 - z)) : Continuous R := by
  obtain ⟨T, hT, eT⟩ := schwartzBergman_schwartzLine_topology I hI cI nI
  obtain ⟨V, hV, eV⟩ := schwartzBergman_schwartzLine_topology J hJ cJ nJ
  let N := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ) (F := ℂ)
  apply eV.continuous_iff.mpr
  apply continuous_pi
  intro a
  let b : I := ⟨1 - a.val, hIJ a.val a.property⟩
  have heq (f : SchwartzBergman I) : V (R f) a = N (T f b) := by
    ext x
    change V (R f) a x = T f b (-x)
    rw [hV, hT]
    simp only [weightedVerticalTrace, pow_zero, one_mul, hR, b, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_neg, neg_mul]
    apply congrArg f.val
    ring
  exact (N.continuous.comp ((continuous_apply b).comp eT.continuous)).congr fun f ↦ (heq f).symm

/-- Reflection exchanges the two half-plane spaces, including their vertical-trace topologies. -/
private theorem sLocalCechBergman_exact_reflection :
    ∃ e : B⁻ ≃L[ℂ] B⁺, (∀ (v : B⁻) z, (e v).val z = v.val (1 - z)) ∧
      ∀ (u : B⁺) z, (e.symm u).val z = u.val (1 - z) := by
  have hl (x : ℝ) : 1 - x ∈ leftInterval ↔ x ∈ rightInterval := by
    simp [mem_Iio, mem_Ioi]
  have hr (x : ℝ) : 1 - x ∈ rightInterval ↔ x ∈ leftInterval := by
    simp [mem_Iio, mem_Ioi]
  let R (v : B⁻) : B⁺ := ⟨_, existsUnique_sLocalZetaPair_reflect_mem hl v⟩
  let L (u : B⁺) : B⁻ := ⟨_, existsUnique_sLocalZetaPair_reflect_mem hr u⟩
  let e : B⁻ ≃ₗ[ℂ] B⁺ :=
    { toFun := R
      invFun := L
      left_inv := fun v ↦ Subtype.ext (funext fun z ↦ congrArg v.val (sub_sub_cancel 1 z))
      right_inv := fun u ↦ Subtype.ext (funext fun z ↦ congrArg u.val (sub_sub_cancel 1 z))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have cp := sLocalCechBergman_exact_reflect_continuous isOpen_Iio isOpen_Ioi
    ordConnected_Iio ordConnected_Ioi ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
    (fun x ↦ (hl x).mpr) R (fun _ _ ↦ rfl)
  have cm := sLocalCechBergman_exact_reflect_continuous isOpen_Ioi isOpen_Iio
    ordConnected_Ioi ordConnected_Iio ⟨1, by norm_num⟩ ⟨0, by norm_num⟩
    (fun x ↦ (hr x).mpr) L (fun _ _ ↦ rfl)
  exact ⟨⟨e, cp, cm⟩, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

private theorem sLocalCechBergman_exact_fourier (χ : PontryaginDual Jₛ) (e : B⁻ ≃L[ℂ] B⁺)
    (he : ∀ (v : B⁻) z, (e v).val z = v.val (1 - z)) (f : ℬₛ) :
    EqOn (e ((sLocalZetaPair χ (Submodule.Quotient.mk f)).2)).val
      (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf := by
  intro s hs
  rw [he]
  have hs' : 1 - s ∈ leftHalf := by simpa [mem_preimage, mem_Iio] using hs
  simpa only [sub_sub_cancel] using (sLocalZetaPair_mk χ f).2 hs'

/-- Paper: (5.4.2.6), p. 276.
On the lower row the right half-plane zeta pair maps to the difference of the
first entry and the reflected second entry multiplied on the overlap by the
functional-equation factor. The image of the first map is the kernel of the difference.
Deviation: The multiplier is used on the overlap where it is holomorphic. -/
theorem sLocalCechBergman_exact (χ : PontryaginDual Jₛ) :
    ∃ (U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺) (D : B⁺ × B⁺ →L[ℂ] B⁰),
      (∀ f : ℬₛ,
        EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
        EqOn (U (Submodule.Quotient.mk f)).2.val
          (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf) ∧
      (∀ p : B⁺ × B⁺,
        EqOn (D p).val (fun s ↦ p.1.val s - ρₛ(χ, s) * p.2.val (1 - s)) overlap) ∧
      Function.Exact U D := by
  let e : B⁻ ≃L[ℂ] B⁺ := sLocalCechBergman_exact_reflection.choose
  have he := sLocalCechBergman_exact_reflection.choose_spec.1
  have hi := sLocalCechBergman_exact_reflection.choose_spec.2
  let E : (B⁺ × B⁻) ≃L[ℂ] (B⁺ × B⁺) := (ContinuousLinearEquiv.refl ℂ B⁺).prodCongr e
  let Z : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁻ := ⟨sLocalZetaPair χ, continuous_sLocalZetaPair χ⟩
  let D : B⁺ × B⁻ →L[ℂ] B⁰ :=
    (existsUnique_sLocalZetaMatchingDifference (F := F) (S := S) χ).exists.choose
  refine ⟨E.toContinuousLinearMap.comp Z, D.comp E.symm.toContinuousLinearMap, ?_, ?_, ?_⟩
  · intro f
    exact ⟨(sLocalZetaPair_mk χ f).1, sLocalCechBergman_exact_fourier χ e he f⟩
  · intro p s hs
    have h := (existsUnique_sLocalZetaMatchingDifference (F := F) (S := S) χ).exists.choose_spec
    change (D (E.symm p)).val s = _
    exact (h (E.symm p) hs).trans (congrArg (fun w ↦ p.1.val s - ρₛ(χ, s) * w) (hi p.2 s))
  · intro p
    change D (E.symm p) = 0 ↔ ∃ x, E (Z x) = p
    have hker : D (E.symm p) = 0 ↔ E.symm p ∈ (sLocalZetaPair (F := F) (S := S) χ).range := by
      rw [sLocalZetaPair_range]
      rfl
    rw [hker]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (congrArg E hx).trans (E.apply_symm_apply p)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, (E.symm_apply_apply (Z x)).symm⟩

/-- Paper: (5.4.2.6), p. 276.
In the lower row the zeta pair of the test and its Fourier transform is a
topological embedding with closed range. -/
theorem sLocalCechBergman_isClosedEmbedding (χ : PontryaginDual Jₛ) (U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺)
    (_hU : ∀ f : ℬₛ,
      EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (U (Submodule.Quotient.mk f)).2.val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf) :
    IsClosedEmbedding U := by
  let e : B⁻ ≃L[ℂ] B⁺ := sLocalCechBergman_exact_reflection.choose
  have he := sLocalCechBergman_exact_reflection.choose_spec.1
  let E : (B⁺ × B⁻) ≃L[ℂ] (B⁺ × B⁺) := (ContinuousLinearEquiv.refl ℂ B⁺).prodCongr e
  have h : E ∘ sLocalZetaPair (F := F) (S := S) χ = ⇑U := by
    funext x
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Prod.ext
    · exact existsUnique_sLocalZetaPair_ext ((sLocalZetaPair_mk χ f).1.trans (_hU f).1.symm)
    · exact existsUnique_sLocalZetaPair_ext
        ((sLocalCechBergman_exact_fourier χ e he f).trans (_hU f).2.symm)
  exact h ▸ E.toHomeomorph.isClosedEmbedding.comp (sLocalZetaPair_isClosedEmbedding χ)

/-- Paper: Theorem 5.4.2.2, p. 276.
Restriction of a unitary character to the norm section defines a unique real
frequency in the Mellin coordinate. -/
theorem existsUnique_sLocalCechFrequency (χ : PontryaginDual Jₛ) (τ : ℝ≥0ˣ →ₜ* Jₛ) :
    ∃! x : ℝ, ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I) :=
  by
    let incl : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let c := incl.comp (χ.comp τ)
    obtain ⟨z, ⟨hz, hval⟩, huniq⟩ := existsUnique_unitaryComplexPower c
      (fun t ↦ Circle.norm_coe (χ (τ t)))
    have him : (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp [hz]
    refine ⟨z.im, fun t ↦ (hval t).trans (by rw [him]), fun x hx ↦ ?_⟩
    have he := huniq ((x : ℂ) * Complex.I) ⟨by simp, hx⟩
    simpa using congrArg Complex.im he

/-- On an open exponent interval, twisting the logarithmic profile by the frequency `x`
followed by the Mellin equivalence gives the vertically shifted Mellin transform. -/
private theorem existsUnique_sLocalDecayMellin_shift (I : Set ℝ) (hOpen : IsOpen I)
    (hInt : OrdConnected I) (hne : I.Nonempty) (x : ℝ) :
    ∃ M : PositiveRealExponentialDecay I ≃L[ℂ] SchwartzBergman I,
      ∀ f s, s ∈ Complex.re ⁻¹' I → (M f).val s =
        mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I) := by
  -- The unimodular multiplier u ↦ exp(i y u), as a Schwartz multiplier.
  let g (y : ℝ) (u : ℝ) : ℂ := Complex.exp (((y * u : ℝ) : ℂ) * Complex.I)
  have hg (y : ℝ) : (g y).HasTemperateGrowth := by
    have h1 : (fun u : ℝ ↦ y * u).HasTemperateGrowth :=
      (y • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
    exact Complex.hasTemperateGrowth_exp_mul_I.comp h1
  have hmem (y : ℝ) (f : logExponentialDecaySubmodule I) :
      (fun u ↦ g y u * f.val u) ∈ logExponentialDecaySubmodule I := by
    apply (Submodule.mem_iInf _).2
    intro a
    refine ⟨SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f), ?_⟩
    funext u
    change SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f) u =
      (Real.exp ((a : ℝ) * u) : ℂ) * (g y u * f.val u)
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg y), logExponentialDecayTwist_apply, smul_eq_mul]
    ring
  let mod (y : ℝ) : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I :=
    { toFun := fun f ↦ (⟨_, hmem y f⟩ : logExponentialDecaySubmodule I)
      map_add' := fun f h ↦ Subtype.ext (funext fun u ↦ by
        change g y u * (f.val u + h.val u) = g y u * f.val u + g y u * h.val u
        ring)
      map_smul' := fun c f ↦ Subtype.ext (funext fun u ↦ by
        change g y u * (c * f.val u) = c * (g y u * f.val u)
        ring) }
  have hmod (y : ℝ) (f : PositiveRealExponentialDecay I) (u : ℝ) :
      (mod y f).val u = g y u * f.val u := rfl
  have hE := positiveRealExponentialDecay_isEmbedding I hne
  have htw (y : ℝ) (a : I) (f : PositiveRealExponentialDecay I) :
      logExponentialDecayTwist I a (mod y f) =
        SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f) := by
    ext u
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg y), smul_eq_mul]
    refine (logExponentialDecayTwist_apply I a (mod y f) u).trans ?_
    refine Eq.trans ?_ (congrArg (g y u * ·) (logExponentialDecayTwist_apply I a f u)).symm
    change (Real.exp ((a : ℝ) * u) : ℂ) * (g y u * f.val u) = _
    ring
  have hcont (y : ℝ) : Continuous (mod y) := by
    apply hE.continuous_iff.mpr
    apply continuous_pi
    intro a
    exact ((SchwartzMap.smulLeftCLM ℂ (g y)).continuous.comp
      ((continuous_apply a).comp hE.continuous)).congr fun f ↦ (htw y a f).symm
  have hinv (y : ℝ) (f : PositiveRealExponentialDecay I) : mod (-y) (mod y f) = f := by
    apply Subtype.ext
    funext u
    change g (-y) u * (g y u * f.val u) = f.val u
    simp only [g]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  let P : PositiveRealExponentialDecay I ≃L[ℂ] PositiveRealExponentialDecay I :=
    { toLinearMap := mod x
      invFun := mod (-x)
      left_inv := hinv x
      right_inv := fun f ↦ by simpa using hinv (-x) f
      continuous_toFun := hcont x
      continuous_invFun := hcont (-x) }
  have hspec := (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists.choose_spec
  let A := (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists.choose
  have hform : ∀ (f : PositiveRealExponentialDecay I) (s : ℂ), s ∈ Complex.re ⁻¹' I →
      ((P.trans A) f).val s = mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I) := by
    intro f s hs
    change (A (mod x f)).val s = _
    rw [hspec (mod x f) s hs]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    change (t : ℂ) ^ (s - 1) • (g x (Real.log t) * f.val (Real.log t)) =
      (t : ℂ) ^ (s + x * Complex.I - 1) • f.val (Real.log t)
    have hpow : (t : ℂ) ^ (s + x * Complex.I - 1) = (t : ℂ) ^ (s - 1) * g x (Real.log t) := by
      rw [show s + x * Complex.I - 1 = (s - 1) + x * Complex.I by ring,
        Complex.cpow_add _ _ ht0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
      simp only [g]
      push_cast
      ring_nf
    rw [hpow, smul_eq_mul, smul_eq_mul]
    ring
  exact ⟨P.trans A, hform⟩

/-- For a decay profile and an exponent in its strip, the Haar integral of the profile against
`t ^ z` converges and equals the Mellin transform of the profile. -/
private theorem existsUnique_sLocalDecayMellin_integral (I : Set ℝ)
    (p : PositiveRealExponentialDecay I) (z : ℂ) (hz : z.re ∈ I) :
    Integrable (fun t : ℝ≥0ˣ ↦ p.val (Real.log normℝ(t)) * (normℝ(t) : ℂ) ^ z)
        positiveRealHaar ∧
      ∫ t, p.val (Real.log normℝ(t)) * (normℝ(t) : ℂ) ^ z ∂positiveRealHaar =
        mellin (fun t ↦ p.val (Real.log t)) z := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let E : ℝ → ℝ≥0ˣ := fun x ↦
    Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'
  have hE : Measurable E :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hHaar : positiveRealHaar = Measure.map E volume := rfl
  have hEv (x : ℝ) : normℝ(E x) = Real.exp x := Real.coe_toNNReal _ (Real.exp_pos x).le
  let w := logExponentialDecayTwist I ⟨z.re, hz⟩ p
  have hw (x : ℝ) : w x = (Real.exp (z.re * x) : ℂ) * p.val x :=
    logExponentialDecayTwist_apply I ⟨z.re, hz⟩ p x
  have hp (x : ℝ) : p.val x = (Real.exp (z.re * x) : ℂ)⁻¹ * w x := by
    rw [hw, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  have hpc : Continuous p.val := by
    have hc : Continuous (fun x : ℝ ↦ (Real.exp (z.re * x) : ℂ)⁻¹ * w x) := by
      refine (Continuous.inv₀ ?_ fun x ↦ Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne').mul
        w.continuous
      fun_prop
    exact hc.congr fun x ↦ (hp x).symm
  let g : ℝ → ℂ := fun x ↦ p.val x * Complex.exp (z * x)
  have hcpow (x : ℝ) : ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp (z * x) := by
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), mul_comm]
  have hkE (x : ℝ) : p.val (Real.log normℝ(E x)) * (normℝ(E x) : ℂ) ^ z = g x := by
    rw [hEv, Real.log_exp, hcpow]
  have hpos (t : ℝ≥0ˣ) : 0 < normℝ(t) := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hn : Continuous (fun t : ℝ≥0ˣ ↦ normℝ(t)) :=
    NNReal.continuous_coe.comp Units.continuous_val
  have hkc : Continuous (fun t : ℝ≥0ˣ ↦ p.val (Real.log normℝ(t)) * (normℝ(t) : ℂ) ^ z) := by
    refine (hpc.comp (hn.log fun t ↦ (hpos t).ne')).mul ?_
    exact (Complex.continuous_ofReal.comp hn).cpow continuous_const
      fun t ↦ Complex.ofReal_mem_slitPlane.mpr (hpos t)
  have hgc : Continuous g := hpc.mul (by fun_prop)
  have hg : Integrable g := by
    refine w.integrable.norm.mono' hgc.aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [hw, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [mul_comm]
  constructor
  · rw [hHaar, integrable_map_measure (hHaar ▸ hkc.aestronglyMeasurable) hE.aemeasurable]
    exact hg.congr (.of_forall fun x ↦ (hkE x).symm)
  · rw [hHaar, integral_map hE.aemeasurable (hHaar ▸ hkc.aestronglyMeasurable)]
    simp only [hkE]
    rw [← integral_comp_log_Ioi_zero g, mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    simp only [g, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one, Complex.cpow_def_of_ne_zero ht0,
      ← Complex.ofReal_log ht.le, Complex.ofReal_inv]
    field_simp

local notation "mellinIntegrand(" τ ", " φ ", " z ")" =>
  (fun t : ℝ≥0ˣ ↦ (φ) ((τ) t) * (normℝ(t) : ℂ) ^ (z))

/-- The Mellin formula for the composite of the section equivalence and the shifted Mellin
equivalence, with absolute convergence. -/
private theorem existsUnique_sLocalDecayMellin_formula (τ : ℝ≥0ˣ →ₜ* Jₛ) (I : Set ℝ)
    (ω : PontryaginDual J₁) (x : ℝ) (Φ : Eω(I, ω) ≃L[ℂ] PositiveRealExponentialDecay I)
    (hΦ : ∀ f t, (Φ f).val (Real.log normℝ(t)) = f.val.val (τ t))
    (M' : PositiveRealExponentialDecay I ≃L[ℂ] SchwartzBergman I)
    (hM' : ∀ f s, s ∈ Complex.re ⁻¹' I → (M' f).val s =
      mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I))
    (f : Eω(I, ω)) (s : ℂ) (hs : s.re ∈ I) :
    Integrable (mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I)) positiveRealHaar ∧
      ((Φ.trans M') f).val s =
        ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t ∂positiveRealHaar := by
  have hz : (s + (x : ℂ) * Complex.I).re ∈ I := by simpa using hs
  have hk : mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) = fun t : ℝ≥0ˣ ↦
      (Φ f).val (Real.log normℝ(t)) * (normℝ(t) : ℂ) ^ (s + (x : ℂ) * Complex.I) := by
    funext t
    exact congrArg (fun z : ℂ ↦ z * (normℝ(t) : ℂ) ^ (s + (x : ℂ) * Complex.I)) (hΦ f t).symm
  have hint := existsUnique_sLocalDecayMellin_integral I (Φ f) _ hz
  have h1 : Integrable (mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I)) positiveRealHaar := by
    rw [hk]
    exact hint.1
  have h2 : ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t ∂positiveRealHaar =
      mellin (fun t ↦ (Φ f).val (Real.log t)) (s + (x : ℂ) * Complex.I) :=
    (congrArg (fun F : ℝ≥0ˣ → ℂ ↦ ∫ t, F t ∂positiveRealHaar) hk).trans hint.2
  refine ⟨h1, ?_⟩
  exact ((congrArg (fun q : SchwartzBergman I ↦ q.val s)
    (ContinuousLinearEquiv.trans_apply Φ M' f)).trans (hM' (Φ f) s hs)).trans h2.symm

/-- Paper: Theorem 5.4.2.2(1), p. 276.
On a norm-one isotype, restriction to the norm section followed by the
vertically shifted Mellin integral defines a continuous linear equivalence.
The integrals are absolutely convergent in the open strip. -/
theorem existsUnique_sLocalDecayMellin (τ : ℝ≥0ˣ →ₜ* Jₛ) (_hτ : RightInverse τ mₛ)
    (I : Set ℝ) (_hOpen : IsOpen I) (_hInt : OrdConnected I) (_hne : I.Nonempty)
    (ω : PontryaginDual J₁) (x : ℝ) :
    ∃! M : Eω(I, ω) ≃L[ℂ] SchwartzBergman I, ∀ (f : Eω(I, ω)) (s : ℂ), s.re ∈ I →
      let k := mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I)
      Integrable k positiveRealHaar ∧ (M f).val s = ∫ t, k t ∂positiveRealHaar := by
  have hiso := existsUnique_sLocalCechRadialReflection_isotypeEquiv τ _hτ I _hInt _hne ω
  obtain ⟨Φ, hΦ, -⟩ := hiso
  have hshift := existsUnique_sLocalDecayMellin_shift I _hOpen _hInt _hne x
  obtain ⟨M', hM'⟩ := hshift
  have hform (f : Eω(I, ω)) (s : ℂ) (hs : s.re ∈ I) :=
    existsUnique_sLocalDecayMellin_formula τ I ω x Φ hΦ M' hM' f s hs
  refine ⟨Φ.trans M', hform, fun M hM ↦ ?_⟩
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Complex.re ⁻¹' I
  · exact ((hM f s hs).2).trans (hform f s hs).2.symm
  · exact ((M f).property.1 hs).trans (((Φ.trans M') f).property.1 hs).symm

/-- Recover the continuous representative by dividing a Schwartz twist by its weight. -/
private theorem sLocalDecay_continuous {I : Set ℝ} (a : I) (f : Ẽ(I)) : Continuous f.val := by
  let m : Jₛ →ₜ* ℝ≥0ˣ := ⟨mₛ, hmₛ⟩
  let v := modulatedExponentialDecayTwist m I a f
  have hv : Continuous (fun g : Jₛ ↦ v g) := schwartzBruhat_continuous v
  let w (g : Jₛ) := ((m g).val : ℝ) ^ (a : ℝ)
  have hp (g : Jₛ) : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hw : Continuous w := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).rpow_const
    fun g ↦ Or.inl (hp g).ne'
  have hn (g : Jₛ) : (w g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hp g) _).ne'
  exact (hv.div (Complex.continuous_ofReal.comp hw) hn).congr fun g ↦
    (div_eq_iff (hn g)).mpr ((modulatedExponentialDecayTwist_apply m I a f g).trans (mul_comm _ _))

/-- Equality of absolutely convergent Mellin integrals on one vertical line determines
a continuous radial profile, also after twisting by a fixed unitary character. -/
private theorem cechThetaPair_mellin_ext (u v : C(ℝ≥0ˣ, ℂ)) (c : QuasiCharacter ℝ≥0ˣ)
    (h : ∀ z : ℂ, z.re = 1 →
      let k := fun t : ℝ≥0ˣ ↦ c t * (normℝ(t) : ℂ) ^ z
      Integrable (fun t ↦ u t * k t) positiveRealHaar ∧
      Integrable (fun t ↦ v t * k t) positiveRealHaar ∧
      ∫ t, u t * k t ∂positiveRealHaar = ∫ t, v t * k t ∂positiveRealHaar) : u = v := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let : LocallyCompactSpace ℝ≥0ˣ := e.symm.isOpenEmbedding.locallyCompactSpace
  let : SecondCountableTopology ℝ≥0ˣ := e.symm.isEmbedding.secondCountableTopology
  let w := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id c 1
  apply sub_eq_zero.mp
  apply eq_zero_of_weighted_integrals positiveRealHaar (u-v) w
  · have hu := h 1 Complex.one_re
    exact (hu.1.sub hu.2.1).congr (.of_forall fun t ↦ (sub_mul (u t) (v t) (w t)).symm)
  · intro ψ
    obtain ⟨y, ⟨hy, hψ⟩, _⟩ := existsUnique_unitaryComplexPower
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ)
      (fun t ↦ Circle.norm_coe (ψ t))
    obtain ⟨hu, hv, he⟩ := h (1+y) (by simp [hy])
    have hk (t : ℝ≥0ˣ) : w t * (ψ t : ℂ) = c t * (normℝ(t) : ℂ) ^ (1+y) := by
      change (c t * (normℝ(t) : ℂ) ^ (1 : ℂ)) * (ψ t : ℂ) = _
      rw [show (ψ t : ℂ) = _ from hψ t, Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)), mul_assoc]
    refine (integral_congr_ae (.of_forall fun t ↦ ?_)).trans ((integral_sub hu hv).trans (sub_eq_zero.mpr he))
    change (u t - v t) * w t * (ψ t : ℂ) = _ - _
    rw [mul_assoc, hk, sub_mul]

private theorem cechThetaPair_radial (χ : PontryaginDual Jₛ) (σ : ℝ≥0ˣ →ₜ* Aₛˣ)
    (hσ : RightInverse σ (sIdeleNorm F S))
    (x : ℝ) (u : Eω(rightInterval, restrict₁(χ))) (b : B⁺) (f : ℬₛ)
    (hb : EqOn b.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf)
    (hx : ∀ t, (χ (QuotientGroup.mk (σ t)) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I))
    (hM : ∀ (s : ℂ), 0 < s.re →
      let k := fun t ↦ u.val.val (QuotientGroup.mk (σ t)) * (normℝ(t) : ℂ) ^ (s + (x : ℂ) * Complex.I)
      Integrable k positiveRealHaar ∧ b.val s = ∫ t, k t ∂positiveRealHaar) :
    ∀ t, u.val.val (QuotientGroup.mk (σ t)) = φω(restrict₁(χ)) f (QuotientGroup.mk (σ t)) := by
  let q : Aₛˣ →ₜ* Jₛ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let τ := q.comp σ
  have hτ : RightInverse τ mₛ := hσ
  let θ := φω(restrict₁(χ)) f
  let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ.comp τ)
  let U : C(ℝ≥0ˣ, ℂ) := ⟨u.val.val ∘ τ, (sLocalDecay_continuous ⟨1, one_pos⟩ u.val).comp τ.continuous⟩
  let V := θ.comp τ.toContinuousMap
  have he : U = V := by
    apply cechThetaPair_mellin_ext U V c
    intro z hz
    have hz' : 0 < z.re := hz ▸ zero_lt_one
    let k (t : ℝ≥0ˣ) := c t * (normℝ(t) : ℂ) ^ z
    have hk (t : ℝ≥0ˣ) : (normℝ(t) : ℂ) ^ (z + (x : ℂ) * Complex.I) = k t := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)),
        ← hx t, mul_comm]
      rfl
    have h₁ := hM z hz'
    change Integrable (fun t ↦ U t * (normℝ(t) : ℂ) ^ (z + (x : ℂ) * Complex.I)) positiveRealHaar ∧
      b.val z = ∫ t, U t * (normℝ(t) : ℂ) ^ (z + (x : ℂ) * Complex.I) ∂positiveRealHaar at h₁
    simp only [hk] at h₁
    have hk' (t : ℝ≥0ˣ) : normChart(χ) z (τ t) = k t := by
      change (χ (τ t) : ℂ) * (normℝ(mₛ (τ t)) : ℂ) ^ z = _
      rw [hτ t]
      rfl
    have h₂ := sLocalRadialMellinIntegral_integrable σ hσ f χ z hz'
    change Integrable (fun t ↦ V t * normChart(χ) z (τ t)) positiveRealHaar at h₂
    simp only [hk'] at h₂
    refine ⟨h₁.1, h₂, h₁.2.symm.trans ((hb hz').trans ?_)⟩
    have hr : ∃ (ψ : PontryaginDual Jₛ) (s : ℂ), 0 < s.re ∧ normChart(χ) z = normChart(ψ) s := ⟨χ,z,hz',rfl⟩
    have heq : Zₛ f (normChart(χ) z) = sLocalRadialMellinIntegral σ f χ z := (sLocalIdelicZFunction_eq_integral f hr).trans
      ((sLocalThetaMellinIntegral_eq_zeta f hr).symm.trans
        (sLocalRadialMellinIntegral_eq_theta σ hσ f χ z hz').symm)
    refine heq.trans (integral_congr_ae (.of_forall fun t ↦ ?_))
    exact congrArg (V t * ·) (hk' t)
  exact DFunLike.congr_fun he

private theorem cechThetaPair_fiber (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ)
    (ω : PontryaginDual J₁) (u : Eω(rightInterval, ω)) (f : ℬₛ)
    (he : ∀ t, u.val.val (τ t) = φω(ω) f (τ t)) : u.val.val = ⇑(φω(ω) f) := by
  let : MeasurableSpace J₁ := borel _
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  funext g
  let d : J₁ := ⟨τ (mₛ g) / g, by rw [MonoidHom.mem_ker, map_div, hτ, div_self']⟩
  have hd : d.val⁻¹ * τ (mₛ g) = g := by change (_ / _)⁻¹ * _ = _; rw [inv_div, div_mul_cancel]
  have hu := (mem_sLocalDecayIsotype _ _ u.val).mp u.property d (τ (mₛ g))
  have hv := sLocalHomogeneousAdelicTheta_homogeneous F S μ ω f d (τ (mₛ g))
  rw [hd] at hu hv
  exact hu.trans ((congrArg ((ω d : ℂ) * ·) (he (mₛ g))).trans hv.symm)

/-- Inverse Mellin of the right-hand zeta datum recovers the actual homogeneous
theta function, first on the norm section and then on every compact fiber. -/
private theorem cechThetaPair_inverse (χ : PontryaginDual Jₛ) :
    ∃ A : B⁺ ≃L[ℂ] Eω(rightInterval, restrict₁(χ)), ∀ (b : B⁺) (f : ℬₛ),
      EqOn b.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf →
      (A b).val.val = ⇑(φω(restrict₁(χ)) f) := by
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let σ : ℝ≥0ˣ →ₜ* Aₛˣ := ⟨p.comp (canonicalIdeleNormSection F), hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hσ : RightInverse σ (sIdeleNorm F S) := sIdeleNorm_project_canonicalSection F S
  let q : Aₛˣ →ₜ* Jₛ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let τ := q.comp σ
  have hτ : RightInverse τ mₛ := hσ
  have hfreq := (existsUnique_sLocalCechFrequency (F := F) (S := S) χ τ).exists
  let x := hfreq.choose
  have hx := hfreq.choose_spec
  have hMellin := (existsUnique_sLocalDecayMellin (F := F) (S := S) τ hτ rightInterval isOpen_Ioi
    ordConnected_Ioi ⟨1, one_pos⟩ restrict₁(χ) x).exists
  let M := hMellin.choose
  have hM := hMellin.choose_spec
  refine ⟨M.symm, fun b f hb ↦ ?_⟩
  let u := M.symm b
  have he := cechThetaPair_radial χ σ hσ x u b f hb hx (fun s hs ↦ by
    have hr := hM u s hs
    exact ⟨hr.1, (congrArg (fun a : B⁺ ↦ a.val s) (M.apply_symm_apply b).symm).trans hr.2⟩)
  exact cechThetaPair_fiber τ hτ restrict₁(χ) u f he


private theorem cechThetaPair_build (χ : PontryaginDual Jₛ)
    (A : B⁺ ≃L[ℂ] Eω(rightInterval, restrict₁(χ))) (B : B⁺ ≃L[ℂ] Eω(rightInterval, restrict₁(χ⁻¹)))
    (hA : ∀ (b : B⁺) (f : ℬₛ), EqOn b.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf →
      (A b).val.val = ⇑(φω(restrict₁(χ)) f))
    (hB : ∀ (b : B⁺) (f : ℬₛ), EqOn b.val (fun s ↦ Zₛ f (normChart(χ⁻¹) s)) rightHalf →
      (B b).val.val = ⇑(φω(restrict₁(χ⁻¹)) f)) :
    ∃! U : Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ), ∀ f : ℬₛ,
      (U (Submodule.Quotient.mk f)).1.val.val = ⇑(φω(restrict₁(χ)) f) ∧
      (U (Submodule.Quotient.mk f)).2.val.val = ⇑(φω(restrict₁(χ⁻¹)) (Fourierₛ f)) := by
  let R := sLocalCechBergman_exact_reflection.choose
  have hR := sLocalCechBergman_exact_reflection.choose_spec.1
  let Z : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁻ := ⟨sLocalZetaPair χ, continuous_sLocalZetaPair χ⟩
  let U : Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ) := (A.prodCongr (R.trans B)).toContinuousLinearMap.comp Z
  have hU (f : ℬₛ) : (U (Submodule.Quotient.mk f)).1.val.val = ⇑(φω(restrict₁(χ)) f) ∧
      (U (Submodule.Quotient.mk f)).2.val.val = ⇑(φω(restrict₁(χ⁻¹)) (Fourierₛ f)) := by
    change (A (Z (Submodule.Quotient.mk f)).1).val.val = _ ∧ (B (R (Z (Submodule.Quotient.mk f)).2)).val.val = _
    exact ⟨hA _ f (sLocalZetaPair_mk χ f).1, hB _ _ (sLocalCechBergman_exact_fourier χ R hR f)⟩
  refine ⟨U, hU, fun V hV ↦ ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  refine Quotient.inductionOn' z fun f ↦ ?_
  exact Prod.ext (Subtype.ext (Subtype.ext ((hV f).1.trans (hU f).1.symm)))
    (Subtype.ext (Subtype.ext ((hV f).2.trans (hU f).2.symm)))

/-- Paper: (5.4.2.6), p. 276.
The upper left arrow pairs the two homogeneous theta functions attached to
a test and to its S-adelic Fourier transform. -/
theorem existsUnique_sLocalCechThetaPair (χ : PontryaginDual Jₛ) :
    ∃! U : Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ), ∀ f : ℬₛ,
      (U (Submodule.Quotient.mk f)).1.val.val = ⇑(φω(restrict₁(χ)) f) ∧
      (U (Submodule.Quotient.mk f)).2.val.val = ⇑(φω(restrict₁(χ⁻¹)) (Fourierₛ f)) := by
  have h₁ := cechThetaPair_inverse (F := F) (S := S) χ
  have h₂ := cechThetaPair_inverse (F := F) (S := S) χ⁻¹
  exact cechThetaPair_build χ h₁.choose h₂.choose h₁.choose_spec h₂.choose_spec

local notation "cechThetaPair(" χ ")" => (show Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ) from
  (existsUnique_sLocalCechThetaPair (F := F) (S := S) χ).exists.choose)

/-- Paper: Theorem 5.4.2.2(6), p. 277.
The right vertical arrow is the Mellin equivalence on the overlap followed by
translation of the spectral argument by the section's imaginary frequency. -/
theorem existsUnique_sLocalCechStripMellin (x : ℝ) :
    ∃! M : PositiveRealExponentialDecay overlapInterval ≃L[ℂ] B⁰,
      ∀ f s, s ∈ overlap → (M f).val s =
        mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I) := by
  let I : Set ℝ := Ioo 0 1
  have hne : I.Nonempty := ⟨1 / 2, by norm_num [I]⟩
  -- The unimodular multiplier u ↦ exp(i y u), as a Schwartz multiplier.
  let g (y : ℝ) (u : ℝ) : ℂ := Complex.exp (((y * u : ℝ) : ℂ) * Complex.I)
  have hg (y : ℝ) : (g y).HasTemperateGrowth := by
    have h1 : (fun u : ℝ ↦ y * u).HasTemperateGrowth :=
      (y • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
    exact Complex.hasTemperateGrowth_exp_mul_I.comp h1
  have hmem (y : ℝ) (f : logExponentialDecaySubmodule I) :
      (fun u ↦ g y u * f.val u) ∈ logExponentialDecaySubmodule I := by
    apply (Submodule.mem_iInf _).2
    intro a
    refine ⟨SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f), ?_⟩
    funext u
    change SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f) u =
      (Real.exp ((a : ℝ) * u) : ℂ) * (g y u * f.val u)
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg y), logExponentialDecayTwist_apply, smul_eq_mul]
    ring
  let mod (y : ℝ) : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I :=
    { toFun := fun f ↦ (⟨_, hmem y f⟩ : logExponentialDecaySubmodule I)
      map_add' := fun f h ↦ Subtype.ext (funext fun u ↦ by
        change g y u * (f.val u + h.val u) = g y u * f.val u + g y u * h.val u
        ring)
      map_smul' := fun c f ↦ Subtype.ext (funext fun u ↦ by
        change g y u * (c * f.val u) = c * (g y u * f.val u)
        ring) }
  have hmod (y : ℝ) (f : PositiveRealExponentialDecay I) (u : ℝ) :
      (mod y f).val u = g y u * f.val u := rfl
  have hE := positiveRealExponentialDecay_isEmbedding I hne
  have htw (y : ℝ) (a : I) (f : PositiveRealExponentialDecay I) :
      logExponentialDecayTwist I a (mod y f) =
        SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f) := by
    ext u
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg y), smul_eq_mul]
    refine (logExponentialDecayTwist_apply I a (mod y f) u).trans ?_
    refine Eq.trans ?_ (congrArg (g y u * ·) (logExponentialDecayTwist_apply I a f u)).symm
    change (Real.exp ((a : ℝ) * u) : ℂ) * (g y u * f.val u) = _
    ring
  have hcont (y : ℝ) : Continuous (mod y) := by
    apply hE.continuous_iff.mpr
    apply continuous_pi
    intro a
    exact ((SchwartzMap.smulLeftCLM ℂ (g y)).continuous.comp
      ((continuous_apply a).comp hE.continuous)).congr fun f ↦ (htw y a f).symm
  have hinv (y : ℝ) (f : PositiveRealExponentialDecay I) : mod (-y) (mod y f) = f := by
    apply Subtype.ext
    funext u
    change g (-y) u * (g y u * f.val u) = f.val u
    simp only [g]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  let P : PositiveRealExponentialDecay I ≃L[ℂ] PositiveRealExponentialDecay I :=
    { toLinearMap := mod x
      invFun := mod (-x)
      left_inv := hinv x
      right_inv := fun f ↦ by simpa using hinv (-x) f
      continuous_toFun := hcont x
      continuous_invFun := hcont (-x) }
  have hOpen : IsOpen I := isOpen_Ioo
  have hInt : OrdConnected I := ordConnected_Ioo
  have hspec := (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists.choose_spec
  let A := (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists.choose
  have hform : ∀ (f : PositiveRealExponentialDecay I) (s : ℂ), s ∈ Complex.re ⁻¹' I →
      ((P.trans A) f).val s = mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I) := by
    intro f s hs
    change (A (mod x f)).val s = _
    rw [hspec (mod x f) s hs]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    change (t : ℂ) ^ (s - 1) • (g x (Real.log t) * f.val (Real.log t)) =
      (t : ℂ) ^ (s + x * Complex.I - 1) • f.val (Real.log t)
    have hpow : (t : ℂ) ^ (s + x * Complex.I - 1) = (t : ℂ) ^ (s - 1) * g x (Real.log t) := by
      rw [show s + x * Complex.I - 1 = (s - 1) + x * Complex.I by ring,
        Complex.cpow_add _ _ ht0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
      simp only [g]
      push_cast
      ring_nf
    rw [hpow, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨P.trans A, hform, ?_⟩
  intro M hM
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Complex.re ⁻¹' I
  · exact (hM f s hs).trans (hform f s hs).symm
  · exact ((M f).property.1 hs).trans (((P.trans A) f).property.1 hs).symm

/-- A homogeneous function times its character is constant on norm fibers. -/
private theorem sLocalCech_left_commutes_invariant {G H : Type*} [CommGroup G] [Group H]
    (m : G →* H) (χ : G →* ℂ) (θ : G → ℂ)
    (hθ : ∀ (k : m.ker) g, θ (k.val⁻¹ * g) = χ k.val * θ g)
    (a b : G) (hab : m a = m b) : θ a * χ a = θ b * χ b := by
  let k : m.ker := ⟨b * a⁻¹, by simp only [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]⟩
  have harg : k.val⁻¹ * b = a := by dsimp [k]; simp [mul_comm]
  have hc : χ k.val * χ a = χ b := by rw [← map_mul]; congr 1; dsimp [k]; simp
  calc
    θ a * χ a = (χ k.val * θ b) * χ a := congrArg (· * χ a) ((congrArg θ harg).symm.trans (hθ k b))
    _ = θ b * (χ k.val * χ a) := by ring
    _ = θ b * χ b := congrArg (θ b * ·) hc

/-- Compare an arbitrary quotient norm section with the canonical idelic section. -/
private theorem sLocalCech_left_commutes_mellin (χ : PontryaginDual Jₛ)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ)
    (x : ℝ) (hx : ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I))
    (f : ℬₛ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t : ℝ≥0ˣ, (φω(restrict₁(χ)) f) (τ t) *
      (normℝ(t) : ℂ) ^ (s + (x : ℂ) * Complex.I) ∂positiveRealHaar) =
        Zₛ f (normChart(χ) s) := by
  let : MeasurableSpace J₁ := borel J₁
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let σ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ := ⟨p.comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hσ : RightInverse σ (sIdeleNorm F S) := thetaSection_rightInverse F S
  let q : (SAdeleRing F S)ˣ →ₜ* Jₛ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  have hq (t : ℝ≥0ˣ) : mₛ (q (σ t)) = t := hσ t
  have hi : (∫ t : ℝ≥0ˣ, (φω(restrict₁(χ)) f) (τ t) *
      (normℝ(t) : ℂ) ^ (s + (x : ℂ) * Complex.I) ∂positiveRealHaar) =
      sLocalRadialMellinIntegral σ f χ s := by
    apply integral_congr_ae
    filter_upwards [] with t
    have hn : (normℝ(t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)
    have heq := sLocalCech_left_commutes_invariant mₛ (Circle.coeHom.comp χ.toMonoidHom)
      (φω(restrict₁(χ)) f) (fun k g ↦
        sLocalHomogeneousAdelicTheta_homogeneous F S μ restrict₁(χ) f k g)
      (τ t) (q (σ t)) ((hτ t).trans (hq t).symm)
    change (φω(restrict₁(χ)) f) (τ t) * (normℝ(t) : ℂ) ^ (s + (x : ℂ) * Complex.I) =
      (φω(restrict₁(χ)) f) (q (σ t)) * normChart(χ) s (q (σ t))
    rw [Complex.cpow_add _ _ hn]
    change _ = (φω(restrict₁(χ)) f) (q (σ t)) *
      ((χ (q (σ t)) : ℂ) * ((((mₛ (q (σ t))).val : ℝ) : ℂ) ^ s))
    rw [hq]
    calc
      _ = ((φω(restrict₁(χ)) f) (τ t) * (χ (τ t) : ℂ)) * (normℝ(t) : ℂ) ^ s := by rw [hx]; ring
      _ = ((φω(restrict₁(χ)) f) (q (σ t)) * (χ (q (σ t)) : ℂ)) * (normℝ(t) : ℂ) ^ s := congrArg (· * (normℝ(t) : ℂ) ^ s) heq
      _ = _ := by ring
  have hr : ∃ (ψ : PontryaginDual Jₛ) (z : ℂ), 0 < z.re ∧ normChart(χ) s = normChart(ψ) z := ⟨χ, s, hs, rfl⟩
  exact hi.trans ((sLocalRadialMellinIntegral_eq_theta σ hσ f χ s hs).trans
    ((sLocalThetaMellinIntegral_eq_zeta f hr).trans (sLocalIdelicZFunction_eq_integral f hr).symm))

/-- Paper: (5.4.2.6), p. 276.
Applying the two shifted Mellin transforms to the upper left arrow gives the
lower zeta pair on every theta class.
Deviation: The first and conjugate isotypes use opposite frequency shifts. -/
theorem sLocalCech_left_commutes (χ : PontryaginDual Jₛ)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (_hτ : RightInverse τ mₛ)
    (x : ℝ) (_hx : ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I))
    (M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺)
    (M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺)
    (_h₁ : ∀ f s, s ∈ rightHalf →
      (M₁ f).val s = ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t
        ∂positiveRealHaar)
    (_h₂ : ∀ f s, s ∈ rightHalf →
      (M₂ f).val s = ∫ t, mellinIntegrand(τ, f.val.val, s - (x : ℂ) * Complex.I) t
        ∂positiveRealHaar)
    (f : ℬₛ) :
    let p : upperMiddle(χ) := cechThetaPair(χ) (Submodule.Quotient.mk f)
    EqOn (M₁ p.1).val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
    EqOn (M₂ p.2).val (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf := by
  let p : upperMiddle(χ) := cechThetaPair(χ) (Submodule.Quotient.mk f)
  have hp := (existsUnique_sLocalCechThetaPair (F := F) (S := S) χ).exists.choose_spec f
  have hx' (t : ℝ≥0ˣ) : (χ⁻¹ (τ t) : ℂ) =
      (normℝ(t) : ℂ) ^ (((-x : ℝ) : ℂ) * Complex.I) := by
    change (χ (τ t) : ℂ)⁻¹ = _
    rw [_hx, Complex.ofReal_neg, neg_mul, Complex.cpow_neg]
  constructor
  · intro s hs
    refine (_h₁ p.1 s hs).trans ?_
    refine Eq.trans (integral_congr_ae (.of_forall fun t ↦ ?_))
      (sLocalCech_left_commutes_mellin χ τ _hτ x _hx f s hs)
    exact congrArg (· * (normℝ(t) : ℂ) ^ (s + (x : ℂ) * Complex.I))
      (congrFun hp.1 (τ t))
  · intro s hs
    refine (_h₂ p.2 s hs).trans ?_
    have h := sLocalCech_left_commutes_mellin χ⁻¹ τ _hτ (-x) hx' (Fourierₛ f) s hs
    simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at h
    refine Eq.trans (integral_congr_ae (.of_forall fun t ↦ ?_)) h
    exact congrArg (· * (normℝ(t) : ℂ) ^ (s - (x : ℂ) * Complex.I))
      (congrFun hp.2 (τ t))


/-- A holomorphic factor with polynomial growth on compact substrips acts continuously
after reflection. Point evaluations give the closed graph. -/
private theorem decayFourier_bergman_reflect_multiplier (I J : Set ℝ)
    (hoI : IsOpen I) (hiI : OrdConnected I) (hnI : I.Nonempty)
    (hoJ : IsOpen J) (hiJ : OrdConnected J) (hnJ : J.Nonempty)
    (hJ : ∀ a ∈ J, 1 - a ∈ I)
    (r : ℂ → ℂ) (hr : DifferentiableOn ℂ r (Complex.re ⁻¹' J))
    (hbound : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ J →
      ∃ C ≥ (0 : ℝ), ∃ n : ℕ, ∀ z : ℂ, z.re ∈ Icc a b →
        ‖r z‖ ≤ C * (1 + ‖z‖) ^ n) :
    ∃ T : SchwartzBergman I →L[ℂ] SchwartzBergman J,
      ∀ f z, z.re ∈ J → (T f).val z = r z * f.val (1 - z) := by
  let G (f : SchwartzBergman I) : ℂ → ℂ :=
    (Complex.re ⁻¹' J).indicator (fun z ↦ r z * f.val (1-z))
  have hG (f : SchwartzBergman I) : G f ∈ schwartzBergmanSubmodule J := by
    refine ⟨fun z hz ↦ indicator_of_notMem hz _, ?_, ?_⟩
    · have hd : Differentiable ℂ (fun z : ℂ ↦ 1 - z) :=
        (differentiable_const (1 : ℂ)).sub differentiable_id
      apply DifferentiableOn.congr (hr.mul (f.property.2.1.comp hd.differentiableOn _))
      · intro z hz
        exact indicator_of_mem hz _
      · intro z hz
        change (1 - z).re ∈ I
        simpa only [Complex.sub_re, Complex.one_re] using hJ z.re hz
    · intro a b hab hj N
      have hab' : 1-b ≤ 1-a := by linarith
      have hI : Icc (1-b) (1-a) ⊆ I := by
        intro s hs
        have h : 1 - s ∈ Icc a b := ⟨by linarith [hs.2], by linarith [hs.1]⟩
        simpa only [sub_sub_cancel] using hJ _ (hj h)
      obtain ⟨C, hC, k, hk⟩ := hbound a b hab hj
      obtain ⟨A, hA⟩ := f.property.2.2 _ _ hab' hI 0
      obtain ⟨B, hB⟩ := f.property.2.2 _ _ hab' hI (N + k)
      refine ⟨C * (3 ^ (N+k) : ℝ) * max A B, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      let w : ℂ := 1-z
      have hw : w.re ∈ Icc (1-b) (1-a) := by
        change (1-z).re ∈ Icc (1-b) (1-a)
        rw [Complex.sub_re, Complex.one_re]
        exact ⟨sub_le_sub_left hz.2 _, sub_le_sub_left hz.1 _⟩
      have hN : ‖z‖ ≤ 1 + ‖w‖ := by simpa [w] using norm_sub_le (1 : ℂ) w
      have hle : ‖z‖ ^ N * (1 + ‖z‖)^k * ‖f.val w‖ ≤
          (3 ^ (N+k) : ℝ) * max A B := by
        rcases le_total ‖w‖ 1 with h | h
        · have hZ : ‖z‖ ≤ 3 := by linarith
          have hZ' : 1 + ‖z‖ ≤ 3 := by linarith
          have hf : ‖f.val w‖ ≤ max A B :=
            (by simpa only [pow_zero, one_mul] using hA (mem_image_of_mem _ hw) : ‖f.val w‖ ≤ A).trans
              (le_max_left _ _)
          rw [pow_add]
          gcongr
        · have hZ : ‖z‖ ≤ 3 * ‖w‖ := by linarith
          have hZ' : 1 + ‖z‖ ≤ 3 * ‖w‖ := by linarith
          have hf := hB (mem_image_of_mem _ hw)
          rw [norm_mul, norm_pow] at hf
          calc
            _ ≤ (3 * ‖w‖)^N * (3 * ‖w‖)^k * ‖f.val w‖ := by gcongr
            _ = (3 ^ (N+k) : ℝ) * (‖w‖^(N+k) * ‖f.val w‖) := by
              rw [← pow_add, mul_pow, mul_assoc]
            _ ≤ _ := mul_le_mul_of_nonneg_left (hf.trans (le_max_right _ _)) (by positivity)
      change ‖z ^ N * G f z‖ ≤ _
      dsimp only [G]
      rw [indicator_of_mem (show z ∈ Complex.re ⁻¹' J from hj hz), norm_mul, norm_pow, norm_mul]
      calc
        _ ≤ ‖z‖ ^ N * ((C * (1+‖z‖)^k) * ‖f.val w‖) := by gcongr; exact hk z hz
        _ = C * (‖z‖ ^ N * (1+‖z‖)^k * ‖f.val w‖) := by ring
        _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hle hC
  let X := SchwartzBergman I
  let Y := SchwartzBergman J
  let L : X →ₗ[ℂ] Y :=
    { toFun := fun f ↦ ⟨G f, hG f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun z ↦ by
        change G (f + g) z = G f z + G g z
        by_cases hz : z ∈ Complex.re ⁻¹' J
        · simp only [G, indicator_of_mem hz]
          exact mul_add _ _ _
        · simp only [G, indicator_of_notMem hz, zero_add])
      map_smul' := fun c f ↦ Subtype.ext (funext fun z ↦ by
        change G (c • f) z = c * G f z
        by_cases hz : z ∈ Complex.re ⁻¹' J
        · simp only [G, indicator_of_mem hz]
          exact mul_left_comm _ _ _
        · simp only [G, indicator_of_notMem hz, mul_zero]) }
  have hL (f : X) (z : ℂ) : (L f).val z = G f z := rfl
  let V : Submodule ℂ (ℂ → ℂ) := schwartzBergmanSubmodule J
  let i : Y →L[ℂ] V :=
    ⟨LinearMap.id, Continuous.subtype_mk
      (continuous_pi fun z ↦ decayFourier_bergman_eval J hoJ hiJ hnJ z) _⟩
  let u : X →L[ℂ] V := ⟨L, Continuous.subtype_mk (continuous_pi fun z ↦ ?_) _⟩
  · obtain ⟨_, T, hT⟩ := frechet_factorization (X := fun _ ↦ Y)
      (fun _ ↦ schwartzBergman_frechet J hoJ hiJ hnJ) (fun _ ↦ i)
      (fun _ _ _ h ↦ h) (fun _ ↦ Subset.rfl) (fun v ↦ ⟨0, v, rfl⟩)
      (schwartzBergman_frechet I hoI hiI hnI) u
    refine ⟨T, fun f z hz ↦ ?_⟩
    have heq := congrArg (fun v : V ↦ v.val z) (DFunLike.congr_fun hT f)
    change (T f).val z = G f z at heq
    refine heq.trans ?_
    exact indicator_of_mem (show z ∈ Complex.re ⁻¹' J from hz) _
  · change Continuous (fun f : X ↦ G f z)
    by_cases hz : z.re ∈ J
    · simpa only [G, indicator_of_mem (show z ∈ Complex.re ⁻¹' J from hz)] using
        (decayFourier_bergman_eval I hoI hiI hnI (1-z)).const_mul (r z)
    · simpa only [G, indicator_of_notMem (show z ∉ Complex.re ⁻¹' J from hz)] using
        (continuous_const (y := (0 : ℂ)) : Continuous (fun _ : X ↦ (0 : ℂ)))

private theorem decayFourier_shift_norm (z : ℂ) (t : ℝ) (n : ℕ) :
    ‖z‖ ^ n ≤ (2 * (1 + |t|)) ^ n * (1 + ‖z - (t : ℂ) * Complex.I‖ ^ n) := by
  let w := z - (t : ℂ) * Complex.I
  have hz : ‖z‖ ≤ ‖w‖ + |t| := by
    calc
      ‖z‖ = ‖w + (t : ℂ) * Complex.I‖ := by rw [sub_add_cancel]
      _ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp [Real.norm_eq_abs]
  have h₁ : ‖w‖ + |t| ≤ (1 + |t|) * (1 + ‖w‖) := by
    nlinarith [mul_nonneg (abs_nonneg t) (norm_nonneg w)]
  have h₂ : (1 + ‖w‖) ^ n ≤ (2 : ℝ) ^ n * (1 + ‖w‖ ^ n) := by
    rcases le_total ‖w‖ 1 with hw | hw
    · have h : 1 + ‖w‖ ≤ 2 := by linarith
      exact (pow_le_pow_left₀ (by positivity) h n).trans
        (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
    · have h : 1 + ‖w‖ ≤ 2 * ‖w‖ := by linarith
      refine (pow_le_pow_left₀ (by positivity) h n).trans ?_
      rw [mul_pow]
      gcongr
      exact le_add_of_nonneg_left zero_le_one
  calc
    _ ≤ ((1 + |t|) * (1 + ‖w‖)) ^ n := pow_le_pow_left₀ (norm_nonneg _) (hz.trans h₁) _
    _ ≤ (1 + |t|) ^ n * (2 ^ n * (1 + ‖w‖ ^ n)) := by rw [mul_pow]; gcongr
    _ = _ := by rw [mul_pow]; ring

private theorem decayFourier_bergman_shift (I : Set ℝ) (f : SchwartzBergman I) (t : ℝ) :
    ∃ g : SchwartzBergman I, (∀ z, g.val z = f.val (z - (t : ℂ) * Complex.I)) ∧
      ∀ (a : I) (n : ℕ),
        lpNorm (weightedVerticalTrace a n g.val) 2 volume ≤
          (2 * (1 + |t|)) ^ n *
          (lpNorm (weightedVerticalTrace a 0 f.val) 2 volume +
            lpNorm (weightedVerticalTrace a n f.val) 2 volume) := by
  let τ (z : ℂ) := z - (t : ℂ) * Complex.I
  have hτ (z : ℂ) : (τ z).re = z.re := by simp [τ, Complex.mul_re]
  have hτd : Differentiable ℂ τ := differentiable_id.sub (differentiable_const _)
  have hg : f.val ∘ τ ∈ schwartzBergmanSubmodule I := by
    refine ⟨fun z hz ↦ f.property.1 (show (τ z).re ∉ I from by rw [hτ]; exact hz),
      f.property.2.1.comp hτd.differentiableOn
        (fun z hz ↦ (show (τ z).re ∈ I from by rw [hτ]; exact hz)), ?_⟩
    intro a b hab hsub n
    obtain ⟨C, hC⟩ := f.property.2.2 a b hab hsub 0
    obtain ⟨D, hD⟩ := f.property.2.2 a b hab hsub n
    refine ⟨(2 * (1 + |t|)) ^ n * (C+D), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hw : τ z ∈ Complex.re ⁻¹' Icc a b := by
      simpa only [mem_preimage, hτ] using hz
    have hx : ‖f.val (τ z)‖ ≤ C := by simpa using hC (mem_image_of_mem _ hw)
    have hy : ‖τ z‖ ^ n * ‖f.val (τ z)‖ ≤ D := by
      simpa only [norm_mul, norm_pow] using hD (mem_image_of_mem _ hw)
    change ‖z ^ n * f.val (τ z)‖ ≤ _
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ((2 * (1 + |t|)) ^ n * (1 + ‖τ z‖ ^ n)) * ‖f.val (τ z)‖ :=
        mul_le_mul_of_nonneg_right (decayFourier_shift_norm z t n) (norm_nonneg _)
      _ = (2 * (1 + |t|)) ^ n * (‖f.val (τ z)‖ + ‖τ z‖ ^ n * ‖f.val (τ z)‖) := by ring
      _ ≤ _ := by gcongr
  let g : SchwartzBergman I := ⟨f.val ∘ τ, hg⟩
  refine ⟨g, fun _ ↦ rfl, fun a n ↦ ?_⟩
  let B : ℝ := (2 * (1 + |t|)) ^ n
  let P (k : ℕ) (x : ℝ) := ‖weightedVerticalTrace a k f.val x‖
  let ρ (x : ℝ) := x - t
  have hρ : MeasurePreserving ρ (volume : Measure ℝ) volume := measurePreserving_sub_right volume t
  have hP (k : ℕ) : MemLp (P k) 2 volume :=
    (schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) k f).norm
  have hdom : MemLp (fun x ↦ B * (P 0 (ρ x) + P n (ρ x))) 2 volume :=
    (((hP 0).comp_measurePreserving hρ).add ((hP n).comp_measurePreserving hρ)).const_mul B
  have hbound (x : ℝ) :
      ‖weightedVerticalTrace a n g.val x‖ ≤ B * (P 0 (ρ x) + P n (ρ x)) := by
    let z : ℂ := (a.val : ℂ) + (x : ℂ) * Complex.I
    have heq : τ z = (a.val : ℂ) + (ρ x : ℂ) * Complex.I := by
      dsimp [τ,z,ρ]
      push_cast
      ring
    change ‖z ^ n * f.val (τ z)‖ ≤ B * (_ + _)
    rw [norm_mul, norm_pow]
    calc
      _ ≤ B * (1 + ‖τ z‖ ^ n) * ‖f.val (τ z)‖ :=
        mul_le_mul_of_nonneg_right (decayFourier_shift_norm z t n) (norm_nonneg _)
      _ = _ := by
        simp only [P, weightedVerticalTrace, ← heq, pow_zero, one_mul, norm_mul, norm_pow]
        ring
  refine (lpNorm_mono_real hdom hbound).trans ?_
  have hPρ (k : ℕ) : lpNorm (P k ∘ ρ) 2 volume = lpNorm (weightedVerticalTrace a k f.val) 2 volume := by
    have h := eLpNorm_comp_measurePreserving (hP k).aestronglyMeasurable hρ (p := (2 : ENNReal))
    change (eLpNorm (P k ∘ ρ) 2 volume).toReal = _
    rw [h]
    exact lpNorm_norm (schwartzBergman_trace_memLp I a 2 (by norm_num) (by norm_num) k f).aestronglyMeasurable _
  change lpNorm (B • ((P 0 ∘ ρ) + (P n ∘ ρ))) 2 volume ≤ _
  rw [lpNorm_const_smul]
  change ‖B‖ * lpNorm (P 0 ∘ ρ + P n ∘ ρ) 2 volume ≤
    B * (lpNorm (weightedVerticalTrace a 0 f.val) 2 volume +
      lpNorm (weightedVerticalTrace a n f.val) 2 volume)
  rw [Real.norm_of_nonneg (by dsimp [B]; positivity), ← hPρ 0, ← hPρ n]
  apply mul_le_mul_of_nonneg_left
    (lpNorm_add_le ((hP 0).comp_measurePreserving hρ) (by norm_num))
  dsimp [B]
  positivity


/-- A multiplier from the left half-plane to the overlap has polynomial growth
on compact substrips, by testing it on vertical translates of a Gaussian. -/
private theorem decayFourier_bergman_multiplier_growth (r : ℂ → ℂ)
    (T : SchwartzBergman (Iio 1) →L[ℂ] SchwartzBergman (Ioo 0 1))
    (hT : ∀ (f : SchwartzBergman (Iio 1)) (z : ℂ), z.re ∈ Ioo 0 1 →
      (T f).val z = r z * f.val z)
    (a b : ℝ) (hab : a ≤ b) (hsub : Icc a b ⊆ Ioo 0 1) :
    ∃ C ≥ (0 : ℝ), ∃ n : ℕ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖r z‖ ≤ C * (1 + ‖z‖) ^ n := by
  let I := Iio (1 : ℝ)
  let J := Ioo (0 : ℝ) 1
  have hnJ : J.Nonempty := ⟨1 / 2, by norm_num [J]⟩
  let E := SchwartzBergman I
  let V := SchwartzBergman J
  let Z := Complex.re ⁻¹' Icc a b
  let p (z : Z) : Seminorm ℂ V :=
    (normSeminorm ℂ ℂ).comp ((LinearMap.proj z.val).comp (schwartzBergmanSubmodule J).subtype)
  have hp (z : Z) : Continuous (p z) :=
    (decayFourier_bergman_eval J isOpen_Ioo ordConnected_Ioo hnJ z.val).norm
  have hbd : BddAbove (range p) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f
    obtain ⟨C, hC⟩ := f.property.2.2 a b hab hsub 0
    exact ⟨C, by
      rintro _ ⟨z, rfl⟩
      change ‖f.val z.val‖ ≤ C
      simpa only [pow_zero, one_mul] using hC (mem_image_of_mem _ z.property)⟩
  let : BarrelledSpace ℂ V := isFrechetTVS_barrelled
    (schwartzBergman_frechet J isOpen_Ioo ordConnected_Ioo hnJ)
  let q : Seminorm ℂ E := (⨆ z : Z, p z).comp T.toLinearMap
  have hq : Continuous q := by
    change Continuous (((⨆ z : Z, p z) : Seminorm ℂ V) ∘ T)
    rw [Seminorm.coe_iSup_eq hbd]
    exact (Seminorm.continuous_iSup p hp hbd).comp T.continuous
  let P : I × ℕ → Seminorm ℂ E := fun i ↦ Seminorm.of
    (fun f : schwartzBergmanSubmodule I ↦ (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
    (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2
  have hP : WithSeminorms P := withGeneratingSeminorms_spec (schwartzBergmanSubmodule I) P
  obtain ⟨s, D, _, hD⟩ := Seminorm.bound_of_continuous hP q hq
  let n := s.sup Prod.snd
  let g : E := ⟨_, gaussian_mem_schwartzBergmanSubmodule I isOpen_Iio⟩
  let K (i : I × ℕ) := (2 : ℝ) ^ i.2 * (P (i.1, 0) g + P i g)
  let C : ℝ := ∑ i ∈ s, K i
  have hK (i : I × ℕ) : 0 ≤ K i := by dsimp [K]; positivity
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ hK i
  refine ⟨(D : ℝ) * C, mul_nonneg (NNReal.coe_nonneg _) hC, n, fun z hz ↦ ?_⟩
  obtain ⟨f, hf, hnorm⟩ := decayFourier_bergman_shift I g z.im
  have hPbound (i : I × ℕ) (hi : i ∈ s) : P i f ≤ C * (1 + ‖z‖) ^ n := by
    have h := hnorm i.1 i.2
    change P i f ≤ (2 * (1 + |z.im|)) ^ i.2 * (P (i.1, 0) g + P i g) at h
    apply h.trans
    have hi' : i.2 ≤ n := Finset.le_sup hi
    have hre : 1 + |z.im| ≤ 1 + ‖z‖ := by linarith [Complex.abs_im_le_norm z]
    have hpow := (pow_le_pow_left₀ (by positivity) hre i.2).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg z)) hi')
    rw [mul_pow, mul_right_comm _ _ (P (i.1, 0) g + P i g)]
    refine mul_le_mul (Finset.single_le_sum (fun i _ ↦ hK i) hi) hpow (by positivity) hC
  have hsup : (s.sup P) f ≤ C * (1 + ‖z‖) ^ n :=
    Seminorm.finset_sup_apply_le (by positivity) hPbound
  have hqz : ‖(T f).val z‖ ≤ q f :=
    (le_ciSup hbd (⟨z, hz⟩ : Z)) (T f)
  have hzg : z - (z.im : ℂ) * Complex.I = (z.re : ℂ) := by
    exact sub_eq_iff_eq_add.mpr (Complex.re_add_im z).symm
  have hf1 : 1 ≤ ‖f.val z‖ := by
    rw [hf, hzg]
    change 1 ≤ ‖(Complex.re ⁻¹' I).indicator (fun z ↦ Complex.exp (z ^ 2)) (z.re : ℂ)‖
    have hzI : (z.re : ℂ) ∈ Complex.re ⁻¹' I := by
      simpa only [mem_preimage, Complex.ofReal_re] using (show z.re ∈ I from (hsub hz).2)
    rw [indicator_of_mem hzI, Complex.norm_exp, Real.one_le_exp_iff]
    norm_cast
    positivity
  calc
    ‖r z‖ ≤ ‖r z‖ * ‖f.val z‖ := le_mul_of_one_le_right (norm_nonneg _) hf1
    _ = ‖(T f).val z‖ := by rw [hT f z (hsub hz), norm_mul]
    _ ≤ q f := hqz
    _ ≤ (D : ℝ) * (s.sup P) f := hD f
    _ ≤ (D : ℝ) * (C * (1 + ‖z‖) ^ n) := mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = _ := by ring



/-- The dual Tate factors are reciprocals throughout the overlap. Use the character chart
calculation from the S-local zeta functional equation above. -/
private theorem decayFourier_rho_mul_reflect (χ : PontryaginDual Jₛ) (z : ℂ)
    (hz : z.re ∈ overlapInterval) :
    ρₛ(χ, z) * ρₛ(χ⁻¹, 1-z) = 1 := by
  have hneg : (QuotientGroup.mk (-1 : Aₛˣ) : Jₛ) = 1 := by
    refine (sIdeleQuotient_mk_eq_one F S _).2 ⟨-1, ?_⟩
    apply Units.ext
    simp
  have hdual (w : ℂ) :
      dualQuasiCharacter mₛ hmₛ (normChart(χ) w) = normChart(χ⁻¹) (1-w) := by
    ext1 g
    let N : ℂ := (normℝ(mₛ g) : ℂ)
    have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
    change N * normChart(χ) w g⁻¹ = ((χ g : ℂ)⁻¹ * N ^ (1-w))
    rw [map_inv]
    change N * ((χ g : ℂ) * N ^ w)⁻¹ = (χ g : ℂ)⁻¹ * N ^ (1-w)
    rw [Complex.cpow_sub _ _ hN, Complex.cpow_one, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have hpos : 0 < (1-z).re := by simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hz.2
  have h₁ : ContinuousAt (fun w ↦ ρₛ(χ, w)) z := by
    have h := sLocalRhoFactor_iteratedDeriv_analyticOn (F := F) (S := S) χ 0 z hz.1
    rw [iteratedDeriv_zero] at h
    exact h.continuousAt
  have h₂ : ContinuousAt (fun w ↦ ρₛ(χ⁻¹, w)) (1-z) := by
    have h := sLocalRhoFactor_iteratedDeriv_analyticOn (F := F) (S := S) χ⁻¹ 0 (1-z) hpos
    rw [iteratedDeriv_zero] at h
    exact h.continuousAt
  have he : (fun w ↦ ρₛ(χ,w) * ρₛ(χ⁻¹, 1-w)) =ᶠ[𝓝[≠] z] (fun _ ↦ 1 : ℂ → ℂ) := by
    filter_upwards [nhdsNE_le_codiscrete z (sLocalRhoFactor_mul_dual χ)] with w hw
    dsimp only at hw
    rw [hdual w, hneg, map_one] at hw
    exact hw
  exact tendsto_nhds_unique_of_eventuallyEq
    (h₁.mul (h₂.comp (continuousAt_const.sub continuousAt_id))).continuousWithinAt
    tendsto_const_nhds he

private theorem decayFourier_rho_growth (χ : PontryaginDual Jₛ)
    (a b : ℝ) (hab : a ≤ b) (hsub : Icc a b ⊆ overlapInterval) :
    ∃ C ≥ (0 : ℝ), ∃ n : ℕ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖ρₛ(χ,z)‖ ≤ C * (1 + ‖z‖) ^ n := by
  obtain ⟨D, hD, _⟩ := existsUnique_sLocalZetaMatchingDifference χ
  let T : SchwartzBergman leftInterval →L[ℂ] SchwartzBergman overlapInterval :=
    -(D.comp (ContinuousLinearMap.inr ℂ (SchwartzBergman rightInterval) (SchwartzBergman leftInterval)))
  apply decayFourier_bergman_multiplier_growth (fun z ↦ ρₛ(χ,z)) T _ a b hab hsub
  intro f z hz
  have he := hD (0, f) (show z ∈ overlap from hz)
  change -(D (0,f)).val z = _
  rw [he]
  change -(0 - ρₛ(χ,z) * f.val z) = _
  simp

private theorem decayFourier_reflected_interval (I : Set ℝ) (ho : IsOpen I)
    (hi : OrdConnected I) (hn : I.Nonempty) (hsub : I ⊆ overlapInterval) :
    IsOpen (reflect(I)) ∧ OrdConnected (reflect(I)) ∧ (reflect(I)).Nonempty ∧
      reflect(I) ⊆ overlapInterval := by
  refine ⟨ho.preimage (continuous_const.sub continuous_id),
    hi.preimage_anti (fun x y hxy ↦ sub_le_sub_left hxy _), ?_, ?_⟩
  · exact ⟨1 - hn.some, by simpa only [mem_preimage, sub_sub_cancel] using hn.some_mem⟩
  · intro a ha
    have h : 1-a ∈ overlapInterval := hsub ha
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

private theorem decayFourier_bergman_equiv (χ : PontryaginDual Jₛ) (I : Set ℝ)
    (ho : IsOpen I) (hi : OrdConnected I) (hn : I.Nonempty) (hsub : I ⊆ overlapInterval) :
    ∃ T : SchwartzBergman I ≃L[ℂ] SchwartzBergman (reflect(I)),
      ∀ f z, z.re ∈ reflect(I) → (T f).val z = ρₛ(χ⁻¹,z) * f.val (1-z) := by
  let J := reflect(I)
  obtain ⟨ho', hi', hn', hsub'⟩ := decayFourier_reflected_interval I ho hi hn hsub
  have hρ (η : PontryaginDual Jₛ) : DifferentiableOn ℂ (fun z ↦ ρₛ(η,z)) rightHalf := by
    have h := sLocalRhoFactor_iteratedDeriv_analyticOn (F := F) (S := S) η 0
    rw [iteratedDeriv_zero] at h
    exact h.differentiableOn
  obtain ⟨A, hA⟩ := decayFourier_bergman_reflect_multiplier I J ho hi hn ho' hi' hn'
    (fun _ h ↦ h) (fun z ↦ ρₛ(χ⁻¹,z)) ((hρ χ⁻¹).mono (fun _ h ↦ (hsub' h).1))
    (fun a b hab h ↦ decayFourier_rho_growth χ⁻¹ a b hab (h.trans hsub'))
  obtain ⟨B, hB⟩ := decayFourier_bergman_reflect_multiplier J I ho' hi' hn' ho hi hn
    (fun a h ↦ show 1-(1-a) ∈ I by rwa [sub_sub_cancel])
    (fun z ↦ ρₛ(χ,z)) ((hρ χ).mono (fun _ h ↦ (hsub h).1))
    (fun a b hab h ↦ decayFourier_rho_growth χ a b hab (h.trans hsub))
  have hfl (f : SchwartzBergman I) : B (A f) = f := by
    apply existsUnique_sLocalZetaPair_ext
    intro z hz
    have hz' : (1-z).re ∈ J := by
      change 1-(1-z).re ∈ I
      simpa only [Complex.sub_re, Complex.one_re, sub_sub_cancel] using (show z.re ∈ I from hz)
    rw [hB (A f) z hz, hA f (1-z) hz', sub_sub_cancel, ← mul_assoc,
      decayFourier_rho_mul_reflect χ z (hsub hz), one_mul]
  have hfr (f : SchwartzBergman J) : A (B f) = f := by
    apply existsUnique_sLocalZetaPair_ext
    intro z hz
    have hz' : (1-z).re ∈ I := by
      simpa only [Complex.sub_re, Complex.one_re] using (show 1-z.re ∈ I from hz)
    have h := decayFourier_rho_mul_reflect χ (1-z) (hsub hz')
    rw [sub_sub_cancel, mul_comm] at h
    rw [hA (B f) z hz, hB f (1-z) hz', sub_sub_cancel, ← mul_assoc, h, one_mul]
  let T : SchwartzBergman I ≃L[ℂ] SchwartzBergman J :=
    { toLinearMap := A.toLinearMap
      invFun := B
      left_inv := hfl
      right_inv := hfr
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  exact ⟨T, hA⟩

/-- Restrict the family of weighted Schwartz–Bruhat conditions to a smaller interval. -/
private theorem decayFourier_restrict (I J : Set ℝ) (hIJ : I ⊆ J) (ω : PontryaginDual J₁)
    (v : Eω(J, ω)) : ∃ u : Eω(I, ω), u.val.val = v.val.val := by
  let w : Ẽ(I) := ⟨v.val.val, (Submodule.mem_iInf _).mpr fun a ↦
    (Submodule.mem_iInf _).mp v.val.property ⟨a.val, hIJ a.property⟩⟩
  have hw := (mem_sLocalDecayIsotype J ω v.val).mp v.property
  exact ⟨⟨w, (mem_sLocalDecayIsotype I ω w).mpr hw⟩, rfl⟩

/-- Construct the extension in the two shifted Mellin coordinates using the
S-local Čech commutation and the zeta functional equation. -/
private theorem decayFourier_extension (χ : PontryaginDual Jₛ) (I : Set ℝ)
    (ho : IsOpen I) (hi : OrdConnected I) (hn : I.Nonempty) (hsub : I ⊆ overlapInterval) :
    ∃ e : Eω(I, restrict₁(χ)) ≃L[ℂ] Eω(reflect(I), restrict₁(χ⁻¹)),
      ∀ f : ℬₛ, ∃ (u : Eω(I, restrict₁(χ))) (v : Eω(reflect(I), restrict₁(χ⁻¹))), e u = v ∧
        (∀ g : Jₛ, u.val.val g = φω(restrict₁(χ)) f g) ∧
        (∀ g : Jₛ, v.val.val g = φω(restrict₁(χ⁻¹)) (Fourierₛ f) g) := by
  let τ : ℝ≥0ˣ →ₜ* Jₛ := (sIdeleQuotientNorm_exists_section F S).choose
  have hτ : RightInverse τ mₛ := (sIdeleQuotientNorm_exists_section F S).choose_spec
  have hfreq := (existsUnique_sLocalCechFrequency (F := F) (S := S) χ τ).exists
  let x := hfreq.choose
  have hx := hfreq.choose_spec
  have hreflect := decayFourier_reflected_interval I ho hi hn hsub
  have hsub' := hreflect.2.2.2
  have h₁ := (existsUnique_sLocalDecayMellin (F := F) (S := S)
    τ hτ I ho hi hn restrict₁(χ) x).exists
  have h₂ := (existsUnique_sLocalDecayMellin (F := F) (S := S)
    τ hτ (reflect(I)) hreflect.1 hreflect.2.1 hreflect.2.2.1 restrict₁(χ⁻¹) (-x)).exists
  let M := h₁.choose
  let M' := h₂.choose
  have hM := h₁.choose_spec
  have hM' := h₂.choose_spec
  have hT' := decayFourier_bergman_equiv (F := F) (S := S) χ I ho hi hn hsub
  let T := hT'.choose
  have hT := hT'.choose_spec
  let e := M.trans (T.trans M'.symm)
  refine ⟨e, fun f ↦ ?_⟩
  let p := cechThetaPair(χ) (Submodule.Quotient.mk f)
  have hp := (existsUnique_sLocalCechThetaPair χ).exists.choose_spec f
  have hu' := decayFourier_restrict (F := F) (S := S) I rightInterval
    (fun _ h ↦ (hsub h).1) restrict₁(χ) p.1
  have hv' := decayFourier_restrict (F := F) (S := S) (reflect(I)) rightInterval
    (fun _ h ↦ (hsub' h).1) restrict₁(χ⁻¹) p.2
  let u := hu'.choose
  let v := hv'.choose
  have hu := hu'.choose_spec
  have hv := hv'.choose_spec
  refine ⟨u, v, ?_, fun g ↦ congrFun (hu.trans hp.1) g, fun g ↦ congrFun (hv.trans hp.2) g⟩
  have hR₁ := (existsUnique_sLocalDecayMellin (F := F) (S := S) τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi ⟨1, one_pos⟩ restrict₁(χ) x).exists
  have hR₂ := (existsUnique_sLocalDecayMellin (F := F) (S := S) τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi ⟨1, one_pos⟩ restrict₁(χ⁻¹) (-x)).exists
  let R := hR₁.choose
  let R' := hR₂.choose
  have hR := hR₁.choose_spec
  have hR' := hR₂.choose_spec
  have hcomm := sLocalCech_left_commutes χ τ hτ x hx R R'
    (fun w z hz ↦ (hR w z hz).2)
    (fun w z hz ↦ by
      simpa only [R', Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using (hR' w z hz).2) f
  have hMu (z : ℂ) (hz : z.re ∈ I) : (M u).val z = Zₛ f (normChart(χ) z) := by
    have hz' : z ∈ rightHalf := (hsub hz).1
    rw [(hM u z hz).2, hu, ← (hR p.1 z hz').2]
    exact hcomm.1 hz'
  have hMv (z : ℂ) (hz : z.re ∈ reflect(I)) :
      (M' v).val z = Zₛ (Fourierₛ f) (normChart(χ⁻¹) z) := by
    have hz' : z ∈ rightHalf := (hsub' hz).1
    rw [(hM' v z hz).2, hv, ← (hR' p.2 z hz').2]
    exact hcomm.2 hz'
  have heq : T (M u) = M' v := by
    apply existsUnique_sLocalZetaPair_ext
    intro z hz
    have hz' : (1-z).re ∈ I := by
      simpa only [Complex.sub_re, Complex.one_re] using (show 1-z.re ∈ I from hz)
    have hρ := decayFourier_rho_mul_reflect χ (1-z) (hsub hz')
    rw [sub_sub_cancel, mul_comm] at hρ
    have hFE := existsUnique_sLocalZetaPair_equation χ f (1-z) (hsub hz')
    rw [sub_sub_cancel] at hFE
    calc
      (T (M u)).val z = ρₛ(χ⁻¹,z) * (M u).val (1-z) := hT _ z hz
      _ = ρₛ(χ⁻¹,z) * Zₛ f (normChart(χ) (1-z)) := congrArg (ρₛ(χ⁻¹,z) * ·) (hMu _ hz')
      _ = Zₛ (Fourierₛ f) (normChart(χ⁻¹) z) := by
        rw [hFE, ← mul_assoc, hρ, one_mul]
      _ = (M' v).val z := (hMv _ hz).symm
  have hsymm : M'.symm (T (M u)) = M'.symm (M' v) := congrArg M'.symm heq
  exact hsymm.trans (M'.symm_apply_apply v)

-- The twisting calculation below is adapted from the zero pole-bound lift in Ch07 Sec2.
/-- Multiplication of a test by a character of the idele quotient factors that character
out of the S-unit sum, since every projected diagonal S-unit has class one. -/
private theorem decayFourier_theta_twist_sum (b : QuasiCharacter Jₛ)
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
private theorem decayFourier_theta_twist (η : PontryaginDual J₁)
    (χ : PontryaginDual Jₛ) (hχ : ∀ u : J₁, χ u.val = η u) (f f' : ℬₛ)
    (h : ∀ z : Aₛˣ, f' (Multiplicative.ofAdd z.val) =
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ⁻¹) (QuotientGroup.mk z) * f (Multiplicative.ofAdd z.val))
    (g : Jₛ) : sLocalHomogeneousAdelicThetaLinearMap F S η f' g =
      (χ g : ℂ)⁻¹ * sLocalHomogeneousAdelicThetaLinearMap F S 1 f g := by
  let : MeasurableSpace J₁ := borel _
  let μ := sLocalNormOneQuotientMeasure F S
  let b := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ⁻¹
  have hfactor (u : J₁) : b (g * u.val) * (η u : ℂ) = (χ g : ℂ)⁻¹ := by
    change (((χ (g * u.val))⁻¹ : Circle) : ℂ) * (η u : ℂ) = _
    rw [map_mul, Circle.coe_inv, Circle.coe_mul, hχ]
    field_simp [Circle.coe_ne_zero]
  have hint (u : J₁) :
      sLocalAdelicThetaOnClasses F S f' (g * u.val) * (η u : ℂ) =
      (χ g : ℂ)⁻¹ * (sLocalAdelicThetaOnClasses F S f (g * u.val) * ((1 : PontryaginDual J₁) u : ℂ)) := by
    rw [decayFourier_theta_twist_sum b f f' h, mul_right_comm, hfactor]
    change _ = _ * (_ * ((1 : Circle) : ℂ))
    rw [Circle.coe_one, mul_one]
  exact (sLocalHomogeneousAdelicThetaLinearMap_apply η f' g).trans
    ((MeasureTheory.integral_congr_ae (μ := μ) (.of_forall hint)).trans
      ((MeasureTheory.integral_const_mul _ _).trans
        (congrArg ((χ g : ℂ)⁻¹ * ·) (sLocalHomogeneousAdelicThetaLinearMap_apply (F := F) (S := S) (1 : PontryaginDual J₁) f g).symm)))


/-- Transport Appendix D's density of compactly supported profiles by logarithmic coordinates. -/
private theorem decayFourier_dense_compact_profiles (I : Set ℝ) (hi : OrdConnected I)
    (hn : I.Nonempty) :
    Dense {f : PositiveRealExponentialDecay I | HasCompactSupport f.val} := by
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  let t₀ : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm : IsModulation m := ⟨isProperMap_id, t₀, by
    intro h
    have he : (2 : ℝ≥0) = 1 := congrArg Units.val h
    norm_num at he⟩
  have hs : Surjective m := surjective_id
  obtain ⟨L, hL⟩ := positiveRealExponentialDecay_log_equiv I hi hn
  let j := bruhatCompactSupportToModulatedExponentialDecay m I hm hs
  have hd : DenseRange j := bruhatCompactSupport_dense_modulatedExponentialDecay m I hm hs hi hn
  apply (L.symm.surjective.denseRange.dense_image L.symm.continuous hd).mono
  rintro _ ⟨_, ⟨φ, rfl⟩, rfl⟩
  let v : ℝ ≃ₜ ℝ≥0ˣ :=
    Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he : (L.symm (j φ)).val = fun x ↦ φ.val (v x) := by
    funext x
    have h := hL (L.symm (j φ)) (v x)
    rw [L.apply_symm_apply] at h
    change (j φ).val (v x) = (L.symm (j φ)).val (Real.log (Real.exp x)) at h
    rw [Real.log_exp] at h
    exact h.symm.trans (bruhatCompactSupportToModulatedExponentialDecay_apply m I hm hs φ _)
  change HasCompactSupport (L.symm (j φ)).val
  rw [he]
  exact φ.property.2.comp_homeomorph v

private theorem decayFourier_compact_profile_all_weights (I : Set ℝ) (hI : I.Nonempty)
    (f : PositiveRealExponentialDecay I) (hf : HasCompactSupport f.val) :
    ∃ p : PositiveRealExponentialDecay univ, p.val = f.val := by
  let a : I := ⟨hI.some, hI.some_mem⟩
  let T := logExponentialDecayTwist I a f
  have hexp (b : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ ↦ (Real.exp (b * t) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f.val := by
    have he : (fun x : ℝ ↦ T x * (Real.exp (-(a : ℝ) * x) : ℂ)) = f.val := by
      funext x
      show T x * (Real.exp (-(a : ℝ) * x) : ℂ) = f.val x
      rw [show T x = _ from logExponentialDecayTwist_apply I a f x, mul_right_comm,
        ← Complex.ofReal_mul, ← Real.exp_add, show (a : ℝ) * x + -(a : ℝ) * x = 0 by ring,
        Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [← he]
    exact (T.smooth ⊤).mul (hexp (-(a : ℝ)))
  refine ⟨⟨f.val, (Submodule.mem_iInf _).2 fun b ↦ ?_⟩, rfl⟩
  let ψ (x : ℝ) := (Real.exp ((b : ℝ) * x) : ℂ) * f.val x
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := (hexp (b : ℝ)).mul hφ
  have hs : HasCompactSupport ψ := hf.mul_left
  exact ⟨hs.toSchwartzMap hψ, rfl⟩

/-- A compact log profile, transported to the chosen isotype, is represented
by a polar-free theta test. This is the lift used for the zero pole bound in
Chapter 7, with the compact profile supplied directly. -/
private theorem decayFourier_compact_theta_lift (I : Set ℝ) (hn : I.Nonempty) (η : PontryaginDual J₁)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ)
    (Φ : Eω(I, η) ≃L[ℂ] PositiveRealExponentialDecay I)
    (hΦ : ∀ p t (k : J₁), (Φ.symm p).val.val (τ t * k.val) =
      star (η k : ℂ) * p.val (Real.log normℝ(t)))
    (p : PositiveRealExponentialDecay I) (hp : HasCompactSupport p.val) :
    ∃ f : ℬₛ, ∀ g : Jₛ, φω(η) f g = (Φ.symm p).val.val g := by
  let r (w : {w : InfinitePlace F // w.IsReal}) :
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.property,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal w.property).toHomeomorph.isHomeomorph⟩
  let c (w : {w : InfinitePlace F // w.IsComplex}) :
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.property).toHomeomorph.isHomeomorph⟩
  let rchar := existsUnique_sLocalNormSectionCharacter (F := F) (S := S) τ hτ η
  let χ : PontryaginDual Jₛ := rchar.exists.choose
  have hχ := rchar.exists.choose_spec
  have ht (t : ℝ≥0ˣ) : χ (τ t) = 1 := hχ.2 t
  have hres (u : J₁) : χ u.val = η u := DFunLike.congr_fun hχ.1 u
  have hprofile := decayFourier_compact_profile_all_weights I hn p hp
  let p' := hprofile.choose
  have hp' := hprofile.choose_spec
  have hlift := sLocalHomogeneousTheta_trivial_exists_polarFree (F := F) (S := S) r c p'
  let f := hlift.choose
  have hf := hlift.choose_spec
  have hmul := sAdelePolarFree_quasiCharacter_mul (F := F) (S := S) r c
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ⁻¹)
  let M := hmul.choose
  have hM := hmul.choose_spec
  refine ⟨(M f).val, fun g ↦ ?_⟩
  let t := mₛ g
  let k : J₁ := ⟨g / τ t, by simp [MonoidHom.mem_ker, hτ t, t]⟩
  have hg : τ t * k.val = g := by
    change τ t * (g / τ t) = g
    exact (mul_comm _ _).trans (div_mul_cancel _ _)
  have hk : mₛ (τ t * k.val) = t := by rw [map_mul, k.property, hτ, mul_one]
  have hθ : φω(η) (M f).val (τ t * k.val) =
      (χ (τ t * k.val) : ℂ)⁻¹ * φω((1 : PontryaginDual J₁)) f.val (τ t * k.val) :=
    decayFourier_theta_twist (F := F) (S := S) η χ hres f.val (M f).val (hM f) _
  have hr : φω((1 : PontryaginDual J₁)) f.val (τ t * k.val) =
      p.val (Real.log normℝ(t)) := by
    refine (hf _).trans ?_
    rw [hk, hp']
  have hχk : (χ (τ t * k.val) : ℂ)⁻¹ = star (η k : ℂ) := by
    rw [map_mul, ht, one_mul, hres]
    exact (Circle.coe_inv (η k)).symm.trans (Circle.coe_inv_eq_conj (η k))
  have htest : φω(η) (M f).val (τ t * k.val) = (Φ.symm p).val.val (τ t * k.val) :=
    hθ.trans ((congrArg₂ (· * ·) hχk hr).trans (hΦ p t k).symm)
  exact hg ▸ htest

/-- Compact radial profiles lift to tests, so homogeneous theta functions are dense
in each isotype of an interval decay space. -/
private theorem sLocalDecay_dense_theta (I : Set ℝ) (hi : OrdConnected I)
    (hn : I.Nonempty) (ω : PontryaginDual J₁) :
    Dense {u : Eω(I, ω) | ∃ f : ℬₛ, ∀ g, u.val.val g = φω(ω) f g} := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  have hcoordinates := existsUnique_sLocalCechRadialReflection_isotypeEquiv
    (F := F) (S := S) τ hτ I hi hn ω
  let Φ := hcoordinates.choose
  have hΦ := hcoordinates.choose_spec.2
  apply (Φ.symm.surjective.denseRange.dense_image Φ.symm.continuous
    (decayFourier_dense_compact_profiles I hi hn)).mono
  rintro _ ⟨p, hp, rfl⟩
  have hlift := decayFourier_compact_theta_lift (F := F) (S := S) I hn ω τ hτ Φ hΦ p hp
  exact ⟨hlift.choose, fun g ↦ (hlift.choose_spec g).symm⟩

/-- Paper: Proposition 5.4.2.1(1), p. 275.
Fourier transform extends uniquely between the weighted isotype and the conjugate
isotype for the reflected exponent interval. Its value on each embedded homogeneous
theta function is the homogeneous theta function of the Fourier-transformed test.
Deviation: The extension identity uses the two isotypes of the theta quotient. -/
theorem existsUnique_sLocalDecayFourier (χ : PontryaginDual Jₛ) (I : Set ℝ) (_hOpen : IsOpen I)
    (_hInt : OrdConnected I) (_hne : I.Nonempty) (_hsub : I ⊆ overlapInterval) :
    let domain : Submodule ℂ Ẽ(I) := sLocalDecayIsotype (F := F) (S := S) I (restrict₁(χ))
    let codomain : Submodule ℂ Ẽ(reflect(I)) :=
      sLocalDecayIsotype (F := F) (S := S) (reflect(I)) (restrict₁(χ⁻¹))
    ∃! e : domain ≃L[ℂ] codomain,
      let transform : domain → codomain := e
      ∀ f : ℬₛ, ∃ (u : domain) (v : codomain), transform u = v ∧
        (∀ g : Jₛ, u.val.val g = φω(restrict₁(χ)) f g) ∧
        (∀ g : Jₛ, v.val.val g = φω(restrict₁(χ⁻¹)) (Fourierₛ f) g) := by
  have hex := decayFourier_extension (F := F) (S := S) χ I _hOpen _hInt _hne _hsub
  let e := hex.choose
  have he := hex.choose_spec
  refine ⟨e, he, fun e' he' ↦ ?_⟩
  have hsection := sIdeleQuotientNorm_exists_section F S
  let τ := hsection.choose
  have hτ := hsection.choose_spec
  let D : Set Eω(I, restrict₁(χ)) :=
    {u | ∃ f : ℬₛ, ∀ g, u.val.val g = φω(restrict₁(χ)) f g}
  have hD : Dense D := sLocalDecay_dense_theta I _hInt _hne restrict₁(χ)
  have heq : EqOn e' e D := by
    intro u hu
    change ∃ f : ℬₛ, ∀ g, u.val.val g = φω(restrict₁(χ)) f g at hu
    let f := hu.choose
    have hf := hu.choose_spec
    have h₁ := he' f
    have h₂ := he f
    let u₁ := h₁.choose
    let u₂ := h₂.choose
    let v₁ := h₁.choose_spec.choose
    let v₂ := h₂.choose_spec.choose
    have hw₁ := h₁.choose_spec.choose_spec
    have hw₂ := h₂.choose_spec.choose_spec
    have hu₁ : u₁ = u :=
      Subtype.ext (Subtype.ext (funext fun g ↦ (hw₁.2.1 g).trans (hf g).symm))
    have hu₂ : u₂ = u :=
      Subtype.ext (Subtype.ext (funext fun g ↦ (hw₂.2.1 g).trans (hf g).symm))
    have hv : v₁ = v₂ :=
      Subtype.ext (Subtype.ext (funext fun g ↦ (hw₁.2.2 g).trans (hw₂.2.2 g).symm))
    calc
      e' u = e' u₁ := congrArg e' hu₁.symm
      _ = v₁ := hw₁.1
      _ = v₂ := hv
      _ = e u₂ := hw₂.1.symm
      _ = e u := congrArg e hu₂
  have hJ := decayFourier_reflected_interval I _hOpen _hInt _hne _hsub
  let Ψ := (existsUnique_sLocalCechRadialReflection_isotypeEquiv (F := F) (S := S)
    τ hτ (reflect(I)) hJ.2.1 hJ.2.2.1 restrict₁(χ⁻¹)).choose
  let : T2Space (PositiveRealExponentialDecay (reflect(I))) :=
    (positiveRealExponentialDecay_isEmbedding (reflect(I)) hJ.2.2.1).t2Space
  let : T2Space Eω(reflect(I), restrict₁(χ⁻¹)) :=
    T2Space.of_injective_continuous Ψ.injective Ψ.continuous
  refine ContinuousLinearEquiv.ext (funext fun u ↦ ?_)
  exact closure_minimal (fun _ hv ↦ heq hv)
    (isClosed_eq e'.continuous e.continuous) (hD u)

-- Adapted from the Schwartz–Bruhat square-integrability argument in Ch09, §1.
open scoped ENNReal in
private theorem sLocalDecay_schwartz_memLp_two {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] {μ : Measure G}
    (f : SchwartzBruhat G) (hf : Integrable (f : G → ℂ) μ) : MemLp (f : G → ℂ) 2 μ := by
  obtain ⟨p, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff _).mp
    (show (f : G → ℂ) ∈ schwartzBruhatSubmodule G from
      (show schwartzBruhatSubmodule G from f).property)
  let i : ElementarySchwartzIndex e.realDim e.torusDim e.latticeRank := (0, 0, 0, 0)
  let M := elementarySchwartzBound (s : _ → ℂ) i
  have hM : M < ⊤ := s.property.2 i
  have hMbound (z) : ‖s z‖ ≤ M.toReal := by
    have hz : (‖s z‖₊ : ℝ≥0∞) ≤ M := by
      change _ ≤ elementarySchwartzBound _ (0, 0, 0, 0)
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ℝ≥0∞)) z
    exact ENNReal.toReal_mono hM.ne hz
  have hbound (x : G) : ‖f x‖ ≤ M.toReal := by
    rw [← congrFun hs x, schwartzBruhatStageRealization_apply]
    split_ifs
    · exact hMbound _
    · simp
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply (hf.norm.const_mul M.toReal).mono' (hf.aestronglyMeasurable.norm.pow 2)
  exact .of_forall fun x ↦ by
    change ‖‖f x‖ ^ 2‖ ≤ M.toReal * ‖f x‖
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

/-- The square root of the norm changes the weighted L² norm to the Haar L² norm. -/
private theorem sLocalDecay_untwist_mem (f : SchwartzBruhat Jₛ) :
    MemLp (fun g : Jₛ ↦ f g / (Real.sqrt (normℝ(mₛ g)) : ℂ)) 2 μweighted := by
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : SecondCountableTopology Jₛ := sLocalDecay_secondCountable
  let : (μₛ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  let w (g : Jₛ) := (mₛ g).val
  have hw : Continuous w := Units.continuous_val.comp hmₛ
  have hp (g : Jₛ) : 0 < (w g : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hq (g : Jₛ) : 0 < Real.sqrt (w g : ℝ) := Real.sqrt_pos.2 (hp g)
  have hf := SchwartzBruhat.integrable μₛ f
  have hm := sLocalDecay_schwartz_memLp_two f hf
  have hc := schwartzBruhat_continuous f
  have hdiv := hc.div (Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (NNReal.continuous_coe.comp hw))) fun g ↦ Complex.ofReal_ne_zero.mpr (hq g).ne'
  apply (memLp_two_iff_integrable_sq_norm hdiv.aestronglyMeasurable).mpr
  simp only [ENNReal.ofReal_coe_nnreal]
  apply (integrable_withDensity_iff_integrable_coe_smul hw.measurable).mpr
  apply ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hm).congr (.of_forall fun g ↦ ?_)
  change ‖f g‖ ^ 2 = (w g : ℝ) * ‖f g / (Real.sqrt (w g : ℝ) : ℂ)‖ ^ 2
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hq g).le, div_pow, Real.sq_sqrt (hp g).le,
    mul_div_cancel₀ _ (hp g).ne']

private theorem sLocalDecay_untwistL2 :
    ∃ L : SchwartzBruhat Jₛ →L[ℂ] L²ₛ, ∀ f,
      ⇑(L f) =ᵐ[μweighted] fun g : Jₛ ↦ f g / (Real.sqrt (normℝ(mₛ g)) : ℂ) := by
  let : SecondCountableTopology Jₛ := sLocalDecay_secondCountable
  let v : SchwartzBruhat Jₛ →ₗ[ℂ] (Jₛ → ℂ) := LinearMap.pi fun g ↦
    ((Real.sqrt (normℝ(mₛ g)) : ℂ)⁻¹) • (show SchwartzBruhat Jₛ →ₗ[ℂ] ℂ from
      { toFun := fun f ↦ f g, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl })
  have hv (f : SchwartzBruhat Jₛ) (g : Jₛ) : v f g = f g / (Real.sqrt (normℝ(mₛ g)) : ℂ) :=
    (mul_comm _ _).trans (div_eq_mul_inv ..).symm
  have h (f : SchwartzBruhat Jₛ) : MemLp (v f) 2 μweighted :=
    (sLocalDecay_untwist_mem f).ae_eq (.of_forall fun g ↦ (hv f g).symm)
  let L : SchwartzBruhat Jₛ →ₗ[ℂ] L²ₛ :=
    { toFun := fun f ↦ (h f).toLp _
      map_add' := fun f g ↦ by simp only [map_add]; exact (h f).toLp_add (h g)
      map_smul' := fun c f ↦ by simp only [map_smul, RingHom.id_apply]; exact (h f).toLp_const_smul c }
  have hL (f : SchwartzBruhat Jₛ) : ⇑(L f) =ᵐ[μweighted] v f := (h f).coeFn_toLp
  refine ⟨⟨L, ?_⟩, fun f ↦ (hL f).trans (.of_forall (hv f))⟩
  apply SchwartzBruhat.continuous_of_continuous_comp_ofStage
  intro a e
  let : FirstCountableTopology (SchwartzBruhatStage e) :=
    elementarySchwartz_withSeminorms.firstCountableTopology
  let : BarrelledSpace ℂ (SchwartzBruhatStage e) := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  exact thetaLp_stage μweighted (L.comp (SchwartzBruhat.ofStage a e))
    (fun u ↦ v (SchwartzBruhat.ofStage a e u)) (fun u ↦ hL _)
    (fun x ↦ continuous_const.mul ((continuous_schwartzBruhat_eval x).comp
      (SchwartzBruhat.continuous_ofStage a e)))

private theorem sLocalDecay_ambientL2 (I : Set ℝ) (hInt : OrdConnected I) (hhalf : (1 / 2 : ℝ) ∈ I) :
    ∃ L : Ẽ(I) →L[ℂ] L²ₛ, ∀ f, ⇑(L f) =ᵐ[μweighted] f.val := by
  let : SecondCountableTopology Jₛ := sLocalDecay_secondCountable
  let m : Jₛ →ₜ* ℝ≥0ˣ := ⟨mₛ, hmₛ⟩
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  let a : I := ⟨1/2, hhalf⟩
  let T : Ẽ(I) →L[ℂ] SchwartzBruhat Jₛ := ⟨modulatedExponentialDecayTwist m I a,
    (continuous_apply a).comp (modulatedExponentialDecay_twists_continuous m I (sLocalDecay_isModulation τ hτ)
      hInt ⟨_, hhalf⟩ τ hτ)⟩
  obtain ⟨L, hL⟩ := sLocalDecay_untwistL2 (F := F) (S := S)
  refine ⟨L.comp T, fun f ↦ (hL (T f)).trans (.of_forall fun g ↦ ?_)⟩
  have hp : 0 < normℝ(mₛ g) := NNReal.coe_pos.mpr (Units.zero_lt _)
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hp).ne')).mpr
  exact (modulatedExponentialDecayTwist_apply m I a f g).trans (by rw [Real.sqrt_eq_rpow, mul_comm]; rfl)

/-- A closed submodule containing every isotype of a compact abelian group is the
whole space. Apply uniqueness of Fourier coefficients to a separating functional.
The separation argument is the one used for the isotype sum in Chapter 6, §2. -/
private theorem sLocalDecay_closed_of_isotypes {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    [PolynormableSpace ℂ E] [CompleteSpace E]
    (ρ : G →* (E →L[ℂ] E)) (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2)
    (hb : ∀ p : Seminorm ℂ E, (∀ B : Set E, Bornology.IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (D : Submodule ℂ E) (hc : IsClosed (D : Set E)) (hD : ∀ ω, actionIsotype ρ ω ≤ D) :
    ∀ x, x ∈ D := by
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let μ : Measure G := Measure.haar
  let C (y : E) : C(G, E) := ⟨fun g ↦ ρ g y, hρ.comp (continuous_id.prodMk continuous_const)⟩
  have hC : Continuous C := ContinuousMap.continuous_of_continuous_uncurry _ (hρ.comp continuous_swap)
  have hseq (v : ℕ → E) (y : E) (hv : Tendsto v atTop (𝓝 y)) :
      TendstoUniformly (fun n g ↦ ρ g (v n)) (fun g ↦ ρ g y) atTop :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mp ((hC.tendsto y).comp hv)
  intro x
  by_contra hn
  obtain ⟨φ, hne, hz⟩ := exists_dual_eq_zero_on_submodule_of_notMem D hc hn
  let v : C(G, ℂ) := ⟨fun g ↦ φ (ρ g x), φ.continuous.comp (C x).continuous⟩
  have hcoeff (ω : PontryaginDual G) : ∫ g, star (ω g : ℂ) * v g ∂μ = 0 := by
    obtain ⟨P, hP, _⟩ := existsUnique_compactActionIsotypicAverage μ ρ hρ hb hseq ω
    have hmem : P x ∈ actionIsotype ρ ω :=
      (compactActionAverage_range μ ρ hρ ω P hP) ▸ LinearMap.mem_range_self P.toLinearMap x
    have h := LinearMap.congr_fun (hP x).2 φ
    change φ (P x) = ∫ g, φ (star (ω g : ℂ) • ρ g x) ∂μ.restrict univ at h
    simp only [Measure.restrict_univ, map_smul, smul_eq_mul] at h
    exact h.symm.trans (hz _ (hD ω hmem))
  have he : v = 0 := by
    apply eq_zero_of_weighted_integrals μ v 1
    · simpa using v.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
    · intro ω
      have hi (g : G) : ω⁻¹ g = (ω g)⁻¹ := rfl
      simpa [mul_comm, ← Circle.coe_inv_eq_conj, hi] using hcoeff ω⁻¹
  exact hne (by simpa [v] using DFunLike.congr_fun he 1)

local notation "thetaAction₁" => ((existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose.comp
  (mₛ).ker.subtype)
local notation "thetaAverage(" ω ")" => (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) ω).exists.choose

/-- Evaluating the ordinary Pettis average gives the unnormalized homogeneous theta
function. This is the evaluation argument of Chapter 10, §1. -/
private theorem sLocalDecay_thetaAverage_eval (ω : PontryaginDual J₁) (f r : ℬₛ)
    (hr : (Submodule.Quotient.mk r : Θₛ) = thetaAverage(ω) (Submodule.Quotient.mk f)) :
    (sLocalAdelicThetaOnClasses F S r : Jₛ → ℂ) = ⇑(φω(ω) f) := by
  let : MeasurableSpace J₁ := borel _
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  funext x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  let ev := thetaQuotientEval (sLocalAdelicTheta F S) a (sLocalAdelicTheta_continuous_eval a)
  have h := LinearMap.congr_fun
    (((existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) ω).exists.choose_spec
      (Submodule.Quotient.mk f)).2) ev
  change ev (thetaAverage(ω) (Submodule.Quotient.mk f)) =
    ∫ k, ev (star (ω k : ℂ) • thetaAction₁ k (Submodule.Quotient.mk f)) ∂μ.restrict univ at h
  have hρ (k : J₁) : ev (thetaAction₁ k (Submodule.Quotient.mk f)) =
      sLocalAdelicThetaOnClasses F S f (QuotientGroup.mk a * k.val⁻¹) :=
    sLocalThetaAction_eval _ (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2 f a k.val _
  rw [← hr] at h
  simp only [Measure.restrict_univ, map_smul, smul_eq_mul, hρ] at h
  rw [sLocalAdelicThetaOnClasses_mk, sLocalHomogeneousAdelicThetaLinearMap_apply]
  refine h.trans ((integral_congr_ae (.of_forall fun k ↦ ?_)).trans
    (integral_inv_eq_self (fun k : J₁ ↦ sLocalAdelicThetaOnClasses F S f (QuotientGroup.mk a * k.val) * (ω k : ℂ)) μ))
  rw [map_inv, Circle.coe_inv_eq_conj, mul_comm]
  rfl

private theorem sLocalDecay_isotype_mem_closure (I : Set ℝ) (hi : OrdConnected I) (hn : I.Nonempty)
    (L : Ẽ(I) →L[ℂ] L²ₛ) (hL : ∀ f, ⇑(L f) =ᵐ[μweighted] f.val)
    (ω : PontryaginDual J₁) (u : Eω(I, ω)) :
    L u.val ∈ (LinearMap.range (weightedTheta).toLinearMap).topologicalClosure := by
  let D := (LinearMap.range (weightedTheta).toLinearMap).topologicalClosure
  have hc : IsClosed {v : Eω(I, ω) | L v.val ∈ D} :=
    (Submodule.isClosed_topologicalClosure _).preimage (L.continuous.comp continuous_subtype_val)
  apply closure_minimal (t := {v : Eω(I, ω) | L v.val ∈ D}) _ hc (sLocalDecay_dense_theta I hi hn ω u)
  rintro v ⟨f, hf⟩
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.ker (sLocalAdelicTheta F S))
    (thetaAverage(ω) (Submodule.Quotient.mk f))
  have ha := sLocalDecay_thetaAverage_eval ω f r hr
  have hw := (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose_spec.2 r
  have ha' : (sLocalAdelicThetaOnClasses F S r : Jₛ → ℂ) =ᵐ[μweighted] v.val.val :=
    .of_forall fun g ↦ (congrFun ha g).trans (hf g).symm
  have he : weightedTheta (Submodule.Quotient.mk r) = L v.val :=
    Lp.ext (hw.trans (ha'.trans (hL v.val).symm))
  exact Submodule.le_topologicalClosure _ ⟨Submodule.Quotient.mk r, he⟩

private theorem sLocalDecay_closed_span (I : Set ℝ) (hi : OrdConnected I) (hn : I.Nonempty)
    (D : Submodule ℂ Ẽ(I)) (hcD : IsClosed (D : Set Ẽ(I)))
    (hD : ∀ ω : PontryaginDual J₁, sLocalDecayIsotype (F := F) (S := S) I ω ≤ D) (u : Ẽ(I)) :
    u ∈ D := by
  let : SecondCountableTopology Jₛ := sLocalDecay_secondCountable
  let m : Jₛ →ₜ* ℝ≥0ˣ := ⟨mₛ, hmₛ⟩
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  have hm := sLocalDecay_isModulation τ hτ
  let : CompleteSpace Ẽ(I) := modulatedExponentialDecay_complete m I hm hi hn τ hτ
  let : T2Space Ẽ(I) := T2Space.of_injective_continuous (f := fun f : Ẽ(I) ↦ f.val)
    (fun _ _ h ↦ Subtype.ext h) (continuous_pi (continuous_modulatedExponentialDecay_eval m I hn))
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : MeasurableSpace J₁ := borel _
  let : BorelSpace J₁ := ⟨rfl⟩
  have hAct := exists_modulatedExponentialDecay_translationAction m I hm hτ.surjective hi hn
  let A := hAct.choose
  have hA := hAct.choose_spec.1
  have hc := hAct.choose_spec.2
  apply sLocalDecay_closed_of_isotypes (A.comp (mₛ).ker.subtype)
    (hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
    (modulatedExponentialDecay_bornological m I hm hi hn τ hτ) D hcD _ u
  intro ω
  exact (sLocalDecayIsotype_eq_actionIsotype I ω A hA) ▸ hD ω

private theorem sLocalDecay_mem_closure (I : Set ℝ) (hi : OrdConnected I) (hn : I.Nonempty)
    (L : Ẽ(I) →L[ℂ] L²ₛ) (hL : ∀ f, ⇑(L f) =ᵐ[μweighted] f.val) (u : Ẽ(I)) :
    L u ∈ (LinearMap.range (weightedTheta).toLinearMap).topologicalClosure := by
  let D := (LinearMap.range (weightedTheta).toLinearMap).topologicalClosure.comap L.toLinearMap
  exact sLocalDecay_closed_span I hi hn D ((Submodule.isClosed_topologicalClosure _).preimage L.continuous)
    (fun ω f hf ↦ sLocalDecay_isotype_mem_closure I hi hn L hL ω ⟨f, hf⟩) u

/-- Paper: Proposition 5.4.2.1(2), p. 275.
If the exponent interval contains one half, the weighted Schwartz–Bruhat space
injects continuously into the theta completion by its almost-everywhere values. -/
theorem existsUnique_sLocalDecayToThetaL2 (I : Set ℝ) (_hOpen : IsOpen I)
    (_hInt : OrdConnected I) (_hsub : I ⊆ overlapInterval) (_hhalf : (1 / 2 : ℝ) ∈ I) :
    ∃! j : Ẽ(I) →L[ℂ] SLocalThetaL2 F S, Injective j ∧ ∀ f : Ẽ(I),
      (((j f).val : L²ₛ) : Jₛ → ℂ) =ᵐ[μweighted] f.val := by
  have h := sLocalDecay_ambientL2 (F := F) (S := S) I _hInt _hhalf
  let L := h.choose
  have hL := h.choose_spec
  let j : Ẽ(I) →L[ℂ] SLocalThetaL2 F S := L.codRestrict _
    (sLocalDecay_mem_closure I _hInt ⟨_, _hhalf⟩ L hL)
  refine ⟨j, ⟨?_, hL⟩, fun j' hj' ↦ ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    intro f hf
    have hz : L f = 0 := congrArg Subtype.val hf
    have ha : f.val =ᵐ[μweighted] 0 := (hL f).symm.trans (hz ▸ Lp.coeFn_zero ..)
    exact Subtype.ext (sLocalThetaWeightedL2_ae_zero f.val (sLocalDecay_continuous ⟨_, _hhalf⟩ f) ha)
  · exact ContinuousLinearMap.ext fun f ↦ Subtype.ext (Lp.ext ((hj'.2 f).trans (hL f).symm))

local notation "mass₁" => (((sLocalNormOneQuotientMeasure F S).real univ : ℝ) : ℂ)

private theorem sLocalDecay_mass_ne_zero : mass₁ ≠ 0 := by
  let : MeasurableSpace J₁ := borel _
  let : BorelSpace J₁ := ⟨rfl⟩
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  exact Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := sLocalNormOneQuotientMeasure F S)).ne'

/-- Averaging an ordinary theta function already in the required isotype multiplies it
by the total mass of the norm-one group. -/
private theorem sLocalDecay_pure_eval (ω : PontryaginDual J₁) (r : ℬₛ)
    (hr : (Submodule.Quotient.mk r : Θₛ) ∈ actionIsotype thetaAction₁ ω) (x : Jₛ) :
    φω(ω) r x = mass₁ * sLocalAdelicThetaOnClasses F S r x := by
  let : MeasurableSpace J₁ := borel _
  let μ := sLocalNormOneQuotientMeasure F S
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  let ev := thetaQuotientEval (sLocalAdelicTheta F S) a (sLocalAdelicTheta_continuous_eval a)
  have hval (k : J₁) :
      sLocalAdelicThetaOnClasses F S r (QuotientGroup.mk a * k.val) * (ω k : ℂ) =
        sLocalAdelicThetaOnClasses F S r (QuotientGroup.mk a) := by
    have hρ := sLocalThetaAction_eval _ (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2
      r a (k⁻¹ : J₁).val (sLocalAdelicTheta_continuous_eval a)
    change ev (thetaAction₁ k⁻¹ (Submodule.Quotient.mk r)) = _ at hρ
    rw [(mem_actionIsotype ..).mp hr k⁻¹, map_smul] at hρ
    simp only [Subgroup.coe_inv, inv_inv, map_inv, Circle.coe_inv, smul_eq_mul] at hρ
    rw [← hρ, sLocalAdelicThetaOnClasses_mk, mul_right_comm, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    rfl
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  exact (integral_congr_ae (.of_forall hval)).trans ((integral_const _).trans (Complex.real_smul ..))

private theorem sLocalDecay_pure_representative (ω : PontryaginDual J₁) (f : ℬₛ) :
    ∃ r : ℬₛ, (Submodule.Quotient.mk r : Θₛ) ∈ actionIsotype thetaAction₁ ω ∧
      (sLocalAdelicThetaOnClasses F S r : Jₛ → ℂ) = ⇑(φω(ω) f) := by
  have h := (sLocalThetaIsotypicAverage_equiv (F := F) (S := S) ω).2
  let e := h.choose
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.ker (sLocalAdelicTheta F S))
    (thetaAverage(ω) (Submodule.Quotient.mk f))
  have he : (Submodule.Quotient.mk r : Θₛ) = (e (Submodule.Quotient.mk f)).val :=
    hr.trans (h.choose_spec f).symm
  exact ⟨r, he ▸ (e (Submodule.Quotient.mk f)).property, sLocalDecay_thetaAverage_eval ω f r hr⟩

/-- On a pure ordinary representative, the defining identity for decay Fourier has the
same Haar mass on its two sides. This recovers the ordinary Fourier representative. -/
private theorem sLocalDecay_fourier_pure (χ : PontryaginDual Jₛ) (I : Set ℝ)
    (e : Eω(I, restrict₁(χ)) ≃L[ℂ] Eω(reflect(I), restrict₁(χ⁻¹)))
    (he : ∀ r : ℬₛ, ∃ (v : Eω(I, restrict₁(χ))) (w : Eω(reflect(I), restrict₁(χ⁻¹))),
      e v = w ∧ (∀ g, v.val.val g = φω(restrict₁(χ)) r g) ∧
        (∀ g, w.val.val g = φω(restrict₁(χ⁻¹)) (Fourierₛ r) g))
    (u : Eω(I, restrict₁(χ))) (r : ℬₛ)
    (hr : (Submodule.Quotient.mk r : Θₛ) ∈ actionIsotype thetaAction₁ restrict₁(χ))
    (hu : ∀ g, u.val.val g = sLocalAdelicThetaOnClasses F S r g) (g : Jₛ) :
    (e u).val.val g = sLocalAdelicThetaOnClasses F S (Fourierₛ r) g := by
  have hF := (sLocalThetaFourier_mem_isotype restrict₁(χ) (Submodule.Quotient.mk r)).mpr hr
  have hFr : (Submodule.Quotient.mk (Fourierₛ r) : Θₛ) ∈ actionIsotype thetaAction₁ restrict₁(χ⁻¹) :=
    (congrArg (fun y : Θₛ ↦ y ∈ actionIsotype thetaAction₁ restrict₁(χ⁻¹))
      ((existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 r)).mp hF
  have h := he r
  let v := h.choose
  let w := h.choose_spec.choose
  have hw := h.choose_spec.choose_spec
  have hv : v = mass₁ • u := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    exact (hw.2.1 t).trans ((sLocalDecay_pure_eval restrict₁(χ) r hr t).trans (congrArg (mass₁ * ·) (hu t).symm))
  have heq : mass₁ • e u = w := ((map_smul e mass₁ u).symm.trans (congrArg e hv.symm)).trans hw.1
  have hval : mass₁ * (e u).val.val g = w.val.val g :=
    congrArg (fun z : Eω(reflect(I), restrict₁(χ⁻¹)) ↦ z.val.val g) heq
  exact mul_left_cancel₀ (sLocalDecay_mass_ne_zero (F := F) (S := S))
    (hval.trans ((hw.2.2 g).trans (sLocalDecay_pure_eval restrict₁(χ⁻¹) (Fourierₛ r) hFr g)))

private theorem sLocalDecay_class_eq (I : Set ℝ) (j : Ẽ(I) →L[ℂ] SLocalThetaL2 F S)
    (hj : ∀ f, ⇑(j f).val =ᵐ[μweighted] f.val) (u : Ẽ(I)) (r : ℬₛ)
    (hu : ∀ g, u.val g = sLocalAdelicThetaOnClasses F S r g) :
    j u = completionMap (Submodule.Quotient.mk r) := by
  apply Subtype.ext
  have ha : u.val =ᵐ[μweighted] ⇑(sLocalAdelicThetaOnClasses F S r) := .of_forall hu
  exact Lp.ext ((hj u).trans (ha.trans
    ((existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose_spec.2 r).symm))


private theorem sLocalDecay_fourier_on_theta (χ : PontryaginDual Jₛ) (I : Set ℝ)
    (j : Ẽ(I) →L[ℂ] SLocalThetaL2 F S) (j' : Ẽ(reflect(I)) →L[ℂ] SLocalThetaL2 F S)
    (hj : ∀ f, ⇑(j f).val =ᵐ[μweighted] f.val) (hj' : ∀ f, ⇑(j' f).val =ᵐ[μweighted] f.val)
    (e : Eω(I, restrict₁(χ)) ≃L[ℂ] Eω(reflect(I), restrict₁(χ⁻¹)))
    (he : ∀ r : ℬₛ, ∃ (v : Eω(I, restrict₁(χ))) (w : Eω(reflect(I), restrict₁(χ⁻¹))),
      e v = w ∧ (∀ g, v.val.val g = φω(restrict₁(χ)) r g) ∧
        (∀ g, w.val.val g = φω(restrict₁(χ⁻¹)) (Fourierₛ r) g))
    (v : Eω(I, restrict₁(χ))) (f : ℬₛ) (hf : ∀ g, v.val.val g = φω(restrict₁(χ)) f g) :
    weightedFourier (j v.val) = j' (e v).val := by
  have hp := sLocalDecay_pure_representative restrict₁(χ) f
  let r := hp.choose
  have hr := hp.choose_spec
  have hv (g : Jₛ) : v.val.val g = sLocalAdelicThetaOnClasses F S r g :=
    (hf g).trans (congrFun hr.2 g).symm
  have hv' := sLocalDecay_fourier_pure χ I e he v r hr.1 hv
  exact (congrArg (weightedFourier) (sLocalDecay_class_eq I j hj v.val r hv)).trans
    (((existsUnique_sLocalThetaL2Fourier (F := F) (S := S)).exists.choose_spec r).trans
      (sLocalDecay_class_eq (reflect(I)) j' hj' (e v).val (Fourierₛ r) hv').symm)

/-- Paper: Proposition 5.4.2.1(2), p. 275.
The unitary Fourier extension agrees on the weighted isotype with the Fourier map
for the reflected interval, after embedding both functions by their L² classes. -/
theorem sLocalDecayFourier_eq_weightedFourier (χ : PontryaginDual Jₛ) (I : Set ℝ) (hOpen : IsOpen I)
    (hInt : OrdConnected I) (hsub : I ⊆ overlapInterval) (hhalf : (1 / 2 : ℝ) ∈ I) :
    let j := (existsUnique_sLocalDecayToThetaL2 (F := F) (S := S)
      I hOpen hInt hsub hhalf).exists.choose
    let e := (existsUnique_sLocalDecayFourier (F := F) (S := S) χ I hOpen hInt ⟨_, hhalf⟩ hsub).exists.choose
    ∀ f : Eω(I, restrict₁(χ)),
      ((((weightedFourier (j f.val)).val : L²ₛ) : Jₛ → ℂ)) =ᵐ[μweighted] (e f).val.val := by
  intro j e
  have hj := (existsUnique_sLocalDecayToThetaL2 (F := F) (S := S) I hOpen hInt hsub hhalf).exists.choose_spec.2
  have he := (existsUnique_sLocalDecayFourier (F := F) (S := S) χ I hOpen hInt ⟨_, hhalf⟩ hsub).exists.choose_spec
  have hJ := decayFourier_reflected_interval I hOpen hInt ⟨_, hhalf⟩ hsub
  have hhalf' : (1/2 : ℝ) ∈ reflect(I) := by
    change 1 - 1 / 2 ∈ I
    rwa [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
  have h := (existsUnique_sLocalDecayToThetaL2 (F := F) (S := S) (reflect(I)) hJ.1 hJ.2.1 hJ.2.2.2 hhalf').exists
  let j' := h.choose
  have hj' := h.choose_spec.2
  let A (u : Eω(I, restrict₁(χ))) := weightedFourier (j u.val)
  let B (u : Eω(I, restrict₁(χ))) := j' (e u).val
  have hc : IsClosed {u | A u = B u} := isClosed_eq
    ((weightedFourier).continuous.comp (j.continuous.comp continuous_subtype_val))
    (j'.continuous.comp (continuous_subtype_val.comp e.continuous))
  intro u
  have hu : A u = B u := by
    apply closure_minimal _ hc (sLocalDecay_dense_theta I hInt ⟨_, hhalf⟩ restrict₁(χ) u)
    rintro v ⟨f, hf⟩
    exact sLocalDecay_fourier_on_theta χ I j j' hj hj' e he v f hf
  change A u = B u at hu
  change ⇑(A u).val =ᵐ[μweighted] (e u).val.val
  rw [hu]
  exact hj' (e u).val

/-- Transport an exact pair through two linear homeomorphisms; separating observations ensure uniqueness. -/
private theorem existsUnique_sLocalCechDifference_conjugate
    {X Y Z W V : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (e : Y ≃L[ℂ] Z) (m : W ≃L[ℂ] V)
    (u : X →L[ℂ] Y) (v : X →L[ℂ] Z) (d : Z →L[ℂ] V)
    (hleft : ∀ q, e (u q) = v q) (hexact : Function.Exact v d)
    (R : Y → V → Prop) (hR : ∀ p, R p (d (e p)))
    (huniq : ∀ p a b, R p a → R p b → a = b) :
    ∃! A : Y →L[ℂ] W, (∀ p, R p (m (A p))) ∧ Function.Exact u A := by
  let A := m.symm.toContinuousLinearMap.comp (d.comp e.toContinuousLinearMap)
  have hA (p : Y) : m (A p) = d (e p) := m.apply_symm_apply _
  have hform (p : Y) : R p (m (A p)) := (hA p).symm ▸ hR p
  refine ⟨A, ⟨hform, ?_⟩, ?_⟩
  · intro p
    constructor
    · intro hp
      have hd : d (e p) = 0 := (hA p).symm.trans ((congrArg m hp).trans (map_zero m))
      obtain ⟨q,hq⟩ := (hexact (e p)).mp hd
      exact ⟨q, e.injective ((hleft q).trans hq)⟩
    · rintro ⟨q,rfl⟩
      apply m.injective
      exact (hA _).trans ((congrArg d (hleft q)).trans
        ((hexact.apply_apply_eq_zero q).trans (map_zero m).symm))
  · intro A' hA'
    apply ContinuousLinearMap.ext
    intro p
    exact m.injective (huniq p _ _ (hA'.1 p) (hform p))

/-- Paper: Theorem 5.4.2.2(3)–(6) and (5.4.2.6), pp. 276–277.
The upper difference is the unique continuous map whose shifted Mellin transform
is the lower difference. The upper row is exact at the pair of decay spaces.
Deviation: The correcting factor multiplies the reflected transform on the overlap. -/
theorem existsUnique_sLocalCechDifference (χ : PontryaginDual Jₛ)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ) (x : ℝ)
    (_hx : ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I)) :
    ∀ (M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺)
      (M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺)
      (M₀ : PositiveRealExponentialDecay overlapInterval ≃L[ℂ] B⁰),
      (∀ f s, s ∈ rightHalf → (M₁ f).val s =
        ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t ∂positiveRealHaar) →
      (∀ f s, s ∈ rightHalf → (M₂ f).val s =
        ∫ t, mellinIntegrand(τ, f.val.val, s - (x : ℂ) * Complex.I) t ∂positiveRealHaar) →
      (∀ f s, s ∈ overlap → (M₀ f).val s =
        mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I)) →
    ∃! D : upperMiddle(χ) →L[ℂ] PositiveRealExponentialDecay overlapInterval,
      (∀ p : upperMiddle(χ), EqOn (M₀ (D p)).val
        (fun s ↦ (M₁ p.1).val s - ρₛ(χ, s) * (M₂ p.2).val (1 - s)) overlap) ∧
      Function.Exact cechThetaPair(χ) D := by
  intro M₁ M₂ M₀ h₁ h₂ _h₀
  let lower := sLocalCechBergman_exact (F := F) (S := S) χ
  let U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺ := lower.choose
  let D : B⁺ × B⁺ →L[ℂ] B⁰ := lower.choose_spec.choose
  have hU := lower.choose_spec.choose_spec.1
  have hD := lower.choose_spec.choose_spec.2.1
  have hExact : Function.Exact U D := lower.choose_spec.choose_spec.2.2
  let e : upperMiddle(χ) ≃L[ℂ] B⁺ × B⁺ := M₁.prodCongr M₂
  have hleft (q : Θω(restrict₁(χ))) : e (cechThetaPair(χ) q) = U q := by
    refine Submodule.Quotient.induction_on _ q (fun f ↦ ?_)
    have h := sLocalCech_left_commutes χ τ hτ x _hx M₁ M₂ h₁ h₂ f
    exact Prod.ext (existsUnique_sLocalZetaPair_ext (h.1.trans (hU f).1.symm))
      (existsUnique_sLocalZetaPair_ext (h.2.trans (hU f).2.symm))
  exact existsUnique_sLocalCechDifference_conjugate e M₀ cechThetaPair(χ) U D hleft hExact
    (fun p f ↦ EqOn f.val
      (fun s ↦ (M₁ p.1).val s - ρₛ(χ,s) * (M₂ p.2).val (1-s)) overlap)
    (fun p ↦ hD (e p))
    (fun _ _ _ hf hg ↦ existsUnique_sLocalZetaPair_ext (hf.trans hg.symm))

/-- Paper: Remark 5.4.2.3 and (5.4.2.7), p. 277.
The pair of homogeneous theta functions of a test and its Fourier transform
embeds the homogeneous quotient as a closed subspace of the two weighted isotypes. -/
theorem sLocalCechThetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ) : IsClosedEmbedding cechThetaPair(χ) := by
  let τ := (sIdeleQuotientNorm_exists_section F S).choose
  have hτ := (sIdeleQuotientNorm_exists_section F S).choose_spec
  let x := (existsUnique_sLocalCechFrequency χ τ).exists.choose
  have hx := (existsUnique_sLocalCechFrequency χ τ).exists.choose_spec
  have hM₁ := existsUnique_sLocalDecayMellin τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi ⟨1, by norm_num⟩ restrict₁(χ) x
  have hM₂ := existsUnique_sLocalDecayMellin τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi ⟨1, by norm_num⟩ restrict₁(χ⁻¹) (-x)
  let M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺ := hM₁.exists.choose
  let M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺ := hM₂.exists.choose
  have h₁ := hM₁.exists.choose_spec
  have h₂ := hM₂.exists.choose_spec
  let e : upperMiddle(χ) ≃L[ℂ] B⁺ × B⁺ := M₁.prodCongr M₂
  let U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺ := e.toContinuousLinearMap.comp cechThetaPair(χ)
  have hU : IsClosedEmbedding U := sLocalCechBergman_isClosedEmbedding χ U (by
    intro f
    exact sLocalCech_left_commutes χ τ hτ x hx M₁ M₂
      (fun g s hs ↦ (h₁ g s hs).2)
      (fun g s hs ↦ by simpa only [M₂, neg_mul, Complex.ofReal_neg, sub_eq_add_neg] using
        (h₂ g s hs).2) f)
  have heq : e.symm ∘ U = ⇑cechThetaPair(χ) := by
    funext z
    exact e.symm_apply_apply _
  have h := e.symm.toHomeomorph.isClosedEmbedding.comp hU
  exact heq ▸ h

end Cech

end RiemannMasullo
