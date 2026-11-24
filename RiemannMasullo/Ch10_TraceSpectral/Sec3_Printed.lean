module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.DirichletZeros
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHecke
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # §10.3 assertions that are false as printed -/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "Wω(" F ", " l ", " r ", " s ", " hI ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) m𝔽(F) l r s hI hs).comp
    (ideleClassNorm F).ker.subtype) ω

local notation "μ𝔽(" F ")" => ideleClassTamagawaMeasure F
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "orderAt(" F ", " χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mellinAt(" F ", " φ ", " χ ", " z ")" =>
  ∫ g, (φ : BruhatCompactSupport C𝔽(F)).val g * ideleClassNormTwist (F := F) χ z g ∂μ𝔽(F)

local notation "printedMultiplicity(" F ", " χ ", " a ", " s ", " t ")" =>
  min ((meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ)
    ((a : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat) (Nat.floor ((s - 1) / 2 + 1))

/-- Paper: (10.3.1.18), p. 451. The products of jet norms and biorthogonal
vector norms within each zero block have a single bound across all blocks.
The family consists of all orders selected by the printed floor cutoff. -/
def Printed.spectralLineJet_uniformBiorthogonalBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)),
    IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < printedMultiplicity(F, χ j.1, a, s, j.2.1)}
      let Q := spectralSobolevQuotient F a h₀ hs₀(hs)
      let D := spectralSobolevDualEmbedding F a h₀ hs₀(hs)
      let w := (ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦
        ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹
      ∀ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ →
        (∀ j, let η := spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2
          ∃ h : MemLp η 2 w, D (Λ j) = h.toLp η) →
        ∃ C : ℝ, 0 < C ∧ ∀ i j : J,
          i.val.1 = j.val.1 → i.val.2.1 = j.val.2.1 → j.val.2.2 ≤ i.val.2.2 →
          ‖D (Λ j)‖ * ‖x i‖ ≤ C

/-- A grid of width 1/(k+1) forces two distinct ordinates in the same cell. -/
private theorem spectralLineJet_close_ordinates
    (hcount : ∀ k : ℕ, ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)
    (k : ℕ) : ∃ t u : ℝ, t ≠ u ∧ |t - u| < 1 / ((k : ℝ) + 1) ∧
      riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 ∧
      riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 := by
  obtain ⟨T, S, hS, hz⟩ := hcount k
  let f (t : ℝ) := ⌊((k : ℝ) + 1) * t⌋₊
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hmap : MapsTo f S (Finset.range ((k + 1) * (T + 1))) := by
    intro t ht
    apply Finset.mem_range.mpr
    have hle : f t ≤ (k + 1) * T := by
      apply Nat.floor_le_of_le
      exact_mod_cast mul_le_mul_of_nonneg_left (hz t ht).1.2 hk.le
    exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self T) (Nat.succ_pos k))
  obtain ⟨t, ht, u, hu, hneq, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simpa only [Finset.card_range] using hS) hmap
  refine ⟨t, u, hneq, ?_, (hz t ht).2, (hz u hu).2⟩
  have h₁ := Nat.floor_le (mul_nonneg hk.le (hz t ht).1.1.le)
  have h₂ := Nat.floor_le (mul_nonneg hk.le (hz u hu).1.1.le)
  have h₃ := Nat.lt_floor_add_one (((k : ℝ) + 1) * t)
  have h₄ := Nat.lt_floor_add_one (((k : ℝ) + 1) * u)
  change f t = f u at he
  change (f t : ℝ) ≤ _ at h₁
  change _ < (f t : ℝ) + 1 at h₃
  change (f u : ℝ) ≤ _ at h₂
  change _ < (f u : ℝ) + 1 at h₄
  rw [he] at h₁ h₃
  rw [abs_lt, ← neg_div, div_lt_iff₀ hk, lt_div_iff₀ hk]
  constructor <;> nlinarith

/-- The L² distance of two jets can be estimated by integrating their squared pointwise distance. -/
private theorem spectralLineJet_norm_sq {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ g, ‖f g‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), Real.sq_sqrt inner_self_nonneg]
    _ = RCLike.re (∫ g, inner ℂ (f g) (f g) ∂μ) := by rw [L2.inner_def]
    _ = ∫ g, RCLike.re (inner ℂ (f g) (f g)) ∂μ :=
      (integral_re (L2.integrable_inner f f)).symm
    _ = ∫ g, ‖f g‖ ^ 2 ∂μ := by simp_rw [inner_self_eq_norm_sq]

open Filter in
open scoped Topology in
/-- A vanishing ordinate gap gives vanishing L² distance for unit-modulus phases.
The fixed L² representative shows the constant dominator is integrable. -/
private theorem spectralLineJet_dist_tendsto {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (P : ℝ → G → ℂ) (hone : ∀ t g, ‖P t g‖ = 1)
    (hp : ∀ g, ContinuousAt (fun t ↦ P t g) 0) (hp0 : ∀ g, P 0 g = 1)
    (hsub : ∀ t u g, P t g - P u g = (P (t - u) g - 1) * P u g)
    (t u : ℕ → ℝ) (hlim : Tendsto (fun n ↦ t n - u n) atTop (𝓝 0))
    (x y : ℕ → Lp ℂ 2 μ)
    (hx : ∀ n, (x n : G → ℂ) =ᵐ[μ] P (t n))
    (hy : ∀ n, (y n : G → ℂ) =ᵐ[μ] P (u n)) :
    Tendsto (fun n ↦ dist (x n) (y n)) atTop (𝓝 0) := by
  let d (n : ℕ) := x n - y n
  have hd (n : ℕ) : ∀ᵐ g ∂μ, d n g = P (t n) g - P (u n) g := by
    filter_upwards [Lp.coeFn_sub (x n) (y n), hx n, hy n] with g h₁ h₂ h₃
    exact h₁.trans (congrArg₂ (· - ·) h₂ h₃)
  have h4 : Integrable (fun _ : G ↦ (4 : ℝ)) μ := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (x 0))).mp (Lp.memLp _)
    refine (hi.const_mul 4).congr ?_
    filter_upwards [hx 0] with g hg
    simp only [hg, hone, one_pow, mul_one]
  have he (g : G) : Tendsto (fun n ↦ ‖P (t n) g - P (u n) g‖ ^ 2) atTop (𝓝 0) := by
    have h := (((hp g).tendsto.comp hlim).sub_const 1).norm.pow 2
    simpa only [hsub, norm_mul, hone, mul_one, Function.comp_def, hp0, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0)] using h
  have hs := tendsto_integral_of_dominated_convergence
    (F := fun n g ↦ ‖d n g‖ ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (4 : ℝ))
    (fun n ↦ (Lp.aestronglyMeasurable (d n)).norm.pow _) h4
    (fun n ↦ (hd n).mono fun g hg ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hg]
      have h := norm_sub_le (P (t n) g) (P (u n) g)
      rw [hone, hone] at h
      exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by norm_num))
    (by
      filter_upwards [ae_all_iff.mpr hd] with g hg
      simpa only [hg] using he g)
  have hs' : Tendsto (fun n ↦ ‖d n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [spectralLineJet_norm_sq μ, integral_zero] using hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    d, dist_eq_norm] using (Real.continuous_sqrt.tendsto _).comp hs'

/-- Choose the trivial lift of the trivial rational norm-one character. -/
private theorem spectralLineJet_rational_basepoint :
    ∃ χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ), IsSpectralBasepointChoice χ ∧ χ 1 = 1 := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_spectralBasepointChoice ℚ
  refine ⟨Function.update ψ 1 1, ?_, Function.update_self ..⟩
  intro ω
  by_cases h : ω = 1
  · subst ω
    rw [Function.update_self]
    rfl
  · simpa only [Function.update_of_ne h] using hψ ω

/-- Each distinct critical-line zeta zero supplies a zeroth jet at Sobolev exponent two. -/
private theorem spectralLineJet_rational_zero_index
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : χ 1 = 1) (t : ℝ)
    (ht : riemannZeta (1/2 + (t : ℂ) * Complex.I) = 0) :
    ∃ j : SpectralLineJetIndex χ (1/2) 2, j.val = (1, t, 0) := by
  let z : ℂ := 1/2 + (t : ℂ) * Complex.I
  have hre : z.re = 1/2 := by simp [z, Complex.mul_re]
  have hne : z ≠ 1 := fun e ↦ by norm_num [e] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hz : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at ht
    rw [← ht]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  have htwo : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 :=
    (analyticOn_riemannZeta _ (by norm_num : (2 : ℂ) ≠ 1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [htwo]; simp)
  have hnat : 0 < (meromorphicOrderAt riemannZeta z).untop₀.toNat := by
    rw [← WithTop.coe_untop₀_of_ne_top hfin] at hz
    have hint : 0 < (meromorphicOrderAt riemannZeta z).untop₀ := WithTop.coe_lt_coe.mp hz
    omega
  refine ⟨⟨(1, t, 0), ?_⟩, rfl⟩
  apply (lt_spectralBoundaryMultiplicity 2 _ 0).mpr
  refine ⟨?_, by norm_num⟩
  rw [hχ]
  convert hnat using 1
  push_cast
  rw [meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C𝔽(ℚ)) hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]

/-- A uniform bound on the diagonal products of a biorthogonal system
with normalized coordinate forms forces the forms to be uniformly separated. -/
private theorem spectralLineJet_separation_of_diagonal_bound
    {ι E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
    (x : ι → E) (Λ : ι → StrongDual ℂ E) (hB : IsSpectralMarkushevichBasis x Λ)
    (D : StrongDual ℂ E → V) (hD : Isometry D)
    (hN : IsNormalizedSpectralFamily (fun i ↦ D (Λ i)))
    (C : ℝ) (hC : 0 < C) (hbound : ∀ i, ‖D (Λ i)‖ * ‖x i‖ ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε ≤ dist (D (Λ i)) (D (Λ j)) := by
  obtain ⟨c, hc, hlower⟩ := hN.2
  refine ⟨c / C, div_pos hc hC, fun i j hij ↦ ?_⟩
  have heval : 1 ≤ ‖Λ i - Λ j‖ * ‖x i‖ := by
    simpa only [sub_apply, hB.1 i, hB.2.1 i j hij, sub_zero, norm_one]
      using (Λ i - Λ j).le_opNorm (x i)
  have hx : c * ‖x i‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (hlower i) (norm_nonneg _)).trans (hbound i)
  rw [hD.dist_eq, dist_eq_norm, div_le_iff₀ hC]
  calc
    c = c * 1 := (mul_one _).symm
    _ ≤ c * (‖Λ i - Λ j‖ * ‖x i‖) := mul_le_mul_of_nonneg_left heval hc.le
    _ = ‖Λ i - Λ j‖ * (c * ‖x i‖) := by ring
    _ ≤ ‖Λ i - Λ j‖ * C := mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- At exponent two the printed and corrected jet cutoffs agree. The printed
bound would therefore separate all the rational jet vectors uniformly in L². -/
private theorem spectralLineJet_separation_of_printed
    (h : Printed.spectralLineJet_uniformBiorthogonalBound)
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : IsSpectralBasepointChoice χ) :
    let hs : (1 : ℝ) < 2 := by norm_num
    let jet (j : SpectralLineJetIndex χ (1 / 2) 2) :=
      (spectralLineJet_memLp χ hs j).toLp (spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2)
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε ≤ dist (jet i) (jet j) := by
  intro hs jet
  obtain ⟨x, Λ, hB, heq, hN⟩ := spectralLineMarkushevichBasis_normalized (a := 1/2) χ hχ hs
  let D := spectralSobolevDualEmbedding ℚ (1/2) (le_rfl (a := (0 : ℝ))) (zero_lt_one.trans hs).le
  have hD : Isometry D := (spectralSobolevDualEmbedding_isometry_range (F := ℚ) (1/2) le_rfl _).1
  have hP := h ℚ χ hχ (1/2) 2 hs
  dsimp only at hP
  have hcut : Nat.floor (((2 : ℝ) - 1) / 2 + 1) = Nat.ceil (((2 : ℝ) - 1) / 2) := by
    exact ((Nat.floor_eq_iff (by norm_num) (n := 1)).mpr (by norm_num)).trans
      ((Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr (by norm_num)).symm
  rw [hcut] at hP
  obtain ⟨C, hC, hbound⟩ := hP x Λ hB (fun j ↦ ⟨_, heq j⟩)
  obtain ⟨ε, hε, hsep⟩ := spectralLineJet_separation_of_diagonal_bound x Λ hB D hD hN C hC
    (fun i ↦ hbound i i rfl rfl le_rfl)
  refine ⟨ε, hε, fun i j hij ↦ ?_⟩
  simpa only [D, heq] using hsep i j hij

open Filter in
open scoped Topology in
/-- For the rational trivial character, the order-zero jet at frequency t is the
unitary phase |g|^(it). Its L² distance to the jet at u tends to zero when t-u does. -/
private theorem spectralLineJet_rational_phase_dist
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : χ 1 = 1)
    (t u : ℕ → ℝ) (hlim : Tendsto (fun n ↦ t n - u n) atTop (𝓝 0))
    (i j : ℕ → SpectralLineJetIndex χ (1 / 2) 2)
    (hi : ∀ n, (i n).val = (1, t n, 0)) (hj : ∀ n, (j n).val = (1, u n, 0)) :
    let hs : (1 : ℝ) < 2 := by norm_num
    let jet (v : SpectralLineJetIndex χ (1 / 2) 2) :=
      (spectralLineJet_memLp χ hs v).toLp (spectralZeroJet (χ v.val.1) 0 v.val.2.1 v.val.2.2)
    Tendsto (fun n ↦ dist (jet (i n)) (jet (j n))) atTop (𝓝 0) := by
  intro hs jet
  let R (g : C𝔽(ℚ)) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  let P (t : ℝ) (g : C𝔽(ℚ)) : ℂ := (R g : ℂ) ^ ((t : ℂ) * Complex.I)
  have hR (g) : 0 < R g := Units.zero_lt (ideleClassNorm ℚ g)
  have hP (t g) : ‖P t g‖ = 1 := by
    dsimp only [P]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hR g)]
    simp [Complex.mul_re]
  have hcont (g) : ContinuousAt (fun r ↦ P r g) 0 :=
    ((continuous_const_cpow' (Complex.ofReal_ne_zero.mpr (hR g).ne')).comp
      (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  have hsub (t u g) : P t g - P u g = (P (t - u) g - 1) * P u g := by
    have he : P t g = P (t - u) g * P u g := by
      dsimp [P]
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hR g).ne')]
      push_cast
      ring_nf
    rw [he, sub_mul, one_mul]
  let ν := (ideleClassTamagawaMeasure ℚ).withDensity fun g : C𝔽(ℚ) ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 2 (Real.log (R g)))⁻¹
  have hc (v : SpectralLineJetIndex χ (1 / 2) 2) (r : ℝ) (hv : v.val = (1, r, 0)) :
      (jet v : C𝔽(ℚ) → ℂ) =ᵐ[ν] P r := by
    refine (MemLp.coeFn_toLp (spectralLineJet_memLp χ hs v)).trans (ae_of_all _ fun g ↦ ?_)
    rw [hv, hχ, spectralZeroJet, pow_zero, mul_one, Complex.ofReal_zero, zero_add]
    change (1 : ℂ) * _ = _
    exact one_mul _
  exact spectralLineJet_dist_tendsto ν P hP hcont (fun g ↦ by simp [P]) hsub t u hlim
    (fun n ↦ jet (i n)) (fun n ↦ jet (j n)) (fun n ↦ hc _ _ (hi n)) (fun n ↦ hc _ _ (hj n))

/-- Classical input: the number of distinct critical-line zeta ordinates up to height T,
divided by T, is unbounded. This follows from a positive proportion of distinct critical-line
zeros (Selberg 1942) and the Riemann–von Mangoldt count. Not a statement of the paper and not
a gap in it: a known theorem of which this project has no formal proof. It is the arithmetic
input for the refutation of (10.3.1.18), p. 451, which is proved from it by name. -/
private theorem spectralLineJet_rational_critical_zero_count (k : ℕ) :
    ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 := by sorry

/-- Paper: (10.3.1.18), p. 451. For F = ℚ use the trivial base character,
a = 1/2 and s = 2. Take pairs of simple critical-line zeta zeros with
ordinates t and u tending arbitrarily close. The two cutoffs agree at s = 2.
The zeroth jets have the same positive norm and their difference tends to
zero by dominated convergence in the reciprocal Sobolev weight. Biorthogonality gives
1 ≤ ‖Λₜ − Λᵤ‖ ‖ψₜ‖, forcing the paired norm products to be unbounded. -/
theorem Printed.spectralLineJet_uniformBiorthogonalBound_false :
    ¬ Printed.spectralLineJet_uniformBiorthogonalBound := by
  classical
  intro h
  obtain ⟨χ, hχ, hχ₁⟩ := spectralLineJet_rational_basepoint
  obtain ⟨ε, hε, hsep⟩ := spectralLineJet_separation_of_printed h χ hχ
  choose t u hne hgap ht hu using spectralLineJet_close_ordinates spectralLineJet_rational_critical_zero_count
  choose i hi using fun n ↦ spectralLineJet_rational_zero_index χ hχ₁ (t n) (ht n)
  choose j hj using fun n ↦ spectralLineJet_rational_zero_index χ hχ₁ (u n) (hu n)
  have hlim : Filter.Tendsto (fun n ↦ t n - u n) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n ↦ (hgap n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hdist := spectralLineJet_rational_phase_dist χ hχ₁ t u hlim i j hi hj
  obtain ⟨n, hn⟩ := (hdist.eventually (eventually_lt_nhds hε)).exists
  apply (hsep (i n) (j n) ?_).not_gt hn
  intro heq
  have hr := congrArg (fun v : SpectralLineJetIndex χ (1 / 2) 2 ↦ v.val.2.1) heq
  exact hne n (by simpa only [hi, hj] using hr)

/-- Paper: Theorem 10.3.1.1(3), p. 449. A test of left-translation weight
ω⁻¹ is asserted to give an operator valued in the line quotient isotype ω. -/
def Printed.spectralLineConvolution_conjugateWeight_range : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) →
    ∀ (a s : ℝ) (hs : 1 < s) (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      range (spectralConvolution (F := F) a h₀ hs₀(hs) φ) ⊆
        range (fun v : Wω(F, 0, 0, s, h₀, hs₀(hs), ω) ↦
          (globalThetaSobolev F a h₀ hs₀(hs)).mkQ v.val)

section ConjugateWeightCounterexample

open Filter IsDedekindDomain
open scoped NumberField.AdeleRing SchwartzMap Topology

local notation "restrictNormOne(" F ")" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
local notation "logNorm(" F ")" => (logIdeleClassNorm F)
local notation "W(" F ", " s ")" => CompactIntervalSobolev (μ𝔽(F)) logNorm(F) 0 0 s
local notation "ρ(" F ", " hs ")" => hardySobolevTranslation (μ𝔽(F)) m𝔽(F) 0 0 _ h₀ hs
local notation "N(" F ", " a ", " hs ")" => globalThetaSobolev F a h₀ hs

private theorem spectralLine_wrongWeight_log_continuous (F : Type) [Field F] [NumberField F] :
    Continuous logNorm(F) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
    (fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')

/-- A compact Bruhat cutoff times the inverse of a norm twist has the opposite
translation weight to the twist's restriction, and its pairing is positive. -/
private theorem spectralLine_wrongWeight_test {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (t : ℝ) :
    let η := ideleClassNormTwist θ (shift(0, t))
    let γ := θ.comp (restrictNormOne(F))
    ∃ φ : BruhatCompactSupport C𝔽(F), Continuous φ.val ∧
      (∀ k : C₁(F), ∀ g, φ.val (k.val⁻¹ * g) = (γ k : ℂ) * φ.val g) ∧
      (∫ g, φ.val g * η g ∂μ𝔽(F)) ≠ 0 := by
  intro η γ
  let m := m𝔽(F)
  let hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m := by
    intro q
    exact ⟨QuotientGroup.mk (canonicalIdeleNormSection F q),
      canonicalIdeleNormSection_rightInverse F q⟩
  obtain ⟨b, hb⟩ := exists_smoothModulatedCutoff_radius_two m hm hms
  have hbc : HasCompactSupport b := by
    let e := Nonneg.unitsHomeomorphPos ℝ
    have hS : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc (2⁻¹ : ℝ) 2) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr]
      · exact isCompact_Icc
      · intro r hr
        exact (by norm_num : (0 : ℝ) < 2⁻¹).trans_le hr.1
    exact (hm.1.isCompact_preimage (e.isCompact_preimage.mpr hS)).of_isClosed_subset
      (isClosed_tsupport b) hb.1.support_subset
  have hbC : HasCompactSupport (fun g ↦ (b g : ℂ)) :=
    hbc.comp_left Complex.ofReal_zero
  let b₀ : BruhatCompactSupport C𝔽(F) :=
    ⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hb.2, hbC⟩
  let B := bruhatCompactSupportToModulatedExponentialDecay m univ hm hms b₀
  let ηInv := η.comp (ContinuousMonoidHom.inv _)
  obtain ⟨E, hE⟩ := modulatedExponentialDecay_mul_quasiCharacter m hm hms ηInv
  have hEB (g : C𝔽(F)) : (E B).val g = (η g)⁻¹ * (b g : ℂ) :=
    (hE B g).trans (by change η g⁻¹ * (b g : ℂ) = _; rw [map_inv])
  have hBs : HasCompactSupport (E B).val := by
    rw [funext hEB]
    exact hbC.mul_left (f := fun g ↦ (η g)⁻¹)
  let φ : BruhatCompactSupport C𝔽(F) :=
    ⟨_, modulatedExponentialDecay_mem_bruhatSmooth m univ univ_nonempty (E B), hBs⟩
  have hη (k : C₁(F)) : η k.val = (γ k : ℂ) := by
    change (θ k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ shift(0, t) = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp [γ]
    rfl
  have hηne (g : C𝔽(F)) : η g ≠ 0 := ((Group.isUnit g).map η).ne_zero
  have hprod (g : C𝔽(F)) : φ.val g * η g = (b g : ℂ) := by
    change (E B).val g * η g = _
    rw [hEB, mul_right_comm, inv_mul_cancel₀ (hηne g), one_mul]
  refine ⟨φ, ?_, ?_, ?_⟩
  · change Continuous (E B).val
    rw [funext hEB]
    exact (η.continuous.inv₀ hηne).mul (Complex.continuous_ofReal.comp hb.continuous)
  · intro k g
    change (E B).val (k.val⁻¹ * g) = (γ k : ℂ) * (E B).val g
    obtain ⟨p, _, hp, _⟩ := hb.1.profile
    rw [hEB, hEB, map_mul, map_inv, mul_inv_rev, inv_inv, hη]
    have hbkg : b (k.val⁻¹ * g) = b g := by
      rw [hp, hp]
      change p (((ideleClassNorm F (k.val⁻¹ * g)).val : ℝ≥0) : ℝ) = _
      rw [map_mul, map_inv, show ideleClassNorm F k.val = 1 from k.property, inv_one, one_mul]
      rfl
    rw [hbkg]
    ring
  · simp_rw [hprod]
    rw [integral_complex_ofReal]
    apply Complex.ofReal_ne_zero.mpr
    exact (hb.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hbc hb.1.nonneg
      (show b 1 ≠ 0 from (IsModulatedCutoff.apply_one (m := m) (ρ := b) hb.1 (by norm_num) (by norm_num)).trans_ne one_ne_zero)).ne'

/-- A continuous functional given by a character pairing is an eigenfunctional
for left translations, and integrating the orbit yields the test's multiplier. -/
private theorem spectralLine_wrongWeight_convolution {F : Type} [Field F] [NumberField F]
    {s : ℝ} (hs : 0 ≤ s) (η : QuasiCharacter C𝔽(F)) (Λ : StrongDual ℂ W(F, s))
    (hΛ : ∀ f : W(F, s), Λ f = ∫ g, f g * η g ∂μ𝔽(F)) :
    (∀ k : C𝔽(F), ∀ f : W(F, s), Λ (ρ(F, hs) k f) = η k * Λ f) ∧
    ∀ φ : BruhatCompactSupport C𝔽(F), ∀ f : W(F, s),
      Λ (hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs φ f) =
        (∫ g, φ.val g * η g ∂μ𝔽(F)) * Λ f := by
  have eig (k : C𝔽(F)) (f : W(F, s)) : Λ (ρ(F, hs) k f) = η k * Λ f := by
    have htr := hardySobolevTranslation_apply (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs k f
    rw [hΛ, hΛ, integral_congr_ae (htr.mono fun g hg ↦ congrArg (· * η g) hg)]
    calc
      _ = ∫ g, f g * η (k * g) ∂μ𝔽(F) := by
        rw [← integral_mul_left_eq_self (fun g ↦ f (k⁻¹ * g) * η g) k]
        simp only [inv_mul_cancel_left]
      _ = η k * ∫ g, f g * η g ∂μ𝔽(F) := by
        rw [← integral_const_mul]
        congr with g
        rw [map_mul]
        ring
  refine ⟨eig, fun φ f ↦ ?_⟩
  let τ := ρ(F, hs)
  have hτ := (exists_hardySobolevTranslation (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs).choose_spec.2
  have hp := bruhatRegularizedAction_apply (μ𝔽(F)) τ hτ φ f
  have he := congrArg (fun z : PettisWeakCompletion W(F, s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(F, s)) from z) Λ) hp.2
  change Λ (hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs φ f) =
    ∫ g, Λ (φ.val g • τ g f) ∂μ𝔽(F) at he
  rw [he, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change Λ (φ.val g • ρ(F, hs) g f) = φ.val g * η g * Λ f
  rw [map_smul, eig]
  simp only [smul_eq_mul, mul_assoc]

/-- A weighted Sobolev class representing a compactly supported Bruhat test. -/
private theorem spectralLine_wrongWeight_test_vector {F : Type} [Field F] [NumberField F]
    (φ : BruhatCompactSupport C𝔽(F)) (hc : Continuous φ.val) :
    ∃ f : W(F, 2), (f : C𝔽(F) → ℂ) =ᵐ[μ𝔽(F)] φ.val := by
  let d : C𝔽(F) → ℝ := fun g ↦ intervalSobolevDensity 0 0 2 (logNorm(F) g)
  let w := (μ𝔽(F)).withDensity (fun g ↦ ENNReal.ofReal (d g))
  have hd_eq (g : C𝔽(F)) : d g = 1 + logNorm(F) g ^ 2 := by
    norm_num [d, intervalSobolevDensity]
  have hd : Continuous d := by
    rw [funext hd_eq]
    exact continuous_const.add ((spectralLine_wrongWeight_log_continuous F).pow 2)
  have hp (g : C𝔽(F)) : 0 < d g := by rw [hd_eq]; positivity
  have hmem : MemLp φ.val 2 w := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    apply (integrable_withDensity_iff hd.measurable.ennreal_ofReal (ae_of_all _ fun _ ↦
      ENNReal.ofReal_lt_top)).2
    have hcont : Continuous (fun x ↦ ‖φ.val x‖ ^ 2 * d x) := (hc.norm.pow 2).mul hd
    have hpow : HasCompactSupport (fun x ↦ ‖φ.val x‖ ^ 2) :=
      φ.property.2.comp_left (g := fun z : ℂ ↦ ‖z‖ ^ 2) (by simp)
    have hcompact : HasCompactSupport (fun x ↦ ‖φ.val x‖ ^ 2 * d x) :=
      hpow.mul_right (f' := d)
    refine (hcont.integrable_of_hasCompactSupport hcompact).congr (ae_of_all _ fun x ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hp x).le]
  have h_ac : μ𝔽(F) ≪ w := withDensity_absolutelyContinuous' hd.measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp x))
  exact ⟨hmem.toLp φ.val, h_ac.ae_eq hmem.coeFn_toLp⟩

/-- At a zero of the continued completed L-function, every adelic zeta
transform vanishes on the same nontrivial norm-one component. -/
private theorem spectralLine_wrongWeight_zeta {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (k : C₁(F))
    (hk : (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹)
    (z : ℂ) (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL θ) z)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    globalIdelicZFunction f (ideleClassNormTwist θ z) = 0 := by
  have hk1 : θ k.val ≠ 1 := by
    intro he
    exact hk (by rw [he]; simp)
  have hθ : θ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := by
    intro he
    exact hk1 (DFunLike.congr_fun he k)
  have hrestrict (y : ℂ) : ideleClassNormTwist θ y k.val = (θ k.val : ℂ) := by
    change (θ k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ y = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp
  have hp₀ : ideleClassNormTwist θ z ≠ 1 := by
    intro he
    apply hk1
    apply Subtype.ext
    rw [← hrestrict, he]
    rfl
  have hp₁ : ideleClassNormTwist θ z ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽(F)) 1 := by
    intro he
    apply hk1
    apply Subtype.ext
    rw [← hrestrict, he]
    change (1 : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ (1 : ℂ) = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp
  let G := gaussianCompletedHeckeL θ
  let L := continuedCompletedHeckeL θ
  let c : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  obtain ⟨hL, hLe⟩ := continuedCompletedHeckeL_spec θ
  have hGdiff : Differentiable ℂ G :=
    globalIdelicZFunction_entire_of_nontrivial (adelicStandardGaussian θ) θ hθ
  have hLdiff : Differentiable ℂ L := completedHeckeL_continuation_entire θ L hL hLe hθ
  have hcL : Differentiable ℂ (fun w ↦ c * L w) :=
    (differentiable_const (c := c)).mul hLdiff
  have hGa : G = fun w ↦ c * L w := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hGdiff).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hcL) (z₀ := (2 : ℂ))
    have hnhd : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnhd] with w hw
    exact (gaussianCompletedHeckeL_eq_completedHeckeL θ w hw).trans
      (congrArg (c * ·) (hLe ⟨w, hw⟩).symm)
  have hLz : L z = 0 := by
    by_contra hne
    exact (ne_of_gt hz) ((hL (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hne)
  obtain ⟨D, -, -, hD⟩ := adelicEigendistribution_normalized θ
  rw [hD z hp₀ hp₁ f, show gaussianCompletedHeckeL θ z = c * L z from congrFun hGa z,
    hLz, mul_zero, zero_mul]

/-- The zeroth jet at a zero of the completed L-function kills the closed
weighted theta subspace, by Mellin factorization on the dense polar-free tests. -/
private theorem spectralLine_wrongWeight_kernel {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (k : C₁(F))
    (hk : (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹)
    (a t : ℝ) (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL θ) (shift(a, t)))
    {s : ℝ} (hs : 0 ≤ s) (Λ : StrongDual ℂ W(F, s))
    (hΛ : ∀ f : W(F, s), Λ f = ∫ g, f g * ideleClassNormTwist θ (shift(0, t)) g ∂μ𝔽(F)) :
    ∀ f : W(F, s), f ∈ N(F, a, hs) → Λ f = 0 := by
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s h₀ hs).exists.choose
  have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s h₀ hs).exists.choose_spec.2
  have hN : N(F, a, hs) ≤ Λ.ker := by
    apply Submodule.topologicalClosure_minimal _ _ Λ.isClosed_ker
    rintro v ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective
      ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype) x
    have hweight (g : C𝔽(F)) :
        modulationWeight m𝔽(F) a (adelicTheta f.val) g * ideleClassNormTwist θ (shift(0, t)) g =
          adelicTheta f.val g * ideleClassNormTwist θ (shift(a, t)) g := by
      let r : ℝ := ((ideleClassNorm F g).val : ℝ)
      have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt _)
      change ((r ^ a : ℝ) : ℂ) * adelicTheta f.val g * ((θ g : ℂ) * (r : ℂ) ^ shift(0, t)) =
        adelicTheta f.val g * ((θ g : ℂ) * (r : ℂ) ^ shift(a, t))
      simp only [Complex.ofReal_zero, zero_add]
      rw [Complex.ofReal_cpow hr.le,
        Complex.cpow_add (a : ℂ) ((t : ℂ) * Complex.I) (Complex.ofReal_ne_zero.mpr hr.ne')]
      ring
    have hI : (fun g ↦ (E (Submodule.Quotient.mk f)) g * ideleClassNormTwist θ (shift(0, t)) g)
        =ᵐ[μ𝔽(F)] fun g ↦ adelicTheta f.val g * ideleClassNormTwist θ (shift(a, t)) g := by
      exact (hE f).mono fun g hg ↦ (congrArg (· * ideleClassNormTwist θ (shift(0, t)) g) hg).trans
        (hweight g)
    change Λ (E (Submodule.Quotient.mk f)) = 0
    rw [hΛ, integral_congr_ae hI]
    obtain ⟨h₁, h₂⟩ := (mem_adelePolarSubspace f.val).mp f.property
    change globalThetaMellinIntegral f.val (ideleClassNormTwist θ (shift(a, t))) = 0
    rw [globalThetaMellinIntegral_eq_continuation_of_vanishing _ h₁ h₂]
    exact spectralLine_wrongWeight_zeta θ k hk (shift(a, t)) hz _
  exact fun f hf ↦ hN hf

private theorem spectralLine_wrongWeight_range_of_zero {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (k : C₁(F))
    (hk : (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹)
    (a t : ℝ) (hz : 0 < (orderAt(F, θ, shift(a, t))).untop₀.toNat) :
    ¬ Printed.spectralLineConvolution_conjugateWeight_range := by
  classical
  intro hprinted
  let γ := θ.comp (restrictNormOne(F))
  let ω : PontryaginDual C₁(F) := γ⁻¹
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice F
  let χ (δ : PontryaginDual C₁(F)) := if δ = γ then θ else χ₀ δ
  have hχ : IsSpectralBasepointChoice χ := by
    intro δ
    by_cases h : δ = γ
    · subst δ
      rw [show χ γ = θ by exact ite_eq_left rfl]
    · rw [show χ δ = χ₀ δ by simp [χ, h]]
      exact hχ₀ δ
  have hχγ : χ γ = θ := ite_eq_left rfl
  have hs : (1 : ℝ) < 2 := by norm_num
  let j : SpectralLineJetIndex χ a 2 := ⟨(γ, t, 0), by
    rw [lt_spectralBoundaryMultiplicity]
    refine ⟨?_, by norm_num⟩
    change 0 < (orderAt(F, χ γ, shift(a, t))).untop₀.toNat
    rw [hχγ]
    exact hz⟩
  let η := ideleClassNormTwist θ (shift(0, t))
  have hjet (g : C𝔽(F)) : spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2 g = η g := by
    change spectralZeroJet (χ γ) 0 t 0 g = η g
    rw [hχγ, spectralZeroJet, pow_zero, mul_one]
  obtain ⟨Λ, hΛ, -⟩ := spectralLineJet_functional χ hs j
  have hΛeval (f : W(F, 2)) : Λ f = ∫ g, f g * η g ∂μ𝔽(F) := by
    simpa only [hjet] using (hΛ f).2
  let N := N(F, a, hs₀(hs))
  have hpos : 0 < orderAt(F, θ, shift(a, t)) := by
    have h := j.order_pos
    change 0 < orderAt(F, χ γ, shift(a, t)) at h
    rwa [hχγ] at h
  have hzero := spectralLine_wrongWeight_kernel θ k hk a t hpos hs₀(hs) Λ hΛeval
  obtain ⟨heig, hmult⟩ := spectralLine_wrongWeight_convolution hs₀(hs) η Λ hΛeval
  obtain ⟨φ, hφcont, hφ, hφne⟩ := spectralLine_wrongWeight_test θ t
  obtain ⟨f, hf⟩ := spectralLine_wrongWeight_test_vector φ hφcont
  have h_f : Λ f ≠ 0 := by
    rw [hΛeval, integral_congr_ae (hf.mono fun g hg ↦ congrArg (· * η g) hg)]
    exact hφne
  let P := spectralConvolution (F := F) a h₀ hs₀(hs) φ
  have hwrong : ∀ k : C₁(F), ∀ g, φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g := by
    rw [show ω⁻¹ = γ from inv_inv γ]
    exact hφ
  obtain ⟨v, hv⟩ := hprinted F χ hχ a 2 hs ω φ hwrong
    (show P (N.mkQ f) ∈ range P from mem_range_self _)
  let T := hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 2 h₀ hs₀(hs) φ
  have hpv : N.mkQ v.val = N.mkQ (T f) :=
    hv.trans (spectralConvolution_mkQ (F := F) a h₀ hs₀(hs) φ f)
  have hΛv : Λ v.val = Λ (T f) := by
    have h := hzero _ ((Submodule.Quotient.eq N).mp hpv)
    rwa [map_sub, sub_eq_zero] at h
  have hPv : Λ (T f) ≠ 0 := by
    change Λ (hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 2 h₀ hs₀(hs) φ f) ≠ 0
    rw [hmult]
    exact mul_ne_zero hφne h_f
  apply hPv
  rw [← hΛv]
  have hinv : ρ(F, hs₀(hs)) k.val v.val = (ω k : ℂ) • v.val :=
    (mem_actionIsotype _ _ _).mp v.property k
  have he := heig k.val v.val
  rw [hinv, map_smul, smul_eq_mul] at he
  have hηk : η k.val = (θ k.val : ℂ) := by
    change (θ k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ shift(0, t) = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp
  have hωk : (ω k : ℂ) = (θ k.val : ℂ)⁻¹ := by
    change (((θ k.val)⁻¹ : Circle) : ℂ) = _
    simp
  rw [hηk, hωk] at he
  exact (mul_eq_mul_right_iff.mp he).resolve_left (Ne.symm hk)

-- The local evaluation uses the computation in Ch06_LocalGlobal/Sec2_Printed.lean.
open NumberFieldKB.Chebotarev.RatIdele in
/-- The idelic character of a Dirichlet character modulo 5, at the idele with `2` at the place
over 5 and `1` elsewhere, is the inverse of the character value at `2`. -/
private theorem rational_quartic_local_two
    (χ : DirichletCharacter ℂ 5) (v : Pl) (hv : pr v = 5) (u : (v.adicCompletion ℚ)ˣ)
    (hu : (u : v.adicCompletion ℚ) = ((2 : ℕ) : v.adicCompletion ℚ)) :
    ((ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂˣ) : ℂ) =
      (χ (2 : ZMod 5))⁻¹ := by
  have hval : Valued.v (u : v.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ)) := by
    rw [neg_zero, WithZero.exp_zero, hu, ← Rat.cast_natCast, valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem, natCast_mem_asIdeal_iff, hv]
    norm_num
  have hq : ratPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
    rw [ratPart_ofAdicCompletion v u 0 hval, zpow_zero]
  have hU : unitPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) =
      IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u := by
    rw [unitPart_apply, hq, map_one, inv_one, mul_one]
  have hr : resMod 5 (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = (2 : ZMod 5) := by
    rw [resMod_apply, resModFun, hU]
    refine (ZMod.equivPi 5 (NeZero.ne 5)).symm_apply_eq.mpr (funext fun q ↦ ?_)
    have hq5 : (q : ℕ) = 5 :=
      (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors q.2) Nat.prime_five).mp
        (Nat.dvd_of_mem_primeFactors q.2)
    have hqN : (q : ℕ) ^ (5 : ℕ).factorization q ∣ 5 := Nat.ordProj_dvd 5 q
    have hcomp : ZMod.equivPi 5 (NeZero.ne 5) (2 : ZMod 5) q =
        ZMod.castHom hqN (ZMod ((q : ℕ) ^ (5 : ℕ).factorization q)) (2 : ZMod 5) :=
      RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi 5 (NeZero.ne 5)).toRingHom) (ZMod.castHom hqN _)) (2 : ZMod 5)
    rw [hcomp, map_ofNat]
    have hqv : placeP 5 q = v := pr_injective (by rw [placeP, pr_placeOf, hq5, hv])
    subst hqv
    rw [compV_ofAdicCompletion_self]
    erw [hu, redP_natCast]
    rfl
  rw [coe_ideleChar, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, hr]

/-- The rational idele class character induced by a quartic Dirichlet character modulo five
is nonreal on the norm-one class of the local unit two. -/
private theorem exists_ratNormOne_nonselfinverse_zero :
    ∃ (θ : PontryaginDual C𝔽(ℚ)) (k : (ideleClassNorm ℚ).ker),
      (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹ ∧
      ∃ z : ℂ, 0 < (meromorphicOrderAt (continuedCompletedHeckeL θ) z).untop₀.toNat := by
  classical
  let v5 : HeightOneSpectrum (𝓞 ℚ) := NumberFieldKB.Chebotarev.RatIdele.placeOf 5 Nat.prime_five
  have hv5 : NumberFieldKB.Chebotarev.RatIdele.pr v5 = 5 := NumberFieldKB.Chebotarev.RatIdele.pr_placeOf 5 Nat.prime_five
  -- Detecting 4 forces the image of 2 to have order four.
  obtain ⟨χ, hχ4⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod 5) ℂ
    (a := (4 : ZMod 5)) (by decide)
  obtain ⟨hprim, z, hzr, _, hz⟩ := dirichletFive_positiveOrder χ hχ4
  obtain ⟨ψ, _, hval, hf⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hprim
  have hψz : 0 < (meromorphicOrderAt (continuedCompletedHeckeL ψ) z).untop₀.toNat := by
    rw [← meromorphicOrderAt_finiteHeckeL_continuation ψ (meromorphic_dirichletLFunction χ)
      (fun s ↦ (_root_.DirichletCharacter.LFunction_eq_LSeries χ s.property).trans (hf s s.property).symm) hzr]
    exact hz
  have hval2 : Valued.v ((2 : ℕ) : v5.adicCompletion ℚ) = 1 := by
    rw [← Rat.cast_natCast, NumberFieldKB.Chebotarev.RatIdele.valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem,
      NumberFieldKB.Chebotarev.RatIdele.natCast_mem_asIdeal_iff, hv5]
    norm_num
  have h2ne : ((2 : ℕ) : v5.adicCompletion ℚ) ≠ 0 := fun e ↦ by
    rw [e, map_zero] at hval2
    exact zero_ne_one hval2
  let u2 : (v5.adicCompletion ℚ)ˣ := Units.mk0 _ h2ne
  have hu2v : Valued.v (u2 : v5.adicCompletion ℚ) = 1 := hval2
  let a := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u2
  have hmem : a ∈ (ideleClassNorm ℚ).ker := by
    rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
    ext
    simpa using (Valued.toNormedField.norm_eq_one_iff.mpr hu2v)
  refine ⟨ψ, ⟨a, hmem⟩, ?_, z, hψz⟩
  have hev : (ψ a : ℂ) = (χ (2 : ZMod 5))⁻¹ :=
    (hval (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u2)).trans
      (rational_quartic_local_two χ v5 hv5 u2 rfl)
  change (ψ a : ℂ) ≠ (ψ a : ℂ)⁻¹
  rw [hev, inv_inv]
  intro h
  have hn : χ (2 : ZMod 5) ≠ 0 := by
    exact (ZMod.isUnit_iff_coprime 2 5 |>.mpr (by decide)).map χ |>.ne_zero
  apply hχ4
  rw [show (4 : ZMod 5) = 2 * 2 by decide, map_mul]
  exact (congrArg (· * χ (2 : ZMod 5)) h.symm).trans (inv_mul_cancel₀ hn)

/-- Paper: Theorem 10.3.1.1(3), p. 449. For F = ℚ let the base character
θ be induced by a quartic Dirichlet character modulo 5.
Take s = 2, a+it a nontrivial zero of its completed L-function and
ω = (θ|C¹)⁻¹. Multiply the conjugate of θ(g)|g|^(it) by a nonzero
nonnegative smooth bump in log |g|. This test has left-translation weight
ω⁻¹. The zeroth jet function has weight ω, and the associated bilinear
functional detects the ω⁻¹-isotype. Its transpose eigenvalue is the positive
integral of the bump, and it annihilates the ω-isotype. See ERRATA.md F177. -/
theorem Printed.spectralLineConvolution_conjugateWeight_range_false :
    ¬ Printed.spectralLineConvolution_conjugateWeight_range := by
  obtain ⟨θ, k, hk, z, hz⟩ := exists_ratNormOne_nonselfinverse_zero
  apply spectralLine_wrongWeight_range_of_zero θ k hk z.re z.im
  rw [Complex.re_add_im]
  exact hz

end ConjugateWeightCounterexample

/-- Paper: Theorem 10.3.2.1(3), p. 454. A test of left-translation weight
ω⁻¹ is asserted to give an operator valued in the strip quotient isotype ω. -/
def Printed.spectralStripConvolution_conjugateWeight_range : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s)
      (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      range (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) ⊆
        range (fun v : Wω(F, -α, α, s, hStrip(hα), hs₀(hs), ω) ↦
          (globalThetaSobolev F a hStrip(hα) hs₀(hs)).mkQ v.val)

/-- Paper: Theorem 10.3.2.1(3), p. 454. Take F = ℚ, α = 1, s = 2 and
the primitive quartic character modulo 5 as in the line counterexample.
Choose a+it to be a nontrivial zero of its completed L-function, so the offset
b = 0 is interior. The same bump times the conjugate of θ(g)|g|^(it) acts
nontrivially on that zeroth jet, which annihilates the printed output isotype. -/
theorem Printed.spectralStripConvolution_conjugateWeight_range_false :
    ¬ Printed.spectralStripConvolution_conjugateWeight_range := by
  intro h
  apply Printed.spectralLineConvolution_conjugateWeight_range_false
  intro F _ _ χ hχ a s hs ω φ hφ
  let P (l : ℝ) (hl : l ≤ 0) : Prop :=
    range (spectralConvolution (F := F) a hl hs₀(hs) φ) ⊆
      range (fun v : Wω(F, l, 0, s, hl, hs₀(hs), ω) ↦
        (globalThetaSobolev F a hl hs₀(hs)).mkQ v.val)
  have transport (l : ℝ) (hl : l ≤ 0) (he : l = 0) (hp : P l hl) : P 0 le_rfl := by
    subst l
    exact hp
  exact transport _ _ (neg_zero : -(0 : ℝ) = 0) (h F χ hχ a 0 s le_rfl hs ω φ hφ)

/-- Paper: Theorem 10.3.1.1(3), p. 449. A test of conjugate weight is
claimed to act through the indicated isotype by a strongly nuclear operator.
The full trace is the sum in (10.3.1.5) with the floor in (10.3.1.4). -/
def Printed.spectralLineConvolution_conjugateWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a s : ℝ) (hs : 1 < s) (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      let H := spectralSobolevQuotient F a h₀ hs₀(hs)
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      let Z := {t : ℝ // 0 < orderAt(F, χ ω, shift(a, t))}
      let term (t : Z) := ((printedMultiplicity(F, χ ω, a, s, t.val) : ℕ) : ℂ) *
        mellinAt(F, φ, χ ω, shift(0, t.val))
      range A ⊆ range (fun v : Wω(F, 0, 0, s, h₀, hs₀(hs), ω) ↦
        (globalThetaSobolev F a h₀ hs₀(hs)).mkQ v.val) ∧
      IsStronglyNuclearBanachOperator (spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ) ∧
      ∃ T : nuclearEndomorphisms H, T.val = A ∧ HasSum term (hilbertTrace T)

/-- Paper: Theorem 10.3.1.1(3), p. 449. The quartic character modulo five and
the bump in the range counterexample already contradict the first conjunct. -/
theorem Printed.spectralLineConvolution_conjugateWeight_false :
    ¬ Printed.spectralLineConvolution_conjugateWeight := by
  intro h
  apply Printed.spectralLineConvolution_conjugateWeight_range_false
  intro F _ _ χ hχ a s hs ω φ hφ
  exact (h F χ hχ a s hs ω φ hφ).1

/-- Paper: Theorem 10.3.2.1(3), p. 454. A test of conjugate weight is
claimed to act through the indicated isotype by a strongly nuclear operator.
Its full trace is (10.3.2.5), with the printed boundary and interior counts. -/
def Printed.spectralStripConvolution_conjugateWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s)
      (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      let H := spectralSobolevQuotient F a hStrip(hα) hs₀(hs)
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let Z := {z : ℝ × ℝ // z.1 ∈ Icc (-α) α ∧ 0 < orderAt(F, χ ω, shift(a + z.1, z.2))}
      let term (z : Z) :=
        let b := z.val.1
        let t := z.val.2
        let n := (orderAt(F, χ ω, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min n (Nat.floor ((s - 1) / 2 + 1)) else n
        (count : ℂ) * mellinAt(F, φ, χ ω, shift(b, t))
      range A ⊆ range (fun v : Wω(F, -α, α, s, hStrip(hα), hs₀(hs), ω) ↦
        (globalThetaSobolev F a hStrip(hα) hs₀(hs)).mkQ v.val) ∧
      IsStronglyNuclearBanachOperator (spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ) ∧
      ∃ T : nuclearEndomorphisms H, T.val = A ∧ HasSum term (hilbertTrace T)

/-- Paper: Theorem 10.3.2.1(3), p. 454. At half-width one, the quartic
character modulo five gives the same contradiction at an interior zero. -/
theorem Printed.spectralStripConvolution_conjugateWeight_false :
    ¬ Printed.spectralStripConvolution_conjugateWeight := by
  intro h
  apply Printed.spectralStripConvolution_conjugateWeight_range_false
  intro F _ _ χ hχ a α s hα hs ω φ hφ
  exact (h F χ hχ a α s hα hs ω φ hφ).1

end RiemannMasullo
