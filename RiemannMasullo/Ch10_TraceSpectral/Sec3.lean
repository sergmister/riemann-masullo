module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
public import RiemannMasullo.Ch09_HardySobolev.Sec3
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import RiemannMasullo.Ch10_TraceSpectral.Sec1

import all RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Spectral nuclearity

Masullo, §10.3, pp. 447–455. Convolution acts on the spectral Sobolev quotients
from §10.2. The trace formulas use the strict boundary multiplicity from that
section and the integrated left-translation action from §9.3.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section StrongNuclearity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Paper: §10.3, p. 447. A strongly nuclear operator is an operator-norm sum
of rank-one terms with unit-ball vectors and functionals and rapidly decreasing
coefficients.
Deviation: The name is kept apart from `IsStronglyNuclearOperator` of §7.4
(Theorem 7.4.1.1(2), pp. 366–367), which is stated for endomorphisms of a locally
convex space through a nuclear presentation. This one is for maps between normed spaces. -/
def IsStronglyNuclearBanachOperator (A : E →L[ℂ] G) : Prop :=
  ∃ (c : ℕ → ℂ) (Λ : ℕ → StrongDual ℂ E) (y : ℕ → G),
    (∀ n, ‖Λ n‖ ≤ 1 ∧ ‖y n‖ ≤ 1) ∧
    (∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * c n) atTop (𝓝 0)) ∧
    HasSum (fun n ↦ c n • (Λ n).smulRight (y n)) A

/-- Paper: §10.3, p. 447. A rank-one operator has a strongly nuclear expansion
using a single coefficient after normalizing the factors.
Deviation: Sanity check for the strongly nuclear condition. -/
theorem isStronglyNuclearBanachOperator_smulRight (Λ : StrongDual ℂ E) (y : G) :
    IsStronglyNuclearBanachOperator (Λ.smulRight y) := by
  classical
  refine ⟨fun n ↦ if n = 0 then ((‖Λ‖ * ‖y‖ : ℝ) : ℂ) else 0,
    fun n ↦ if n = 0 then ((‖Λ‖⁻¹ : ℝ) : ℂ) • Λ else 0,
    fun n ↦ if n = 0 then ((‖y‖⁻¹ : ℝ) : ℂ) • y else 0, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      constructor
      · by_cases h : ‖Λ‖ = 0 <;> simp [h]
      · by_cases h : ‖y‖ = 0 <;> simp [h]
    · simp [hn]
  · intro k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [hn]
  · convert hasSum_single (f := fun n : ℕ ↦ (if n = 0 then ((‖Λ‖ * ‖y‖ : ℝ) : ℂ) else 0) •
        (if n = 0 then ((‖Λ‖⁻¹ : ℝ) : ℂ) • Λ else 0).smulRight
          (if n = 0 then ((‖y‖⁻¹ : ℝ) : ℂ) • y else 0)) 0 (by intro n hn; simp [hn]) using 1
    simp only [ite_true]
    by_cases hΛ : ‖Λ‖ = 0
    · have : Λ = 0 := norm_eq_zero.mp hΛ
      subst this; ext; simp
    by_cases hy : ‖y‖ = 0
    · have : y = 0 := norm_eq_zero.mp hy
      subst this; ext; simp
    ext x
    simp [ContinuousLinearMap.smulRight_apply, smul_smul]
    field_simp [hΛ, hy]

/-- Paper: §10.3, p. 448. Strong nuclearity implies nuclearity. -/
theorem IsStronglyNuclearBanachOperator.isNuclearOperator [CompleteSpace E]
    {A : E →L[ℂ] G} (_hA : IsStronglyNuclearBanachOperator A) : IsNuclearOperator A := by
  obtain ⟨c, Λ, y, hb, hc, hs⟩ := _hA
  rw [isNuclearOperator_iff_isBanachNuclear]
  let d : ℕ → ℂ := fun n ↦ (n : ℂ) + 1
  have hd (n : ℕ) : ‖d n‖ = (n : ℝ) + 1 := by
    simp only [d]; exact_mod_cast Complex.norm_natCast (n + 1)
  have hd0 (n : ℕ) : d n ≠ 0 := by
    intro h; have := hd n; rw [h, norm_zero] at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ⟨fun n ↦ c n * d n ^ 2, fun n ↦ (d n)⁻¹ • Λ n, fun n ↦ (d n)⁻¹ • y n, ?_, ?_, ?_, ?_⟩
  · have h4 := (tendsto_zero_iff_norm_tendsto_zero.mp (hc 4)).eventually (gt_mem_nhds one_pos)
    refine Summable.of_norm_bounded_eventually_nat
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 4) ?_
    filter_upwards [h4, eventually_ge_atTop 1] with n hn h1
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    rw [norm_mul, norm_pow, Complex.norm_natCast] at hn
    rw [norm_norm, norm_mul, norm_pow, hd]
    have hcn := norm_nonneg (c n)
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    have : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
    calc ‖c n‖ * ((n : ℝ) + 1) ^ 2 * (n : ℝ) ^ 2
        ≤ ‖c n‖ * (4 * (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by gcongr
      _ = 4 * ((n : ℝ) ^ 4 * ‖c n‖) := by ring
      _ ≤ 4 := by nlinarith
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hinv
    rw [norm_smul, norm_inv, hd]
    exact mul_le_of_le_one_right (by positivity) (hb n).1
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hinv
    rw [norm_smul, norm_inv, hd]
    exact mul_le_of_le_one_right (by positivity) (hb n).2
  · intro x
    refine (hs.mapL (ContinuousLinearMap.apply ℂ G x)).congr_fun fun n ↦ ?_
    simp only [ContinuousLinearMap.apply_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul, smul_eq_mul]
    congr 1
    field_simp [hd0 n]

end StrongNuclearity

private theorem liftQL_mkQ_aux {M N : Type*} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N] (S : Submodule ℂ M) (f : M →L[ℂ] N)
    (h : S ≤ f.ker) (v : M) : S.liftQL f h (S.mkQ v) = f v := by
  rw [Submodule.liftQL_apply]; rfl


variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" l ", " r ", " s ")" =>
  CompactIntervalSobolev μ𝔽 (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) l r s
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "Qω(" a ", " hI ", " hs ", " ω ")" =>
  spectralSobolevIsotypeQuotient F a hI hs ω
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "testAction(" l ", " r ", " s ", " hI ", " hs ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 l r s hI hs
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽
    (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) χ z)

-- Select the norm topology directly when using the locally convex nuclear ideal.
local instance instSpectralQuotientPolynormableSec3 (a : ℝ) {l r s : ℝ}
    (hI : l ≤ r) (hs : 0 ≤ s) : PolynormableSpace ℂ Q(a, hI, hs) :=
  (norm_withSeminorms ℂ Q(a, hI, hs)).toPolynormableSpace

section Convolution

variable (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)

/-- A Pettis integral of translates of a vector in a closed invariant subspace of a
Hilbert space stays in that subspace, since every vector orthogonal to it kills the integrand. -/
private theorem hardySobolevTestAction_preserves_globalTheta_aux {X V : Type*}
    [Group X] [MeasurableSpace X] (μ : Measure X) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (K : Submodule ℂ V) (hK : IsClosed (K : Set V))
    (τ : X →* (V →L[ℂ] V)) (hτ : ∀ g, ∀ v ∈ K, τ g v ∈ K) {ψ : X → ℂ} {u b : V}
    (hu : u ∈ K) (hb : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) b) : b ∈ K := by
  have : CompleteSpace K := hK.completeSpace_coe
  rw [← K.orthogonal_orthogonal]
  intro w hw
  have hδ := congrArg
    (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z)
      (innerSL ℂ w)) hb.2
  change innerSL ℂ w b = ∫ g, innerSL ℂ w (ψ g • τ g u) ∂μ at hδ
  rw [innerSL_apply_apply] at hδ
  rw [hδ]
  refine integral_eq_zero_of_ae (.of_forall fun g ↦ ?_)
  change innerSL ℂ w (ψ g • τ g u) = 0
  rw [innerSL_apply_apply]
  exact (K.mem_orthogonal' w).mp hw _ (K.smul_mem _ (hτ g u hu))

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. Convolution with a
test preserves the closed weighted theta subspace, so it descends to the quotient. -/
theorem hardySobolevTestAction_preserves_globalTheta (φ : BruhatCompactSupport C𝔽) :
    Θ(a, hI, hs) ≤ ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ)).ker := by
  intro v hv
  obtain ⟨ρ, hρ, -, -⟩ := exists_globalThetaSobolevAction (F := F) a hI hs
  have hinv : ∀ g, ∀ w ∈ Θ(a, hI, hs), hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs g w ∈
      Θ(a, hI, hs) := fun g w hw ↦ by
    rw [← hρ g ⟨w, hw⟩]
    exact (ρ g ⟨w, hw⟩).property
  have hmem := hardySobolevTestAction_preserves_globalTheta_aux μ𝔽 (Θ(a, hI, hs))
    (Submodule.isClosed_topologicalClosure _) (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
    hinv hv (bruhatRegularizedAction_apply μ𝔽 (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
      (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2 φ v)
  exact (Submodule.Quotient.mk_eq_zero (Θ(a, hI, hs))).mpr hmem

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. The spectral convolution
operator is the descended Hardy–Sobolev test action. -/
def spectralConvolution (φ : BruhatCompactSupport C𝔽) : Q(a, hI, hs) →L[ℂ] Q(a, hI, hs) :=
  (Θ(a, hI, hs)).liftQL ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ))
    (hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs φ)

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. On a representative,
spectral convolution takes the quotient class of its ambient convolution. -/
theorem spectralConvolution_mkQ (φ : BruhatCompactSupport C𝔽) (v : W(l, r, s)) :
    spectralConvolution (F := F) a hI hs φ ((Θ(a, hI, hs)).mkQ v) =
      (Θ(a, hI, hs)).mkQ (testAction(l, r, s, hI, hs) φ v) := by
  unfold spectralConvolution
  have h := (liftQL_mkQ_aux (Θ(a, hI, hs))
    ((Θ(a, hI, hs)).mkQL.comp (testAction(l, r, s, hI, hs) φ))
    (hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs φ) v)
  with_reducible_and_instances exact h.trans (Submodule.mkQL_apply _ _)

open scoped UniformConvergenceCLM in
/-- Descending a linear family of operators through a fixed quotient is linear. -/
private theorem spectralConvolution_isLinear_aux {P M : Type*} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul ℂ M] {𝔖 : Set (Set M)} (S : Submodule ℂ M)
    (T : P →ₗ[ℂ] (M →Lᵤ[ℂ, 𝔖] M)) (h : ∀ p, S ≤ (S.mkQL.comp (T p)).ker) :
    IsLinearMap ℂ (fun p ↦ S.liftQL (S.mkQL.comp (T p)) (h p)) := by
  constructor
  · intro p q
    refine ContinuousLinearMap.coe_injective (Submodule.linearMap_qext S (LinearMap.ext fun x ↦ ?_))
    change S.mkQ (T (p + q) x) = S.mkQ (T p x) + S.mkQ (T q x)
    rw [← map_add, T.map_add]
    rfl
  · intro c p
    refine ContinuousLinearMap.coe_injective (Submodule.linearMap_qext S (LinearMap.ext fun x ↦ ?_))
    change S.mkQ (T (c • p) x) = c • S.mkQ (T p x)
    rw [← map_smul, T.map_smul]
    rfl

/-- Paper: (10.3.1.2), p. 448, and (10.3.2.2), p. 454. The descended action
is complex linear in the test. -/
theorem spectralConvolution_isLinear :
    IsLinearMap ℂ (spectralConvolution (F := F) a hI hs) :=
  spectralConvolution_isLinear_aux (Θ(a, hI, hs)) (testAction(l, r, s, hI, hs))
    (hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs)

/-- A continuous endomorphism commuting with the translation action intertwines the
two regularized vectors obtained from Pettis integrals of the corresponding orbits. -/
private theorem hardySobolevTestAction_preserves_spectralIsotype_aux {X V : Type*}
    [CommGroup X] [MeasurableSpace X] (μ : Measure X) [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [SeparatingDual ℂ V]
    (τ : X →* (V →L[ℂ] V)) {ψ : X → ℂ} (k : X) (u w : V) (hk : τ k u = w) {a b : V}
    (ha : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) a)
    (hb : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g w) b) : τ k a = b := by
  have ev {f : X → V} {v : V} (h : HasPettisIntegral (.positive μ) f v) (δ : StrongDual ℂ V) :
      δ v = ∫ g, δ (f g) ∂μ :=
    congrArg (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) h.2
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun δ ↦ ?_
  have hδ := ev ha (δ.comp (τ k))
  rw [ContinuousLinearMap.comp_apply] at hδ
  rw [hδ, ev hb]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change δ (τ k (ψ g • τ g u)) = δ (ψ g • τ g w)
  congr 1
  rw [(τ k).map_smul, ← hk]
  congr 1
  exact congrArg (fun T : V →L[ℂ] V ↦ T u)
    (show τ k * τ g = τ g * τ k by rw [← map_mul, ← map_mul, mul_comm])

/-- The regularized action of a commutative group commutes with its translations, so it
preserves every isotype of a restricted translation action. -/
private theorem hardySobolevTestAction_preserves_spectralIsotype_aux₂ {X V : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [μ.IsHaarMeasure] [AddCommGroup V] [Module ℂ V] [UniformSpace V]
    [IsUniformAddGroup V] [PolynormableSpace ℂ V] [T2Space V] [CompleteSpace V]
    [SeparatingDual ℂ V] (τ : X →* (V →L[ℂ] V)) (hτ : Continuous (fun p : X × V ↦ τ p.1 p.2))
    (φ : BruhatCompactSupport X) (K : Subgroup X) (ω : PontryaginDual K) :
    ∀ v ∈ actionIsotype (τ.comp K.subtype) ω,
      bruhatRegularizedAction μ τ hτ φ v ∈ actionIsotype (τ.comp K.subtype) ω := by
  intro v hv
  rw [mem_actionIsotype] at hv ⊢
  intro k
  have h := hardySobolevTestAction_preserves_spectralIsotype_aux μ τ k.val v ((ω k : ℂ) • v)
    (hv k) (bruhatRegularizedAction_apply μ τ hτ φ v)
    (bruhatRegularizedAction_apply μ τ hτ φ ((ω k : ℂ) • v))
  change τ k.val (bruhatRegularizedAction μ τ hτ φ v) = _
  exact h.trans (map_smul (bruhatRegularizedAction μ τ hτ φ) _ _)

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
Convolution preserves the ambient norm-one isotype. -/
theorem hardySobolevTestAction_preserves_spectralIsotype (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) :
    ∀ v ∈ Wω(hI, hs, ω), testAction(l, r, s, hI, hs) φ v ∈ Wω(hI, hs, ω) :=
  hardySobolevTestAction_preserves_spectralIsotype_aux₂ μ𝔽
    (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
    (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2 φ C₁ ω

local notation "Nω(" ω ")" => (Θ(a, hI, hs)).comap (Wω(hI, hs, ω)).subtype
local notation "Aω(" ω ", " φ ")" =>
  (ContinuousLinearMap.restrict (testAction(l, r, s, hI, hs) φ)
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ))

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
Convolution preserves the theta intersection in each norm-one isotype. -/
theorem hardySobolevTestAction_preserves_spectralIsotypeTheta (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) :
    Nω(ω) ≤ ((Nω(ω)).mkQL.comp Aω(ω, φ)).ker := by
  intro v hv
  have hz := hardySobolevTestAction_preserves_globalTheta (F := F) a hI hs φ
    (show v.val ∈ Θ(a, hI, hs) from hv)
  have hout : testAction(l, r, s, hI, hs) φ v.val ∈ Θ(a, hI, hs) :=
    (Submodule.Quotient.mk_eq_zero (Θ(a, hI, hs))).mp hz
  apply (Submodule.Quotient.mk_eq_zero (Nω(ω))).mpr
  exact hout

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
The isotype operator descends ambient convolution restricted to that isotype. -/
def spectralIsotypeConvolution (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽) :
    Qω(a, hI, hs, ω) →L[ℂ] Qω(a, hI, hs, ω) :=
  (Nω(ω)).liftQL ((Nω(ω)).mkQL.comp Aω(ω, φ))
    (hardySobolevTestAction_preserves_spectralIsotypeTheta (F := F) a hI hs ω φ)

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
On an isotypic representative the restricted operator takes the class of its convolution. -/
theorem spectralIsotypeConvolution_mkQ (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (v : Wω(hI, hs, ω)) :
    spectralIsotypeConvolution (F := F) a hI hs ω φ ((Nω(ω)).mkQ v) =
      (Nω(ω)).mkQ (Aω(ω, φ) v) := by
  unfold spectralIsotypeConvolution
  have h := (liftQL_mkQ_aux (Nω(ω)) ((Nω(ω)).mkQL.comp Aω(ω, φ))
    (hardySobolevTestAction_preserves_spectralIsotypeTheta (F := F) a hI hs ω φ) v)
  with_reducible_and_instances exact h.trans (Submodule.mkQL_apply _ _)

private theorem spectralConvolution_range_isotype_aux {X V : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [μ.IsHaarMeasure]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℂ V] [SeparatingDual ℂ V]
    (τ : X →* (V →L[ℂ] V)) (ψ : X → ℂ) (k : X) (c : ℂ)
    (hψ : ∀ g, ψ (k⁻¹ * g) = c * ψ g) (u a : V)
    (ha : HasPettisIntegral (.positive μ) (fun g ↦ ψ g • τ g u) a) :
    τ k a = c • a := by
  have ev (δ : StrongDual ℂ V) : δ a = ∫ g, δ (ψ g • τ g u) ∂μ :=
    congrArg (fun z : PettisWeakCompletion V ↦
      (show Module.Dual ℂ (StrongDual ℂ V) from z) δ) ha.2
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro δ
  have hδ := ev (δ.comp (τ k))
  rw [ContinuousLinearMap.comp_apply] at hδ
  calc
    δ (τ k a) = ∫ g, δ (τ k (ψ g • τ g u)) ∂μ := hδ
    _ = ∫ g, δ (ψ g • τ (k * g) u) ∂μ := by
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [(τ k).map_smul, map_mul]
      rfl
    _ = ∫ g, δ (ψ (k⁻¹ * g) • τ g u) ∂μ := by
      rw [← integral_mul_left_eq_self
        (fun g ↦ δ (ψ (k⁻¹ * g) • τ g u)) k]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      simp
    _ = c * ∫ g, δ (ψ g • τ g u) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [hψ g, mul_smul, map_smul]
      simp
    _ = δ (c • a) := by rw [← ev δ, map_smul]; rfl

/-- Paper: Theorems 10.3.1.1(3), p. 449, and 10.3.2.1(3), p. 454.
The full quotient action of an isotypic test has range in the corresponding quotient isotype.
Deviation: For left translation φ(x) ↦ φ(k⁻¹x), the weight is ω as an
eigencharacter. Equivalently the pointwise covariance is φ(kx) = ω⁻¹(k)φ(x). -/
theorem spectralConvolution_range_isotype (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    range (spectralConvolution (F := F) a hI hs φ) ⊆
      range (fun v : Wω(hI, hs, ω) ↦ (Θ(a, hI, hs)).mkQ v.val) := by
  have hW (v : W(l, r, s)) :
      testAction(l, r, s, hI, hs) φ v ∈ Wω(hI, hs, ω) := by
    rw [mem_actionIsotype]
    intro k
    exact spectralConvolution_range_isotype_aux μ𝔽
      (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs) φ.val k.val (ω k : ℂ)
      (_hφ k) v _ (bruhatRegularizedAction_apply μ𝔽
        (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs)
        (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2 φ v)
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (Θ(a, hI, hs)) x
  exact ⟨⟨testAction(l, r, s, hI, hs) φ v, hW v⟩,
    spectralConvolution_mkQ (F := F) a hI hs φ v⟩

end Convolution

section FiniteSums

variable {ι Z E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Paper: (10.3.1.1), p. 448, and (10.3.2.1), p. 453. Form a finite section
by summing the rank-one contributions of all jets belonging to the selected zeros.
The functional in each term is the transpose of convolution applied to that jet. -/
def spectralConvolutionFiniteSum (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) : E →L[ℂ] E :=
  ∑ z ∈ K, ∑ m : Fin (N z), ((Λ (jet z m)).comp A).smulRight (x (jet z m))

/-- Paper: (10.3.1.21), p. 451. The finite section at one zero with one
surviving jet is exactly the transpose functional times its biorthogonal vector.
Deviation: Sanity check in multiplicity one. -/
theorem spectralConvolutionFiniteSum_single (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (z : Z) (jet : Z → Fin 1 → ι) :
    spectralConvolutionFiniteSum A x Λ {z} (fun _ ↦ 1) jet =
      ((Λ (jet z 0)).comp A).smulRight (x (jet z 0)) := by
  simp [spectralConvolutionFiniteSum]

end FiniteSums

section TraceNormLimits

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Paper: (10.3.1.23), p. 452. Trace-norm Cauchy tails for a rectangular
family of finite-rank operators. A trace-class witness gives the difference
its actual trace norm. -/
def SpectralRectanglesTraceCauchy (B : ℕ × ℕ → H →L[ℂ] H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ i : ℕ × ℕ, ∀ j k, i ≤ j → i ≤ k →
    ∃ T : nuclearEndomorphisms H, T.val = B j - B k ∧ traceNorm T < ε

/-- Paper: (10.3.1.23), p. 452. Constant rectangles have zero differences.
Deviation: Sanity check for the trace-norm Cauchy condition. -/
theorem spectralRectanglesTraceCauchy_const (A : H →L[ℂ] H) :
    SpectralRectanglesTraceCauchy (fun _ ↦ A) := by
  intro ε hε
  refine ⟨(0, 0), fun _ _ _ _ ↦ ⟨0, by simp, ?_⟩⟩
  letI : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hz := ((traceNorm_normedSpaceCore (H := H)).norm_eq_zero_iff
    (0 : nuclearEndomorphisms H)).mpr rfl
  exact lt_of_eq_of_lt hz hε

private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg
    (T : H →L[ℂ] H) (n : ℕ) : 0 ≤ approximationNumber T n :=
  Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _

/-- Every finite sum of approximation numbers is bounded by the trace norm. -/
private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_bound
    (T : nuclearEndomorphisms H) (s : Finset ℕ) :
    ∑ n ∈ s, approximationNumber T.val n ≤ traceNorm T := by
  have hmem := (mem_traceClassOperators_iff_isNuclearOperator T.val).2 T.property
  have hsum : Summable (approximationNumber T.val) := by simpa using hmem.2
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  rw [← ht]
  exact hsum.sum_le_tsum s (fun n _ ↦ spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg T.val n)

/-- Once the rectangle includes a zero, its jets reproduce the corresponding
coordinates of the image of the original operator. -/
private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate {ι Z : Type*}
    (A : H →L[ℂ] H) (x : ι → H) (Λ : ι → StrongDual ℂ H) (K : Finset Z)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : Injective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (z : Z) (hz : z ∈ K) (m : Fin (N z)) (v : H) :
    Λ (jet z m) (spectralConvolutionFiniteSum A x Λ K N jet v) = Λ (jet z m) (A v) := by
  classical
  simp only [spectralConvolutionFiniteSum, sum_apply, map_sum, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem z hz]
  · rw [Finset.sum_eq_single m]
    · rw [hb.1, mul_one]
    · intro k _ hk
      have hne : jet z k ≠ jet z m :=
        fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.mp (hj (a₁ := ⟨z, k⟩) (a₂ := ⟨z, m⟩) h)).2)
      rw [hb.2.1 _ _ hne, mul_zero]
    · simp
  · intro w _ hw
    apply Finset.sum_eq_zero
    intro k _
    have hne : jet w k ≠ jet z m :=
      fun h ↦ hw (congrArg Sigma.fst (hj (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h))
    rw [hb.2.1 _ _ hne, mul_zero]

/-- Trace-norm Cauchy bounds pass to each finite sum of powers of approximation
numbers at an operator-norm limit. Taking their supremum controls the Schatten tail. -/
private theorem spectralConvolutionFiniteSum_limit_of_traceCauchy_tail
    (B : ℕ × ℕ → H →L[ℂ] H) (C : H →L[ℂ] H) (hlim : Tendsto B atTop (𝓝 C))
    (hc : SpectralRectanglesTraceCauchy B) (p : ℝ) (hp : 1 ≤ p) (ε : ℝ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∀ᶠ j in atTop, Summable (fun n ↦ approximationNumber (B j - C) n ^ p) ∧
      ∑' n, approximationNumber (B j - C) n ^ p ≤ ε := by
  have nn := spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (H := H)
  have hcont (n : ℕ) : Continuous (fun D : H →L[ℂ] H ↦ approximationNumber D n) :=
    (LipschitzWith.of_dist_le' (K := 1) (fun D E ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, one_mul] using abs_approximationNumber_sub_le D E n)).continuous
  obtain ⟨i, hi⟩ := hc ε hε
  filter_upwards [eventually_ge_atTop i] with j hj
  have hbound (s : Finset ℕ) : ∑ n ∈ s, approximationNumber (B j - C) n ^ p ≤ ε := by
    apply le_of_tendsto (tendsto_finsetSum s fun n _ ↦
      ((hcont n).continuousAt.tendsto.comp (tendsto_const_nhds.sub hlim)).rpow_const
        (Or.inr (zero_le_one.trans hp)))
    filter_upwards [eventually_ge_atTop i] with k hk
    obtain ⟨T, hT, ht⟩ := hi j k hj hk
    change ∑ n ∈ s, approximationNumber (B j - B k) n ^ p ≤ ε
    rw [← hT]
    refine (Finset.sum_le_sum fun n _ ↦ Real.rpow_le_self_of_le_one (nn _ n) ?_ hp).trans
      ((spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T s).trans ht.le)
    have h := spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T {n}
    exact (by simpa using h : approximationNumber T.val n ≤ traceNorm T).trans (ht.le.trans hε₁)
  have hnonneg : 0 ≤ fun n ↦ approximationNumber (B j - C) n ^ p :=
    fun n ↦ Real.rpow_nonneg (nn _ n) _
  exact ⟨summable_of_sum_le hnonneg hbound, Real.tsum_le_of_sum_le hnonneg hbound⟩

/-- Paper: (10.3.1.23), p. 452. A trace-norm Cauchy family of biorthogonal
finite sections converges to the given operator in every Schatten norm.
Each coordinate of the image eventually agrees with the corresponding
coordinate of the operator. Totality of the functionals identifies the limit. -/
theorem spectralConvolutionFiniteSum_limit_of_traceCauchy {ι Z : Type*}
    (A : H →L[ℂ] H) (x : ι → H) (Λ : ι → StrongDual ℂ H)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι)
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let B (ij : ℕ × ℕ) := spectralConvolutionFiniteSum A x Λ
      (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) N jet
    let S := schattenClass H H p hp
    SpectralRectanglesTraceCauchy B →
      ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
        Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
          (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  classical
  intro B S hc
  have hB (j) : B j ∈ S := by
    exact S.sum_mem fun z _ ↦ S.sum_mem fun m _ ↦ smulRight_mem_schattenClass hp _ _
  have hCauchy : CauchySeq B := by
    refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
    obtain ⟨i, hi⟩ := hc ε hε
    refine ⟨i, fun j hj k hk ↦ ?_⟩
    obtain ⟨T, hT, ht⟩ := hi j k hj hk
    rw [dist_eq_norm, ← hT, ← approximationNumber_zero_eq_opNorm T.val
      (isCompactOperator_of_isNuclearOperator T.property)]
    have h := spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T {0}
    exact lt_of_le_of_lt (by simpa using h) ht
  obtain ⟨C, hlim⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hCA : C = A := by
    ext v
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    have hev : ContinuousLinearMap.apply ℂ ℂ (C v) = ContinuousLinearMap.apply ℂ ℂ (A v) := by
      apply ContinuousLinearMap.ext_on _hb.2.2.2
      rintro _ ⟨i, rfl⟩
      obtain ⟨⟨z, m⟩, rfl⟩ := _hj.2 i
      change Λ (jet z m) (C v) = Λ (jet z m) (A v)
      apply tendsto_nhds_unique ((Λ (jet z m)).continuous.continuousAt.tendsto.comp
        (((ContinuousLinearMap.apply ℂ H v).continuous.continuousAt.tendsto).comp hlim))
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (e z)] with j hj
      exact (spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate A x Λ _ N jet _hb _hj.1
        z (Finset.mem_preimage.mpr (Finset.mem_product.mpr
          ⟨Finset.mem_Iic.mpr hj.1, Finset.mem_Iic.mpr hj.2⟩)) m v).symm
    exact fun ℓ ↦ DFunLike.congr_fun hev ℓ
  subst C
  have hcompact := isCompactOperator_of_tendsto hlim (.of_forall fun j ↦ (hB j).1)
  have tail := spectralConvolutionFiniteSum_limit_of_traceCauchy_tail B A hlim hc p hp
  obtain ⟨j, hj, _⟩ := (tail 1 zero_lt_one le_rfl).exists
  have hdiff : B j - A ∈ S := ⟨(hB j).1.sub hcompact, hj⟩
  have hA : A ∈ S := by simpa only [sub_sub_cancel] using S.sub_mem (hB j) hdiff
  refine ⟨hA, hB, ?_⟩
  have hzero : Tendsto (fun j ↦ ∑' n, approximationNumber (B j - A) n ^ p) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [tail _ (lt_min (half_pos hε) zero_lt_one) (min_le_right (ε / 2) 1)] with j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun n ↦ Real.rpow_nonneg
      (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (B j - A) n) p)]
    exact hj.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε))
  exact hzero.rpow_const_nhds_zero (one_div_pos.mpr (zero_lt_one.trans_le hp))

/-- An operator whose range lies in a subspace of dimension at most `r` is a sum of
`r` rank-one operators whose functionals have norm at most that of the operator and
whose vectors have norm at most one. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_rankOne
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] (D : H →L[ℂ] H) (hD : ∀ x, D x ∈ V)
    (r : ℕ) (hr : Module.finrank ℂ V ≤ r) :
    ∃ (Λ : ℕ → StrongDual ℂ H) (y : ℕ → H), (∀ i, ‖Λ i‖ ≤ ‖D‖ ∧ ‖y i‖ ≤ 1) ∧
      ∑ i ∈ Finset.range r, (Λ i).smulRight (y i) = D := by
  classical
  let b := stdOrthonormalBasis ℂ V
  let d := Module.finrank ℂ V
  let y : ℕ → H := fun i ↦ if h : i < d then (b ⟨i, h⟩ : H) else 0
  have hy (i : ℕ) : ‖y i‖ ≤ 1 := by
    by_cases h : i < d
    · simp only [y, h, ↓reduceDIte, Submodule.norm_coe]
      exact (b.orthonormal.1 _).le
    · simp [y, h]
  refine ⟨fun i ↦ (innerSL ℂ (y i)).comp D, y, fun i ↦ ⟨?_, hy i⟩, ?_⟩
  · calc ‖(innerSL ℂ (y i)).comp D‖ ≤ ‖innerSL ℂ (y i)‖ * ‖D‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖D‖ := by
          rw [innerSL_apply_norm]
          exact mul_le_mul_of_nonneg_right (hy i) (norm_nonneg _)
      _ = ‖D‖ := one_mul _
  · ext x
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    rw [← Finset.sum_subset (Finset.range_mono hr) (fun i _ hi ↦ by
      have hi' : ¬ i < d := fun h ↦ hi (Finset.mem_range.mpr h)
      simp only [y, hi', ↓reduceDIte, smul_zero]), Finset.sum_range]
    have h := congrArg Subtype.val (b.sum_repr' ⟨D x, hD x⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, Submodule.coe_inner] at h
    refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans h
    simp only [y, dif_pos (show (j : ℕ) < d from j.is_lt), Fin.eta]

/-- Rapid decay against `n ^ k` for every `k` gives rapid decay against `(n + 1) ^ k`. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_succ
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * f n) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ k * f n) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n : ℕ ↦ 2 ^ k * ((n : ℝ) ^ k * f n)) atTop (𝓝 0) := by
    simpa using (hf k).const_mul (2 ^ k)
  refine squeeze_zero' (.of_forall fun n ↦ mul_nonneg (by positivity) (hf0 n)) ?_ h2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) k) (hf0 n)

/-- If `c n ≤ e (n + 1) + e n` and `e` decays rapidly, then `c (⌊√m⌋)` decays rapidly in `m`. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_sqrt
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n)
    (he : ∀ j : ℕ, Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ j * e n) atTop (𝓝 0))
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : ∀ n, c n ≤ e (n + 1) + e n) (k : ℕ) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) ^ k * c (Nat.sqrt m)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (2 * k) * e (n + 1)) atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 1).mpr (he (2 * k))
    refine squeeze_zero (fun n ↦ mul_nonneg (by positivity) (he0 _)) (fun n ↦ ?_) h
    push_cast
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (he0 _)
  have hg : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (2 * k) * c n) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ mul_nonneg (by positivity) (hc0 n)) (fun n ↦ ?_)
      (by simpa using hshift.add (he (2 * k)))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hc n) (by positivity)
  have hsqrt : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b * b, fun m hm ↦ Nat.le_sqrt.mpr hm⟩
  refine squeeze_zero (fun m ↦ mul_nonneg (by positivity) (hc0 _)) (fun m ↦ ?_) (hg.comp hsqrt)
  simp only [Function.comp_apply]
  refine mul_le_mul_of_nonneg_right ?_ (hc0 _)
  rw [pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have h := Nat.lt_succ_sqrt' m
  have h' : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) ^ 2 := by exact_mod_cast h
  exact h'.le

/-- Rescaling a rank-one term by the norm bound of its functional. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_smul
    (c : ℝ) (Λ : StrongDual ℂ H) (hΛ : ‖Λ‖ ≤ c) (v : H) :
    (c : ℂ) • (((c : ℂ)⁻¹ • Λ).smulRight v) = Λ.smulRight v ∧ ‖(c : ℂ)⁻¹ • Λ‖ ≤ 1 := by
  by_cases hc : c = 0
  · subst hc
    have : Λ = 0 := norm_le_zero_iff.mp hΛ
    subst this
    simp
  constructor
  · ext x
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_smul,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc), one_mul]
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    have hc' : 0 < c := lt_of_le_of_ne ((norm_nonneg _).trans hΛ) (Ne.symm hc)
    rw [abs_of_pos hc', inv_mul_le_iff₀ hc', mul_one]
    exact hΛ

/-- An approximant of rank at most `n` within `2⁻ⁿ` of the `n`-th approximation number;
the zeroth one is zero. -/
private theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_approx
    (A : H →L[ℂ] H) (n : ℕ) :
    ∃ S : H →L[ℂ] H, FiniteDimensional ℂ (LinearMap.range S.toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range S.toLinearMap) ≤ n ∧
      ‖S - A‖ ≤ approximationNumber A n + (1 / 2) ^ n ∧ (n = 0 → S = 0) := by
  let X : Set ℝ := {r | ∃ S : H →L[ℂ] H,
    Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - A‖}
  have hX : X.Nonempty := ⟨_, 0, by simp, rfl⟩
  have hlt : sInf X < sInf X + (1 / 2) ^ n := lt_add_of_pos_right _ (by positivity)
  obtain ⟨r, ⟨S, hS, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hX hlt
  have hfin : FiniteDimensional ℂ (LinearMap.range S.toLinearMap) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hS Cardinal.natCast_lt_aleph0)
  have hrank : Module.finrank ℂ (LinearMap.range S.toLinearMap) ≤ n :=
    Module.finrank_le_of_rank_le hS
  refine ⟨S, hfin, hrank, hr.le, fun hn ↦ ?_⟩
  subst hn
  have h0 : LinearMap.range S.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hrank)
  ext x
  have hx : S x ∈ LinearMap.range S.toLinearMap := ⟨x, rfl⟩
  rw [h0, Submodule.mem_bot] at hx
  simpa using hx

/-- Paper: Theorem 10.3.1.1(3), p. 449. Rapid decay of the approximation
numbers gives a strongly nuclear expansion by the singular-value decomposition. -/
theorem isStronglyNuclearBanachOperator_of_rapid_approximationNumbers (A : H →L[ℂ] H)
    (_hA : ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n)
      atTop (𝓝 0)) : IsStronglyNuclearBanachOperator A := by
  classical
  choose S hSfin hSrank hSA hS0 using
    isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_approx A
  have hdec (n : ℕ) : ∃ (Λ : ℕ → StrongDual ℂ H) (y : ℕ → H),
      (∀ i, ‖Λ i‖ ≤ ‖S (n + 1) - S n‖ ∧ ‖y i‖ ≤ 1) ∧
      ∑ i ∈ Finset.range (2 * n + 1), (Λ i).smulRight (y i) = S (n + 1) - S n := by
    have := hSfin n
    have := hSfin (n + 1)
    refine isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_rankOne
      (LinearMap.range (S (n + 1)).toLinearMap ⊔ LinearMap.range (S n).toLinearMap)
      (S (n + 1) - S n) (fun x ↦ ?_) (2 * n + 1) ?_
    · exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩)
        (Submodule.mem_sup_right ⟨x, rfl⟩)
    · refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      have := hSrank n
      have := hSrank (n + 1)
      omega
  choose Λ y hΛy hsum using hdec
  let e : ℕ → ℝ := fun n ↦ ‖S n - A‖
  let a : ℕ → ℝ := fun n ↦ approximationNumber A n
  have ha0 (n : ℕ) : 0 ≤ a n :=
    Real.sInf_nonneg (by rintro _ ⟨T, -, rfl⟩; exact norm_nonneg _)
  have he (j : ℕ) : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ j * e n) atTop (𝓝 0) := by
    have h1 := isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_succ a ha0 _hA j
    have h2 := isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_succ
      (fun n ↦ (1 / 2 : ℝ) ^ n) (fun n ↦ by positivity)
      (fun k ↦ tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by norm_num)) j
    refine squeeze_zero (fun n ↦ mul_nonneg (by positivity) (norm_nonneg _)) (fun n ↦ ?_)
      (by simpa using h1.add h2)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left ((hSA n).trans_eq (by rw [one_div, inv_pow])) (by positivity)
  let c : ℕ → ℝ := fun n ↦ ‖S (n + 1) - S n‖
  have hc (n : ℕ) : c n ≤ e (n + 1) + e n := by
    have : S (n + 1) - S n = (S (n + 1) - A) - (S n - A) := by abel
    simp only [c, e, this]
    exact norm_sub_le _ _
  have hdecay := isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_sqrt e
    (fun n ↦ norm_nonneg _) he c (fun n ↦ norm_nonneg _) hc
  let idx : ℕ → ℕ := fun m ↦ m - Nat.sqrt m * Nat.sqrt m
  let term : ℕ → H →L[ℂ] H := fun m ↦ (c (Nat.sqrt m) : ℂ) •
    (((c (Nat.sqrt m) : ℂ)⁻¹ • Λ (Nat.sqrt m) (idx m)).smulRight (y (Nat.sqrt m) (idx m)))
  have hterm (m : ℕ) : term m = (Λ (Nat.sqrt m) (idx m)).smulRight (y (Nat.sqrt m) (idx m)) :=
    (isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_smul _ _
      (hΛy _ _).1 _).1
  have hblock (N : ℕ) : ∑ m ∈ Finset.range (N * N), term m = S N := by
    induction N with
    | zero => simp [hS0 0 rfl]
    | succ N ih =>
      rw [show (N + 1) * (N + 1) = N * N + (2 * N + 1) by ring, Finset.sum_range_add, ih,
        show S (N + 1) = S N + (S (N + 1) - S N) by abel, ← hsum N]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' : i ≤ N + N := by rw [Finset.mem_range] at hi; omega
      rw [hterm]
      simp only [idx, Nat.sqrt_add_eq N hi', Nat.add_sub_cancel_left]
  have hS : Tendsto S atTop (𝓝 A) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [e] using he 0)
  have hnorm (m : ℕ) : ‖term m‖ ≤ c (Nat.sqrt m) := by
    rw [hterm, ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul (hΛy _ _).1 (hΛy _ _).2 (norm_nonneg _) (norm_nonneg _)).trans_eq
      (mul_one _)
  have hsumm : Summable term := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun m : ℕ ↦ 1 / (m : ℝ) ^ 2)
      (Real.summable_one_div_nat_pow.mpr one_lt_two) ?_
    filter_upwards [(hdecay 2).eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1]
      with m h1 hm
    have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    refine (hnorm m).trans ?_
    rw [le_div_iff₀ hm', mul_comm]
    exact h1.le
  have hsq : Tendsto (fun N : ℕ ↦ N * N) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun N hN ↦ hN.trans (Nat.le_mul_self N)⟩
  have hlim : ∑' m, term m = A := by
    refine tendsto_nhds_unique ((hsumm.hasSum.tendsto_sum_nat).comp hsq) ?_
    refine hS.congr fun N ↦ ?_
    exact (hblock N).symm
  refine ⟨fun m ↦ (c (Nat.sqrt m) : ℂ), fun m ↦ (c (Nat.sqrt m) : ℂ)⁻¹ • Λ (Nat.sqrt m) (idx m),
    fun m ↦ y (Nat.sqrt m) (idx m), fun m ↦ ⟨?_, (hΛy _ _).2⟩, fun k ↦ ?_, ?_⟩
  · exact (isStronglyNuclearBanachOperator_of_rapid_approximationNumbers_smul _ _
      (hΛy _ _).1 (0 : H)).2
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (hdecay k).congr fun m ↦ ?_
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  · exact hlim ▸ hsumm.hasSum


end TraceNormLimits

-- TODO(paper-gap): On p. 450 an interval cannot select an arbitrary K with
-- omitted zeros between selected ordinates. The sums below use the actual
-- biorthogonal finite sections of (10.3.1.1) and (10.3.2.1).
-- TODO(paper-gap): (10.3.1.18) uses a uniform bound on paired norms, which fails
-- for close simple zeta zeros (ERRATA R5). The finite sections need another estimate.
-- The same display evaluates the entire Mellin transform at t. Its block matrix
-- in (10.3.1.17) uses i*t. A transform (t-z)H(z) separates the two points.

/-- Paper: (10.3.1.18)–(10.3.1.22), p. 451. Each individual finite section
has a singular-value bound in terms of its actual rank-one factors.
Deviation: The bound depends on the selected vectors and functionals. For a
single zero it is a local block bound, with no uniform biorthogonal constant. -/
theorem spectralConvolutionFiniteSum_approximationNumber_le {ι Z E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (x : ι → E) (Λ : ι → StrongDual ℂ E)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → ι) (n : ℕ) :
    approximationNumber (spectralConvolutionFiniteSum A x Λ K N jet) n ≤
      ∑ z ∈ K, ∑ m : Fin (N z), ‖(Λ (jet z m)).comp A‖ * ‖x (jet z m)‖ := by
  classical
  let T := spectralConvolutionFiniteSum A x Λ K N jet
  have h : approximationNumber T n ≤ ‖T‖ := by
    unfold approximationNumber
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro _ ⟨S, _, rfl⟩
      exact norm_nonneg _
    · exact ⟨0, by simp, by simp⟩
  apply h.trans
  unfold T spectralConvolutionFiniteSum
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun z _ ↦ ?_
  simpa only [ContinuousLinearMap.norm_smulRight_apply] using
    (norm_sum_le Finset.univ (fun m : Fin (N z) ↦ ((Λ (jet z m)).comp A).smulRight (x (jet z m))))

/-- Paper: (10.3.1.17), p. 450. Compactly supported Bruhat tests have
an integrable Fourier–Mellin pairing at every norm twist. The pairing is
the unweighted integral against the twisted base character. -/
theorem spectralConvolution_mellin_integrable (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C𝔽) (z : ℂ) :
    Integrable (fun g ↦ φ.val g * ideleClassNormTwist (F := F) χ z g) μ𝔽 ∧
      M(φ, χ, z) = ∫ g, φ.val g * ideleClassNormTwist (F := F) χ z g ∂μ𝔽 := by
  have hc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  constructor
  · exact (hc.mul (ideleClassNormTwist χ z).continuous).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  · exact Set.indicator_of_mem (Set.mem_univ _) _

section ApproximationDecay

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem spectralApprox_antitone (A : H →L[ℂ] H) : Antitone (approximationNumber A) := by
  intro m n hmn
  unfold approximationNumber
  refine le_csInf ⟨_, 0, by simp, rfl⟩ ?_
  rintro _ ⟨S, hS, rfl⟩
  exact csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩
    ⟨S, hS.trans (Nat.cast_le.mpr hmn), rfl⟩

omit [CompleteSpace H] in
/-- Adding two rank-n approximants gives a rank-at-most-2n approximant. -/
private theorem spectralApprox_add (A B : H →L[ℂ] H) (n : ℕ) :
    approximationNumber (A + B) (2 * n + 1) ≤ approximationNumber A n + approximationNumber B n := by
  refine le_add_of_forall_lt fun a ha b hb ↦ ?_
  have nonempty (T : H →L[ℂ] H) :
      {r : ℝ | ∃ S : H →L[ℂ] H, S.toLinearMap.rank ≤ (n : Cardinal) ∧ r = ‖S - T‖}.Nonempty :=
    ⟨_, 0, by simp, rfl⟩
  obtain ⟨_, ⟨S, hS, rfl⟩, hSa⟩ := exists_lt_of_csInf_lt (nonempty A) ha
  obtain ⟨_, ⟨T, hT, rfl⟩, hTb⟩ := exists_lt_of_csInf_lt (nonempty B) hb
  have hrank : (S + T).toLinearMap.rank ≤ ((2 * n + 1 : ℕ) : Cardinal) := by
    refine (LinearMap.rank_add_le _ _).trans ((add_le_add hS hT).trans ?_)
    exact_mod_cast (show n + n ≤ 2 * n + 1 by omega)
  calc
    approximationNumber (A + B) (2 * n + 1) ≤ ‖S + T - (A + B)‖ :=
      csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨S + T, hrank, rfl⟩
    _ = ‖(S - A) + (T - B)‖ := by congr 1; abel
    _ ≤ a + b := (norm_add_le _ _).trans (add_le_add hSa.le hTb.le)

private abbrev SpectralApproxBound (A : H →L[ℂ] H) (k : ℕ) :=
  ∃ C : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) ^ k * approximationNumber A n ≤ C

/-- A polynomial bound on odd approximation numbers extends to all indices by monotonicity. -/
private theorem spectralApprox_bound_of_odd (A : H →L[ℂ] H) (k : ℕ) (C : ℝ)
    (h : ∀ m : ℕ, ((m : ℝ) + 1) ^ k * approximationNumber A (2 * m + 1) ≤ C) :
    SpectralApproxBound A k := by
  refine ⟨max (approximationNumber A 0) (3 ^ k * C), fun n ↦ ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    let m := n / 2
    have hi : 2 * m + 1 ≤ n + 1 := by dsimp [m]; omega
    have hc : ((n + 1 : ℕ) : ℝ) + 1 ≤ 3 * ((m : ℝ) + 1) := by
      exact_mod_cast (show n + 1 + 1 ≤ 3 * (m + 1) by dsimp [m]; omega)
    apply le_trans _ (le_max_right _ _)
    calc
      _ ≤ (3 * ((m : ℝ) + 1)) ^ k * approximationNumber A (2 * m + 1) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hc k) (spectralApprox_antitone A hi)
          (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg _ _) (by positivity)
      _ = 3 ^ k * (((m : ℝ) + 1) ^ k * approximationNumber A (2 * m + 1)) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (h m) (by positivity)

/-- Trace-class operators have a uniform, one-power approximation-number bound. -/
private theorem spectralApprox_trace (T : nuclearEndomorphisms H) : SpectralApproxBound T.val 1 := by
  refine ⟨traceNorm T, fun n ↦ ?_⟩
  have h := Finset.sum_le_sum (s := Finset.range (n + 1))
    (fun i hi ↦ spectralApprox_antitone T.val (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  calc
    _ = ∑ _i ∈ Finset.range (n + 1), approximationNumber T.val n := by simp
    _ ≤ _ := h.trans (spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T _)

private theorem spectralApprox_bound_add (A B : H →L[ℂ] H) (k : ℕ)
    (hA : SpectralApproxBound A k) (hB : SpectralApproxBound B k) : SpectralApproxBound (A + B) k := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨D, hD⟩ := hB
  apply spectralApprox_bound_of_odd _ _ (C + D)
  intro n
  calc
    _ ≤ ((n : ℝ) + 1) ^ k * (approximationNumber A n + approximationNumber B n) :=
      mul_le_mul_of_nonneg_left (spectralApprox_add A B n) (by positivity)
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hC n) (hD n)

private theorem spectralApprox_bound_comp (A B : H →L[ℂ] H) (k : ℕ)
    (hA : SpectralApproxBound A k) (hB : SpectralApproxBound B 1) :
    SpectralApproxBound (A.comp B) (k + 1) := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨D, hD⟩ := hB
  apply spectralApprox_bound_of_odd _ _ (C * D)
  intro n
  have ha := spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg A n
  have hb := spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg B n
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (by positivity) ha) (hC n)
  calc
    _ ≤ ((n : ℝ) + 1) ^ (k + 1) * (approximationNumber A n * approximationNumber B n) :=
      mul_le_mul_of_nonneg_left (by simpa [two_mul] using approximationNumber_comp_le A B n n)
        (by positivity)
    _ = (((n : ℝ) + 1) ^ k * approximationNumber A n) *
          (((n : ℝ) + 1) ^ 1 * approximationNumber B n) := by ring
    _ ≤ _ := mul_le_mul (hC n) (hD n) (mul_nonneg (by positivity) hb) hC0

/-- A family of trace-class operators in which every member is a finite sum of
two-fold products of family members has rapidly decreasing approximation numbers. -/
private theorem spectralApprox_rapid_of_factorization {ι : Type*} (A : ι → H →L[ℂ] H)
    (htrace : ∀ i, IsNuclearOperator (A i))
    (hfactor : ∀ i, A i ∈ AddSubmonoid.closure {T | ∃ j l, T = (A j).comp (A l)}) (i : ι) (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber (A i) n) atTop (𝓝 0) := by
  have bounds (p : ℕ) : ∀ j, SpectralApproxBound (A j) p := by
    induction p with
    | zero => exact fun j ↦ ⟨approximationNumber (A j) 0, fun n ↦ by
        simpa using spectralApprox_antitone (A j) (Nat.zero_le n)⟩
    | succ p ih =>
      intro j
      apply AddSubmonoid.closure_induction (motive := fun T _ ↦ SpectralApproxBound T (p + 1))
        _ _ _ (hfactor j)
      · rintro T ⟨u, v, rfl⟩
        exact spectralApprox_bound_comp _ _ _ (ih u) (spectralApprox_trace ⟨A v, htrace v⟩)
      · refine ⟨0, fun n ↦ ?_⟩
        have hz : approximationNumber (0 : H →L[ℂ] H) n ≤ ‖(0 : H →L[ℂ] H) - 0‖ :=
          csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨0, by simp, rfl⟩
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by simpa using hz)
      · exact fun X Y _ _ ↦ spectralApprox_bound_add X Y _
  obtain ⟨C, hC⟩ := bounds (k + 1) i
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine squeeze_zero (fun n : ℕ ↦ mul_nonneg (by positivity)
    (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (A i) n)) ?_
    (show Tendsto (fun n : ℕ ↦ C * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) by simpa using hinv.const_mul C)
  intro n
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ ((n : ℝ) + 1) ^ k * approximationNumber (A i) n * ((n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ n.cast_nonneg (by linarith) k)
        (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg (A i) n)) (by positivity)
    _ = ((n : ℝ) + 1) ^ (k + 1) * approximationNumber (A i) n := by ring
    _ ≤ C := hC n

end ApproximationDecay

section TestFactorization

private local instance spectralApprox_isotype_polynormable (a : ℝ) {l r s : ℝ} (hI : l ≤ r)
    (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : PolynormableSpace ℂ Qω(a, hI, hs, ω) :=
  (norm_withSeminorms ℂ Qω(a, hI, hs, ω)).toPolynormableSpace

/-- Bounded restriction and projection preserve a Banach nuclear presentation. -/
private theorem spectralApprox_nuclear_compression {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (J : K →L[ℂ] H) (P : H →L[ℂ] K) :
    IsNuclearOperator (P.comp (A.comp J)) := by
  obtain ⟨c, f, y, hc, hf, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear _).mp hA
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, fun n ↦ (f n).comp J, P ∘ y, hc, ?_,
    (P.continuous.tendsto' 0 0 (map_zero P)).comp hy, fun x ↦ ?_⟩
  · exact ((J.precomp ℂ).continuous.tendsto' 0 0 (map_zero _)).comp hf
  · simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using
      P.hasSum (hs (J x))

/-- The quotient representative formulas identify the compression with the restricted action. -/
private theorem spectralApprox_nuclear_representatives {H K V W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [PolynormableSpace ℂ H] [PolynormableSpace ℂ K]
    (A : H →L[ℂ] H) (D : K →L[ℂ] K) (hn : IsNuclearOperator A)
    (S : Submodule ℂ H) [CompleteSpace S] (U : K ≃ₗᵢ[ℂ] S)
    (q : V → K) (π : W → H) (i : V → W) (B : V → V) (C : W → W)
    (hq : Surjective q) (hU : ∀ v, (U (q v) : H) = π (i v))
    (hD : ∀ v, D (q v) = q (B v))
    (hA : ∀ w, A (π w) = π (C w)) (hB : ∀ v, C (i v) = i (B v)) :
    IsNuclearOperator D := by
  let J := S.subtypeL.comp U.toContinuousLinearEquiv.toContinuousLinearMap
  let P := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp S.orthogonalProjectionOnto
  have hPJ : LeftInverse P J := fun x ↦ by
    change U.symm (S.orthogonalProjectionOnto (U x : H)) = x
    rw [S.orthogonalProjectionOnto_mem_subspace_eq_self, U.symm_apply_apply]
  have hcomp : P.comp (A.comp J) = D := by
    ext x
    obtain ⟨v, rfl⟩ := hq x
    apply Eq.trans _ (hPJ (D (q v)))
    apply congrArg P
    change A (U (q v) : H) = (U (D (q v)) : H)
    rw [hU, hA, hB, hD, hU]
  rw [← hcomp]
  exact spectralApprox_nuclear_compression A hn J P

set_option maxHeartbeats 800000 in
/-- Compress ambient convolution to the isotype using the quotient isometry and
its orthogonal projection. -/
private theorem spectralApprox_isotype_nuclear (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hn : IsNuclearOperator (spectralConvolution (F := F) a hI hs φ)) :
    let H := Qω(a, hI, hs, ω)
    let D : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a hI hs ω φ
    IsNuclearOperator (E := H) (F := H) D := by
  have hiso := spectralSobolevIsotypeQuotient_isometry (F := F) a hI hs ω
  with_reducible obtain ⟨ρ, _, _, U, hU⟩ := hiso
  let S := actionIsotype (ρ.comp (ideleClassNorm F).ker.subtype) ω
  let _ : CompleteSpace S := (isClosed_actionIsotype _ _).completeSpace_coe
  let E := Wω(hI, hs, ω)
  let N := Θ(a, hI, hs)
  let B := (testAction(l, r, s, hI, hs) φ).restrict
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ)
  with_reducible_and_instances
    exact spectralApprox_nuclear_representatives _ _ hn S U (N.comap E.subtype).mkQ N.mkQ
      Subtype.val B (testAction(l, r, s, hI, hs) φ) (N.comap E.subtype).mkQ_surjective hU
      (spectralIsotypeConvolution_mkQ (F := F) a hI hs ω φ)
      (spectralConvolution_mkQ (F := F) a hI hs φ) (fun _ ↦ rfl)

/-- Equality of descended convolutions can be checked on representatives. -/
private theorem spectralApprox_descend {H K V W : Type*}
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    (q : V →ₗ[ℂ] H) (hq : Surjective q) (i : V →ₗ[ℂ] W) (hi : Injective i)
    (f : K → H →L[ℂ] H) (g : K → W →L[ℂ] W) (b : K → V → V)
    (hf : ∀ k v, f k (q v) = q (b k v)) (hg : ∀ k v, i (b k v) = g k (i v)) :
    (∀ t, g t = 0 → f t = 0) ∧
    (∀ t u v, g t = g u + g v → f t = f u + f v) ∧
    (∀ t u v, (∀ x, g t x = g u (g v x)) → f t = (f u).comp (f v)) := by
  refine ⟨fun t ht ↦ ?_, fun t u v ht ↦ ?_, fun t u v ht ↦ ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := hq x
    change f t (q y) = 0
    rw [hf, ← q.map_zero]
    apply congrArg q
    apply hi
    rw [hg, ht, map_zero]
    rfl
  · ext x
    obtain ⟨y, rfl⟩ := hq x
    rw [add_apply, hf, hf, hf, ← q.map_add]
    apply congrArg q
    apply hi
    rw [map_add, hg, hg, hg, ht, add_apply]
  · ext x
    obtain ⟨y, rfl⟩ := hq x
    rw [ContinuousLinearMap.comp_apply, hf, hf, hf]
    apply congrArg q
    apply hi
    rw [hg, hg, hg, ht]

set_option maxHeartbeats 600000 in
private theorem spectralApprox_isotype_laws (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    let D := spectralIsotypeConvolution (F := F) a hI hs ω
    D 0 = 0 ∧ (∀ u v, D (u + v) = D u + D v) ∧
      ∀ t u v : BruhatCompactSupport C𝔽,
        t.val = lcaConvolution μ𝔽 u.val v.val → D t = (D u).comp (D v) := by
  let N := Θ(a, hI, hs)
  let E := Wω(hI, hs, ω)
  let q := (N.comap E.subtype).mkQ
  let b (φ : BruhatCompactSupport C𝔽) := (testAction(l, r, s, hI, hs) φ).restrict
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ)
  have laws := spectralApprox_descend q (N.comap E.subtype).mkQ_surjective E.subtype
    Subtype.val_injective (spectralIsotypeConvolution (F := F) a hI hs ω)
    (fun φ ↦ testAction(l, r, s, hI, hs) φ)
    (fun φ v ↦ b φ v) (spectralIsotypeConvolution_mkQ (F := F) a hI hs ω) (fun _ _ ↦ rfl)
  refine ⟨laws.1 0 (map_zero _), fun u v ↦ laws.2.1 _ u v (map_add _ _ _), ?_⟩
  intro t u v ht
  apply laws.2.2
  let ρ := hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs
  have hρ := (exists_hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).choose_spec.2
  have hconv := bruhatRegularizedAction_convolution μ𝔽 ρ hρ u v
  with_reducible obtain ⟨t', ht', hact⟩ := hconv
  have heq : t' = t := Subtype.ext (ht'.trans ht.symm)
  exact heq ▸ hact

private def spectralApprox_isotype_addHom (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    BruhatCompactSupport C𝔽 →+ (Qω(a, hI, hs, ω) →L[ℂ] Qω(a, hI, hs, ω)) where
  toFun := spectralIsotypeConvolution (F := F) a hI hs ω
  map_zero' := (spectralApprox_isotype_laws (F := F) a hI hs ω).1
  map_add' := (spectralApprox_isotype_laws (F := F) a hI hs ω).2.1

local notation "homTest(" ω ", " φ ")" =>
  ∀ (k : C₁) (x : C𝔽), (φ : BruhatCompactSupport C𝔽).val (k.val⁻¹ * x) =
    (ω k : ℂ) * (φ : BruhatCompactSupport C𝔽).val x

/-- Classical input: the Dixmier–Malliavin factorization theorem on the additive real line,
from J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. 102 (1978), 307–330. Every smooth compactly supported
function is a finite sum of convolutions of such functions for the chosen Haar measure.
`mem_bruhatCompactSupportSubmodule_real_iff` identifies the tests here with those functions. -/
private theorem spectralHomogeneousTest_real_factorization
    (ν : Measure (Multiplicative ℝ)) [ν.IsHaarMeasure]
    (f : BruhatCompactSupport (Multiplicative ℝ)) :
    f ∈ AddSubmonoid.closure {h | ∃ u v : BruhatCompactSupport (Multiplicative ℝ),
      h.val = lcaConvolution ν u.val v.val} := by
  sorry

/-- Restriction to a one-parameter subgroup is smooth in the real parameter. -/
private theorem spectralHomogeneousTest_section_smooth (σ : Multiplicative ℝ →ₜ* C𝔽)
    (f : bruhatSmoothSubmodule (G := C𝔽)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ f.val (σ (Multiplicative.ofAdd t))) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing f with
  | zero =>
    exact contDiff_zero.mpr ((continuous_of_bruhatSmooth
      ((mem_bruhatSmoothSubmodule_iff _).mp f.property)).comp σ.continuous)
  | succ n ih =>
    let d : bruhatSmoothSubmodule (G := C𝔽) :=
      ⟨bruhatDirectionalDeriv σ f.val, bruhatDirectionalDeriv_mem_smooth σ f⟩
    have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ f.val (σ (Multiplicative.ofAdd s)))
        (d.val (σ (Multiplicative.ofAdd t))) t := by
      have h := hasDerivAt_bruhatDirectionalDeriv σ
        ((mem_bruhatSmoothSubmodule_iff _).mp f.property 1) (σ (Multiplicative.ofAdd t))
      have hs := HasDerivAt.comp_sub_const t t (by simpa only [sub_self] using h)
      apply hs.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)
      change f.val (σ (Multiplicative.ofAdd s)) =
        f.val (σ (Multiplicative.ofAdd t) * σ (Multiplicative.ofAdd (s - t)))
      rw [← map_mul, ← ofAdd_add, add_sub_cancel]
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ (hd t).differentiableAt, fun h ↦ absurd h (by simp), ?_⟩
    rw [show deriv (fun t : ℝ ↦ f.val (σ (Multiplicative.ofAdd t))) =
      fun t ↦ d.val (σ (Multiplicative.ofAdd t)) from funext fun t ↦ (hd t).deriv]
    exact ih d

/-- A character times the pullback of a real-line test by the log norm is a Bruhat test. -/
private theorem spectralHomogeneousTest_lift_mem (hsur : Surjective m𝔽)
    (χ : PontryaginDual C𝔽) (f : BruhatCompactSupport (Multiplicative ℝ)) :
    (fun x : C𝔽 ↦ (χ x : ℂ) * f.val (positiveRealLogEquiv (m𝔽 x))) ∈
      bruhatCompactSupportSubmodule C𝔽 := by
  let L := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m𝔽
  have hp : IsProperMap L :=
    positiveRealLogEquiv.toHomeomorph.isProperMap.comp (isProperMap_ideleClassNorm F)
  have hc : HasCompactSupport (fun x : C𝔽 ↦ f.val (L x)) :=
    HasCompactSupport.intro (hp.isCompact_preimage f.property.2) fun _ hx ↦
      image_eq_zero_of_notMem_tsupport hx
  have hs := isBruhatSmooth_logProfile m𝔽
    ((mem_bruhatCompactSupportSubmodule_real_iff _).mp f.property).1
  have hval (x : C𝔽) : L x = Multiplicative.ofAdd (Real.log ((m𝔽 x).val : ℝ)) :=
    congrArg Multiplicative.ofAdd (positiveRealLogEquiv_apply _)
  let r : BruhatCompactSupport C𝔽 := ⟨fun x ↦ f.val (L x),
    (mem_bruhatSmoothSubmodule_iff _).mpr (by simpa only [hval, Function.comp_apply] using hs), hc⟩
  -- At weight zero the radial test is Schwartz, so it can be multiplied by the character.
  have hr := modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩
    ⟨r.val, bruhatCompactSupport_le_modulatedExponentialDecay m𝔽 univ hm𝔽 hsur r.property⟩
  rw [modulationWeight_zero] at hr
  obtain ⟨M, hM⟩ := schwartzBruhat_mul_unitaryCharacter χ
  let w := M (⟨r.val, hr⟩ : SchwartzBruhat C𝔽)
  have hw : w.val = fun x ↦ (χ x : ℂ) * f.val (L x) := funext (hM _)
  exact ⟨hw ▸ (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth w), hc.mul_left⟩

/-- The two character factors in the convolution integral multiply to `χ x`. The remaining
integrand factors through the log norm, so it integrates against the pushforward Haar measure. -/
private theorem spectralHomogeneousTest_lift_convolution (χ : PontryaginDual C𝔽)
    (u v : BruhatCompactSupport (Multiplicative ℝ)) (x : C𝔽) :
    let L := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m𝔽
    (χ x : ℂ) * lcaConvolution ((μ𝔽).map L) u.val v.val (L x) =
      lcaConvolution μ𝔽 (fun y ↦ (χ y : ℂ) * u.val (L y))
        (fun y ↦ (χ y : ℂ) * v.val (L y)) x := by
  intro L
  let b (t : Multiplicative ℝ) := u.val t * v.val (t⁻¹ * L x)
  have continuous_test (f : BruhatCompactSupport (Multiplicative ℝ)) : Continuous f.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)
  have hb : Continuous b := (continuous_test u).mul
    ((continuous_test v).comp (continuous_inv.mul continuous_const))
  change (χ x : ℂ) * (∫ t, b t ∂(μ𝔽).map L) = _
  rw [integral_map (φ := (L : C𝔽 → Multiplicative ℝ)) L.continuous.measurable.aemeasurable
    hb.aestronglyMeasurable, ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun y ↦ ?_)
  change (χ x : ℂ) * (u.val (L y) * v.val ((L y)⁻¹ * L x)) =
    ((χ y : ℂ) * u.val (L y)) * ((χ (y⁻¹ * x) : ℂ) * v.val (L (y⁻¹ * x)))
  have hχ : (χ y : ℂ) * (χ (y⁻¹ * x) : ℂ) = (χ x : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel_left]
  rw [map_mul L, map_inv, ← hχ]
  ring

/-- Paper: Theorems 10.3.1.1(3) and 10.3.2.1(3), pp. 449 and 454. A homogeneous
compactly supported Bruhat test is a finite sum of convolutions of pairs of tests
of the same character. Deviation: Isolate the radial Dixmier–Malliavin
factorization and its transport along the idelic norm. -/
private theorem spectralHomogeneousTest_convolution_factorization (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : homTest(ω, φ)) :
    φ ∈ AddSubmonoid.closure {θ : BruhatCompactSupport C𝔽 |
      ∃ ψ η : BruhatCompactSupport C𝔽,
        homTest(ω, ψ) ∧ homTest(ω, η) ∧ θ.val = lcaConvolution μ𝔽 ψ.val η.val} := by
  let L := (positiveRealLogEquiv : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m𝔽
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let σ := τ.comp (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
  have hσ (t : Multiplicative ℝ) : L (σ t) = t :=
    (congrArg positiveRealLogEquiv (hτ _)).trans (positiveRealLogEquiv.apply_symm_apply t)
  -- The inverse compact component gives the eigencharacter for left translation.
  let P : C𝔽 →ₜ* C𝔽 := (τ.comp m𝔽) / ContinuousMonoidHom.id C𝔽
  have hP (x : C𝔽) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (τ (ideleClassNorm F x) / x) = 1
    rw [map_div, hτ, div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  let χ := ω.comp r
  have hk (k : C₁) : χ k.val⁻¹ = ω k := by
    apply congrArg ω
    apply Subtype.ext
    change τ (ideleClassNorm F k.val⁻¹) / k.val⁻¹ = k.val
    rw [map_inv, show ideleClassNorm F k.val = 1 from k.property, inv_one, map_one,
      one_div, inv_inv]
  let T : BruhatCompactSupport (Multiplicative ℝ) →+ BruhatCompactSupport C𝔽 :=
    { toFun := fun f ↦ ⟨fun x ↦ (χ x : ℂ) * f.val (L x),
        spectralHomogeneousTest_lift_mem hτ.surjective χ f⟩
      map_zero' := Subtype.ext (funext fun _ ↦ mul_zero _)
      map_add' := fun _ _ ↦ Subtype.ext (funext fun _ ↦ mul_add _ _ _) }
  have hT (f : BruhatCompactSupport (Multiplicative ℝ)) : homTest(ω, T f) := by
    intro k x
    have hL : L k.val = 1 :=
      (congrArg positiveRealLogEquiv k.property).trans (map_one _)
    change (χ (k.val⁻¹ * x) : ℂ) * f.val (L (k.val⁻¹ * x)) = _
    rw [map_mul, hk, Circle.coe_mul, map_mul, map_inv, hL, inv_one, one_mul, mul_assoc]
    rfl
  -- Homogeneity recovers the whole test from its restriction to the section.
  let f : BruhatCompactSupport (Multiplicative ℝ) := ⟨φ.val ∘ σ, (mem_bruhatCompactSupportSubmodule_real_iff _).mpr
    ⟨spectralHomogeneousTest_section_smooth σ ⟨φ.val, φ.property.1⟩,
      HasCompactSupport.intro (φ.property.2.image L.continuous) (fun t ht ↦
        show φ.val (σ (Multiplicative.ofAdd t)) = 0 from
          image_eq_zero_of_notMem_tsupport fun h ↦ ht ⟨_, h, hσ t⟩)⟩⟩
  have hφT : φ = T f := by
    apply Subtype.ext
    funext x
    have he : (r x).val⁻¹ * τ (m𝔽 x) = x := by
      change (τ (m𝔽 x) / x)⁻¹ * τ (m𝔽 x) = x
      rw [inv_div, div_mul_cancel]
    have h := hφ (r x) (τ (m𝔽 x))
    rw [he] at h
    change φ.val x = (ω (r x) : ℂ) *
      φ.val (τ (positiveRealLogEquiv.symm (positiveRealLogEquiv (m𝔽 x))))
    rwa [positiveRealLogEquiv.symm_apply_apply]
  let ν : Measure (Multiplicative ℝ) := (μ𝔽).map L
  have hp : IsProperMap L :=
    positiveRealLogEquiv.toHomeomorph.isProperMap.comp (isProperMap_ideleClassNorm F)
  have : ν.IsHaarMeasure := Measure.isHaarMeasure_map μ𝔽 L.toMonoidHom L.continuous
    (RightInverse.surjective hσ) (isProperMap_iff_tendsto_cocompact.mp hp).2
  rw [hφT, ← AddSubmonoid.mem_comap (f := T)]
  refine AddSubmonoid.closure_le.mpr ?_ (spectralHomogeneousTest_real_factorization ν f)
  rintro a ⟨u, v, huv⟩
  apply AddSubmonoid.mem_comap.mpr
  refine AddSubmonoid.subset_closure ⟨T u, T v, hT u, hT v, ?_⟩
  exact funext fun x ↦ (congrArg ((χ x : ℂ) * ·) (congrFun huv (L x))).trans
    (spectralHomogeneousTest_lift_convolution χ u v x)

/-- An additive convolution action transports finite factorizations to compositions. -/
private theorem spectralApprox_map_factorization {V O : Type*}
    [AddCommMonoid V] [AddCommMonoid O] (f : V →+ O) (p : V → Prop) (R : V → V → V → Prop)
    (m : O → O → O) (hm : ∀ t u v, R t u v → f t = m (f u) (f v))
    (t : V) (ht : t ∈ AddSubmonoid.closure {t | ∃ u v, p u ∧ p v ∧ R t u v}) :
    f t ∈ AddSubmonoid.closure {z | ∃ i j : Subtype p, z = m (f i.val) (f j.val)} := by
  induction ht using AddSubmonoid.closure_induction with
  | mem t h =>
    obtain ⟨u, v, hu, hv, h⟩ := h
    exact AddSubmonoid.subset_closure ⟨⟨u, hu⟩, ⟨v, hv⟩, hm _ _ _ h⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ hu hv => rw [map_add]; exact add_mem hu hv

set_option maxHeartbeats 800000 in
private theorem spectralApprox_isotype_rapid (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hφ : homTest(ω, φ))
    (htrace : ∀ ψ : BruhatCompactSupport C𝔽, IsNuclearOperator (spectralConvolution (F := F) a hI hs ψ)) :
    let H := Qω(a, hI, hs, ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a hI hs ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by
  dsimp only
  let p := fun ψ : BruhatCompactSupport C𝔽 ↦ homTest(ω, ψ)
  let M := spectralApprox_isotype_addHom (F := F) a hI hs ω
  let A := fun i : Subtype p ↦ M i.val
  intro k
  refine spectralApprox_rapid_of_factorization (H := Qω(a, hI, hs, ω)) A ?_ ?_ ⟨φ, hφ⟩ k
  · intro i
    exact spectralApprox_isotype_nuclear (F := F) a hI hs ω i.val (htrace i.val)
  · intro i
    exact spectralApprox_map_factorization M p (fun θ ψ η ↦ θ.val = lcaConvolution μ𝔽 ψ.val η.val)
      ContinuousLinearMap.comp (spectralApprox_isotype_laws (F := F) a hI hs ω).2.2 i.val
      (spectralHomogeneousTest_convolution_factorization (F := F) ω i.val i.property)

end TestFactorization

section Line

variable (a : ℝ)

local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

/-- Finite sums of the jet functionals with vector coefficients approximate a contraction
on each biorthogonal vector without increasing its norm. Project first onto the span of
the finitely many Riesz vectors. -/
private theorem spectralLineConvolution_traceCauchy_probes {H J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) :
    ∃ v : Finset J → J → H, (∀ K i, i ∉ K → v K i = 0) ∧
      (∀ K, ‖∑ i ∈ K, (Λ i).smulRight (v K i)‖ ≤ 1) ∧
      ∀ i, Tendsto (fun K ↦ v K i) atTop (𝓝 (U (x i))) := by
  classical
  let u (i : J) := (InnerProductSpace.toDual ℂ H).symm (Λ i)
  let V (K : Finset J) := Submodule.span ℂ (u '' (K : Set J))
  let dim (K : Finset J) : FiniteDimensional ℂ (V K) :=
    FiniteDimensional.span_of_finite ℂ (K.finite_toSet.image u)
  let v (K : Finset J) (i : J) := U ((V K).starProjection (x i))
  have hoff (K : Finset J) (i : J) (hi : i ∉ K) : v K i = 0 := by
    have hperp : x i ∈ (V K)ᗮ := by
      have hV : V K ≤ (innerSL ℂ (x i)).ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, hk, rfl⟩
        apply inner_eq_zero_symm.mp
        rw [show u k = (InnerProductSpace.toDual ℂ H).symm (Λ k) from rfl,
          InnerProductSpace.toDual_symm_apply]
        exact hb.2.1 i k (fun h ↦ hi (h.symm ▸ hk))
      exact ((V K).mem_orthogonal' _).mpr (fun _ hw ↦ hV hw)
    simp only [v, ((V K).starProjection_apply_eq_zero_iff).mpr hperp, map_zero]
  refine ⟨v, hoff, fun K ↦ ?_, fun i ↦ ?_⟩
  · have heq : ∑ k ∈ K, (Λ k).smulRight (v K k) = U.comp (V K).starProjection := by
      apply ContinuousLinearMap.ext_on hb.2.2.1
      rintro _ ⟨i, rfl⟩
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
      change ∑ k ∈ K, (Λ k (x i)) • v K k = v K i
      rw [Finset.sum_eq_single i]
      · rw [hb.1, one_smul]
      · intro k _ hki
        rw [hb.2.1 i k hki.symm, zero_smul]
      · intro hi
        rw [hoff K i hi, smul_zero]
    rw [heq]
    exact (U.opNorm_comp_le _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (V K).starProjection_norm_le).trans hU)
  · have mono : Monotone V := fun K L h ↦ Submodule.span_mono (Set.image_mono h)
    have hd : ⊤ ≤ (⨆ K, V K).topologicalClosure := by
      apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
      rw [Submodule.eq_bot_iff]
      intro w hw
      have hev : ContinuousLinearMap.apply ℂ ℂ w = 0 := by
        apply ContinuousLinearMap.ext_on hb.2.2.2
        rintro _ ⟨k, rfl⟩
        have hmem : u k ∈ V {k} := Submodule.subset_span ⟨k, Finset.mem_singleton_self k, rfl⟩
        change Λ k w = 0
        simpa only [u, InnerProductSpace.toDual_symm_apply] using
          (Submodule.mem_orthogonal _ _).mp hw _ ((le_iSup V {k}) hmem)
      exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
        (fun f ↦ (DFunLike.congr_fun hev f).trans (map_zero f).symm)
    exact U.continuous.continuousAt.tendsto.comp (Submodule.starProjection_tendsto_self V mono (x i) hd)

/-- A contraction attains the trace norm of a nuclear operator in the real trace pairing. -/
private theorem spectralLineConvolution_traceCauchy_norming {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : nuclearEndomorphisms H) :
    ∃ U : H →L[ℂ] H, ‖U‖ ≤ 1 ∧
      traceNorm T = (hilbertTrace ⟨U * T.val, mul_mem_nuclearEndomorphisms_left U T⟩).re := by
  let S := CFC.sqrt (T.val.adjoint * T.val)
  -- Pointwise norm identity as in AppC_LCTVS/Sec3a, norm_sqrt_adjoint_mul_apply.
  have hpos : 0 ≤ S := CFC.sqrt_nonneg (T.val.adjoint * T.val)
  have hS : S.adjoint = S := (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).isSelfAdjoint.adjoint_eq
  have hsq : S * S = T.val.adjoint * T.val :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      T.val.isPositive_adjoint_comp_self)
  have hn (w : H) : ‖S w‖ ≤ ‖T.val w‖ := by
    rw [S.apply_norm_eq_sqrt_inner_adjoint_right, T.val.apply_norm_eq_sqrt_inner_adjoint_right,
      hS, ← ContinuousLinearMap.mul_def, hsq, ContinuousLinearMap.mul_def]
  obtain ⟨U, hU, hUS⟩ := exists_contraction_comp_eq_of_norm_le T.val S hn
  refine ⟨U, hU, ?_⟩
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  have hs := Complex.reCLM.hasSum (summable_norm_hilbertDiagonal b (U * T.val)
    (mul_mem_nuclearEndomorphisms_left U T)).of_norm.hasSum
  apply (hasSum_traceNorm_diagonal b T).unique
  change HasSum _ (∑' i, inner ℂ (b i) ((U * T.val) (b i))).re
  simpa only [Complex.reCLM_apply, ContinuousLinearMap.mul_def U, hUS] using hs

/-- Testing the finite section against a left multiplier gives the scalar sum of its
jet functionals evaluated on the images of the biorthogonal vectors. -/
private theorem spectralLineConvolution_traceCauchy_pairing {H J Z : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (K : Finset Z)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    ∃ T : nuclearEndomorphisms H, T.val = U * spectralConvolutionFiniteSum A x Λ K N jet ∧
      hilbertTrace T = ∑ z ∈ K, ∑ m : Fin (N z), Λ (jet z m) (A (U (x (jet z m)))) := by
  let r (j : J) : nuclearEndomorphisms H :=
    ⟨((Λ j).comp A).smulRight (U (x j)), smulRight_mem_nuclearEndomorphisms _ _⟩
  refine ⟨∑ z ∈ K, ∑ m : Fin (N z), r (jet z m), ?_, ?_⟩
  · ext w
    simp [r, spectralConvolutionFiniteSum, sum_apply, ContinuousLinearMap.mul_def]
  · obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    simp only [← htr, map_sum]
    exact Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun m _ ↦
      (htr _).trans (hilbertTrace_smulRight _ _)

/-- A scalar estimate on each enlargement of one rectangle bounds its difference
from the anchor in trace norm. Two such bounds control arbitrary late rectangles. -/
private theorem spectralLineConvolution_traceCauchy_of_scalar_shell {H J Z : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [DecidableEq Z]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (box : ℕ × ℕ → Finset Z) (hbox : Monotone box) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J)
    (hshell : ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset J) (v : J → H),
      (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
      (∑ z ∈ box j \ box i, ∑ m : Fin (N z), Λ (jet z m) (A (v (jet z m)))).re ≤ ε) :
    SpectralRectanglesTraceCauchy (fun j ↦ spectralConvolutionFiniteSum A x Λ (box j) N jet) := by
  classical
  let B (K : Finset Z) := spectralConvolutionFiniteSum A x Λ K N jet
  have hmem (K : Finset Z) : B K ∈ nuclearEndomorphisms H :=
    (nuclearEndomorphisms H).sum_mem fun z _ ↦
      (nuclearEndomorphisms H).sum_mem fun m _ ↦ smulRight_mem_nuclearEndomorphisms _ _
  intro ε hε
  obtain ⟨i, hi⟩ := hshell (ε / 3) (by positivity)
  let D (j : ℕ × ℕ) : nuclearEndomorphisms H := ⟨B (box j \ box i), hmem _⟩
  have hD (j : ℕ × ℕ) (hj : i ≤ j) : (D j).val + B (box i) = B (box j) :=
    Finset.sum_sdiff (hbox hj)
  have hsmall (j : ℕ × ℕ) (hj : i ≤ j) : traceNorm (D j) ≤ ε / 3 := by
    obtain ⟨U, hU, hnorm⟩ := spectralLineConvolution_traceCauchy_norming (D j)
    obtain ⟨v, hoff, hV, hlim⟩ := spectralLineConvolution_traceCauchy_probes x Λ hb U hU
    obtain ⟨T, hT, htrace⟩ := spectralLineConvolution_traceCauchy_pairing U A x Λ (box j \ box i) N jet
    have hEq : (⟨U * (D j).val, mul_mem_nuclearEndomorphisms_left _ _⟩ : nuclearEndomorphisms H) = T :=
      Subtype.ext hT.symm
    rw [hnorm, hEq, htrace]
    apply le_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_finsetSum _ fun z _ ↦ tendsto_finsetSum _ fun m _ ↦
        ((Λ (jet z m)).continuous.comp A.continuous).continuousAt.tendsto.comp (hlim (jet z m))))
    exact fun K ↦ hi j hj K (v K) (hoff K) (hV K)
  refine ⟨i, fun j k hj hk ↦ ⟨D j - D k, ?_, ?_⟩⟩
  · change (D j).val - (D k).val = B (box j) - B (box k)
    rw [← hD j hj, ← hD k hk, add_sub_add_right_eq_sub]
  · let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    let core := traceNorm_normedSpaceCore (H := H)
    let : NormedAddCommGroup (nuclearEndomorphisms H) := NormedAddCommGroup.ofCore core
    let : SeminormedAddCommGroup (nuclearEndomorphisms H) :=
      (inferInstance : NormedAddCommGroup (nuclearEndomorphisms H)).toSeminormedAddCommGroup
    apply (norm_sub_le (D j) (D k)).trans_lt
    change traceNorm (D j) + traceNorm (D k) < ε
    linarith [hsmall j hj, hsmall k hk]

open Classical in
/-- Paper: Theorem 10.3.1.1(1), p. 448. For a finite family of vectors defining a
contraction by the jet functionals, the sum of the convolved evaluations on the added
zero blocks should have uniformly small real part. Vectors outside the rectangle also
enter the contraction bound. The finite Gram matrices of the jets and the vectors
determine that bound. Estimating the scalar sum subject to it would account for the
angles between nearby jets omitted in (10.3.1.18)–(23), pp. 451–452. -/
private theorem spectralLineConvolution_traceCauchy_scalar_shell
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice (F := F) χ)
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (Λ : SpectralLineJetIndex (F := F) χ a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) χ hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)) :
    let box (ij : ℕ × ℕ) := ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn
    let jet (z : Z(χ)) (m : Fin (N(χ, s, z))) : SpectralLineJetIndex (F := F) χ a s :=
      ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
    let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
    ∀ ε > (0 : ℝ), ∃ i, ∀ j ≥ i, ∀ (K : Finset (SpectralLineJetIndex (F := F) χ a s))
      (v : SpectralLineJetIndex (F := F) χ a s → Q(a, h₀, hs₀(hs))),
      (∀ k ∉ K, v k = 0) → ‖∑ k ∈ K, (Λ k).smulRight (v k)‖ ≤ 1 →
      (∑ z ∈ box j \ box i, ∑ m : Fin (N(χ, s, z)), Λ (jet z m) (A (v (jet z m)))).re ≤ ε := by
  sorry

/-- Paper: Theorem 10.3.1.1(1), p. 448. The rectangular sums have Cauchy tails in trace norm.
Gap: Trace-norm tails of the actual rectangles need an estimate allowing arbitrarily close zeros. -/
theorem spectralLineConvolution_traceCauchy (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → Q(a, h₀, hs₀(hs)))
    (Λ : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) (fun ω ↦ χ ω) hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2)) :
    let H := Q(a, h₀, hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a h₀ hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
    SpectralRectanglesTraceCauchy B := by
  classical
  intro H A B
  refine spectralLineConvolution_traceCauchy_of_scalar_shell A x Λ _hb
    (fun ij : ℕ × ℕ ↦ ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
    ?_ (fun z ↦ N(χ, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩) ?_
  · intro i j hij z hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp (Finset.mem_preimage.mp hz)
    exact Finset.mem_preimage.mpr (Finset.mem_product.mpr
      ⟨Finset.mem_Iic.mpr ((Finset.mem_Iic.mp h₁).trans hij.1),
       Finset.mem_Iic.mpr ((Finset.mem_Iic.mp h₂).trans hij.2)⟩)
  · exact spectralLineConvolution_traceCauchy_scalar_shell (F := F) a χ _hχ hs φ eχ e _he Λ _hj

/-- Paper: Theorem 10.3.1.1(1) and (10.3.1.1), p. 448. The rectangular
finite-rank sums over any enumeration converge to convolution in each Schatten class.
Deviation: The injections permit finite or empty character and zero sets. Use
the strict multiplicity cutoff and the jet realization of Theorem 10.2.1.1. -/
theorem spectralLineConvolution_schatten_tendsto (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → Q(a, h₀, hs₀(hs)))
    (Λ : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s → StrongDual ℂ Q(a, h₀, hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a h₀ hs₀(hs) (Λ j) =
      (spectralLineJet_memLp (F := F) (fun ω ↦ χ ω) hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let H := Q(a, h₀, hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a h₀ hs₀(hs) φ
    let S := schattenClass H H p hp
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2, m.val), m.isLt⟩)
    ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
      Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
        (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  let count (z : Z(χ)) := N(χ, s, z)
  let jet (z : Z(χ)) (m : Fin (count z)) : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s :=
    ⟨(z.val.1, z.val.2, m.val), m.isLt⟩
  let index (j : SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s) : (z : Z(χ)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1), SpectralLineJetIndex.order_pos j⟩, ⟨j.val.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ)) × Fin (count z)) ≃ SpectralLineJetIndex (F := F) (fun ω ↦ χ ω) a s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralConvolutionFiniteSum_limit_of_traceCauchy
    (spectralConvolution (F := F) a h₀ hs₀(hs) φ) x Λ e count jet
    _hb equiv.bijective p hp
    (spectralLineConvolution_traceCauchy (F := F) a χ _hχ hs φ eχ e _he x Λ _hb _hj)

/-- Number the norm-one characters and, within each row, the selected zeros. -/
private theorem spectralLineConvolution_nuclear_indices {Z : Type*}
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (row : Z → PontryaginDual C₁) (point : Z → ℂ)
    (hinj : Injective (fun z ↦ (row z, point z))) (hz : ∀ z, 0 < order(χ (row z), point z)) :
    ∃ (r : PontryaginDual C₁ ↪ ℕ) (e : Z ↪ ℕ × ℕ), ∀ z, (e z).1 = r (row z) := by
  have hK := IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let zeros (ω : PontryaginDual C₁) := {z : ℂ | 0 < order(χ ω, z)}
  have hc (ω) : (zeros ω).Countable := by
    obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec (χ ω)
    have hfinite : order(χ ω, (2 : ℂ)) ≠ ⊤ := by
      intro h
      have hp : 0 < order(χ ω, (2 : ℂ)) := by rw [h]; exact WithTop.coe_lt_top (0 : ℤ)
      have := completedHeckeL_continuation_zeros (χ ω) _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
      norm_num at this
    have hd : (zeros ω)ᶜ ∈ codiscrete ℂ := by
      filter_upwards [hL.meromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz'
      rcases hz'.2 with h | h
      · simp [zeros, h]
      · exact (hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
          isPreconnected_univ (mem_univ _) (mem_univ z) hfinite h).elim
    let : DiscreteTopology (zeros ω) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hd).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let : Countable (⋃ ω, zeros ω) := (Set.countable_iUnion hc).to_subtype
  obtain ⟨r⟩ := nonempty_embedding_nat (PontryaginDual C₁)
  obtain ⟨c⟩ := nonempty_embedding_nat (⋃ ω, zeros ω)
  let pt (z : Z) : ⋃ ω, zeros ω := ⟨point z, mem_iUnion.mpr ⟨row z, hz z⟩⟩
  refine ⟨r, ⟨fun z ↦ (r (row z), c (pt z)), ?_⟩, fun _ ↦ rfl⟩
  intro i j hij
  exact hinj (Prod.ext (r.injective (congrArg Prod.fst hij))
    (congrArg Subtype.val (c.injective (congrArg Prod.snd hij))))

/-- Paper: Theorem 10.3.1.1(2), p. 448. Convolution on the a-line spectral
quotient is trace class for each test. -/
theorem spectralLineConvolution_nuclear {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a h₀ hs₀(hs) φ) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  obtain ⟨_, x, Λ, hb, hj⟩ := spectralLineMarkushevichBasis (a := a) χ hχ hs
  obtain ⟨r, e, he⟩ := spectralLineConvolution_nuclear_indices χ
    (fun z : Z(χ) ↦ z.val.1) (fun z ↦ shift(a, z.val.2)) (by
      intro i j h
      have hrow := congrArg Prod.fst h
      exact Subtype.ext (Prod.ext hrow
        (by simpa using congrArg (fun p ↦ (p.2 : ℂ).im) h))) (fun z ↦ z.property)
  obtain ⟨hA, _⟩ := spectralLineConvolution_schatten_tendsto (F := F) a χ hχ hs φ
    r e he x Λ hb hj 1 le_rfl
  exact (mem_traceClassOperators_iff_isNuclearOperator _).mp hA

/-- A descended endomorphism has operator norm bounded by the ambient operator norm. -/
private theorem spectralConvolution_norm_le_of_quotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (S : Submodule ℂ E) (A : E →L[ℂ] E) (B : (E ⧸ S) →L[ℂ] (E ⧸ S))
    (h : ∀ x, B (S.mkQ x) = S.mkQ (A x)) : ‖B‖ ≤ ‖A‖ := by
  refine B.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨u, hu, hnorm⟩ := Submodule.Quotient.norm_mk_lt (S := S) x
    (div_pos hε (show 0 < ‖A‖ + 1 by positivity))
  calc
    ‖B x‖ = ‖S.mkQ (A u)‖ := by rw [← hu]; exact congrArg norm (h u)
    _ ≤ ‖A u‖ := Submodule.Quotient.norm_mk_le S _
    _ ≤ ‖A‖ * (‖x‖ + ε / (‖A‖ + 1)) :=
      (A.le_opNorm u).trans (mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg A))
    _ = ‖A‖ * ‖x‖ + ε * (‖A‖ / (‖A‖ + 1)) := by ring
    _ ≤ ‖A‖ * ‖x‖ + ε := by
      have hscale : ‖A‖ / (‖A‖ + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (le_add_of_nonneg_right zero_le_one)
      exact add_le_add_right (mul_le_of_le_one_right hε.le hscale) _

/-- The Hardy–Sobolev action is continuous in operator norm, and passing to
the quotient can only decrease the norm. -/
private theorem spectralConvolution_opNorm_continuous {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    Continuous (spectralConvolution (F := F) a hI hs) := by
  let A := (spectralConvolution_isLinear (F := F) a hI hs).mk' (spectralConvolution (F := F) a hI hs)
  let B (φ : BruhatCompactSupport C𝔽) : W(l, r, s) →L[ℂ] W(l, r, s) :=
    (testAction(l, r, s, hI, hs) φ : W(l, r, s) →L[ℂ] W(l, r, s))
  have htest : Continuous B := continuous_hardySobolevTestAction μ𝔽 m𝔽 l r s hI hs
  have hn (φ : BruhatCompactSupport C𝔽) : ‖A φ‖ ≤ ‖B φ‖ :=
    spectralConvolution_norm_le_of_quotient (Θ(a, hI, hs)) _ _
      (spectralConvolution_mkQ (F := F) a hI hs φ)
  have hB0 : B 0 = 0 := map_zero (testAction(l, r, s, hI, hs))
  change Continuous A
  apply continuous_of_tendsto_nhds_zero A
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ ↦ norm_nonneg _) hn ?_
  have hc : Tendsto (fun φ ↦ ‖B φ‖) (𝓝 0) (𝓝 ‖B 0‖) := htest.norm.continuousAt
  rwa [hB0, norm_zero] at hc

/-- The trace norm is a supremum of continuous finite sums of approximation numbers
on any operator-norm continuous family of trace-class operators. -/
private theorem spectralConvolution_traceNorm_lowerSemicontinuous {X H : Type*}
    [TopologicalSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : X → nuclearEndomorphisms H) (hT : Continuous (fun x ↦ (T x).val)) :
    LowerSemicontinuous (fun x ↦ traceNorm (T x)) := by
  let p (I : Finset ℕ) (x : X) := ∑ n ∈ I, approximationNumber (T x).val n
  have hbound (x : X) : BddAbove (range (fun I ↦ p I x)) :=
    ⟨traceNorm (T x), fun _ ⟨I, h⟩ ↦ h ▸
      spectralConvolutionFiniteSum_limit_of_traceCauchy_bound (T x) I⟩
  have hsum (x : X) : traceNorm (T x) = ⨆ I, p I x := by
    apply le_antisymm ?_ (ciSup_le fun I ↦ spectralConvolutionFiniteSum_limit_of_traceCauchy_bound (T x) I)
    have he := schattenNorm_one_eq_traceNorm (T x)
    simp only [schattenNorm, Real.rpow_one, div_one] at he
    rw [← he]
    exact Real.tsum_le_of_sum_le (spectralConvolutionFiniteSum_limit_of_traceCauchy_nonneg _)
      (fun I ↦ le_ciSup (hbound x) I)
  simp_rw [hsum]
  refine lowerSemicontinuous_ciSup hbound fun I ↦ Continuous.lowerSemicontinuous ?_
  apply continuous_finsetSum _ fun n _ ↦ ?_
  have hcont : Continuous (fun D : H →L[ℂ] H ↦ approximationNumber D n) :=
    (LipschitzWith.of_dist_le' (K := 1) (fun D E ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, one_mul] using abs_approximationNumber_sub_le D E n)).continuous
  exact hcont.comp hT

/-- A lower semicontinuous seminorm restricts continuously to each Fréchet stage of a
strict LF-space, whose topology is final locally convex. This is the Fréchet-stage
argument of `IsLFSpace.barrelled` from Appendix C. -/
private theorem spectralConvolution_continuous_of_lsc_seminorm {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (hE : IsStrictLFSpace E) (p : Seminorm ℂ E)
    (hp : LowerSemicontinuous p) : Continuous p := by
  obtain ⟨_, S, _, hS, _, htop⟩ := hE
  have hP : WithSeminorms
      (Subtype.val : {q : Seminorm ℂ E // ∀ k, Continuous (q ∘ (S k).subtype)} → Seminorm ℂ E) :=
    ⟨htop⟩
  apply hP.continuous_seminorm (i := ⟨p, ?_⟩)
  intro k
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hS k
  let : UniformSpace (S k) := IsTopologicalAddGroup.rightUniformSpace (S k)
  let : IsUniformAddGroup (S k) := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (S k) := hcomplete
  let : ContinuousSMul ℂ (S k) := PolynormableSpace.continuousSMul ℂ (S k)
  have : (uniformity (S k)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero (S k)]
    infer_instance
  have : BaireSpace (S k) := by
    let := UniformSpace.metricSpace (S k)
    infer_instance
  exact (p.comp (S k).subtype).continuous_of_lowerSemicontinuous (hp.comp continuous_subtype_val)

/-- A linear operator-norm continuous family of nuclear endomorphisms has a
trace-norm continuous lift when its domain is a strict LF-space. -/
private theorem spectralConvolution_traceNorm_lift {E H : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hE : IsStrictLFSpace E) (A : E →ₗ[ℂ] (H →L[ℂ] H)) (hA : Continuous A)
    (hn : ∀ x, IsNuclearOperator (A x)) :
    ∃ T : E →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ x, (T x).val = A x) ∧ Tendsto (fun x ↦ traceNorm (T x)) (𝓝 0) (𝓝 0) := by
  let T := A.codRestrict (nuclearEndomorphisms H) hn
  refine ⟨T, fun _ ↦ rfl, ?_⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let hcore := traceNorm_normedSpaceCore (H := H)
  let p : Seminorm ℂ E :=
    { toFun := fun x ↦ traceNorm (T x)
      map_zero' := by rw [map_zero]; exact (hcore.norm_eq_zero_iff _).mpr rfl
      add_le' := fun x y ↦ by rw [map_add]; exact hcore.norm_triangle _ _
      neg' := fun x ↦ by
        rw [map_neg, ← neg_one_smul ℂ (T x)]
        have h := hcore.norm_smul (-1 : ℂ) (T x)
        simpa only [norm_neg, norm_one, one_mul] using h
      smul' := fun c x ↦ by rw [map_smul]; exact hcore.norm_smul _ _ }
  have hp : LowerSemicontinuous p := spectralConvolution_traceNorm_lowerSemicontinuous T hA
  have hc := spectralConvolution_continuous_of_lsc_seminorm hE p hp
  change Tendsto p (𝓝 0) (𝓝 0)
  exact hc.tendsto' 0 0 p.map_zero'

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.2), p. 448. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralLineConvolution_traceNorm_continuous {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a h₀ hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by
  intro H
  let A : BruhatCompactSupport C𝔽 →ₗ[ℂ] (H →L[ℂ] H) :=
    (spectralConvolution_isLinear (F := F) a h₀ hs₀(hs)).mk'
      (spectralConvolution (F := F) a h₀ hs₀(hs))
  exact spectralConvolution_traceNorm_lift bruhatCompactSupport_strictLF A
    (spectralConvolution_opNorm_continuous (F := F) a h₀ hs₀(hs))
    (spectralLineConvolution_nuclear (F := F) a hs)

/-- Paper: Theorem 10.3.1.1(2), p. 448. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralLineConvolution_trace_distribution {s : ℝ} (hs : 1 < s) :
    let H := Q(a, h₀, hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a h₀ hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  exact traceDistribution (X := BruhatCompactSupport C𝔽) (H := Q(a, h₀, hs₀(hs)))
    (spectralConvolution (F := F) a h₀ hs₀(hs))
    (spectralLineConvolution_traceNorm_continuous (F := F) a hs)

-- TODO(paper-gap): The L¹ comparison after (10.3.1.26) supplies no
-- sampling estimate at zero ordinates, and the rapid-decay claim uses arbitrary numbering.

section StripTraceFormula

open InnerProductSpace
open scoped InnerProductSpace

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

section InvariantBlockTrace

/-- Along a countably generated filter, strong convergence to the identity suffices for
convergence of the traces of left products with a fixed nuclear operator. -/
private theorem stripTrace_tendsto_strong {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {l : Filter I} [l.IsCountablyGenerated]
    (P : I → H →L[ℂ] H) (hP : ∀ y, Tendsto (fun i ↦ P i y) l (𝓝 y))
    (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ hilbertTrace ⟨P i * T.val, mul_mem_nuclearEndomorphisms_left (P i) T⟩)
      l (𝓝 (hilbertTrace T)) := by
  apply tendsto_iff_seq_tendsto.2
  intro u hu
  let A : traceClassOperators H H := ⟨T.val, (mem_traceClassOperators_iff_isNuclearOperator _).2 T.property⟩
  let B (n : ℕ) : nuclearEndomorphisms H :=
    ⟨P (u n) * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩
  obtain ⟨hm, hI, hlim⟩ := tendsto_schattenNorm_comp_left A (P ∘ u) (ContinuousLinearMap.id ℂ H)
    (fun y ↦ (hP y).comp hu)
  have hn : Tendsto (fun n ↦ traceNorm (B n - T)) atTop (𝓝 0) := by
    refine hlim.congr fun n ↦ ?_
    rw [← schattenNorm_one_eq_traceNorm]
    congr 1
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun n ↦ ‖hilbertTrace (B n) - hilbertTrace T‖) atTop (𝓝 0)
  have hdiff (n : ℕ) : hilbertTrace (B n) - hilbertTrace T = hilbertTrace (B n - T) :=
    ((congrArg₂ (· - ·) (htr (B n)).symm (htr T).symm).trans (tr.map_sub _ _).symm).trans (htr _)
  simp only [hdiff]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_hilbertTrace_le (B n - T)) hn

/-- Finite independent moment functionals have biorthogonal vectors in their Riesz span. -/
private theorem stripDualTrace_finiteCoordinates {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I] [DecidableEq I]
    (u : I → H) (hu : LinearIndependent ℂ u) :
    let V := Submodule.span ℂ (range u)
    let _ : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (finite_range u)
    ∃ y : I → H, (∀ i j, ⟪u j, y i⟫_ℂ = if i = j then 1 else 0) ∧
      ∀ v, V.starProjection v = ∑ i, ⟪u i, v⟫_ℂ • y i := by
  classical
  intro V hdim
  let ev : V →ₗ[ℂ] I → ℂ := LinearMap.pi fun i ↦ (innerSL ℂ (u i)).toLinearMap.comp V.subtype
  have hi : Injective ev := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro v hv
    have vanish (i : I) : ⟪u i, (v : H)⟫_ℂ = 0 := congrFun (LinearMap.mem_ker.mp hv) i
    have hV : V ≤ (innerSL ℂ (v : H)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact inner_eq_zero_symm.mp (vanish i)
    exact Subtype.ext (inner_self_eq_zero.mp (hV v.property))
  have hs : Surjective ev := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℂ V = Module.finrank ℂ (I → ℂ) from
      (finrank_span_eq_card hu).trans (Module.finrank_fintype_fun_eq_card ℂ).symm)).mp hi
  let e := LinearEquiv.ofBijective ev ⟨hi, hs⟩
  let b := (Pi.basisFun ℂ I).map e.symm
  refine ⟨fun i ↦ (b i : H), fun i j ↦ ?_, fun v ↦ ?_⟩
  · change e (b i) j = _
    simp [b, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  · let w : V := ⟨V.starProjection v, V.starProjection_apply_mem v⟩
    have hc (i : I) : b.repr w i = ⟪u i, v⟫_ℂ := by
      change (Pi.basisFun ℂ I).repr (e w) i = _
      rw [Pi.basisFun_repr]
      change ⟪u i, V.starProjection v⟫_ℂ = _
      rw [← V.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr
        (show u i ∈ V from Submodule.subset_span (mem_range_self i))]
    have he := congrArg (fun z : V ↦ (z : H)) (b.sum_repr w).symm
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hc] using he

/-- A total family of independent moment functionals computes a nuclear trace if the
operator acts diagonally modulo the earlier moments of each finite block. -/
private theorem stripDualTrace_hasSum {H Z : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Countable Z] (N : Z → ℕ)
    (u : (z : Z) → Fin (N z) → H)
    (hu : LinearIndependent ℂ (fun i : (z : Z) × Fin (N z) ↦ u i.1 i.2))
    (hsep : ∀ v : H, (∀ z m, ⟪u z m, v⟫_ℂ = 0) → v = 0)
    (T : nuclearEndomorphisms H) (t : Z → ℂ)
    (hflag : ∀ z m v, (∀ k : Fin (N z), k < m → ⟪u z k, v⟫_ℂ = 0) →
      ⟪u z m, T.val v⟫_ℂ = t z * ⟪u z m, v⟫_ℂ) :
    HasSum (fun z ↦ (N z : ℂ) * t z) (hilbertTrace T) := by
  classical
  let I (K : Finset Z) := (z : ↥K) × Fin (N z.val)
  let b (K : Finset Z) (i : I K) := u i.1.val i.2
  let V (K : Finset Z) := Submodule.span ℂ (range (b K))
  let fi (K : Finset Z) : Fintype (I K) := inferInstanceAs (Fintype ((z : ↥K) × Fin (N z.val)))
  let dim (K : Finset Z) : FiniteDimensional ℂ (V K) := FiniteDimensional.span_of_finite ℂ (finite_range (b K))
  let P (K : Finset Z) := (V K).starProjection
  have mono : Monotone V := by
    intro K L h
    apply Submodule.span_mono
    rintro _ ⟨⟨z, m⟩, rfl⟩
    exact ⟨⟨⟨z.val, h z.property⟩, m⟩, rfl⟩
  have hd : ⊤ ≤ (⨆ K, V K).topologicalClosure := by
    apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro v hv
    apply hsep
    intro z m
    have hmem : u z m ∈ V {z} :=
      Submodule.subset_span (show b {z} ⟨⟨z, Finset.mem_singleton_self z⟩, m⟩ ∈ range (b {z}) from mem_range_self _)
    exact (Submodule.mem_orthogonal _ _).mp hv _ ((le_iSup V {z}) hmem)
  have hsot (v : H) := Submodule.starProjection_tendsto_self V mono v hd
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  have hfin (K : Finset Z) :
      hilbertTrace ⟨P K * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩ =
        ∑ z ∈ K, (N z : ℂ) * t z := by
    have hi : Injective (fun i : I K ↦ (⟨i.1.val, i.2⟩ : (z : Z) × Fin (N z))) := by
      rintro ⟨⟨z, hz⟩, m⟩ ⟨⟨w, hw⟩, n⟩ h
      obtain ⟨rfl, h⟩ := Sigma.mk.inj h
      cases eq_of_heq h
      rfl
    obtain ⟨y, hy, hP⟩ := stripDualTrace_finiteCoordinates (b K) (hu.comp _ hi)
    let r (i : I K) : nuclearEndomorphisms H :=
      ⟨((innerSL ℂ (b K i)).comp T.val).smulRight (y i), smulRight_mem_nuclearEndomorphisms _ _⟩
    have heq : (⟨P K * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩ : nuclearEndomorphisms H) =
        ∑ i, r i := by
      apply Subtype.ext
      ext v
      simpa [P, V, r, ContinuousLinearMap.mul_def, Submodule.coe_sum] using hP (T.val v)
    rw [heq, ← htr, map_sum]
    calc
      _ = ∑ i : I K, t i.1.val := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [htr, hilbertTrace_smulRight]
        change ⟪u i.1.val i.2, T.val (y i)⟫_ℂ = _
        have hlower (k : Fin (N i.1.val)) (hk : k < i.2) : ⟪u i.1.val k, y i⟫_ℂ = 0 := by
          have hne : i ≠ (⟨i.1, k⟩ : I K) := by
            intro h
            exact hk.ne (eq_of_heq (Sigma.mk.inj h.symm).2)
          exact (hy i ⟨i.1, k⟩).trans (ite_eq_right hne)
        rw [hflag i.1.val i.2 _ hlower]
        have hone : ⟪u i.1.val i.2, y i⟫_ℂ = 1 := (hy i i).trans (ite_eq_left rfl)
        rw [hone, mul_one]
      _ = _ := by
        change (∑ i : (z : ↥K) × Fin (N z.val), t i.1.val) = _
        rw [Fintype.sum_sigma]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact Finset.sum_attach K (fun z ↦ (N z : ℂ) * t z)
  exact (stripTrace_tendsto_strong P hsot T).congr hfin

end InvariantBlockTrace

section StripConvolutionCoefficients

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

local notation "logNorm" => (logIdeleClassNorm F)
local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ a α s

/-- A quotient jet functional evaluates on a representative by its explicit Haar moment. -/
private theorem spectralStripConvolution_jet_eval
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (j : SpectralStripJetIndex χ a α s) (f : StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hf : D f = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j))) (v : W(-α, α, s)) :
    Integrable (fun y ↦ v y * raw(χ, j) y) μ𝔽 ∧
      f ((Θ(a, hStrip(hα), hs₀(hs))).mkQL v) = ∫ y, v y * raw(χ, j) y ∂μ𝔽 := by
  let w (g : C𝔽) := intervalSobolevDensity (-α) α s (logNorm g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity (-α) α s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact hD.measurable.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log)
  have habs : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hae : (D f : C𝔽 → ℂ) =ᵐ[μ𝔽] raw(χ, j) := by
    rw [hf]
    exact habs.ae_le (MemLp.coeFn_toLp _)
  have he := spectralSobolevPairing_dual (hStrip(hα)) hs₀(hs) (f.comp ((Θ(a, hStrip(hα), hs₀(hs))).mkQL)) v
  change Integrable (fun y ↦ v y * D f y) μ𝔽 ∧
      f ((Θ(a, hStrip(hα), hs₀(hs))).mkQL v) = ∫ y, v y * D f y ∂μ𝔽 at he
  have hEq := hae.mono fun y hy ↦ congrArg (v y * ·) hy
  exact ⟨he.1.congr hEq, he.2.trans (integral_congr_ae hEq)⟩

/-- If the lower moments vanish, translation multiplies the top moment by the norm twist. -/
private theorem spectralStripConvolution_jet_translate (η : PontryaginDual C𝔽) (b t : ℝ)
    (m : ℕ) (v : W(-α, α, s))
    (hint : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet η b t i x) μ𝔽)
    (hzero : ∀ i < m, ∫ x, v x * spectralZeroJet η b t i x ∂μ𝔽 = 0) (g : C𝔽) :
    let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)
    ∫ y, τ g v y * spectralZeroJet η b t m y ∂μ𝔽 =
      ideleClassNormTwist η (shift(b, t)) g * ∫ y, v y * spectralZeroJet η b t m y ∂μ𝔽 := by
  intro τ
  let T := ideleClassNormTwist η ((b : ℂ) + (t : ℂ) * Complex.I)
  let L (y : C𝔽) : ℂ := logNorm y
  let c (i : ℕ) := T g * L g ^ (m - i) * (m.choose i : ℂ)
  have hlog (y : C𝔽) : L (g * y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add, add_comm]
  have hsum (y : C𝔽) : v y * spectralZeroJet η b t m (g * y) =
      ∑ i ∈ Finset.range (m + 1), c i * (v y * spectralZeroJet η b t i y) := by
    change v y * (T (g * y) * L (g * y) ^ m) = _
    rw [map_mul, hlog, add_pow]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change v y * (T g * T y * (L y ^ i * L g ^ (m - i) * (m.choose i : ℂ))) =
      (T g * L g ^ (m - i) * (m.choose i : ℂ)) * (v y * (T y * L y ^ i))
    ring
  let J := spectralZeroJet η b t m
  let H (y : C𝔽) := v (g⁻¹ * y) * J y
  calc
    _ = ∫ y, H y ∂μ𝔽 := integral_congr_ae
      ((hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) g v).mono
        fun y hy ↦ congrArg (· * J y) hy)
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, v y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = _ := by
      simp_rw [show ∀ y, v y * J (g * y) = _ from hsum]
      rw [integral_finsetSum _ fun i hi ↦ (hint i (Finset.mem_range_succ_iff.mp hi)).const_mul (c i)]
      simp_rw [integral_const_mul]
      rw [Finset.sum_eq_single_of_mem m (Finset.mem_range_succ_iff.mpr le_rfl)]
      · simp [c, T]
      · intro i hi hne
        rw [hzero i (lt_of_le_of_ne (Finset.mem_range_succ_iff.mp hi) hne), mul_zero]

/-- On the common kernel of all lower moments at this zero, the selected jet coordinate
of the convolution is the Mellin value times the same coordinate of the input. -/
private theorem spectralStripConvolution_jet_top
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (z : Z(χ, α)) (m : Fin (N(χ, α, s, z)))
    (u : Q(a, hStrip(hα), hs₀(hs)))
    (hlower : ∀ k : Fin (N(χ, α, s, z)), k < m → f (jet(z, k)) u = 0) :
    f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ u) =
      M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2)) * f (jet(z, m)) u := by
  let θ := globalThetaSobolev F a (hStrip(hα)) hs₀(hs)
  obtain ⟨v, hv⟩ := θ.mkQ_surjective u
  let J (i : ℕ) := spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i
  let j : J(χ) := jet(z, m)
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)
  let ℓ := (f j).comp θ.mkQL
  let η := ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2))
  have heval (j : J(χ)) (w : W(-α, α, s)) :=
    spectralStripConvolution_jet_eval (a := a) hα hs χ j (f j) (hj j) w
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun y ↦ v y * J i y) μ𝔽 := by
    let k : Fin (N(χ, α, s, z)) := ⟨i, hi.trans_lt m.isLt⟩
    exact (heval (jet(z, k)) v).1
  have hzero (i : ℕ) (hi : i < m.val) : ∫ y, v y * J i y ∂μ𝔽 = 0 := by
    let k : Fin (N(χ, α, s, z)) := ⟨i, hi.trans m.isLt⟩
    refine (heval (jet(z, k)) v).2.symm.trans ?_
    change f (jet(z, k)) (θ.mkQ v) = 0
    exact (congrArg (f (jet(z, k))) hv).trans (hlower k hi)
  have htop : ∫ y, v y * J m.val y ∂μ𝔽 = f j u :=
    (heval j v).2.symm.trans (congrArg (f j) hv)
  have hτ (g : C𝔽) : ℓ (τ g v) = η g * f j u :=
    (heval j (τ g v)).2.trans ((spectralStripConvolution_jet_translate hα hs
      (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hint hzero g).trans (congrArg (η g * ·) htop))
  have hP := bruhatRegularizedAction_apply μ𝔽 τ
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs)).choose_spec.2 φ v
  have he := congrArg (fun p : PettisWeakCompletion W(-α, α, s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(-α, α, s)) from p) ℓ) hP.2
  change ℓ (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) φ v) =
    ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 at he
  have hM := (spectralConvolution_mellin_integrable φ (χ z.val.1) (shift(z.val.2.1, z.val.2.2))).2
  calc
    _ = ℓ (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) φ v) :=
      (congrArg (fun w ↦ f j (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ w)) hv.symm).trans
        (congrArg (f j) (spectralConvolution_mkQ a (hStrip(hα)) hs₀(hs) φ v))
    _ = ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 := he
    _ = ∫ g, (φ.val g * η g) * f j u ∂μ𝔽 := integral_congr_ae (.of_forall fun g ↦ by
      exact (map_smul ℓ _ _).trans ((congrArg (φ.val g * ·) (hτ g)).trans (mul_assoc _ _ _).symm))
    _ = _ := (integral_mul_const _ _).trans (congrArg (· * f j u) hM.symm)

/-- Paper: (10.3.1.17), p. 450. Evaluation at a retained zero is an eigenfunctional
for the quotient convolution. The zeroth coordinate has no lower jet terms. -/
theorem spectralStripConvolution_zeroJet
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) (z : Z(χ, α)) (h : 0 < N(χ, α, s, z))
    (u : Q(a, hStrip(hα), hs₀(hs))) :
    let m : Fin (N(χ, α, s, z)) := ⟨0,h⟩
    f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ u) =
      M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2)) * f (jet(z, m)) u :=
  spectralStripConvolution_jet_top a hα hs χ f hj φ z ⟨0,h⟩ u
    (fun k hk ↦ (Nat.not_lt_zero k.val hk).elim)

/-- Paper: (10.3.1.17), p. 450, and Theorem 10.3.2.1(2), p. 454. In a basis realizing the strip jets, the
convolution matrix has no coefficients between distinct zeros. Each diagonal coefficient
is the Mellin value at the unshifted exponent of its zero. -/
theorem spectralStripConvolution_jetCoefficients
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : J(χ) → Q(a, hStrip(hα), hs₀(hs))) (f : J(χ) → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x f)
    (hj : ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (raw(χ, j)))
    (φ : BruhatCompactSupport C𝔽) :
    (∀ (z z' : Z(χ, α)), z ≠ z' → ∀ (m : Fin (N(χ, α, s, z))) (n : Fin (N(χ, α, s, z'))),
      f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ (x (jet(z', n)))) = 0) ∧
    (∀ (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))),
      f (jet(z, m)) (spectralConvolution (F := F) a (hStrip(hα)) hs₀(hs) φ (x (jet(z, m)))) =
        M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))) := by
  have coeff := spectralStripConvolution_jet_top a hα hs χ f hj φ
  constructor
  · intro z z' hzz m n
    have hindex (k : Fin (N(χ, α, s, z))) : (jet(z', n) : J(χ)) ≠ jet(z, k) := by
      intro h
      exact hzz (Subtype.ext (congrArg (fun u : J(χ) ↦ (u.val.1, u.val.2.1, u.val.2.2.1)) h).symm)
    exact (coeff z m _ (fun k _ ↦ hb.2.1 _ _ (hindex k))).trans
      ((congrArg (_ * ·) (hb.2.1 _ _ (hindex m))).trans (mul_zero _))
  · intro z m
    have hindex (k : Fin (N(χ, α, s, z))) (hk : k < m) : (jet(z, m) : J(χ)) ≠ jet(z, k) := by
      intro h
      exact (ne_of_lt hk) (Fin.ext (congrArg (fun u : J(χ) ↦ u.val.2.2.2) h).symm)
    exact (coeff z m _ (fun k hk ↦ hb.2.1 _ _ (hindex k hk))).trans
      ((congrArg (_ * ·) (hb.1 _)).trans (mul_one _))

end StripConvolutionCoefficients

/-- Linear independence passes to the conjugate Riesz representatives. -/
private theorem stripDualTrace_riesz_independent {H J : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (f : J → StrongDual ℂ H)
    (hf : LinearIndependent ℂ f) :
    LinearIndependent ℂ (fun j ↦ (toDual ℂ H).symm (f j)) := by
  apply linearIndependent_iff'.mpr
  intro s c h i hi
  have h' := congrArg (toDual ℂ H) h
  simp only [map_sum, map_smulₛₗ, LinearIsometryEquiv.apply_symm_apply, map_zero] at h'
  have hz := linearIndependent_iff'.mp hf s _ h' i hi
  simpa using hz

/-- The common-kernel identity lifts the strip moments to a separating family on the quotient. -/
private theorem stripDualTrace_separating (a : ℝ) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let H := Q(a, hStrip(hα), hs)
    let D := spectralSobolevDualEmbedding F a (hStrip(hα)) hs
    let raw (j : J) := spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
    (∀ v, v ∈ Θ(a, hStrip(hα), hs) ↔
      ∀ j, spectralSobolevPairing v ((spectralStripJet_memLp χ hα hs j).toLp (raw j)) = 0) →
    ∃ f : J → StrongDual ℂ H,
      (∀ j, D (f j) = (spectralStripJet_memLp χ hα hs j).toLp (raw j)) ∧
      ∀ v : H, (∀ j, f j v = 0) → v = 0 := by
  classical
  intro J H D raw hK
  let θ := Θ(a, hStrip(hα), hs)
  let w (j : J) := (spectralStripJet_memLp χ hα hs j).toLp (raw j)
  have hr (j : J) : w j ∈ Set.range D := by
    rw [(spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip(hα)) hs).2]
    exact fun v hv ↦ (hK v).mp hv j
  choose f hf using hr
  refine ⟨f, hf, ?_⟩
  intro v hv
  obtain ⟨y, hy⟩ := θ.mkQ_surjective v
  rw [← hy]
  apply (spectralSobolevQuotient_eq_zero a (hStrip(hα)) hs y).mpr
  apply (hK y).mpr
  intro j
  have hp : f j (θ.mkQ y) = spectralSobolevPairing y (D (f j)) :=
    (spectralSobolevPairing_dual (hStrip(hα)) hs ((f j).comp θ.mkQL) y).2
  rw [hy, hv, hf] at hp
  exact hp.symm

/-- Paper: Theorem 10.3.2.1(2), p. 454. For a given nuclear convolution the
strip trace formula follows if the surviving moments identify the theta closure
at this width and Sobolev exponent.
Deviation: This conditional form isolates the common-kernel assertion of p. 446
and uses the strict boundary multiplicity. -/
theorem spectralStripConvolution_trace_of_commonKernel (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (hk : ∀ v, v ∈ Θ(a, hStrip(hα), hs₀(hs)) ↔ ∀ j : SpectralStripJetIndex χ a α s,
      spectralSobolevPairing v ((spectralStripJet_memLp χ hα hs₀(hs) j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) = 0) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let term (z : Z(χ, α)) := (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term T hT
  classical
  obtain ⟨_, e, _⟩ := spectralLineConvolution_nuclear_indices χ
    (fun z : Z(χ, α) ↦ z.val.1) (fun z ↦ shift(a + z.val.2.1, z.val.2.2)) (by
      intro i j h
      have hrow := congrArg Prod.fst h
      have hre := congrArg (fun p ↦ (p.2 : ℂ).re) h
      have him := congrArg (fun p ↦ (p.2 : ℂ).im) h
      exact Subtype.ext (Prod.ext hrow
        (Prod.ext (by simpa using hre) (by simpa using him)))) (fun z ↦ z.property.2)
  let : Countable (Z(χ, α)) := e.injective.countable
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨f, hf, hsep⟩ := stripDualTrace_separating a χ hα hs₀(hs) hk
  let D := spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
  have hli : LinearIndependent ℂ f := LinearIndependent.of_comp D (by
    have eqw : D ∘ f = _ := funext hf
    rw [eqw]
    exact spectralStripJet_toLp_linearIndependent χ _hχ a hα hs₀(hs))
  let u (z : Z(χ, α)) (m : Fin (count z)) := (toDual ℂ H).symm (f (jet z m))
  have hu : LinearIndependent ℂ (fun i : (z : Z(χ, α)) × Fin (count z) ↦ u i.1 i.2) :=
    (stripDualTrace_riesz_independent f hli).comp equiv equiv.injective
  have heval (z : Z(χ, α)) (m : Fin (count z)) (v : H) :
      ⟪u z m, v⟫_ℂ = f (jet z m) v := toDual_symm_apply
  have htotal (v : H) (hv : ∀ z m, ⟪u z m, v⟫_ℂ = 0) : v = 0 := by
    apply hsep v
    intro i
    obtain ⟨⟨z, m⟩, rfl⟩ := equiv.surjective i
    exact (heval z m v).symm.trans (hv z m)
  have ht : HasSum term (hilbertTrace T) := stripDualTrace_hasSum count u hu htotal T
    (fun z ↦ M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))) (by
      intro z m v hlow
      simp only [heval] at hlow ⊢
      rw [hT]
      exact spectralStripConvolution_jet_top a hα hs χ f hf φ z m v hlow)
  exact ⟨ht.summable.norm, ht⟩

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.3)–(10.3.2.4), p. 454. The trace
is the absolutely convergent sum of the Mellin values at the strip zeros with
full interior multiplicities and truncated boundary multiplicities.
Deviation: Use the strict boundary cutoff and positive meromorphic order.
The dependent double sum is expressed as one family. -/
theorem spectralStripConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω)) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let term (z : Z(χ, α)) := (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  exact spectralStripConvolution_trace_of_commonKernel a χ _hχ hα hs φ
    (spectralStripJet_commonKernel (a := a) χ _hχ hα hs₀(hs))

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.3)–(10.3.1.4), p. 448. The
trace of convolution is the absolutely convergent sum of the Mellin values at
the line zeros weighted by their surviving multiplicities.
Deviation: Apply the strict cutoff of §10.2 and use positive meromorphic
order to exclude poles. The dependent double sum is expressed as one family. -/
theorem spectralLineConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs₀(hs))
    let term (z : Z(χ)) := (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralConvolution (F := F) a h₀ hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  let L := Z(χ)
  let term (z : L) := (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))
  let claim (l : ℝ) (hl : l ≤ 0) := ∀ T : nuclearEndomorphisms Q(a, hl, hs₀(hs)),
    T.val = spectralConvolution (F := F) a hl hs₀(hs) φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace T)
  have transport (l : ℝ) (hl : l ≤ 0) (h : l = 0) : claim l hl → claim 0 le_rfl := by
    subst l
    exact id
  apply transport (-0) (hStrip(le_refl (0 : ℝ))) neg_zero
  intro T hT
  let Z := Z(χ, 0)
  have hoff (z : Z) : z.val.2.1 = 0 := by simpa using z.property.1
  let e : L ≃ Z :=
    { toFun := fun z ↦ ⟨(z.val.1, 0, z.val.2), by simp, by simpa only [add_zero] using z.property⟩
      invFun := fun z ↦ ⟨(z.val.1, z.val.2.2), by simpa only [hoff z, add_zero] using z.property.2⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun z ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hoff z).symm rfl)) }
  let u (z : Z) := (N(χ, 0, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
  have hsum : HasSum u (hilbertTrace T) :=
    (spectralStripConvolution_trace (F := F) a χ _hχ le_rfl hs φ T hT).2
  have hterm (z : L) : u (e z) = term z := by
    simp only [u, e, Equiv.coe_fn_mk, term, add_zero, spectralStripMultiplicity_boundary
      (le_refl (0 : ℝ)) (Or.inr rfl)]
  have h := (e.hasSum_iff.mpr hsum).congr_fun fun z ↦ (hterm z).symm
  exact ⟨h.summable.norm, h⟩

end StripTraceFormula

/-- Paper: Theorem 10.3.1.1(3), p. 449. The singular values decay faster than every inverse power.
Deviation: Assume trace class for all tests. Factor the homogeneous radial profile into
finite sums of iterated convolutions of smooth compactly supported functions on ℝ.
The approximation-number product inequality then gives arbitrary polynomial decay. -/
theorem spectralLineIsotypeConvolution_rapid_approximationNumbers
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (_htrace : ∀ ψ : BruhatCompactSupport C𝔽,
      IsNuclearOperator (spectralConvolution (F := F) a h₀ hs₀(hs) ψ)) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by
  exact spectralApprox_isotype_rapid (F := F) a h₀ hs₀(hs) ω φ _hφ _htrace

/-- Paper: Theorem 10.3.1.1(3), p. 449. Convolution by a homogeneous
test acts by a strongly nuclear operator on the corresponding quotient isotype.
Deviation: Use the left-translation eigencharacter ω. -/
theorem spectralLineIsotypeConvolution_stronglyNuclear
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    IsStronglyNuclearBanachOperator (E := H) (G := H)
      (spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ) := by
  exact isStronglyNuclearBanachOperator_of_rapid_approximationNumbers _
    (spectralLineIsotypeConvolution_rapid_approximationNumbers (F := F) a hs ω φ _hφ
      (spectralLineConvolution_nuclear (F := F) a hs))

/-- Cyclicity identifies the trace with its restriction when the range lies in an isometric copy. -/
private theorem spectralIsotype_trace_of_range {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [PolynormableSpace ℂ H] [PolynormableSpace ℂ K]
    (A : nuclearEndomorphisms H) (D : nuclearEndomorphisms K)
    (J : K →L[ℂ] H) (P : H →L[ℂ] K) (hPJ : LeftInverse P J)
    (hr : ∀ x, A.val x ∈ range J) (hJ : ∀ y, A.val (J y) = J (D.val y)) :
    hilbertTrace A = hilbertTrace D := by
  let B := P.comp A.val
  have hB : IsNuclearOperator B := by
    obtain ⟨c, Λ, v, hc, hΛ, hv, hsum⟩ :=
      (isNuclearOperator_iff_isBanachNuclear A.val).mp A.property
    refine (isNuclearOperator_iff_isBanachNuclear B).mpr
      ⟨c, Λ, P ∘ v, hc, hΛ, (P.continuous.tendsto' 0 0 (map_zero P)).comp hv, fun x ↦ ?_⟩
    simpa only [B, Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul]
      using P.hasSum (hsum x)
  have hJB : J.comp B = A.val := by
    ext x
    obtain ⟨y, hy⟩ := hr x
    change J (P (A.val x)) = A.val x
    rw [← hy, hPJ y]
  have hBJ : B.comp J = D.val := by
    ext y
    exact (congrArg P (hJ y)).trans (hPJ _)
  have hn := isNuclearOperator_factor_comps J hPJ.injective B hB
  calc
    hilbertTrace A = hilbertTrace ⟨J.comp B, hn.2⟩ :=
      congrArg (hilbertTrace (H := H)) (Subtype.ext hJB.symm)
    _ = hilbertTrace ⟨B.comp J, hn.1⟩ := by
      rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
      exact (nuclearTrace_factor_comps (hilbert_approximationProperty (H := K))
        (hilbert_approximationProperty (H := H)) J hPJ.injective B hB).symm
    _ = hilbertTrace D := congrArg (hilbertTrace (H := K)) (Subtype.ext hBJ)

/-- Check range containment and intertwining on quotient representatives before comparing traces. -/
private theorem spectralIsotype_trace_representatives {H K V W : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [PolynormableSpace ℂ H] [PolynormableSpace ℂ K]
    (A : nuclearEndomorphisms H) (D : nuclearEndomorphisms K)
    (S : Submodule ℂ H) [CompleteSpace S] (U : K ≃ₗᵢ[ℂ] S)
    (q : V → K) (π : W → H) (i : V → W) (B : V → V) (C : W → W)
    (hq : Surjective q) (hU : ∀ v, (U (q v) : H) = π (i v))
    (hr : range A.val ⊆ range (fun v ↦ π (i v)))
    (hD : ∀ v, D.val (q v) = q (B v))
    (hA : ∀ w, A.val (π w) = π (C w)) (hB : ∀ v, C (i v) = i (B v)) :
    hilbertTrace A = hilbertTrace D := by
  let J := S.subtypeL.comp U.toContinuousLinearEquiv.toContinuousLinearMap
  let P := U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp S.orthogonalProjectionOnto
  have hPJ : LeftInverse P J := fun x ↦ by
    change U.symm (S.orthogonalProjectionOnto (U x : H)) = x
    rw [S.orthogonalProjectionOnto_mem_subspace_eq_self, U.symm_apply_apply]
  apply spectralIsotype_trace_of_range A D J P hPJ
  · intro x
    obtain ⟨v, hv⟩ := hr ⟨x, rfl⟩
    exact ⟨q v, (hU v).trans hv⟩
  · intro y
    obtain ⟨v, rfl⟩ := hq y
    change A.val (U (q v) : H) = (U (D.val (q v)) : H)
    rw [hU, hA, hB, hD, hU]

/-- The isometric quotient-isotype inclusion intertwines the two convolutions on representatives. -/
private theorem spectralIsotype_trace_eq (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (hA : IsNuclearOperator (spectralConvolution (F := F) a hI hs φ))
    (D : nuclearEndomorphisms Qω(a, hI, hs, ω))
    (hD : D.val = spectralIsotypeConvolution (F := F) a hI hs ω φ) :
    hilbertTrace ⟨spectralConvolution (F := F) a hI hs φ, hA⟩ = hilbertTrace D := by
  have hiso := spectralSobolevIsotypeQuotient_isometry (F := F) a hI hs ω
  with_reducible obtain ⟨ρQ, _, _, U, hU⟩ := hiso
  let S := actionIsotype (ρQ.comp (ideleClassNorm F).ker.subtype) ω
  let : CompleteSpace S := (isClosed_actionIsotype _ _).completeSpace_coe
  let : PolynormableSpace ℂ Qω(a, hI, hs, ω) :=
    (norm_withSeminorms ℂ Qω(a, hI, hs, ω)).toPolynormableSpace
  let E := Wω(hI, hs, ω)
  let N := Θ(a, hI, hs)
  let B := (testAction(l, r, s, hI, hs) φ).restrict
    (hardySobolevTestAction_preserves_spectralIsotype (F := F) hI hs ω φ)
  with_reducible_and_instances
    refine spectralIsotype_trace_representatives _ D S U (N.comap E.subtype).mkQ N.mkQ
      Subtype.val B (testAction(l, r, s, hI, hs) φ) (N.comap E.subtype).mkQ_surjective hU
      (spectralConvolution_range_isotype (F := F) a hI hs ω φ hφ) ?_
      (spectralConvolution_mkQ (F := F) a hI hs φ) (fun _ ↦ rfl)
  intro v
  exact (congrArg (fun L : Qω(a, hI, hs, ω) →L[ℂ] Qω(a, hI, hs, ω) ↦
    L ((N.comap E.subtype).mkQ v)) hD).trans
    (spectralIsotypeConvolution_mkQ (F := F) a hI hs ω φ v)

/-- Haar translation forces the Mellin transform of a homogeneous test to vanish off its character. -/
private theorem spectralIsotype_mellin_eq_zero
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {ω η : PontryaginDual C₁} (hne : η ≠ ω) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) (z : ℂ) :
    M(φ, χ η, z) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : C₁, (η k : ℂ) ≠ (ω k : ℂ) := by
    by_contra! heq
    exact hne (DFunLike.ext _ _ fun k ↦ Subtype.ext (heq k))
  let ξ := ideleClassNormTwist (F := F) (χ η) z
  have hkξ : ξ k.val = (η k : ℂ) := by
    have h := DFunLike.congr_fun (hχ η) k
    change (χ η) k.val = η k at h
    change (χ η k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ z = _
    rw [k.property]
    simpa using congrArg (fun u : Circle ↦ (u : ℂ)) h
  rw [(spectralConvolution_mellin_integrable φ (χ η) z).2]
  let I := ∫ g, φ.val g * ξ g ∂μ𝔽
  have heq : (ω k : ℂ) * I = (η k : ℂ) * I := calc
    _ = ∫ g, φ.val (k.val⁻¹ * g) * ξ g ∂μ𝔽 := by
      rw [← integral_const_mul]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [hφ, mul_assoc]
    _ = ∫ g, φ.val (k.val⁻¹ * (k.val * g)) * ξ (k.val * g) ∂μ𝔽 :=
      (integral_mul_left_eq_self (fun g ↦ φ.val (k.val⁻¹ * g) * ξ g) k.val).symm
    _ = (η k : ℂ) * I := by
      rw [← integral_const_mul]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [inv_mul_cancel_left, map_mul, hkξ]
      ring
  exact (mul_eq_mul_right_iff.mp heq).resolve_left hk.symm

/-- A sum on pairs supported on one character is the sum over that character's fiber. -/
private theorem spectralIsotype_trace_fiber {Ω X : Type*} (ω : Ω) (p : Ω → X → Prop)
    (f : {z : Ω × X // p z.1 z.2} → ℂ) {L : ℂ}
    (hn : Summable (fun z ↦ ‖f z‖)) (hsum : HasSum f L)
    (hzero : ∀ z, z.val.1 ≠ ω → f z = 0) :
    let j (x : {x : X // p ω x}) : {z : Ω × X // p z.1 z.2} := ⟨(ω, x.val), x.property⟩
    Summable (fun x ↦ ‖f (j x)‖) ∧ HasSum (fun x ↦ f (j x)) L := by
  let j (x : {x : X // p ω x}) : {z : Ω × X // p z.1 z.2} := ⟨(ω, x.val), x.property⟩
  have hj : Injective j := fun x y h ↦ Subtype.ext (congrArg (fun z ↦ z.val.2) h)
  have hoff (z) (hz : z ∉ range j) : f z = 0 := by
    apply hzero
    rcases z with ⟨⟨η, x⟩, hx⟩
    rintro rfl
    exact hz ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(hj.summable_iff (fun z hz ↦ by simp [hoff z hz])).mpr hn,
    (hj.hasSum_iff hoff).mpr hsum⟩

/-- Paper: Theorem 10.3.1.1(3) and (10.3.1.5), p. 449. The isotype
trace is the absolutely convergent zero sum of its base character.
Deviation: Use the strict cutoff and the left-translation eigencharacter ω
as in spectralConvolution_range_isotype. -/
theorem spectralLineIsotypeConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {s : ℝ} (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, h₀, hs₀(hs), ω)
    let term (t : {t : ℝ // 0 < order(χ ω, shift(a, t))}) :=
      (spectralBoundaryMultiplicity s (mult(χ ω, shift(a, t.val))) : ℂ) *
        M(φ, χ ω, shift(0, t.val))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ →
      Summable (fun t ↦ ‖term t‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term D hD
  let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
  have hA : IsNuclearOperator A := spectralLineConvolution_nuclear (F := F) a hs φ
  have hfull := spectralLineConvolution_trace (F := F) a χ _hχ hs φ ⟨A, hA⟩ rfl
  have ht := spectralIsotype_trace_eq (F := F) a h₀ hs₀(hs) ω φ _hφ hA D hD
  have sub := spectralIsotype_trace_fiber ω (fun η t ↦ 0 < order(χ η, shift(a, t)))
    (fun z ↦ (N(χ, s, z) : ℂ) * M(φ, χ z.val.1, shift(0, z.val.2))) hfull.1 hfull.2
    (fun z hz ↦ by rw [spectralIsotype_mellin_eq_zero χ _hχ hz φ _hφ, mul_zero])
  exact ⟨sub.1, ht ▸ sub.2⟩

end Line

section Strip

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

-- TODO(paper-gap): The strip synthesis gap in §10.2 remains. The proof on
-- p. 455 also replaces log powers of unbounded order by a fixed Sobolev
-- weight and concludes only p > 1 for the displayed scalar sum.

/-- For included jets the finite section has exactly the convolution coordinate.
Consequently the difference of two sufficiently large sections lies in the orthogonal
complement of any fixed finite span of Riesz vectors. Finite diagonal sums for a
single section after this orthogonal projection bound its trace norm. -/
private theorem spectralStripConvolution_traceCauchy_of_compressed_diagonal
    {H J κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (B : ℕ × ℕ → H →L[ℂ] H) (Λ : J → StrongDual ℂ H)
    (b : HilbertBasis κ ℂ H) (hnuc : ∀ j, B j ∈ nuclearEndomorphisms H)
    (hcoord : ∀ k, ∀ᶠ j in atTop, ∀ v, Λ k (B j v) = Λ k (A v))
    (ht : ∀ ε > (0 : ℝ), ∃ S : Finset J, ∀ᶠ j in atTop, ∀ t : Finset κ,
      let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ H).symm (Λ k)) '' (S : Set J))
      ∑ n ∈ t, (inner ℂ (b n) (CFC.sqrt ((B j).adjoint * Vᗮ.starProjection * B j) (b n))).re ≤ ε) :
    SpectralRectanglesTraceCauchy B := by
  classical
  intro ε hε
  obtain ⟨S, hS⟩ := ht (ε / 3) (by positivity)
  let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ H).symm (Λ k)) '' (S : Set J))
  let P := Vᗮ.starProjection
  let D (j : ℕ × ℕ) : nuclearEndomorphisms H :=
    ⟨P * B j, mul_mem_nuclearEndomorphisms_left P ⟨B j, hnuc j⟩⟩
  have hgram (j : ℕ × ℕ) : (D j).val.adjoint * (D j).val = (B j).adjoint * P * B j := by
    change star (P * B j) * (P * B j) = star (B j) * P * B j
    have hP : IsStarProjection P := isStarProjection_starProjection
    rw [star_mul, hP.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc (star (B j)), hP.isIdempotentElem.eq]
  have hnorm : ∀ᶠ j in atTop, traceNorm (D j) ≤ ε / 3 := by
    filter_upwards [hS] with j hj
    apply le_of_tendsto' (hasSum_traceNorm_diagonal b (D j))
    intro t
    simpa only [hgram] using hj t
  have hScoord : ∀ᶠ j in atTop, ∀ k ∈ S, ∀ v, Λ k (B j v) = Λ k (A v) :=
    S.eventually_all.mpr fun k _ ↦ hcoord k
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hnorm.and hScoord)
  refine ⟨j₀, fun j k hj hk ↦ ⟨D j - D k, ?_, ?_⟩⟩
  · ext v
    change P (B j v) - P (B k v) = B j v - B k v
    rw [← map_sub]
    apply Submodule.starProjection_eq_self_iff.mpr
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      rw [InnerProductSpace.toDual_symm_apply, map_sub, (hj₀ j hj).2 r hr v, (hj₀ k hk).2 r hr v,
        sub_self]
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  · let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
    have hc := traceNorm_normedSpaceCore (H := H)
    have hneg : traceNorm (-(D k)) = traceNorm (D k) := by
      rw [← neg_one_smul ℂ (D k)]
      simpa only [norm_neg, norm_one, one_mul] using hc.norm_smul (-1 : ℂ) (D k)
    have htr := hc.norm_triangle (D j) (-(D k))
    change traceNorm (D j + -(D k)) ≤ traceNorm (D j) + traceNorm (-(D k)) at htr
    rw [← sub_eq_add_neg, hneg] at htr
    linarith [(hj₀ j hj).1, (hj₀ k hk).1]

/-- Pointwise square-root identity from AppC_LCTVS/Sec3a, used for compression
and for the contraction which attains the trace norm. -/
private theorem spectralStripConvolution_traceCauchy_abs_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X : H →L[ℂ] H) (v : H) : ‖CFC.sqrt (X.adjoint * X) v‖ = ‖X v‖ := by
  let S := CFC.sqrt (X.adjoint * X)
  have hpos : 0 ≤ S := CFC.sqrt_nonneg _
  have ha := (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).isSelfAdjoint.adjoint_eq
  have hsq : S * S = X.adjoint * X :=
    CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr X.isPositive_adjoint_comp_self)
  change ‖S v‖ = ‖X v‖
  rw [S.apply_norm_eq_sqrt_inner_adjoint_right, X.apply_norm_eq_sqrt_inner_adjoint_right, ha,
    ← ContinuousLinearMap.mul_def, hsq, ContinuousLinearMap.mul_def]

/-- The two orthogonal output compressions satisfy a weighted trace-norm bound.
This follows from the Pythagorean identity on each input vector and operator
monotonicity of the positive square root. -/
private theorem spectralStripConvolution_traceCauchy_compression_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) [V.HasOrthogonalProjection] (T : nuclearEndomorphisms H)
    {d : ℝ} (hd : 0 ≤ d) :
    let left (P : H →L[ℂ] H) := (⟨P * T.val, mul_mem_nuclearEndomorphisms_left P T⟩ :
      nuclearEndomorphisms H)
    traceNorm (left V.starProjection) + d * traceNorm (left Vᗮ.starProjection) ≤
      (1 + d ^ 2) * traceNorm T := by
  intro left
  let absOp (X : H →L[ℂ] H) := CFC.sqrt (X.adjoint * X)
  let A := left V.starProjection
  let B := left Vᗮ.starProjection
  let Y := absOp A.val + d • absOp B.val
  let c := 1 + d ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have bound (v : H) : ‖Y v‖ ≤ ‖(c • T.val) v‖ := by
    have hp := V.norm_sq_eq_add_norm_sq_starProjection (T.val v)
    change ‖T.val v‖ ^ 2 = ‖A.val v‖ ^ 2 + ‖B.val v‖ ^ 2 at hp
    calc
      ‖Y v‖ ≤ ‖absOp A.val v‖ + ‖d • absOp B.val v‖ := norm_add_le _ _
      _ = ‖A.val v‖ + d * ‖B.val v‖ := by
        simp only [absOp, norm_smul, Real.norm_of_nonneg hd, spectralStripConvolution_traceCauchy_abs_norm]
      _ ≤ c * ‖T.val v‖ := by
        apply le_of_sq_le_sq _ (mul_nonneg hc (norm_nonneg _))
        calc
          _ ≤ (1 + d ^ 2) * (‖A.val v‖ ^ 2 + ‖B.val v‖ ^ 2) := by
            nlinarith [sq_nonneg (d * ‖A.val v‖ - ‖B.val v‖)]
          _ ≤ (c * ‖T.val v‖) ^ 2 := by
            rw [← hp, mul_pow]
            exact mul_le_mul_of_nonneg_right (by dsimp [c]; nlinarith [sq_nonneg d, sq_nonneg (d^2)])
              (sq_nonneg _)
      _ = ‖(c • T.val) v‖ := by simp [norm_smul, Real.norm_of_nonneg hc]
  have hY : 0 ≤ Y := add_nonneg (CFC.sqrt_nonneg (A.val.adjoint * A.val))
    (smul_nonneg hd (CFC.sqrt_nonneg (B.val.adjoint * B.val)))
  have hle := CFC.sqrt_le_sqrt _ _ ((ContinuousLinearMap.norm_map_le_norm_map_iff_le _ _).mp bound)
  change CFC.abs Y ≤ CFC.abs ((c : ℂ) • T.val) at hle
  rw [CFC.abs_of_nonneg Y hY, CFC.abs_smul, Complex.norm_real, Real.norm_of_nonneg hc] at hle
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  refine hasSum_le (fun i ↦ ?_)
    ((hasSum_traceNorm_diagonal b A).add ((hasSum_traceNorm_diagonal b B).mul_left d))
    ((hasSum_traceNorm_diagonal b T).mul_left c)
  have h := (ContinuousLinearMap.le_def.mp hle).re_inner_nonneg_right (b i)
  simpa [Y, absOp, CFC.abs, ContinuousLinearMap.star_eq_adjoint, inner_sub_right,
    inner_add_right, inner_smul_right_eq_smul, sub_nonneg] using h

/-- A finite block sum nearly attaining the common bound leaves little trace norm
for disjoint sums. A finite span of moments detects the almost maximal sum and is
orthogonal to every block outside a fixed finite set. -/
private theorem spectralStripConvolution_traceCauchy_bounded_tails
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : Z → nuclearEndomorphisms H) (V : Finset J → Submodule ℂ H)
    [∀ S, (V S).HasOrthogonalProjection]
    (hcap : ∀ K : Finset Z, ∀ η > (0 : ℝ), ∃ S : Finset J,
      traceNorm ⟨(V S)ᗮ.starProjection * (∑ z ∈ K, R z).val,
        mul_mem_nuclearEndomorphisms_left _ _⟩ < η)
    (hoff : ∀ S, ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      (V S)ᗮ.starProjection * (∑ z ∈ K, R z).val = (∑ z ∈ K, R z).val)
    (hbound : BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, R z))) :
    ∀ ε > (0 : ℝ), ∃ F : Finset Z, ∀ K : Finset Z, Disjoint K F →
      traceNorm (∑ z ∈ K, R z) < ε := by
  classical
  intro ε hε
  let n (K : Finset Z) := traceNorm (∑ z ∈ K, R z)
  let M := ⨆ K, n K
  have upper (K : Finset Z) : n K ≤ M := le_ciSup hbound K
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let core := (traceNorm_normedSpaceCore (H := H)).toCore
  have hM : 0 ≤ M := (core.norm_nonneg (∑ z ∈ (∅ : Finset Z), R z)).trans (upper ∅)
  let d := min 1 (ε / (4 * (M + 1)))
  have hd : 0 < d := lt_min one_pos (div_pos hε (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdM : d * M ≤ ε / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (M + 1))).mp (min_le_right 1 (ε / (4 * (M + 1))))
    change d * (4 * (M + 1)) ≤ ε at h
    linarith
  let η := d * ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K, hK⟩ : ∃ K, M - η < n K := exists_lt_of_lt_ciSup (show M - η < M by linarith)
  obtain ⟨S, hS⟩ := hcap K η hη
  obtain ⟨F, hF⟩ := hoff S
  refine ⟨K ∪ F, ?_⟩
  intro L hL
  let X := ∑ z ∈ K, R z
  let Y := ∑ z ∈ L, R z
  let P := (V S).starProjection
  let Q := (V S)ᗮ.starProjection
  let left (A : H →L[ℂ] H) (T : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨A * T.val, mul_mem_nuclearEndomorphisms_left _ _⟩
  have hQ : Q = 1 - P := (V S).starProjection_orthogonal'
  have hQY : Q * Y.val = Y.val := hF L (Finset.disjoint_union_right.mp hL).2
  have hPY : P * Y.val = 0 := by rwa [hQ, sub_mul, one_mul, sub_eq_self] at hQY
  have hX : left P (X + Y) + left Q X = X := by
    apply Subtype.ext
    change P * (X.val + Y.val) + Q * X.val = X.val
    rw [mul_add, hPY, add_zero, hQ, sub_mul, one_mul]
    abel
  have hY : left Q (X + Y) - left Q X = Y := by
    apply Subtype.ext
    change Q * (X.val + Y.val) - Q * X.val = Y.val
    rw [mul_add, hQY, add_sub_cancel_left]
  -- The head of X + Y still sees almost M. The common bound on X + Y then limits its tail.
  have bound := spectralStripConvolution_traceCauchy_compression_bound (V S) (X + Y) hd.le
  change traceNorm (left P (X + Y)) + d * traceNorm (left Q (X + Y)) ≤ _ at bound
  have hXY : traceNorm (X + Y) ≤ M := by
    simpa only [n, Finset.sum_union (Finset.disjoint_union_right.mp hL).1.symm] using upper (K ∪ L)
  have hnX : n K ≤ traceNorm (left P (X + Y)) + traceNorm (left Q X) := by
    change ‖X‖ ≤ _
    calc
      ‖X‖ = ‖left P (X + Y) + left Q X‖ := congrArg norm hX.symm
      _ ≤ _ := core.norm_triangle _ _
  have hnY : traceNorm Y ≤ traceNorm (left Q (X + Y)) + traceNorm (left Q X) :=
    calc
      ‖Y‖ = ‖left Q (X + Y) - left Q X‖ := congrArg norm hY.symm
      _ ≤ _ := by
        have hneg : traceNorm (-(left Q X)) = traceNorm (left Q X) := by
          rw [← neg_one_smul ℂ (left Q X)]
          simpa only [norm_neg, norm_one, one_mul] using core.norm_smul (-1 : ℂ) (left Q X)
        change traceNorm (_ - _) ≤ _
        rw [sub_eq_add_neg, ← hneg]
        exact core.norm_triangle _ _
  change traceNorm (left Q X) < η at hS
  change traceNorm Y < ε
  by_contra! hbad
  have small := mul_le_mul_of_nonneg_left hdM hd.le
  have cost := mul_le_mul_of_nonneg_left hXY (by positivity : 0 ≤ 1 + d ^ 2)
  have hscaled := mul_le_mul_of_nonneg_left (hbad.trans hnY) hd.le
  have herror := mul_le_mul_of_nonneg_right hd1 (core.norm_nonneg (left Q X))
  change d * traceNorm (left Q X) ≤ 1 * traceNorm (left Q X) at herror
  dsimp only [η] at hK hS
  nlinarith only [bound, cost, small, hscaled, herror, hnX, hK, hS, mul_pos hd hε]

/-- Every selected block takes values in the span of its finitely many jet vectors. -/
private theorem spectralStripConvolution_traceCauchy_finiteRank
    {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (L : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    FiniteDimensional ℂ (spectralConvolutionFiniteSum A x Λ L N jet).toLinearMap.range := by
  classical
  let Y := (L.sigma fun z ↦ (Finset.univ : Finset (Fin (N z)))).image (fun p ↦ x (jet p.1 p.2))
  let W := Submodule.span ℂ (Y : Set H)
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ Y.finite_toSet
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  rintro _ ⟨v, rfl⟩
  change spectralConvolutionFiniteSum A x Λ L N jet v ∈ W
  simp only [spectralConvolutionFiniteSum, sum_apply, ContinuousLinearMap.smulRight_apply]
  refine W.sum_mem fun z hz ↦ W.sum_mem fun m _ ↦ W.smul_mem _ (Submodule.subset_span ?_)
  exact Finset.mem_image.mpr ⟨⟨z, m⟩, Finset.mem_sigma.mpr ⟨hz, Finset.mem_univ _⟩, rfl⟩

/-- Biorthogonality identifies the blocks missed by any finite set of moments.
Totality makes the complementary projections strongly null, hence small in
trace norm on any fixed finite section. -/
private theorem spectralStripConvolution_traceCauchy_of_bounded_blocks
    {H J Z κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) (row : J → Z) (hr : ∀ z m, row (jet z m) = z)
    (K : ℕ × ℕ → Finset Z) (hK : ∀ z, ∀ᶠ j in atTop, z ∈ K j) (b : HilbertBasis κ ℂ H)
    (R : Z → nuclearEndomorphisms H)
    (hR : ∀ L : Finset Z, (∑ z ∈ L, R z).val = spectralConvolutionFiniteSum A x Λ L N jet)
    (hbound : BddAbove (range fun L : Finset Z ↦ traceNorm (∑ z ∈ L, R z))) :
    ∀ ε > (0 : ℝ), ∃ S : Finset J, ∀ᶠ j in atTop, ∀ t : Finset κ,
      let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ H).symm (Λ k)) '' (S : Set J))
      let B := spectralConvolutionFiniteSum A x Λ (K j) N jet
      ∑ i ∈ t, (inner ℂ (b i) (CFC.sqrt (B.adjoint * Vᗮ.starProjection * B) (b i))).re ≤ ε := by
  classical
  let u (k : J) := (InnerProductSpace.toDual ℂ H).symm (Λ k)
  let V (S : Finset J) := Submodule.span ℂ (u '' (S : Set J))
  let dim (S : Finset J) : FiniteDimensional ℂ (V S) :=
    FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image u)
  let Q (S : Finset J) := (V S)ᗮ.starProjection
  have hQ (v : H) : Tendsto (fun S ↦ Q S v) atTop (𝓝 0) := by
    have hd : ⊤ ≤ (⨆ S, V S).topologicalClosure := by
      apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
      rw [Submodule.eq_bot_iff]
      intro w hw
      have he : ContinuousLinearMap.apply ℂ ℂ w = 0 := by
        apply ContinuousLinearMap.ext_on hb.2.2.2
        rintro _ ⟨k, rfl⟩
        have hm : u k ∈ V {k} := Submodule.subset_span ⟨k, Finset.mem_singleton_self k, rfl⟩
        have h := (Submodule.mem_orthogonal _ _).mp hw _ (le_iSup V {k} hm)
        change Λ k w = 0
        simpa only [u, InnerProductSpace.toDual_symm_apply] using h
      have hz := congrArg (fun f : StrongDual ℂ H →L[ℂ] ℂ ↦ f (InnerProductSpace.toDual ℂ H w)) he
      exact inner_self_eq_zero.mp hz
    have hm : Monotone V := fun _ _ h ↦ Submodule.span_mono (image_mono h)
    have h := tendsto_const_nhds (x := v) |>.sub (Submodule.starProjection_tendsto_self V hm v hd)
    simpa only [Q, Submodule.starProjection_orthogonal_val, sub_self] using h
  let B (L : Finset Z) := ∑ z ∈ L, R z
  let left (S : Finset J) (T : nuclearEndomorphisms H) : nuclearEndomorphisms H :=
    ⟨Q S * T.val, mul_mem_nuclearEndomorphisms_left _ _⟩
  have capture (L : Finset Z) (η : ℝ) (hη : 0 < η) : ∃ S, traceNorm (left S (B L)) < η := by
    have hdim : FiniteDimensional ℂ (B L).val.toLinearMap.range := by
      change FiniteDimensional ℂ (∑ z ∈ L, R z).val.toLinearMap.range
      rw [hR]
      exact spectralStripConvolution_traceCauchy_finiteRank A x Λ L N jet
    obtain ⟨_, hlim⟩ := tendsto_traceNorm_mul_finiteRank Q hQ (B L).val
      hdim
    exact (hlim.eventually_lt_const hη).exists
  have off (S : Finset J) : ∃ F : Finset Z, ∀ L : Finset Z, Disjoint L F →
      Q S * (B L).val = (B L).val := by
    refine ⟨S.image row, ?_⟩
    intro L hL
    ext v
    apply Submodule.starProjection_eq_self_iff.mpr
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      change inner ℂ (u k) ((B L).val v) = 0
      rw [show inner ℂ (u k) ((B L).val v) = Λ k ((B L).val v) from InnerProductSpace.toDual_symm_apply]
      change Λ k ((∑ z ∈ L, R z).val v) = 0
      rw [hR]
      simp only [spectralConvolutionFiniteSum, sum_apply, map_sum, ContinuousLinearMap.smulRight_apply, map_smul]
      refine Finset.sum_eq_zero fun z hz ↦ Finset.sum_eq_zero fun m _ ↦ ?_
      have hne : jet z m ≠ k := by
        intro h
        exact (Finset.disjoint_left.mp hL hz)
          (Finset.mem_image.mpr ⟨k, hk, (congrArg row h).symm.trans (hr z m)⟩)
      rw [hb.2.1 _ _ hne, smul_zero]
    | zero => exact inner_zero_left _
    | add y w _ _ hy hw => rw [inner_add_left, hy, hw, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  intro ε hε
  obtain ⟨F, hF⟩ := spectralStripConvolution_traceCauchy_bounded_tails R V capture off hbound _ (half_pos hε)
  obtain ⟨S, hS⟩ := capture F _ (half_pos hε)
  refine ⟨S, ?_⟩
  filter_upwards [F.eventually_all.mpr (fun z _ ↦ hK z)] with j hj
  let T := B (K j \ F)
  have heq : left S (B (K j)) = left S T + left S (B F) := by
    have hadd : B (K j) = T + B F := (Finset.sum_sdiff (f := R) (show F ⊆ K j from hj)).symm
    rw [hadd]
    exact Subtype.ext (mul_add _ _ _)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let core := (traceNorm_normedSpaceCore (H := H)).toCore
  have hsmall : traceNorm (left S (B (K j))) ≤ ε := by
    have hc := (traceNorm_mul_left_le (Q S) T).trans
      (mul_le_of_le_one_left (core.norm_nonneg T) (V S)ᗮ.starProjection_norm_le)
    rw [heq]
    exact (core.norm_triangle _ _).trans ((add_le_add (hc.trans (hF _ Finset.sdiff_disjoint).le)
      hS.le).trans_eq (add_halves ε))
  intro t
  let D := left S (B (K j))
  have hs := hasSum_traceNorm_diagonal b D
  have hpos (i : κ) : 0 ≤ (inner ℂ (b i) (CFC.sqrt (D.val.adjoint * D.val) (b i))).re :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg (D.val.adjoint * D.val))).re_inner_nonneg_right _
  have hsum := hs.summable.sum_le_tsum t fun i _ ↦ hpos i
  rw [hs.tsum_eq] at hsum
  have gram : D.val.adjoint * D.val = (B (K j)).val.adjoint * Q S * (B (K j)).val := by
    change star (Q S * _) * (Q S * _) = star _ * Q S * _
    have hp : IsStarProjection (Q S) := isStarProjection_starProjection
    rw [star_mul, hp.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc (star _), hp.isIdempotentElem.eq]
  simpa only [gram, B, hR] using hsum.trans hsmall

/-- A finite-rank operator attains its trace norm against a compact contraction.
Use the contraction taking the operator to its absolute value and restrict it
to the finite-dimensional range. -/
private theorem spectralStripConvolution_traceCauchy_norming
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (hdim : FiniteDimensional ℂ T.val.toLinearMap.range) :
    ∃ U : compactOperator (RingHom.id ℂ) H H, ‖U‖ ≤ 1 ∧
      traceNorm T = (hilbertTrace ⟨U.val * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩).re := by
  let W := T.val.toLinearMap.range
  let B := CFC.sqrt (T.val.adjoint * T.val)
  obtain ⟨C, hC, hCB⟩ := exists_contraction_comp_eq_of_norm_le T.val B
    fun v ↦ (spectralStripConvolution_traceCauchy_abs_norm T.val v).le
  let U : compactOperator (RingHom.id ℂ) H H := ⟨C * W.starProjection,
    (isCompactOperator_of_locallyCompactSpace_rng (C.comp W.subtypeL)).comp_clm W.orthogonalProjectionOnto⟩
  refine ⟨U, (norm_mul_le C W.starProjection).trans
    ((mul_le_of_le_one_right (norm_nonneg _) W.starProjection_norm_le).trans hC), ?_⟩
  have hUB : U.val * T.val = B := by
    ext v
    change C (W.starProjection (T.val v)) = B v
    rw [Submodule.starProjection_eq_self_iff.mpr (show T.val v ∈ W from ⟨v, rfl⟩)]
    exact congrArg (fun L : H →L[ℂ] H ↦ L v) hCB
  let D : nuclearEndomorphisms H := ⟨U.val * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  have h := Complex.reCLM.hasSum (summable_norm_hilbertDiagonal b D.val D.property).of_norm.hasSum
  change HasSum (fun i ↦ (inner ℂ (b i) ((U.val * T.val) (b i))).re) (hilbertTrace D).re at h
  rw [hUB] at h
  exact (hasSum_traceNorm_diagonal b T).unique h

/-- Pointwise summability of the block traces against compact operators gives
one trace-norm bound for all finite selections, by uniform boundedness on the
Banach space of compact operators. -/
private theorem spectralStripConvolution_traceCauchy_scalar_bound
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (h : ∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z ↦ ∑ m : Fin (N z), Λ (jet z m) (A (U.val (x (jet z m)))))) :
    ∃ R : Z → nuclearEndomorphisms H,
      (∀ K : Finset Z, (∑ z ∈ K, R z).val = spectralConvolutionFiniteSum A x Λ K N jet) ∧
      BddAbove (range fun K : Finset Z ↦ traceNorm (∑ z ∈ K, R z)) := by
  classical
  let f (j : J) := (Λ j).comp A
  let term (j : J) (y : H) : nuclearEndomorphisms H :=
    ⟨(f j).smulRight y, smulRight_mem_nuclearEndomorphisms _ _⟩
  let R (z : Z) := ∑ m, term (jet z m) (x (jet z m))
  have hR (K : Finset Z) : (∑ z ∈ K, R z).val = spectralConvolutionFiniteSum A x Λ K N jet := by
    simp only [R, Submodule.coe_sum, term, f, spectralConvolutionFiniteSum]
  refine ⟨R, hR, ?_⟩
  let C := compactOperator (RingHom.id ℂ) H H
  let : CompleteSpace C := (show IsClosed (C : Set (H →L[ℂ] H)) from
    isClosed_setOfPred_isCompactOperator).completeSpace_coe
  let eval (j : J) := (f j).comp ((ContinuousLinearMap.apply ℂ H (x j)).comp C.subtypeL)
  let test (K : Finset Z) := ∑ z ∈ K, ∑ m, eval (jet z m)
  obtain ⟨c, hc⟩ := banach_steinhaus (g := test) (fun U ↦ by
    refine ⟨∑' z, ‖∑ m, Λ (jet z m) (A (U.val (x (jet z m))))‖, fun K ↦ ?_⟩
    simp only [test, sum_apply]
    exact (norm_sum_le _ _).trans ((h U).norm.sum_le_tsum K fun _ _ ↦ norm_nonneg _))
  refine ⟨c, ?_⟩
  rintro _ ⟨K, rfl⟩
  let T := ∑ z ∈ K, R z
  have hd : FiniteDimensional ℂ T.val.toLinearMap.range := by
    dsimp only [T]
    rw [hR]
    exact spectralStripConvolution_traceCauchy_finiteRank A x Λ K N jet
  obtain ⟨U, hU, hnorm⟩ := spectralStripConvolution_traceCauchy_norming T hd
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  let D : nuclearEndomorphisms H := ⟨U.val * T.val, mul_mem_nuclearEndomorphisms_left _ T⟩
  have heq : D = ∑ z ∈ K, ∑ m, term (jet z m) (U.val (x (jet z m))) := by
    apply Subtype.ext
    ext v
    change U.val (T.val v) = _
    simp only [T, R, term, Submodule.coe_sum, sum_apply, ContinuousLinearMap.smulRight_apply,
      map_sum, map_smul]
  have ht : hilbertTrace D = test K U := by
    rw [← htr, heq]
    simp only [map_sum]
    simp only [htr, term, hilbertTrace_smulRight, test, sum_apply]
    rfl
  change traceNorm T ≤ c
  rw [hnorm, show hilbertTrace ⟨U.val * T.val, _⟩ = test K U from ht]
  exact (Complex.re_le_norm _).trans (((test K).le_opNorm U).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hU).trans (hc K)))

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. After inserting any fixed compact
operator on the biorthogonal vectors, the scalar traces of the individual zero
blocks are summable. The jets at each zero are summed before testing summability.
The estimates for (10.3.2.7) involve only Mellin derivatives and give no bound for these
pairings with a compact operator. A summable majorant for the absolute block
traces, allowed to depend on the operator and test, would suffice. -/
private theorem spectralStripConvolution_traceCauchy_compact_block_series (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let jet (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) :
        SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
      ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
    ∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z : Z(χ, α) ↦ ∑ m, Λ (jet z m) (A (U.val (x (jet z m))))) := by
  sorry

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455, after (10.3.2.7). For a fixed test,
discard the output directions of finitely many jets. The positive square root of
the remaining Gram operator should have uniformly small finite diagonal sums.
By `_hb` the Riesz vectors span densely, so the complementary projections tend strongly to
zero and compress any fixed finite-rank rectangle to zero in trace norm. In a trace-norm
Cauchy tail, contractivity bounds each later compressed trace norm, and hence each finite
diagonal sum, by the fixed rectangle's compressed trace norm plus the tail error.
Gap: The scalar Mellin estimates on p. 455 do not control this sum for an
individual rectangle, in particular when its boundary separates nearby zeros. -/
private theorem spectralStripConvolution_traceCauchy_compressed_diagonal (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    {κ : Type*} (b : HilbertBasis κ ℂ Q(a, hStrip(hα), hs₀(hs))) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    let diagonal {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
        {J : Type _} (forms : J → StrongDual ℂ E) (S : Finset J) (D : E →L[ℂ] E) (v : E) :=
      let V := Submodule.span ℂ ((fun k ↦ (InnerProductSpace.toDual ℂ E).symm (forms k)) '' (S : Set J))
      (inner ℂ v (CFC.sqrt (D.adjoint * Vᗮ.starProjection * D) v)).re
    ∀ ε > (0 : ℝ), ∃ S : Finset (SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s),
      ∀ᶠ j in atTop, ∀ t : Finset κ, ∑ n ∈ t, diagonal Λ S (B j) (b n) ≤ ε := by
  classical
  intro H A B diagonal
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) :
      SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let row (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : Z(χ, α) :=
    ⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩
  obtain ⟨R, hR, hbound⟩ := spectralStripConvolution_traceCauchy_scalar_bound A x Λ count jet
    (spectralStripConvolution_traceCauchy_compact_block_series a χ _hχ hα hs φ x Λ _hb _hj)
  apply spectralStripConvolution_traceCauchy_of_bounded_blocks A x Λ _hb count jet row
    (fun _ _ ↦ rfl) (fun ij : ℕ × ℕ ↦
      ((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn) _ b R hR hbound
  intro z
  filter_upwards [eventually_ge_atTop (e z)] with ij hij
  simpa using (show (e z).1 ≤ ij.1 ∧ (e z).2 ≤ ij.2 from hij)

/-- Paper: Theorem 10.3.2.1(1), p. 453. The rectangular sums have Cauchy tails in trace norm.
Gap: Trace-norm tails must control close zeros and high jet orders in the strip norm.
A strip component with bounded central-line frequency support vanishes by holomorphy. -/
theorem spectralStripConvolution_traceCauchy (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    SpectralRectanglesTraceCauchy B := by
  classical
  intro H A B
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩
  let eqv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  apply spectralStripConvolution_traceCauchy_of_compressed_diagonal A B Λ b
  · intro j
    exact (nuclearEndomorphisms H).sum_mem fun z _ ↦
      (nuclearEndomorphisms H).sum_mem fun m _ ↦ smulRight_mem_nuclearEndomorphisms _ _
  · intro r
    obtain ⟨⟨z, m⟩, rfl⟩ := eqv.surjective r
    filter_upwards [eventually_ge_atTop (e z)] with j hj
    exact spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate A x Λ _ count jet _hb eqv.injective
      z (by simpa using (show (e z).1 ≤ j.1 ∧ (e z).2 ≤ j.2 from hj)) m
  · exact spectralStripConvolution_traceCauchy_compressed_diagonal (F := F) a χ _hχ hα hs φ
      eχ e _he x Λ _hb _hj b

/-- Paper: Theorem 10.3.2.1(1) and (10.3.2.1), p. 453. The rectangular
finite-rank sums over any enumeration of the strip zeros converge to convolution
in every Schatten class.
Deviation: The injections include finite or empty enumerations. The
interval is allowed to be a singleton and the jets use the strict boundary cutoff. -/
theorem spectralStripConvolution_schatten_tendsto (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (eχ : PontryaginDual C₁ ↪ ℕ) (e : Z(χ, α) ↪ ℕ × ℕ) (_he : ∀ z, (e z).1 = eχ z.val.1)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs₀(hs)))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (_hb : IsSpectralMarkushevichBasis x Λ)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (p : ℝ) (hp : 1 ≤ p) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A : H →L[ℂ] H := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let S := schattenClass H H p hp
    let B (ij : ℕ × ℕ) : H →L[ℂ] H :=
      spectralConvolutionFiniteSum A x Λ
        (((Finset.Iic ij.1).product (Finset.Iic ij.2)).preimage e e.injective.injOn)
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)
    ∃ (hA : A ∈ S) (hB : ∀ ij, B ij ∈ S),
      Tendsto (fun ij ↦ schattenNorm (E := H) (F := H) (p := p) (hp := hp)
        (⟨B ij, hB ij⟩ - ⟨A, hA⟩ : S)) atTop (𝓝 0) := by
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralConvolutionFiniteSum_limit_of_traceCauchy
    (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) x Λ e count jet
    _hb equiv.bijective p hp
    (spectralStripConvolution_traceCauchy (F := F) a χ _hχ hα hs φ eχ e _he x Λ _hb _hj)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Convolution on the strip spectral
quotient is trace class for each test. -/
theorem spectralStripConvolution_nuclear {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  obtain ⟨_, x, Λ, hb, hj⟩ := spectralStripMarkushevichBasis (a := a) χ hχ hα hs₀(hs)
  obtain ⟨r, e, he⟩ := spectralLineConvolution_nuclear_indices χ
    (fun z : Z(χ, α) ↦ z.val.1) (fun z ↦ shift(a + z.val.2.1, z.val.2.2)) (by
      intro i j h
      have hrow := congrArg Prod.fst h
      have hre := congrArg (fun p ↦ (p.2 : ℂ).re) h
      have him := congrArg (fun p ↦ (p.2 : ℂ).im) h
      exact Subtype.ext (Prod.ext hrow
        (Prod.ext (by simpa using hre) (by simpa using him)))) (fun z ↦ z.property.2)
  obtain ⟨hA, _⟩ := spectralStripConvolution_schatten_tendsto (F := F) a χ hχ hα hs φ
    r e he x Λ hb hj 1 le_rfl
  exact (mem_traceClassOperators_iff_isNuclearOperator _).mp hA

-- TODO(paper-gap): (10.3.2.2), p. 454 asks for continuity of the strip convolution action in
-- trace norm. The printed proof of Theorem 10.3.2.1 replaces the scalar series (10.3.2.6) by
-- (10.3.2.7) and shows the latter converges for p > 1; but the constants C_{N,I,s}(phi) of
-- (10.3.2.11) carry the derivatives of the test itself, so this is an estimate at a fixed test
-- and yields no seminorm bound uniform in the test. The per-zero bounds (10.3.1.19)-(10.3.1.22),
-- which the proof says carry over, rest on the single biorthogonality constant C of (10.3.1.18),
-- which is Printed.spectralLineJet_uniformBiorthogonalBound, refuted in Sec3_Printed.lean. On the
-- strip N_{I,s} is unbounded for alpha > 0 (as the proof of 10.3.2.1 notes), so the jets of one
-- character grow with s and alpha as well. What is missing is a bound on the number of strip
-- zeros of L(s, chi w) with |Im s| <= T in the number of jet orders used, together with a
-- trace-norm estimate uniform in the test. A reduction of this statement to that single
-- seminorm estimate is blocked at elaboration: the linear lift into
-- nuclearEndomorphisms (Q a (hStrip hα) (hs₀ hs)) cannot be built by the anonymous constructor
-- of LinearMap (here LinearMap extends AddHom and MulActionHom, so the field literal
-- { toFun := ..., map_add' := ..., map_smul' := ... } is rejected by the parser), and building
-- it from an abstract function via AddHom exhausts the heartbeat budget in isDefEq and whnf on
-- that quotient type; see #5398.

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.2), p. 454. The convolution
action lifts to a linear map into the trace class, continuous at zero in trace norm. -/
theorem spectralStripConvolution_traceNorm_continuous {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ T : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms H,
      (∀ φ, (T φ).val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) ∧
      Tendsto (fun φ : BruhatCompactSupport C𝔽 ↦ traceNorm (H := H) (T φ)) (𝓝 0) (𝓝 0) := by
  intro H
  let A : BruhatCompactSupport C𝔽 →ₗ[ℂ] (H →L[ℂ] H) :=
    (spectralConvolution_isLinear (F := F) a hStrip(hα) hs₀(hs)).mk'
      (spectralConvolution (F := F) a hStrip(hα) hs₀(hs))
  exact spectralConvolution_traceNorm_lift bruhatCompactSupport_strictLF A
    (spectralConvolution_opNorm_continuous (F := F) a hStrip(hα) hs₀(hs))
    (spectralStripConvolution_nuclear (F := F) a hα hs)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Taking the trace of convolution gives
a distribution on the Bruhat compactly supported test space. -/
theorem spectralStripConvolution_trace_distribution {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms H),
        T.val = spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ →
        D φ = hilbertTrace (H := H) T := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  exact traceDistribution (X := BruhatCompactSupport C𝔽) (H := Q(a, hStrip(hα), hs₀(hs)))
    (spectralConvolution (F := F) a hStrip(hα) hs₀(hs))
    (spectralStripConvolution_traceNorm_continuous (F := F) a hα hs)

/-- Paper: Theorem 10.3.2.1(3), p. 454. The singular values decay faster than every inverse power.
Deviation: Assume trace class for all tests. Factor the homogeneous radial profile into
finite sums of iterated convolutions of smooth compactly supported functions on ℝ.
The approximation-number product inequality then gives arbitrary polynomial decay. -/
theorem spectralStripIsotypeConvolution_rapid_approximationNumbers
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x)
    (_htrace : ∀ ψ : BruhatCompactSupport C𝔽,
      IsNuclearOperator (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) ψ)) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    let A : H →L[ℂ] H := spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by
  exact spectralApprox_isotype_rapid (F := F) a hStrip(hα) hs₀(hs) ω φ _hφ _htrace

/-- Paper: Theorem 10.3.2.1(3), p. 454. Convolution by a homogeneous
test acts by a strongly nuclear operator on the corresponding quotient isotype.
Deviation: Use the left-translation eigencharacter ω. -/
theorem spectralStripIsotypeConvolution_stronglyNuclear
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    IsStronglyNuclearBanachOperator (E := H) (G := H)
      (spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ) := by
  exact isStronglyNuclearBanachOperator_of_rapid_approximationNumbers _
    (spectralStripIsotypeConvolution_rapid_approximationNumbers (F := F) a hα hs ω φ _hφ
      (spectralStripConvolution_nuclear (F := F) a hα hs))

/-- Paper: Theorem 10.3.2.1(3) and (10.3.2.5), p. 454. The isotype
trace is the absolutely convergent zero sum of its base character.
Deviation: Use the strict cutoff and the left-translation eigencharacter ω
as in spectralConvolution_range_isotype. -/
theorem spectralStripIsotypeConvolution_trace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (_hφ : ∀ (k : C₁) (x : C𝔽), φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    let H := Qω(a, hStrip(hα), hs₀(hs), ω)
    let term (z : {z : ℝ × ℝ // z.1 ∈ Icc (-α) α ∧ 0 < order(χ ω, shift(a + z.1, z.2))}) :=
      (spectralStripMultiplicity α s z.val.1 (mult(χ ω, shift(a + z.val.1, z.val.2))) : ℂ) *
        M(φ, χ ω, shift(z.val.1, z.val.2))
    ∀ (T : nuclearEndomorphisms H),
      T.val = spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ →
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace (H := H) T) := by
  intro H term D hD
  let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
  have hA : IsNuclearOperator A := spectralStripConvolution_nuclear (F := F) a hα hs φ
  have hfull := spectralStripConvolution_trace (F := F) a χ _hχ hα hs φ ⟨A, hA⟩ rfl
  have ht := spectralIsotype_trace_eq (F := F) a hStrip(hα) hs₀(hs) ω φ _hφ hA D hD
  have sub := spectralIsotype_trace_fiber ω
    (fun η (x : ℝ × ℝ) ↦ x.1 ∈ Icc (-α) α ∧ 0 < order(χ η, shift(a + x.1, x.2)))
    (fun z ↦ (N(χ, α, s, z) : ℂ) * M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))) hfull.1 hfull.2
    (fun z hz ↦ by rw [spectralIsotype_mellin_eq_zero χ _hχ hz φ _hφ, mul_zero])
  exact ⟨sub.1, ht ▸ sub.2⟩

end Strip

end RiemannMasullo
