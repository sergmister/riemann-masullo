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

section Line

variable (a : ℝ)

local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ // 0 < order(χ z.1, shift(a, z.2))}
local notation "N(" χ ", " s ", " z ")" => spectralBoundaryMultiplicity s (mult(χ (z).val.1,
  shift(a, (z).val.2)))

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
    SpectralRectanglesTraceCauchy B := by sorry

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

local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
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
    dsimp only [L]
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
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by sorry

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
    SpectralRectanglesTraceCauchy B := by sorry

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
    ∀ k : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k * approximationNumber A n) atTop (𝓝 0) := by sorry

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
