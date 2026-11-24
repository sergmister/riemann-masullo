module
public import RiemannMasullo.Research.PositiveStrip.Angular
public import RiemannMasullo.Research.PositiveStrip.Generators
public import RiemannMasullo.Research.PositiveStrip.Compatibility
public import RiemannMasullo.Research.PositiveStrip.TailFamily
import all RiemannMasullo.Ch10_TraceSpectral.Sec2

@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal NumberField.AdeleRing
namespace RiemannMasullo
open StripDual
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "stripJet(" χ ", " j ")" => spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2

/-- Membership on a single inverse-character component follows from its
continuous Taylor functionals that annihilate the whole theta test ideal. -/
theorem spectralStrip_radial_synthesis (ψ : PontryaginDual C𝔽) (a α s : ℝ)
    (ha : 0 ≤ α) (hs : 0 ≤ s) (e : Tests →ₗ[ℂ] SE α s) (he : DenseRange e)
    (her : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (L : SE α s →L[ℂ] W(-α,α,s))
    (hL : ∀ q, (L q : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * q (logNorm x))
    (y : SE α s) (hy : ∀ (w : ℂ) (k : ℕ) (K : StrongDual ℂ (SE α s)),
      (∀ H, K (e H) = iteratedDeriv k H.val w) →
      (∀ H ∈ thetaProducts ψ a, iteratedDeriv k H.val w = 0) → K y = 0) :
    L y ∈ Θ(a, neg_le_self ha, hs) := by
  let β := α+s+1
  let r := β+1
  have hβ : 2*α+s < 2*β := by dsimp [β]; linarith
  have hβr : β < r := by dsimp [r]; linarith
  have hr : α+s/2 < r := by linarith
  obtain ⟨f,b,U,S,m,hG,hGB,-,hm,ho,-,-,-,hlim,hprof,hideal⟩ :=
    exists_single_generator_tail_family ψ a α s β r ha hs hβ hβr e her L hL
  let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist ψ ((a:ℂ)+z))
  let N := (Θ(a, neg_le_self ha, hs)).comap L.toLinearMap
  have hN : IsClosed (N : Set (SE α s)) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  apply analytic_strip_synthesis N hN e he (thetaProducts ψ a) (thetaProducts_stable ψ a)
    (chart_multiplier_action ha hs hβ hβr e her) G hG hGB atTop U hlim S m hm ho hideal _ y hy
  intro n H hH
  let M := N.comap ((U n).toLinearMap.comp e)
  change H ∈ M
  have hspan : thetaProducts ψ a ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,K⟩,rfl⟩
    exact cutoff_generator_mem ha hs hr ψ e L hL (U n) (b n) (hprof n) g K _ (thetaProduct_apply ψ a g K)
  exact hspan hH

local notation "stripI(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripU(" χ ", " hα ", " hs ")" =>
  (fun j ↦ (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)))

local notation "W'(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s true
local notation "JetKernel(" a ", " hI ", " hs ", " u ")" =>
  (∀ f, f ∈ Θ(a, hI, hs) ↔ ∀ j, spectralSobolevPairing (F := F) f (u j) = 0)
local notation "JetInterpolation(" J ", " a ", " hI ", " hs ", " u ")" =>
  (∃ v : J → W(_, _, _), (∀ i, spectralSobolevPairing (F := F) (v i) (u i) = 1) ∧
    (∀ i j, i ≠ j → spectralSobolevPairing (F := F) (v i) (u j) = 0) ∧
    Dense (Submodule.span ℂ (range (fun i ↦ (Θ(a, hI, hs)).mkQ (v i))) :
      Set (spectralSobolevQuotient F a hI hs)))


/-- Paper: Theorem 10.2.2.1, p. 446. Vanishing of every admitted moment
places a vector in the closed span of the weighted polar-free theta tests.
Deviation: At the boundary the admitted orders satisfy the strict inequality
`2k+1<s`. The proof uses Mellin division and weighted Sobolev approximation. -/
theorem spectralStripJet_reverse_synthesis (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (y : W(-α,α,s)) (hy : ∀ j : SpectralStripJetIndex χ a α s,
      spectralSobolevPairing y ((stripU(χ, hα, hs)) j) = 0) : y ∈ Θ(a, neg_le_self hα, hs) := by
  apply spectralStripJet_reverse_of_radial_lifts χ hχ hα hs _ y hy
  intro ω p v hv hz
  obtain ⟨e, hd, he⟩ := exists_chart hα hs
  obtain ⟨L, hL⟩ := stripTail_radial_lift (χ ω) hα hs
  have hr := thetaProducts_detect_radial χ hχ ω hα hs e he p v hv hz
  have hEq : L p = v := Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq ((hL p).trans hv.symm))
  exact hEq ▸ spectralStrip_radial_synthesis (χ ω) a α s hα hs e hd he L hL p hr

/-- Paper: Theorem 10.2.2.1, p. 446. Every vector annihilated by the surviving
strip jets admits weighted polar-free theta approximants in the strip Sobolev norm.
Deviation: Boundary moments obey the strict reciprocal-weight cutoff. -/
theorem spectralStripJet_approximation_direct (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a (-α) α s (stripI(hα)) hs).exists.choose
    ∀ y : W(-α, α, s), (∀ j, spectralSobolevPairing y (u j) = 0) → ∀ ε > (0 : ℝ),
      ∃ f : adelePolarSubspace F, ‖y - E (Submodule.Quotient.mk f)‖ < ε := by
  intro u E y hy ε hε
  have h := spectralStripJet_reverse_synthesis χ _hχ hα hs y hy
  change y ∈ closure (E.toLinearMap.range : Set W(-α, α, s)) at h
  obtain ⟨_, ⟨q, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨f, (dist_eq_norm y (E (Submodule.Quotient.mk f))).symm.trans_lt hdist⟩

/-- Paper: Theorem 10.2.2.1, p. 446. The geometric theta closure is the
common kernel of the surviving jets, with the corrected boundary condition. -/
theorem spectralStripJet_commonKernel_direct (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let u : SpectralStripJetIndex χ a α s → W'(-α, α, s) := stripU(χ, hα, hs)
    JetKernel(a, stripI(hα), hs, u) := by
  intro u y
  exact ⟨spectralStripJet_commonKernel_forward χ hα hs y, spectralStripJet_reverse_synthesis χ _hχ hα hs y⟩

/-- Paper: Theorem 10.2.2.1, p. 446. There are individual biorthogonal interpolants
with dense span in the geometric quotient for the corrected strip index. -/
theorem spectralStripJet_denseInterpolants_direct (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let u : J → W'(-α, α, s) := stripU(χ, hα, hs)
    JetInterpolation(J, a, stripI(hα), hs, u) := by
  intro J u
  let v (i : J) := (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose
  refine ⟨v, ?_, ?_, spectralStripJet_dense_quotient_of_reverse χ _hχ hα hs
    (spectralStripJet_reverse_synthesis χ _hχ hα hs)⟩
  · intro i
    simpa only [ite_true] using (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose_spec i
  · intro i j hij
    simpa only [ite_eq_right (Ne.symm hij), ite_eq_right hij] using
      (spectralStripJet_singleInterpolant χ _hχ hα hs i).choose_spec j

/-- Paper: Theorem 10.2.2.1 and Terminology 10.2.2.1, p. 446. The strip
jets represent quotient functionals and admit a Markushevich biorthogonal family.
Deviation: Exclude the divergent endpoint and allow finite or empty enumerations. -/
theorem spectralStripMarkushevichBasis_direct (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let J := SpectralStripJetIndex χ a α s
    let Q := spectralSobolevQuotient F a (neg_nonpos.mpr hα |>.trans hα) hs
    let D := spectralSobolevDualEmbedding F a (neg_nonpos.mpr hα |>.trans hα) hs
    Countable J ∧ ∃ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
      ∀ j, D (Λ j) = (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j)) := by
  exact ⟨spectralStripJet_countable χ a α s, spectralSobolevQuotient_basis_of_interpolation a
    (stripI(hα)) hs (stripU(χ, hα, hs))
    (spectralStripJet_commonKernel_direct χ hχ hα hs) (spectralStripJet_denseInterpolants_direct χ hχ hα hs)⟩

end RiemannMasullo
