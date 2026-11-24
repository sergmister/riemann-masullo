module

public import RiemannMasullo.Research.TraceComparison.PhysicalBandTrace
public import RiemannMasullo.AppB_AnalyticNT.Sec7b
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch11_ShellStructure.Sec1b
-- Reuse the polar Fourier approximants and the support estimate for integer insertion.
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b

/-! # Finite-place and Fourier exhaustion of the global geometric space

At bandwidth B, use the finite places whose ideal norms are below B, and bound
the additive Fourier variables at all selected places and the infinite places by B.
Globalizing polar-free tests at these stages and taking closed spans gives an
increasing family in the physical strip. On every compact strip its closed union
is the full theta space. The nonarchimedean transition uses integer-ring indicators.
This supplies an independent global trace approximation for the missing §12.3 on p. 514.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set IsDedekindDomain
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.PhysicalBandTrace

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Z(" S ")" => sAdelePolarSubspace F S
local notation "W(" l ", " r ", " s ")" =>
  CompactIntervalSobolev (ideleClassTamagawaMeasure F) (logIdeleClassNorm F) l r s
local notation "E(" a ", " hI ", " hs ")" =>
  (existsUnique_globalThetaSobolevEmbedding (F := F) a _ _ _ hI hs).exists.choose
local notation "Q" => (Submodule.Quotient.mk : adelePolarSubspace F → GlobalPolarFreeThetaSpace F)

local notation "glob(" S ", " f ")" =>
  (⟨sAdeleSchwartzToGlobal F S (f).val, sAdeleSchwartzToGlobal_mem_polarSubspace (f)⟩ : adelePolarSubspace F)

/-- Closed ambient span of global polar theta generators from the Fourier boxes of §7.3,
using finite places of ideal norm below the same bandwidth. -/
def globalThetaPWBand (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) (B : ℝ) :
    Submodule ℂ W(l, r, s) :=
  (Submodule.span ℂ {u | ∃ S : Finset V, S ⊆ heckePrimesBelow F B ∧ ∃ f : Z(S),
    tsupport (sAdeleSchwartzFourier f.val).val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWBox S B ∧
    E(a, hI, hs) (Q (glob(S, f))) = u}).topologicalClosure

/-- Increasing the common bound enlarges both the finite-place set and every Fourier box. -/
theorem globalThetaPWBand_monotone (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    Monotone (globalThetaPWBand (F := F) a hI hs) := by
  intro B C hBC
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨S, hS, f, hf, rfl⟩
  refine ⟨S, fun {v} hv ↦ (heckePrimesBelow_mem_iff (F := F) v C).mpr
    (((heckePrimesBelow_mem_iff (F := F) v B).mp (hS hv)).trans_le hBC), f, ?_, rfl⟩
  intro x hx
  exact ⟨fun v ↦ ((hf hx).1 v).trans hBC, fun v ↦ ((hf hx).2 v).trans hBC⟩

/-- The closed span of these finite-place, finite-band spaces is exactly the strip
geometric subspace for every compact interval, every twist and nonnegative Sobolev order. -/
theorem globalThetaPWBand_generates (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    (⨆ B, globalThetaPWBand (F := F) a hI hs B).topologicalClosure = globalThetaSobolev F a hI hs := by
  let E := E(a, hI, hs)
  let levels := globalThetaPWBand (F := F) a hI hs
  let D := (iSup levels).topologicalClosure
  have hD : IsClosed (D : Set W(l, r, s)) := Submodule.isClosed_topologicalClosure _
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    apply iSup_le
    intro B
    apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    apply Submodule.span_le.mpr
    rintro _ ⟨S, -, f, -, rfl⟩
    exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self E.toLinearMap _)
  · apply Submodule.topologicalClosure_minimal _ _ hD
    rintro _ ⟨q, rfl⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨S, g, hg⟩ := sAdeleSchwartzToGlobal_exhaustive F f.val
    have hgp : g ∈ Z(S) := (mem_sAdelePolarSubspace _).mpr
      ((sAdeleSchwartzToGlobal_mem_polarSubspace_iff S g).mp (hg.symm ▸ f.property))
    let g₀ : Z(S) := ⟨g, hgp⟩
    have hglob : glob(S, g₀) = f := Subtype.ext hg
    let J (z : Z(S)) := E (Q (glob(S, z)))
    have hglob_cont : Continuous (fun z : Z(S) ↦ glob(S, z)) := by
      apply Continuous.subtype_mk
      exact (sAdeleSchwartzToGlobal_isEmbedding F S).continuous.comp continuous_subtype_val
    have hJ : Continuous J := E.continuous.comp ((Submodule.continuous_mkQ _).comp hglob_cont)
    obtain ⟨v, hv, ht⟩ := sLocalAbsolutePW_fourier_compact_seq_polar g₀
    let u (n : ℕ) : Z(S) := ⟨v n, (hv n).1⟩
    have hu : Tendsto u atTop (𝓝 g₀) := tendsto_subtype_rng.mpr ht
    have hmem (n : ℕ) : J (u n) ∈ D := by
      obtain ⟨b, -, hb⟩ := sLocalAbsolutePW_compact_box (S := S) (hv n).2
      let B := max b ((∑ v ∈ S, (v.asIdeal.absNorm : ℝ)) + 1)
      apply Submodule.le_topologicalClosure _ ((le_iSup levels B) ?_)
      apply Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
      refine ⟨S, fun {v} hvS ↦ ?_, u n, ?_, rfl⟩
      · apply (heckePrimesBelow_mem_iff (F := F) v B).mpr
        have hle := Finset.single_le_sum (f := fun v : V ↦ (v.asIdeal.absNorm : ℝ))
          (fun _ _ ↦ by positivity) hvS
        exact (lt_add_of_le_of_pos hle zero_lt_one).trans_le (le_max_right ..)
      · intro x hx
        exact ⟨fun v ↦ ((hb hx).1 v).trans (le_max_left ..),
          fun v ↦ ((hb hx).2 v).trans (le_max_left ..)⟩
    have hlim := hD.mem_of_tendsto (hJ.continuousAt.tendsto.comp hu) (Eventually.of_forall hmem)
    change E (Q (glob(S, g₀))) ∈ D at hlim
    change E (Q f) ∈ D
    simpa only [hglob] using hlim

/-- The closed span at one specified finite stage and one additive Fourier bandwidth. -/
def globalThetaPWStage (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (S : Finset V) (B : ℝ) : Submodule ℂ W(l, r, s) :=
  (Submodule.span ℂ {u | ∃ f : Z(S), tsupport (sAdeleSchwartzFourier f.val).val ⊆
    Multiplicative.toAdd ⁻¹' sLocalPWBox S B ∧ E(a, hI, hs) (Q (glob(S, f))) = u}).topologicalClosure

private theorem differentRadius_bounded :
    ∃ D : ℝ, ∀ v : V,
      (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) ≤ D := by
  classical
  let d (v : V) := (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))
  have h : (mulSupport d).Finite := by
    apply (Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).subset
    intro v hv
    by_contra hn
    exact hv (by simp [d, multiplicity_eq_zero_of_not_dvd hn])
  obtain ⟨C, hC⟩ := (h.image d).bddAbove
  refine ⟨max 1 C, fun v ↦ ?_⟩
  by_cases hv : v ∈ mulSupport d
  · exact (hC (mem_image_of_mem d hv)).trans (le_max_right ..)
  · exact (show d v = 1 from not_not.mp hv).le.trans (le_max_left ..)

/-- Beyond a constant depending only on the field different, the accumulating band is
exactly the ordinary Fourier box at the single finite stage of all primes below B.
Integer insertion contributes an inverse-different bound at each newly included place. -/
theorem eventually_globalThetaPWBand_eq_stage (a : ℝ) {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s) :
    ∀ᶠ B : ℝ in atTop, globalThetaPWBand (F := F) a hI hs B =
      globalThetaPWStage a hI hs (heckePrimesBelow F B) B := by
  obtain ⟨D, hD⟩ := differentRadius_bounded (F := F)
  filter_upwards [eventually_ge_atTop D] with B hB
  let T := heckePrimesBelow F B
  apply le_antisymm <;> apply Submodule.topologicalClosure_mono <;> apply Submodule.span_mono
  · rintro _ ⟨S, hS, f, hf, rfl⟩
    let g : Z(T) := ⟨sAdeleSchwartzTransition F hS f.val, (sLocalAbsolutePW_insert_polar hS f.val).mpr f.property⟩
    have hglob : glob(T, g) = glob(S, f) := Subtype.ext (DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hS) f.val)
    refine ⟨g, ?_, congrArg (fun z ↦ E(a, hI, hs) (Q z)) hglob⟩
    let : T2Space (SAdeleRing F T) :=
      inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) × ((v : T) → v.val.adicCompletion F)))
    apply closure_minimal _ ((isCompact_sLocalPWBox (S := T) B).isClosed.preimage continuous_toAdd)
    intro x hx
    obtain ⟨h₁, h₂⟩ := sLocalAbsolutePW_fourier_transition_support hS f.val x.toAdd hx
    have hy := hf (subset_tsupport _ h₁)
    refine ⟨hy.1, fun v ↦ ?_⟩
    by_cases hv : v.val ∈ S
    · exact hy.2 ⟨v.val, hv⟩
    · exact (h₂ ⟨v, hv⟩).trans ((hD v.val).trans hB)
  · rintro _ ⟨f, hf, rfl⟩
    exact ⟨T, le_rfl, f, hf, rfl⟩

instance instCompleteSpace_globalThetaPWBand (a : ℝ) {l r s : ℝ}
    (hI : l ≤ r) (hs : 0 ≤ s) (B : ℝ) : CompleteSpace (globalThetaPWBand (F := F) a hI hs B) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance instCompleteSpace_globalThetaPWStage (a : ℝ) {l r s : ℝ}
    (hI : l ≤ r) (hs : 0 ≤ s) (S : Finset V) (B : ℝ) :
    CompleteSpace (globalThetaPWStage (F := F) a hI hs S B) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

private theorem starProjection_congr {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {K J : Submodule ℂ H} [K.HasOrthogonalProjection] [J.HasOrthogonalProjection] (h : K = J) :
    K.starProjection = J.starProjection := by subst J; rfl

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "physicalBands(" hα ", " hs ")" =>
  globalThetaPWBand (F := F) (1/2) (neg_le_self hα) (zero_le_one.trans (le_of_lt hs))
local notation "physicalFormula(" hα ", " hs ", " φ ", " hφ ", " ε ", " ρ ", " hε ", " hρ ")" =>
  exists_physicalBandTrace (F := F) hα hs φ hφ (physicalBands(hα, hs))
    (globalThetaPWBand_monotone _ _ _) (globalThetaPWBand_generates _ _ _) ε ρ hε hρ

/-- For the concrete expanding finite-place Fourier boxes, the geometric band limit of
the physical trace is minus the localized spectral trace. The subsequent physical limit
and every diagonal selection above the radius-dependent thresholds give minus the
unlocalized spectral trace. This holds over every number field for nonnegative strip
half-width and Sobolev order greater than one. -/
theorem exists_globalThetaPWBandTrace {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0)
    (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    type_of% physicalFormula(hα, hs, φ, hφ, ε, ρ, hε, hρ) :=
  physicalFormula(hα, hs, φ, hφ, ε, ρ, hε, hρ)

local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "A(" hα ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (neg_le_self hα) hs φ
local notation "P(" hα ", " hs ")" => spectralProjection (F := F) (1/2) hα hs
local notation "M(" α ", " s ", " hc ")" => modulatedCutoffOperator m𝔽
  ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logIdeleClassNorm F g))) hc
local notation "stage(" hα ", " hs ", " B ")" =>
  globalThetaPWStage (F := F) (1/2) (neg_le_self hα) hs (heckePrimesBelow F B) B

/-- For a compact Bruhat test that vanishes at the identity, take the additive Fourier
box of bandwidth B at the single stage of all finite primes of norm strictly below B.
At every fixed admissible physical cutoff the traces tend to minus the localized spectral
trace. Exhausting the physical cutoff gives minus the full spectral trace, and the same
limit is attained at integer physical radii by every sufficiently large choice of bands. -/
theorem exists_globalThetaPWStageTrace {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (φ : BruhatCompactSupport C𝔽) (hφ : φ.val 1 = 0)
    (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    let hs₀ := zero_le_one.trans hs.le
    let A := A(hα, hs₀, φ)
    let P := P(hα, hs₀)
    ∃ (hAP : IsNuclearOperator (A.comp P)) (T : ℝ → nuclearEndomorphisms W(-α, α, s)),
      (∀ R (hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R)), 0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R →
        (T R).val = (M(α, s, hc)).comp A) ∧
      (∀ R, hilbertTrace (T R) = 0) ∧
      (∀ R, Tendsto (fun B ↦ hilbertTrace (rightProduct (T R) (stage(hα, hs₀, B)).starProjection))
        atTop (𝓝 (-hilbertTrace (rightProduct (T R) P)))) ∧
      Tendsto (fun R ↦ -hilbertTrace (rightProduct (T R) P)) atTop
        (𝓝 (-hilbertTrace (H := W(-α, α, s)) ⟨A.comp P, hAP⟩)) ∧
      ∃ b : ℕ → ℝ, Tendsto b atTop atTop ∧ ∀ B : ℕ → ℝ, (∀ᶠ n in atTop, b n ≤ B n) →
        Tendsto (fun n : ℕ ↦ hilbertTrace (rightProduct (T (n : ℝ)) (stage(hα, hs₀, B n)).starProjection))
          atTop (𝓝 (-hilbertTrace (H := W(-α, α, s)) ⟨A.comp P, hAP⟩)) := by
  intro hs₀ A P
  have hstage := eventually_globalThetaPWBand_eq_stage (F := F) (1/2) (neg_le_self hα) hs₀
  obtain ⟨hAP, T, hcut, hzero, hfix, hlim, b, hb, hdiag⟩ :=
    exists_globalThetaPWBandTrace (F := F) hα hs φ hφ ε ρ hε hρ
  refine ⟨hAP, T, hcut, hzero, ?_, hlim, b, hb, ?_⟩
  · intro R
    apply (hfix R).congr'
    filter_upwards [hstage] with B he
    rw [starProjection_congr he]
  · intro B hB
    apply (hdiag B hB).congr'
    filter_upwards [(tendsto_atTop_mono' _ hB hb).eventually hstage] with n he
    rw [starProjection_congr he]

end RiemannMasullo.PhysicalBandTrace
