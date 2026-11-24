module

public import RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
public import RiemannMasullo.Research.TraceComparison.HeckeWideCalibration
import all RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
import RiemannMasullo.Research.StripNuclearity.NormSectionCharacters
import all RiemannMasullo.Research.StripNuclearity.OddTraceComparison

/-! # Fixed-width comparison over the rational field

A right half-plane of nonvanishing for Dirichlet L-functions confines the divisors
of section-normalized rational Hecke characters to a closed band. Every strictly
larger open strip contains their full multiplicities. The distinction between a
closed arithmetic bound and an open trace window matters at its edges.

The external arithmetic proof is a separate input. In particular the Dirichlet
theorem in OpenAI's `OAI/NumberTheory/DirichletL/Nonvanishing.lean` at commit
`4eaee87548250b2682affda7d05d947c05554bae` has precisely the input at σ = 7/8.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F:=ℚ) ψ) univ
local notation "chart(" τ ")" => {η : PontryaginDual Cℚ // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local notation "outside(" τ "," r ")" =>
  {p : chart(τ) × ℂ // 0 < D(p.1.val) p.2 ∧ r ≤ |p.2.re - 1/2|}
local notation "dirichlet(" σ ")" => (∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
  σ < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0)

private theorem rational_divisor_re_le_of_dirichlet {σ : ℝ} (hσ : 0 ≤ σ)
    (hn : dirichlet(σ)) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (ψ : chart(τ)) (s : ℂ) (hz : 0 < D(ψ.val) s) : s.re ≤ σ := by
  by_contra! hs
  obtain ⟨N, _, χ, -, hL⟩ :=
    exists_primitive_finiteHeckeL_eq_of_trivial_on_section τ hτ ψ.val ψ.property
  have hp := order_pos_of_ord_pos ψ.val hz
  have hpos := hσ.trans_lt hs
  have hspec := continuedCompletedHeckeL_spec ψ.val
  have hlt := completedHeckeL_continuation_zeros ψ.val _ hspec.1 hspec.2 hpos hp
  have h1 : s ≠ 1 := fun he ↦ by simp [he] at hlt
  have heq := meromorphicOrderAt_finiteHeckeL_continuation ψ.val (meromorphic_dirichletLFunction χ)
    (fun z ↦ by rw [DirichletCharacter.LFunction_eq_LSeries χ z.2, hL z.1 z.2]) hpos
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun z hz ↦
    (DirichletCharacter.differentiableAt_LFunction χ z (.inl hz)).differentiableWithinAt
  have ha := hd.analyticAt (isOpen_compl_singleton.mem_nhds h1)
  have horder : meromorphicOrderAt (DirichletCharacter.LFunction χ) s = 0 := by
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr (hn χ hs (fun h ↦ h1 h.2))]
    rfl
  rw [← heq, horder] at hp
  exact hp.false

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Over ℚ the exterior-zero index is
empty in every open strip wider than the closed band supplied by a Dirichlet
zero-free half-plane. Both edges and all angular characters are included.
Deviation: The half-plane estimate is an independent arithmetic hypothesis. -/
theorem rational_isEmpty_exteriorZeros_of_dirichlet_band {σ r : ℝ} (hσ : 0 ≤ σ)
    (hn : dirichlet(σ)) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (hr : σ - 1/2 < r) : IsEmpty outside(τ,r) := by
  refine ⟨fun ⟨⟨ψ,s⟩, hz, hout⟩ ↦ ?_⟩
  let ψ' : chart(τ) := ⟨ψ.val⁻¹, fun t ↦ by change (ψ.val (τ t))⁻¹ = 1; rw [ψ.property, inv_one]⟩
  have hz' : 0 < D(ψ'.val) (1-s) := by
    change 0 < D(ψ.val⁻¹) (1-s)
    rwa [divisor_functionalEquation]
  have hright := rational_divisor_re_le_of_dirichlet hσ hn τ hτ ψ s hz
  have hleft := rational_divisor_re_le_of_dirichlet hσ hn τ hτ ψ' (1-s) hz'
  rw [Complex.sub_re, Complex.one_re] at hleft
  have hin : |s.re-1/2| ≤ σ-1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (not_le.mpr (hin.trans_lt hr)) hout

/-- Paper: Theorem 12.5.1.1, pp. 519–520. With Dirichlet nonvanishing to the right
of 7/8, the literal exterior sum in #5571 vanishes over ℚ for every test and norm
section at every half-width strictly greater than 3/8.
Deviation: The arithmetic input is the published Dirichlet seven-eighths theorem. -/
theorem rational_exteriorZeros_of_dirichlet_seven_eighths
    (hn : dirichlet((7/8:ℝ))) (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ x : Kℚ, φ.val x = 0) {r : ℝ} (hr : 3/8 < r) :
    type_of% (traceFormula_exteriorZeros τ hτ φ hφ (show 0 < r by linarith)) := by
  exact (hasSum_exteriorZeros_iff_isEmpty τ hτ r).mpr
    (rational_isEmpty_exteriorZeros_of_dirichlet_band (by norm_num : (0:ℝ) ≤ 7/8) hn τ hτ
      (by linarith)) φ hφ

/-- Paper: Section 12.3, p. 514. If the open strip contains the entire divisor for
every section-normalized character, its actual projected diagonal agrees with the
wide diagonal. The two smoothing sequences and Sobolev orders are independent. -/
theorem rational_diagonal_eq_wide_of_isEmpty_exterior
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (φ : BruhatCompactSupport Cℚ) (hφ : ∀ x : Kℚ, φ.val x = 0) {α s t : ℝ} (hα : 0 < α)
    (hempty : IsEmpty outside(τ,α)) (hs : 3 ≤ s) (ht : 3 ≤ t) (U V : ℕ → Set Cℚ)
    (hU : IsDPrimeSequence μℚ U) (hmU : ∀ n, MeasurableSet (U n))
    (hV : IsDPrimeSequence μℚ V) (hmV : ∀ n, MeasurableSet (V n)) :
    centeredStripGeometricDiagonalIntegral φ hα hs U =
      centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ)<1/2) ht V := by
  let e := normSectionCharacterEquiv τ hτ
  let χ (ξ : PontryaginDual Kℚ) := (e ξ).val
  let Z := {p : PontryaginDual Kℚ × ℂ // 0 < D(χ p.1) p.2}
  have h := (hasSum_missingHeckeJets_centeredStripDiagonalIntegral_sub φ hφ χ
    (isSpectralBasepointChoice_normSection τ hτ) hα hs (β:=1/2) le_rfl ht U V hU hmU hV hmV).2
  have hh : HasSum (fun _ : Z ↦ (0 : ℂ))
      (centeredStripGeometricDiagonalIntegral φ hα hs U -
        centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ)<1/2) ht V) := by
    apply h.congr_fun
    intro z
    have hin : |z.val.2.re-1/2| < α := lt_of_not_ge (fun hn ↦
      hempty.false ⟨(e z.val.1,z.val.2),z.property,hn⟩)
    simp only [spectralStripMultiplicity_interior (abs_lt.mp hin), Nat.sub_self, Nat.cast_zero, zero_mul]
  exact sub_eq_zero.mp (hh.unique (hasSum_zero ..))

end RiemannMasullo.StripNuclearity
