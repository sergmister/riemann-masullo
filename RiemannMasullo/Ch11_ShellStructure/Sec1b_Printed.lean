module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec1b

import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# Printed claims in §11.1.2

The repaired statements are in Sec1b.lean.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ω[" F ", " χ "]" =>
  (χ).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    (ideleClassNorm F).ker →ₜ* C[F])
local notation "norm[" F "]" => fun g : C[F] ↦ ((ideleClassNorm F g).val : ℝ)
local notation "band[" b ", " Λ "]" => sLocalCarvingBand b Λ
local notation "bandMeasurable[" b ", " Λ "]" => measurableSet_sLocalCarvingBand b Λ

local instance instIdeleClassMeasurableSpaceSec1bPrinted (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace C[F] := borel _
local instance instIdeleClassBorelSpaceSec1bPrinted (F : Type*) [Field F] [NumberField F] :
    BorelSpace C[F] := ⟨rfl⟩

/-- Paper: Theorem 11.1.2.1(2), p. 480, strictness in (11.1.2.6).
The printed claim requires a strictly smaller closed cutoff stage along a
subsequence of every increasing exhaustion by radii, for each cutoff choice. -/
def Printed.sLocalCutoffCarving_strictSubsequence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ s : ℝ, 2 * (Module.finrank ℚ F : ℝ) ≤ s →
    ∀ i i' : SLocalCarvingIndex (F := F) S, i < i' →
    (∃ p : ℕ, p.Prime ∧ (∀ v ∈ i.val, (p : 𝓞 F) ∉ v.asIdeal) ∧
      ∃ v ∈ i'.val, (p : 𝓞 F) ∈ v.asIdeal) →
    ∀ (twoSided : Bool) (Λ : ℕ → ℝ), (∀ k, 0 < Λ k) → Monotone Λ →
      Tendsto Λ atTop atTop →
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ m,
        sLocalCutoffCarving s (ω[F, χ]) i'.val (band[twoSided, Λ (k m)])
            (bandMeasurable[twoSided, Λ (k m)]) <
          sLocalCutoffCarving s (ω[F, χ]) i.val (band[twoSided, Λ (k m)])
            (bandMeasurable[twoSided, Λ (k m)])

/-- Paper: Theorem 11.1.2.1(2), p. 480, strictness in (11.1.2.6).
Take F = ℚ, the trivial character, S with no finite places, s = 2, the empty
index and the singleton at 2. Use bounded cutoffs with radii k + 2. On the
logarithmic line the principal value is I − T, where T translates by log 2
up to sign. The theta test space is translation invariant. Applying I − T
to a finite sum of translates of a test gives the test minus a distant
translate, which tends to zero after cutting off to any bounded window.
Thus the two closed stages are equal at every radius in the sequence. -/
theorem Printed.sLocalCutoffCarving_strictSubsequence_false :
    ¬ Printed.sLocalCutoffCarving_strictSubsequence := by sorry

/-- Paper: Theorem 11.1.2.1(3), p. 480, (11.1.2.7). The printed
generators are the raw cutoff theta series for all tests with both
polar values zero. Each raw generator must represent a weighted L² vector,
and the limit must be the closed span of those vectors. -/
def Printed.sLocalCarvingLimit_eq_rawClosedSpan : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ (s : ℝ), 2 * (Module.finrank ℚ F : ℝ) ≤ s →
    ∀ (twoSided : Bool) (Λ : ℝ), 0 < Λ →
      let J := band[twoSided, Λ]
      let E := norm[F] ⁻¹' J
      let ν := (ideleClassTamagawaMeasure F).withDensity
        (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm[F] g))))
      let raw := fun f ↦ E.indicator (sLocalCarvingTheta S f)
      (∀ f : sAdelePolarSubspace F S, MemLp (raw f.val) 2 ν) ∧
        sLocalCarvingLimit s (ω[F, χ]) S J (bandMeasurable[twoSided, Λ]) =
          (Submodule.span ℂ {u : IdeleClassZeroLineSobolev F s |
            ∃ f : sAdelePolarSubspace F S, (u : C[F] → ℂ) =ᵐ[ν] raw f.val}).topologicalClosure

/-- Paper: Theorem 11.1.2.1(3), p. 480, (11.1.2.7).
Take F = ℚ, the even quadratic character modulo 5, S with finite part {5},
s = 2 and the two-sided cutoff with radius 2. Take the local test with 5-adic
factor 1_{ℤ₅} and an even real bump supported at absolute values in (3/4, 5/4),
positive near 1. Subtract an even bump at absolute values in (1/4, 1/3)
to cancel the additive integral. The resulting raw theta is norm-one invariant
and is nonzero near norm 1, where the only contributing rationals are ±1.
It cannot belong to the nontrivial isotype of the left side. -/
theorem Printed.sLocalCarvingLimit_eq_rawClosedSpan_false :
    ¬ Printed.sLocalCarvingLimit_eq_rawClosedSpan := by sorry

/-- Paper: (11.1.2.9), p. 481. The printed lower-half-line integral is
claimed to compute the cutoff norm for both choices of cutoff. -/
def Printed.sLocalCarving_cutoff_norm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ (s : ℝ), 2 * (Module.finrank ℚ F : ℝ) ≤ s →
    ∀ (twoSided : Bool) (Λ : ℝ), 0 < Λ →
    ∀ f : adelePolarSubspace F,
      let μ := ideleClassTamagawaMeasure F
      let ν := μ.withDensity
        (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm[F] g))))
      let m : C[F] →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
      let θ := homogeneousAdelicTheta (ω[F, χ]) f.val
      let u := (memLp_homogeneousTheta_zeroLine s (ω[F, χ]) f).toLp θ
      ‖modulatedAbsoluteCutoffOperator m ν (band[twoSided, Λ]) (bandMeasurable[twoSided, Λ]) u‖ =
        Real.sqrt (∫ g in (norm[F] ⁻¹' Ici Λ⁻¹), ‖θ g‖ ^ 2 *
          (1 + Real.log (norm[F] g) ^ 2) ^ (s / 2) ∂μ)

/-- Paper: (11.1.2.9), p. 481. Use F = ℚ, the trivial character, S with no
finite places, s = 2, and the two-sided radius 2 cutoff. Take the standard
integral factors at the finite places and an even real bump supported at
absolute values in (3, 4), positive near 7/2. Subtract an even bump below
absolute value 1/2, supported away from zero, to cancel the Fourier value at
zero. For norms near 7/2 only the terms ±1 contribute. This gives positive
norm mass in the lower half-line integral outside the bounded cutoff band. -/
theorem Printed.sLocalCarving_cutoff_norm_false :
    ¬ Printed.sLocalCarving_cutoff_norm := by sorry

end RiemannMasullo
