module

public import RiemannMasullo.Research.StripNuclearity.IntegratedDivisorialShells
public import RiemannMasullo.Ch12_TraceGeometric.Sec2
import RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # Divisorial shells of the normalized skew diagonal

Use the normalized indentation and first skew diagonal of §12.2. The second
coordinate of this parametrization is an actual idèle, so the disjoint primary
shells can be integrated before summing. The identified total is the
smoothened quotient diagonal for the actual idèlic Tamagawa measures.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "P𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "q𝔽" => QuotientGroup.mk' P𝔽
local notation "μ" => multiplicativeTamagawaMeasure F
local notation "ν" => ideleClassTamagawaMeasure F
local notation "countP" => (Measure.count : Measure P𝔽)
attribute [local instance] instIdeleMeasurableSpaceSec1a instIdeleClassMeasurableSpaceSec1
  instIdeleClassBorelSpaceSec1
local instance idelicShellBorel : BorelSpace I𝔽 := ⟨rfl⟩
local instance idelicShellT2 : T2Space I𝔽 := (ideleGroup_topology F).1
local instance idelicShellLocallyCompact : LocallyCompactSpace I𝔽 := (ideleGroup_topology F).2.1
local instance idelicShellSecondCountable : SecondCountableTopology I𝔽 := by
  let : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) :=
    instSecondCountableTopologyMultiplicativeFiniteAdeleRingRingOfIntegers_riemannMasullo F
  let : SecondCountableTopology (InfiniteAdeleRing F) :=
    instSecondCountableTopologyMultiplicativeInfiniteAdeleRing_riemannMasullo F
  let : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
    inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  let : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
local instance idelicShellDiscrete : DiscreteTopology P𝔽 :=
  SetLike.isDiscrete_iff_discreteTopology.mp (ideleGroup_quotient.{_,0} F).2.2.1
local instance idelicShellCountable : Countable P𝔽 :=
  TopologicalSpace.separableSpace_iff_countable.mp inferInstance
local instance idelicShellHaar : (μ).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.1

set_option quotPrecheck false
local notation "smooth(" U ", " u ")" => dSequenceKernelSmoothening ν (fun n ↦ q𝔽 '' (U n)) u
local notation "skew" => (fun z : I𝔽 × P𝔽 ↦ (((z.2 : I𝔽)⁻¹ * z.1), z.1))
local notation "lift(" b ", " U ", " u ")" => diagonalIndentationLift P𝔽 countP b smooth(U, u)
local notation "m(" D ")" => (((μ).restrict D).prod countP)

/-- Paper: (11.3.1.4), p. 494, and (12.2.2.3)–(12.2.2.4), p. 508. For a
normalized indentation, the successive primary shell masses on the idèlic
skew diagonal sum absolutely to its S-restriction minus the full smoothened
diagonal integral on the idèle class group. Their L¹ masses add up to precisely
the skew mass outside the S-local stratum.
Deviation: The restricted term still uses the normalized global lift on the
chosen fundamental domain; the identification with an S-local trace is M25. -/
theorem hasSum_normalized_idelic_shells_sub_quotient_diagonal
    (S : Finset V) (hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    {D : Set I𝔽} {U : ℕ → Set I𝔽} (hD : IsDiagonalIndentationSituation P𝔽 μ D U)
    {b : I𝔽 → ℝ} (hb : IsIndentation P𝔽 countP b) {u : C𝔽 × C𝔽 → ℂ}
    (hu : LocallyIntegrable u ((ν).prod ν))
    (hreg : ∀ᵐ x ∂ν, (x,x) ∈ dSequenceRegularSet ((ν).prod ν)
      (fun n ↦ (q𝔽 '' U n) ×ˢ (q𝔽 '' U n)) u)
    (hi : Integrable (fun x ↦ smooth(U, u) (x,x)) ν) :
    let Dₛ := (Prod.fst : I𝔽 × P𝔽 → I𝔽) ⁻¹' sLocalDivisorialStratum F S
    let δ := fun n z ↦ divisorialKernelDifference S n (lift(b, U, u)) (skew z)
    (∀ n, Integrable (δ n) (m(D))) ∧
      HasSum (fun n ↦ ∫ z, ‖δ n z‖ ∂m(D)) (∫ z in Dₛᶜ, ‖lift(b, U, u) (skew z)‖ ∂m(D)) ∧
      Summable (fun n ↦ ‖∫ z, δ n z ∂m(D)‖) ∧
      HasSum (fun n ↦ ∫ z, δ n z ∂m(D))
        ((∫ z in Dₛ, lift(b, U, u) (skew z) ∂m(D)) - ∫ x, smooth(U, u) (x,x) ∂ν) := by
  intro Dₛ δ
  have hclosed : IsClosed (P𝔽 : Set I𝔽) := (ideleGroup_quotient.{_,0} F).2.1
  have hskew := integrable_diagonalIndentationLift_left P𝔽 hclosed (ideleClassTamagawaMeasure_isWeil F)
    hD hb hu hreg hi
  obtain ⟨hint, hmass, habs, hsum⟩ := hasSum_integral_divisorialKernelDifference
    (m(D)) S hS (lift(b, U, u)) skew measurable_fst hskew
  have htotal := (integral_prod _ hskew).trans
    (integral_diagonalIndentationLift_left P𝔽 hclosed (ideleClassTamagawaMeasure_isWeil F)
      hD hb hu hreg hi).symm
  exact ⟨hint, hmass, habs, htotal ▸ hsum⟩

end RiemannMasullo
