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

/-- Paper: Proposition 12.2.2.2(2), p. 508. Summing the skew lift over all
principal translates recovers the diagonal value at each individual idèle. -/
theorem integral_normalized_idelic_skew_fiber {b : I𝔽 → ℝ} (hb : IsIndentation P𝔽 countP b)
    (u : C𝔽 × C𝔽 → ℂ) (x : I𝔽) :
    (∫ h : P𝔽, diagonalIndentationLift P𝔽 countP b u (((h : I𝔽)⁻¹ * x), x) ∂countP) =
      u (q𝔽 x, q𝔽 x) := by
  let β : P𝔽 → ℝ := fun k ↦ b ((k : I𝔽)⁻¹ * x)
  have hi : Integrable β countP := (hb.2.2.2 x).1
  have h1 : ∫ k, β k ∂countP = 1 := (hb.2.2.2 x).2
  have hprod : Integrable (fun z : P𝔽 × P𝔽 ↦ β (z.1 * z.2) * β z.2) ((countP).prod countP) :=
    (measurePreserving_mul_prod countP countP).integrable_comp_of_integrable (hi.mul_prod hi)
  have hw (h : P𝔽) : diagonalIndentationWeight P𝔽 countP b ((h : I𝔽)⁻¹ * x, x) =
      ∫ k, β (h * k) * β k ∂countP := by
    simp only [diagonalIndentationWeight, β, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
  have hweight : (∫ h : P𝔽, diagonalIndentationWeight P𝔽 countP b ((h : I𝔽)⁻¹ * x, x) ∂countP) = 1 := by
    simp_rw [hw]
    rw [integral_integral_swap (f := fun h k ↦ β (h * k) * β k) hprod]
    simp_rw [integral_mul_const, integral_mul_right_eq_self, h1, one_mul]
    exact h1
  have hq (h : P𝔽) : q𝔽 ((h : I𝔽)⁻¹ * x) = q𝔽 x := by
    have he : q𝔽 (h : I𝔽) = 1 := (QuotientGroup.eq_one_iff _).mpr h.property
    rw [map_mul, map_inv, he, inv_one, one_mul]
  simp only [diagonalIndentationLift, Prod.map_apply, hq]
  rw [integral_mul_const, integral_complex_ofReal, hweight, Complex.ofReal_one, one_mul]

/-- Paper: (11.3.1.4), p. 494, and Proposition 12.2.2.2(2), p. 508. Each
integrable normalized shell integral is the integral of the quotient diagonal
weighted by its two idèlic indicators on the chosen representatives. -/
theorem integral_normalized_idelic_shell_eq {b : I𝔽 → ℝ} (hb : IsIndentation P𝔽 countP b)
    (u : C𝔽 × C𝔽 → ℂ) (S : Finset V) (k : ℕ) (m : Measure I𝔽) [SFinite m]
    (hi : Integrable (fun z : I𝔽 × P𝔽 ↦
      divisorialKernelDifference S k (diagonalIndentationLift P𝔽 countP b u) (skew z))
      (m.prod countP)) :
    (∫ z : I𝔽 × P𝔽, divisorialKernelDifference S k (diagonalIndentationLift P𝔽 countP b u)
      (skew z) ∂m.prod countP) =
      ∫ x, (divisorialIndicator (primaryDivisorialPlaces F S (k+1)) x -
        divisorialIndicator (primaryDivisorialPlaces F S k) x) * u (q𝔽 x, q𝔽 x) ∂m := by
  rw [integral_prod _ hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [divisorialKernelDifference, integral_const_mul, integral_normalized_idelic_skew_fiber hb]

/-- Paper: Proposition 12.2.2.2(2), p. 508, and the restriction on p. 520. The
normalized skew mass over any idèlic first-coordinate mask is exactly the
quotient diagonal evaluated on those representatives. The mask remains on the
chosen fundamental domain. -/
theorem integral_normalized_idelic_skew_restrict {b : I𝔽 → ℝ} (hb : IsIndentation P𝔽 countP b)
    (u : C𝔽 × C𝔽 → ℂ) (A : Set I𝔽) (m : Measure I𝔽) [SFinite m]
    (hi : Integrable (fun z : I𝔽 × P𝔽 ↦ diagonalIndentationLift P𝔽 countP b u (skew z))
      (m.prod countP)) :
    (∫ z in (Prod.fst : I𝔽 × P𝔽 → I𝔽) ⁻¹' A,
      diagonalIndentationLift P𝔽 countP b u (skew z) ∂m.prod countP) =
      ∫ x in A, u (q𝔽 x, q𝔽 x) ∂m := by
  have hA : (Prod.fst : I𝔽 × P𝔽 → I𝔽) ⁻¹' A = A ×ˢ univ := by ext z; simp
  rw [hA, setIntegral_prod _ hi.integrableOn]
  simp only [Measure.restrict_univ, integral_normalized_idelic_skew_fiber hb]

end RiemannMasullo
