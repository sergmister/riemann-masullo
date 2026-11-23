module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1

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

/-- Paper: (10.3.1.18), p. 451. For F = ℚ use the trivial base character,
a = 1/2 and s = 2. Take pairs of simple critical-line zeta zeros with
ordinates t and u tending arbitrarily close. The two cutoffs agree at s = 2.
The zeroth jets have the same positive norm and their difference tends to
zero by dominated convergence in the reciprocal Sobolev weight. Biorthogonality gives
1 ≤ ‖Λₜ − Λᵤ‖ ‖ψₜ‖, forcing the paired norm products to be unbounded. -/
theorem Printed.spectralLineJet_uniformBiorthogonalBound_false :
    ¬ Printed.spectralLineJet_uniformBiorthogonalBound := by sorry

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

/-- Paper: Theorem 10.3.1.1(3), p. 449. For F = ℚ let the base character
θ be induced by the primitive Dirichlet character modulo 5 with θ(2) = i.
Take s = 2, a+it a nontrivial zero of its completed L-function and
ω = (θ|C¹)⁻¹. Multiply the conjugate of θ(g)|g|^(it) by a nonzero
nonnegative smooth bump in log |g|. This test has left-translation weight
ω⁻¹. The zeroth jet function has weight ω, and the associated bilinear
functional detects the ω⁻¹-isotype. Its transpose eigenvalue is the positive
integral of the bump, and it annihilates the ω-isotype. -/
theorem Printed.spectralLineConvolution_conjugateWeight_range_false :
    ¬ Printed.spectralLineConvolution_conjugateWeight_range := by sorry

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
