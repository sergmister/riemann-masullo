module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # False assertions in §10.4.3 -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "logNorm(" F ")" => (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "h₀" => le_refl (0 : ℝ)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "w(" F ", " α ", " s ")" => (fun g : C𝔽(F) ↦
  intervalSobolevDensity (-α) α s (logNorm(F) g))
local notation "W(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s
local notation "W'(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s true
local notation "A(" F ", " hα ", " hs ", " φ ")" =>
  hardySobolevTestAction (μ(F)) m𝔽(F) _ _ _ (hStrip(hα)) hs φ
local notation "ν(" F ", " α ", " s ")" =>
  ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g))
local notation "ν'(" F ", " α ", " s ")" =>
  ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g)⁻¹)
local notation "sourceFirst(" F ", " α ", " s ")" =>
  Lp ℂ 2 ((ν'(F, α, s)).prod (ν(F, α, s)))
local notation "tensor(" F ", " α ", " s ")" =>
  Completion (ProjectiveTensor W'(F, α, s) W(F, α, s))
local notation "printedClass(" F ", " α ", " s ", " hα ", " hs ", " K ")" =>
  Lp.compMeasurePreserving Prod.swap
    (Measure.measurePreserving_swap (μ := ν'(F, α, s)) (ν := ν(F, α, s)))
    (sobolevProjectiveKernelClass (F := F) hα hs K)

/-- Paper: (10.4.3.1), p. 465. The displayed polynomial is claimed to
regularize the completed Hecke L-function for every unitary character.
Removable values are filled in according to the meromorphic convention of §7.1. -/
def Printed.unshiftedHeckeRegularization_entire : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)),
    Differentiable ℂ (toMeromorphicNFOn (fun z : ℂ ↦
      (z * (z - 1) / 2) ^ (if ∀ g : C₁(F), χ g.val = 1 then (1 : ℕ) else 0) *
        continuedCompletedHeckeL χ z) univ)

/-- Paper: (10.4.3.1), p. 465. For F = ℚ and χ = |·|^i the completed
L-function is completed zeta at z + i. Its pole at 1 − i survives
multiplication by z(z − 1)/2, which is nonzero there. -/
theorem Printed.unshiftedHeckeRegularization_entire_false :
    ¬ Printed.unshiftedHeckeRegularization_entire := by
  intro h
  let c := ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) Complex.I
  have hunit (g : C𝔽(ℚ)) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I)‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let χ : PontryaginDual C𝔽(ℚ) :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hunit g)⟩
      map_one' := Subtype.ext c.map_one
      map_mul' := fun g k ↦ Subtype.ext (c.map_mul g k)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hk (g : C₁(ℚ)) : χ g.val = 1 := by
    apply Subtype.ext
    change (1 : ℂ) * ((((ideleClassNorm ℚ g.val).val : ℝ) : ℂ) ^ Complex.I) = 1
    rw [MonoidHom.mem_ker.mp g.property]
    simp
  have htwist : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
      (-Complex.I * ((-1 : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one, neg_neg]
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hker : χ.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype = 1 := by
    ext1 g
    exact hk g
  obtain ⟨t, ht, -⟩ := completedHeckeL_continuation_simplePoles χ _ hL hEq hker
  have ht' := (existsUnique_ideleClassNormTwist χ hker).unique ht.1 htwist
  have hpole : meromorphicOrderAt (continuedCompletedHeckeL χ) (1 - Complex.I) = -1 := by
    simpa [ht', sub_eq_add_neg] using ht.2.2.1
  let P := fun z : ℂ ↦ z * (z - 1) / 2
  have hP : Differentiable ℂ P := by
    dsimp [P]
    fun_prop
  have hPne : P (1 - Complex.I) ≠ 0 := by
    dsimp [P]
    apply div_ne_zero (mul_ne_zero _ _) (by norm_num)
    · intro he
      have := congrArg Complex.re he
      norm_num at this
    · simp
  have hentire := h ℚ χ
  simp only [ite_eq_left hk, pow_one] at hentire
  change Differentiable ℂ (toMeromorphicNFOn (P * continuedCompletedHeckeL χ) univ) at hentire
  have hnonneg := (hentire.analyticAt (1 - Complex.I)).meromorphicOrderAt_nonneg
  have hm : MeromorphicOn P univ := fun z _ ↦ (hP.analyticAt z).meromorphicAt
  rw [meromorphicOrderAt_toMeromorphicNFOn (hm.mul hL.meromorphicOn) (mem_univ _),
    meromorphicOrderAt_mul_of_ne_zero (hP.analyticAt _) hPne, hpole] at hnonneg
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hnonneg

/-- Paper: (10.4.3.5), p. 466. For a fixed character and shift, a unique
family of isotypic exponential-decay tests is biorthogonal to the zero jets.
The functional label uses the unshifted zero, as in the displayed formula. -/
def Printed.spectralSchwartzBiorthogonal_unique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (a : ℝ),
    let ι : C₁(F) →ₜ* C𝔽(F) := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
    let E := ↥(modulatedDecayIsotype m𝔽(F) univ (mem_univ 0) (χ.comp ι))
    let J := {j : ℂ × ℕ // j.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + j.1)).untop₀.toNat}
    ∃! ψ : J → E, ∀ j j' : J,
      (∫ g, (ψ j').val.val g * ideleClassNormTwist χ ((a : ℂ) + j.val.1) g *
        (logNorm(F) g : ℂ) ^ j.val.2 ∂(μ(F))) = if j = j' then 1 else 0

/-- Paper: (10.4.3.5), p. 466. For F = ℚ, χ = 1 and a = 0, add the
theta function of the rational test with finite factor 1_{ℤ̂} and archimedean
factor exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²) to any claimed biorthogonal
vector. This nonzero test has zero values under every zeta jet by divisibility
of its Mellin transform. Its theta function is nonzero at large norm. -/
theorem Printed.spectralSchwartzBiorthogonal_unique_false :
    ¬ Printed.spectralSchwartzBiorthogonal_unique := by sorry

local notation "represents(" F ", " α ", " s ", " B ", " k ")" =>
  (∀ u : W(F, α, s), ∀ᵐ x ∂(μ(F)),
    Integrable (fun y ↦ k (x, y) * u y) (μ(F)) ∧
      B u x = ∫ y, k (x, y) * u y ∂(μ(F)))
local notation "printedWeight(" F ", " α ", " s ", " ρ ", " k ")" =>
  (fun p : C𝔽(F) × C𝔽(F) ↦ (ρ p.1 * (w(F, α, s) p.2)⁻¹ ^ 2 : ℝ) • k p)

/-- Paper: (10.4.3.24)–(10.4.3.25), p. 470. The tensor image in the
source-first product is claimed to be the unique class whose displayed
weighted integral gives the spectral operator, with k evaluated at (x,y). -/
def Printed.spectralLineKernel_extraWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ φ : BruhatCompactSupport C𝔽(F),
      let B := (spectralProjection (F := F) a h₀ hs₀(hs)).comp (A(F, h₀, hs₀(hs), φ))
      ∃ K : tensor(F, 0, s), sobolevProjectiveKernelOperator (F := F) h₀ hs₀(hs) K = B ∧
        ∀ l : sourceFirst(F, 0, s),
          represents(F, 0, s, B, (fun p ↦ ((w(F, 0, s) p.2)⁻¹ : ℝ) • l p)) ↔
            l = printedClass(F, 0, s, h₀, hs₀(hs), K)

/-- Paper: (10.4.3.25), p. 470. Take F = ℚ, s = 4 and a equal to the
abscissa of the first positive-ordinate nontrivial zeta zero. A nonnegative
smooth test supported in a sufficiently small log-norm band about zero has
nonzero Mellin value there after shifting by a. The order-zero jet shows
spectral projection after convolution is nonzero. Let h be its output-first
Haar kernel. The displayed weighted integral would give
h(x,y) = h(y,x)/w(y) locally almost everywhere. Swapping x,y forces h to
vanish unless w(x)w(y)=1, a product-null set. Missing existence of a tensor
would itself falsify the asserted existence and uniqueness. -/
theorem Printed.spectralLineKernel_extraWeight_false :
    ¬ Printed.spectralLineKernel_extraWeight := by sorry

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, second formula. The cutoff
spectral function is claimed to represent the geometric truncation.
The two reciprocal weights account for (10.4.3.26) and (10.4.3.30). -/
def Printed.spectralLineTruncatedKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ φ : BruhatCompactSupport C𝔽(F),
        let B := (spectralProjection (F := F) a h₀ hs₀(hs)).comp (A(F, h₀, hs₀(hs), φ))
        ∃ K : tensor(F, 0, s), sobolevProjectiveKernelOperator (F := F) h₀ hs₀(hs) K = B ∧
          IsSobolevHilbertSchmidtKernel (geometricTruncatedConvolution a h₀ hs₀(hs) hρ φ)
            (printedWeight(F, 0, s, ρ, printedClass(F, 0, s, h₀, hs₀(hs), K)))

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471. For F = ℚ, a = 2 and s = 4
there are no line zeros, so the spectral projector and its kernel vanish.
Use Λ = 2, ε = 1/8 and the indicator of the outer norm band as cutoff.
An even nonnegative bump in the log-norm band (−1/8, 1/8) convolved with
itself is positive near the identity, where the cutoff equals one. -/
theorem Printed.spectralLineTruncatedKernel_geometric_false :
    ¬ Printed.spectralLineTruncatedKernel_geometric := by sorry

-- TODO(paper-gap): (10.4.3.45) applies the ambient kernel map to the
-- quotient tensor from (10.4.3.42). The bounds in (10.4.3.40) and in
-- (10.4.3.42) use N_s, while (10.4.3.38) and (10.4.3.43) use N_{I,s}.
-- There is no single literal typed assertion fixing both choices. Any
-- ambient limit of the transposed rectangles has spectral output, also
-- when the quotient tensors are transported by the map of (10.4.3.20).

/-- Paper: Theorem 10.4.3.5(3), p. 473. A necessary consequence of the
operator identity is that convolution after spectral projection has
spectral range, since every displayed rectangle has spectral output.
Deviation: This records a consequence independent of the ambiguous index
bounds and tensor type in the display. -/
def spectralStripTransposeLimit_rangeConsequence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F)),
      ∀ u : W(F, α, s),
        A(F, hα, hs₀(hs), φ) (spectralProjection a hα hs₀(hs) u) ∈
          (globalThetaSobolev F a hStrip(hα) hs₀(hs)).orthogonal

/-- Paper: Theorem 10.4.3.5(3), p. 473. Over ℚ use α = 0, s = 4
and a nontrivial zeta zero a + iγ. Its order-zero Riesz vector on the
log-norm line is g(t) = exp(−iγt)/(1+t²)². Every printed finite section
has spectral output. Take the nonzero weighted theta vector q of the
polar-free rational test with finite factor 1_{ℤ̂} and real factor
exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²).
The Fourier transform of (1+t²)⁻² is everywhere positive, so pairing q
with translates of g cannot vanish identically. Choose a smooth bump
of integral one concentrated at such a shift as φ. Then A(φ)g has a
nonzero geometric component, whereas any limit of the printed tensors
has spectral output. -/
theorem spectralStripTransposeLimit_rangeConsequence_false :
    ¬ spectralStripTransposeLimit_rangeConsequence := by sorry

/-- Paper: Theorem 10.4.3.6(2), p. 473, second formula. The cutoff
spectral function is claimed to represent the geometric restriction.
The two reciprocal weights account for (10.4.3.47) and (10.4.3.49).
The tensor is identified by the operator in (10.4.3.45).
Deviation: Interpret the unbound endpoint b using the cited interval [−α, α]. -/
def Printed.spectralStripRestrictionKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ)
      (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ φ : BruhatCompactSupport C𝔽(F),
        let B := (A(F, hα, hs₀(hs), φ)).comp (spectralProjection (F := F) a hα hs₀(hs))
        ∃ K : tensor(F, α, s), sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K = B ∧
          IsSobolevHilbertSchmidtKernel (geometricRestriction a hα hs₀(hs) hρ φ)
            (printedWeight(F, α, s, ρ, printedClass(F, α, s, hα, hs₀(hs), K)))

/-- Paper: Theorem 10.4.3.6(2), p. 473. For F = ℚ, a = 3, α = 1
and s = 4 the strip lies in the zero-free half-plane. The spectral
kernel vanishes. With Λ = 2, ε = 1/8 and the outer-band indicator,
geometric restriction is nonzero on the same even log-norm bump used
for the line counterexample. -/
theorem Printed.spectralStripRestrictionKernel_geometric_false :
    ¬ Printed.spectralStripRestrictionKernel_geometric := by sorry

end RiemannMasullo
