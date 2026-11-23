module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3

import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The line and strip trace formulas with the printed multiplicity -/

@[expose] public noncomputable section

open MeasureTheory NumberField Set

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "orderAt(" F ", " χ ", " z ")" =>
  meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mellinAt(" F ", " φ ", " χ ", " z ")" =>
  ∫ g, (φ : BruhatCompactSupport C𝔽(F)).val g * ideleClassNormTwist (F := F) χ z g
    ∂ideleClassTamagawaMeasure F

/-- Paper: Theorem 10.3.1.1(2) and (10.3.1.3)–(10.3.1.4), p. 448. As printed:
For every number field, basepoint choice, real a, degree s > 1 and test, the
line convolution has trace given by the sum over all Hecke zeros on the line,
counted with the minimum of their order and the printed floor. The trace-class
witness gives meaning to the trace on the left. See `spectralLineConvolution_trace`
and ERRATA F239. -/
def Printed.spectralLineConvolution_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a s : ℝ) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F)),
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let H := spectralSobolevQuotient F a hI hs₀
      let Z := {z : PontryaginDual C₁(F) × ℝ // 0 < orderAt(F, χ z.1, shift(a, z.2))}
      let term (z : Z) :=
        let n := (orderAt(F, χ z.val.1, shift(a, z.val.2))).untop₀.toNat
        let count := min n (Nat.floor ((s - 1) / 2 + 1))
        (count : ℂ) * mellinAt(F, φ, χ z.val.1, shift(0, z.val.2))
      ∃ T : nuclearEndomorphisms H,
        T.val = spectralConvolution (F := F) a hI hs₀ φ ∧ HasSum term (hilbertTrace T)

/-- Paper: Theorem 10.3.1.1(2), p. 448. Let F be the splitting field of X³−2
and K = ℚ(ζ₃). The two nontrivial characters of Gal(F/K) have the same Hecke
L-function by conjugation. Take a common critical-strip zero β+iγ. It has
order at least two for the trivial character of F. Set a = β and s = 3 and
choose the trivial representative on the norm-one trivial type. Use the radial
autocorrelation of b(x) = exp(−iγx) η(x), where η is a nonzero nonnegative smooth
bump in (1, 2). Divide by the norm-one volume to give multiplier B = |b̂|² on that
type and zero elsewhere. To bound the actual trace, take the standard adelic Gaussian
with finite integer indicators and apply (1−D)(1−cD), where D dilates the argument
by an idele of norm c > 1. This kills its value at zero and its additive integral.
Its Mellin factor Λ_F(z)(1−c^(−z))(1−c^(1−z))
forces dual support in the trivial-type zero set on the line. Nonzero eigenvalues
have generalized eigenspaces supported where B takes that eigenvalue. Only the
constant jet at each point has finite dual norm at s = 3. The printed sum
counts at least one extra positive term B(γ). -/
theorem Printed.spectralLineConvolution_trace_false :
    ¬ Printed.spectralLineConvolution_trace := by sorry

/-- Paper: Theorem 10.3.2.1(2) and (10.3.2.3)–(10.3.2.4), p. 454. As printed:
For every number field, basepoint choice, closed symmetric strip, degree s > 1 and
test, the strip convolution has trace given by the sum over all strip zeros with
full order inside and the printed floor truncation at either edge. The trace-class
witness gives meaning to the trace on the left. See `spectralStripConvolution_trace`
and ERRATA F240. -/
def Printed.spectralStripConvolution_trace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F)),
      let hI := (neg_nonpos.mpr hα).trans hα
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let H := spectralSobolevQuotient F a hI hs₀
      let Z := {z : PontryaginDual C₁(F) × ℝ × ℝ //
        z.2.1 ∈ Icc (-α) α ∧ 0 < orderAt(F, χ z.1, shift(a + z.2.1, z.2.2))}
      let term (z : Z) :=
        let b := z.val.2.1
        let t := z.val.2.2
        let n := (orderAt(F, χ z.val.1, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min n (Nat.floor ((s - 1) / 2 + 1)) else n
        (count : ℂ) * mellinAt(F, φ, χ z.val.1, shift(b, t))
      ∃ T : nuclearEndomorphisms H,
        T.val = spectralConvolution (F := F) a hI hs₀ φ ∧ HasSum term (hilbertTrace T)

/-- Paper: Theorem 10.3.2.1(2), p. 454. Use the splitting field of X³−2 and the
multiple trivial-type zero β+iγ from the line case. Choose the trivial representative,
s = 3, α = 1 and a = β−1. With x the log norm, take the radial test
V⁻¹ exp(−iγx) v(x), where V is the norm-one volume and v is a nonzero nonnegative
smooth bump supported in (1, 2). Its multiplier reaches its unique maximum modulus R
at the upper-edge zero. Applying the printed formula to the convolution powers gives
normalized traces tending to 2. For a peripheral generalized eigenvector of the
transpose, factoring out exp((1+iγ)x) gives the positive-shift averaging equation
with density v(y) exp(y)/R. The equation and dual norm give growth at most polynomial,
and the Fourier transform of the averaging density has modulus one only at zero.
Only constants then meet the dual norm at s = 3. Thus the peripheral algebraic
multiplicity is at most one, contradicting the printed limit of 2. -/
theorem Printed.spectralStripConvolution_trace_false :
    ¬ Printed.spectralStripConvolution_trace := by
  classical
  intro hall
  apply Printed.spectralLineConvolution_trace_false
  intro F _ _ χ hχ a s hs φ
  let L := {z : PontryaginDual C₁(F) × ℝ // 0 < orderAt(F, χ z.1, shift(a, z.2))}
  let term (z : L) := ((min (orderAt(F, χ z.val.1, shift(a, z.val.2))).untop₀.toNat
    (Nat.floor ((s - 1) / 2 + 1)) : ℕ) : ℂ) * mellinAt(F, φ, χ z.val.1, shift(0, z.val.2))
  let P (l : ℝ) (hl : l ≤ 0) : Prop :=
    ∃ T : nuclearEndomorphisms (spectralSobolevQuotient F a hl (zero_lt_one.trans hs).le),
      T.val = spectralConvolution (F := F) a hl (zero_lt_one.trans hs).le φ ∧
      HasSum term (hilbertTrace T)
  have transport (l : ℝ) (hl : l ≤ 0) (he : l = 0) (hp : P l hl) : P 0 le_rfl := by
    subst l
    exact hp
  apply transport _ ((neg_nonpos.mpr (le_refl (0 : ℝ))).trans le_rfl) neg_zero
  let Z := {z : PontryaginDual C₁(F) × ℝ × ℝ //
    z.2.1 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < orderAt(F, χ z.1, shift(a + z.2.1, z.2.2))}
  have hoff (z : Z) : z.val.2.1 = 0 := by simpa using z.property.1
  let e : L ≃ Z :=
    { toFun := fun z ↦ ⟨(z.val.1, 0, z.val.2), by simp, by simpa only [add_zero] using z.property⟩
      invFun := fun z ↦ ⟨(z.val.1, z.val.2.2), by simpa only [hoff z, add_zero] using z.property.2⟩
      left_inv := fun z ↦ Subtype.ext rfl
      right_inv := fun z ↦ Subtype.ext (Prod.ext rfl (Prod.ext (hoff z).symm rfl)) }
  obtain ⟨T, hT, hsum⟩ := hall F χ hχ a 0 s le_rfl hs φ
  refine ⟨T, hT, ?_⟩
  let u (z : Z) :=
    let b := z.val.2.1
    let t := z.val.2.2
    let n := (orderAt(F, χ z.val.1, shift(a + b, t))).untop₀.toNat
    ((if b = -0 ∨ b = 0 then min n (Nat.floor ((s - 1) / 2 + 1)) else n : ℕ) : ℂ) *
      mellinAt(F, φ, χ z.val.1, shift(b, t))
  have hu : HasSum u (hilbertTrace T) := hsum
  have heq (z : L) : u (e z) = term z := by simp only [u, e, Equiv.coe_fn_mk, add_zero, or_true, ite_true, term]
  exact (e.hasSum_iff.mpr hu).congr_fun (fun z ↦ (heq z).symm)

end RiemannMasullo
