module

public import RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.Grh.Theorems.RationalExplicitFormula
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Printed claims in the introduction's deduction of GRH -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "q(" v ")" => (((v) : HeightOneSpectrum _).asIdeal.absNorm : ℝ)
local notation "N[" F "](" g ")" => (((ideleClassNorm F) (g : C[F])).val : ℝ)
local notation "right(" a ")" => (Complex.re ⁻¹' Ioi (a : ℝ))
local notation "finiteL[" F "](" χ ")" => (finiteHeckeL_exists_continuation (F := F) χ).choose
local notation "approx(" h ", " ρ ", " n ", " z ")" => introTraceApprox (h n) (ρ n) z
local notation "finiteClass[" F "](" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "archClass[" F "](" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "zeroOrder[" F "](" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros[" F "](" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder[F](χ, s) ∧ |s.re - 1 / 2| < (a : ℝ)}
local notation "chartBase[" F "](" χ ")" =>
  ((∀ u : (ideleClassNorm F).ker, (χ : U[F]) u.val = 1) → χ = 1)
local notation "literalZeros[" F "](" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder[F](χ, s) ∧ |s.re| < (a : ℝ)}
local notation "moment[" F "](" f ", " χ ", " s ")" =>
  (∫ g : C[F], (f : C[F] → ℂ) g * ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F)
local notation "printedFamily[" F "](" χ ", " h ", " ρ ", " n ", " z ")" =>
  (fun g : C[F] ↦ (χ g : ℂ) * approx(h, ρ, n, z) (N[F](g)))
local notation "printedArch[" F "](" χ ", " f ", " w ")" =>
  ((if InfinitePlace.IsReal w then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) *
    ∫ u : (w : InfinitePlace F).Completionˣ,
      (χ (archClass[F](w) u) : ℂ) * (f : C[F] → ℂ) (archClass[F](w) u) * (Real.sqrt ‖u.val‖ : ℂ) /
        ((if InfinitePlace.IsReal w then |1 - ‖u.val‖| else ‖1 - u.val‖) : ℝ)
      ∂infiniteLocalMultiplicativeTamagawaMeasure F w)
local notation "printedReal[" F "](" χ ", " h ")" =>
  (∑ w : InfinitePlace F, if w.IsReal then printedArch[F](χ, h, w) else 0)
local notation "printedComplex[" F "](" χ ", " h ")" =>
  (∑ w : InfinitePlace F, if w.IsReal then 0 else printedArch[F](χ, h, w))
local notation "uniformizers[" F "]" => ((v : V[F]) → (v.adicCompletion F)ˣ)
local notation "isUniformizer[" F "](" v ", " π ")" =>
  ((Valued.v : Valuation (HeightOneSpectrum.adicCompletion F v) (WithZero (Multiplicative ℤ)))
    |>.IsUniformizer (π : HeightOneSpectrum.adicCompletion F v))
local notation "printedPrime[" F "](" χ ", " h ", " π ", " p ")" =>
  (let v := (p : V[F] × ℕ).1
   let m := (p : V[F] × ℕ).2 + 1
   let c := (χ (finiteClass[F](v) ((π : uniformizers[F]) v)) : ℂ)
   (Real.log q(v) : ℂ) * (c ^ m * h (q(v) ^ m) + star c ^ m * h ((q(v) ^ m)⁻¹)) /
     (q(v) : ℂ) ^ ((m : ℂ) / 2))

open Classical in
/-- Paper: §1.4, pp. 27–28. The opening trace identity sums zeros with abscissa
strictly between minus and plus the half-width. The Mellin argument is shifted by
one half. The complex denominator is the ordinary modulus in the display. -/
def Printed.introTrace_globalTrace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    ∀ φ : BruhatCompactSupport C[F], (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
    ∀ α : ℝ, 0 < α →
      let zeros := {z : {χ : PontryaginDual C[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
        0 < zeroOrder[F](z.1.val, z.2) ∧ |z.2.re| < α}
      let finiteTerm := fun (v : HeightOneSpectrum (𝓞 F))
          (b : BruhatCompactSupport (v.adicCompletion F)ˣ) ↦
        let μ := finiteLocalMultiplicativeTamagawaMeasure F v
        let mass := (μ (v.adicCompletionIntegers F).units).toReal
        ((Real.log (v.asIdeal.absNorm : ℝ) / mass : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b
      let archTerm := fun (w : InfinitePlace F) (a : BruhatCompactSupport w.Completionˣ) ↦
        if w.IsReal then infiniteConnesWeilPrincipalValue w a
        else (1 / (2 * (Real.pi : ℂ))) * ∫ u : w.Completionˣ,
          a.val u * (‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ)
            ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)
      ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
        (b : (v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ),
        (∀ w u, (a w).val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (b v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        Summable (fun v ↦ finiteTerm v (b v)) ∧
        HasSum (fun z : zeros ↦ ((zeroOrder[F](z.val.1.val, z.val.2) : ℤ) : ℂ) *
            moment[F](φ.val, z.val.1.val, (z.val.2 - 1 / 2)))
          (moment[F](φ.val, (1 : U[F]), (1 / 2)) + moment[F](φ.val, (1 : U[F]), (-1 / 2)) -
            ((∑ w : InfinitePlace F, archTerm w (a w)) +
              ∑' v, finiteTerm v (b v)))

/-- Paper: §1.4, p. 28. Over ℚ(i) take half-width two and
φ(g) = h(|g|) − h(1/|g|) with a nonzero nonnegative smooth bump in (9/4,11/4).
This width contains the full trivial-character divisor, which pairs to zero by
the functional equation and inversion. The poles cancel and the finite shells
miss the support. After inversion the complex term integrates a positive
multiple of h(r²)(r−1)/‖1−u‖ on the outer annulus, where r = ‖u‖. -/
theorem Printed.introTrace_globalTrace_false : ¬ Printed.introTrace_globalTrace := by sorry

open Classical in
/-- Paper: §1.4.1, p. 28. The local archimedean integrands multiply the restricted
test by the local character. For the bare positive arguments of φ in the finite
sum we use its values on the canonical norm section. Section 1.1.4 fixes the
base point of the pure-norm component. Both polar terms are the
Mellin integrals of φ. The zero index uses the strip printed on this page. -/
def Printed.introTrace_characterTrace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (φ : BruhatCompactSupport C[F]) (h : ℝ → ℂ), chartBase[F](χ) →
    (∀ u : (ideleClassNorm F).ker, φ.val u.val = 0) →
    (∀ (g : C[F]) (u : (ideleClassNorm F).ker),
      φ.val (g * u.val) = star (χ u.val : ℂ) * φ.val g) →
    (∀ t : ℝ≥0ˣ, h (t.val : ℝ) = φ.val (QuotientGroup.mk (canonicalIdeleNormSection F t))) →
    ∀ a : ℝ, 0 < a → ∀ π : uniformizers[F], (∀ v, isUniformizer[F](v, π v)) →
      Summable (fun p : V[F] × ℕ ↦ printedPrime[F](χ, h, π, p)) ∧
      HasSum (fun ρ : literalZeros[F](χ, a) ↦ (zeroOrder[F](χ, ρ.val) : ℂ) *
        moment[F](φ.val, χ, (ρ.val - 1 / 2)))
        (moment[F](φ.val, (1 : U[F]), (1 / 2)) + moment[F](φ.val, (1 : U[F]), (-1 / 2)) -
          printedReal[F](χ, φ.val) - printedComplex[F](χ, φ.val) -
          ∑' p : V[F] × ℕ, printedPrime[F](χ, h, π, p))

/-- Paper: §1.4.1, p. 28. Take the primitive quadratic character modulo
three over the rationals and a smooth radial bump equal to one at three
with support in `(5/2, 7/2)`. The only surviving prime power is three.
Its printed term changes sign when the uniformizer at three is changed
from three to minus three. Every other term is independent of this choice. -/
theorem Printed.introTrace_characterTrace_false : ¬ Printed.introTrace_characterTrace :=
  by sorry

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. The displayed products can be chosen as a cofinal
family of approximants with conjugate norm-one weight. -/
def Printed.introTraceApprox_conjugateWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]), chartBase[F](χ) →
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
    ∀ (n : ℕ) (z : ℂ) (g : C[F]) (u : (ideleClassNorm F).ker),
      (χ (g * u.val) : ℂ) * approx(h, ρ, n, z) (N[F](g * u.val)) =
        star (χ u.val : ℂ) * ((χ g : ℂ) * approx(h, ρ, n, z) (N[F](g)))

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. Use an order-four character modulo
five over the rationals with value `i` at two and let `u` have local unit
two at five and components one elsewhere. At norm two and parameter two,
the radial value is nonzero for all sufficiently late approximants.
Right translation by `u` multiplies the displayed test by `i`, while the
asserted conjugate weight would multiply it by `-i`. -/
theorem Printed.introTraceApprox_conjugateWeight_false :
    ¬ Printed.introTraceApprox_conjugateWeight := by sorry

open Classical in
/-- Paper: §1.4.3, p. 29. The printed real and complex archimedean
terms of the cutoff tests are uniformly bounded on the specified compact set. -/
def Printed.introTraceApprox_archimedean_bounded : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ right(a) → (interior K ∩ right(1)).Nonempty →
      ∃ C : ℝ, 0 < C ∧ ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
        ∀ (n : ℕ) (z : ℂ), z ∈ K →
          ‖printedReal[F](χ, printedFamily[F](χ, h, ρ, n, z))‖ ≤ C ∧
          ‖printedComplex[F](χ, printedFamily[F](χ, h, ρ, n, z))‖ ≤ C

/-- Paper: §1.4.3, p. 29. Over the rationals take the trivial character,
half-width one, and the closed disk of radius one quarter about two. On
`1 < t < 2`, the positive real branch at parameter two dominates one half
of the integral of the approximant against `t^(-1/2)/(t-1) dt`. Fatou's
lemma gives divergence since the approximant tends to `t^(-2)`. -/
theorem Printed.introTraceApprox_archimedean_bounded_false :
    ¬ Printed.introTraceApprox_archimedean_bounded := by sorry

open Classical in
/-- Paper: §1.4.3, p. 29. The two printed archimedean families have
holomorphic limits along a chosen cofinal cutoff sequence on the interior of
the specified compact set. -/
def Printed.introTraceApprox_archimedean_montel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ right(a) → (interior K ∩ right(1)).Nonempty →
      ∃ (h ρ : ℕ → ℝ → ℝ) (A B : ℂ → ℂ), IsIntroTraceApproximation h ρ ∧
        TendstoLocallyUniformlyOn (fun n z ↦ printedReal[F](χ, printedFamily[F](χ, h, ρ, n, z)))
          A atTop (interior K) ∧
        TendstoLocallyUniformlyOn (fun n z ↦ printedComplex[F](χ, printedFamily[F](χ, h, ρ, n, z)))
          B atTop (interior K) ∧
        AnalyticOnNhd ℂ A (interior K) ∧ AnalyticOnNhd ℂ B (interior K)

/-- Paper: §1.4.3, p. 29. At the trivial rational character, with half-width
one and the closed disk of radius one quarter about two, the real term at
the interior point two diverges along every cutoff subsequence. -/
theorem Printed.introTraceApprox_archimedean_montel_false :
    ¬ Printed.introTraceApprox_archimedean_montel := by sorry

/-- Paper: §1.4.3, p. 29. The spectral sums of the cutoff family converge
to a holomorphic function on the interior of the compact set outside the
window. The compact set is already to the right of the window. The
printed Mellin pairing is taken in the character of the zeros. -/
def Printed.introTraceApprox_spectral_limit : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ right(a) → (interior K ∩ right(1)).Nonempty →
      ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
        let term := fun n (z : ℂ) (r : windowZeros[F](χ, a)) ↦
          (zeroOrder[F](χ, r.val) : ℂ) *
            moment[F]((fun g : C[F] ↦ approx(h, ρ, n, z) (N[F](g))), χ, (r.val - 1 / 2))
        ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (interior K) ∧
          ∀ z ∈ interior K, (∀ n, Summable (term n z)) ∧
            Tendsto (fun n ↦ ∑' r, term n z r) atTop (𝓝 (H z))

local notation "CQ" => C[ℚ]
local notation "LQ" => continuedCompletedHeckeL (F := ℚ) 1
local notation "DQ" => MeromorphicOn.divisor LQ univ
local notation "ZQ" => {z : ℂ // 0 < DQ z ∧ |z.re - 1 / 2| < (1 : ℝ)}

private theorem printedTrace_ratZero_order (z : ℂ) (hz : 0 < z.re) :
    meromorphicOrderAt riemannZeta z = meromorphicOrderAt LQ z :=
  meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual CQ)
    (by simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1))
    (fun s ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property]) hz

private theorem printedTrace_ratZero_right {z : ℂ} (h : 0 < meromorphicOrderAt LQ z) : z.re < 1 := by
  rcases le_or_gt z.re 0 with hz | hz
  · exact hz.trans_lt zero_lt_one
  · obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec (1 : PontryaginDual CQ)
    exact completedHeckeL_continuation_zeros _ _ hL hEq hz h

private theorem printedTrace_ratZero_strip {z : ℂ} (h : 0 < DQ z) : 0 < z.re ∧ z.re < 1 := by
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec (1 : PontryaginDual CQ)
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at h
  have hp : 0 < meromorphicOrderAt LQ z := by
    cases he : meromorphicOrderAt LQ z with
    | top => simp
    | coe k => simpa [he] using h
  obtain ⟨ε, hε, hne, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation (1 : PontryaginDual CQ) _ _ hL hEq
      (by simpa using hL) (by simpa using hEq)
  have hcomp : meromorphicOrderAt (fun s ↦ LQ (1 - s)) z = meromorphicOrderAt LQ (1 - z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero (f := LQ)
      (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
      (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  have hf : (fun s ↦ LQ (1 - s)) = ε * LQ := by
    funext t
    simpa only [inv_one, Pi.mul_apply] using hfe t
  rw [hf, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at hcomp
  have hl := printedTrace_ratZero_right (hcomp ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact ⟨by linarith, printedTrace_ratZero_right hp⟩

private theorem printedTrace_ratZero_divisor (r : External.Grh.criticalStripZetaZeros) :
    DQ r.val = (External.Grh.zetaZeroOrder r : ℤ) := by
  obtain ⟨_, hp, h1⟩ := External.Grh.mem_criticalStripZetaZeros.mp r.property
  have hn : r.val ≠ 1 := fun he ↦ by simp [he] at h1
  have ha := analyticOn_riemannZeta _ hn
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (1 : PontryaginDual CQ)).1.meromorphicOn
    (mem_univ _), ← printedTrace_ratZero_order _ hp, ha.meromorphicOrderAt_eq, ← External.Grh.zetaZeroOrder_cast_eq]
  simp

/-- The width-one rational window indexes exactly the classical nontrivial zeta zeros. -/
private noncomputable def printedTrace_ratZero_equiv : ZQ ≃ External.Grh.criticalStripZetaZeros where
  toFun r := ⟨r.val, by
    have ⟨hp,h1⟩ := printedTrace_ratZero_strip r.property.1
    refine External.Grh.mem_criticalStripZetaZeros.mpr ⟨?_, hp, h1⟩
    by_contra hn
    have ha := analyticOn_riemannZeta r.val (show r.val ≠ 1 from fun he ↦ by simp [he] at h1)
    have hz := ha.analyticOrderAt_eq_zero.mpr hn
    have h := r.property.1
    rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (1 : PontryaginDual CQ)).1.meromorphicOn
      (mem_univ _), ← printedTrace_ratZero_order _ hp, ha.meromorphicOrderAt_eq, hz] at h
    simp at h⟩
  invFun r := ⟨r.val, by
    obtain ⟨_, hp, h1⟩ := External.Grh.mem_criticalStripZetaZeros.mp r.property
    refine ⟨?_, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
    rw [printedTrace_ratZero_divisor]
    exact_mod_cast External.Grh.zetaZeroOrder_pos r⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Changing from the norm to its logarithm absorbs the half-shift into the compact test. -/
private theorem printedTrace_compactLogMellin_radial (A : ℝ → ℂ) (s : ℂ) :
    External.Grh.compactLogMellin (fun x ↦ Complex.exp (-(x : ℂ) / 2) * A (Real.exp x)) s =
      introTraceMellin A (s - 1/2) := by
  rw [External.Grh.compactLogMellin, introTraceMellin, mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
  calc
    _ = Complex.exp (-(x : ℂ)/2 + s * x) * A (Real.exp x) := by rw [Complex.exp_add]; ring
    _ = Complex.exp ((x : ℂ) + x * (s - 1/2 - 1)) * A (Real.exp x) := by congr 2; ring
    _ = _ := by rw [Complex.exp_add]; ring

private theorem printedTrace_ratSum_reindex (A : ℝ → ℂ) :
    introTraceSpectralSum (F := ℚ) 1 A 1 = ∑' r : External.Grh.criticalStripZetaZeros,
      (External.Grh.zetaZeroOrder r : ℂ) *
      External.Grh.compactLogMellin (fun x ↦ Complex.exp (-(x : ℂ) / 2) * A (Real.exp x)) r.val := by
  rw [introTraceSpectralSum, ← printedTrace_ratZero_equiv.tsum_eq]
  apply tsum_congr
  intro z
  rw [printedTrace_compactLogMellin_radial]
  have h := printedTrace_ratZero_divisor (printedTrace_ratZero_equiv z)
  change DQ z.val = _ at h
  change (DQ z.val : ℂ) * _ = _ * introTraceMellin A (z.val - 1/2)
  simp [h]

/-- Fatou’s lemma on (0,1) detects the nonintegrable reciprocal at the lower endpoint. -/
private theorem printedTrace_logGamma_integral_tendsto (b : ℕ → ℝ → ℝ) (hb : ∀ n, Continuous (b n))
    (hb0 : ∀ n x, 0 ≤ b n x)
    (hlim : ∀ x ∈ Ioo (0 : ℝ) 1, Tendsto (fun n ↦ b n x) atTop (𝓝 (Real.exp (-(5 / 2) * x))))
    (hI : ∀ n, IntegrableOn (fun x ↦ b n x / (1 - Real.exp (-(2 * x)))) (Ioi 0)) :
    Tendsto (fun n ↦ ∫ x in Ioi (0 : ℝ), b n x / (1 - Real.exp (-(2 * x)))) atTop atTop := by
  let D (x : ℝ) := 1 - Real.exp (-(2 * x))
  have hD (x : ℝ) (hx : 0 < x) : 0 < D x := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  let G (n : ℕ) (x : ℝ) := ENNReal.ofReal (b n x / D x)
  have hG (n : ℕ) : Measurable (G n) :=
    ENNReal.measurable_ofReal.comp ((hb n).measurable.div (by unfold D; fun_prop))
  let Y (n : ℕ) := ∫⁻ x in Ioi (0 : ℝ), G n x
  have hj (n : ℕ) : (∫ x in Ioi (0 : ℝ), b n x / D x) = (Y n).toReal :=
    integral_eq_lintegral_of_nonneg_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
      (.of_forall fun x hx ↦ div_nonneg (hb0 n x) (hD x hx).le)) (hI n).aestronglyMeasurable
  have hfin (n : ℕ) : Y n ≠ ⊤ := by
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun x ↦ b n x / D x) :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx ↦
        div_nonneg (hb0 n x) (hD x hx).le)
    exact (lintegral_ofReal_ne_top_iff_integrable (hI n).aestronglyMeasurable hnn).mpr (hI n)
  let c := Real.exp (-(5 / 2 : ℝ)) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hdiv : ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (c / x) = ⊤ := by
    by_contra he
    have hi : IntegrableOn (fun x : ℝ ↦ c / x) (Ioo (0 : ℝ) 1) := by
      have ht := integrable_toReal_of_lintegral_ne_top (μ := volume.restrict (Ioo (0 : ℝ) 1))
        (ENNReal.measurable_ofReal.comp (measurable_const.div measurable_id)).aemeasurable he
      exact ht.congr ((ae_restrict_iff' measurableSet_Ioo).mpr (.of_forall fun x hx ↦
        ENNReal.toReal_ofReal (div_nonneg hc.le hx.1.le)))
    have hi' : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
      refine IntegrableOn.congr_fun (Integrable.const_mul hi c⁻¹) (fun x hx ↦ ?_) measurableSet_Ioo
      field_simp [hc.ne']
    simp [intervalIntegrable_inv_iff] at hi'
  have hlow (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      ENNReal.ofReal (c / x) ≤ liminf (fun n ↦ G n x) atTop := by
    have hpt := ENNReal.tendsto_ofReal ((hlim x hx).div_const (D x))
    rw [show liminf (fun n ↦ G n x) atTop = _ from hpt.liminf_eq]
    apply ENNReal.ofReal_le_ofReal
    have hnum : Real.exp (-(5 / 2 : ℝ)) ≤ Real.exp (-(5 / 2) * x) :=
      Real.exp_le_exp.mpr (by linarith [hx.2])
    have hden : D x ≤ 2 * x := by dsimp [D]; linarith [Real.add_one_le_exp (-(2 * x))]
    calc c / x = Real.exp (-(5 / 2 : ℝ)) / (2 * x) := by dsimp [c]; ring
         _ ≤ _ := div_le_div₀ (Real.exp_pos _).le hnum (hD x hx.1) hden
  have hy : liminf Y atTop = ⊤ := top_unique <| calc
    ⊤ = ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (c / x) := hdiv.symm
    _ ≤ ∫⁻ x in Ioo (0 : ℝ) 1, liminf (fun n ↦ G n x) atTop :=
      lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr (.of_forall hlow))
    _ ≤ liminf (fun n ↦ ∫⁻ x in Ioo (0 : ℝ) 1, G n x) atTop := lintegral_liminf_le hG
    _ ≤ liminf Y atTop := liminf_le_liminf (.of_forall fun n ↦
      lintegral_mono' (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl) (fun _ ↦ le_rfl))
  change Tendsto (fun n ↦ ∫ x in Ioi (0 : ℝ), b n x / D x) atTop atTop
  simp_rw [hj]
  refine tendsto_atTop.mpr fun M ↦ ?_
  have hlt : ENNReal.ofReal (max M 0) < liminf Y atTop := by rw [hy]; exact ENNReal.ofReal_lt_top
  filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
  exact (le_max_left M 0).trans ((ENNReal.ofReal_lt_iff_lt_toReal (le_max_right M 0) (hfin n)).mp hn).le

/-- For a nonnegative log profile supported at positive arguments, the real gamma term is
negative and the von Mangoldt sum is nonnegative. -/
private theorem printedTrace_rationalContour_bound (b : ℝ → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (b x : ℂ)))
    (hc : HasCompactSupport (fun x ↦ (b x : ℂ))) (hb : ∀ x, 0 ≤ b x) (hz : ∀ x ≤ 0, b x = 0) :
    let g := fun x ↦ (b x : ℂ)
    IntegrableOn (fun x ↦ b x / (1 - Real.exp (-(2*x)))) (Ioi 0) ∧
    (∑' r : External.Grh.criticalStripZetaZeros, (External.Grh.zetaZeroOrder r : ℂ) *
      External.Grh.compactLogMellin g r.val).re ≤
      (External.Grh.compactLogMellin g 0 + External.Grh.compactLogMellin g 1).re -
        ∫ x in Ioi (0 : ℝ), b x / (1 - Real.exp (-(2*x))) := by
  intro g
  let P (n : ℕ) := (ArithmeticFunction.vonMangoldt n : ℂ) *
    (g (Real.log n) + g (-Real.log n) / (n : ℂ))
  let R (x : ℝ) := (2 * g 0 * Complex.exp (-2 * (x : ℂ)) - g x -
    Complex.exp (-(x : ℂ)) * g (-x)) / (1 - Complex.exp (-2 * (x : ℂ)))
  let F := External.Grh.compactLogMellin g
  let Z := ∑' r : External.Grh.criticalStripZetaZeros, (External.Grh.zetaZeroOrder r : ℂ) * F r.val
  have hstat := External.Grh.completedZeta_explicit_formula hs hc
  obtain ⟨hR, hP, _hZ, he⟩ := hstat
  change IntegrableOn R (Ioi 0) at hR
  change Summable (fun n ↦ ‖P n‖) at hP
  change (-((Real.log Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) * g 0 +
    ∫ x in Ioi (0 : ℝ), R x) - ∑' n, P n = -F 0 - F 1 + Z at he
  have hzero : g 0 = 0 := by simp [g, hz]
  rw [hzero, mul_zero, zero_add] at he
  have hRR (x : ℝ) (hx : 0 < x) : R x = ↑(-(b x / (1 - Real.exp (-(2*x))))) := by
    have hxm : g (-x) = 0 := by simp [g, hz _ (by linarith : -x ≤ 0)]
    dsimp only [R]
    rw [hzero, hxm, mul_zero, zero_mul, zero_sub, mul_zero, sub_zero]
    push_cast
    simp only [g, neg_div]
    congr 2
    ring
  have hAE : (fun x ↦ (R x).re) =ᵐ[volume.restrict (Ioi 0)] fun x ↦ -(b x / (1 - Real.exp (-(2*x)))) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx ↦ congrArg Complex.re (hRR x hx))
  have hi := (hR.re.congr hAE).neg
  refine ⟨by simpa [IntegrableOn] using hi, ?_⟩
  have hrint : (∫ x in Ioi (0 : ℝ), R x).re = -(∫ x in Ioi (0 : ℝ), b x / (1 - Real.exp (-(2*x)))) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), (R x).re := (integral_re hR).symm
      _ = _ := (integral_congr_ae hAE).trans (integral_neg _)
  have hPP (n : ℕ) : 0 ≤ (P n).re := by
    let a : ℝ := ArithmeticFunction.vonMangoldt n * (b (Real.log n) + b (-Real.log n) / n)
    have hPa : P n = (a : ℂ) := by dsimp [P, g, a]; push_cast; rfl
    rw [hPa, Complex.ofReal_re]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (add_nonneg (hb _) (div_nonneg (hb _) n.cast_nonneg))
  have hpos : 0 ≤ (∑' n, P n).re := by rw [Complex.re_tsum hP.of_norm]; exact tsum_nonneg hPP
  have hh := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, hrint] at hh
  change Z.re ≤ (F 0 + F 1).re - _
  rw [Complex.add_re]
  linarith


/-- The two pole moments stay bounded as the cutoffs exhaust the radial power. The gamma
integral diverges and forces the real part of the spectral sum to tend to minus infinity. -/
private theorem printedTrace_direct_rat_spectral_tendsto_atBot (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) :
    Tendsto (fun n ↦ (introTraceSpectralSum (F := ℚ) 1 (introTraceApprox (h n) (ρ n) 2) 1).re)
      atTop atBot := by
  let A (n : ℕ) := introTraceApprox (h n) (ρ n) 2
  let g (n : ℕ) (x : ℝ) := Complex.exp (-(x : ℂ) / 2) * A n (Real.exp x)
  let b (n : ℕ) (x : ℝ) := Real.exp (-x / 2) * (A n (Real.exp x)).re
  have heq (n : ℕ) : (fun x ↦ (b n x : ℂ)) = g n := by
    obtain ⟨q, _, hq⟩ := (introTraceApprox_two_logProfile h ρ hA n).2
    funext x
    dsimp [b, g, A]
    rw [hq]
    simp
  have hpos (n : ℕ) (x : ℝ) : 0 ≤ b n x := by
    obtain ⟨q, hq, hq'⟩ := (introTraceApprox_two_logProfile h ρ hA n).2
    dsimp [b, A]
    rw [hq']
    exact mul_nonneg (Real.exp_pos _).le (hq _)
  have hzero (n : ℕ) (x : ℝ) (hx : x ≤ 0) : b n x = 0 := by
    have hz : A n (Real.exp x) = 0 := image_eq_zero_of_notMem_tsupport
      (fun hm ↦ (not_lt.mpr (Real.exp_le_one_iff.mpr hx))
        (introTraceApprox_support h ρ hA n 2 hm))
    simp [b, hz]
  have hreg (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g n) ∧ HasCompactSupport (g n) := by
    obtain ⟨hs, hc⟩ := (introTraceApprox_two_logProfile h ρ hA n).1
    exact ⟨(Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg.div_const 2)).mul hs,
      hc.mul_left⟩
  have hEst (n : ℕ) := printedTrace_rationalContour_bound (b n) ((heq n).symm ▸ (hreg n).1)
    ((heq n).symm ▸ (hreg n).2) (hpos n) (hzero n)
  have hLim (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      Tendsto (fun n ↦ b n x) atTop (𝓝 (Real.exp (-(5/2)*x))) := by
    have hx1 : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx.1
    have ht := (Complex.continuous_re.tendsto _).comp
      (introTraceApprox_tendsto h ρ hA 2 _ (Real.exp_pos x) hx1.ne')
    have hv : (introTracePower 2 (Real.exp x)).re = ((Real.exp x)^2)⁻¹ := by
      simp only [introTracePower, hx1, ↓reduceIte, Complex.cpow_neg]
      have hsq : (Real.exp x : ℂ) ^ (2 : ℂ) = ((Real.exp x : ℂ) ^ (2 : ℕ)) :=
        Complex.cpow_natCast _ 2
      rw [hsq, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re]
    have he : Real.exp (-x / 2) * ((Real.exp x)^2)⁻¹ = Real.exp (-(5/2)*x) := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [← he, ← hv]
    exact tendsto_const_nhds.mul ht
  have hb (n : ℕ) : Continuous (b n) := by
    have hg := Complex.continuous_re.comp ((heq n).symm ▸ (hreg n).1.continuous)
    exact hg
  have hD := printedTrace_logGamma_integral_tendsto b hb hpos hLim fun n ↦ (hEst n).1
  have hM (n : ℕ) (s : ℂ) :
      External.Grh.compactLogMellin (fun x ↦ (b n x : ℂ)) s = introTraceMellin (A n) (s - 1/2) := by
    rw [heq n]
    exact printedTrace_compactLogMellin_radial _ _
  have hZ (n : ℕ) := printedTrace_ratSum_reindex (A n)
  let m := (introTraceMellin (introTracePower 2) (-1/2) + introTraceMellin (introTracePower 2) (1/2)).re
  have hPol := ((introTraceApprox_mellin_tendsto h ρ hA (-1/2)).tendsto_at
    (a := (2 : ℂ)) (by norm_num)).add ((introTraceApprox_mellin_tendsto h ρ hA (1/2)).tendsto_at
    (a := (2 : ℂ)) (by norm_num))
  have hBound := ((Complex.continuous_re.tendsto _).comp hPol).eventually
    (eventually_lt_nhds (lt_add_one m))
  apply tendsto_atBot.2
  intro M
  filter_upwards [hBound, (tendsto_atTop.1 hD) (m + 1 - M)] with n hp hd
  have hi := (hEst n).2
  rw [hM n, hM n] at hi
  norm_num only [zero_sub, show (1 : ℂ) - 1/2 = 1/2 by norm_num] at hi
  change (introTraceMellin (A n) (-1 / 2) + introTraceMellin (A n) (1 / 2)).re < m + 1 at hp
  rw [heq n] at hi
  change (introTraceSpectralSum (F := ℚ) 1 (A n) 1).re ≤ M
  rw [hZ n]
  linarith

/-- The closed disc around two lies in the right half-plane used in §1.4.3. -/
private theorem printedTrace_spectralDisk :
    Metric.closedBall (2 : ℂ) (1 / 4) ⊆ right(1) ∧
      (2 : ℂ) ∈ interior (Metric.closedBall (2 : ℂ) (1 / 4)) ∩ right(1) := by
  refine ⟨fun z hz ↦ ?_, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num)),
    by change (1 : ℝ) < (2 : ℂ).re; norm_num⟩
  have hd := (Complex.abs_re_le_norm (z - 2)).trans (mem_closedBall_iff_norm.mp hz)
  rw [Complex.sub_re, Complex.re_ofNat] at hd
  change (1 : ℝ) < z.re
  linarith [(abs_le.mp hd).1]

/-- For the trivial rational character, the printed moment of a radial approximant is its
radial Mellin transform multiplied by the norm-one Tamagawa volume. -/
private theorem printedTrace_rat_moment (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (n : ℕ) (s : ℂ) :
    moment[ℚ]((fun g : C[ℚ] ↦ approx(h, ρ, n, (2 : ℂ)) (N[ℚ](g))), (1 : U[ℚ]), s) =
      (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ) *
        introTraceMellin approx(h, ρ, n, (2 : ℂ)) s := by
  obtain ⟨φ, hφ⟩ := introTraceApprox_exists_bruhat (F := ℚ) 1 h ρ hA n 2
  rw [← (introTraceTest_mellin (F := ℚ) 1 _ φ hφ s).2]
  refine integral_congr_ae (Eventually.of_forall fun g ↦ ?_)
  simp [hφ, introTraceTest]

/-- Paper: §1.4.3, p. 29. Take the trivial rational character, half-width
one, and the closed disk of radius one quarter about two. This window
contains the full zeta zero divisor. At two the full explicit formula
expresses the zero sum as the two bounded polar moments minus the bounded
prime-power sum and the real-place term tending to positive infinity.
Its real part tends to negative infinity, also along every subsequence. -/
theorem Printed.introTraceApprox_spectral_limit_false :
    ¬ Printed.introTraceApprox_spectral_limit := by
  classical
  intro hall
  obtain ⟨h, ρ, hA⟩ := exists_introTraceApproximation
  obtain ⟨H, _, hlimit⟩ := hall ℚ 1 1 (fun _ ↦ rfl) one_pos _ (isCompact_closedBall _ _)
    printedTrace_spectralDisk.1 ⟨2, printedTrace_spectralDisk.2⟩ h ρ hA
  have hlim := (hlimit 2 printedTrace_spectralDisk.2.1).2
  let V₁ : ℂ := ((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal
  have hV : V₁ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have hcl := NumberField.classNumber_pos ℚ
    have hreg := NumberField.Units.regulator_pos ℚ
    have htor := NumberField.Units.torsionOrder_pos ℚ
    have hdisc := Int.natAbs_pos.mpr (NumberField.discr_ne_zero ℚ)
    rw [normOneIdeleClassTamagawaMeasure_volume, ENNReal.toReal_ofReal (by positivity)]
    positivity
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ
  let Z := {r : ℂ // 0 < D r ∧ |r.re - 1 / 2| < (1 : ℝ)}
  have hscale (n : ℕ) :
      (∑' r : Z, (D r.val : ℂ) *
        moment[ℚ]((fun g : C[ℚ] ↦ approx(h, ρ, n, (2 : ℂ)) (N[ℚ](g))), (1 : U[ℚ]), (r.val - 1 / 2))) =
        V₁ * introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1 := by
    rw [introTraceSpectralSum, ← tsum_mul_left]
    apply tsum_congr
    intro r
    rw [printedTrace_rat_moment h ρ hA]
    dsimp [V₁]
    ring
  have hlim' : Tendsto (fun n ↦ V₁ * introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1)
      atTop (𝓝 (H 2)) := hlim.congr hscale
  have hconv : Tendsto (fun n ↦ introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1)
      atTop (𝓝 (V₁⁻¹ * H 2)) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hV, one_mul] using hlim'.const_mul V₁⁻¹
  exact not_tendsto_nhds_of_tendsto_atBot (printedTrace_direct_rat_spectral_tendsto_atBot h ρ hA) _
    (Complex.continuous_re.continuousAt.tendsto.comp hconv)

/-- Paper: §1.4.4, p. 29. The displayed prime-power sum converges locally
uniformly on the right of one to the positive shifted logarithmic derivative. -/
def Printed.introTraceApprox_primeSum_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (π : uniformizers[F]), chartBase[F](χ) →
    (∀ v, isUniformizer[F](v, π v)) →
    ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
      TendstoLocallyUniformlyOn
        (fun n z ↦ ∑' p : V[F] × ℕ, printedPrime[F](χ, approx(h, ρ, n, z), π, p))
        (fun z ↦ logDeriv finiteL[F](χ) (z + 1 / 2)) atTop right(1)

/-- Paper: §1.4.4, p. 29. At parameter two the trivial rational character's
prime-power limit is strictly positive, with the prime two contributing a
positive term. The printed target `ζ'(5/2)/ζ(5/2)` is strictly negative. -/
theorem Printed.introTraceApprox_primeSum_tendsto_false :
    ¬ Printed.introTraceApprox_primeSum_tendsto := by sorry

open Classical in
/-- Paper: §1.4.5, pp. 29–30. Subtracting the two polar terms when the
character is trivial on the norm-one classes gives a holomorphic function
on the right of each positive half-width, with removable values filled in. -/
def Printed.introTrace_regularized_logDeriv_analytic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
      EqOn H (fun z ↦ logDeriv finiteL[F](χ) (z + 1 / 2) -
        if ∀ u : (ideleClassNorm F).ker, χ u.val = 1
        then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) (right(a) \ {1 / 2})

open scoped ComplexOrder in
private theorem introTrace_regularized_logDeriv_neg (x : ℝ) (hx : 1 < x) :
    (logDeriv (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose x).re < 0 := by
  let L := (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose
  have hnear : L =ᶠ[𝓝 (x : ℂ)] riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with z hz
    calc
      L z = finiteHeckeL (1 : U[ℚ]) ⟨z, hz⟩ :=
        (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose_spec.2 ⟨z, hz⟩
      _ = dedekindZeta ℚ z := finiteHeckeL_one_eq_dedekindZeta ⟨z, hz⟩
      _ = riemannZeta z := dedekindZeta_rat_eq_riemannZeta hz
  let a (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n
  have hpos : 0 < LSeries a (x : ℂ) := by
    have hterm (n : ℕ) : 0 ≤ LSeries.term a x n :=
      LSeries.term_nonneg (Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg) x
    apply (ArithmeticFunction.LSeriesSummable_vonMangoldt hx).tsum_pos hterm 2
    apply LSeries.term_pos (by decide)
    apply Complex.zero_lt_real.mpr
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos one_lt_two
  change (logDeriv L x).re < 0
  rw [(logDeriv_congr_nhds hnear).eq_of_nhds]
  rw [show LSeries a (x : ℂ) = -logDeriv riemannZeta x by
    simpa only [logDeriv_apply, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hx] at hpos
  exact (Complex.lt_def.mp (neg_pos.mp hpos)).1

/-- Paper: §1.4.5, p. 30. With the trivial rational character and
half-width one quarter, the shifted log derivative has residue minus one
at one half because zeta has a simple pole at one. Subtracting the
printed correction gives residue minus two there. -/
theorem Printed.introTrace_regularized_logDeriv_analytic_false :
    ¬ Printed.introTrace_regularized_logDeriv_analytic := by
  intro hall
  obtain ⟨H, han, heq⟩ := hall ℚ 1 (1 / 4) (fun _ ↦ rfl) (by norm_num)
  have hhalf := (han _ (show (1 / 2 : ℂ) ∈ right(1 / 4) by norm_num)).continuousAt
  have hcont : ContinuousAt (fun t : ℝ ↦ (t - 1) * (H ((t : ℂ) - 1 / 2)).re) 1 := by
    apply (continuousAt_id.sub continuousAt_const).mul
    apply Complex.continuous_re.continuousAt.comp
    apply ContinuousAt.comp (g := H) _ (Complex.continuous_ofReal.continuousAt.sub_const _)
    convert hhalf using 1
    norm_num
  have hlim : Tendsto (fun t : ℝ ↦ (t - 1) * (H ((t : ℂ) - 1 / 2)).re)
      (𝓝[>] 1) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- The logarithmic derivative is negative to the right of one. The printed
  -- correction subtracts a further 1/(t-1), even arbitrarily close to one.
  have hbound : (0 : ℝ) ≤ -1 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
    have hz : (t : ℂ) - 1 / 2 ∈ right(1 / 4) \ {(1 / 2 : ℂ)} := by
      constructor
      · change 1 / 4 < ((t : ℂ) - 1 / 2).re
        norm_num
        linarith
      · intro h
        have := congrArg Complex.re (mem_singleton_iff.mp h)
        norm_num at this
        linarith
    have he := heq hz
    have htriv : ∀ u : (ideleClassNorm ℚ).ker, (1 : U[ℚ]) u.val = 1 := fun _ ↦ rfl
    simp only [ite_eq_left htriv, sub_add_cancel, show (t : ℂ) - 1 / 2 - 1 / 2 = t - 1 by ring] at he
    have hreal : (H ((t : ℂ) - 1 / 2)).re =
        (logDeriv (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose t).re - (1 / t + 1 / (t - 1)) := by
      simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
        ← Complex.ofReal_add, Complex.sub_re, Complex.ofReal_re] using congrArg Complex.re he
    rw [hreal, mul_sub, mul_add, mul_one_div_cancel (sub_ne_zero.mpr ht.ne')]
    have hneg := introTrace_regularized_logDeriv_neg t ht
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.le) hneg.le,
      mul_nonneg (sub_nonneg.mpr ht.le) (show 0 ≤ 1 / t by positivity)]
  linarith

-- Section 1.1.4 (p. 12) chooses χ = 1 on the pure-norm component. In that
-- coordinate the possible pole of the shifted logarithmic derivative is at 1/2.
-- The twist |·|^i changes coordinates and supplies no refutation of §1.4.5.

/-- Paper: §1.4.7, p. 30. The Mellin transform of the extended test is the
local Mellin transform multiplied by the finite Euler product outside `S`.
Section 1.1.4 defines the local character by descent when χ is unramified
outside S. For the finite S specified on p. 30 the multiplier in print has no
outside integer-unit mass. The comparison is an identity of meromorphic germs. -/
def Printed.introTrace_transition_mellin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V[F]) (χ : U[F])
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))),
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦ sLocalIdelicZFunction f (twist s) *
        reciprocalPartialHeckeEulerProduct χ S s * finiteL[F](χ) s)

/-- The product of the omitted unit masses at the archimedean-only stage is
the reciprocal square root of the absolute discriminant. -/
private theorem introTrace_transition_mellin_false_mass (F : Type) [Field F] [NumberField F] :
    (∏ᶠ v : {v : V[F] // v ∉ (∅ : Finset V[F])},
      (((finiteLocalMultiplicativeTamagawaMeasure F v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) =
      (((Real.sqrt ((NumberField.discr F).natAbs : ℝ))⁻¹ : ℝ) : ℂ) := by
  classical
  let J := differentIdeal ℤ (𝓞 F)
  have hJ : J ≠ ⊥ := differentIdeal_ne_bot
  let T := (Ideal.finite_factors hJ).toFinset
  let d (v : V[F]) := multiplicity v.asIdeal J
  have hout (v : V[F]) (hv : v ∉ T) : d v = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    simpa [T, J] using hv
  have hfactor : ∏ v ∈ T, v.asIdeal ^ d v = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset (f := fun v : V[F] ↦ v.asIdeal ^ d v)]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ
    · intro v hv
      by_contra hn
      exact hv (by simp [hout v hn])
  have hnorm : (∏ v ∈ T, (v.asIdeal.absNorm : ℝ) ^ d v) = ((NumberField.discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) ↦ Ideal.absNorm I) hfactor :
      (∏ v ∈ T, v.asIdeal.absNorm ^ d v) = (NumberField.discr F).natAbs)
  let m (v : V[F]) := (((finiteLocalMultiplicativeTamagawaMeasure F v)
    (v.adicCompletionIntegers F).units).toReal : ℂ)
  have hm (v : V[F]) : m v = (((Real.sqrt ((v.asIdeal.absNorm : ℝ) ^ d v))⁻¹ : ℝ) : ℂ) := by
    simp [m, finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv, d, J]
  change (∏ᶠ v : {v : V[F] // v ∉ (∅ : Finset V[F])}, m v.val) = _
  rw [finprod_subtype_eq_finprod_cond (f := m)]
  simp only [Finset.notMem_empty, not_false_eq_true, finprod_true]
  rw [finprod_eq_finsetProd_of_mulSupport_subset m (s := T)]
  · simp_rw [hm]
    rw [← Complex.ofReal_prod, Finset.prod_inv_distrib,
      ← Real.sqrt_prod T (fun _ _ ↦ by positivity), hnorm]
  · intro v hv
    by_contra hn
    exact hv (by simp [hm, hout v hn])

/-- Paper: §1.4.7, pp. 30–31. Take ℚ(i), the trivial character, S consisting
of the complex place alone, and a positive Gaussian there. The prime above 2
has different norm 4, hence unit mass 1/2. Every other finite unit mass is one.
The local transform and finite Euler product are positive for every real s > 1.
Their product must be multiplied by 1/2. Enlarging S as on p. 25 to contain
all field-ramified primes makes the printed multiplier valid in that case. -/
theorem Printed.introTrace_transition_mellin_false :
    ¬ Printed.introTrace_transition_mellin := by
  classical
  intro h
  let F := CyclotomicField 4 ℚ
  have : NeZero (4 : ℕ) := ⟨by decide⟩
  have : IsCyclotomicExtension {4} ℚ F := by
    convert CyclotomicField.isCyclotomicExtension 4 ℚ
    exact Subsingleton.elim _ _
  have : NumberField F := IsCyclotomicExtension.numberField {4} ℚ F
  have hdisc : (NumberField.discr F).natAbs = 4 := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr (n := 4) (K := F)]
    have hfac : Nat.primeFactors 4 = {2} := by
      rw [show 4 = 2 ^ 2 by decide]
      exact Nat.primeFactors_prime_pow (by decide) Nat.prime_two
    rw [hfac, Finset.prod_singleton, show Nat.totient 4 = 2 by decide]
    norm_num
  let S : Finset V[F] := ∅
  let χ : U[F] := 1
  let ψ : PontryaginDual (SIdeleQuotient F S) := 1
  have hχ0 : ideleClassNormTwist χ 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S := by
    rw [hχ0]
    exact (mem_unramifiedOutside_iff F S 1).mpr fun _ _ _ ↦ rfl
  let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
  have hc : c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ := by
    ext g
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous c
  obtain ⟨f, hf⟩ := exists_sLocalIdelicZFunction_principalValue_attaining_poles (S := S) ψ
  let g := sAdelePrincipalValue F (Finset.Subset.refl S) f
  let Z (s : ℂ) := sLocalIdelicZFunction g (twist s)
  have hZ : meromorphicOrderAt Z 1 ≠ ⊤ := by
    dsimp only [Z, twist]
    rw [hc, hf]
    exact WithTop.coe_ne_top
  let L := finiteL[F](χ)
  obtain ⟨hL, hLf⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hnL : ∀ᶠ s in 𝓝[≠] (1 : ℂ), L s ≠ 0 := by
    apply ((hL (mem_univ (1 : ℂ))).meromorphicAt.eventually_eq_zero_or_eventually_ne_zero).resolve_left
    intro he
    have horder : meromorphicOrderAt L 1 ≤ 0 := introTrace_finiteL_no_zeros_one_line χ 0
    rw [meromorphicOrderAt_eq_top_iff.mpr he] at horder
    exact (not_le.mpr (WithTop.coe_lt_top (0 : ℤ))) horder
  have hraw := weilIdentity_unramifiedOutside_meromorphic (F := F) S g χ hχ L hL
    (fun z hz ↦ hLf ⟨z, hz⟩)
  have hbad := h F S χ hχ g
  have hmass := introTrace_transition_mellin_false_mass F
  rw [hdisc] at hmass
  have hs4 : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [hs4] at hmass
  apply hZ (meromorphicOrderAt_eq_top_iff.mpr ?_)
  filter_upwards [hbad.filter_mono (nhdsNE_le_codiscrete 1),
    hraw.filter_mono (nhdsNE_le_codiscrete 1), hnL] with s h₁ h₂ hs
  have he := h₁.symm.trans h₂
  change Z s * reciprocalPartialHeckeEulerProduct χ S s * L s =
    _ * Z s * (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s at he
  simp only [reciprocalPartialHeckeEulerProduct, S, Finset.prod_empty, mul_one, hmass] at he
  apply (mul_eq_zero.mp ?_).resolve_right hs
  linear_combination 2 * he

end RiemannMasullo
