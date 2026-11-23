module

public import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.Ch13_ZerosHecke.Targets
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

/-- Paper: §1.4.3, p. 29. Take the trivial rational character, half-width
one, and the closed disk of radius one quarter about two. This window
contains the full zeta zero divisor. At two the full explicit formula
expresses the zero sum as the two bounded polar moments minus the bounded
prime-power sum and the real-place term tending to positive infinity.
Its real part tends to negative infinity, also along every subsequence. -/
theorem Printed.introTraceApprox_spectral_limit_false :
    ¬ Printed.introTraceApprox_spectral_limit := by sorry

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

/-- Paper: §1.4.7, pp. 30–31. Take ℚ(i), the trivial character, S consisting
of the complex place alone, and a positive Gaussian there. The prime above 2
has different norm 4, hence unit mass 1/2. Every other finite unit mass is one.
The local transform and finite Euler product are positive for every real s > 1.
Their product must be multiplied by 1/2. Enlarging S as on p. 25 to contain
all field-ramified primes makes the printed multiplier valid in that case. -/
theorem Printed.introTrace_transition_mellin_false :
    ¬ Printed.introTrace_transition_mellin := by sorry

end RiemannMasullo
