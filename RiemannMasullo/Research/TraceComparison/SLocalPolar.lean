module

public import Mathlib.LinearAlgebra.Trace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Research.TraceComparison.SLocalQuotient

/-! # Global Mellin coefficients of the S-local polar moments

The scalar dilation on additive S-adelic tests acts diagonally on the two polar
coordinates in §12.4. The quotient and its measure supply the volume conversion
to the global Mellin integrals in (12.5.1.3). -/

@[expose] public noncomputable section

open IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "mF" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "vF" => (normOneIdeleClassTamagawaMeasure F) univ
local notation "vS" => (sLocalNormOneQuotientMeasure F S) univ
local notation "M(" φ "," s ")" => modulatedFourierMellin mF univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  (ideleClassTamagawaMeasure F) φ (ideleClassNormTwist 1 s)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

local instance : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- Paper: (12.4.1.4)–(12.4.1.7) and (12.5.1.3), pp. 515–516, 519–520.
For each compact S-idelic lift of the global test, the normalized scalar dilation acts
on evaluation at zero and on the additive integral by the global polar Mellin values
at exponents −1/2 and +1/2, after conversion by the norm-one volumes.
Deviation: The result acts on the two moments of additive Schwartz–Bruhat tests.
The cutoff Paley–Wiener trace and the global strip diagonal require a separate
comparison. -/
theorem sLocalTraceLift_global_polar_moments
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽),
      φ.val (QuotientGroup.mk u.val * x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ g : Iₛ,
      HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S g))))
    (b : SchwartzBruhat (Multiplicative Aₛ)) :
    let k := sLocalTraceDilationKernel f (fun x ↦ b (Multiplicative.ofAdd x))
    ((vF / vS).toReal • k 0, (vF / vS).toReal • ∫ x, k x ∂νₛ) =
      (M(φ.val, -(1 / 2)) * b (Multiplicative.ofAdd 0),
       M(φ.val, 1 / 2) * sAdeleSchwartzFourier b (Multiplicative.ofAdd 0)) := by
  have hpow (g : Iₛ) : (((sIdeleNorm F S g).val : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt ((sIdeleNorm F S g).val : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    norm_num
  have hplus := sLocalTraceLift_global_normPowerMellin hPic φ hout f hLift (1 / 2)
  have hminus := sLocalTraceLift_global_normPowerMellin hPic φ hout f hLift (-(1 / 2))
  simp only [hpow] at hplus
  simp only [Complex.cpow_neg, hpow, ← div_eq_mul_inv] at hminus
  obtain ⟨hc, hi⟩ := sLocalTraceTest_continuous_integrable b
  have h := (sLocalTraceDilationKernel_polar_moments f _ hc hi).2
  dsimp only
  rw [sAdeleSchwartzFourier_apply_zero, hplus, hminus, smul_mul_assoc, smul_mul_assoc]
  exact Prod.ext (congrArg ((vF / vS).toReal • ·) (congrArg Prod.fst h))
    (congrArg ((vF / vS).toReal • ·) (congrArg Prod.snd h))

/-- Paper: (12.5.1.3), pp. 519–520. The induced endomorphism of the two-dimensional
space of polar moments is unique, and its trace is the sum of the two global polar
Mellin values. Every pair occurs already on the additive Paley–Wiener test space
with unrestricted Fourier region. The normalization is the same as in the preceding
moment identity. -/
theorem sLocalTraceLift_global_polar_trace
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽),
      φ.val (QuotientGroup.mk u.val * x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ g : Iₛ,
      HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S g)))) :
    ∃! A : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ),
      (∀ b : SchwartzBruhat (Multiplicative Aₛ),
        let k := sLocalTraceDilationKernel f (fun x ↦ b (Multiplicative.ofAdd x))
        A (b (Multiplicative.ofAdd 0), sAdeleSchwartzFourier b (Multiplicative.ofAdd 0)) =
          ((vF / vS).toReal • k 0, (vF / vS).toReal • ∫ x, k x ∂νₛ)) ∧
      LinearMap.trace ℂ (ℂ × ℂ) A = M(φ.val, 1 / 2) + M(φ.val, -(1 / 2)) := by
  let A := LinearMap.prodMap (M(φ.val, -(1 / 2)) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
    (M(φ.val, 1 / 2) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
  have hA (b : SchwartzBruhat (Multiplicative Aₛ)) :=
    (sLocalTraceLift_global_polar_moments hPic φ hout f hLift b).symm
  refine ⟨A, ⟨hA, ?_⟩, ?_⟩
  · simp [A, LinearMap.trace_prodMap', LinearMap.trace_id, add_comm]
  · rintro B ⟨hB, -⟩
    apply LinearMap.ext
    rintro ⟨x, y⟩
    obtain ⟨b, -, hx, hy⟩ := sLocalPWTests_moments_surjective (F := F) (S := S) (T := S)
      Subset.rfl univ Filter.univ_mem x y
    rw [← hx, ← hy]
    exact (hB b).trans (hA b).symm

section SharpLimit

open Filter
open scoped Topology

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- Paper: (12.4.1.25)–(12.4.1.28) and (12.5.1.3), pp. 519–520. After dividing the
sharp S-unit orbital sum by the local norm-one volume and removing its logarithmic
term, subtracting the trace of the two polar moments gives the sum of the local
principal values less the two global polar Mellin integrals.
Deviation: This limit concerns the literal sharp orbital sum of (12.4.1.24). Identifying
it with the remaining global diagonal on p. 520 requires the missing §12.3 comparison. -/
theorem sLocalTraceSharpMass_sub_polar_trace_tendsto
    (hPic : Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)))
    (hRamified : ∀ v : HeightOneSpectrum (𝓞 F), differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (φ : BruhatCompactSupport C𝔽)
    (hout : ∀ (u : outsideIntegralIdeleUnits F S) (x : C𝔽),
      φ.val (QuotientGroup.mk u.val * x) = φ.val x)
    (f : BruhatCompactSupport Iₛ) (hLift : ∀ g : Iₛ,
      HasSum (fun ξ : sProjectedDiagonal F S ↦ f.val (ξ.val * g))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S g)))) :
    ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
      (b : (v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
      (A : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ)),
      (∀ w u, (a w).val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
      (∀ (v : S) u, (b v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v.val u)) ∧
      (∀ p : SchwartzBruhat (Multiplicative Aₛ),
        let k := sLocalTraceDilationKernel f (fun x ↦ p (Multiplicative.ofAdd x))
        A (p (Multiplicative.ofAdd 0), sAdeleSchwartzFourier p (Multiplicative.ofAdd 0)) =
          ((vF / vS).toReal • k 0, (vF / vS).toReal • ∫ x, k x ∂νₛ)) ∧
      Tendsto (fun R : ℝ ↦ (∑' ξ : sProjectedDiagonal F S, sLocalTraceSharpMass f ξ R) /
          ((vS).toReal : ℂ) - φ.val 1 * (Real.log R : ℂ) - LinearMap.trace ℂ (ℂ × ℂ) A)
        atTop (𝓝 (principalValues(a, b) - (M(φ.val, 1 / 2) + M(φ.val, -(1 / 2))))) := by
  obtain ⟨a, b, mass, ha, hb, hsum, hlim⟩ := sLocalTraceSharpMass_asymptotic φ hPic hRamified hout f hLift
  obtain ⟨A, ⟨hA, htr⟩, -⟩ := sLocalTraceLift_global_polar_trace hPic φ hout f hLift
  refine ⟨a, b, A, ha, hb, hA, ?_⟩
  let G := (sIdeleQuotientNorm F S).ker
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hv : ((vS).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨isOpen_univ.measure_ne_zero μ univ_nonempty, measure_ne_top μ univ⟩)
  have hn := hlim.div_const ((vS).toReal : ℂ)
  rw [mul_div_cancel_left₀ _ hv] at hn
  refine (hn.sub_const (M(φ.val, 1 / 2) + M(φ.val, -(1 / 2)))).congr' ?_
  filter_upwards [hsum] with R hR
  rw [hR.tsum_eq, htr]
  field_simp

end SharpLimit

end RiemannMasullo
