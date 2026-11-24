module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import all RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # Inversion symmetry of the normalized local Weil terms

For complex places the local absolute value is the square of the ordinary
complex modulus. The resulting kernel is invariant under inversion, as are
the real and finite kernels. The complex calculation below removes the
finite-part cutoff for tests vanishing near the identity.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

local notation "ν(" w ")" => infiniteLocalAdditiveTamagawaMeasure F w
local notation "μ(" w ")" => infiniteLocalMultiplicativeTamagawaMeasure F w
local notation "addTest(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))

/-- Paper: Definition B.4.4.1, p. 619, and Proposition B.4.3.2(2), p. 619.
At a complex place, the additive principal value on tests vanishing near zero
is the ordinary integral with weight `1/(2π ‖x‖²)` for additive Tamagawa measure.
Deviation: The constant uses the Fourier normalization recorded in Appendix B. -/
theorem complexConnesPrincipalValue_of_zero_near (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion))
    (hf : ∀ᶠ x : w.Completion in 𝓝 0, addTest(f) x = 0) :
    infiniteConnesPrincipalValue w f =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ x, addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂ν(w) := by
  have h0 : addTest(f) 0 = 0 := hf.self_of_nhds
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hf
  have hL := (complexLogFourier_finitePart w hw f).2.2
  have hT := ((exists_infiniteConnesPrincipalValue w).choose_spec f).2
  change infiniteConnesPrincipalValue w f = _ at hT
  simp only [h0, mul_zero, zero_mul, add_zero] at hL
  let g (x : w.Completion) := addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ)
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2}, g x ∂ν(w))
      (𝓝[>] 0) (𝓝 (∫ x, g x ∂ν(w))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (sq_pos_of_pos hδ))] with ε hε
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hsmall : ‖x‖ < δ := by
      change ¬ ε ≤ ‖x‖ ^ 2 at hx
      nlinarith [lt_of_not_ge hx, norm_nonneg x]
    have hz := hball (show dist x 0 < δ by simpa using hsmall)
    simp only [g, hz, zero_div]
  have he := tendsto_nhds_unique hlim hL
  rw [hT, he]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Paper: Definition B.4.4.1(2), p. 620. For a complex place and a test
vanishing near one, the normalized multiplicative principal value is the
ordinary Tamagawa integral of `f(u) ‖u‖ / ‖1-u‖²` divided by `2π`.
Deviation: The denominator uses the normalized complex absolute value. -/
theorem complexConnesWeilPrincipalValue_of_zero_near (w : InfinitePlace F) (hw : w.IsComplex)
    (f : BruhatCompactSupport w.Completionˣ) (hf : ∀ᶠ u in 𝓝 1, f.val u = 0) :
    infiniteConnesWeilPrincipalValue w f = (2 * (Real.pi : ℂ))⁻¹ *
      ∫ u : w.Completionˣ, f.val u * (‖u.val‖ : ℂ) / ((‖1-u.val‖ ^ 2 : ℝ) : ℂ) ∂μ(w) := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  let A := (exists_infiniteWeilTestMap w).choose
  have hA := (exists_infiniteWeilTestMap w).choose_spec f
  let Fz := Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ 0)
  have hFu (u : w.Completionˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have hFz (y : w.Completion) (hy : y ∉ range (Units.val : w.Completionˣ → w.Completion)) :
      Fz y = 0 := by simp only [Fz, Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ hy ⟨u, hu⟩)]
  have hzero : ∀ᶠ y : w.Completion in 𝓝 1, Fz y = 0 := by
    have he := IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)
    change ∀ᶠ y in 𝓝 ((1 : w.Completionˣ).val), Fz y = 0
    rw [← he.map_nhds_eq]
    exact hf.mono fun u hu ↦ (hFu u).trans hu
  have ht : Tendsto (fun x : w.Completion ↦ 1 + x) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun x : w.Completion ↦ 1 + x) := by fun_prop
    have ht := hc.tendsto 0
    change Tendsto (fun x : w.Completion ↦ 1 + x) (𝓝 0) (𝓝 (1+0)) at ht
    simpa only [add_zero] using ht
  have hz : ∀ᶠ x : w.Completion in 𝓝 0, addTest(A f) x = 0 := by
    filter_upwards [ht.eventually hzero] with x hx
    have := hA x
    change addTest(A f) x = Fz (1+x) / _ at this
    exact this.trans (by rw [hx, zero_div])
  change infiniteConnesPrincipalValue w (A f) = _
  rw [complexConnesPrincipalValue_of_zero_near w hw (A f) hz]
  congr 1
  let G (y : w.Completion) := Fz y / (‖y‖ : ℂ) / ((‖y-1‖ ^ 2 : ℝ) : ℂ)
  have hpoint (x : w.Completion) : addTest(A f) x / ((‖x‖ ^ 2 : ℝ) : ℂ) = G (1+x) := by
    rw [hA]
    simp only [G, Fz, hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _), add_sub_cancel_left]
  have : (ν(w)).IsAddHaarMeasure := infiniteLocalAdditiveTamagawaMeasure_isAddHaar F w
  simp_rw [hpoint]
  rw [integral_add_left_eq_self G 1]
  let d (y : w.Completion) : ℝ≥0∞ := (↑(‖y‖₊ ^ w.mult) : ℝ≥0∞)⁻¹
  have hd : Measurable d := by dsimp only [d]; fun_prop
  simp only [← hFu]
  change _ = ∫ u : w.Completionˣ, _ ∂((ν(w)).withDensity d).comap Units.val
  rw [← hval.integral_map (g := fun y ↦ Fz y * (‖y‖ : ℂ) / ((‖1-y‖ ^ 2 : ℝ) : ℂ)),
    hval.map_comap, setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _ hval.measurableSet_range,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
      (fun y hy ↦ by simp only [G, hFz y hy, zero_div])]
  · refine setIntegral_congr_fun hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    have hy : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hu ▸ u.ne_zero))
    simp only [G, d, hw.mult_eq_two, ENNReal.toReal_inv, ENNReal.coe_toReal, NNReal.coe_pow,
      coe_nnNorm, Complex.real_smul, norm_sub_rev (1 : w.Completion) y]
    push_cast
    field_simp
  · refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    simp [d, hw.mult_eq_two, ← hu]
    exact pos_iff_ne_zero.mpr (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (nnNorm_ne_zero_iff.mpr u.ne_zero)))

private theorem zero_integral_of_inv_neg {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (μ : Measure G) [μ.IsInvInvariant] (f : G → ℂ) (hf : ∀ u, f u⁻¹ = -f u) :
    (∫ u, f u ∂μ) = 0 := by
  have h := integral_inv_eq_self f μ
  simp only [hf, integral_neg] at h
  linear_combination -h / 2

private theorem local_weight_inv {K : Type*} [NormedField K] (u : Kˣ) (n : ℕ) :
    Real.sqrt (‖(u⁻¹).val‖ ^ n) / ‖1 - (u⁻¹).val‖ ^ n =
      Real.sqrt (‖u.val‖ ^ n) / ‖1 - u.val‖ ^ n := by
  have hid : 1 - u.val⁻¹ = -((1-u.val)/u.val) := by field_simp; ring
  have hp : 0 < ‖u.val‖ ^ n := pow_pos (norm_pos_iff.mpr u.ne_zero) _
  rw [Units.val_inv_eq_inv_val, norm_inv, inv_pow, Real.sqrt_inv, hid, norm_neg, norm_div, div_pow]
  have hsq := Real.sq_sqrt hp.le
  have hs := Real.sqrt_pos.mpr hp
  by_cases hz : ‖1-u.val‖ ^ n = 0
  · simp only [hz, zero_div, div_zero]
  · field_simp
    nlinarith

private theorem local_integral_of_inv_odd {K : Type*} [NormedField K]
    [MeasurableSpace Kˣ] [MeasurableInv Kˣ] (μ : Measure Kˣ) [μ.IsInvInvariant]
    (f : Kˣ → ℂ) (hf : ∀ u, f u⁻¹ = -f u) (n : ℕ) :
    (∫ u : Kˣ, f u * (Real.sqrt (‖u.val‖ ^ n) : ℂ) / ((‖1-u.val‖ ^ n : ℝ) : ℂ) ∂μ) = 0 := by
  apply zero_integral_of_inv_neg
  intro u
  rw [hf, neg_mul, neg_div, neg_inj, mul_div_assoc, mul_div_assoc]
  exact congrArg (f u * ·) (by exact_mod_cast local_weight_inv u n)

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

/-- Paper: Definition B.4.4.1(2), p. 620. The finite-place principal value
annihilates any compact Bruhat test odd under inversion. -/
theorem finiteWeilPrincipalValue_of_inv_odd (v : HeightOneSpectrum (𝓞 F))
    (f : BruhatCompactSupport (v.adicCompletion F)ˣ) (hf : ∀ u, f.val u⁻¹ = -f.val u) :
    finiteConnesWeilPrincipalValue v 1 f = 0 := by
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : SecondCountableTopology (v.adicCompletion F)ˣ :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).secondCountableTopology
  have : (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_haar F v
  have h1 := hf 1
  rw [inv_one] at h1
  rw [(finiteConnesWeilPrincipalValue_of_apply_one_zero v f (by linear_combination h1 / 2)).2]
  simpa only [pow_one] using
    local_integral_of_inv_odd (finiteLocalMultiplicativeTamagawaMeasure F v) f.val hf 1

/-- Paper: Definition B.4.4.1(2), p. 620, with the corrected archimedean
normalization. At a real place an inversion-odd test has zero principal
value. At a complex place the same holds for tests vanishing near one. -/
theorem infiniteWeilPrincipalValue_of_inv_odd (w : InfinitePlace F)
    (f : BruhatCompactSupport w.Completionˣ) (hf : ∀ u, f.val u⁻¹ = -f.val u)
    (hnear : w.IsComplex → ∀ᶠ u in 𝓝 1, f.val u = 0) :
    infiniteConnesWeilPrincipalValue w f = 0 := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  have : (μ(w)).IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  by_cases hw : w.IsReal
  · have h1 := hf 1
    rw [inv_one] at h1
    rw [realConnesWeilPrincipalValue_of_apply_one_zero w hw f (by linear_combination h1 / 2)]
    exact mul_eq_zero_of_right _ (by simpa only [pow_one] using local_integral_of_inv_odd μ(w) f.val hf 1)
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [complexConnesWeilPrincipalValue_of_zero_near w hc f (hnear hc)]
    exact mul_eq_zero_of_right _ (by
      simpa only [Real.sqrt_sq (norm_nonneg _)] using local_integral_of_inv_odd μ(w) f.val hf 2)

end RiemannMasullo.StripNuclearity
