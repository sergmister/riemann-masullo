module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-!
# Printed cutoff and spectral lift claims in §§10.4.1–10.4.2

The corresponding truncation and lift declarations are in `Sec4a.lean`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped Classical NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
local notation "μ[" F "]" => ideleClassTamagawaMeasure F
local notation "logNorm[" F "]" => fun g : C[F] ↦ Real.log ((ideleClassNorm F g).val : ℝ)

/-- Paper: §10.4, introduction, p. 455. As printed: on the symmetric
interval Sobolev space, multiplication by a smooth cutoff has closed range.
The multiplier used in `spectralTruncation` is bounded (ERRATA F186). -/
def Printed.smoothCutoffMultiplier_isClosedRange : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α s : ℝ), 0 ≤ α → 1 < s →
    ∀ (Λ ε : ℝ) (ρ : C[F] → ℝ) (hρ : IsSmoothModulatedCutoff m[F] Λ ε ρ),
      let ν := (μ[F]).withDensity (fun g ↦
        ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm[F] g)))
      IsClosed (range (modulatedCutoffOperator m[F] ν hρ.1))

private theorem sec4a_not_isClosed_range_of_small_images {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hclosed : IsClosed (Set.range T))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ u : E, ‖u‖ ≠ 0 ∧ ‖T u‖ ≤ δ * ‖u‖ ∧
      ∀ x : E, T x = T u → ‖u‖ ≤ ‖x‖) : False := by
  have hclosed' : IsClosed (LinearMap.range (T : E →ₗ[ℂ] E) : Set E) := by
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hclosed
  have : CompleteSpace (LinearMap.range (T : E →ₗ[ℂ] E)) := hclosed'.completeSpace_coe
  let S : E →L[ℂ] LinearMap.range (T : E →ₗ[ℂ] E) :=
    T.codRestrict (LinearMap.range (T : E →ₗ[ℂ] E)) fun x ↦ ⟨x, rfl⟩
  have hsurj : Function.Surjective S := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨C, hCpos, hC⟩ := S.exists_preimage_norm_le hsurj
  obtain ⟨u, hu_ne, hu_img, hu_min⟩ := hsmall (1 / (2 * C)) (by positivity)
  obtain ⟨x, hx_eq, hx_norm⟩ := hC (S u)
  have hTx : T x = T u := congrArg Subtype.val hx_eq
  have hu_le_x : ‖u‖ ≤ ‖x‖ := hu_min x hTx
  have hx_le : ‖x‖ ≤ C * ‖T u‖ := hx_norm
  have hu_le : ‖u‖ ≤ (1 / 2 : ℝ) * ‖u‖ := by
    calc ‖u‖ ≤ ‖x‖ := hu_le_x
      _ ≤ C * ‖T u‖ := hx_le
      _ ≤ C * ((1 / (2 * C)) * ‖u‖) := mul_le_mul_of_nonneg_left hu_img hCpos.le
      _ = (1 / 2 : ℝ) * ‖u‖ := by field_simp [hCpos.ne']
  have hupos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) hu_ne.symm
  linarith

private theorem sec4a_small_cutoff_measure {ρ : C[ℚ] → ℝ}
    (hρ : IsSmoothModulatedCutoff m[ℚ] 2 (1 / 4) ρ) (δ : ℝ) (hδ : 0 < δ) :
    let ν := (μ[ℚ]).withDensity (fun g ↦
      ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)))
    let U := ρ ⁻¹' Ioo 0 δ
    MeasurableSet U ∧ 0 < ν U ∧ ν U < ⊤ := by
  intro ν U
  have hUopen : IsOpen U := isOpen_Ioo.preimage hρ.continuous
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  let uReal : ℝ → ℝ≥0ˣ := fun t ↦
    ⟨⟨max t (2⁻¹ : ℝ), by positivity⟩, ⟨(max t (2⁻¹ : ℝ))⁻¹, by positivity⟩,
      Subtype.ext (mul_inv_cancel₀ (by positivity)),
      Subtype.ext (inv_mul_cancel₀ (by positivity))⟩
  have huReal : Continuous uReal := by
    rw [Units.continuous_iff]
    exact ⟨(continuous_id.max continuous_const).subtype_mk _,
      ((continuous_id.max continuous_const).inv₀ fun _ ↦ by positivity).subtype_mk _⟩
  let σ : ℝ → C[ℚ] := fun t ↦
    QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) (ratIdeleNormSection (uReal t))
  have hσ : Continuous σ :=
    QuotientGroup.continuous_mk.comp (ratIdeleNormSection_continuous.comp huReal)
  have hσm (t : ℝ) (ht : (2⁻¹ : ℝ) ≤ t) : ((m[ℚ] (σ t)).val : ℝ) = t := by
    change ((ideleClassNorm ℚ (σ t)).val : ℝ) = t
    rw [show ideleClassNorm ℚ (σ t) = uReal t from ratIdeleNormSection_class_rightInverse (uReal t)]
    exact max_eq_left ht
  have hUne : U.Nonempty := by
    have hρ1 : ρ (σ 1) = 1 := hρ.1.eq_one (by
      change ((m[ℚ] (σ 1)).val : ℝ) ∈ Icc ((2 : ℝ)⁻¹ + 1 / 4) (2 - 1 / 4)
      rw [hσm 1 (by norm_num)]
      norm_num)
    have hρ3 : ρ (σ 3) = 0 := by
      by_contra hne
      have hsub := hρ.1.support_subset (subset_closure (Function.mem_support.mpr hne))
      change ((m[ℚ] (σ 3)).val : ℝ) ∈ Icc (2⁻¹ : ℝ) 2 at hsub
      rw [hσm 3 (by norm_num)] at hsub
      linarith [hsub.2]
    let δ₀ : ℝ := min (δ / 2) (1 / 2)
    have hδ₀_mem : δ₀ ∈ Icc (ρ (σ 3)) (ρ (σ 1)) := by
      rw [hρ3, hρ1]
      exact ⟨le_min (by linarith) (by norm_num), min_le_of_right_le (by norm_num)⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc' (show (1 : ℝ) ≤ 3 by norm_num)
      (hρ.continuous.comp hσ).continuousOn hδ₀_mem
    refine ⟨σ t, ?_⟩
    have ht' : ρ (σ t) = δ₀ := ht
    change ρ (σ t) ∈ Ioo 0 δ
    rw [ht']
    exact ⟨lt_min (by linarith) (by norm_num), (min_le_left _ _).trans_lt (by linarith)⟩
  have hHaar : (μ[ℚ]).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  have hμpos : 0 < μ[ℚ] U := hUopen.measure_pos (μ[ℚ]) hUne
  have hw_ge (g : C[ℚ]) :
      (1 : ENNReal) ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    dsimp [intervalSobolevDensity]
    norm_num
    exact sq_nonneg _
  have hνpos : 0 < ν U := by
    refine hμpos.trans_le ?_
    rw [withDensity_apply _ hUmeas]
    calc μ[ℚ] U = ∫⁻ _ in U, (1 : ENNReal) ∂μ[ℚ] := by simp
      _ ≤ ∫⁻ g in U, ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) ∂μ[ℚ] :=
        setLIntegral_mono' hUmeas fun g _ ↦ hw_ge g
  let K' : Set ℝ≥0ˣ := uReal '' Icc (2⁻¹ : ℝ) 2
  have hK'compact : IsCompact K' := isCompact_Icc.image huReal
  let K : Set C[ℚ] := m[ℚ] ⁻¹' K'
  have hKcompact : IsCompact K := (isProperMap_ideleClassNorm ℚ).isCompact_preimage hK'compact
  have hKmeas : MeasurableSet K := (hK'compact.isClosed.preimage m[ℚ].continuous).measurableSet
  have hμK_lt_top : μ[ℚ] K < ⊤ := hKcompact.measure_lt_top
  have hUK : U ⊆ K := by
    intro g hg
    have hsupp := hρ.1.support_subset (subset_closure (Function.mem_support.mpr hg.1.ne'))
    change ((m[ℚ] g).val : ℝ) ∈ Icc (2⁻¹ : ℝ) 2 at hsupp
    refine ⟨((m[ℚ] g).val : ℝ), hsupp, ?_⟩
    apply Units.ext
    ext
    exact max_eq_left hsupp.1
  have hw_le (g : C[ℚ]) (hg : g ∈ K) :
      ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) ≤
        ENNReal.ofReal (1 + (Real.log 2) ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨r, hr, hrg⟩ := hg
    have hmr : ((ideleClassNorm ℚ g).val : ℝ) = r := by
      have : (m[ℚ] g).val = (uReal r).val := congrArg Units.val hrg.symm
      exact (congrArg NNReal.toReal this).trans (max_eq_left hr.1)
    have hlog_le : |Real.log r| ≤ Real.log 2 := by
      rw [abs_le, ← Real.log_inv]
      have hrpos : 0 < r := by linarith [hr.1]
      exact ⟨(Real.log_le_log_iff (by norm_num) hrpos).mpr hr.1,
        (Real.log_le_log_iff hrpos (by norm_num)).mpr hr.2⟩
    have hsq : (Real.log ((ideleClassNorm ℚ g).val : ℝ)) ^ 2 ≤ (Real.log 2) ^ 2 := by
      rw [hmr, ← sq_abs (Real.log r)]
      exact pow_le_pow_left₀ (abs_nonneg _) hlog_le 2
    dsimp [intervalSobolevDensity]
    norm_num
    linarith [hsq]
  have hνfin : ν U < ⊤ := by
    calc ν U ≤ ν K := measure_mono hUK
      _ = ∫⁻ g in K, ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) ∂μ[ℚ] :=
        withDensity_apply _ hKmeas
      _ ≤ ∫⁻ _ in K, ENNReal.ofReal (1 + (Real.log 2) ^ 2) ∂μ[ℚ] :=
        setLIntegral_mono' hKmeas hw_le
      _ = ENNReal.ofReal (1 + (Real.log 2) ^ 2) * μ[ℚ] K := setLIntegral_const K _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK_lt_top
  exact ⟨hUmeas, hνpos, hνfin⟩

/-- Paper: §10.4, introduction, p. 455. Use `F = ℚ`, `α = 0`, `s = 2`,
`Λ = 2` and `ε = 1/4`. In log norm choose an even smooth cutoff equal to
one on `|x| ≤ log(7/4)`, strictly tapering on `log(7/4) < |x| < log 2`,
and zero on `|x| ≥ log 2`. The normalized indicators of `0 < ρ < 1/n`
are unit vectors perpendicular to the kernel and their images have norm at
most `1/n`, contradicting the lower bound for an operator with closed range. -/
theorem Printed.smoothCutoffMultiplier_isClosedRange_false :
    ¬ Printed.smoothCutoffMultiplier_isClosedRange := by
  intro h
  have hmℚ : IsModulation m[ℚ] := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  have hmsℚ : Function.Surjective m[ℚ] := ratIdeleNormSection_class_rightInverse.surjective
  obtain ⟨ρ, hρ⟩ := exists_smoothModulatedCutoff_radius_two m[ℚ] hmℚ hmsℚ
  let ν := (μ[ℚ]).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)))
  let ν₀ := (μ[ℚ]).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity (-(0 : ℝ)) 0 2 (logNorm[ℚ] g)))
  have hνeq : ν₀ = ν := by dsimp only [ν₀, ν]; simp only [neg_zero]
  let T := modulatedCutoffOperator m[ℚ] ν hρ.1
  have hclosed0 : IsClosed (Set.range (modulatedCutoffOperator m[ℚ] ν₀ hρ.1)) :=
    h ℚ 0 2 (by norm_num) (by norm_num) 2 (1 / 4) ρ hρ
  have hclosed : IsClosed (Set.range T) := by
    dsimp only [T]
    rw [← hνeq]
    exact hclosed0
  refine sec4a_not_isClosed_range_of_small_images T hclosed fun δ hδ ↦ ?_
  obtain ⟨hUmeas, hUpos, hUfin⟩ := sec4a_small_cutoff_measure hρ δ hδ
  let U : Set C[ℚ] := ρ ⁻¹' Ioo 0 δ
  let u : Lp ℂ 2 ν := indicatorConstLp 2 hUmeas hUfin.ne (1 : ℂ)
  refine ⟨u, ?_, ?_, ?_⟩
  · have hnorm : ‖u‖ = ‖(1 : ℂ)‖ * ν.real U ^ (1 / (2 : ENNReal).toReal) :=
      norm_indicatorConstLp (by norm_num) (by norm_num)
    have hreal : 0 < ν.real U := ENNReal.toReal_pos hUpos.ne' hUfin.ne
    have hpos : 0 < ‖u‖ := by
      rw [hnorm, norm_one, one_mul]
      exact Real.rpow_pos_of_pos hreal _
    exact hpos.ne'
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [modulatedCutoffOperator_apply m[ℚ] ν hρ.1 u,
      indicatorConstLp_coeFn (p := 2) (hs := hUmeas) (hμs := hUfin.ne) (c := (1 : ℂ))] with g hTg hug
    change ‖T u g‖ ≤ δ * ‖u g‖
    rw [hTg, norm_mul, Complex.norm_real]
    by_cases hg : g ∈ U
    · have hρ_abs : |ρ g| ≤ δ := by
        have hmem : ρ g ∈ Ioo 0 δ := hg
        rw [abs_of_pos hmem.1]
        exact hmem.2.le
      exact mul_le_mul_of_nonneg_right hρ_abs (norm_nonneg _)
    · have hu0 : u g = 0 := hug.trans (indicator_of_notMem hg _)
      simp [hu0]
  · intro x hTx
    apply Lp.norm_le_norm_of_ae_le
    have hEq : (T x : C[ℚ] → ℂ) =ᵐ[ν] (T u : C[ℚ] → ℂ) := by rw [hTx]
    filter_upwards [hEq, modulatedCutoffOperator_apply m[ℚ] ν hρ.1 x,
      modulatedCutoffOperator_apply m[ℚ] ν hρ.1 u,
      indicatorConstLp_coeFn (p := 2) (hs := hUmeas) (hμs := hUfin.ne) (c := (1 : ℂ))]
      with g hgg hx hu hug
    by_cases hg : g ∈ U
    · have hρne : (ρ g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show ρ g ≠ 0 from hg.1.ne')
      have hmul : (ρ g : ℂ) * x g = (ρ g : ℂ) * u g := by
        rw [← hx, ← hu]
        exact hgg
      have hux : u g = x g := (mul_left_cancel₀ hρne hmul).symm
      rw [hux]
    · have hu0 : u g = 0 := hug.trans (indicator_of_notMem hg _)
      simp [hu0]

/-- Paper: Remark 10.4.2.3, p. 460. As printed: at each admissible radius
the cutoff is continuous on the idele class group. This is the continuity
clause following (10.4.2.10). The cutoff hypotheses of
`spectralTruncatedConvolution_trace_tendsto` allow piecewise smooth profiles (ERRATA F188). -/
def Printed.spectralCutoffFamily_continuous : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ε : ℝ → ℝ) (ρ : ℝ → C[F] → ℝ),
    Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) →
    let admissible := fun Λ ↦ IsModulatedCutoff m[F] Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ
    (∀ᶠ Λ in atTop, admissible Λ) → ∀ Λ, admissible Λ → Continuous (ρ Λ)

private theorem sec4a_ideleClassNorm_rat_surjective :
    Function.Surjective (ideleClassNorm ℚ) :=
  ratIdeleNormSection_class_rightInverse.surjective

private theorem sec4a_eventuallyEq_iteratedDeriv_const {c : ℝ} {s : Set ℝ} (hs : IsOpen s)
    {q : ℝ → ℝ} (hq : EqOn q (fun _ ↦ c) s) (n : ℕ) :
    EqOn (iteratedDeriv n q) (fun _ ↦ if n = 0 then c else 0) s := by
  intro x hx
  have heq : q =ᶠ[𝓝 x] fun _ ↦ c := Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hx, hq⟩
  rw [(heq.iteratedDeriv n).eq_of_nhds]
  rcases n with _ | n
  · simp
  · simp [iteratedDeriv_const]

private theorem sec4a_sharpCutoff_admissible (Λ : ℝ) (hΛ : 2 ≤ Λ) :
    let ε : ℝ := 1 / (2 * Λ ^ 2)
    let ρ : C[ℚ] → ℝ := fun g ↦
      if ((m[ℚ] g).val : ℝ) ∈ Icc Λ⁻¹ Λ then 1 else 0
    IsModulatedCutoff m[ℚ] Λ ε ρ ∧ 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε := by
  intro ε ρ
  have hΛpos : 0 < Λ := by linarith
  have hεpos : 0 < ε := by positivity
  have hΛinv_le_one : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have h2ε_lt : 2 * ε < Λ⁻¹ := by
    dsimp [ε]
    rw [show 2 * (1 / (2 * Λ ^ 2)) = (Λ ^ 2)⁻¹ by ring]
    exact inv_strictAnti₀ (by positivity) (by nlinarith)
  have hε_lt_inv : ε < Λ⁻¹ := by linarith
  have h_sub_pos : 0 < Λ⁻¹ - ε := sub_pos.mpr hε_lt_inv
  have h_left_lt_right : Λ⁻¹ + ε < Λ - ε := by
    have hhalf : Λ⁻¹ ≤ 1 / 2 := by simpa only [one_div] using inv_anti₀ (by norm_num) hΛ
    have h2ε_lt_one : 2 * ε < 1 := by linarith
    linarith
  have h_sub_lt : Λ⁻¹ - ε < Λ - ε := by linarith
  refine ⟨⟨hΛpos, hεpos, h_sub_pos, h_sub_lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by positivity, h_left_lt_right⟩
  · intro x
    dsimp [ρ]
    split_ifs <;> norm_num
  · intro x
    dsimp [ρ]
    split_ifs <;> norm_num
  · apply IsGreatest.csSup_eq
    refine ⟨⟨1, ?_⟩, forall_mem_range.mpr fun x ↦ ?_⟩
    · dsimp [ρ]
      rw [map_one, Units.val_one, NNReal.coe_one]
      split_ifs with h1
      · rfl
      · exact False.elim (h1 ⟨hΛinv_le_one, by linarith⟩)
    · dsimp [ρ]
      split_ifs <;> norm_num
  · let q : ℝ → ℝ := fun r ↦ if r ∈ Icc Λ⁻¹ Λ then 1 else 0
    have hq0 : EqOn q (fun _ ↦ 0) (Iio Λ⁻¹) := fun r hr ↦ by
      dsimp [q]; split_ifs with hmem; exact False.elim (not_le_of_gt hr hmem.1); rfl
    have hq1 : EqOn q (fun _ ↦ 1) (Ioo Λ⁻¹ Λ) := fun r hr ↦ by
      dsimp [q]; split_ifs with hmem; rfl; exact False.elim (hmem ⟨hr.1.le, hr.2.le⟩)
    have hq2 : EqOn q (fun _ ↦ 0) (Ioi Λ) := fun r hr ↦ by
      dsimp [q]; split_ifs with hmem; exact False.elim (not_le_of_gt hr hmem.2); rfl
    refine ⟨q, {Λ⁻¹, Λ}, fun x ↦ rfl, ?_, ?_, ?_⟩
    · intro c hc
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · exact inv_pos.mpr hΛpos
      · exact hΛpos
    · intro r hr
      rcases lt_trichotomy r Λ⁻¹ with hlt | rfl | hgt
      · exact (contDiffOn_const.congr hq0).contDiffAt (isOpen_Iio.mem_nhds hlt) |>.contDiffWithinAt
      · exact False.elim (hr.2 (by simp))
      · rcases lt_trichotomy r Λ with hlt' | rfl | hgt'
        · exact (contDiffOn_const.congr hq1).contDiffAt (isOpen_Ioo.mem_nhds ⟨hgt, hlt'⟩) |>.contDiffWithinAt
        · exact False.elim (hr.2 (by simp))
        · exact (contDiffOn_const.congr hq2).contDiffAt (isOpen_Ioi.mem_nhds hgt') |>.contDiffWithinAt
    · intro c hc n
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with hc_eq | hc_eq <;> rw [hc_eq]
      · refine ⟨if n = 0 then 0 else 0, if n = 0 then 1 else 0, ?_, ?_⟩
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact (sec4a_eventuallyEq_iteratedDeriv_const isOpen_Iio hq0 n hy).symm
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [Ioo_mem_nhdsGT (show Λ⁻¹ < Λ by linarith)] with y hy
          exact (sec4a_eventuallyEq_iteratedDeriv_const isOpen_Ioo hq1 n hy).symm
      · refine ⟨if n = 0 then 1 else 0, if n = 0 then 0 else 0, ?_, ?_⟩
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [Ioo_mem_nhdsLT (show Λ⁻¹ < Λ by linarith)] with y hy
          exact (sec4a_eventuallyEq_iteratedDeriv_const isOpen_Ioo hq1 n hy).symm
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact (sec4a_eventuallyEq_iteratedDeriv_const isOpen_Ioi hq2 n hy).symm
  · intro x
    dsimp [ρ]
    have hpos : 0 < ((m[ℚ] x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
    congr 1
    simp only [mem_Icc]
    refine propext ⟨fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩, fun ⟨h1, h2⟩ ↦ ⟨?_, ?_⟩⟩
    · exact (le_inv_comm₀ (inv_pos.mpr hΛpos) hpos).mpr (by simpa only [inv_inv] using h2)
    · exact (inv_le_comm₀ hpos hΛpos).mpr h1
    · exact (inv_le_comm₀ hpos hΛpos).mp h2
    · exact by simpa only [inv_inv] using (le_inv_comm₀ (inv_pos.mpr hΛpos) hpos).mp h1
  · apply closure_minimal _
      (isClosed_Icc.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m[ℚ].continuous)))
    intro x hx
    dsimp only [ρ] at hx ⊢
    by_contra hnot
    apply hx
    change (if ((m[ℚ] x).val : ℝ) ∈ Icc Λ⁻¹ Λ then (1 : ℝ) else 0) = 0
    split_ifs with hmem
    · exact False.elim (hnot hmem)
    · rfl
  · intro x hx
    dsimp [ρ]
    split_ifs with hmem
    · rfl
    · exact False.elim (hmem ⟨by linarith [hx.1], by linarith [hx.2]⟩)

/-- Paper: Remark 10.4.2.3, p. 460. Over ℚ take `ε(Λ) = 1/(2Λ²)` and
let `ρ(Λ)` be the indicator of `Λ⁻¹ ≤ |g|_F ≤ Λ`. For `Λ > 2`
these are admissible cutoffs. Each jumps at both endpoints along the
continuous positive-real section of the idelic norm. -/
theorem Printed.spectralCutoffFamily_continuous_false :
    ¬ Printed.spectralCutoffFamily_continuous := by
  intro h
  let ε : ℝ → ℝ := fun Λ ↦ 1 / (2 * Λ ^ 2)
  let ρ : ℝ → C[ℚ] → ℝ := fun Λ g ↦
    if ((m[ℚ] g).val : ℝ) ∈ Icc Λ⁻¹ Λ then 1 else 0
  have hε : Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) := by
    have hEq : (fun Λ : ℝ ↦ ε Λ * Λ) =ᶠ[atTop] fun Λ ↦ (1 / 2 : ℝ) * Λ⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      dsimp [ε]
      field_simp [hΛ.ne']
    refine Tendsto.congr' hEq.symm ?_
    simpa only [mul_zero] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
      (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hcont : Continuous (ρ 2) :=
    h ℚ ε ρ hε ((eventually_ge_atTop 2).mono fun Λ hΛ ↦ sec4a_sharpCutoff_admissible Λ hΛ)
      2 (sec4a_sharpCutoff_admissible 2 le_rfl)
  let u : Ioi (0 : ℝ) → ℝ≥0ˣ := fun t ↦
    ⟨⟨t.1, t.2.le⟩, ⟨t.1⁻¹, (inv_pos.mpr t.2).le⟩,
      Subtype.ext (mul_inv_cancel₀ t.2.ne'), Subtype.ext (inv_mul_cancel₀ t.2.ne')⟩
  have hu : Continuous u := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val.subtype_mk _,
      (continuous_subtype_val.inv₀ fun t ↦ t.2.ne').subtype_mk _⟩
  let σ : Ioi (0 : ℝ) → C[ℚ] := fun t ↦
    QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) (ratIdeleNormSection (u t))
  have hσ : Continuous σ :=
    QuotientGroup.continuous_mk.comp (ratIdeleNormSection_continuous.comp hu)
  have hσm (t : Ioi (0 : ℝ)) : ((m[ℚ] (σ t)).val : ℝ) = t.1 := by
    change ((ideleClassNorm ℚ (σ t)).val : ℝ) = t.1
    rw [show ideleClassNorm ℚ (σ t) = u t from ratIdeleNormSection_class_rightInverse (u t)]
    rfl
  have hcomp : Continuous (fun t : Ioi (0 : ℝ) ↦ ρ 2 (σ t)) := hcont.comp hσ
  let x₀ : Ioi (0 : ℝ) := ⟨2, by norm_num⟩
  let seq : ℕ → Ioi (0 : ℝ) := fun n ↦ ⟨2 + 1 / ((n : ℝ) + 1), mem_Ioi.mpr (by positivity)⟩
  have hseq : Tendsto seq atTop (𝓝 x₀) := by
    rw [tendsto_subtype_rng]
    have hLim : Tendsto (fun n : ℕ ↦ (2 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 2) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (2 : ℝ))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact hLim
  have h1 : Tendsto (fun n ↦ ρ 2 (σ (seq n))) atTop (𝓝 1) := by
    have hx₀ : ρ 2 (σ x₀) = 1 := by
      dsimp [ρ]
      rw [hσm x₀]
      split_ifs with hmem
      · rfl
      · exact False.elim (hmem ⟨by norm_num, by norm_num⟩)
    simpa only [hx₀, Function.comp_def] using (hcomp.continuousAt.tendsto).comp hseq
  have h0 : (fun n ↦ ρ 2 (σ (seq n))) = fun _ ↦ 0 := by
    funext n
    dsimp [ρ]
    rw [hσm (seq n)]
    split_ifs with hmem
    · exfalso
      have : 2 < (seq n).1 := by
        dsimp [seq]
        linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
      linarith [hmem.2]
    · rfl
  rw [h0] at h1
  exact one_ne_zero (tendsto_nhds_unique (show Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 1) from h1)
    (tendsto_const_nhds (x := (0 : ℝ))))

local notation "W[" F ", " α ", " s "]" =>
  CompactIntervalSobolev μ[F] logNorm[F] (-α) α s
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- Paper: Theorem 10.4.2.8, proof, (10.4.2.24), p. 463. As printed:
ambient biorthogonal lifts of the strip basis can be chosen with a common
upper bound `C + ε`. The indices and the pullback of the coefficient
functionals use `s + b + it` from (10.4.2.21) and `a + b + it` from
(10.4.2.22), respectively, with the full multiplicity displayed there.
The basis vectors belong to the quotient isotype of the fixed character.
Their coefficients pull back to Haar integration, and their ambient lifts
satisfy the upper half of (10.4.2.24) for each permitted ε.
The lemma `exists_biorthogonalBasisLift` assumes a collar for the quotient
vectors (ERRATA F191). -/
def Printed.spectralStripBasisLift_uniformUpperBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (a α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s),
    let hI := (neg_nonpos.mpr hα).trans hα
    let N := globalThetaSobolev F a hI hs
    let Q := spectralSobolevQuotient F a hI hs
    let res : (ideleClassNorm F).ker →ₜ* C[F] :=
      ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
    letI := instClosedSpectralIsotypeThetaSec2 (F := F) a hI hs (χ.comp res)
    let B := spectralSobolevIsotypeQuotient F a hI hs (χ.comp res)
    let incl : B →ₗ[ℂ] Q := Submodule.mapQ _ N (Submodule.subtype _) le_rfl
    let J := {j : ℝ × ℝ × ℕ // j.1 ∈ Icc (-α) α ∧ j.2.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(s + j.1, j.2.1))).untop₀.toNat}
    let η := fun i : J ↦ spectralZeroJet χ (a + i.val.1) i.val.2.1 i.val.2.2
    ∃ (ψ : J → B) (d : J → StrongDual ℂ B) (D : J → StrongDual ℂ Q) (C : ℝ), 0 < C ∧
      IsSpectralMarkushevichBasis ψ d ∧ (∀ i y, d i y = D i (incl y)) ∧
      (∀ (i : J) (v : W[F, α, s]), Integrable (fun g ↦ v g * η i g) μ[F] ∧
        D i (N.mkQ v) = ∫ g, v g * η i g ∂μ[F]) ∧
      ∀ ε : ℝ, 0 < ε → ε < C⁻¹ → ∃ u : J → W[F, α, s],
        ∀ j, N.mkQ (u j) = incl (ψ j) ∧ ‖u j‖ < C + ε

/-- Paper: Theorem 10.4.2.8, proof, (10.4.2.24), p. 463. Use `F = ℚ`,
`χ = 1`, `a = s = α = 2`, and the order-zero jets with `b = −3/2` at
distinct simple critical-line zeros with ordinates `t,u` arbitrarily close
together (Bui–Conrey–Young, Theorem 1.1, and the zeta zero count).
Dominated convergence in the reciprocal Sobolev weight makes
the dual norm of the difference of these jets tend to zero. On the
`t`-indexed lift the difference is one, forcing unbounded lift norms. -/
theorem Printed.spectralStripBasisLift_uniformUpperBound_false :
    ¬ Printed.spectralStripBasisLift_uniformUpperBound := by sorry

end RiemannMasullo
