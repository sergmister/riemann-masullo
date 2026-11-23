module

public import RiemannMasullo.Research.StripNuclearity.RationalConvolutionBlocks

/-!
# Radial convolution for one angular eigencharacter

Let `L f(x) = ψ(x)⁻¹ f(log |x|)`. A compact Bruhat test of angular character `ψ`
has a smooth compact radial profile `p` with `φ(x) = ψ(x)⁻¹ p(log |x|)`. Its
Hardy–Sobolev convolution is `L Aₚ L*`, where `Aₚ` uses ordinary Lebesgue
convolution. Substituting `y = x/g` in the adelic convolution and testing
adjunction against a compact translate divided by the Sobolev weight proves
the identity. The Hilbert adjoint carries the Haar normalization.

This argument connects the ambient action of §9.3, p. 419, to scalar estimates for
the projective-kernel hypothesis in §12.5, p. 520. The single-character identity
works over every number field. The finite decomposition over the rational field
is in `RationalConvolutionBlocks`.
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory NumberField Set Topology
open scoped NNReal ContDiff ENNReal ComplexConjugate

namespace RiemannMasullo

set_option quotPrecheck false

section BruhatProfile

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G]

/-- Smoothness in the Bruhat sense implies ordinary smoothness on each one-parameter subgroup. -/
theorem contDiff_bruhat_one_parameter (v : LCATopologicalLie G)
    (φ : bruhatSmoothSubmodule (G := G)) : ContDiff ℝ (∞) (fun t : ℝ ↦ φ.val (v (Multiplicative.ofAdd t))) := by
  have hd (φ : bruhatSmoothSubmodule (G := G)) (x : ℝ) : HasDerivAt (fun t : ℝ ↦ φ.val (v (Multiplicative.ofAdd t))) (bruhatDirectionalDeriv v φ (v (Multiplicative.ofAdd x))) x := by
    let w := v (Multiplicative.ofAdd x)
    have h := hasDerivAt_bruhatDirectionalDeriv v ((mem_bruhatSmoothSubmodule_iff _).mp φ.property 1) w
    have h' : HasDerivAt (fun t : ℝ ↦ φ.val (w * v (Multiplicative.ofAdd t))) (bruhatDirectionalDeriv v φ w) (x - x) := by
      simpa only [sub_self] using h
    have he : (fun t : ℝ ↦ φ.val (w * v (Multiplicative.ofAdd (t-x)))) =
        fun t : ℝ ↦ φ.val (v (Multiplicative.ofAdd t)) := by
      funext t
      change φ.val (v (Multiplicative.ofAdd x) * v (Multiplicative.ofAdd (t-x))) = _
      rw [← map_mul, ← ofAdd_add, show x + (t - x) = t by abel]
    exact he ▸ h'.comp_sub_const x x
  apply contDiff_infty.mpr
  intro n
  induction n generalizing φ with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x ↦ (hd φ x).continuousAt)
  | succ n ih =>
    let D : bruhatSmoothSubmodule (G := G) := ⟨_, bruhatDirectionalDeriv_mem_smooth v φ⟩
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (hd φ x).differentiableAt, by simp, ?_⟩
    exact (funext fun x ↦ (hd φ x).deriv) ▸ ih D

/-- A compact angular eigenfunction is an inverse character times a smooth compactly
supported function of the real logarithm of the modulation. -/
theorem bruhatCompactSupport_exists_radial_eigenprofile (m : G →ₜ* ℝ≥0ˣ)
    (v : LCATopologicalLie G)
    (hv : ∀ t : ℝ, Real.log ((m (v (Multiplicative.ofAdd t))).val : ℝ) = t)
    (ψ : PontryaginDual G) (φ : BruhatCompactSupport G)
    (hφ : ∀ (k : m.toMonoidHom.ker) (x : G), φ.val (k.val⁻¹*x) = (ψ k.val : ℂ)*φ.val x) :
    ∃ p : ℝ → ℂ, HasCompactSupport p ∧ ContDiff ℝ (∞) p ∧
      ∀ x, φ.val x = (ψ x : ℂ)⁻¹ * p (Real.log ((m x).val : ℝ)) := by
  let l (x : G) := Real.log ((m x).val : ℝ)
  have hpos (u : ℝ≥0ˣ) : 0 < (u.val : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr u.ne_zero)
  have hl : Continuous l := (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log (fun x ↦ (hpos _).ne')
  let p (t : ℝ) := (ψ (v (Multiplicative.ofAdd t)) : ℂ) * φ.val (v (Multiplicative.ofAdd t))
  refine ⟨p, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro (φ.property.2.isCompact.image hl) fun t ht ↦ ?_
    have hn : v (Multiplicative.ofAdd t) ∉ tsupport φ.val := fun hh ↦ ht ⟨_, hh, hv t⟩
    exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hn)
  · exact (contDiff_bruhat_one_parameter v ⟨_, pontryaginDual_mem_bruhatSmooth ψ⟩).mul
      (contDiff_bruhat_one_parameter v ⟨φ.val, φ.property.1⟩)
  · intro x
    let y := v (Multiplicative.ofAdd (l x))
    have hy : m y = m x := by
      apply Units.ext
      apply NNReal.eq
      exact Real.log_injOn_pos (hpos _) (hpos _) (hv (l x))
    let k : m.toMonoidHom.ker := ⟨y / x, by change m (y / x) = 1; rw [map_div, hy, div_self']⟩
    have hk : k.val⁻¹ * y = x := by change (y / x)⁻¹ * y = x; simp [div_eq_mul_inv, mul_assoc]
    have he := hφ k y
    rw [hk] at he
    change φ.val x = (ψ x : ℂ)⁻¹ * ((ψ y : ℂ) * φ.val y)
    rw [he]
    change (ψ (y / x) : ℂ) * φ.val y = _
    rw [map_div, Circle.coe_div]
    ring

end BruhatProfile

private theorem weighted_complex_inner {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {w : X → ℝ} (hw : AEMeasurable w μ) (hp : ∀ x, 0 < w x)
    (u v : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))) :
    inner ℂ u v = ∫ x, (w x : ℂ) * conj (u x) * v x ∂μ := by
  rw [L2.inner_def, integral_withDensity_eq_integral_toReal_smul₀ hw.ennreal_ofReal
    (.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [ENNReal.toReal_ofReal (hp x).le, RCLike.inner_apply, Complex.real_smul]
  ring

/-- Pairing the adjoint of the inverse-character lift against a compact continuous test
recovers its ordinary unweighted angular pushforward, with its Haar normalization. -/
theorem integral_character_radial_adjoint {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (l : X → ℝ) (hl : QuasiMeasurePreserving l μ volume)
    (ψ : X → Circle) {w : ℝ → ℝ} (hw : Continuous w) (hpos : ∀ t, 0 < w t) :
    let η := volume.withDensity fun t ↦ ENNReal.ofReal (w t)
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (w (l x))
    ∀ (L : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 ν)
      (_ : ∀ f, (L f : X → ℂ) =ᵐ[μ] fun x ↦ (ψ x : ℂ)⁻¹ * f (l x))
      (p : ℝ → ℂ) (_ : Continuous p) (_ : HasCompactSupport p) (u : Lp ℂ 2 ν),
      (∫ x, p (l x) * (ψ x : ℂ) * u x ∂μ) = ∫ t : ℝ, p t * L.adjoint u t := by
  intro η ν L hL p hp hs u
  let : IsLocallyFiniteMeasure η := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hbase : volume ≪ η := withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let q (t : ℝ) := (w t : ℂ)⁻¹ * conj (p t)
  have hq : Continuous q := ((Complex.continuous_ofReal.comp hw).inv₀ (fun t ↦
    Complex.ofReal_ne_zero.mpr (hpos t).ne')).mul (Complex.continuous_conj.comp hp)
  have hqc : HasCompactSupport q := (hs.comp_left (show conj (0 : ℂ) = 0 from map_zero _)).mul_left
  have hmem := hq.memLp_of_hasCompactSupport (p := (2 : ENNReal)) (μ := η) hqc
  let v : Lp ℂ 2 η := hmem.toLp q
  have hv : (v : ℝ → ℂ) =ᵐ[volume] q := hbase.ae_eq hmem.coeFn_toLp
  have hqcancel (t : ℝ) : (w t : ℂ) * conj (q t) = p t := by
    simp only [q, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_conj]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hpos t).ne'), one_mul]
  have hψ (x : X) : conj ((ψ x : ℂ)⁻¹) = (ψ x : ℂ) := by
    rw [← Circle.coe_inv, Circle.coe_inv_eq_conj, Complex.conj_conj]
  calc
    _ = inner ℂ (L v) u := by
      rw [weighted_complex_inner μ (hw.measurable.comp_aemeasurable hl.aemeasurable) (fun x ↦ hpos (l x))]
      apply integral_congr_ae
      filter_upwards [hL v, hl.ae_eq_comp hv] with x h₁ h₂
      change v (l x) = q (l x) at h₂
      change p (l x) * (ψ x : ℂ) * u x = (w (l x) : ℂ) * conj ((L v) x) * u x
      rw [h₁, h₂, map_mul, hψ, ← hqcancel (l x)]
      ring
    _ = inner ℂ v (L.adjoint u) := (L.adjoint_inner_right v u).symm
    _ = _ := by
      rw [weighted_complex_inner volume hw.measurable.aemeasurable hpos]
      apply integral_congr_ae
      filter_upwards [hv] with t ht
      rw [ht, hqcancel]

private theorem eigenWeight_continuous (a b s : ℝ) : Continuous (intervalSobolevDensity a b s) := by
  have h₁ : Continuous (fun x : ℝ ↦ Real.exp (2 * a * x)) := by fun_prop
  have h₂ : Continuous (fun x : ℝ ↦ Real.exp (2 * b * x)) := by fun_prop
  refine (h₁.max h₂).mul
    (Continuous.rpow_const (show Continuous (fun x : ℝ ↦ 1 + x^2) by fun_prop) fun x ↦ Or.inl ?_)
  positivity

private theorem eigenWeight_pos (a b s t : ℝ) : 0 < intervalSobolevDensity a b s t :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

section RadialConvolution

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

private theorem radial_convolution_formula
    (μ : Measure G) [μ.IsHaarMeasure] (l : G → ℝ) (hl : ∀ x y, l (x / y) = l x - l y)
    (ψ : PontryaginDual G) (φ : G → ℂ) (p : ℝ → ℂ)
    (hφ : ∀ x, φ x = (ψ x : ℂ)⁻¹ * p (l x)) (u : G → ℂ) (x : G) :
    lcaConvolution μ φ u x = (ψ x : ℂ)⁻¹ * ∫ y, p (l x - l y) * (ψ y : ℂ) * u y ∂μ := by
  unfold lcaConvolution
  rw [← integral_const_mul, ← integral_div_left_eq_self (fun y ↦ φ y * u (y⁻¹ * x)) μ x]
  apply integral_congr_ae (.of_forall fun y ↦ ?_)
  rw [hφ, hl, map_div, Circle.coe_div]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  ring

/-- A compact test of a single angular character acts by ordinary radial convolution
between the lift and its Hilbert adjoint. The raw section profile needs no Haar factor. -/
theorem hardySobolevTestAction_eq_radial_adjoint
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
    (hm : QuasiMeasurePreserving (fun x ↦ Real.log ((m x).val : ℝ)) μ volume)
    (ψ : PontryaginDual G) (φ : BruhatCompactSupport G) (p : ℝ → ℂ) (hpc : Continuous p)
    (hps : HasCompactSupport p) (hφ : ∀ x, φ.val x = (ψ x : ℂ)⁻¹ * p (Real.log ((m x).val : ℝ)))
    {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) :
    let l := fun x : G ↦ Real.log ((m x).val : ℝ)
    let E := CompactIntervalSobolev volume id a b s
    let W := CompactIntervalSobolev μ l a b s
    ∀ (L : E →L[ℂ] W) (_ : ∀ f, (L f : G → ℂ) =ᵐ[μ] fun x ↦ (ψ x : ℂ)⁻¹ * f (l x))
      (B : E →L[ℂ] E) (_ : ∀ f, ∀ᵐ x ∂volume, B f x = ∫ t : ℝ, p t * f (x-t)),
      (hardySobolevTestAction μ m a b s hab hs φ : W →L[ℂ] W) = (L.comp B).comp L.adjoint := by
  intro l E W L hL B hB
  let w := intervalSobolevDensity a b s
  have hw : Continuous w := eigenWeight_continuous a b s
  have hp := eigenWeight_pos a b s
  have hpos (u : ℝ≥0ˣ) : 0 < (u.val : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr u.ne_zero)
  have hl (x y : G) : l (x/y) = l x - l y := by
    change Real.log ((m (x/y)).val : ℝ) = _
    rw [map_div, Units.val_div_eq_div_val, NNReal.coe_div, Real.log_div (hpos _).ne' (hpos _).ne']
  ext u : 1
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ _).ae_eq
  change (hardySobolevTestAction μ m a b s hab hs φ u : G → ℂ) =ᵐ[μ] L (B (L.adjoint u))
  filter_upwards [hardySobolevTestAction_apply μ m a b s hab hs φ u,
    hL (B (L.adjoint u)), hm.ae_eq_comp (hB (L.adjoint u))] with x hA hlift hscalar
  change B (L.adjoint u) (l x) = ∫ t : ℝ, p t * L.adjoint u (l x - t) at hscalar
  rw [hA, hlift, hscalar, radial_convolution_formula μ l hl ψ φ.val p hφ]
  apply congrArg ((ψ x : ℂ)⁻¹ * ·)
  let q (t : ℝ) := p (l x - t)
  have hq : Continuous q := hpc.comp (continuous_const.sub continuous_id)
  have hqc : HasCompactSupport q := hps.comp_homeomorph (Homeomorph.subLeft (l x))
  calc
    _ = ∫ t : ℝ, p (l x-t) * L.adjoint u t := integral_character_radial_adjoint μ l hm ψ hw hp L hL q hq hqc u
    _ = _ := by
      rw [← integral_sub_left_eq_self (fun t : ℝ ↦ p t * L.adjoint u (l x-t)) volume (l x)]
      simp

end RadialConvolution

private def eigenLogSectionExp : Multiplicative ℝ ≃ₜ* ℝ≥0ˣ :=
  { Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm with
    map_mul' := fun x y ↦ by
      apply Units.ext
      apply NNReal.eq
      exact Real.exp_add x.toAdd y.toAdd }

private theorem eigenLogSectionExp_log (u : ℝ≥0ˣ) :
    (eigenLogSectionExp.symm u).toAdd = Real.log (u.val : ℝ) := by
  obtain ⟨x,rfl⟩ := eigenLogSectionExp.surjective u
  rw [ContinuousMulEquiv.symm_apply_apply]
  exact (Real.log_exp _).symm

private theorem exists_log_haar_scalar {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
    (hp : IsProperMap m) (hs : Surjective m) :
    let l := fun x : G ↦ Real.log ((m x).val : ℝ)
    ∃ c : ℝ≥0, μ.map l = (c : ℝ≥0∞) • volume := by
  intro l
  let e := eigenLogSectionExp.symm
  let f : G →ₜ* Multiplicative ℝ := (⟨e,e.continuous⟩ : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp m
  let η : Measure (Multiplicative ℝ) := volume (α := ℝ)
  let : IsFiniteMeasureOnCompacts η := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  let : Measure.IsOpenPosMeasure η := inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
  let : η.IsMulLeftInvariant :=
    ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
  let : η.IsHaarMeasure := by constructor
  have hproper : Tendsto f (cocompact G) (cocompact (Multiplicative ℝ)) :=
    (isProperMap_iff_tendsto_cocompact.mp (e.toHomeomorph.isProperMap.comp hp)).2
  let : (μ.map f).IsHaarMeasure := Measure.isHaarMeasure_map μ f.toMonoidHom f.continuous
    (e.surjective.comp hs) hproper
  have heq : (fun x ↦ (f x).toAdd) = l := funext fun x ↦ eigenLogSectionExp_log (m x)
  rw [← heq]
  exact ⟨Measure.haarScalarFactor (μ.map f) η, Measure.isMulLeftInvariant_eq_smul_of_regular (μ.map f) η⟩

section Lift

private theorem complexLp_change_scalar (η : Measure ℝ) (c : ℝ≥0) :
    ∃ J : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 ((c : ℝ≥0∞) • η), ∀ f, (J f : ℝ → ℂ) =ᵐ[(c : ℝ≥0∞) • η] f := by
  let ν := (c : ℝ≥0∞) • η
  let R : Lp ℂ 2 η →L[ℝ] Lp ℂ 2 ν := Lp.LpToLpOfMeasureLeSMul (ENNReal.coe_ne_top (r := c)) le_rfl
  have hR (f : Lp ℂ 2 η) : (R f : ℝ → ℂ) =ᵐ[ν] f := Lp.coeFn_LpToLpOfMeasureLeSMul _ le_rfl f
  let J : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 ν := {
    toFun := R
    map_add' := R.map_add
    map_smul' := fun z f ↦ by
      apply Lp.ext
      have hdom : ν ≪ η := Measure.smul_absolutelyContinuous
      filter_upwards [hR (z • f), hdom.ae_eq (Lp.coeFn_smul z f), Lp.coeFn_smul z (R f), hR f] with x h₁ h₂ h₃ h₄
      exact h₁.trans (h₂.trans (h₃.symm ▸ congrArg (fun v : ℂ ↦ z • v) h₄.symm))
    cont := R.continuous }
  exact ⟨J, hR⟩

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
  {w : ℝ → ℝ} (hw : Measurable w) (hp : ∀ t, 0 < w t)

include hl hw hp in
/-- A weighted logarithmic pullback followed by a unitary multiplier, for an
arbitrary finite Haar normalization on the logarithmic line. -/
private theorem exists_weighted_character_lift (c : ℝ≥0) (hμ : μ.map l = (c : ℝ≥0∞) • volume)
    (ψ : X → ℂ) (hψ : Measurable ψ) (hψn : ∀ x, ‖ψ x‖ = 1) :
    let η := volume.withDensity fun t ↦ ENNReal.ofReal (w t)
    let ν := μ.withDensity fun x ↦ ENNReal.ofReal (w (l x))
    ∃ L : Lp ℂ 2 η →L[ℂ] Lp ℂ 2 ν, ∀ f, (L f : X → ℂ) =ᵐ[μ] fun x ↦ ψ x * f (l x) := by
  intro η ν
  have ht : MeasurePreserving l μ (μ.map l) := ⟨hl,rfl⟩
  have hh : MeasurePreserving l ν ((μ.map l).withDensity fun t ↦ ENNReal.ofReal (w t)) := by
    refine ⟨hl, ?_⟩
    ext S hS
    rw [Measure.map_apply hl hS, withDensity_apply _ (hl hS), withDensity_apply _ hS]
    exact ht.setLIntegral_comp_preimage hS hw.ennreal_ofReal
  rw [hμ, withDensity_smul_measure] at hh
  obtain ⟨J,hJ⟩ := complexLp_change_scalar η c
  let T := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ l hh
  have hm : MemLp ψ ⊤ ν := memLp_top_of_bound hψ.aestronglyMeasurable 1 (.of_forall fun x ↦ (hψn x).le)
  let D := ContinuousLinearMap.mul ℂ ℂ
  let U := D.holderL ν ⊤ 2 2 (hm.toLp ψ)
  have hbase : μ ≪ ν := withDensity_absolutelyContinuous' (hw.comp hl).ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp _)).ne')
  refine ⟨(U.comp T.toContinuousLinearMap).comp J, fun f ↦ hbase.ae_eq ?_⟩
  filter_upwards [D.coeFn_holder (r := 2) (hm.toLp ψ) (T (J f)), hm.coeFn_toLp,
    Lp.coeFn_compMeasurePreserving (J f) hh, hh.quasiMeasurePreserving.ae_eq_comp (hJ f)] with x h₁ h₂ h₃ h₄
  change (U (T (J f))) x = ψ x * f (l x)
  change (J f) (l x) = f (l x) at h₄
  change (T (J f)) x = (J f) (l x) at h₃
  change (U (T (J f))) x = (hm.toLp ψ) x * (T (J f)) x at h₁
  rw [h₁, h₂, h₃, h₄]

end Lift
section ModulatedEigenkernel

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
  (hproper : IsProperMap m) (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m)
local notation "ℓ" => (fun x : G ↦ Real.log ((m x).val : ℝ))

include hproper hσ in
/-- The lift and radial factorization for a proper split positive-real modulation. -/
private theorem exists_modulated_eigenkernel_factorization (ψ : PontryaginDual G)
    (φ : BruhatCompactSupport G)
    (hφ : ∀ (k : m.toMonoidHom.ker) x, φ.val (k.val⁻¹ * x) = (ψ k.val : ℂ) * φ.val x)
    {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) :
    let E := CompactIntervalSobolev volume id a b s
    let W := CompactIntervalSobolev μ ℓ a b s
    ∃ (p : ℝ → ℂ) (L : E →L[ℂ] W),
      HasCompactSupport p ∧ ContDiff ℝ (∞) p ∧
      (∀ x, φ.val x = (ψ x : ℂ)⁻¹ * p (ℓ x)) ∧
      (∀ f, (L f : G → ℂ) =ᵐ[μ] fun x ↦ (ψ x : ℂ)⁻¹ * f (ℓ x)) ∧
      ∀ (B : E →L[ℂ] E), (∀ f, ∀ᵐ x ∂volume, B f x = ∫ t : ℝ, p t * f (x - t)) →
        (hardySobolevTestAction μ m a b s hab hs φ : W →L[ℂ] W) = (L.comp B).comp L.adjoint := by
  intro E W
  let v : LCATopologicalLie G := σ.comp ⟨eigenLogSectionExp, eigenLogSectionExp.continuous⟩
  have hv (t : ℝ) : ℓ (v (Multiplicative.ofAdd t)) = t := by
    change Real.log (((m (σ (eigenLogSectionExp (Multiplicative.ofAdd t)))).val) : ℝ) = t
    rw [hσ]
    exact Real.log_exp t
  obtain ⟨p,hpc,hpd,hval⟩ := bruhatCompactSupport_exists_radial_eigenprofile m v hv ψ φ hφ
  obtain ⟨c,hc⟩ := exists_log_haar_scalar μ m hproper hσ.surjective
  have hpos (u : ℝ≥0ˣ) : 0 < (u.val : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr u.ne_zero)
  have hl : Measurable ℓ := ((NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)).log
    (fun x ↦ (hpos _).ne')).measurable
  have hq : QuasiMeasurePreserving ℓ μ volume := ⟨hl.aemeasurable, hc ▸ Measure.smul_absolutelyContinuous⟩
  let w := intervalSobolevDensity a b s
  have hw : Continuous w := eigenWeight_continuous a b s
  have hp := eigenWeight_pos a b s
  let z (x : G) := (ψ x : ℂ)⁻¹
  have hz : Continuous z := (continuous_subtype_val.comp ψ.continuous).inv₀ (fun x ↦ Circle.coe_ne_zero _)
  obtain ⟨L,hL⟩ := exists_weighted_character_lift μ ℓ hl hw.measurable hp c hc z hz.measurable (fun x ↦ by simp [z])
  exact ⟨p,L,hpc,hpd,hval,hL,fun B hB ↦ hardySobolevTestAction_eq_radial_adjoint μ m hq ψ φ p
    hpd.continuous hpc hval hab hs L hL B hB⟩

end ModulatedEigenkernel

section IdeleClasses

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))

/-- A compact Bruhat eigen-test on the idele classes factors its actual Hardy–Sobolev
convolution as a scalar convolution between the inverse-character lift and its Hilbert adjoint.
The scalar kernel is smooth, compactly supported, and measured with ordinary Lebesgue measure. -/
theorem exists_ideleClass_eigenkernel_factorization (ψ : PontryaginDual C𝔽)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) x, φ.val (k.val⁻¹ * x) = (ψ k.val : ℂ) * φ.val x)
    {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s) :
    let E := CompactIntervalSobolev volume id a b s
    let W := CompactIntervalSobolev μ𝔽 logNorm a b s
    ∃ (p : ℝ → ℂ) (L : E →L[ℂ] W),
      HasCompactSupport p ∧ ContDiff ℝ (∞) p ∧
      (∀ x, φ.val x = (ψ x : ℂ)⁻¹ * p (logNorm x)) ∧
      (∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x)) ∧
      ∀ (B : E →L[ℂ] E), (∀ f, ∀ᵐ x ∂volume, B f x = ∫ t : ℝ, p t * f (x - t)) →
        (hardySobolevTestAction μ𝔽 m𝔽 a b s hab hs φ : W →L[ℂ] W) = (L.comp B).comp L.adjoint := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  exact exists_modulated_eigenkernel_factorization μ𝔽 m𝔽 (isProperMap_ideleClassNorm F) σ
    (canonicalIdeleNormSection_rightInverse F) ψ φ hφ hab hs

end IdeleClasses

end RiemannMasullo
