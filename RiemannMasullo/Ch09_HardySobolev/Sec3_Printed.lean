module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian

/-! # §9.3: statements that are false as printed -/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace RiemannMasullo

set_option quotPrecheck false

local notation "logMod(" m ")" => (fun x ↦ Real.log ((m x).val : ℝ))

/-- Paper: Lemma 9.3.1.5, (9.3.1.6), p. 421. As printed: For each continuous
operator seminorm and each compact base interval, the translation bound is a
constant times the maximum endpoint twist times the absolute log-module raised
to s/2. This is the bound in (9.3.1.6). The repaired operator-norm bound is
`norm_hardySobolevTranslation_le`. See ERRATA F175. -/
def Printed.hardySobolevTranslation_seminorm_le : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s),
    let W := CompactIntervalSobolev μ logMod(m) a b s
    ∀ p : Seminorm ℂ (W →L[ℂ] W), Continuous p →
      ∃ C : ℝ, 0 < C ∧ ∀ g : G,
        p (hardySobolevTranslation μ m a b s hab hs g) ≤
          C * max (((m g).val : ℝ) ^ a) (((m g).val : ℝ) ^ b) * |logMod(m) g| ^ (s / 2)

/-- The multiplicative Haar measure `dt/t` gives a set of logarithmic coordinates
its Lebesgue measure. -/
private theorem positiveRealHaar_logPreimage_hardySobolevTranslation (K : Set ℝ)
    (hK : MeasurableSet K) :
    positiveRealHaar {t : ℝ≥0ˣ | Real.log (t.val : ℝ) ∈ K} = volume K := by
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hset : MeasurableSet {t : ℝ≥0ˣ | Real.log (t.val : ℝ) ∈ K} :=
    hK.preimage (Real.measurable_log.comp
      (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap))
  change (volume.map e) _ = _
  rw [Measure.map_apply he hset]
  congr 1
  ext x
  change Real.log ((Real.exp x).toNNReal : ℝ) ∈ K ↔ x ∈ K
  rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]

/-- The identity is a surjective modulation of the positive reals. -/
private theorem isModulation_id_hardySobolevTranslation :
    IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ) :=
  ⟨isProperMap_id, ⟨Units.mk0 2 (by norm_num), by
    intro h
    have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    norm_num at this⟩⟩

/-- The degree-two compact-interval space over the base `{0}` on the positive reals
is nonzero: the indicator of `|log t| ≤ 1` has positive finite weighted mass. -/
private theorem nontrivial_compactIntervalSobolev_hardySobolevTranslation :
    Nontrivial (CompactIntervalSobolev positiveRealHaar
      (fun x : ℝ≥0ˣ ↦ Real.log (x.val : ℝ)) 0 0 2) := by
  let S : Set ℝ≥0ˣ := {t | Real.log (t.val : ℝ) ∈ Icc (-1 : ℝ) 1}
  have hS : MeasurableSet S := measurableSet_Icc.preimage (Real.measurable_log.comp
    (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap))
  have hμS : positiveRealHaar S = 2 := by
    rw [positiveRealHaar_logPreimage_hardySobolevTranslation _ measurableSet_Icc,
      Real.volume_Icc]
    norm_num
  have hd (x : ℝ) : intervalSobolevDensity 0 0 2 x = 1 + x ^ 2 := by
    simp [intervalSobolevDensity]
  set ν := positiveRealHaar.withDensity fun x : ℝ≥0ˣ ↦ ENNReal.ofReal
    (if (false : Bool) then (intervalSobolevDensity 0 0 2 (Real.log (x.val : ℝ)))⁻¹
     else intervalSobolevDensity 0 0 2 (Real.log (x.val : ℝ))) with hν
  have hνS : ν S = ∫⁻ x in S, ENNReal.ofReal (1 + Real.log (x.val : ℝ) ^ 2) ∂positiveRealHaar := by
    rw [hν, withDensity_apply _ hS]
    simp only [Bool.false_eq_true, ite_false, hd]
  have hlow : 2 ≤ ν S := by
    rw [hνS, ← hμS, ← setLIntegral_one]
    refine setLIntegral_mono (ENNReal.measurable_ofReal.comp (measurable_const.add
      ((Real.measurable_log.comp (NNReal.continuous_coe.measurable.comp
        MeasurableSpace.le_map_comap)).pow_const 2))) fun x _ ↦ ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (Real.log (x.val : ℝ))])
  have hup : ν S ≤ 4 := by
    calc ν S ≤ ∫⁻ _ in S, ENNReal.ofReal 2 ∂positiveRealHaar := by
          rw [hνS]
          refine setLIntegral_mono measurable_const fun x hx ↦ ENNReal.ofReal_le_ofReal ?_
          obtain ⟨h1, h2⟩ := hx
          nlinarith
      _ = 4 := by
          rw [setLIntegral_const, hμS, ENNReal.ofReal_ofNat]
          norm_num
  have hfin : ν S ≠ ∞ := (hup.trans_lt (by norm_num)).ne
  have hpos : ν S ≠ 0 := (lt_of_lt_of_le (by norm_num) hlow).ne'
  refine ⟨indicatorConstLp 2 hS hfin (1 : ℂ), 0, fun h ↦ ?_⟩
  have hn := congrArg norm h
  rw [norm_zero, norm_indicatorConstLp' (by norm_num) hpos, norm_one, one_mul] at hn
  have : 0 < ν.real S := ENNReal.toReal_pos hpos hfin
  exact (Real.rpow_pos_of_pos this _).ne' hn

/-- On a nonzero normed space the identity has positive norm. -/
private theorem not_norm_id_nonpos_hardySobolevTranslation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [Nontrivial E] : ¬ ‖ContinuousLinearMap.id ℂ E‖ ≤ 0 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have h1 := (ContinuousLinearMap.id ℂ E).le_opNorm v
  rw [ContinuousLinearMap.id_apply] at h1
  exact hv (norm_le_zero_iff.mp (h1.trans (mul_nonpos_of_nonpos_of_nonneg h (norm_nonneg v))))

/-- Paper: Lemma 9.3.1.5, (9.3.1.6), p. 421. On the positive reals with
identity module and Haar measure dt/t, take a = b = 0, s = 2 and the operator
norm seminorm. The space is nonzero, since a nonzero smooth compact log-profile
lies in it. At g = 1 the translate is the identity, so the bound reads 1 ≤ 0. -/
theorem Printed.hardySobolevTranslation_seminorm_le_false :
    ¬ Printed.hardySobolevTranslation_seminorm_le := by
  intro h
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have hW := nontrivial_compactIntervalSobolev_hardySobolevTranslation
  obtain ⟨C, -, hC⟩ := h ℝ≥0ˣ positiveRealHaar (ContinuousMonoidHom.id ℝ≥0ˣ)
    isModulation_id_hardySobolevTranslation surjective_id 0 0 2 le_rfl (by norm_num)
    (normSeminorm ℂ _) continuous_norm
  have h1 := hC 1
  rw [map_one, coe_normSeminorm, ContinuousLinearMap.one_def] at h1
  refine @not_norm_id_nonpos_hardySobolevTranslation _ _ _ hW (h1.trans_eq ?_)
  simp

/-- Paper: Definition 9.3.1.1, p. 419. As printed: The left-translation action
used in the definition acts on the Sobolev space for every nonempty closed
interval. This is its assertion that a finite-norm exponential-decay test
still has finite norm after translation, using the supremum in (9.2.2.3).
`hardySobolevTranslation` provides the action on compact bases. See ERRATA F175. -/
def Printed.hardySobolevTranslation_preserves_finiteNorm : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (I : Set ℝ), IsClosed I → OrdConnected I → I.Nonempty →
    ∀ s : ℝ, 0 ≤ s → ∀ (f : ModulatedExponentialDecay m univ) (g : G),
      intervalSobolevENorm μ logMod(m) I s f.val < ∞ →
      intervalSobolevENorm μ logMod(m) I s (fun x ↦ f.val (g⁻¹ * x)) < ∞

/-- A smooth function of the logarithmic module is Bruhat smooth. On each
structural quotient, compose the descended positive quasi-character with log. -/
private theorem isBruhatSmooth_logProfile_preservesFiniteNorm {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* ℝ≥0ˣ) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsBruhatSmooth (fun x ↦ (f (Real.log ((m x).val : ℝ)) : ℂ)) := by
  let χ : QuasiCharacter G :=
    { toFun := fun x ↦ ((m x).val : ℝ)
      map_one' := by simp
      map_mul' := fun x y ↦ by simp
      continuous_toFun := Complex.continuous_ofReal.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)) }
  intro p
  obtain ⟨k, hk, hinv, hdesc⟩ :=
    (mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth χ) p
  refine ⟨k, hk, fun h x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hinv h x), ?_⟩
  intro a ha
  obtain ⟨q, hq, hdiff⟩ := hdesc a ha
  have hpos (y : a.quotient) : 0 < (q y).re := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hq]
    exact NNReal.coe_pos.mpr (Units.zero_lt _)
  refine ⟨fun y ↦ (f (Real.log (q y).re) : ℂ),
    fun x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hq x), ?_⟩
  intro e z b
  exact Complex.ofRealCLM.contDiff.comp ((hf.of_le (by simp)).comp
    ((Complex.reCLM.contDiff.comp (hdiff e z b)).log fun x ↦ (hpos _).ne'))

/-- A set of logarithmic coordinates of a compact set is compact in the positive reals. -/
private theorem isCompact_logPreimage_preservesFiniteNorm {K : Set ℝ} (hK : IsCompact K) :
    IsCompact {t : ℝ≥0ˣ | Real.log (t.val : ℝ) ∈ K} := by
  let e : ℝ → ℝ≥0ˣ := fun x ↦ Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'
  have he : Continuous e := Units.continuous_iff.mpr
    ⟨continuous_real_toNNReal.comp Real.continuous_exp, by
      change Continuous fun x ↦ ((Real.exp x).toNNReal)⁻¹
      exact (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun x ↦ (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'⟩
  convert hK.image he using 1
  ext t
  constructor
  · intro ht
    refine ⟨_, ht, Units.ext (NNReal.eq ?_)⟩
    change ((Real.exp (Real.log (t.val : ℝ))).toNNReal : ℝ) = _
    rw [Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t)),
      Real.coe_toNNReal _ (NNReal.coe_nonneg _)]
  · rintro ⟨x, hx, rfl⟩
    change Real.log ((Real.exp x).toNNReal : ℝ) ∈ K
    rwa [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]

/-- Paper: Definition 9.3.1.1, p. 419. On the positive reals with identity
module and Haar measure dt/t, take I = [0, ∞), s = 0 and a nonzero smooth
bump in log coordinates supported in (−2, −1). There the endpoint twists
are uniformly bounded as the nonnegative exponent grows. The left translate
by exp 3 is supported in (1, 2) in log coordinates, where the norms for
[0, b] grow without bound as b tends to infinity. -/
theorem Printed.hardySobolevTranslation_preserves_finiteNorm_false :
    ¬ Printed.hardySobolevTranslation_preserves_finiteNorm := by
  intro h
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  have hm : IsModulation m := isModulation_id_hardySobolevTranslation
  let L : ℝ≥0ˣ → ℝ := fun x ↦ Real.log (x.val : ℝ)
  have hL : Measurable L :=
    Real.measurable_log.comp (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  have hLS (K : Set ℝ) (hK : MeasurableSet K) : MeasurableSet {t : ℝ≥0ˣ | L t ∈ K} :=
    hK.preimage hL
  -- The bump in logarithmic coordinates, supported in (−2, −1) and equal to one near −3/2.
  let B : ContDiffBump (-3 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let F : ℝ≥0ˣ → ℂ := fun x ↦ (B (L x) : ℂ)
  have hFm : Measurable F := Complex.measurable_ofReal.comp (B.continuous.measurable.comp hL)
  have hBsupp (y : ℝ) (hy : B y ≠ 0) : y ∈ Icc (-2 : ℝ) (-1) := by
    have : y ∈ Function.support B := hy
    rw [B.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt,
      show B.rOut = 1 / 2 from rfl] at this
    constructor <;> linarith [this.1, this.2]
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.intro (isCompact_logPreimage_preservesFiniteNorm
      (isCompact_Icc (a := (-2 : ℝ)) (b := -1)))
      fun x hx ↦ ?_
    by_contra hne
    exact hx (hBsupp _ fun h0 ↦ hne (show ((B (L x) : ℝ) : ℂ) = 0 by
      rw [h0, Complex.ofReal_zero]))
  have hFmem : F ∈ modulatedExponentialDecaySubmodule m univ :=
    bruhatCompactSupport_le_modulatedExponentialDecay m univ hm surjective_id
      ⟨(mem_bruhatSmoothSubmodule_iff _).mpr
        (isBruhatSmooth_logProfile_preservesFiniteNorm m B.contDiff), hFc⟩
  let f : ModulatedExponentialDecay m univ := ⟨F, hFmem⟩
  let g : ℝ≥0ˣ := Units.mk0 (Real.exp 3).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos 3)).ne'
  have hLg (x : ℝ≥0ˣ) : L (g⁻¹ * x) = L x - 3 := by
    have hx : (0 : ℝ) < (x.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt x)
    change Real.log ((((g⁻¹ * x : ℝ≥0ˣ) : ℝ≥0)) : ℝ) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv,
      Real.log_mul (inv_pos.mpr (NNReal.coe_pos.mpr (Units.zero_lt g))).ne' hx.ne',
      Real.log_inv]
    change -Real.log ((Real.exp 3).toNNReal : ℝ) + _ = _
    rw [Real.coe_toNNReal _ (Real.exp_pos 3).le, Real.log_exp]
    ring
  have hd (a b x : ℝ) : intervalSobolevDensity a b 0 x =
      max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
    simp [intervalSobolevDensity]
  -- The norm of the bump is finite: every density is at most one on its support.
  let S : Set ℝ≥0ˣ := {t | L t ∈ Icc (-2 : ℝ) (-1)}
  have hμS : positiveRealHaar S = 1 := by
    rw [positiveRealHaar_logPreimage_hardySobolevTranslation _ measurableSet_Icc,
      Real.volume_Icc]
    norm_num
  have hfin : intervalSobolevENorm positiveRealHaar L (Ici 0) 0 f.val < ∞ := by
    refine lt_of_le_of_lt (iSup₂_le fun a b ↦ ?_) ENNReal.one_lt_top
    have ha : (0 : ℝ) ≤ a := a.2
    have hb : (0 : ℝ) ≤ b := b.2
    set ν := positiveRealHaar.withDensity fun x ↦
      ENNReal.ofReal (intervalSobolevDensity a b 0 (L x))
    calc eLpNorm f.val 2 ν ≤ eLpNorm (S.indicator fun _ ↦ (1 : ℂ)) 2 ν := by
          refine eLpNorm_mono hFm.aestronglyMeasurable fun x ↦ ?_
          by_cases hx : x ∈ S
          · rw [indicator_of_mem hx, norm_one]
            change ‖((B (L x) : ℝ) : ℂ)‖ ≤ 1
            rw [Complex.norm_real, Real.norm_of_nonneg B.nonneg]
            exact B.le_one
          · rw [indicator_of_notMem hx, norm_zero]
            have : B (L x) = 0 := by
              by_contra hne
              exact hx (hBsupp _ hne)
            change ‖((B (L x) : ℝ) : ℂ)‖ ≤ 0
            rw [this]
            simp
      _ = ν S ^ (1 / (2 : ℝ≥0∞).toReal) := by
          rw [eLpNorm_indicator_const (hLS _ measurableSet_Icc).nullMeasurableSet
            (by norm_num) (by norm_num), eNorm_one, one_mul]
      _ ≤ 1 := by
          refine ENNReal.rpow_le_one ?_ (by norm_num)
          rw [withDensity_apply _ (hLS _ measurableSet_Icc), ← hμS, ← setLIntegral_one]
          refine setLIntegral_mono measurable_const fun x hx ↦ ?_
          rw [hd, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal (max_le ?_ ?_) <;>
            exact Real.exp_le_one_iff.mpr (by nlinarith [hx.2])
  have hinf := h ℝ≥0ˣ positiveRealHaar m hm surjective_id (Ici 0) isClosed_Ici ordConnected_Ici
    nonempty_Ici 0 le_rfl f g hfin
  -- The translate is one on `5/4 ≤ log t ≤ 7/4`, where the weight of exponent `k` is
  -- at least `exp (2k)`.
  let S' : Set ℝ≥0ˣ := {t | L t ∈ Icc (5 / 4 : ℝ) (7 / 4)}
  have hμS' : positiveRealHaar S' = ENNReal.ofReal (1 / 2) := by
    rw [positiveRealHaar_logPreimage_hardySobolevTranslation _ measurableSet_Icc,
      Real.volume_Icc]
    norm_num
  refine hinf.ne (ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_)
  obtain ⟨k, hk⟩ := exists_nat_ge (r : ℝ)
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  refine le_trans ?_ (le_iSup₂_of_le (⟨k, hk0⟩ : Ici (0 : ℝ)) (⟨k, hk0⟩ : Ici (0 : ℝ)) le_rfl)
  set ν := positiveRealHaar.withDensity fun x ↦
    ENNReal.ofReal (intervalSobolevDensity (k : ℝ) (k : ℝ) 0 (L x))
  have hνS' : ENNReal.ofReal ((k : ℝ) ^ 2) ≤ ν S' := by
    rw [withDensity_apply _ (hLS _ measurableSet_Icc)]
    calc ENNReal.ofReal ((k : ℝ) ^ 2)
        ≤ ∫⁻ _ in S', ENNReal.ofReal (Real.exp (2 * k)) ∂positiveRealHaar := by
          rw [setLIntegral_const, hμS', ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          refine ENNReal.ofReal_le_ofReal ?_
          have := Real.pow_div_factorial_le_exp (2 * (k : ℝ)) (by positivity) 2
          norm_num [Nat.factorial] at this
          nlinarith
      _ ≤ _ := by
          refine setLIntegral_mono (ENNReal.measurable_ofReal.comp
            ((show Measurable fun x : ℝ ↦ intervalSobolevDensity (k : ℝ) k 0 x by
              unfold intervalSobolevDensity; fun_prop).comp hL)) fun x hx ↦ ?_
          rw [hd, max_self]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [hx.1]))
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal ((k : ℝ) ^ 2) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        rw [ENNReal.ofReal_pow hk0, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
        exact_mod_cast hk
    _ ≤ ν S' ^ (1 / (2 : ℝ≥0∞).toReal) := ENNReal.rpow_le_rpow hνS' (by norm_num)
    _ = eLpNorm (S'.indicator fun _ ↦ (1 : ℂ)) 2 ν := by
        rw [eLpNorm_indicator_const (hLS _ measurableSet_Icc).nullMeasurableSet
          (by norm_num) (by norm_num), eNorm_one, one_mul]
    _ ≤ eLpNorm (fun x ↦ f.val (g⁻¹ * x)) 2 ν := by
        refine eLpNorm_mono ((measurable_const.indicator (hLS _ measurableSet_Icc)).aestronglyMeasurable)
          fun x ↦ ?_
        by_cases hx : x ∈ S'
        · rw [indicator_of_mem hx, norm_one]
          change 1 ≤ ‖((B (L (g⁻¹ * x)) : ℝ) : ℂ)‖
          rw [hLg, B.one_of_mem_closedBall]
          · simp
          rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
          change _ ∧ _ ≤ 1 / 4
          constructor <;> linarith [hx.1, hx.2]
        · rw [indicator_of_notMem hx, norm_zero]
          exact norm_nonneg _

/-- Paper: Lemma 9.3.2.1(2)–(4), p. 422. Given the extension (9.3.2.1), there is a
family indexed by the nonnegative integers and all norm-one characters. Each member is in its
indexed left isotype and its twisted Fourier transform is supported in the band
based on the chosen extension of that same character. The identity lies in the
strong closure of their images under the convolution extension (9.3.2.1).
Applying that map to B requires B to lie in its stated Schwartz domain, as
well as requiring the b-twists to be Schwartz. The band convention in
`exists_singletonDecay_isotype_approximation` uses the inverse isotype character.
See ERRATA F175. -/
def Printed.singletonDecay_approximation_isotype_band : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (b s : ℝ) (hs : 0 ≤ s),
    let K := m.toMonoidHom.ker
    ∀ χ : PontryaginDual K → PontryaginDual G,
    (∀ (ω : PontryaginDual K) (k : K), χ ω k.val = ω k) →
    let W := CompactIntervalSobolev μ logMod(m) b b s
    ∀ A : SchwartzBruhat G →L[ℂ] (W →L[ℂ] W),
      (∀ (d : BruhatCompactSupport G) (f : SchwartzBruhat G), f.val = d.val →
        A f = hardySobolevTestAction μ m b b s le_rfl hs d) →
    ∃ φ : ℕ → PontryaginDual K → SchwartzBruhat G,
      (∀ n ω, modulationWeight m b (φ n ω).val ∈ schwartzBruhatSubmodule G) ∧
      (∀ n ω (k : K) x, (φ n ω).val (k.val⁻¹ * x) = (ω k : ℂ) * (φ n ω).val x) ∧
      (∀ n ω, tsupport (lcaFourier μ (modulationWeight m b (φ n ω).val)) ⊆
        modulatedFrequencyBand m (χ ω) (-(n : ℝ)) n) ∧
      (ContinuousLinearMap.id ℂ W : W →Lₚₜ[ℂ] W) ∈
        closure (range (fun i : ℕ × PontryaginDual K ↦ (A (φ i.1 i.2) : W →Lₚₜ[ℂ] W)))

/-- A left-isotypic Schwartz kernel in the printed Fourier band vanishes when the character value is not its inverse. -/
private theorem singletonDecay_approximation_isotype_band_false_fourier_zero
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
    (ω : PontryaginDual m.toMonoidHom.ker) (χ : PontryaginDual G)
    (hχ : ∀ k : m.toMonoidHom.ker, χ k.val = ω k)
    (k : m.toMonoidHom.ker) (hk : (ω k) ^ 2 ≠ 1)
    (f : SchwartzBruhat G) (hf : ∀ x, f (k.val⁻¹ * x) = (ω k : ℂ) * f x)
    (a b : ℝ) (hband : tsupport (lcaFourier μ f) ⊆ modulatedFrequencyBand m χ a b) :
    f = 0 := by
  have hz (γ : PontryaginDual G) : lcaFourier μ f γ = 0 := by
    by_contra hne
    obtain ⟨t, ht, hγ⟩ := hband (subset_tsupport _ (mem_support.mpr hne))
    have hγk : γ k.val = ω k := by
      simpa only [show m k.val = 1 from k.property, Units.val_one, NNReal.coe_one,
        Real.log_one, mul_zero, Circle.exp_zero, mul_one, hχ] using hγ k.val
    have hscale : lcaFourier μ (fun x ↦ (ω k : ℂ) * f x) γ =
        (ω k : ℂ) * lcaFourier μ f γ := by
      unfold lcaFourier
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    have hh := lcaFourier_translate μ (f : G → ℂ) k.val⁻¹ γ
    rw [funext hf, hscale, map_inv, hγk, Circle.coe_inv] at hh
    have heq : (ω k : ℂ) = (ω k : ℂ)⁻¹ := mul_right_cancel₀ hne hh
    apply hk
    apply Subtype.ext
    change (ω k : ℂ) ^ 2 = 1
    have hωne : (ω k : ℂ) ≠ 0 := fun h ↦ by simpa [h] using Circle.norm_coe (ω k)
    calc
      (ω k : ℂ) ^ 2 = (ω k : ℂ)⁻¹ * (ω k : ℂ) := by simpa only [pow_two] using congrArg (fun z : ℂ ↦ z * (ω k : ℂ)) heq
      _ = 1 := inv_mul_cancel₀ hωne
  have hae := ae_eq_zero_of_lcaFourier_eq_zero μ (SchwartzBruhat.integrable μ f) hz
  have heq : (f : G → ℂ) = 0 :=
    Measure.eq_of_ae_eq hae (schwartzBruhat_continuous f) continuous_const
  exact Subtype.ext heq
/-- Pettis convolution by a kernel of one isotype kills a vector of a different isotype. -/
private theorem singletonDecay_approximation_isotype_band_false_convolution_zero
    (G E : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : G →* (E →L[ℂ] E)) (k : G) (c d : ℂ) (hcd : c ≠ d)
    (f : G → ℂ) (hf : ∀ g, f (k⁻¹ * g) = c * f g)
    (u a : E) (hu : ρ k u = d • u)
    (ha : HasPettisIntegral (.positive μ) (fun g ↦ f g • ρ g u) a) : a = 0 := by
  have hz (δ : StrongDual ℂ E) : δ a = 0 := by
    have he : δ (ρ k a) = ∫ g, δ (ρ k (f g • ρ g u)) ∂μ :=
      eval_pettis_positive μ ha (δ.comp (ρ k))
    have hl : δ (ρ k a) = c * δ a := by
      rw [he, ← integral_mul_left_eq_self (μ := μ) (fun g ↦ δ (ρ k (f g • ρ g u))) k⁻¹]
      calc
        (∫ g, δ (ρ k (f (k⁻¹ * g) • ρ (k⁻¹ * g) u)) ∂μ) = ∫ g, c * δ (f g • ρ g u) ∂μ := by
          apply integral_congr_ae
          filter_upwards with g
          have hv : ρ k (ρ (k⁻¹ * g) u) = ρ g u := by
            rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
          rw [map_smul, hv, hf, map_smul, map_smul, smul_eq_mul]
          ring
        _ = c * δ a := by rw [integral_const_mul, ← eval_pettis_positive μ ha δ]
    have hr : δ (ρ k a) = d * δ a := by
      rw [he]
      calc
        (∫ g, δ (ρ k (f g • ρ g u)) ∂μ) = ∫ g, d * δ (f g • ρ g u) ∂μ := by
          apply integral_congr_ae
          filter_upwards with g
          have hv : ρ k (ρ g u) = d • ρ g u := by
            rw [← mul_apply_eq_comp, ← map_mul, mul_comm k g, map_mul,
              mul_apply_eq_comp, hu, map_smul]
          rw [map_smul, hv, smul_smul, map_smul, map_smul, smul_eq_mul]
          ring
        _ = d * δ a := by rw [integral_const_mul, ← eval_pettis_positive μ ha δ]
    exact (mul_eq_mul_right_iff.mp (hl.symm.trans hr)).resolve_left hcd
  apply ext_inner_left ℂ
  intro z
  simpa only [innerSL_apply_apply, inner_zero_right] using hz (innerSL ℂ z)
/-- The printed kernel conditions cannot strongly approximate the identity on a nonzero mismatched eigenspace. -/
private theorem singletonDecay_approximation_isotype_band_false_strong_obstruction
    (G E : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : G →* (E →L[ℂ] E)) (A : SchwartzBruhat G →L[ℂ] (E →L[ℂ] E))
    (hA : ∀ f u, HasPettisIntegral (.positive μ) (fun g ↦ f.val g • T g u) (A f u))
    (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
    (hχ : ∀ ω k, χ ω k.val = ω k) (k : m.toMonoidHom.ker)
    (z : Circle) (hz : z ^ 2 ≠ 1) (u : E) (hu : u ≠ 0) (heigen : T k.val u = (z : ℂ) • u)
    (φ : ℕ → PontryaginDual m.toMonoidHom.ker → SchwartzBruhat G)
    (hφ : ∀ n ω x, φ n ω (k.val⁻¹ * x) = (ω k : ℂ) * φ n ω x)
    (hband : ∀ n ω, tsupport (lcaFourier μ (φ n ω)) ⊆ modulatedFrequencyBand m (χ ω) (-(n : ℝ)) n) :
    (ContinuousLinearMap.id ℂ E : E →Lₚₜ[ℂ] E) ∉
      @closure (E →Lₚₜ[ℂ] E) inferInstance (range (fun i : ℕ × PontryaginDual m.toMonoidHom.ker ↦ (A (φ i.1 i.2) : E →Lₚₜ[ℂ] E))) := by
  have hkill (n : ℕ) (ω : PontryaginDual m.toMonoidHom.ker) : A (φ n ω) u = 0 := by
    by_cases he : (ω k : ℂ) = (z : ℂ)
    · have hw : (ω k) ^ 2 ≠ 1 := by simpa only [show ω k = z from Subtype.ext he] using hz
      have hf := singletonDecay_approximation_isotype_band_false_fourier_zero G μ m ω (χ ω) (hχ ω) k hw (φ n ω) (hφ n ω) _ _ (hband n ω)
      rw [hf, map_zero, ContinuousLinearMap.zero_apply]
    · exact singletonDecay_approximation_isotype_band_false_convolution_zero G E μ T k (ω k : ℂ) (z : ℂ) he
        (φ n ω) (hφ n ω) u (A (φ n ω) u) heigen (hA (φ n ω) u)
  have hc : IsClosed {B : E →Lₚₜ[ℂ] E | B u = 0} := isClosed_eq (PointwiseConvergenceCLM.evalCLM (σ := RingHom.id ℂ) (E := E) (F := E) u).continuous continuous_const
  have hs : @closure (E →Lₚₜ[ℂ] E) inferInstance (range (fun i : ℕ × PontryaginDual m.toMonoidHom.ker ↦
      (A (φ i.1 i.2) : E →Lₚₜ[ℂ] E))) ⊆ {B : E →Lₚₜ[ℂ] E | B u = 0} := by
    apply closure_minimal _ hc
    rintro B ⟨⟨n, ω⟩, rfl⟩
    exact hkill n ω
  intro hid
  have hh := hs (a := (ContinuousLinearMap.id ℂ E : E →Lₚₜ[ℂ] E)) hid
  exact hu hh
/-- A proper modulus has a compact positive-mass log band invariant under its kernel. -/
private theorem singletonDecay_approximation_isotype_band_false_band
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m) :
    ∃ A : Set G, MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ⊤ ∧
      ∀ k : G, m k = 1 → ∀ x : G, (k⁻¹ * x ∈ A ↔ x ∈ A) := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) := (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let l : G → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  let A : Set G := l ⁻¹' Icc (-1) 1
  have hl : Continuous l := by simpa [l, Function.comp_def, he] using e.continuous.comp m.continuous
  have hcompact : IsCompact A := by
    have hh := (e.isProperMap.comp hm).isCompact_preimage (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    simpa only [Function.comp_def, he] using hh
  have hA : MeasurableSet A := hcompact.measurableSet
  have hmass : μ A ≠ 0 := by
    have hU : IsOpen (l ⁻¹' Ioo (-1) 1) := isOpen_Ioo.preimage hl
    have hnonempty : (l ⁻¹' Ioo (-1) 1).Nonempty := ⟨1, by simp [l]⟩
    intro hzero
    exact hU.measure_ne_zero μ hnonempty (measure_mono_null (preimage_mono Ioo_subset_Icc_self) hzero)
  refine ⟨A, hA, hmass, hcompact.measure_lt_top.ne, ?_⟩
  intro k hk x
  simp only [A, l, mem_preimage, map_mul, map_inv, hk, inv_one, one_mul]
/-- A unitary character gives a nonzero weighted-free L² eigenvector for kernel translations. -/
private theorem singletonDecay_approximation_isotype_band_false_eigenvector
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m)
    (ξ : PontryaginDual G) (k : G) (hk : m k = 1)
    (T : G →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
    (hT : ∀ g u, (T g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x)) :
    ∃ u : Lp ℂ 2 μ, u ≠ 0 ∧ T k u = (ξ k : ℂ) • u := by
  classical
  obtain ⟨A, hA, hpos, hfinite, hinv⟩ := singletonDecay_approximation_isotype_band_false_band G μ m hm
  have hξ : MemLp (fun x ↦ star (ξ x : ℂ)) ⊤ μ :=
    memLp_top_of_bound (((continuous_subtype_val : Continuous (fun z : Circle ↦ (z : ℂ))).comp ξ.continuous).star).measurable.aestronglyMeasurable 1
      (.of_forall fun x ↦ by simp)
  have hI : MemLp (A.indicator (fun _ ↦ (1 : ℂ))) 2 μ :=
    memLp_indicator_const 2 hA.nullMeasurableSet 1 (Or.inr hfinite)
  let f (x : G) := star (ξ x : ℂ) * A.indicator (fun _ ↦ (1 : ℂ)) x
  have hf : MemLp f 2 μ := hξ.mul hI
  let u : Lp ℂ 2 μ := hf.toLp f
  have hu : (u : G → ℂ) =ᵐ[μ] f := MemLp.coeFn_toLp hf
  have hune : u ≠ 0 := by
    intro hz
    have hz' : f =ᵐ[μ] 0 := hu.symm.trans (hz ▸ Lp.coeFn_zero ℂ 2 μ)
    have hnot : ∀ᵐ x ∂μ, x ∉ A := by
      filter_upwards [hz'] with x hx
      intro hmem
      have hh := congrArg norm hx
      simp only [f, indicator_of_mem hmem, mul_one, norm_star, Circle.norm_coe, Pi.zero_apply, norm_zero] at hh
      norm_num at hh
    exact hpos (by simpa only [ae_iff, not_not, setOf_mem_eq] using hnot)
  refine ⟨u, hune, ?_⟩
  have hpoint (x : G) : f (k⁻¹ * x) = (ξ k : ℂ) * f x := by
    have he : A.indicator (fun _ ↦ (1 : ℂ)) (k⁻¹ * x) = A.indicator (fun _ ↦ (1 : ℂ)) x := by
      simp only [indicator_apply, hinv k hk x]
    dsimp only [f]
    rw [he, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj, star_mul,
      Complex.star_def, Complex.conj_conj]
    ring
  apply Lp.ext
  filter_upwards [hT k u, (measurePreserving_mul_left μ k⁻¹).quasiMeasurePreserving.ae_eq_comp hu,
    hu, Lp.coeFn_smul (ξ k : ℂ) u] with x hx hraw hux hscalar
  change u (k⁻¹ * x) = f (k⁻¹ * x) at hraw
  rw [hx, hraw, hpoint, hscalar]
  change (ξ k : ℂ) * f x = (ξ k : ℂ) * u x
  rw [hux]

/-- Paper: Lemma 9.3.2.1(2)–(4), pp. 422–424. Take the positive reals times
Circle, module the first projection, Haar measure, and b = s = 0. At an element
with circle coordinate i, the printed Fourier band forces a kernel with
character value i to vanish. Kernels with other character values kill a nonzero
L² vector in the i-eigenspace. Their strong closure therefore excludes the
identity. The proof also transports the operator-norm closure inferred by the
current statement to pointwise closure; neither closure contains the identity. -/
theorem Printed.singletonDecay_approximation_isotype_band_false :
    ¬ Printed.singletonDecay_approximation_isotype_band := by
  classical
  intro hall
  letI : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  letI : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  letI : MeasurableSpace Circle := borel _
  letI : BorelSpace Circle := ⟨rfl⟩
  letI : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let G := ℝ≥0ˣ × Circle
  let m : G →ₜ* ℝ≥0ˣ := ⟨MonoidHom.fst _ _, continuous_fst⟩
  have hm : IsModulation m := by
    refine ⟨isProperMap_fst_of_compactSpace, ⟨(Units.mk0 2 (by norm_num), 1), ?_⟩⟩
    intro he
    have hh := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) he
    change (2 : ℝ) = 1 at hh
    norm_num at hh
  have hsur : Surjective m := fun t ↦ ⟨(t, 1), rfl⟩
  let μ : Measure G := Measure.haar
  let q : G →ₜ* m.toMonoidHom.ker :=
    { toFun := fun x ↦ ⟨(1, x.2), rfl⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ ↦ Subtype.ext (Prod.ext (one_mul 1).symm rfl)
      continuous_toFun := (continuous_const.prodMk continuous_snd).subtype_mk _ }
  let χ (ω : PontryaginDual m.toMonoidHom.ker) : PontryaginDual G := ω.comp q
  have hχ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker) : χ ω k.val = ω k := by
    apply congrArg ω
    apply Subtype.ext
    exact Prod.ext k.property.symm rfl
  let z : Circle := ⟨Complex.I, by exact mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
  have hz : z ^ 2 ≠ 1 := by
    intro he
    have hh := congrArg (fun t : Circle ↦ (t : ℂ)) he
    rw [Circle.coe_pow, Circle.coe_one] at hh
    change Complex.I ^ 2 = 1 at hh
    norm_num [Complex.I_sq] at hh
  let k : m.toMonoidHom.ker := ⟨(1, z), rfl⟩
  let ξ : PontryaginDual G := ⟨MonoidHom.snd _ _, continuous_snd⟩
  let ν : Measure G := μ.withDensity (fun x ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 0 (Real.log ((m x).val : ℝ))))
  have hν : ν = μ := by simp [ν, intervalSobolevDensity]
  letI : ν.IsHaarMeasure := by rw [hν]; infer_instance
  let T : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) := by
    with_unfolding_all exact hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl
  have hT (g : G) (u : Lp ℂ 2 ν) : (T g u : G → ℂ) =ᵐ[ν] fun x ↦ u (g⁻¹ * x) := by
    with_unfolding_all
      exact (withDensity_absolutelyContinuous μ _).ae_eq
        (hardySobolevTranslation_apply μ m 0 0 0 le_rfl le_rfl g u)
  obtain ⟨u, hu, heigen⟩ := singletonDecay_approximation_isotype_band_false_eigenvector G ν m hm.1 ξ k.val k.property T hT
  have heigen' : T k.val u = (z : ℂ) • u := heigen
  have hAct : ∃ A : SchwartzBruhat G →L[ℂ] (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν),
      ∀ f u, HasPettisIntegral (.positive μ) (fun g ↦ f.val g • T g u) (A f u) := by
    with_unfolding_all exact (existsUnique_schwartzBruhat_zeroLineAction μ m 0 le_rfl).exists
  obtain ⟨A, hA⟩ := hAct
  have hExt (d : BruhatCompactSupport G) (f : SchwartzBruhat G) (hf : f.val = d.val) :
      A f = hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl d := by
    apply ContinuousLinearMap.ext
    intro v
    have ha := hA f v
    rw [hf] at ha
    apply ha.unique
    have hd : HasPettisIntegral (.positive μ) (fun g ↦ d.val g • T g v)
        (hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl d v) := by
      with_unfolding_all
        exact bruhatRegularizedAction_apply μ
          (hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl)
          (exists_hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl).choose_spec.2 d v
    exact hd
  obtain ⟨φ, htwist, hiso, hband, hclosure⟩ := hall G μ m hm hsur 0 0 le_rfl χ hχ A hExt
  have hpointwise : (ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) : (Lp ℂ 2 ν) →Lₚₜ[ℂ] (Lp ℂ 2 ν)) ∈
      @closure ((Lp ℂ 2 ν) →Lₚₜ[ℂ] (Lp ℂ 2 ν)) inferInstance
        (range (fun i : ℕ × PontryaginDual m.toMonoidHom.ker ↦ (A (φ i.1 i.2) : (Lp ℂ 2 ν) →Lₚₜ[ℂ] (Lp ℂ 2 ν)))) := by
    let J := ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (Lp ℂ 2 ν) (Lp ℂ 2 ν)
    have hh := mem_closure_image J.continuous.continuousAt hclosure
    have hid : J (ContinuousLinearMap.id ℂ (CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 0)) =
        (ContinuousLinearMap.id ℂ (Lp ℂ 2 ν) : (Lp ℂ 2 ν) →Lₚₜ[ℂ] (Lp ℂ 2 ν)) := by
      ext v
      rfl
    rw [hid] at hh
    have hset : J '' range (fun i : ℕ × PontryaginDual m.toMonoidHom.ker ↦ A (φ i.1 i.2)) =
        range (fun i : ℕ × PontryaginDual m.toMonoidHom.ker ↦ (A (φ i.1 i.2) : (Lp ℂ 2 ν) →Lₚₜ[ℂ] (Lp ℂ 2 ν))) := by
      rw [← Set.range_comp]
      congr 1
    rw [hset] at hh
    exact hh
  exact singletonDecay_approximation_isotype_band_false_strong_obstruction G (Lp ℂ 2 ν) μ m T A hA χ hχ k z hz u hu heigen' φ
    (fun n ω x ↦ hiso n ω k x) (fun n ω ↦ by simpa only [modulationWeight_zero] using hband n ω) hpointwise

/-- Paper: Theorem 9.3.2.6, (9.3.2.10), p. 426. As the cutoff height grows,
the orthogonal projections onto the common kernels of all indicated Mellin
jets converge strongly to the identity. The Hilbert completion is specified
by its dense test map and the norm (9.2.2.31).
Deviation: The display uses the character and test from Lemma 9.3.2.5 without
binding them again. We use those data and its interior-zero hypothesis. The
convergence assertion is made for each realization of the printed completion,
since on an unbounded base the displayed norm can be infinite. See ERRATA F144. -/
def Printed.hardySobolevJetKernelProjection_tendsto : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m), Surjective m →
    ∀ (I : Set ℝ), IsClosed I → OrdConnected I → (interior I).Nonempty →
    ∀ s : ℝ, 0 ≤ s → ∀ (χ : PontryaginDual G) (φ : ModulatedExponentialDecay m univ),
    let μ := canonicalModulatedHaar m hm
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let M := fun (f : ModulatedExponentialDecay m univ) (z : ℂ) ↦
      modulatedFourierMellin m univ hm μ f.val (quasiCharacterNormTwist m.toMonoidHom m.continuous χ₀ z)
    (∀ z, M φ z = 0 → z.re ∈ interior I) →
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
      (ι : ModulatedExponentialDecay m univ →ₗ[ℂ] W), DenseRange ι →
      (∀ f, ENNReal.ofReal ‖ι f‖ = intervalSobolevENorm μ logMod(m) I s f.val) →
      let J := {i : ℂ × ℕ // M φ i.1 = 0 ∧ (i.2 : ℕ∞) < analyticOrderAt (M φ) i.1}
      ∃ (δ : J → W →L[ℂ] ℂ) (P : Ioi (0 : ℝ) → W →L[ℂ] W),
        (∀ i f, δ i (ι f) = iteratedDeriv i.val.2 (M f) i.val.1) ∧
        (∀ T, IsStarProjection (P T) ∧
          range (P T) = {u | ∀ i : J, |i.val.1.im| ≤ T.val → δ i u = 0}) ∧
        ∀ u, Tendsto (fun T ↦ P T u) atTop (𝓝 u)

/-- The Gaussian profile centred at `c`. -/
private theorem gaussProfile_mem_hardySobolevJetKernelProjection (c : ℝ) :
    (fun x : ℝ ↦ Complex.exp (-(((x - c : ℝ) : ℂ) ^ 2))) ∈
      logExponentialDecaySubmodule univ := by
  refine Submodule.mem_iInf _ |>.mpr fun a ↦ ?_
  refine Submodule.mem_comap.mpr ⟨(Real.exp (a * c + a ^ 2 / 4) : ℂ) •
    SchwartzMap.compSubConstCLM ℂ (c + a / 2)
      ((SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM), ?_⟩
  funext x
  change (Real.exp (a * c + a ^ 2 / 4) : ℂ) *
      Complex.ofRealCLM (SchwartzMap.gaussian 1 one_pos (x - (c + a / 2))) =
    (Real.exp (a * x) : ℂ) * Complex.exp (-(((x - c : ℝ) : ℂ) ^ 2))
  rw [SchwartzMap.gaussian_apply, Complex.ofRealCLM_apply, Real.norm_eq_abs, sq_abs,
    Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Integration against `dt/t` in logarithmic coordinates. -/
private theorem integral_positiveRealHaar_hardySobolevJetKernelProjection
    (_hBo : BorelSpace ℝ≥0ˣ) (F : ℝ≥0ˣ → ℂ) :
    ∫ t, F t ∂positiveRealHaar = ∫ x : ℝ, F (Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) := by
  let E : ℝ → ℝ≥0ˣ := fun x ↦ Units.mk0 (Real.exp x).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))
  let L : ℝ≥0ˣ → ℝ := fun t ↦ Real.log (t.val : ℝ)
  have hE : Measurable E :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hL : Measurable L :=
    Real.measurable_log.comp (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  have hLE : LeftInverse L E := fun x ↦ by
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  have hEL : RightInverse L E := fun t ↦ Units.ext (NNReal.eq (by
    change ((Real.exp (Real.log (t.val : ℝ))).toNNReal : ℝ) = _
    rw [Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt t)),
      Real.coe_toNNReal _ (NNReal.coe_nonneg _)]))
  have hrange : range E = univ := range_eq_univ.mpr hEL.surjective
  have hme : MeasurableEmbedding E :=
    MeasurableEmbedding.of_measurable_inverse hE (hrange ▸ MeasurableSet.univ) hL hLE
  exact hme.integral_map F

/-- The Gaussian Laplace transform: the profile centred at `c` against `exp(zx)`. -/
private theorem integral_gaussProfile_hardySobolevJetKernelProjection (c : ℝ) (z : ℂ) :
    ∫ x : ℝ, Complex.exp (-(((x - c : ℝ) : ℂ) ^ 2)) * Complex.exp (z * x) =
      ((Real.pi : ℂ) / -(-1)) ^ (1 / 2 : ℂ) * Complex.exp (z ^ 2 / 4 + c * z) := by
  have h (x : ℝ) : Complex.exp (-(((x - c : ℝ) : ℂ) ^ 2)) * Complex.exp (z * x) =
      Complex.exp (-1 * (x : ℂ) ^ 2 + (2 * c + z) * x + -(c : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_cexp_quadratic (by norm_num)]
  congr 2
  ring

/-- The difference of the Gaussian profiles at `0` and `1` against `exp(zx)`. -/
private theorem integral_gaussDifference_hardySobolevJetKernelProjection (z : ℂ) :
    ∫ x : ℝ, (Complex.exp (-(((x - 0 : ℝ) : ℂ) ^ 2)) - Complex.exp (-(((x - 1 : ℝ) : ℂ) ^ 2))) *
        Complex.exp (z * x) =
      ((Real.pi : ℂ) / -(-1)) ^ (1 / 2 : ℂ) *
        (Complex.exp (z ^ 2 / 4 + (0 : ℝ) * z) - Complex.exp (z ^ 2 / 4 + (1 : ℝ) * z)) := by
  have hi (c : ℝ) : Integrable fun x : ℝ ↦
      Complex.exp (-(((x - c : ℝ) : ℂ) ^ 2)) * Complex.exp (z * x) := by
    have h (x : ℝ) : Complex.exp (-(((x - c : ℝ) : ℂ) ^ 2)) * Complex.exp (z * x) =
        Complex.exp (-1 * (x : ℂ) ^ 2 + (2 * c + z) * x + -(c : ℂ) ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [h]
    exact integrable_cexp_quadratic (by norm_num) _ _
  simp_rw [sub_mul]
  rw [integral_sub (hi 0) (hi 1), integral_gaussProfile_hardySobolevJetKernelProjection,
    integral_gaussProfile_hardySobolevJetKernelProjection, mul_sub]

/-- On the base `[-1, 1]` with degree zero, the supremum of the endpoint norms is the
norm with endpoints `-1` and `1`. -/
private theorem intervalSobolevDensity_le_hardySobolevJetKernelProjection (a b : Icc (-1 : ℝ) 1)
    (y : ℝ) : intervalSobolevDensity a b 0 y ≤ intervalSobolevDensity (-1) 1 0 y := by
  have h (u : Icc (-1 : ℝ) 1) :
      Real.exp (2 * u * y) ≤ max (Real.exp (2 * -1 * y)) (Real.exp (2 * 1 * y)) := by
    obtain ⟨u, hu1, hu2⟩ := u
    rcases le_total 0 y with hy | hy
    · exact (Real.exp_le_exp.mpr (by nlinarith)).trans (le_max_right _ _)
    · exact (Real.exp_le_exp.mpr (by nlinarith)).trans (le_max_left _ _)
  unfold intervalSobolevDensity
  exact mul_le_mul_of_nonneg_right (max_le (h a) (h b)) (by positivity)

/-- Paper: Theorem 9.3.2.6, p. 426. Use the positive reals with identity module,
trivial character, I = [−1,1] and s = 0. In log coordinates use
g(x) = exp(−x²/4)/√(4π) and φ = −g′. Their Mellin transforms are exp(z²) and
z exp(z²). Zero is the unique zero of the latter and is simple. The compact
interval weighted L² model realizes the completion. For every positive T the
range is the kernel of evaluation at zero. That functional takes value 1 on
the vector of g, so continuity rules out convergence of its projections to g. -/
theorem Printed.hardySobolevJetKernelProjection_tendsto_false :
    ¬ Printed.hardySobolevJetKernelProjection_tendsto := by
  intro h
  have hBo : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  have hm : IsModulation m := isModulation_id_hardySobolevTranslation
  let μ := canonicalModulatedHaar m hm
  have : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  let k := μ.haarScalarFactor positiveRealHaar
  have hμ : μ = k • positiveRealHaar := Measure.isMulLeftInvariant_eq_smul μ positiveRealHaar
  have hk0 : (k : ℂ) ≠ 0 := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ positiveRealHaar).ne'
  obtain ⟨e, he⟩ := identityModulationExponentialDecay_equiv univ ordConnected_univ univ_nonempty
  let p : ℝ → ℝ → ℂ := fun c x ↦ Complex.exp (-(((x - c : ℝ) : ℂ) ^ 2))
  let g0 : ModulatedExponentialDecay m univ :=
    e ⟨p 0, gaussProfile_mem_hardySobolevJetKernelProjection 0⟩
  let φ : ModulatedExponentialDecay m univ :=
    e ⟨p 0 - p 1, sub_mem (gaussProfile_mem_hardySobolevJetKernelProjection 0)
      (gaussProfile_mem_hardySobolevJetKernelProjection 1)⟩
  have hg0val (t : ℝ≥0ˣ) : g0.val t = p 0 (Real.log (t.val : ℝ)) := he _ t
  have hφval (t : ℝ≥0ˣ) : φ.val t = (p 0 - p 1) (Real.log (t.val : ℝ)) := he _ t
  let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
    (1 : PontryaginDual ℝ≥0ˣ)
  have hχ (t : ℝ≥0ˣ) : χ₀ t = 1 := by
    change (((1 : PontryaginDual ℝ≥0ˣ) t : Circle) : ℂ) = 1
    rw [PontryaginDual.one_apply, Circle.coe_one]
  let M := fun (f : ModulatedExponentialDecay m univ) (z : ℂ) ↦
    modulatedFourierMellin m univ hm μ f.val
      (quasiCharacterNormTwist m.toMonoidHom m.continuous χ₀ z)
  -- The Fourier–Mellin transform of a log-profile is its Laplace transform, up to `k`.
  have hM (f : ModulatedExponentialDecay m univ) (q : ℝ → ℂ)
      (hq : ∀ t : ℝ≥0ˣ, f.val t = q (Real.log (t.val : ℝ))) (z : ℂ) :
      M f z = (k : ℂ) * ∫ x : ℝ, q x * Complex.exp (z * x) := by
    have hstrip : quasiCharacterNormTwist m.toMonoidHom m.continuous χ₀ z ∈
        relativeVerticalStrip m.toMonoidHom (And.left hm) (And.right hm) univ := trivial
    change Set.indicator _ _ _ = _
    rw [Set.indicator_of_mem hstrip, hμ, integral_smul_nnreal_measure,
      integral_positiveRealHaar_hardySobolevJetKernelProjection hBo]
    refine (NNReal.smul_def k _).trans (Complex.real_smul.trans ?_)
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    have hx : ((Real.exp x).toNNReal : ℝ) = Real.exp x := Real.coe_toNNReal _ (Real.exp_pos x).le
    change f.val _ * (χ₀ _ * ((((Real.exp x).toNNReal : ℝ≥0) : ℝ) : ℂ) ^ z) = _
    rw [hq]
    simp only [Units.val_mk0, hx, hχ, one_mul]
    rw [Real.log_exp, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    simp [mul_comm]
  let A : ℂ := ((Real.pi : ℂ) / -(-1)) ^ (1 / 2 : ℂ)
  have hA : A ≠ 0 := by
    simp only [A, Ne, Complex.cpow_eq_zero_iff, neg_neg, div_one, Complex.ofReal_eq_zero,
      Real.pi_ne_zero, false_and, not_false_eq_true]
  have hMφ (z : ℂ) : M φ z = (k : ℂ) * (A * (Complex.exp (z ^ 2 / 4 + ((0 : ℝ) : ℂ) * z) -
      Complex.exp (z ^ 2 / 4 + ((1 : ℝ) : ℂ) * z))) := by
    rw [hM φ (p 0 - p 1) hφval z]
    exact congrArg _ (integral_gaussDifference_hardySobolevJetKernelProjection z)
  have hzeros : ∀ z, M φ z = 0 → z.re ∈ interior (Icc (-1 : ℝ) 1) := by
    intro z hz
    rw [hMφ, mul_eq_zero, mul_eq_zero, sub_eq_zero] at hz
    rcases hz with h0 | h0 | h0
    · exact absurd h0 hk0
    · exact absurd h0 hA
    · simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, add_zero, one_mul,
        Complex.exp_add] at h0
      have h1 : Complex.exp z = 1 :=
        ((mul_eq_left₀ (Complex.exp_ne_zero _)).mp h0.symm)
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      rw [interior_Icc, hn]
      simp
  have hval0 : M φ 0 = 0 := by
    rw [hMφ]
    simp
  have han : AnalyticAt ℂ (M φ) 0 := by
    rw [show M φ = _ from funext hMφ]
    exact Differentiable.analyticAt (by fun_prop) 0
  have hord : ((0 : ℕ) : ℕ∞) < analyticOrderAt (M φ) 0 := by
    rw [Nat.cast_zero, pos_iff_ne_zero]
    exact analyticOrderAt_ne_zero.mpr ⟨han, hval0⟩
  -- The completion: weighted L² with the endpoint density of `[-1, 1]`.
  obtain ⟨j, -, hjd, hjrep⟩ := modulatedIntervalSobolev_dense m hm (-1) 1 0 (by norm_num) le_rfl
    univ isOpen_univ ordConnected_univ (subset_univ _)
  have hnorm : ∀ f : ModulatedExponentialDecay m univ,
      ENNReal.ofReal ‖(j : ModulatedExponentialDecay m univ →ₗ[ℂ] ModulatedIntervalSobolev m hm (-1) 1 0) f‖ =
      intervalSobolevENorm μ (fun x ↦ Real.log ((m x).val : ℝ)) (Icc (-1) 1) 0 f.val := by
    intro f
    have hac : (μ.withDensity fun x ↦ ENNReal.ofReal
        (intervalSobolevDensity (-1) 1 0 (Real.log ((m x).val : ℝ)))) ≪ μ :=
      withDensity_absolutelyContinuous _ _
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    change eLpNorm (j f) 2 (μ.withDensity fun x ↦ ENNReal.ofReal
      (intervalSobolevDensity (-1) 1 0 (Real.log ((m x).val : ℝ)))) = _
    rw [eLpNorm_congr_ae (hac.ae_eq (hjrep f))]
    refine le_antisymm (le_iSup₂_of_le (⟨-1, by norm_num⟩ : Icc (-1 : ℝ) 1)
      (⟨1, by norm_num⟩ : Icc (-1 : ℝ) 1) le_rfl) (iSup₂_le fun a b ↦ ?_)
    exact eLpNorm_mono_measure _ (withDensity_mono (ae_of_all _ fun x ↦
      ENNReal.ofReal_le_ofReal (intervalSobolevDensity_le_hardySobolevJetKernelProjection a b _)))
  have hI : (interior (Icc (-1 : ℝ) 1)).Nonempty := ⟨0, by rw [interior_Icc]; norm_num⟩
  obtain ⟨δ, P, hδ, hP, hlim⟩ := h ℝ≥0ˣ m hm surjective_id (Icc (-1) 1) isClosed_Icc
    ordConnected_Icc hI 0 le_rfl 1 φ hzeros _
    (j : ModulatedExponentialDecay m univ →ₗ[ℂ] ModulatedIntervalSobolev m hm (-1) 1 0) hjd hnorm
  -- Every projection lands in the kernel of the value at the zero `0`, so the limit does too.
  let i₀ : {i : ℂ × ℕ // M φ i.1 = 0 ∧ (i.2 : ℕ∞) < analyticOrderAt (M φ) i.1} :=
    ⟨(0, 0), hval0, hord⟩
  let u := (j : ModulatedExponentialDecay m univ →ₗ[ℂ] ModulatedIntervalSobolev m hm (-1) 1 0) g0
  have hT (T : Ioi (0 : ℝ)) : δ i₀ (P T u) = 0 := by
    have hmem : P T u ∈ range (P T) := ⟨u, rfl⟩
    rw [(hP T).2] at hmem
    exact hmem i₀ (by simpa [i₀] using T.2.le)
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, one_pos⟩⟩
  have hlim0 := ((δ i₀).continuous.tendsto u).comp (hlim u)
  rw [show (δ i₀ ∘ fun T ↦ P T u) = fun _ ↦ 0 from funext hT] at hlim0
  have hu : δ i₀ u = 0 := tendsto_nhds_unique tendsto_const_nhds hlim0 |>.symm
  rw [hδ] at hu
  change iteratedDeriv 0 (M g0) 0 = 0 at hu
  rw [iteratedDeriv_zero, hM g0 (p 0) hg0val,
    integral_gaussProfile_hardySobolevJetKernelProjection] at hu
  simp only [zero_pow two_ne_zero, zero_div, mul_zero, add_zero, Complex.exp_zero,
    mul_one, mul_eq_zero, hk0, false_or] at hu
  exact hA hu

/-- Paper: Theorem 9.3.3.5(3), (9.3.3.9), p. 429. On the reading that (3)
uses the bounded compactly supported symbols in (1), the integral of the
smoothed diagonal differs from 2 log(Λ) μ₁(G¹) φ(1) by o(1).
Deviation: This is the ordinary Haar L² case I = {0}, s = 0 used on p. 429.
Measurability of the symbol is implicit in the kernel integral. If (3)
inherits the smoothness assumptions of (2), the singleton symbol below is
outside its scope. See ERRATA F175 and `truncatedHardySobolevConvolution_trace_tendsto`. -/
def Printed.truncatedHardySobolevConvolution_diagonal_tendsto : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m →
    ∀ (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m →
    ∀ (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure],
    μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2) →
    ∀ (φ : G → ℂ), AEMeasurable φ μ → HasCompactSupport φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) →
    ∀ (U : ℕ → Set G), IsDPrimeSequence μ U → (∀ n, MeasurableSet (U n)) →
    ∀ (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ),
    Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) →
    (∀ x, Tendsto (fun Λ ↦ ρ Λ x) atTop (𝓝 1)) →
    (∀ᶠ Λ in atTop, IsModulatedCutoff m Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ) →
    let κ (Λ : ℝ) (p : G × G) := (ρ Λ p.1 : ℂ) * φ (p.1 * p.2⁻¹)
    let diagonal (Λ : ℝ) (x : G) := dSequenceKernelSmoothening μ U (κ Λ) (x, x)
    (∀ᶠ Λ in atTop, Integrable (diagonal Λ) μ) ∧
      Tendsto (fun Λ ↦ (∫ x, diagonal Λ x ∂μ) -
        (2 * Real.log Λ * μ₁.real univ : ℝ) * φ 1) atTop (𝓝 0)

/-- A kernel that vanishes almost everywhere for the product measure has zero
product smoothening: every average vanishes. -/
private theorem dSequenceKernelSmoothening_eq_zero_diagonalTendsto {G : Type*} [CommGroup G]
    [MeasurableSpace G] (μ : Measure G) (U : ℕ → Set G) (k : G × G → ℂ)
    (hk : k =ᵐ[μ.prod μ] 0) (p : G × G) : dSequenceKernelSmoothening μ U k p = 0 := by
  have havg (n : ℕ) : dSequenceAverage (μ.prod μ) (U n ×ˢ U n) k p = 0 := by
    unfold dSequenceAverage
    rw [setAverage_eq, integral_congr_ae (ae_restrict_of_ae hk)]
    simp
  unfold dSequenceKernelSmoothening dSequenceSmootheningOrZero
  split_ifs with hx
  · simp only [dSequenceSmoothening, havg]
    exact tendsto_const_nhds.limUnder_eq
  · rfl

/-- If a function is locally constant with value `v` near the points of a filter, its
iterated derivatives tend to those of the constant `v`. -/
private theorem tendsto_iteratedDeriv_diagonalTendsto {q : ℝ → ℝ} {l : Filter ℝ} (v : ℝ)
    (h : ∀ᶠ y in l, q =ᶠ[𝓝 y] fun _ ↦ v) (n : ℕ) :
    Tendsto (iteratedDeriv n q) l (𝓝 (if n = 0 then v else 0)) :=
  tendsto_const_nhds.congr' (h.mono fun y hy ↦ by
    rw [hy.iteratedDeriv_eq n, iteratedDeriv_const])

/-- The indicator of a closed interval is locally constant away from its endpoints. -/
private theorem indicator_Icc_eventuallyEq_diagonalTendsto (a b y : ℝ) (ha : y ≠ a)
    (hb : y ≠ b) :
    (Icc a b).indicator (fun _ ↦ (1 : ℝ)) =ᶠ[𝓝 y]
      fun _ ↦ (Icc a b).indicator (fun _ ↦ (1 : ℝ)) y := by
  by_cases hy : y ∈ Icc a b
  · have hy' : y ∈ Ioo a b := ⟨lt_of_le_of_ne hy.1 (Ne.symm ha), lt_of_le_of_ne hy.2 hb⟩
    filter_upwards [isOpen_Ioo.mem_nhds hy'] with x hx
    rw [indicator_of_mem (Ioo_subset_Icc_self hx), indicator_of_mem hy]
  · filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hy] with x hx
    rw [indicator_of_notMem hx, indicator_of_notMem hy]

open scoped Pointwise in
/-- Paper: Theorem 9.3.3.5(3), (9.3.3.9), p. 429. Take G = ℝ_{>0}, the identity
module, Haar measure dt/t, mass one on the trivial kernel, base {0} and degree
zero. Let φ be the indicator of {1}, let Uₙ = [exp(−2⁻ⁿ), exp(2⁻ⁿ)],
and use the sharp cutoff of [Λ⁻¹, Λ] with ε = Λ⁻² for large Λ. The Haar kernel
is zero almost everywhere, since it is supported on the product diagonal,
so every average defining its smoothening vanishes. The asserted leading
term is 2 log Λ because φ(1) = 1. -/
theorem Printed.truncatedHardySobolevConvolution_diagonal_tendsto_false :
    ¬ Printed.truncatedHardySobolevConvolution_diagonal_tendsto := by
  intro h
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  have hm : IsModulation m := isModulation_id_hardySobolevTranslation
  let L : ℝ≥0ˣ → ℝ := fun x ↦ Real.log (x.val : ℝ)
  have hL : Measurable L :=
    Real.measurable_log.comp (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  have hLS (K : Set ℝ) (hK : MeasurableSet K) : MeasurableSet {t : ℝ≥0ˣ | L t ∈ K} :=
    hK.preimage hL
  have hpos (x : ℝ≥0ˣ) : (0 : ℝ) < (x.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt x)
  have hLmul (x y : ℝ≥0ˣ) : L (x * y⁻¹) = L x - L y := by
    change Real.log ((((x * y⁻¹ : ℝ≥0ˣ) : ℝ≥0)) : ℝ) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv,
      Real.log_mul (hpos x).ne' (inv_pos.mpr (hpos y)).ne', Real.log_inv]
    rfl
  let e : ℝ → ℝ≥0ˣ := fun x ↦ Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'
  have he : Continuous e := Units.continuous_iff.mpr
    ⟨continuous_real_toNNReal.comp Real.continuous_exp, by
      change Continuous fun x ↦ ((Real.exp x).toNNReal)⁻¹
      exact (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun x ↦ (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne'⟩
  have heL (t : ℝ≥0ˣ) : e (L t) = t := by
    refine Units.ext (NNReal.eq ?_)
    change ((Real.exp (Real.log (t.val : ℝ))).toNNReal : ℝ) = _
    rw [Real.exp_log (hpos t), Real.coe_toNNReal _ (NNReal.coe_nonneg _)]
  have he0 : e 0 = 1 := by
    refine Units.ext (NNReal.eq ?_)
    change ((Real.exp 0).toNNReal : ℝ) = 1
    simp
  -- The trivial kernel carries the Dirac mass.
  let K := m.toMonoidHom.ker
  have hK : Subsingleton K := ⟨fun a b ↦ Subtype.ext
    ((MonoidHom.mem_ker.mp a.2).trans (MonoidHom.mem_ker.mp b.2).symm)⟩
  let μ₁ : Measure K := Measure.dirac 1
  have hμ₁ : μ₁.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ _ ↦ measure_lt_top _ _
      map_mul_left_eq_self := fun g ↦ by
        change Measure.map _ (Measure.dirac 1) = Measure.dirac 1
        rw [Measure.map_dirac' Subsingleton.measurable, Subsingleton.elim (g * 1) 1]
      open_pos := fun U _ hne ↦ by
        obtain ⟨u, hu⟩ := hne
        rw [Subsingleton.elim u 1] at hu
        change Measure.dirac 1 U ≠ 0
        rw [Measure.dirac_apply_of_mem hu]
        exact one_ne_zero }
  have hμ : positiveRealHaar = (μ₁.prod positiveRealHaar).map
      (fun z : K × ℝ≥0ˣ ↦ z.1.val * ContinuousMonoidHom.id ℝ≥0ˣ z.2) := by
    have hf : (fun z : K × ℝ≥0ˣ ↦ z.1.val * ContinuousMonoidHom.id ℝ≥0ˣ z.2) = Prod.snd := by
      funext z
      rw [show z.1.val = 1 from MonoidHom.mem_ker.mp z.1.2, one_mul]
      rfl
    rw [hf, Measure.map_snd_prod, measure_univ, one_smul]
  -- The symbol is the indicator of the identity.
  let φ : ℝ≥0ˣ → ℂ := ({1} : Set ℝ≥0ˣ).indicator fun _ ↦ 1
  have hφm : AEMeasurable φ positiveRealHaar :=
    (measurable_const.indicator (measurableSet_singleton 1)).aemeasurable
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro isCompact_singleton fun x hx ↦ indicator_of_notMem hx _
  have hφb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C :=
    ⟨1, fun g ↦ (norm_indicator_le_norm_self _ _).trans (by simp)⟩
  -- The D′-sequence of logarithmic balls of radius 2⁻ⁿ.
  let r : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  have hr (n : ℕ) : 0 < r n := by positivity
  let U : ℕ → Set ℝ≥0ˣ := fun n ↦ {t | L t ∈ Icc (-r n) (r n)}
  have hUm (n : ℕ) : MeasurableSet (U n) := hLS _ measurableSet_Icc
  have hμU (n : ℕ) : positiveRealHaar (U n) = ENNReal.ofReal (2 * r n) := by
    rw [positiveRealHaar_logPreimage_hardySobolevTranslation _ measurableSet_Icc,
      Real.volume_Icc]
    ring_nf
  have hU1 (n : ℕ) : (1 : ℝ≥0ˣ) ∈ U n := by
    simp only [U, L, mem_ofPred_eq, Units.val_one, NNReal.coe_one, Real.log_one]
    exact ⟨by linarith [hr n], (hr n).le⟩
  have hUU (n : ℕ) : U n * (U n)⁻¹ ⊆ {t | L t ∈ Icc (-(2 * r n)) (2 * r n)} := by
    rintro t ⟨x, hx, y, hy, rfl⟩
    have hy' : L y⁻¹ ∈ Icc (-r n) (r n) := hy
    have hLy : L y⁻¹ = -L y := by
      change Real.log ((((y⁻¹ : ℝ≥0ˣ) : ℝ≥0)) : ℝ) = _
      rw [Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
    rw [hLy] at hy'
    show L (x * y) ∈ Icc (-(2 * r n)) (2 * r n)
    rw [show x * y = x * y⁻¹⁻¹ by rw [inv_inv], hLmul]
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy'
    constructor <;> linarith
  have hD : IsDPrimeSequence positiveRealHaar U := by
    unfold IsDPrimeSequence IsDSequence
    refine ⟨⟨fun n ↦ ⟨hU1 n, (hUm n).nullMeasurableSet, ?_, ?_⟩, ?_, 3, by norm_num, fun n ↦ ⟨?_, ?_⟩⟩, ?_⟩
    · rw [hμU]
      exact ENNReal.ofReal_pos.mpr (by linarith [hr n])
    · rw [hμU]
      exact ENNReal.ofReal_lt_top
    · intro a b hab t ht
      have : r b ≤ r a := pow_le_pow_of_le_one (by norm_num) (by norm_num) hab
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · refine lt_of_lt_of_le ?_ (measure_mono (fun t ht ↦ ⟨t, ht, 1, by simpa using hU1 n,
        mul_one t⟩ : U n ⊆ U n * (U n)⁻¹))
      rw [hμU]
      exact ENNReal.ofReal_pos.mpr (by linarith [hr n])
    · refine lt_of_le_of_lt (measure_mono (hUU n)) ?_
      rw [positiveRealHaar_logPreimage_hardySobolevTranslation _ measurableSet_Icc,
        Real.volume_Icc, hμU, ← ENNReal.ofReal_mul (by norm_num)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by nlinarith [hr n])).mpr (by nlinarith [hr n])
    · intro W hW
      have hW' : e ⁻¹' W ∈ 𝓝 (0 : ℝ) := he.continuousAt.preimage_mem_nhds (he0 ▸ hW)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hW'
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
      refine ⟨n, fun t ht ↦ ?_⟩
      rw [← heL t]
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hn⟩
  -- The sharp cutoffs of [Λ⁻¹, Λ] with width Λ⁻².
  let ε : ℝ → ℝ := fun Λ ↦ Λ⁻¹ ^ 2
  let q : ℝ → ℝ → ℝ := fun Λ ↦ (Icc Λ⁻¹ Λ).indicator fun _ ↦ 1
  let ρ : ℝ → ℝ≥0ˣ → ℝ := fun Λ x ↦ q Λ (x.val : ℝ)
  have hε : Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) := by
    refine tendsto_inv_atTop_zero.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Λ hΛ
    change Λ⁻¹ = Λ⁻¹ ^ 2 * Λ
    field_simp
  have hρ1 (x : ℝ≥0ˣ) : Tendsto (fun Λ ↦ ρ Λ x) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (x.val : ℝ), eventually_ge_atTop (x.val : ℝ)⁻¹]
      with Λ h1 h2
    have hΛ : 0 < Λ := lt_of_lt_of_le (inv_pos.mpr (hpos x)) h2
    exact (indicator_of_mem (show ((x : ℝ≥0) : ℝ) ∈ Icc Λ⁻¹ Λ from
      ⟨(inv_le_comm₀ hΛ (hpos x)).mpr h2, h1⟩) (fun _ ↦ (1 : ℝ))).symm
  have hcut : ∀ᶠ Λ in atTop, IsModulatedCutoff m Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ := by
    filter_upwards [eventually_ge_atTop 2] with Λ hΛ2
    have hΛ : 0 < Λ := by linarith
    have hu : 0 < Λ⁻¹ := inv_pos.mpr hΛ
    have hu2 : Λ⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hΛ (by norm_num)]
      linarith
    have huΛ : Λ⁻¹ < Λ := by linarith
    have hmem1 : (1 : ℝ) ∈ Icc Λ⁻¹ Λ := ⟨by linarith, by linarith⟩
    have hle (x : ℝ≥0ˣ) : ρ Λ x ≤ 1 := by
      change (Icc Λ⁻¹ Λ).indicator (fun _ ↦ (1 : ℝ)) _ ≤ 1
      by_cases hx : (x.val : ℝ) ∈ Icc Λ⁻¹ Λ
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]; norm_num
    have hnn (x : ℝ≥0ˣ) : 0 ≤ ρ Λ x :=
      indicator_nonneg (fun _ _ ↦ zero_le_one) _
    have hρ1' : ρ Λ 1 = 1 := by
      change (Icc Λ⁻¹ Λ).indicator (fun _ ↦ (1 : ℝ)) (((1 : ℝ≥0ˣ) : ℝ≥0) : ℝ) = 1
      rw [Units.val_one, NNReal.coe_one, indicator_of_mem hmem1]
    have hcontmod : Continuous fun x : ℝ≥0ˣ ↦ ((m x).val : ℝ) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    refine ⟨⟨hΛ, by positivity, by nlinarith, by nlinarith, hnn,
      fun x ↦ (abs_of_nonneg (hnn x)).trans_le (hle x), ?_, ?_, ?_, ?_, ?_⟩,
      by positivity, by nlinarith⟩
    · exact IsGreatest.csSup_eq ⟨⟨1, hρ1'⟩, forall_mem_range.mpr hle⟩
    · refine ⟨q Λ, {Λ⁻¹, Λ}, fun x ↦ rfl, ?_, ?_, ?_⟩
      · intro c hc
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
          mem_singleton_iff] at hc
        rcases hc with rfl | rfl
        · exact hu
        · exact hΛ
      · intro y hy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff, mem_insert_iff,
          mem_singleton_iff, not_or] at hy
        exact (contDiffAt_const.congr_of_eventuallyEq
          (indicator_Icc_eventuallyEq_diagonalTendsto _ _ y hy.2.1 hy.2.2)).contDiffWithinAt
      · intro c hc n
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        -- Below Λ⁻¹ and above Λ the cutoff is zero; between them it is one.
        have hlow : ∀ᶠ y in 𝓝[<] Λ⁻¹, q Λ =ᶠ[𝓝 y] fun _ ↦ 0 := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          filter_upwards [isOpen_Iio.mem_nhds hy] with x hx
          exact indicator_of_notMem (fun h : x ∈ Icc Λ⁻¹ Λ ↦ not_le.mpr (show x < Λ⁻¹ from hx) h.1) _
        have hhigh : ∀ᶠ y in 𝓝[>] Λ, q Λ =ᶠ[𝓝 y] fun _ ↦ 0 := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          filter_upwards [isOpen_Ioi.mem_nhds hy] with x hx
          exact indicator_of_notMem (fun h : x ∈ Icc Λ⁻¹ Λ ↦ not_le.mpr (show Λ < x from hx) h.2) _
        have hmid (c : ℝ) (hc : c ∈ Icc Λ⁻¹ Λ) (l : Filter ℝ) (hl : l ≤ 𝓝 c)
            (hl' : ∀ᶠ y in l, y ≠ c) (hside : ∀ᶠ y in l, Λ⁻¹ ≤ y ∧ y ≤ Λ) :
            ∀ᶠ y in l, q Λ =ᶠ[𝓝 y] fun _ ↦ 1 := by
          have h1 : ∀ᶠ y in l, y ∈ Ioo Λ⁻¹ Λ := by
            have hne : ∀ᶠ y in l, y ≠ Λ⁻¹ ∧ y ≠ Λ := by
              rcases eq_or_ne c Λ⁻¹ with rfl | hc1
              · filter_upwards [hl', hl (isOpen_Iio.mem_nhds huΛ)] with y h1 h2
                exact ⟨h1, (show y < Λ from h2).ne⟩
              · rcases eq_or_ne c Λ with hc2 | hc2
                · rw [hc2] at hl hl'
                  filter_upwards [hl', hl (isOpen_Ioi.mem_nhds huΛ)] with y h1 h2
                  exact ⟨(show Λ⁻¹ < y from h2).ne', h1⟩
                · filter_upwards [hl (isOpen_Ioo.mem_nhds
                    ⟨lt_of_le_of_ne hc.1 (Ne.symm hc1), lt_of_le_of_ne hc.2 hc2⟩)] with y hy
                  exact ⟨(show y ∈ Ioo Λ⁻¹ Λ from hy).1.ne', hy.2.ne⟩
            filter_upwards [hne, hside] with y h1 h2
            exact ⟨lt_of_le_of_ne h2.1 (Ne.symm h1.1), lt_of_le_of_ne h2.2 h1.2⟩
          filter_upwards [h1] with y hy
          filter_upwards [isOpen_Ioo.mem_nhds hy] with x hx
          exact indicator_of_mem (Ioo_subset_Icc_self hx) _
        rcases hc with hc | hc <;> rw [hc]
        · refine ⟨_, _, tendsto_iteratedDeriv_diagonalTendsto 0 hlow n,
            tendsto_iteratedDeriv_diagonalTendsto 1 (hmid Λ⁻¹ ⟨le_rfl, huΛ.le⟩ (𝓝[>] Λ⁻¹)
              nhdsWithin_le_nhds
              (eventually_nhdsWithin_of_forall fun y (hy : Λ⁻¹ < y) ↦ hy.ne') ?_) n⟩
          · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
              (isOpen_Iio.mem_nhds huΛ)] with y h1 h2
            exact ⟨(show Λ⁻¹ < y from h1).le, (show y < Λ from h2).le⟩
        · refine ⟨_, _, tendsto_iteratedDeriv_diagonalTendsto 1 (hmid Λ ⟨huΛ.le, le_rfl⟩ (𝓝[<] Λ)
              nhdsWithin_le_nhds
              (eventually_nhdsWithin_of_forall fun y (hy : y < Λ) ↦ hy.ne) ?_) n,
            tendsto_iteratedDeriv_diagonalTendsto 0 hhigh n⟩
          · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
              (isOpen_Ioi.mem_nhds huΛ)] with y h1 h2
            exact ⟨(show Λ⁻¹ < y from h2).le, (show y < Λ from h1).le⟩
    · intro x
      have hx := hpos x
      have key : (x.val : ℝ) ∈ Icc Λ⁻¹ Λ ↔ (x.val : ℝ)⁻¹ ∈ Icc Λ⁻¹ Λ :=
        ⟨fun h ↦ ⟨(inv_le_inv₀ hΛ hx).mpr h.2, (inv_le_comm₀ hΛ hx).mp h.1⟩,
          fun h ↦ ⟨(inv_le_comm₀ hΛ hx).mpr h.2, (inv_le_inv₀ hΛ hx).mp h.1⟩⟩
      change (Icc Λ⁻¹ Λ).indicator (fun _ ↦ (1 : ℝ)) (x.val : ℝ) =
        (Icc Λ⁻¹ Λ).indicator (fun _ ↦ (1 : ℝ)) (((x⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ)
      rw [Units.val_inv_eq_inv_val, NNReal.coe_inv]
      by_cases h : (x.val : ℝ) ∈ Icc Λ⁻¹ Λ
      · rw [indicator_of_mem h, indicator_of_mem (key.mp h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt key.mpr h)]
    · refine closure_minimal (fun x hx ↦ ?_) (isClosed_Icc.preimage hcontmod)
      by_contra hn
      exact hx (show (Icc Λ⁻¹ Λ).indicator (fun _ ↦ (1 : ℝ)) ((x : ℝ≥0) : ℝ) = 0 from
        indicator_of_notMem (show ((x : ℝ≥0) : ℝ) ∉ Icc Λ⁻¹ Λ from hn) _)
    · intro x hx
      have h1 : Λ⁻¹ + Λ⁻¹ ^ 2 ≤ ((x : ℝ≥0) : ℝ) := hx.1
      have h2 : ((x : ℝ≥0) : ℝ) ≤ Λ - Λ⁻¹ ^ 2 := hx.2
      exact indicator_of_mem (show ((x : ℝ≥0) : ℝ) ∈ Icc Λ⁻¹ Λ from
        ⟨by nlinarith [sq_nonneg Λ⁻¹], by nlinarith [sq_nonneg Λ⁻¹]⟩) _
  have hconcl := h ℝ≥0ˣ positiveRealHaar m hm surjective_id (ContinuousMonoidHom.id ℝ≥0ˣ)
    (fun _ ↦ rfl) μ₁ hμ φ hφm hφc hφb U hD hUm ε ρ hε hρ1 hcut
  -- The kernel lives on the diagonal, which is null for the product measure.
  have hdiag : (positiveRealHaar.prod positiveRealHaar) {p : ℝ≥0ˣ × ℝ≥0ˣ | p.1 * p.2⁻¹ = 1} = 0 := by
    have hDm : MeasurableSet {p : ℝ≥0ˣ × ℝ≥0ˣ | p.1 * p.2⁻¹ = 1} :=
      (measurableSet_singleton 1).preimage (measurable_fst.mul measurable_snd.inv)
    refine (Measure.measure_prod_null hDm).mpr (Eventually.of_forall fun x ↦ ?_)
    refine measure_mono_null (fun y (hy : x * y⁻¹ = 1) ↦ ?_)
      ((positiveRealHaar_logPreimage_hardySobolevTranslation {L x}
        (measurableSet_singleton _)).trans Real.volume_singleton)
    exact (congrArg L (mul_inv_eq_one.mp hy)).symm
  have hzero (Λ : ℝ) (x : ℝ≥0ˣ) : dSequenceKernelSmoothening positiveRealHaar U
      (fun p ↦ (ρ Λ p.1 : ℂ) * φ (p.1 * p.2⁻¹)) (x, x) = 0 := by
    refine dSequenceKernelSmoothening_eq_zero_diagonalTendsto _ _ _ ?_ _
    filter_upwards [compl_mem_ae_iff.mpr hdiag] with p hp
    have hp' : p.1 * p.2⁻¹ ∉ ({1} : Set ℝ≥0ˣ) := hp
    change _ * φ _ = 0
    rw [show φ (p.1 * p.2⁻¹) = 0 from indicator_of_notMem hp' _, mul_zero]
  have h2 := hconcl.2
  simp only [hzero, integral_zero, zero_sub] at h2
  have hre := (Complex.continuous_re.tendsto 0).comp h2
  have hμ₁ : μ₁.real univ = 1 := by simp [μ₁]
  have hφ1 : φ 1 = 1 := indicator_of_mem rfl _
  simp only [hμ₁, hφ1, Function.comp_def, mul_one, Complex.neg_re, Complex.ofReal_re,
    Complex.zero_re] at hre
  refine not_tendsto_nhds_of_tendsto_atBot ?_ 0 hre
  exact tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.const_mul_atTop two_pos)

end RiemannMasullo
