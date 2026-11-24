module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2b

/-! # The upper polar cusp of global adelic theta

After a half twist, subtracting the Fourier value at zero times the inverse square
root of the norm cancels the lower cusp. Riemann–Roch identifies the difference
exactly with the half-twisted Fourier theta at the inverse class if the original
test vanishes at the origin. The subtracted term supplies a genuine upper cusp.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing Topology

namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "𝓑" => SchwartzBruhat (Multiplicative 𝔸)
local notation "𝟎ₐ" => Multiplicative.ofAdd (0 : 𝔸)
local notation "q(" g ")" => (((ideleClassNorm F g).val : ℝ))
local notation "p(" f ")" => adeleSchwartzFourier f 𝟎ₐ

/-- Adelic theta on the centered line with the positive square root of the idele norm. -/
def halfTwistedAdelicTheta (f : 𝓑) (g : C𝔽) : ℂ :=
  Real.sqrt q(g) • adelicTheta f g

/-- The global compensation subtracts the lower polar character at every idele class. -/
def compensatedAdelicTheta (f : 𝓑) (g : C𝔽) : ℂ :=
  halfTwistedAdelicTheta f g - (Real.sqrt q(g))⁻¹ • p(f)

private theorem norm_pos (g : C𝔽) : 0 < q(g) := NNReal.coe_pos.mpr (Units.zero_lt _)

private theorem sqrt_mul_inv {r : ℝ} (hr : 0 < r) : Real.sqrt r * r⁻¹ = (Real.sqrt r)⁻¹ := by
  field_simp [hr.ne', (Real.sqrt_pos.mpr hr).ne']
  nlinarith [Real.sq_sqrt hr.le]

/-- Paper: Theorem 2.2.3.2, p. 82. The global half-twisted function after compensation
is the half-twisted Fourier theta at the inverse class when the test vanishes at zero.
Deviation: Apply the half twist to the printed equality (2.2.3.2) and assume origin vanishing. -/
theorem adelicTheta_halfTwist_poisson (f : 𝓑) (hf : f 𝟎ₐ = 0) (g : C𝔽) :
    compensatedAdelicTheta f g = halfTwistedAdelicTheta (adeleSchwartzFourier f) g⁻¹ := by
  rw [compensatedAdelicTheta, halfTwistedAdelicTheta, adelicTheta_riemannRoch, hf,
    sub_zero, smul_add, ← mul_smul, ← mul_smul, sqrt_mul_inv (norm_pos g), add_sub_cancel_right]
  simp [halfTwistedAdelicTheta, Units.val_inv_eq_inv_val, Real.sqrt_inv]

/-- Under left translation the coefficient of the polar character is multiplied by the
positive square root of the translating norm. The matching dilation difference therefore
has exactly the same value before and after compensation. -/
theorem compensatedAdelicTheta_dilation_difference (f : 𝓑) (u g : C𝔽) :
    compensatedAdelicTheta f (u⁻¹ * g) - Real.sqrt q(u) • compensatedAdelicTheta f g =
      halfTwistedAdelicTheta f (u⁻¹ * g) - Real.sqrt q(u) • halfTwistedAdelicTheta f g := by
  have hq : q(u⁻¹ * g) = q(u)⁻¹ * q(g) := by
    simp [Units.val_mul, Units.val_inv_eq_inv_val]
  simp only [compensatedAdelicTheta, hq, Real.sqrt_mul (inv_nonneg.mpr (norm_pos u).le),
    Real.sqrt_inv, mul_inv, inv_inv, smul_sub, ← mul_smul]
  abel

private theorem theta_translate (v : IdeleGroup (𝓞 F) F) (f : 𝓑) (g : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate v f) g =
      adelicTheta f ((QuotientGroup.mk v)⁻¹ * g) := by
  induction g using QuotientGroup.induction_on with
  | H x =>
    change _ = adelicTheta f (QuotientGroup.mk (v⁻¹ * x))
    rw [adelicTheta_mk (schwartzBruhatUnitTranslate v f) x, adelicTheta_mk f (v⁻¹ * x)]
    exact tsum_congr fun ξ ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
      (mul_left_comm v.inv (algebraMap F 𝔸 (ξ : F)) x.val)

open MeasureTheory in
open scoped ENNReal in
private theorem fourier_zero_translate (v : IdeleGroup (𝓞 F) F) (f : 𝓑) :
    p(schwartzBruhatUnitTranslate v f) = q(QuotientGroup.mk v) • p(f) := by
  let : MeasurableSpace 𝔸 := borel _
  let : BorelSpace 𝔸 := ⟨rfl⟩
  let μ := additiveTamagawaMeasure F
  have : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let d := (Homeomorph.smul (α := 𝔸) v⁻¹).toMeasurableEquiv
  have hmap : μ.map d = ((ideleNorm F v).val : ℝ≥0∞) • μ := by
    ext s hs
    rw [Measure.map_apply d.measurable hs]
    change μ ((fun x : 𝔸 ↦ v⁻¹ • x) ⁻¹' s) = ((ideleNorm F v).val : ℝ≥0∞) * μ s
    rw [Set.preimage_smul_inv]
    exact adeleHaar_mul_image F μ v s hs
  rw [(adeleSchwartzFourier_apply_zero _).2, (adeleSchwartzFourier_apply_zero f).2]
  change (∫ x, f (Multiplicative.ofAdd (d x)) ∂μ) = _
  rw [← integral_map_equiv d (fun x ↦ f (Multiplicative.ofAdd x)), hmap, integral_smul_measure,
    ENNReal.coe_toReal]
  rfl

/-- The dilation difference of a compensated, origin-vanishing theta is itself
the half-twisted theta of a test with both polar values zero. -/
theorem exists_polarFree_dilation_difference (f : 𝓑) (hf : f 𝟎ₐ = 0) (u : C𝔽) :
    ∃ f₀ : adelePolarSubspace F, ∀ g : C𝔽,
      compensatedAdelicTheta f (u⁻¹ * g) - Real.sqrt q(u) • compensatedAdelicTheta f g =
        halfTwistedAdelicTheta f₀.val g := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
  let u : C𝔽 := QuotientGroup.mk v
  let a := Real.sqrt q(u)
  let f' := schwartzBruhatUnitTranslate v f
  let d : 𝓑 := (↑(a⁻¹) : ℂ) • f' - (↑a : ℂ) • f
  have ht : p(f') = q(u) • p(f) := fourier_zero_translate v f
  have h₀ : f' 𝟎ₐ = 0 := by
    change f (Multiplicative.ofAdd ((↑v⁻¹ : 𝔸) * 0)) = 0
    rw [mul_zero]
    exact hf
  have hsq : a⁻¹ * q(u) = a := by
    rw [← Real.mul_self_sqrt (norm_pos u).le, ← mul_assoc, inv_mul_cancel₀
      (Real.sqrt_pos.mpr (norm_pos u)).ne', one_mul]
  have hd : d ∈ adelePolarSubspace F := by
    apply LinearMap.mem_ker.mpr
    simp only [d, map_sub, map_smul, adelePolarValues_apply, ht, h₀, hf, Prod.smul_mk,
      sub_self, Complex.real_smul, smul_eq_mul, mul_zero, ← mul_assoc,
      ← Complex.ofReal_mul, hsq]
  refine ⟨⟨d, hd⟩, fun g ↦ ?_⟩
  rw [compensatedAdelicTheta_dilation_difference]
  have hq : q(u⁻¹ * g) = q(u)⁻¹ * q(g) := by simp [Units.val_mul, Units.val_inv_eq_inv_val]
  have htheta := adelicTheta_isLinear (F := F)
  have he := DFunLike.congr_fun (htheta.map_sub ((↑(a⁻¹) : ℂ) • f') ((↑a : ℂ) • f)) g
  have hdtheta : adelicTheta d g =
      a⁻¹ • adelicTheta f (u⁻¹ * g) - a • adelicTheta f g := by
    simpa only [htheta.map_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      f', theta_translate, Complex.real_smul, smul_eq_mul] using he
  change halfTwistedAdelicTheta f (u⁻¹ * g) - a • halfTwistedAdelicTheta f g =
    halfTwistedAdelicTheta d g
  simp only [halfTwistedAdelicTheta, hq, Real.sqrt_mul (inv_nonneg.mpr (norm_pos u).le),
    Real.sqrt_inv, hdtheta, smul_sub, ← mul_smul, a]
  rw [mul_comm (Real.sqrt q(u))⁻¹ (Real.sqrt q(g)), mul_comm (Real.sqrt q(u)) (Real.sqrt q(g))]

/-- After origin vanishing, the compensated lower tail and the upper remainder after
removing its polar character both decay to every order, uniformly in the idele class. -/
theorem compensatedAdelicTheta_polar_bounds (f : 𝓑) (hf : f 𝟎ₐ = 0) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : C𝔽,
      (q(g) < 1 → ‖compensatedAdelicTheta f g‖ ≤ C * Real.sqrt q(g) * q(g) ^ N) ∧
      (1 < q(g) → ‖compensatedAdelicTheta f g + (Real.sqrt q(g))⁻¹ • p(f)‖ ≤
        C * (Real.sqrt q(g))⁻¹ * (q(g) ^ N)⁻¹) := by
  obtain ⟨C, hC, hb⟩ := adelicTheta_decay_bounded_threshold_one {f}
    (Bornology.isVonNBounded_singleton (𝕜 := ℂ) f) (N + 1)
  refine ⟨C, hC, fun g ↦ ?_⟩
  have hpos := norm_pos g
  have hs := Real.sqrt_nonneg q(g)
  have h := hb f (Set.mem_singleton f) g
  constructor
  · intro hg
    have hlo := h.2.1 hg
    rw [hf, add_zero] at hlo
    have he : compensatedAdelicTheta f g =
        Real.sqrt q(g) • (adelicTheta f g - q(g)⁻¹ • p(f)) := by
      rw [compensatedAdelicTheta, halfTwistedAdelicTheta, smul_sub, ← mul_smul, sqrt_mul_inv hpos]
    rw [he, norm_smul, Real.norm_of_nonneg hs]
    calc
      _ ≤ Real.sqrt q(g) * (C * q(g) ^ (N + 1)) := mul_le_mul_of_nonneg_left hlo hs
      _ ≤ Real.sqrt q(g) * (C * q(g) ^ N) := by
        apply mul_le_mul_of_nonneg_left _ hs
        apply mul_le_mul_of_nonneg_left _ hC.le
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hpos.le N) hg.le
      _ = _ := by ring
  · intro hg
    rw [compensatedAdelicTheta, sub_add_cancel, halfTwistedAdelicTheta, norm_smul,
      Real.norm_of_nonneg hs]
    calc
      _ ≤ Real.sqrt q(g) * (C * (q(g) ^ (N + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left (h.1 hg) hs
      _ = _ := by rw [pow_succ, mul_inv, ← sqrt_mul_inv hpos]; ring

/-- Multiplication by the square root of the idele norm normalizes the leading upper
term to minus the Fourier value at zero, uniformly over all classes with large norm. -/
theorem compensatedAdelicTheta_upper_coefficient (f : 𝓑) :
    Tendsto (fun g : C𝔽 ↦ Real.sqrt q(g) • compensatedAdelicTheta f g)
      (comap (fun g : C𝔽 ↦ q(g)) atTop) (𝓝 (-p(f))) := by
  let l := comap (fun g : C𝔽 ↦ q(g)) atTop
  have hn : Tendsto (fun g : C𝔽 ↦ q(g)) l atTop := tendsto_comap
  obtain ⟨C, T, _, _, hb⟩ := adelicTheta_decay_large f 2
  have hz : Tendsto (fun g : C𝔽 ↦ q(g) • adelicTheta f g) l (𝓝 0) := by
    have hlim : Tendsto (fun g : C𝔽 ↦ C * q(g)⁻¹) l (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hn).const_mul C
    apply squeeze_zero_norm' _ hlim
    filter_upwards [hn.eventually (eventually_gt_atTop T)] with g hg
    rw [norm_smul, Real.norm_of_nonneg (norm_pos g).le]
    calc
      _ ≤ q(g) * (C * (q(g) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hb g hg) (norm_pos g).le
      _ = C * q(g)⁻¹ := by field_simp [(norm_pos g).ne']
  have he (g : C𝔽) : Real.sqrt q(g) • compensatedAdelicTheta f g =
      q(g) • adelicTheta f g - p(f) := by
    simp only [compensatedAdelicTheta, halfTwistedAdelicTheta, smul_sub, ← mul_smul,
      Real.mul_self_sqrt (norm_pos g).le, mul_inv_cancel₀ (Real.sqrt_pos.mpr (norm_pos g)).ne', one_smul]
  simp_rw [he]
  simpa using hz.sub_const p(f)

/-- The upper threshold coefficient vanishes exactly on the Fourier polar hyperplane.
Surjectivity of the norm ensures that the limit tests actual idele classes arbitrarily
far out in the upper cusp. -/
theorem compensatedAdelicTheta_upper_zero_iff (f : 𝓑) :
    Tendsto (fun g : C𝔽 ↦ Real.sqrt q(g) • compensatedAdelicTheta f g)
      (comap (fun g : C𝔽 ↦ q(g)) atTop) (𝓝 0) ↔ p(f) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  have hn : (comap (fun g : C𝔽 ↦ q(g)) atTop).NeBot := by
    apply comap_neBot_iff_frequently.2
    apply Eventually.frequently
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    let r : NNRealˣ := Units.mk0 (⟨t, ht.le⟩ : NNReal)
      (fun hz ↦ ht.ne' (congrArg (fun x : NNReal ↦ (x : ℝ)) hz))
    obtain ⟨g, hg⟩ := hsurj r
    exact ⟨g, congrArg (fun x : NNRealˣ ↦ (x.val : ℝ)) hg⟩
  have h := compensatedAdelicTheta_upper_coefficient f
  constructor
  · exact fun hz ↦ neg_eq_zero.mp (tendsto_nhds_unique h hz)
  · intro hz
    simpa only [hz, neg_zero] using h

variable (F) in
/-- Every number field admits an origin-vanishing global adelic test with upper polar
coefficient exactly minus one. This fixes the scale of the actual Poisson cusp. -/
theorem exists_adelicTheta_unit_polar_cusp :
    ∃ f : 𝓑, f 𝟎ₐ = 0 ∧ p(f) = 1 ∧
      Tendsto (fun g : C𝔽 ↦ Real.sqrt q(g) • compensatedAdelicTheta f g)
        (comap (fun g : C𝔽 ↦ q(g)) atTop) (𝓝 (-1)) := by
  obtain ⟨f, hf⟩ := adelePolarValues_surjective (F := F) (0, 1)
  have h₀ : f 𝟎ₐ = 0 := congrArg Prod.fst hf
  have h₁ : p(f) = 1 := congrArg Prod.snd hf
  exact ⟨f, h₀, h₁, h₁ ▸ compensatedAdelicTheta_upper_coefficient f⟩

end RiemannMasullo.StripNuclearity
