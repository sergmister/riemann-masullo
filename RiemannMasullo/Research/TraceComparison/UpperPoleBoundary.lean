module

public import RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# The upper polar coefficient at the global theta boundary

This file concerns the proposed comparison in §12.3, pp. 514 and 520.
In an enlarged space a theta function has an ordinary strip component and the
coefficient of the profile `x ↦ x^(-1/2)`. Dilation contracts the ordinary
component when normalized to preserve the coefficient. The resulting closure
splits at each invariant test level. The passage to a geometric trace still
requires the comparison of the regular parts.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace RiemannMasullo.StripNuclearity

section Strip

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
  (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)

set_option quotPrecheck false in
local notation "logNorm" => (fun g : G ↦ Real.log ((m g).val : ℝ))
local notation "τ" => hardySobolevTranslation μ m a b s hab hs

/-- Paper: Lemma 9.3.1.5, p. 421, applied to the missing comparison on p. 520.
On a strip with upper endpoint below one half the translated regular part tends
to zero in operator norm when scaled so the upper polar coefficient stays fixed.
Deviation: This is an estimate for a proposed boundary extension. -/
theorem upperPole_normalized_translation_tendsto (hb : b < 1/2)
    {ι : Type*} {l : Filter ι} (g : ι → G) (hg : Tendsto (fun i ↦ logNorm (g i)) l atTop) :
    Tendsto (fun i ↦ (Real.exp (-(logNorm (g i))/2) : ℂ) • τ (g i)) l (𝓝 0) := by
  let q := (1/2 : ℝ) - b
  have hq : 0 < q := sub_pos.mpr hb
  have hshift : Tendsto (fun i ↦ 1 + logNorm (g i)) l atTop := tendsto_const_nhds.add_atTop hg
  have hcalc := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s/2) q hq).comp hshift).const_mul
    (Real.exp q)
  have hlim : Tendsto (fun i ↦ Real.exp q * ((1 + logNorm (g i)) ^ (s/2) *
      Real.exp (-q * (1 + logNorm (g i))))) l (𝓝 0) := by simpa [Function.comp_def] using hcalc
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ hlim
  filter_upwards [hg.eventually_ge_atTop 0] with i hi
  have h := norm_hardySobolevTranslation_le μ m a b s hab hs (g i)
  rw [abs_of_nonneg hi, max_eq_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hi))] at h
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq ?_
  rw [← mul_assoc, ← Real.exp_add, mul_comm _ (Real.exp _), ← mul_assoc, ← Real.exp_add]
  dsimp [q]
  ring_nf

end Strip

section PolarClosure

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The regular components of members of a space of pairs whose upper polar
coefficient is zero. -/
def zeroUpperPolePart (U : Submodule ℂ (H × ℂ)) : Submodule ℂ H :=
  U.comap (LinearMap.inl ℂ H ℂ)

/-- A sequence in the given test space with unit upper polar coefficient and
vanishing regular parts splits its closure as the closed polar-free part times
the full coefficient line. The approximants retain coefficient one exactly. -/
theorem closure_eq_prod_of_upperPole_sequence (U : Submodule ℂ (H × ℂ))
    (u : ℕ → H) (hu : ∀ n, (u n, (1 : ℂ)) ∈ U) (hlim : Tendsto u atTop (𝓝 0)) :
    U.topologicalClosure = (zeroUpperPolePart U).topologicalClosure.prod ⊤ := by
  let S := (zeroUpperPolePart U).topologicalClosure
  have hclosed : IsClosed (S.prod (⊤ : Submodule ℂ ℂ) : Set (H × ℂ)) :=
    (zeroUpperPolePart U).isClosed_topologicalClosure.prod isClosed_univ
  apply le_antisymm
  · apply U.topologicalClosure_minimal _ hclosed
    rintro ⟨x,c⟩ hx
    refine ⟨?_, Submodule.mem_top⟩
    have hzero (n : ℕ) : x - c • u n ∈ zeroUpperPolePart U := by
      change (x - c • u n, 0) ∈ U
      simpa using U.sub_mem hx (U.smul_mem c (hu n))
    apply (zeroUpperPolePart U).isClosed_topologicalClosure.mem_of_tendsto
      (show Tendsto (fun n ↦ x - c • u n) atTop (𝓝 x) by
        simpa using (tendsto_const_nhds.sub (hlim.const_smul c)))
    exact Eventually.of_forall fun n ↦ (zeroUpperPolePart U).le_topologicalClosure (hzero n)
  · have haxis : ((0 : H), (1 : ℂ)) ∈ U.topologicalClosure :=
      U.isClosed_topologicalClosure.mem_of_tendsto (hlim.prodMk_nhds tendsto_const_nhds)
        (Eventually.of_forall fun n ↦ U.le_topologicalClosure (hu n))
    have hreg : S ≤ zeroUpperPolePart U.topologicalClosure := by
      refine (zeroUpperPolePart U).topologicalClosure_minimal ?_ ?_
      · intro x hx
        exact U.le_topologicalClosure hx
      · exact U.isClosed_topologicalClosure.preimage (continuous_id.prodMk continuous_const)
    rintro ⟨x,c⟩ ⟨hx,-⟩
    have hpair : (x, (0 : ℂ)) ∈ U.topologicalClosure := hreg hx
    simpa using U.topologicalClosure.add_mem hpair (U.topologicalClosure.smul_mem c haxis)

end PolarClosure

section StripClosure

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)
  (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)

set_option quotPrecheck false in
local notation "logNorm" => (fun g : G ↦ Real.log ((m g).val : ℝ))
local notation "W" => CompactIntervalSobolev μ logNorm a b s
local notation "τ" => hardySobolevTranslation μ m a b s hab hs

/-- Paper: §12.3, p. 514 and its use on p. 520. In the proposed extension by
the upper asymptotic coefficient, the coefficient line splits off the closure
of every dilation-invariant test level that realizes coefficient one.
Deviation: The completion of pairs records a boundary value outside the strip. -/
theorem strip_upperPoleClosure_eq_prod (hb : b < 1/2) (U : Submodule ℂ (W × ℂ))
    (v : W) (hv : (v, (1:ℂ)) ∈ U) (g : G) (hg : 0 < logNorm g)
    (hU : ∀ p : W × ℂ, p ∈ U →
      (τ g p.1, (Real.exp (logNorm g / 2) : ℂ) * p.2) ∈ U) :
    U.topologicalClosure = (zeroUpperPolePart U).topologicalClosure.prod ⊤ := by
  let t := logNorm g
  have hlog (n : ℕ) : logNorm (g^n) = (n:ℝ)*t := by
    simp [t, map_pow, Real.log_pow]
  have hpow (n : ℕ) : (τ (g^n) v, (Real.exp ((n:ℝ)*t/2) : ℂ)) ∈ U := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      have H := hU _ ih
      rw [pow_succ', map_mul, Nat.cast_succ,
        show ((n:ℝ)+1)*t/2 = t/2+(n:ℝ)*t/2 by ring, Real.exp_add, Complex.ofReal_mul]
      exact H
  have ht : Tendsto (fun n : ℕ ↦ logNorm (g^n)) atTop atTop := by
    simp_rw [hlog]
    exact (tendsto_id.atTop_mul_const hg).comp tendsto_natCast_atTop_atTop
  let T := fun n : ℕ ↦ (Real.exp (-(logNorm (g^n))/2) : ℂ) • τ (g^n)
  have hT : Tendsto T atTop (𝓝 0) :=
    upperPole_normalized_translation_tendsto μ m a b s hab hs hb _ ht
  apply closure_eq_prod_of_upperPole_sequence U (fun n ↦ T n v)
  · intro n
    have H := U.smul_mem (Real.exp (-((n:ℝ)*t)/2) : ℂ) (hpow n)
    have hone : Real.exp (-((n:ℝ)*t)/2) * Real.exp ((n:ℝ)*t/2) = 1 := by
      rw [← Real.exp_add, show -((n:ℝ)*t)/2+(n:ℝ)*t/2=0 by ring, Real.exp_zero]
    simpa only [T, hlog, smul_apply, Prod.smul_mk, smul_eq_mul,
      ← Complex.ofReal_mul, hone, Complex.ofReal_one] using H
  · exact ((ContinuousLinearMap.apply ℂ W v).continuous.tendsto (0 : W →L[ℂ] W)).comp hT

end StripClosure


section LogConvolution

/-- In log norm, the polar character is an eigenfunction of physical convolution.
The cutoff's value at the observed point multiplies the positive half-Mellin moment. -/
theorem normalized_upperPole_cutoff_convolution (φ ρ : ℝ → ℂ) (t : ℝ) :
    (Real.exp (t / 2) : ℂ) * (ρ t * ∫ v : ℝ, φ v * (Real.exp (-(t-v)/2) : ℂ)) =
      ρ t * ∫ v : ℝ, φ v * (Real.exp (v/2) : ℂ) := by
  have he (v : ℝ) : (Real.exp (-(t-v)/2) : ℂ) =
      (Real.exp (v/2) : ℂ) * (Real.exp (-t/2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show -(t-v)/2=v/2+ -t/2 by ring]
  simp_rw [he, ← mul_assoc]
  rw [integral_mul_const]
  have hc : (Real.exp (t/2) : ℂ) * (Real.exp (-t/2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show t/2+ -t/2=0 by ring, Real.exp_zero,
      Complex.ofReal_one]
  linear_combination (ρ t * (∫ v : ℝ, φ v * (Real.exp (v/2) : ℂ))) * hc

/-- The lower-end value of a spatial cutoff determines its action on the polar
coefficient. This covers upper-only cutoffs (value one) and annuli (value zero). -/
theorem upperPole_cutoff_convolution_limit (φ ρ : ℝ → ℂ) {c : ℂ}
    (hρ : Tendsto ρ atBot (𝓝 c)) :
    Tendsto (fun t : ℝ ↦ (Real.exp (t/2) : ℂ) *
      (ρ t * ∫ v : ℝ, φ v * (Real.exp (-(t-v)/2) : ℂ))) atBot
      (𝓝 (c * ∫ v : ℝ, φ v * (Real.exp (v/2) : ℂ))) := by
  simpa only [normalized_upperPole_cutoff_convolution] using
    hρ.mul_const (∫ v : ℝ, φ v * (Real.exp (v/2) : ℂ))

end LogConvolution

end RiemannMasullo.StripNuclearity
