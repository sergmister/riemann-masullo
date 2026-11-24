module

public import RiemannMasullo.Research.PositiveStrip.Compatibility
public import RiemannMasullo.Research.PositiveStrip.SingleGenerator
import all RiemannMasullo.Research.PositiveStrip.SingleGenerator

@[expose] public noncomputable section

open Filter Function MeasureTheory Metric NumberField Set
open scoped Topology NNReal NumberField.AdeleRing

namespace RiemannMasullo.StripDual

set_option quotPrecheck false

private theorem choose_tail_widths (A r : ℝ) (hr : 0 < r) :
    ∃ k c : ℝ, 0 < k ∧ k < c ∧ k*(|0-A|+r) < Real.pi/2 ∧ c*r < Real.pi/2 := by
  let d := |0-A|+r
  have hd : 0 < d := add_pos_of_nonneg_of_pos (abs_nonneg _) hr
  let k := (Real.pi/2)/(d+1)
  have hk : 0 < k := by dsimp [k]; positivity
  have he : k*(d+1) = Real.pi/2 := div_mul_cancel₀ _ (by positivity)
  have hkd : k*d < Real.pi/2 := by nlinarith
  have hkr : k*r < Real.pi/2 := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _)) hk.le).trans_lt hkd
  obtain ⟨c,hc,hrc⟩ := stripReciprocal_exists_frequency k r hr.le hkr
  exact ⟨k,c,hk,hc,hkd,hrc⟩

/-- All zeros of a nonzero bounded strip generator can be exhausted by a
sequence of finite sets. The complementary products are contractive on the
smaller strip and tend pointwise to one. -/
private theorem single_generator_divisor_sequence (A k r : ℝ) (hk : 0 < k) (_hr : 0 < r)
    (hwide : k*(|0-A|+r) < Real.pi/2) (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hG₀ : G (A:ℂ) ≠ 0) (M : ℝ) (hb : ∀ z : ℂ, |z.re-A| < (Real.pi/2)/k → ‖G z‖ ≤ M) :
    let D := synthesis_stripBlaschkeFromDisk (A:ℂ) k
    let B := synthesis_stripBlaschkeToDisk (A:ℂ) k
    let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
    let m (i : Z) := analyticOrderNatAt G (D i.val)
    let J := Ioo (-r) r
    ∃ S : ℕ → Finset Z, (∀ i : Z, 0 < m i ∧ analyticOrderAt G (D i.val) = m i) ∧
      let b (n : ℕ) (z : ℂ) := DiskTails.diskBlaschkeTail (fun i : Z ↦ i.val) m (S n) (B z)
      (∀ n, AnalyticOnNhd ℂ (b n) (Complex.re ⁻¹' J)) ∧
      (∀ n z, z.re ∈ J → ‖b n z‖ ≤ 1) ∧ (∀ z, z.re ∈ J → Tendsto (fun n ↦ b n z) atTop (𝓝 1)) := by
  intro D B Z m J
  classical
  let g := G ∘ D
  let p (i : Z) := i.val
  have hD (z : ℂ) (hz : z ∈ ball 0 1) : |(D z).re-A| < (Real.pi/2)/k := synthesis_stripBlaschkeFromDisk_mem hk hz
  have hg : AnalyticOnNhd ℂ g (ball 0 1) := fun z hz ↦ (hG.analyticAt _).comp
    (synthesis_stripBlaschkeFromDisk_analytic_deriv hk hz).1
  have hg₀ : g 0 ≠ 0 := by simpa [g,D,synthesis_stripBlaschkeFromDisk] using hG₀
  have hp (i : Z) : p i ≠ 0 := by
    intro h
    have hi : g (p i) = 0 := i.property.2
    rw [h] at hi
    exact hg₀ hi
  have hpn (i : Z) : ‖p i‖ < 1 := mem_ball_zero_iff.mp i.property.1
  have hm (i : Z) : analyticOrderAt G (D i.val) = m i := by
    have hfin := (show AnalyticOnNhd ℂ G univ from fun z _ ↦ hG.analyticAt z).analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := (A:ℂ)) (mem_univ _) (mem_univ (D i.val))
      (by rw [(hG.analyticAt _).analyticOrderAt_eq_zero.mpr hG₀]; simp)
    exact (Nat.cast_analyticOrderNatAt hfin).symm
  have hmpos (i : Z) : 0 < m i := by
    apply Nat.pos_of_ne_zero
    exact fun h ↦ ((hG.analyticAt _).analyticOrderAt_ne_zero.mpr i.property.2) (by rw [hm,h,Nat.cast_zero])
  have hsum : Summable (fun i : Z ↦ (m i : ℝ)*(1-‖p i‖)) := by
    have H := (synthesis_disk_divisor_summable_one_sub_norm hg hg₀ (fun z hz ↦ hb _ (hD z hz))).subtype
      (fun z ↦ z ∈ ball (0:ℂ) 1 ∧ G (D z) = 0)
    apply H.congr
    intro i
    have h := synthesis_stripBlaschkeFromDisk_analytic_deriv (w₀ := (A:ℂ)) hk i.property.1
    have hc : analyticOrderAt g i.val = analyticOrderAt G (D i.val) := analyticOrderAt_comp_of_deriv_ne_zero h.1 h.2
    change (MeromorphicOn.divisor g (ball 0 1) i.val : ℝ)*(1-‖i.val‖) = _
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hg i.property.1,hc,hm]
    simp [p]
  let : Countable Z := Set.countable_univ_iff.mp (hsum.countable_support.mono fun i _ ↦
    mul_ne_zero (Nat.cast_ne_zero.mpr (hmpos i).ne') (sub_pos.mpr (hpn i)).ne')
  obtain ⟨S,hS⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset Z))
  refine ⟨S, fun i ↦ ⟨hmpos i,hm i⟩,?_⟩
  let T (n : ℕ) := DiskTails.diskBlaschkeTail p m (S n)
  have hTa (n) : AnalyticOnNhd ℂ (T n) (ball 0 1) := DiskTails.product_analytic
    (fun i : {j // j ∉ S n} ↦ p i.val) (fun i ↦ m i.val) (fun i ↦ hp _) (fun i ↦ hpn _) (hsum.subtype _)
  have hTb (n) (z : ℂ) (hz : ‖z‖ < 1) : ‖T n z‖ ≤ 1 := (DiskTails.product_bound
    (fun i : {j // j ∉ S n} ↦ p i.val) (fun i ↦ m i.val) (fun i ↦ hp _) (fun i ↦ hpn _) (hsum.subtype _) _ hz).1
  have hw (z : ℂ) (hz : z.re ∈ J) : |z.re-A| < (Real.pi/2)/k := by
    have h := abs_lt.mpr hz
    have hbound : |z.re-A| ≤ |0-A|+r := by
      rw [zero_sub,abs_neg]
      linarith [abs_sub z.re A]
    exact (lt_div_iff₀ hk).mpr (by nlinarith [mul_le_mul_of_nonneg_left hbound hk.le])
  have hB (z : ℂ) (hz : z.re ∈ J) : B z ∈ ball 0 1 := synthesis_stripBlaschkeToDisk_mem hk (hw z hz)
  refine ⟨fun n z hz ↦ (hTa n _ (hB z hz)).comp (synthesis_stripBlaschkeToDisk_analytic hk (hw z hz)),
    fun n z hz ↦ hTb n _ (mem_ball_zero_iff.mp (hB z hz)),fun z hz ↦ ?_⟩
  exact (DiskTails.diskBlaschkeTail_tendsto p m hp hpn hsum (mem_ball_zero_iff.mp (hB z hz))).comp hS

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s

/-- A fixed polar-free Hecke generator supplies a strongly convergent sequence
of contractive strip symbols. Every symbol times an entire test killing the
specified finite divisor lifts into the closed theta space; all tests retain
the actual inverse Mellin formula. -/
theorem exists_single_generator_tail_family (χ : PontryaginDual C𝔽) (a α s β r : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : 2*α+s < 2*β) (hβr : β < r)
    (e : Tests →ₗ[ℂ] SE α s) (he : ∀ H, (e H : ℝ → ℂ) =ᵐ[volume] (ME.symm H).val)
    (L : SE α s →L[ℂ] W(-α, α, s)) (hL : ∀ u, (L u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹*u (logNorm x)) :
    ∃ (f : adelePolarSubspace F) (b : ℕ → ℂ → ℂ) (U : ℕ → SE α s →L[ℂ] SE α s)
      (S : ℕ → Finset ℂ) (m : (n : ℕ) → S n → ℕ),
      let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+z))
      let J := Ioo (-r) r
      Differentiable ℂ G ∧ (∀ l h : ℝ, l ≤ h → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc l h → ‖G z‖ ≤ C) ∧
      G ((2-a : ℝ) : ℂ) ≠ 0 ∧ (∀ n w, 0 < m n w) ∧ (∀ n w, analyticOrderAt G w.val = m n w) ∧
      (∀ n, AnalyticOnNhd ℂ (b n) (Complex.re ⁻¹' J)) ∧ (∀ n z, z.re ∈ J → ‖b n z‖ ≤ 1) ∧
      (∀ z, z.re ∈ J → Tendsto (fun n ↦ b n z) atTop (𝓝 1)) ∧
      (∀ y, Tendsto (fun n ↦ U n y) atTop (𝓝 y)) ∧
      (∀ n H, ∃ q : PositiveRealExponentialDecay J, (U n (e H) : ℝ → ℂ) =ᵐ[volume] q.val ∧
        ∀ z, z.re ∈ J → mellin (fun t ↦ q.val (Real.log t)) z = b n z*H.val z) ∧
      ∀ n (H : Tests), (∀ (w : S n) j, j < m n w → iteratedDeriv j H.val w.val = 0) →
        L (U n (e H)) ∈ globalThetaSobolev F a (neg_le_self hα) hs := by
  classical
  obtain ⟨f,hf⟩ := exists_stripTheta_generator_nonzero χ
  let A := 2-a
  let G (z : ℂ) := globalThetaMellinIntegral f.val (ideleClassNormTwist χ ((a:ℂ)+z))
  have hG₀ : G (A:ℂ) ≠ 0 := by simpa only [G,A,Complex.ofReal_sub,Complex.ofReal_ofNat,add_sub_cancel] using hf
  obtain ⟨h₁,h₂⟩ := (mem_adelePolarSubspace f.val).mp f.property
  have hG : Differentiable ℂ G := (globalThetaMellinIntegral_entire_of_vanishing f.val h₁ h₂ χ).comp
    ((differentiable_const (a:ℂ)).add differentiable_id)
  have hGB (l h : ℝ) (_ : l ≤ h) : ∃ M : ℝ, ∀ z : ℂ, z.re ∈ Icc l h → ‖G z‖ ≤ M := by
    obtain ⟨M,hM⟩ := globalThetaMellinIntegral_bounded_closedStrip χ f (a+l) (a+h)
    exact ⟨M, fun z hz ↦ hM _ (by simpa only [Complex.add_re,Complex.ofReal_re,add_le_add_iff_left] using hz.1)
      (by simpa only [Complex.add_re,Complex.ofReal_re,add_le_add_iff_left] using hz.2)⟩
  have hr : 0 < r := by linarith
  obtain ⟨k,c,hk,hkc,hwide,hcr⟩ := choose_tail_widths A r hr
  let R := (Real.pi/2)/k
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨M,hM⟩ := hGB (A-R) (A+R) (by linarith)
  have hb0 (z : ℂ) (hz : |z.re-A| < R) : ‖G z‖ ≤ M :=
    hM z ⟨by linarith [(abs_lt.mp hz).1],by linarith [(abs_lt.mp hz).2]⟩
  let D := synthesis_stripBlaschkeFromDisk (A:ℂ) k
  let B := synthesis_stripBlaschkeToDisk (A:ℂ) k
  let Z := {z : ℂ // z ∈ ball 0 1 ∧ G (D z) = 0}
  let d (i : Z) := analyticOrderNatAt G (D i.val)
  obtain ⟨T,hord,hb,hcb,hpoint⟩ := single_generator_divisor_sequence A k r hk hr hwide G hG hG₀ M hb0
  let b (n : ℕ) (z : ℂ) := DiskTails.diskBlaschkeTail (fun i : Z ↦ i.val) d (T n) (B z)
  let S (n : ℕ) := (T n).image (fun i : Z ↦ D i.val)
  let m (n : ℕ) (w : S n) := analyticOrderNatAt G w.val
  have hords (n : ℕ) (w : S n) : 0 < m n w ∧ analyticOrderAt G w.val = m n w := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp w.property
    change 0 < analyticOrderNatAt G w.val ∧ analyticOrderAt G w.val = analyticOrderNatAt G w.val
    rw [← hi]
    exact hord i
  obtain ⟨U,hu,hprof⟩ := chart_tail_action hα hs hβ hβr e he atTop b (fun n ↦ (hb n).differentiableOn) hcb hpoint
  refine ⟨f,b,U,S,m,hG,hGB,hG₀,fun n w ↦ (hords n w).1,fun n w ↦ (hords n w).2,hb,hcb,hpoint,hu,hprof,?_⟩
  intro n H hkill
  have hjet (i : Z) (hi : i ∈ T n) : (d i : ℕ∞) ≤ analyticOrderAt H.val (D i.val) := by
    let w : S n := ⟨D i.val,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (test_analytic H _)).mpr (fun j hj ↦ hkill w j hj)
  obtain ⟨_,_,_,hmem⟩ := stripTheta_full_divisor_finite_jet_mem χ f α s a A k c r hα hs (by linarith)
    hk hkc hwide hcr hG₀ (T n) H hjet
  obtain ⟨q,hq,hMq⟩ := hprof n H
  exact hmem q (L (U n (e H))) hMq (radial_rep χ L hL _ q.val hq)

end RiemannMasullo.StripDual
