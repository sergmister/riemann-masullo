module

public import RiemannMasullo.Research.StripNuclearity.RationalPrimeFreeDiagonal
public import RiemannMasullo.Research.TraceComparison.SLocalAnnularCutoff
public import RiemannMasullo.Research.TraceComparison.SLocalRadialLift
import RiemannMasullo.Research.TraceComparison.SLocalQuotient
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # A positive prime-free test for the two spatial cutoff paths

Multiplying a positive real bump by the denominator of the real-place
kernel makes the local principal value exactly its positive integral.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
open RiemannMasullo.StripNuclearity
namespace RiemannMasullo

/-- In any fixed positive log interval there is a genuine smooth compact
profile whose centered real-place principal value is strictly positive.
In particular the interval may be chosen below log 2. -/
theorem exists_positive_rational_real_cutoff_profile {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ (g : ℝ → ℂ) (C : ℝ), ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Icc a b ∧ 0 < C ∧
      ∀ A : BruhatCompactSupport Rat.infinitePlace.Completionˣ,
        (∀ u, A.val u = rationalCenteredLogProfile g (Real.log ‖u.val‖)) →
        infiniteConnesWeilPrincipalValue Rat.infinitePlace A = (C : ℂ) := by
  let β : ContDiffBump ((a+b)/2) := ⟨(b-a)/8,(b-a)/4,by linarith,by linarith⟩
  let k (x : ℝ) : ℂ := 1 - Complex.exp (-2*(x:ℂ))
  let g (x : ℝ) := k x * (β x : ℂ)
  have hd : ContDiff ℝ (∞) g := (contDiff_const.sub
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))).mul
    (Complex.ofRealCLM.contDiff.comp β.contDiff)
  have he {x : ℝ} (hx : β x ≠ 0) : x ∈ Icc a b := by
    have hdist : dist x ((a+b)/2) < (b-a)/4 := lt_of_not_ge fun h ↦ hx (β.zero_of_le_dist h)
    rw [Real.dist_eq,abs_lt] at hdist
    exact ⟨by linarith [hdist.1], by linarith [hdist.2]⟩
  have hs : tsupport g ⊆ Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact he (fun h ↦ hx (by simp [g,h]))
  refine ⟨g,∫ x : ℝ, β x, hd, (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left,
    hs, β.integral_pos, fun A hA ↦ ?_⟩
  rw [rational_real_principalValue_positive_log_profile g hd.continuous ha hs A hA, ← integral_complex_ofReal]
  calc
    _ = ∫ x in Ioi (0:ℝ), (β x : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      have hp : Complex.exp (-2*(x:ℂ)) = (Real.exp (-2*x) : ℂ) := by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring
      have hn : k x ≠ 0 := by
        dsimp only [k]
        rw [hp]
        exact_mod_cast (sub_ne_zero.mpr (Real.exp_lt_one_iff.mpr (by linarith : -2*x < 0)).ne')
      exact mul_div_cancel_left₀ (β x : ℂ) hn
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      have hp : β x = 0 := by by_contra h; exact hx (ha.trans_le (he h).1)
      simp [hp])

section RationalLimits

set_option quotPrecheck false

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "S₀" => (∅ : Finset V)
local notation "I₀" => (SAdeleRing ℚ S₀)ˣ
local notation "H₀" => sProjectedDiagonal ℚ S₀
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μI" => sMultiplicativeTamagawaMeasure ℚ S₀
local notation "vS" => ((sLocalNormOneQuotientMeasure ℚ S₀) univ).toReal

attribute [local instance] instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1
  instIdeleClassMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1
local instance rationalAnnularT2 : T2Space I₀ := (sIdeleGroup_description ℚ S₀).2.1

private theorem empty_rational_pic :
    Subsingleton (CommRing.Pic ((S₀ : Set V).integer ℚ)) := by
  rw [Finset.coe_empty,integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

private theorem empty_rational_ramification (v : V) (h : differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal) :
    v ∈ S₀ := by
  have hd : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ), NumberField.discr_rat]
    rfl
  exact (v.isPrime.ne_top (top_unique (hd ▸ h))).elim

/-- For a positive-log radial profile and any actual lift, the faster
expansion of the lower cutoff gives the real-place integral on every
fundamental domain. The slower expansion gives zero. -/
theorem rational_annularTrace_two_limits_of_radial (g : ℝ → ℂ) (hg : Continuous g)
    {a b : ℝ} (ha : 0 < a) (hs : tsupport g ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x, φ.val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ)))
    (f : BruhatCompactSupport I₀) (hf : ∀ x : I₀, HasSum (fun ξ : H₀ ↦ f.val (ξ.val*x))
      (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S₀ x))))
    (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI) :
    Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D t⁻¹ t (t*t)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D (t*(t*t))⁻¹ t (t*t)) atTop
      (𝓝 ((vS : ℂ) * ∫ x in Ioi (0:ℝ), g x / (1-Complex.exp (-2*(x:ℂ))))) := by
  let := finite_rational_empty_sProjectedDiagonal
  have hn : g 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (not_le.mpr ha) (hs h).1
  have hφ₁ : φ.val 1 = 0 := by simp [hφ,rationalCenteredLogProfile,hn]
  obtain ⟨π, -, hker, hnorm, -⟩ := exists_sLocalTraceQuotient (F := ℚ) (S := S₀) empty_rational_pic
  have hout (u : outsideIntegralIdeleUnits ℚ S₀) (x : Cℚ) :
      φ.val (QuotientGroup.mk u.val * x) = φ.val x := by
    have hu : QuotientGroup.mk u.val ∈ π.toMonoidHom.ker := hker ▸ ⟨u.val,u.property,rfl⟩
    have he := (hnorm (QuotientGroup.mk u.val)).symm
    rw [show π (QuotientGroup.mk u.val) = 1 from hu, map_one] at he
    rw [hφ,hφ,map_mul,he,one_mul]
  obtain ⟨A,B,hArch, -,hzero,hval⟩ := sLocalTraceAnnularOrbitSum_two_local_limits φ hφ₁
    empty_rational_pic empty_rational_ramification hout f hf D hD
  have hreal := rational_real_principalValue_positive_log_profile g hg ha hs (A Rat.infinitePlace) (fun u ↦ by
    rw [hArch,hφ,ideleClassNorm_ofCompletion,Rat.isReal_infinitePlace.mult_eq_one,pow_one]
    rfl)
  have he : (∑ w : InfinitePlace ℚ, infiniteConnesWeilPrincipalValue w (A w)) =
      ∫ x in Ioi (0:ℝ), g x / (1-Complex.exp (-2*(x:ℂ))) := by
    rw [Fintype.sum_unique, @Subsingleton.elim (InfinitePlace ℚ) _ default Rat.infinitePlace]
    exact hreal
  simpa only [he, Fintype.sum_empty, add_zero] using And.intro hzero hval

/-- Paper: Section 12.4, footnote 2 on p. 514. For any fixed interval of
positive log norms below log 2 there is an actual rational idèle-class test
and a compact S-unit lift with two distinct sharp annular trace limits.
Every finite place restriction is zero. With the same spatial upper radius
t and Fourier radius t², the two lower radii 1/t and 1/t³ give respectively
zero and a positive real number, on every S-unit fundamental domain.
Deviation: This answers the question about independent sharp cutoff rates
for this test. The comparison with the smooth PW projection is separate. -/
theorem exists_rational_primeFree_annular_cutoff_distinct_limits {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) :
    ∃ (g : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (f : BruhatCompactSupport I₀) (c : ℝ),
      ContDiff ℝ (∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Icc a b ∧
      (∀ x, φ.val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))) ∧
      (∀ v : V, ∀ u : (v.adicCompletion ℚ)ˣ, φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 0) ∧
      (∀ x : I₀, HasSum (fun ξ : H₀ ↦ f.val (ξ.val*x)) (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S₀ x)))) ∧
      0 < c ∧ ∀ (D : Set I₀), IsFundamentalDomain H₀ D μI →
        Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D t⁻¹ t (t*t)) atTop (𝓝 0) ∧
        Tendsto (fun t : ℝ ↦ sLocalTraceAnnularOrbitSum f D (t*(t*t))⁻¹ t (t*t)) atTop (𝓝 (c : ℂ)) := by
  let := finite_rational_empty_sProjectedDiagonal
  obtain ⟨g,C,hg,hc,hs,hC,hA⟩ := exists_positive_rational_real_cutoff_profile ha hab
  obtain ⟨φ,hφ⟩ := exists_rationalCenteredNormTest g hg hc
  have hd : ContDiff ℝ (∞) (rationalCenteredLogProfile g) :=
    (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.div_const 2)).mul hg
  obtain ⟨f, -, hf⟩ := exists_sLocalTraceLift_radial_of_finite (F := ℚ) (S := S₀)
    (rationalCenteredLogProfile g) hd hc.mul_left φ hφ
  let G := (sIdeleQuotientNorm ℚ S₀).ker
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm ℚ S₀).isCompact_preimage (isCompact_singleton (x:=1)))
  let M := sLocalNormOneQuotientMeasure ℚ S₀
  have : M.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F:=ℚ) (S:=S₀)).1
  have hvol : 0 < vS := ENNReal.toReal_pos (isOpen_univ.measure_ne_zero M univ_nonempty) (measure_ne_top M univ)
  refine ⟨g,φ,f,vS*C,hg,hc,hs,hφ,?_,hf,mul_pos hvol hC,fun D hD ↦ ?_⟩
  · intro v u
    exact rational_finite_prime_free_restriction ha hb hs φ hφ v u
  · obtain ⟨A,hAr⟩ := exists_rational_archimedean_norm_test (rationalCenteredLogProfile g) hd hc.mul_left
    have he := (rational_real_principalValue_positive_log_profile g hg.continuous ha hs A hAr).symm.trans (hA A hAr)
    simpa only [he, Complex.ofReal_mul] using rational_annularTrace_two_limits_of_radial g hg.continuous
      ha hs φ hφ f hf D hD

end RationalLimits
end RiemannMasullo
