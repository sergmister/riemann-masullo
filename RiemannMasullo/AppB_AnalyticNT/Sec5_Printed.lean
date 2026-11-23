module

public import RiemannMasullo.AppB_AnalyticNT.Sec5
import Mathlib.Algebra.Field.ULift
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Data.Nat.Pairing
import RiemannMasullo.External.TauCeti.Analysis.Complex.Runge.Approximation

/-!
# Appendix B.5: statements that are false as printed

The printed claims are kept as propositions with separate refutation statements.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open Complex.HadamardThreeLines (verticalStrip)
open scoped Topology

namespace RiemannMasullo

/-- Paper: §B.5.1, injectivity sentence, p. 627. As printed: in every positive
dimension, the torus flow of rationally independent frequencies is injective.
This is the injectivity clause of the sentence. The repaired
`torusFlow_injective_of_linearIndependent` requires dimension at least two.
See ERRATA F19. -/
def Printed.torusFlow_injective_of_linearIndependent : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (τ : Fin N → ℝ), LinearIndependent ℚ τ → Injective (torusFlow τ)

/-- Paper: §B.5.1, injectivity sentence, p. 627. In dimension one the
single frequency `1` is rationally independent, and times zero and one have the same
image modulo one. -/
theorem Printed.torusFlow_injective_of_linearIndependent_false :
    ¬ Printed.torusFlow_injective_of_linearIndependent := by
  intro h
  have hli : LinearIndependent ℚ (fun _ : Fin 1 ↦ (1 : ℝ)) :=
    linearIndependent_unique_iff.mpr one_ne_zero
  have h01 :
      torusFlow (fun _ : Fin 1 ↦ (1 : ℝ)) 1 = torusFlow (fun _ : Fin 1 ↦ (1 : ℝ)) 0 := by
    rw [torusFlow_one, map_zero]
    funext i
    exact AddCircle.coe_period (1 : ℝ)
  exact one_ne_zero (h 1 le_rfl _ hli h01)

/-- Paper: Theorem B.5.2.1(2), p. 627. As printed: for every frequency vector
and every Riemann-integrable function on its orbit closure, the forward time average
in (B.5.2.1) exists and tends to the Haar probability integral. The forward equality
requires the time integrals to exist for all sufficiently large endpoints.
The repaired `kroneckerWeyl_riemannIntegrable_forward` assumes a measurable time
trace. See ERRATA F20. -/
def Printed.kroneckerWeyl_riemannIntegrable_forward : Prop :=
  ∀ (N : ℕ) [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ), TorusRiemannIntegrable μ u →
      let trace := fun t ↦ u (torusFlowInClosure τ t)
      (∀ᶠ T : ℝ in atTop, IntervalIntegrable trace volume 0 T) ∧
        Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, trace t) atTop (𝓝 (∫ x, u x ∂μ))

private theorem Printed.kroneckerWeyl_rat_functional :
    ∃ g : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, g (q : ℝ) = q := by
  let f : ℚ →ₗ[ℚ] ℝ := LinearMap.toSpanSingleton ℚ ℝ (1 : ℝ)
  have hf (q : ℚ) : f q = (q : ℝ) := by simp [f, Rat.smul_one_eq_cast]
  have hk : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr fun a b hab ↦ by
    rw [hf, hf] at hab; exact_mod_cast hab
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hk
  refine ⟨g, fun q ↦ ?_⟩
  have := LinearMap.congr_fun hg q
  rwa [LinearMap.comp_apply, hf] at this

open scoped Pointwise in
private theorem Printed.kroneckerWeyl_not_nullMeasurable_ker (g : ℝ →ₗ[ℚ] ℚ)
    (hg : ∀ q : ℚ, g (q : ℝ) = q) :
    ¬ ∀ n : ℕ, NullMeasurableSet ({x | g x = 0} ∩ Icc (-(n : ℝ)) n) volume := by
  intro hA
  set A : Set ℝ := {x | g x = 0} with hAdef
  have hAU : A = ⋃ n : ℕ, A ∩ Icc (-(n : ℝ)) n := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_Icc]
    refine ⟨fun hx ↦ ?_, fun ⟨_, hx, _⟩ ↦ hx⟩
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact ⟨n, hx, neg_le_of_abs_le hn, le_of_abs_le hn⟩
  by_cases h0 : ∀ n : ℕ, volume (A ∩ Icc (-(n : ℝ)) n) = 0
  · have hA0 : volume A = 0 := by rw [hAU]; exact measure_iUnion_null h0
    have hcover : (univ : Set ℝ) = ⋃ q : ℚ, (fun x ↦ x + -(q : ℝ)) ⁻¹' A := by
      ext x
      simp only [mem_univ, mem_iUnion, mem_preimage, true_iff]
      refine ⟨g x, ?_⟩
      change g (x + -(g x : ℝ)) = 0
      rw [map_add, map_neg, hg, add_neg_cancel]
    have : volume (univ : Set ℝ) = 0 := by
      rw [hcover]
      refine measure_iUnion_null fun q ↦ ?_
      rw [measure_preimage_add_right]
      exact hA0
    simp at this
  · push Not at h0
    obtain ⟨n, hn⟩ := h0
    obtain ⟨M, hMs, hMm, hMae⟩ := (hA n).exists_measurable_subset_ae_eq
    have hMpos : 0 < volume M := by rw [measure_congr hMae]; exact pos_iff_ne_zero.mpr hn
    have hMfin : volume M ≠ ⊤ := ((measure_mono (hMs.trans inter_subset_right)).trans_lt
      measure_Icc_lt_top).ne
    have hnhds := Measure.sub_mem_nhds_zero_of_addHaar_pos_ne_top volume M hMm hMpos hMfin
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn hδ
    have hqmem : (q : ℝ) ∈ M - M := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hq0]; exact hqδ)
    obtain ⟨a, ha, b, hb, hab⟩ := hqmem
    have ha' : g a = 0 := (hMs ha).1
    have hb' : g b = 0 := (hMs hb).1
    have : g (q : ℝ) = 0 := by rw [← hab, map_sub, ha', hb', sub_self]
    rw [hg] at this
    exact (Rat.cast_pos.mp hq0).ne' this

private theorem Printed.kroneckerWeyl_exists_nonmeasurable :
    ∃ L : ℝ, 0 < L ∧ ∃ E : Set ℝ, E ⊆ Ioc 0 L ∧ ¬ NullMeasurableSet E volume := by
  obtain ⟨g, hg⟩ := Printed.kroneckerWeyl_rat_functional
  have h := Printed.kroneckerWeyl_not_nullMeasurable_ker g hg
  push Not at h
  obtain ⟨n, hn⟩ := h
  set A : Set ℝ := {x | g x = 0} ∩ Icc (-(n : ℝ)) n
  refine ⟨2 * n + 1, by positivity, (fun x ↦ x + -((n : ℝ) + 1)) ⁻¹' A, ?_, fun hE ↦ hn ?_⟩
  · intro x hx
    obtain ⟨-, h1, h2⟩ := hx
    constructor <;> linarith
  · have hpre : A = (fun x ↦ x + ((n : ℝ) + 1)) ⁻¹' ((fun x ↦ x + -((n : ℝ) + 1)) ⁻¹' A) := by
      ext x; simp only [mem_preimage, add_neg_cancel_right]
    rw [hpre]
    exact hE.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving

private theorem Printed.kroneckerWeyl_measure_arc_eq_zero {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [IsFiniteMeasure μ]
    (φ : ℝ →+ G) (hφc : Continuous φ) (hφ : Injective φ) (L : ℝ) (hL : 0 ≤ L) :
    μ (φ '' Icc 0 L) = 0 := by
  set K := φ '' Icc 0 L
  have hKm : MeasurableSet K := ((isCompact_Icc).image hφc).isClosed.measurableSet
  let P : ℕ → Set G := fun k ↦ (fun h ↦ φ (-((k : ℝ) * (L + 1))) + h) ⁻¹' K
  have hPm (k : ℕ) : MeasurableSet (P k) := measurable_const_add _ hKm
  have hPμ (k : ℕ) : μ (P k) = μ K := measure_preimage_add μ _ K
  have hdisj : Pairwise (Disjoint on P) := by
    intro j k hjk
    refine Set.disjoint_left.mpr fun x hxj hxk ↦ hjk ?_
    obtain ⟨s, ⟨hs0, hsL⟩, hs⟩ := hxj
    obtain ⟨s', ⟨hs0', hsL'⟩, hs'⟩ := hxk
    have heq : φ (s - s') = φ (((k : ℝ) - j) * (L + 1)) := by
      have e1 : φ s = φ (-((j : ℝ) * (L + 1))) + x := hs
      have e2 : φ s' = φ (-((k : ℝ) * (L + 1))) + x := hs'
      rw [map_sub, e1, e2, show ((k : ℝ) - j) * (L + 1) = -((j : ℝ) * (L + 1)) - -((k : ℝ) * (L + 1)) by ring,
        map_sub]
      abel
    have h := hφ heq
    rcases lt_trichotomy j k with hlt | heq' | hgt
    · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      nlinarith
    · exact heq'
    · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hgt
      nlinarith
  by_contra hne
  have hU := measure_iUnion (μ := μ) hdisj hPm
  simp only [hPμ, ENNReal.tsum_const_eq_top_of_ne_zero hne] at hU
  exact measure_ne_top μ (⋃ k, P k) hU

private theorem Printed.kroneckerWeyl_linearIndependent_sqrt_two :
    LinearIndependent ℚ ![(1 : ℝ), √2] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have h2 : √2 = ((-s / t : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith
    exact irrational_sqrt_two ⟨_, h2.symm⟩

/-- Paper: Theorem B.5.2.1(2), p. 627. Take frequencies `(1, √2)` and a
non-Lebesgue-measurable subset `E` of `(0, 1)`. The indicator of the image of `E`
under the flow is bounded and continuous off the compact Haar-null orbit arc of
`[0, 1]`. Injectivity makes its time trace the indicator of `E`, which is
nonmeasurable on every interval `[0, T]` with `T ≥ 1`. -/
theorem Printed.kroneckerWeyl_riemannIntegrable_forward_false :
    ¬ Printed.kroneckerWeyl_riemannIntegrable_forward := by
  intro h
  obtain ⟨L, hL, E, hE, hnm⟩ := Printed.kroneckerWeyl_exists_nonmeasurable
  set τ : Fin 2 → ℝ := ![(1 : ℝ), √2]
  have hinj : Injective (torusFlowInClosure τ) := fun s t hst ↦
    RiemannMasullo.torusFlow_injective_of_linearIndependent le_rfl
      Printed.kroneckerWeyl_linearIndependent_sqrt_two (congrArg Subtype.val hst)
  let φ : ℝ →+ torusFlowClosure τ :=
    { toFun := torusFlowInClosure τ
      map_zero' := Subtype.ext (map_zero (torusFlow τ))
      map_add' := fun s t ↦ Subtype.ext (map_add (torusFlow τ) s t) }
  have hφc : Continuous φ := (torusFlow τ).continuous.subtype_mk _
  have : CompactSpace (torusFlowClosure τ) := isCompact_iff_compactSpace.mp
    (AddSubgroup.isClosed_topologicalClosure _).isCompact
  let μ : Measure (torusFlowClosure τ) := Measure.addHaarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨Measure.addHaarMeasure_self⟩
  set K := φ '' Icc 0 L with hKdef
  have hK0 : μ K = 0 :=
    Printed.kroneckerWeyl_measure_arc_eq_zero μ φ hφc hinj L hL.le
  have hKc : IsClosed K := ((isCompact_Icc).image hφc).isClosed
  have hEK : φ '' E ⊆ K := image_mono fun x hx ↦ Ioc_subset_Icc_self (hE hx)
  let u : torusFlowClosure τ → ℂ := (φ '' E).indicator fun _ ↦ 1
  have hu : TorusRiemannIntegrable μ u := by
    refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
    · by_cases hx : x ∈ φ '' E <;> simp [u, hx]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hK0] with x hx
      refine continuousAt_const.congr (f := fun _ ↦ (0 : ℂ)) ?_
      filter_upwards [hKc.isOpen_compl.mem_nhds hx] with y hy
      exact (indicator_of_notMem (fun h ↦ hy (hEK h)) _).symm
  have htrace : (fun t ↦ u (torusFlowInClosure τ t)) = E.indicator fun _ ↦ (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ E
    · have : torusFlowInClosure τ t ∈ φ '' E := ⟨t, ht, rfl⟩
      simp [u, ht, this]
    · have : torusFlowInClosure τ t ∉ φ '' E := fun ⟨s, hs, hst⟩ ↦ ht (hinj hst ▸ hs)
      simp [u, ht, this]
  have hint := (h 2 τ μ u hu).1
  obtain ⟨T, hT, hLT⟩ := (hint.and (eventually_ge_atTop L)).exists
  rw [htrace] at hT
  have hmeas := (hT.1).aestronglyMeasurable.aemeasurable
  have hET : E ⊆ Ioc 0 T := fun x hx ↦ ⟨(hE hx).1, (hE hx).2.trans hLT⟩
  rw [← aemeasurable_indicator_iff measurableSet_Ioc, indicator_indicator,
    inter_eq_right.mpr hET, aemeasurable_indicator_const_iff] at hmeas
  exact hnm hmeas

/-- Paper: Proposition B.5.3.2(1),(3), p. 632. As printed: for every number field,
finite set of places containing the archimedean places, and continuous character
unramified at its finite places, there are heights with both stated signs and a common
finite bound on the product in (B.5.3.3) for every integer index. The bound is written
as a positive lower bound on the norm of the product of the denominators, so it
excludes zeros of every denominator. These two sign conditions and the bound are
the clauses at issue. The repaired
`exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow` allows a positive
height at index zero. See ERRATA F21. -/
def Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
      ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧
        (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k ≤ 0 → T k ≤ 0) ∧
        ∀ k, c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((T k : ℂ) * Complex.I)‖

/-- Every number field refutes the printed bound: the trivial character has a zero
factor at time zero. -/
private theorem
    Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false_of_numberField.{u}
    (F : Type u) [Field F] [NumberField F]
    (h : Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow.{u}) : False := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hone :
      ∀ g, ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 g = 1 := by
    intro g
    change ((1 : Circle) : ℂ) * (_ : ℂ) ^ (0 : ℂ) = 1
    simp
  have hres : ∀ x : v.adicCompletion F, x ≠ 0 →
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).restrict v x =
        1 := by
    intro x hx
    rw [show x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
      HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    simp [hone]
  have hunr :
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).IsUnramifiedAt
        v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    intro x
    exact hres _ (by simp)
  obtain ⟨c, T, hc, hpos, hneg, hbound⟩ := h F {v} 1 (by simpa using hunr)
  have hT : T 0 = 0 := le_antisymm (hneg 0 le_rfl) (hpos 0 le_rfl)
  have h0 := hbound 0
  rw [hT, reciprocalPartialHeckeEulerProduct_singleton _ v hunr,
    hunr.localValue_eq _ Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
    hres _ (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)] at h0
  simp at h0
  linarith

/-- Paper: Proposition B.5.3.2(1),(3), p. 632. Take the rational field,
the trivial character, and the places consisting of infinity and the prime above two.
Both sign conditions apply at index zero, so `T 0 = 0`. The only finite factor
in the denominator is then `|1 - 2^0| = 0`. -/
theorem Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false :
    ¬ Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  exact
    Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false_of_numberField
      (ULift ℚ) h

/-- Paper: Lemma B.5.3.4(2), p. 633. As printed: if a holomorphic function on a
bounded nonempty open vertical strip is strongly recurrent on every closed disc it
contains, then the function is strongly recurrent on every compact subset of the strip.
Part (1) is `stronglyRecurrentOn_of_subset`. See ERRATA F22. -/
def Printed.stronglyRecurrentOn_compact_of_closedBall : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f (verticalStrip a b) →
    (∀ (z : ℂ) (r : ℝ), 0 ≤ r → Metric.closedBall z r ⊆ verticalStrip a b →
      StronglyRecurrentOn f (Metric.closedBall z r)) →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ verticalStrip a b → StronglyRecurrentOn f K

open scoped Complex ENNReal

private theorem Printed.recurrentRows_compl_connected (R : ℝ) (J : Set ℝ) {v : ℝ}
    (hv : v ∉ J) : IsConnected ((Icc (-R) R) ×ℂ J)ᶜ := by
  let S := ((Icc (-R) R) ×ℂ J)ᶜ
  let base : ℂ := ⟨R + 1, v⟩
  have hb : base ∈ S := fun h ↦ hv h.2
  refine (show IsPathConnected S from ⟨base, hb, ?_⟩).isConnected
  have hhorizontal (x y : ℂ) (hxy : x.im = y.im) (hx : x.im ∉ J) : JoinedIn S x y := by
    apply JoinedIn.of_segment_subset
    have hc := (convex_singleton (𝕜 := ℝ) (x.im)).linear_preimage Complex.imLm
    refine (hc.segment_subset (show x.im = x.im from rfl) (show y.im = x.im from hxy.symm)).trans ?_
    intro w hw h
    exact hx ((show w.im = x.im from hw) ▸ h.2)
  have hvertical (x y : ℂ) (hxy : x.re = y.re) (hx : x.re ∉ Icc (-R) R) :
      JoinedIn S x y := by
    apply JoinedIn.of_segment_subset
    have hc := (convex_singleton (𝕜 := ℝ) (x.re)).linear_preimage Complex.reLm
    refine (hc.segment_subset (show x.re = x.re from rfl) (show y.re = x.re from hxy.symm)).trans ?_
    intro w hw h
    exact hx ((show w.re = x.re from hw) ▸ h.1)
  intro z hz
  by_cases hi : z.im ∈ J
  · let w : ℂ := ⟨z.re, v⟩
    exact (hhorizontal base w rfl hv).trans
      (hvertical z w rfl (fun h ↦ hz ⟨h, hi⟩)).symm
  · let w : ℂ := ⟨R + 1, z.im⟩
    exact (hvertical base w rfl (fun h ↦ by
      have h' : R + 1 ≤ R := h.2
      linarith)).trans (hhorizontal z w rfl hi).symm

private theorem Printed.recurrentRows_approximate {ι : Type*} [Finite ι] (R : ℝ)
    (C U : ι → Set ℝ) (hc : ∀ j, IsCompact (C j)) (hu : ∀ j, IsOpen (U j))
    (hcu : ∀ j, C j ⊆ U j) (hd : Pairwise (Disjoint on U))
    (g : ι → ℂ → ℂ) (hg : ∀ j, Differentiable ℂ (g j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ → ℂ, Differentiable ℂ p ∧
      ∀ j z, z.re ∈ Icc (-R) R → z.im ∈ C j → ‖p z - g j z‖ < ε := by
  classical
  let J := ⋃ j, C j
  let V := Complex.im ⁻¹' ⋃ j, U j
  have hJ : IsCompact J := isCompact_iUnion hc
  obtain ⟨v, hv⟩ := hJ.bddAbove
  have hvc : v + 1 ∉ J := fun h ↦ by linarith [hv h]
  let K := Icc (-R) R ×ℂ J
  have hK : IsCompact K := isCompact_Icc.reProdIm hJ
  have hKV : K ⊆ V := by
    rintro z ⟨_, hz⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨j, hcu j hj⟩
  let f (z : ℂ) : ℂ := if h : ∃ j, z.im ∈ U j then g (Classical.choose h) z else 0
  have hf (j : ι) (z : ℂ) (hz : z.im ∈ U j) : f z = g j z := by
    have h : ∃ j, z.im ∈ U j := ⟨j, hz⟩
    have he : Classical.choose h = j := by
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) (Classical.choose_spec h) hz
    simpa only [f, dite_eq_left h] using congrArg (fun i ↦ g i z) he
  have hdiff : DifferentiableOn ℂ f V := by
    intro z hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    apply (DifferentiableAt.congr_of_eventuallyEq (hg j z) ?_).differentiableWithinAt
    filter_upwards [(hu j).preimage Complex.continuous_im |>.mem_nhds hj] with w hw
    exact hf j w hw
  obtain ⟨p, hp⟩ :=
    hK.isConnected_compl_iff_forall_differentiableOn_exists_polynomial_norm_sub_lt.mp
      (Printed.recurrentRows_compl_connected R J hvc) V
      (Complex.continuous_im.isOpen_preimage _ (isOpen_iUnion hu)) hKV f hdiff ε hε
  refine ⟨p.eval, p.differentiable, fun j z hr hi ↦ ?_⟩
  rw [norm_sub_rev, ← hf j z (hcu j hi)]
  exact hp z ⟨hr, mem_iUnion.mpr ⟨j, hi⟩⟩

private abbrev Printed.RecurrentRow (L : ℕ) := Option (Fin L ⊕ Fin L ⊕ Fin L)

private def Printed.recurrentRows_bounds (L : ℕ) : Printed.RecurrentRow L → ℤ × ℤ
  | none => (-4 * (L : ℤ), 4 * (L : ℤ))
  | some (.inl k) => (4 * ((L : ℤ) + (k.val : ℤ)) + 1, 4 * ((L : ℤ) + (k.val : ℤ)) + 3)
  | some (.inr (.inl k)) => (4 * ((L : ℤ) + (k.val : ℤ) + 1), 4 * ((L : ℤ) + (k.val : ℤ) + 1))
  | some (.inr (.inr k)) =>
      (-4 * ((L : ℤ) + (k.val : ℤ) + 1), -4 * ((L : ℤ) + (k.val : ℤ) + 1))

private theorem Printed.recurrentRows_separated (L : ℕ) {i j : Printed.RecurrentRow L} (h : i ≠ j) :
    (Printed.recurrentRows_bounds L i).2 + 1 ≤ (Printed.recurrentRows_bounds L j).1 ∨
      (Printed.recurrentRows_bounds L j).2 + 1 ≤ (Printed.recurrentRows_bounds L i).1 := by
  rcases i with _ | (i | i | i) <;> rcases j with _ | (j | j | j) <;>
    simp [Printed.recurrentRows_bounds, Fin.ext_iff] at h ⊢ <;> omega

private theorem Printed.recurrentRows_step (L : ℕ) (c : ℝ) (p : ℂ → ℂ)
    (hp : Differentiable ℂ p) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧
      (∀ z : ℂ, |z.re| ≤ 4 * (L : ℝ) → |z.im| ≤ 4 * (L : ℝ) → ‖q z - p z‖ < ε) ∧
      (∀ (k : Fin L) (z : ℂ), |z.re| ≤ 4 * (L : ℝ) → |z.im - c| ≤ 1 →
        ‖q (z + ((4 * ((L : ℝ) + (k.val : ℝ)) + 2 - c : ℝ) : ℂ) * Complex.I) - p z‖ < ε) ∧
      (∀ (k : Fin L) (s : ℝ), (s = 1 ∨ s = -1) →
        ‖q (((s * (4 * ((L : ℝ) + (k.val : ℝ) + 1)) : ℝ) : ℂ) * Complex.I) - 4‖ < ε) := by
  let a (j : Printed.RecurrentRow L) : ℝ := (Printed.recurrentRows_bounds L j).1
  let b (j : Printed.RecurrentRow L) : ℝ := (Printed.recurrentRows_bounds L j).2
  let g : Printed.RecurrentRow L → ℂ → ℂ
    | none => p
    | some (.inl k) => fun z ↦ p (z - ((4 * ((L : ℝ) + k.val) + 2 - c : ℝ) : ℂ) * Complex.I)
    | some (.inr _) => fun _ ↦ 4
  have hg (j : Printed.RecurrentRow L) : Differentiable ℂ (g j) := by
    rcases j with _ | (k | k | k)
    · exact hp
    · exact hp.comp (differentiable_id.sub (differentiable_const _))
    · exact differentiable_const _
    · exact differentiable_const _
  have hd : Pairwise (Disjoint on fun j ↦ Ioo (a j - 1 / 4) (b j + 1 / 4)) := by
    intro i j hij
    have hgap : b i + 1 ≤ a j ∨ b j + 1 ≤ a i := by
      rcases Printed.recurrentRows_separated L hij with h | h
      · left
        dsimp [a, b]
        exact_mod_cast h
      · right
        dsimp [a, b]
        exact_mod_cast h
    refine disjoint_left.mpr fun x hx hy ↦ ?_
    rcases hgap with h | h
    · linarith [hx.2, hy.1]
    · linarith [hy.2, hx.1]
  obtain ⟨q, hq, hqerr⟩ := Printed.recurrentRows_approximate (4 * (L : ℝ))
    (fun j ↦ Icc (a j) (b j)) (fun j ↦ Ioo (a j - 1 / 4) (b j + 1 / 4))
    (fun _ ↦ isCompact_Icc) (fun _ ↦ isOpen_Ioo)
    (fun j _ hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩) hd g hg hε
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · intro z hz hi
    exact hqerr none z (abs_le.mp hz) (by simpa [a, b, Printed.recurrentRows_bounds] using abs_le.mp hi)
  · intro k z hz hi
    let d : ℝ := 4 * ((L : ℝ) + k.val) + 2 - c
    let w : ℂ := z + (d : ℂ) * Complex.I
    have hwr : w.re = z.re := by simp [w, Complex.mul_re]
    have hwi : w.im = z.im + d := by simp [w, Complex.mul_im]
    have hab := abs_le.mp hi
    have hw : w.im ∈ Icc (a (some (.inl k))) (b (some (.inl k))) := by
      rw [hwi, mem_Icc]
      push_cast [a, b, Printed.recurrentRows_bounds]
      dsimp [d]
      constructor <;> linarith
    simpa [w, d, g] using hqerr (some (.inl k)) w (hwr ▸ abs_le.mp hz) hw
  · intro k s hs
    rcases hs with rfl | rfl
    · refine hqerr (some (.inr (.inl k))) _ ?_ ?_
      · simp [Complex.mul_re, Nat.cast_nonneg]
      · simp [Complex.mul_im, a, b, Printed.recurrentRows_bounds]
    · refine hqerr (some (.inr (.inr k))) _ ?_ ?_
      · simp [Complex.mul_re, Nat.cast_nonneg]
      · simp [Complex.mul_im, a, b, Printed.recurrentRows_bounds]

private def Printed.recurrentSide (n : ℕ) : ℝ := 4 * ((2 ^ n : ℕ) : ℝ)

private def Printed.recurrentSquare (n : ℕ) : Set ℂ :=
  {z | |z.re| ≤ Printed.recurrentSide n ∧ |z.im| ≤ Printed.recurrentSide n}

private def Printed.recurrentError (n : ℕ) : ℝ := (1 / 2) ^ (n + 1)

private theorem Printed.recurrentSide_eventually (B : ℝ) :
    ∀ᶠ n in atTop, B ≤ Printed.recurrentSide n := by
  have h : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa [Printed.recurrentSide, mul_comm] using
    (h.atTop_mul_const (by norm_num : 0 < (4 : ℝ))).eventually_ge_atTop B

private theorem Printed.recurrentSquare_mono : Monotone Printed.recurrentSquare := by
  intro n m h z hz
  have hside : Printed.recurrentSide n ≤ Printed.recurrentSide m := by
    simpa [Printed.recurrentSide] using
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h)
        (by norm_num : (0 : ℝ) ≤ 4)
  exact ⟨hz.1.trans hside, hz.2.trans hside⟩

private theorem Printed.recurrentError_tendsto : Tendsto Printed.recurrentError atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0)
  simpa only [pow_succ, zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)

private theorem Printed.recurrentLimit (p : ℕ → ℂ → ℂ)
    (hd : ∀ n, Differentiable ℂ (p n))
    (hstep : ∀ n, ∀ z ∈ Printed.recurrentSquare n,
      ‖p (n + 1) z - p n z‖ ≤ Printed.recurrentError n - Printed.recurrentError (n + 1)) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ n, ∀ z ∈ Printed.recurrentSquare n, ‖f z - p n z‖ ≤ Printed.recurrentError n := by
  classical
  have hnonneg (n : ℕ) : 0 ≤ Printed.recurrentError n := by
    unfold Printed.recurrentError
    positivity
  have htail (n m : ℕ) (hnm : n ≤ m) (z : ℂ) (hz : z ∈ Printed.recurrentSquare n) :
      dist (p m z) (p n z) ≤ Printed.recurrentError n - Printed.recurrentError m := by
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have hs := hstep m z (Printed.recurrentSquare_mono hnm hz)
      calc
        dist (p (m + 1) z) (p n z) ≤ dist (p (m + 1) z) (p m z) + dist (p m z) (p n z) :=
          dist_triangle _ _ _
        _ ≤ (Printed.recurrentError m - Printed.recurrentError (m + 1)) +
            (Printed.recurrentError n - Printed.recurrentError m) :=
          add_le_add (by simpa only [dist_eq_norm] using hs) ih
        _ = _ := by ring
  have hpoint (z : ℂ) : ∃ fz : ℂ, Tendsto (fun n ↦ p n z) atTop (𝓝 fz) := by
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    have hlarge := Printed.recurrentSide_eventually (max |z.re| |z.im|)
    have hsmall := Printed.recurrentError_tendsto.eventually_lt_const hε
    obtain ⟨N, hN, hNε⟩ := (hlarge.and hsmall).exists
    refine ⟨N, fun n hn ↦ ?_⟩
    have hz : z ∈ Printed.recurrentSquare N :=
      ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
    linarith [htail N n hn z hz, hnonneg n]
  choose f hf using hpoint
  have herr (n : ℕ) (z : ℂ) (hz : z ∈ Printed.recurrentSquare n) :
      ‖f z - p n z‖ ≤ Printed.recurrentError n := by
    rw [← dist_eq_norm]
    have ht : Tendsto (fun m ↦ dist (p m z) (p n z)) atTop (𝓝 (dist (f z) (p n z))) :=
      (hf z).dist tendsto_const_nhds
    refine le_of_tendsto ht ((eventually_ge_atTop n).mono fun m hm ↦ ?_)
    linarith [htail n m hm z hz, hnonneg m]
  refine ⟨f, differentiableOn_univ.mp (?_ : DifferentiableOn ℂ f univ), herr⟩
  apply TendstoLocallyUniformlyOn.differentiableOn (F := p) (φ := atTop) _
    (Eventually.of_forall fun n ↦ (hd n).differentiableOn) isOpen_univ
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
  intro K _ hK
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Printed.recurrentSide_eventually M, Printed.recurrentError_tendsto.eventually_lt_const hε]
    with n hn hnε z hz
  rw [dist_eq_norm]
  apply (herr n z ?_).trans_lt hnε
  exact ⟨Complex.abs_re_le_norm z |>.trans ((hM z hz).trans hn),
    Complex.abs_im_le_norm z |>.trans ((hM z hz).trans hn)⟩

private theorem Printed.upperDensity_blocks_pos {X : Set ℝ} {δ c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hblocks : ∀ N : ℕ, ∃ n ≥ N, ∀ k : Fin (2^n),
      Ioo (4 * (((2^n : ℕ) : ℝ) + (k : ℕ)) + 2 - c - δ)
          (4 * (((2^n : ℕ) : ℝ) + (k : ℕ)) + 2 - c + δ) ⊆ X) :
    0 < upperDensity X := by
  have hb : IsBoundedUnder (· ≤ ·) atTop
      (fun T : ℝ ↦ volume.real (Icc (-T) T ∩ X) / (2 * T)) := by
    refine ⟨1, eventually_map.mpr ((eventually_gt_atTop (0 : ℝ)).mono fun T hT ↦ ?_)⟩
    show volume.real (Icc (-T) T ∩ X) / (2 * T) ≤ 1
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * T)]
    calc volume.real (Icc (-T) T ∩ X) ≤ volume.real (Icc (-T) T) :=
          measureReal_mono inter_subset_left measure_Icc_lt_top.ne
      _ = 2 * T := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  refine lt_of_lt_of_le (show 0 < δ / 12 by positivity) (le_limsup_of_frequently_le ?_ hb)
  refine frequently_atTop.mpr fun T₀ ↦ ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (max |c| T₀)
  obtain ⟨n, hn, hs⟩ := hblocks N
  let L : ℕ := 2^n
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (Nat.one_le_two_pow (n := n))
  have hnL : n ≤ L := by dsimp [L]; exact (Nat.lt_two_pow_self).le
  have hNL : (N : ℝ) ≤ L := by exact_mod_cast hn.trans hnL
  have hc : |c| ≤ L := (le_max_left _ _).trans (hN.trans hNL)
  have hT₀ : T₀ ≤ L := (le_max_right _ _).trans (hN.trans hNL)
  refine ⟨12 * L, by linarith, ?_⟩
  let J (k : ℕ) := Ioo (4 * ((L : ℝ) + k) + 2 - c - δ) (4 * ((L : ℝ) + k) + 2 - c + δ)
  have hdisj : PairwiseDisjoint (↑(Finset.range L)) J := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr fun t hi hj ↦ ?_
    have hi1 := hi.1; have hi2 := hi.2; have hj1 := hj.1; have hj2 := hj.2
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      linarith
  have hu : (⋃ k ∈ Finset.range L, J k) ⊆ Icc (-(12 * L)) (12 * L) ∩ X := by
    intro t ht
    simp only [mem_iUnion, Finset.mem_range] at ht
    obtain ⟨k, hk, ht⟩ := ht
    have hk0 : 0 ≤ (k : ℝ) := k.cast_nonneg
    have hkL : (k : ℝ) ≤ L := by exact_mod_cast hk.le
    exact ⟨⟨by linarith [ht.1, le_abs_self c], by linarith [ht.2, neg_le_abs c]⟩,
      hs ⟨k, hk⟩ ht⟩
  have hvol : volume.real (⋃ k ∈ Finset.range L, J k) = L * (2 * δ) := by
    rw [measureReal_biUnion_finset hdisj (fun k _ ↦ measurableSet_Ioo)
      (fun k _ ↦ measure_Ioo_lt_top.ne)]
    rw [Finset.sum_congr rfl fun k _ ↦ show volume.real (J k) = _ from
      Real.volume_real_Ioo_of_le (by linarith : 4 * ((L : ℝ) + k) + 2 - c - δ ≤
        4 * ((L : ℝ) + k) + 2 - c + δ)]
    have heq (k : ℕ) : 4 * ((L : ℝ) + k) + 2 - c + δ - (4 * ((L : ℝ) + k) + 2 - c - δ) =
        2 * δ := by ring
    simp only [heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [le_div_iff₀ (by linarith : 0 < 2 * (12 * (L : ℝ)))]
  calc δ / 12 * (2 * (12 * (L : ℝ))) = L * (2 * δ) := by ring
    _ = volume.real (⋃ k ∈ Finset.range L, J k) := hvol.symm
    _ ≤ _ := measureReal_mono hu ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne

private theorem Printed.upperDensity_zero_of_subset_Icc {X : Set ℝ} {A : ℝ}
    (hX : X ⊆ Icc (-A) A) : upperDensity X = 0 := by
  have heq : (fun T : ℝ ↦ (volume.real X / 2) * T⁻¹) =ᶠ[atTop]
      fun T ↦ volume.real (Icc (-T) T ∩ X) / (2 * T) := by
    filter_upwards [eventually_ge_atTop A] with T hT
    rw [inter_eq_right.mpr (hX.trans (Icc_subset_Icc (neg_le_neg hT) hT))]
    ring
  have hlim := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (volume.real X / 2)
  simpa [upperDensity] using (hlim.congr' heq).limsup_eq

private theorem Printed.not_stronglyRecurrentOn_segment_of_marks (f : ℂ → ℂ)
    (hseg : ∀ x ∈ Icc (-2 : ℝ) 2, ‖f ((x : ℂ) * Complex.I)‖ ≤ 1)
    (hmark : ∀ j : ℕ, 2 ≤ j →
      3 ≤ ‖f (((4 * (j : ℝ) : ℝ) : ℂ) * Complex.I)‖ ∧
      3 ≤ ‖f (((-(4 * (j : ℝ)) : ℝ) : ℂ) * Complex.I)‖) :
    ¬ StronglyRecurrentOn f ((fun x : ℝ ↦ (x : ℂ) * Complex.I) '' Icc (-2) 2) := by
  set K := (fun x : ℝ ↦ (x : ℂ) * Complex.I) '' Icc (-2) 2
  intro hrec
  have hsub : verticalReturnTimes f K 2 ⊆ Icc (-8 : ℝ) 8 := by
    intro t ht
    by_contra hn
    have hbig : 8 < |t| := by
      contrapose! hn
      exact abs_le.mp hn
    let j : ℕ := ⌊|t| / 4 + 1 / 2⌋₊
    have hj₁ : (j : ℝ) ≤ |t| / 4 + 1 / 2 := Nat.floor_le (by positivity)
    have hj₂ : |t| / 4 + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hj : 2 ≤ j := by
      by_contra! h
      have : (j : ℝ) ≤ 1 := by exact_mod_cast (show j ≤ 1 by omega)
      linarith
    obtain ⟨y, hy, hval⟩ :
        ∃ y : ℝ, y - t ∈ Icc (-2 : ℝ) 2 ∧ 3 ≤ ‖f ((y : ℂ) * Complex.I)‖ := by
      rcases le_or_gt 0 t with hp | hn
      · rw [abs_of_nonneg hp] at hj₁ hj₂
        exact ⟨4 * j, ⟨by linarith, by linarith⟩, (hmark j hj).1⟩
      · rw [abs_of_neg hn] at hj₁ hj₂
        exact ⟨-(4 * j), ⟨by linarith, by linarith⟩, (hmark j hj).2⟩
    let z : K := ⟨((y - t : ℝ) : ℂ) * Complex.I, ⟨y - t, hy, rfl⟩⟩
    have hzt : (z : ℂ) + (t : ℂ) * Complex.I = (y : ℂ) * Complex.I := by
      dsimp [z]; push_cast; ring
    have hlt := (le_iSup (fun w : K ↦
      (‖f ((w : ℂ) + (t : ℂ) * Complex.I) - f w‖₊ : ℝ≥0∞)) z).trans_lt ht
    rw [← eNorm_eq_nnNorm, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 2), hzt] at hlt
    have hnorm := norm_sub_norm_le (f ((y : ℂ) * Complex.I)) (f z)
    have hsmall : ‖f z‖ ≤ 1 := hseg (y - t) hy
    linarith
  have hpos := hrec 2 (by norm_num)
  rw [Printed.upperDensity_zero_of_subset_Icc hsub] at hpos
  exact (lt_irrefl _) hpos

private theorem Printed.stronglyRecurrentOn_closedBall_of_copies {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hcopy : ∀ (c : ℤ) (η : ℝ), 0 < η → ∃ᶠ n : ℕ in atTop, ∀ (k : Fin (2^n)) (z : ℂ),
      |z.re| ≤ 1 → |z.im - (c : ℝ)| ≤ 1 →
        ‖f (z + ((4 * (((2^n : ℕ) : ℝ) + (k.val : ℝ)) + 2 - (c : ℝ) : ℝ) : ℂ) * Complex.I)
          - f z‖ ≤ η)
    (w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hstrip : Metric.closedBall w r ⊆ Complex.HadamardThreeLines.verticalStrip (-(1/2)) (1/2)) :
    StronglyRecurrentOn f (Metric.closedBall w r) := by
  have hrp : w + (r : ℂ) ∈ Metric.closedBall w r := by
    simp [Metric.mem_closedBall, Real.norm_eq_abs, abs_of_nonneg hr]
  have hrm : w - (r : ℂ) ∈ Metric.closedBall w r := by
    simp [Metric.mem_closedBall, Real.norm_eq_abs, abs_of_nonneg hr]
  have hp := (hstrip hrp).2
  have hm := (hstrip hrm).1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hp hm
  have hrlt : r < 1 / 2 := by linarith
  let c : ℤ := ⌊w.im + 1/2⌋
  have hc1 : (c : ℝ) ≤ w.im + 1/2 := Int.floor_le _
  have hc2 : w.im + 1/2 < (c : ℝ) + 1 := Int.lt_floor_add_one _
  intro ε hε
  have huc := (isCompact_closedBall w (r + 1)).uniformContinuousOn_of_continuous
    (hf.continuous.continuousOn)
  obtain ⟨s, hs, hcont⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 4) (by positivity)
  let δ := min 1 (min s (1/2-r))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min hs (sub_pos.mpr hrlt))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδs : δ ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ 1/2-r := (min_le_right _ _).trans (min_le_right _ _)
  apply Printed.upperDensity_blocks_pos (c := (c : ℝ)) hδ hδ1
  intro N
  obtain ⟨n, hn, hc⟩ := frequently_atTop.mp (hcopy c (ε / 4) (by positivity)) N
  refine ⟨n, hn, ?_⟩
  intro k t ht
  let t₀ : ℝ := 4 * (((2^n : ℕ) : ℝ) + (k.val : ℝ)) + 2 - (c : ℝ)
  have hd : |t - t₀| < δ := abs_sub_lt_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  show (⨆ z : Metric.closedBall w r,
    (‖f ((z : ℂ) + (t : ℂ) * Complex.I) - f z‖₊ : ℝ≥0∞)) < ENNReal.ofReal ε
  refine (iSup_le fun z ↦ ?_).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr
    (show ε / 2 < ε by linarith))
  let z' : ℂ := (z : ℂ) + ((t-t₀ : ℝ) : ℂ) * Complex.I
  have hdiff : dist z' z = |t-t₀| := by
    rw [dist_eq_norm, show z' - (z : ℂ) = ((t - t₀ : ℝ) : ℂ) * Complex.I by dsimp [z']; abel,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hzw : dist (z : ℂ) w ≤ r := z.2
  have hz'w : dist z' w ≤ r + 1 := by linarith [dist_triangle z' (z : ℂ) w]
  have him : |(z : ℂ).im - w.im| ≤ r := by
    rw [dist_eq_norm] at hzw
    simpa using (Complex.abs_im_le_norm ((z : ℂ) - w)).trans hzw
  have hz're : |z'.re| ≤ 1 := by
    have h₁ := (hstrip z.2).1
    have h₂ := (hstrip z.2).2
    simp [z', abs_le]; constructor <;> linarith
  have hz'im : |z'.im - (c : ℝ)| ≤ 1 := by
    simp only [z', Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, abs_le]
    constructor <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2, (abs_lt.mp hd).1, (abs_lt.mp hd).2]
  have hv := hc k z' hz're hz'im
  have hcon := hcont z' (show z' ∈ Metric.closedBall w (r+1) from hz'w) (z : ℂ)
    (show (z : ℂ) ∈ Metric.closedBall w (r+1) from by
      exact le_trans hzw (by linarith)) (hdiff.trans_lt (hd.trans_le hδs))
  have heq : z' + (t₀ : ℂ) * Complex.I = (z : ℂ) + (t : ℂ) * Complex.I := by
    dsimp [z']; push_cast; ring
  change ‖f (z' + (t₀ : ℂ) * Complex.I) - f z'‖ ≤ ε / 4 at hv
  rw [heq] at hv
  rw [dist_eq_norm] at hcon
  rw [← eNorm_eq_nnNorm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have htri := dist_triangle (f ((z : ℂ) + (t : ℂ) * Complex.I)) (f z') (f z)
  simp only [dist_eq_norm] at htri
  linarith

private theorem Printed.recurrentMarks_cover (j : ℕ) (hj : 2 ≤ j) :
    ∃ (n : ℕ) (k : Fin (2^n)), j = 2^n + k.val + 1 := by
  let n := Nat.log 2 (j - 1)
  have hl : 2^n ≤ j - 1 := Nat.pow_log_le_self 2 (by omega)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (j - 1)
  change j - 1 < 2 ^ (n+1) at hu
  rw [pow_succ] at hu
  exact ⟨n, ⟨j - 1 - 2^n, by omega⟩, by dsimp; omega⟩

private theorem Printed.recurrentRows_contradiction {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hcopy : ∀ (c : ℤ) (η : ℝ), 0 < η → ∃ᶠ n : ℕ in atTop, ∀ (k : Fin (2^n)) (z : ℂ),
      |z.re| ≤ 1 → |z.im - (c : ℝ)| ≤ 1 →
        ‖f (z + ((4 * (((2^n : ℕ) : ℝ) + (k.val : ℝ)) + 2 - (c : ℝ) : ℝ) : ℂ) * Complex.I)
          - f z‖ ≤ η)
    (hseg : ∀ x ∈ Icc (-2 : ℝ) 2, ‖f ((x : ℂ) * Complex.I)‖ ≤ 1)
    (hmark : ∀ j : ℕ, 2 ≤ j →
      3 ≤ ‖f (((4 * (j : ℝ) : ℝ) : ℂ) * Complex.I)‖ ∧
      3 ≤ ‖f (((-(4 * (j : ℝ)) : ℝ) : ℂ) * Complex.I)‖) :
    ¬ Printed.stronglyRecurrentOn_compact_of_closedBall := by
  intro h
  apply Printed.not_stronglyRecurrentOn_segment_of_marks f hseg hmark
  apply h (-(1/2)) (1/2) (by norm_num) f hf.differentiableOn
    (Printed.stronglyRecurrentOn_closedBall_of_copies hf hcopy)
  · exact isCompact_Icc.image (show Continuous (fun x : ℝ ↦ (x : ℂ) * Complex.I) by fun_prop)
  · rintro _ ⟨x, _, rfl⟩
    change -(1/2 : ℝ) < ((x : ℂ) * Complex.I).re ∧ ((x : ℂ) * Complex.I).re < 1/2
    simp

/-- Paper: Lemma B.5.3.4(2), p. 633. The counterexample follows the Runge
construction in ERRATA F22. At stage `L = 2^n`, copy the current entire function
from a rectangle of height two with integer center height to rectangles centered
at heights `4(L + k) + 2` for `0 ≤ k < L`. Keep the approximation on the old
square and prescribe the value four at the new marks on both imaginary tails.
Tau Ceti's polynomial Runge theorem supplies the approximations on each finite
union of rows. The summable errors give an entire limit, and each source
rectangle occurs in arbitrarily late blocks. Every disc inside the strip fits
into a source rectangle with room for a fixed interval of shifts. The segment
`[-2i, 2i]` has bounded return times at tolerance two, because every sufficiently
large translate of the segment meets a mark. -/
theorem Printed.stronglyRecurrentOn_compact_of_closedBall_false :
    ¬ Printed.stronglyRecurrentOn_compact_of_closedBall := by
  let center (n : ℕ) : ℤ := Equiv.intEquivNat.symm (Nat.unpair n).1
  have hcenter (c : ℤ) : ∃ᶠ n in atTop, center n = c := by
    refine frequently_atTop.mpr fun N ↦ ⟨Nat.pair (Equiv.intEquivNat c) N, Nat.right_le_pair _ _, ?_⟩
    simp [center]
  have hε (n : ℕ) : 0 < Printed.recurrentError n - Printed.recurrentError (n + 1) := by
    have hpos : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    change 0 < (1 / 2 : ℝ) ^ (n + 1) - (1 / 2 : ℝ) ^ (n + 1 + 1)
    rw [pow_succ (1 / 2 : ℝ) (n + 1)]
    linarith
  have hex (n : ℕ) (p : {p : ℂ → ℂ // Differentiable ℂ p}) :=
    Printed.recurrentRows_step (2 ^ n) (center n : ℝ) p.val p.property (hε n)
  choose next hnext hstep hcopy hmark using hex
  let seq : ℕ → {p : ℂ → ℂ // Differentiable ℂ p} :=
    Nat.rec ⟨fun _ ↦ 0, differentiable_const 0⟩ (fun n p ↦ ⟨next n p, hnext n p⟩)
  let p (n : ℕ) : ℂ → ℂ := (seq n).val
  have hp (n : ℕ) : Differentiable ℂ (p n) := (seq n).property
  obtain ⟨f, hf, hclose⟩ := Printed.recurrentLimit p hp fun n z hz ↦
    (hstep n (seq n) z hz.1 hz.2).le
  have hside (n : ℕ) : 1 ≤ Printed.recurrentSide n := by
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simp [Printed.recurrentSide]
    linarith
  have hsucc (n : ℕ) : Printed.recurrentSide (n + 1) = 8 * ((2 ^ n : ℕ) : ℝ) := by
    simp [Printed.recurrentSide, pow_succ]
    ring
  refine Printed.recurrentRows_contradiction hf ?_ ?_ ?_
  · intro c η hη
    have hsmall : ∀ᶠ n in atTop, Printed.recurrentError n < η / 2 :=
      Printed.recurrentError_tendsto.eventually_lt_const (half_pos hη)
    have hlarge := Printed.recurrentSide_eventually (|((c : ℤ) : ℝ)| + 1)
    refine ((hcenter c).and_eventually (hsmall.and hlarge)).mono ?_
    rintro n ⟨hnc, hnε, hnc'⟩ k z hzre hzim
    let d : ℝ := 4 * (((2 ^ n : ℕ) : ℝ) + k.val) + 2 - (c : ℝ)
    let w : ℂ := z + (d : ℂ) * Complex.I
    have hz : z ∈ Printed.recurrentSquare n :=
      ⟨hzre.trans (hside n), by
        calc |z.im| = |z.im - (c : ℝ) + (c : ℝ)| := by rw [sub_add_cancel]
             _ ≤ |z.im - (c : ℝ)| + |(c : ℝ)| := abs_add_le ..
             _ ≤ Printed.recurrentSide n := by linarith⟩
    have hwr : w.re = z.re := by simp [w, Complex.mul_re]
    have hwi : w.im = z.im + d := by simp [w, Complex.mul_im]
    have hk : (k.val : ℝ) + 1 ≤ ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast k.isLt
    have hL : (1 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      norm_cast
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    have hw : w ∈ Printed.recurrentSquare (n + 1) := by
      refine ⟨by rw [hwr]; exact hzre.trans (hside _), ?_⟩
      rw [hwi, hsucc, abs_le]
      obtain ⟨hlo, hhi⟩ := abs_le.mp hzim
      have hk₀ : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
      dsimp [d]
      constructor <;> linarith
    have hcop : ‖p (n+1) w - p n z‖ <
      Printed.recurrentError n - Printed.recurrentError (n+1) := by
      simpa [p, seq, w, d, hnc] using
        hcopy n (seq n) k z (hzre.trans (hside n)) (by simpa only [hnc] using hzim)
    have hs := hclose n z hz
    have ht := hclose (n + 1) w hw
    have hh₁ := dist_triangle (f w) (p (n + 1) w) (f z)
    have hh₂ := dist_triangle (p (n + 1) w) (p n z) (f z)
    simp only [dist_eq_norm] at hh₁ hh₂
    rw [norm_sub_rev (p n z) (f z)] at hh₂
    change ‖f w - f z‖ ≤ η
    linarith
  · intro x hx
    have hx' : |x| ≤ 2 := abs_le.mpr hx
    let w : ℂ := (x : ℂ) * Complex.I
    have hw : w ∈ Printed.recurrentSquare 0 := by
      change |w.re| ≤ _ ∧ |w.im| ≤ _
      simpa [w, Printed.recurrentSide, Complex.mul_re, Complex.mul_im] using hx'.trans (by norm_num : (2 : ℝ) ≤ 4)
    have hc := hclose 0 w hw
    change ‖f w - 0‖ ≤ Printed.recurrentError 0 at hc
    norm_num [Printed.recurrentError] at hc
    exact hc.trans (by norm_num)
  · intro j hj
    obtain ⟨n, k, rfl⟩ := Printed.recurrentMarks_cover j hj
    have hmark₁ (s : ℝ) (hs : s = 1 ∨ s = -1) :
        3 ≤ ‖f (((s * (4 * (((2 ^ n : ℕ) : ℝ) + (k.val : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖ := by
      let m : ℝ := 4 * (((2 ^ n : ℕ) : ℝ) + k.val + 1)
      let w : ℂ := ((s * m : ℝ) : ℂ) * Complex.I
      have hk : (k.val : ℝ) + 1 ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast k.isLt
      have hm : m ≤ Printed.recurrentSide (n + 1) := by
        rw [hsucc]
        dsimp [m]
        linarith
      have hm₀ : 0 ≤ m := by dsimp [m]; positivity
      have hw : w ∈ Printed.recurrentSquare (n + 1) := by
        refine ⟨by simp [w, Complex.mul_re, (zero_le_one.trans (hside _))], ?_⟩
        rcases hs with rfl | rfl <;>
          simpa [w, Complex.mul_im, abs_of_nonneg hm₀] using hm
      have he : ‖f w - 4‖ ≤ Printed.recurrentError n := by
        have h₁ := hclose (n + 1) w hw
        have h₂ : ‖p (n + 1) w - 4‖ < Printed.recurrentError n - Printed.recurrentError (n + 1) :=
          hmark n (seq n) k s hs
        have ht := dist_triangle (f w) (p (n + 1) w) 4
        simp only [dist_eq_norm] at ht
        linarith
      have he' : Printed.recurrentError n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have ht := dist_triangle (4 : ℂ) (f w) 0
      simp only [dist_eq_norm, sub_zero, norm_sub_rev 4 (f w)] at ht
      norm_num at ht
      change 3 ≤ ‖f w‖
      linarith
    constructor
    · simpa using hmark₁ 1 (Or.inl rfl)
    · simpa using hmark₁ (-1) (Or.inr rfl)

end RiemannMasullo
