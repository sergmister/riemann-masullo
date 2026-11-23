module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Chapter 2.2: printed convergence and fractional ideal bounds -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function IsDedekindDomain NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Pointwise nonZeroDivisors

/-- Paper: Proposition 2.2.1.3, p. 76. As printed: for every full lattice, every norm
inducing the Euclidean topology, and every compact set K, the sum of ‖ξ + x‖^(-σ)
over lattice points outside K is finite when x is in K and σ exceeds the dimension.
This is the pointwise convergence clause of (2.2.1.3), recorded at the
Proposition 2.2.1.3 TODO in `Sec2a.lean`. See ERRATA F207. -/
def Printed.latticeShiftedPowerSum_converges : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    ∀ (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
      (p : Seminorm ℝ (Fin N → ℝ)), (∀ x, p x = 0 → x = 0) →
      WithSeminorms (fun _ : Unit ↦ p) →
      ∀ (K : Set (Fin N → ℝ)), IsCompact K →
        ∀ (σ : ℝ), (N : ℝ) < σ → ∀ x ∈ K,
          (∑' ξ : ↥((Γ : Set (Fin N → ℝ)) \ K), (ENNReal.ofReal (p (ξ.val + x))) ^ (-σ)) < ⊤

/-- Paper: Proposition 2.2.1.3, p. 76. In dimension one, take the integer lattice,
the absolute value, K = {1}, x = 1 and σ = 2. The index ξ = −1 remains in the
sum and its extended nonnegative real term is 0^(-2) = ∞. -/
theorem Printed.latticeShiftedPowerSum_converges_false :
    ¬ Printed.latticeShiftedPowerSum_converges := by
  intro h
  let b := Pi.basisFun ℝ (Fin 1)
  let x₀ : Fin 1 → ℝ := fun _ ↦ 1
  have hx₀ : x₀ ∈ (Submodule.span ℤ (Set.range b) : Set (Fin 1 → ℝ)) :=
    Submodule.subset_span ⟨0, by funext i; fin_cases i; simp [b, x₀]⟩
  have hmem : -x₀ ∈ ((Submodule.span ℤ (Set.range b) : Set (Fin 1 → ℝ)) \ {x₀}) := by
    refine ⟨neg_mem hx₀, fun hc ↦ ?_⟩
    have := congrFun (Set.mem_singleton_iff.mp hc) 0
    simp [x₀] at this
    norm_num at this
  have hlt := h 1 le_rfl (Submodule.span ℤ (Set.range b)) (normSeminorm ℝ (Fin 1 → ℝ))
    (fun x hx ↦ norm_eq_zero.mp hx) (norm_withSeminorms ℝ (Fin 1 → ℝ)) {x₀}
    isCompact_singleton 2 (by norm_num) x₀ rfl
  refine hlt.ne (eq_top_iff.mpr ?_)
  have hterm : (ENNReal.ofReal (normSeminorm ℝ (Fin 1 → ℝ) ((-x₀) + x₀))) ^ (-(2 : ℝ)) = ⊤ := by
    rw [neg_add_cancel, map_zero, ENNReal.ofReal_zero]
    exact ENNReal.zero_rpow_of_neg (by norm_num)
  rw [← hterm]
  exact le_tsum (fun ξ : ↥((Submodule.span ℤ (Set.range b) : Set (Fin 1 → ℝ)) \ {x₀}) ↦
    (ENNReal.ofReal (normSeminorm ℝ (Fin 1 → ℝ) (ξ.val + x₀))) ^ (-(2 : ℝ))) ⟨_, hmem⟩

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "ℬ(" X ")" => SchwartzBruhat (Multiplicative X)

set_option maxSynthPendingDepth 3 in
/-- Paper: Lemma 2.2.2.1(3), p. 78. As printed: for each number field and each
Schwartz–Bruhat product (2.2.2.2), one fractional ideal bounds the sum (2.2.2.3)
for every idele whose archimedean projection belongs to T∞·E∞. Here T∞ is the
image of a chosen continuous homomorphic section of the archimedean norm and E∞
is the projection of the chosen norm-one fundamental domain. See
`adelicAverage_at_zero_le_fractionalIdeal` and ERRATA F208. -/
def Printed.adelicAverage_at_zero_le_fractionalIdeal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : CommRing.Pic (𝓞 F) → (ideleNorm F).ker), r 1 = 1 →
    (∀ c, ideleIdealClass F (r c).val = c) →
    ∀ (τ : ℝ≥0ˣ →ₜ* (InfiniteAdeleRing F)ˣ), RightInverse τ (infiniteIdeleNorm F) →
      ∀ (f : ℬ(𝔸[F])) (arch : ℬ(InfiniteAdeleRing F))
        (K : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)),
        (∀ v, IsCompact (K v) ∧ IsOpen (K v) ∧
          K v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
        (∀ᶠ v in cofinite, K v = (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
        (∀ x : 𝔸[F], f (Multiplicative.ofAdd x) = arch (Multiplicative.ofAdd x.1) *
          Set.indicator {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K v} (fun _ ↦ (1 : ℂ)) x.2) →
        ∃ I : FractionalIdeal (𝓞 F)⁰ F,
          let atInfinity := Units.map (RingHom.fst (InfiniteAdeleRing F)
            (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
          let archDomain := (atInfinity.comp (ideleNorm F).ker.subtype) ''
            ideleFundamentalDomain F b v₀ σ r
          ∀ (g : 𝕀[F]), atInfinity g ∈ range τ * archDomain →
            (∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖) ≤
              ∑' ξ : {ξ : Fˣ // (ξ : F) ∈ I},
                ‖arch (Multiplicative.ofAdd
                  (g.val.1 * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖

open scoped Classical in
/-- The bump on the mixed space of ℚ equal to one on the closed unit ball and zero
outside the ball of radius two. -/
private noncomputable def ratBump : ContDiffBump (0 : mixedEmbedding.mixedSpace ℚ) :=
  ⟨1, 2, one_pos, one_lt_two⟩

open scoped Classical in
/-- The bump as a complex Schwartz function. -/
private noncomputable def ratBumpSchwartz : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ :=
  HasCompactSupport.toSchwartzMap (f := fun x ↦ ((ratBump x : ℝ) : ℂ))
    (ratBump.hasCompactSupport.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp ratBump.contDiff)

open scoped Classical in
/-- The bump as an archimedean Schwartz–Bruhat function over ℚ. -/
private noncomputable def ratArch : ℬ(InfiniteAdeleRing ℚ) :=
  ⟨fun x ↦ ratBumpSchwartz (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.toAdd),
    (mem_archimedeanSchwartzBruhat_iff _).mpr ⟨ratBumpSchwartz, fun _ ↦ rfl⟩⟩

open scoped Classical in
private theorem ratArch_apply (x : InfiniteAdeleRing ℚ) :
    ratArch (Multiplicative.ofAdd x) =
      ((ratBump (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x) : ℝ) : ℂ) := rfl

open scoped Classical in
/-- The adelic test `ratArch ⊗ 1_{Ẑ}` over ℚ. -/
private theorem exists_ratTest : ∃ f : ℬ(𝔸[ℚ]), ∀ x : 𝔸[ℚ],
    f (Multiplicative.ofAdd x) = ratArch (Multiplicative.ofAdd x.1) *
      Set.indicator {y : 𝔸ᶠ[ℚ] | ∀ v, y v ∈
        ((fun v : HeightOneSpectrum (𝓞 ℚ) ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) v)}
        (fun _ ↦ (1 : ℂ)) x.2 := by
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  let g : ∀ w : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))), ℬ(w.val.adicCompletion ℚ) :=
    fun w ↦ absurd w.2 (Finset.notMem_empty _)
  refine ⟨sAdeleSchwartzToGlobal ℚ ∅ (e (ratArch ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))), fun x ↦ ?_⟩
  rw [sAdeleSchwartzToGlobal_apply, he]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.notMem_empty,
    not_false_eq_true, forall_const]
  by_cases hx : ∀ v : HeightOneSpectrum (𝓞 ℚ), x.2 v ∈ v.adicCompletionIntegers ℚ
  · rw [ite_eq_left hx, Set.indicator_of_mem (show x.2 ∈ _ from hx), mul_one]
    rfl
  · rw [ite_eq_right hx, Set.indicator_of_notMem (show x.2 ∉ _ from hx), mul_zero]

open scoped Classical in
private theorem ratArch_algebraMap_norm_of_le (ξ : ℚ) (h : |ξ| ≤ 1) :
    ‖ratArch (Multiplicative.ofAdd (algebraMap ℚ (InfiniteAdeleRing ℚ) ξ))‖ = 1 := by
  rw [ratArch_apply, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
    ratBump.one_of_mem_closedBall, Complex.ofReal_one, norm_one]
  rw [mem_closedBall_zero_iff, mixedEmbedding.norm_eq_sup'_normAtPlace]
  simp only [mixedEmbedding.normAtPlace_apply, Rat.infinitePlace_apply, Finset.sup'_const]
  change ((|ξ| : ℚ) : ℝ) ≤ 1
  exact_mod_cast h

open scoped Classical in
private theorem ratArch_algebraMap_eq_zero (ξ : ℚ) (h : 2 ≤ |ξ|) :
    ratArch (Multiplicative.ofAdd (algebraMap ℚ (InfiniteAdeleRing ℚ) ξ)) = 0 := by
  rw [ratArch_apply, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
    ratBump.zero_of_le_dist, Complex.ofReal_zero]
  rw [dist_zero_right, mixedEmbedding.norm_eq_sup'_normAtPlace]
  simp only [mixedEmbedding.normAtPlace_apply, Rat.infinitePlace_apply, Finset.sup'_const]
  change (2 : ℝ) ≤ ((|ξ| : ℚ) : ℝ)
  exact_mod_cast h

/-- A continuous section of the archimedean norm over ℚ. -/
private noncomputable def ratSection : ℝ≥0ˣ →ₜ* (InfiniteAdeleRing ℚ)ˣ :=
  { toMonoidHom := (Units.map (RingHom.fst (InfiniteAdeleRing ℚ)
        (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom).comp
          (singlePlaceIdeleNormSection ℚ Rat.infinitePlace)
    continuous_toFun := (continuous_fst.units_map _).comp
      (singlePlaceIdeleNormSection_continuous ℚ Rat.infinitePlace) }

private theorem ratSection_rightInverse : RightInverse ratSection (infiniteIdeleNorm ℚ) := by
  intro t
  rw [infiniteIdeleNorm_eq_global]
  exact singlePlaceIdeleNormSection_rightInverse ℚ Rat.infinitePlace t

/-- The idele with archimedean component one and finite components the diagonal `q`. -/
private noncomputable def ratIdele (q : ℚ) (hq : q ≠ 0) : IdeleGroup (𝓞 ℚ) ℚ :=
  ⟨(1, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q), (1, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q⁻¹),
    Prod.ext (mul_one 1) (by
      change algebraMap ℚ _ q * algebraMap ℚ _ q⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hq, map_one]),
    Prod.ext (mul_one 1) (by
      change algebraMap ℚ _ q⁻¹ * algebraMap ℚ _ q = 1
      rw [← map_mul, inv_mul_cancel₀ hq, map_one])⟩

/-- A rational number integral at every prime is an integer. -/
private theorem rat_exists_int_of_forall_mem {ξ : ℚ}
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ξ v ∈ v.adicCompletionIntegers ℚ) :
    ∃ n : ℤ, ξ = n := by
  have hr : ξ ∈ (algebraMap (𝓞 ℚ) ℚ).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ ξ fun v => ?_
    have := h v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact this
  obtain ⟨z, rfl⟩ := hr
  refine ⟨Rat.ringOfIntegersEquiv z, ?_⟩
  conv_lhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply z]
  generalize Rat.ringOfIntegersEquiv z = n
  rw [show Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) from
    eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) n, map_intCast]

private theorem rat_intCast_mem (n : ℤ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ) v ∈ v.adicCompletionIntegers ℚ := by
  rw [map_intCast]
  exact intCast_mem _ n

private theorem one_mem_ideleFundamentalDomain (F : Type) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) (r : CommRing.Pic (𝓞 F) → (ideleNorm F).ker)
    (hr₁ : r 1 = 1) :
    (1 : (ideleNorm F).ker) ∈ ideleFundamentalDomain F b v₀ σ r := by
  unfold ideleFundamentalDomain
  refine Set.mem_iUnion.mpr ⟨1, ?_⟩
  rw [hr₁, one_smul]
  refine ⟨one_mem _, ?_⟩
  have h := (unit_mem_infiniteIdeleFundamentalDomain F b v₀ σ (1 : (𝓞 F)ˣ)).mpr rfl
  rw [map_one] at h
  simpa using h

/-- Paper: Lemma 2.2.2.1(3), p. 78. Over ℚ take the norm section through the real
place, any norm-one domain (it contains one), Kᵥ = ℤᵥ at every prime, and f∞ a smooth
bump on ℝ equal to one on [−1, 1] and zero outside (−2, 2). For an integer N ≥ 1 the
idele g with g∞ = 1 and diagonal finite components N is allowed. The left sum is a
finite sum over ξ ∈ N⁻¹ℤ − {0} and is at least N, from ξ = k/N with 0 < k ≤ N, while
the right side does not depend on N. -/
theorem Printed.adelicAverage_at_zero_le_fractionalIdeal_false :
    ¬ Printed.adelicAverage_at_zero_le_fractionalIdeal := by
  classical
  intro H
  obtain ⟨r, hr₁, hr⟩ := exists_normOne_class_representatives ℚ
  obtain ⟨f, hf⟩ := exists_ratTest
  have hK : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ∧
        IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ∧
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ⊆ v.adicCompletionIntegers ℚ :=
    fun v ↦ ⟨isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v),
      Valued.isOpen_valuationSubring _, subset_rfl⟩
  obtain ⟨I, hI⟩ := H ℚ (Units.basisModTorsion ℚ) Rat.infinitePlace AlgEquiv.refl r hr₁ hr
    ratSection ratSection_rightInverse f ratArch
    (fun v ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) hK
    (Eventually.of_forall fun _ ↦ rfl) hf
  set R₀ : ℝ := ∑' ξ : {ξ : ℚˣ // (ξ : ℚ) ∈ I}, ‖ratArch (Multiplicative.ofAdd
    ((1 : InfiniteAdeleRing ℚ) * algebraMap ℚ (InfiniteAdeleRing ℚ) (ξ.val : ℚ)))‖ with hR₀
  have hmem (N : ℕ) (hN : (N : ℚ) ≠ 0) :
      Units.map (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
          (ratIdele N hN) ∈ Set.range ratSection *
        ((Units.map (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom).comp
          (ideleNorm ℚ).ker.subtype ''
          ideleFundamentalDomain ℚ (Units.basisModTorsion ℚ) Rat.infinitePlace AlgEquiv.refl r) := by
    have h1 : Units.map (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom
        (ratIdele N hN) = 1 := Units.ext rfl
    rw [h1]
    exact ⟨1, ⟨1, map_one _⟩, 1, ⟨1, one_mem_ideleFundamentalDomain ℚ _ _ _ r hr₁, map_one _⟩,
      one_mul 1⟩
  have key (N : ℕ) (hN : 0 < N) : (N : ℝ) ≤ R₀ := by
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hle := hI (ratIdele N hNq) (hmem N hNq)
    let T : ℚˣ → ℝ := fun ξ ↦
      ‖ratArch (Multiplicative.ofAdd (algebraMap ℚ (InfiniteAdeleRing ℚ) (ξ : ℚ)))‖ *
        (if ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
          ((N : ℚ) * ξ) v ∈ v.adicCompletionIntegers ℚ then 1 else 0)
    have hT (ξ : ℚˣ) : ‖f (Multiplicative.ofAdd ((ratIdele N hNq).val *
        algebraMap ℚ 𝔸[ℚ] (ξ : ℚ)))‖ = T ξ := by
      have e1 : ((ratIdele N hNq).val * algebraMap ℚ 𝔸[ℚ] (ξ : ℚ)).1 =
          algebraMap ℚ (InfiniteAdeleRing ℚ) ξ := one_mul _
      have e2 : ((ratIdele N hNq).val * algebraMap ℚ 𝔸[ℚ] (ξ : ℚ)).2 =
          algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((N : ℚ) * ξ) := (map_mul _ _ _).symm
      rw [hf, e1, e2, norm_mul]
      congr 1
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs with h₁ h₂ h₂ <;> first | exact absurd h₁ h₂ | exact absurd h₂ h₁ | simp
    have hT0 (ξ : ℚˣ) : 0 ≤ T ξ := by
      refine mul_nonneg (norm_nonneg _) ?_
      split_ifs <;> norm_num
    have hfin : (Units.val ⁻¹' ((fun n : ℤ ↦ (n : ℚ) / N) ''
        (Finset.Icc (-2 * (N : ℤ)) (2 * N) : Set ℤ))).Finite :=
      ((Finset.Icc _ _).finite_toSet.image _).preimage Units.val_injective.injOn
    have hTs : Summable T := by
      refine summable_of_ne_finset_zero (s := hfin.toFinset) fun ξ hξ ↦ ?_
      by_contra hne
      apply hξ
      rw [Set.Finite.mem_toFinset]
      have hint : ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
          ((N : ℚ) * ξ) v ∈ v.adicCompletionIntegers ℚ := by
        by_contra h
        exact hne (by simp only [T, ite_eq_right h, mul_zero])
      have hsmall : |(ξ : ℚ)| < 2 := by
        by_contra h
        exact hne (by simp only [T, ratArch_algebraMap_eq_zero _ (not_lt.mp h), norm_zero, zero_mul])
      obtain ⟨n, hn⟩ := rat_exists_int_of_forall_mem hint
      have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
      have hξ' : (ξ : ℚ) = n / N := by field_simp; linarith
      refine ⟨n, ?_, hξ'.symm⟩
      have habs : |(n : ℚ)| < 2 * N := by
        rw [← hn, abs_mul, abs_of_pos hNpos]; nlinarith [abs_nonneg (ξ : ℚ)]
      have habs' : |n| < 2 * (N : ℤ) := by exact_mod_cast habs
      rw [Finset.coe_Icc, Set.mem_Icc]
      constructor <;> linarith [abs_lt.mp habs']
    have hlow : (N : ℝ) ≤ ∑' ξ, T ξ := by
      have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
      let u : Fin N → ℚˣ := fun k ↦ Units.mk0 ((((k : ℕ) : ℚ) + 1) / N) (by positivity)
      have hu : Injective u := by
        intro k k' h
        have h' := congrArg Units.val h
        simp only [u, Units.val_mk0] at h'
        rw [div_left_inj₀ hNq] at h'
        exact Fin.ext (by exact_mod_cast add_right_cancel h')
      have hone (k : Fin N) : T (u k) = 1 := by
        have hk : ((k : ℕ) : ℚ) + 1 ≤ N := by exact_mod_cast k.isLt
        have hab : |(u k : ℚ)| ≤ 1 := by
          simp only [u, Units.val_mk0]
          rw [abs_of_pos (by positivity), div_le_one hNpos]
          exact hk
        have hint : ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
            ((N : ℚ) * (u k : ℚ)) v ∈ v.adicCompletionIntegers ℚ := by
          have e : (N : ℚ) * (u k : ℚ) = (((k : ℕ) + 1 : ℤ) : ℚ) := by
            simp only [u, Units.val_mk0]; push_cast; field_simp
          rw [e]
          exact rat_intCast_mem _
        simp only [T, ite_eq_left hint, mul_one]
        exact ratArch_algebraMap_norm_of_le _ hab
      have h := tsum_comp_le_tsum_of_inj hTs hT0 hu
      rw [tsum_fintype] at h
      simp only [Function.comp_apply, hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at h
      exact h
    calc (N : ℝ) ≤ ∑' ξ, T ξ := hlow
      _ = _ := (tsum_congr hT).symm
      _ ≤ R₀ := hle
  have h := key (⌈R₀⌉₊ + 1) (Nat.succ_pos _)
  push_cast at h
  linarith [Nat.le_ceil R₀]

end RiemannMasullo
