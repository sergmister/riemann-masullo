module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec4

/-! # The printed Fourier cutoff range in §12.4 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped ContDiff NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

/-- Paper: Theorem 12.4.1.1, Step II and (12.4.1.8), pp. 516–517.
As printed: Fourier transformation, multiplication by the smoothed product-norm ball, and
inverse Fourier transformation send every additive S-adelic Schwartz–Bruhat test to another
such test.
Deviation: Footnote 2 on p. 514 requests a one-sided extension of Definition 9.3.3.1.
Keep its parameter bounds and upper transition. For the ball in Step II, take the
profile to be one from zero through L − ε and zero from L onwards.
See `sLocalTraceFourierCutoff` and ERRATA F246. -/
def Printed.sLocalTraceFourierCutoff_preservesSchwartzBruhat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    (∀ v ∉ S, v.asIdeal.ramificationIdx (𝓞 ℚ) = 1) →
    ∀ (L ε : ℝ), 1 < L → 0 < ε → ε < L⁻¹ →
    ∀ (ρ : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1) →
      EqOn ρ 1 (Icc 0 (L - ε)) → (∀ t ≥ L, ρ t = 0) →
      ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
        let symbol := fun u : SAdeleRing F S ↦
          (ρ ((∏ w : InfinitePlace F, ‖u.1 w‖ ^ w.mult) * ∏ v : S, ‖u.2 v‖) : ℂ)
        (fun x : Multiplicative (SAdeleRing F S) ↦ sLocalTraceFourierCutoff symbol f x.toAdd) ∈
          schwartzBruhatSubmodule (G := Multiplicative (SAdeleRing F S))

open Filter MeasureTheory

attribute [local instance] instMeasurableSpaceSAdeleRing

/-- A continuous integrable frequency function is Schwartz–Bruhat if its inverse
Tamagawa transform is Schwartz–Bruhat. -/
private theorem sLocalTraceFourierCutoff_mem_of_inverse_mem {F : Type} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))} (g : SAdeleRing F S → ℂ)
    (hg : Continuous g) (hgi : Integrable g (sAdditiveTamagawaMeasure F S))
    (h : (fun x : Multiplicative (SAdeleRing F S) ↦
      tamagawaFourier (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S)
        g (-x.toAdd)) ∈ schwartzBruhatSubmodule (G := Multiplicative (SAdeleRing F S))) :
    (fun x : Multiplicative (SAdeleRing F S) ↦ g x.toAdd) ∈
      schwartzBruhatSubmodule (G := Multiplicative (SAdeleRing F S)) := by
  classical
  let G := Multiplicative (SAdeleRing F S)
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  let ψ := sAdeleStandardCharacter F S
  let v : SchwartzBruhat G := ⟨_, h⟩
  let u := sAdeleSchwartzFourier v
  let U : G → ℂ := u
  let V : G → ℂ := fun x ↦ g x.toAdd
  have hG := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  let : BorelSpace G := hG.2.2.1
  let : μ.IsHaarMeasure := hG.2.2.2.1
  let : μ.Regular := hG.2.2.2.2
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  have hU : Integrable U μ := (hfourier u).1
  have hV : Integrable V μ := hgi
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  have htransform (χ : PontryaginDual G) : lcaFourier μ U χ = lcaFourier μ V χ := by
    obtain ⟨y, rfl⟩ := e.surjective χ
    have hpair (x : SAdeleRing F S) : e y (Multiplicative.ofAdd x) = ψ (x * y.toAdd) := by
      rw [mul_comm]
      exact he y.toAdd x
    calc
      lcaFourier μ U (e y) =
          tamagawaFourier (R := SAdeleRing F S) μ ψ (fun x ↦ U (Multiplicative.ofAdd x))
            y.toAdd := (tamagawaFourier_eq_lcaFourier (R := SAdeleRing F S) _ _ _ _ _ hpair).symm
      _ = tamagawaFourier (R := SAdeleRing F S) μ ψ g y.toAdd := by
        change sAdeleSchwartzFourier (sAdeleSchwartzFourier v) y =
          tamagawaFourier (R := SAdeleRing F S) μ ψ g y.toAdd
        have hi := sLocal_fourier_inversion v y.toAdd
        change sAdeleSchwartzFourier (sAdeleSchwartzFourier v) y =
          tamagawaFourier (R := SAdeleRing F S) μ ψ g (-(-y.toAdd)) at hi
        rw [neg_neg] at hi
        exact hi
      _ = lcaFourier μ V (e y) := tamagawaFourier_eq_lcaFourier (R := SAdeleRing F S) _ _ _ _ _ hpair
  obtain ⟨Φ, hΦ, hinj, -⟩ := lcaFourier_L1 (G := G) μ
  have hcoe (w : G → ℂ) (hw : Integrable w μ) (χ : PontryaginDual G) :
      Φ (hw.toL1 w) χ = lcaFourier μ w χ := by
    rw [hΦ]
    exact integral_congr_ae (hw.coeFn_toL1.mono fun y hy ↦ congrArg (· * star (χ y : ℂ)) hy)
  have hL1 : hU.toL1 U = hV.toL1 V :=
    hinj (ZeroAtInftyContinuousMap.ext fun χ ↦ by rw [hcoe, hcoe, htransform])
  have hae : U =ᵐ[μ] V := (Integrable.toL1_eq_toL1_iff U V hU hV).mp hL1
  have heq : U = V := Measure.eq_of_ae_eq hae (schwartzBruhat_continuous u) hg
  exact (congrArg (· ∈ schwartzBruhatSubmodule G) heq).mp u.property

/-- For the rational adeles with a nonempty finite place set, the product-norm cutoff
can destroy the common finite-place period of a Schwartz–Bruhat frequency test.
One can take a Gaussian in the real coordinate and the integer-ring indicator at
the finite places. Compare the all-zero finite tuple with an arbitrarily small
tuple whose coordinates are all nonzero, at a real frequency where the latter
product norm is at least two. -/
private theorem sLocalTraceFourierCutoff_frequency_witness
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} (hS : S.Nonempty) :
    ∃ b : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S)),
      let g := fun u : SAdeleRing ℚ S ↦
        (Real.smoothTransition (4 * (2 -
          ((∏ w : InfinitePlace ℚ, ‖u.1 w‖ ^ w.mult) * ∏ v : S, ‖u.2 v‖))) : ℂ) *
          b (Multiplicative.ofAdd (-u))
      (fun x : Multiplicative (SAdeleRing ℚ S) ↦ g x.toAdd) ∉
          schwartzBruhatSubmodule (G := Multiplicative (SAdeleRing ℚ S)) := by
  classical
  let A := Multiplicative (InfiniteAdeleRing ℚ)
  let H := Multiplicative (FinitePlaceProduct ℚ S)
  let : T2Space A := inferInstanceAs (T2Space ((w : InfinitePlace ℚ) → w.Completion))
  let : LocallyCompactSpace A :=
    inferInstanceAs (LocallyCompactSpace ((w : InfinitePlace ℚ) → w.Completion))
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology A :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion))
  let : T2Space H := inferInstanceAs (T2Space (∀ w : S, w.val.adicCompletion ℚ))
  let : TotallyDisconnectedSpace H :=
    inferInstanceAs (TotallyDisconnectedSpace (∀ w : S, w.val.adicCompletion ℚ))
  obtain ⟨e, he⟩ := kernel_with_finitePlaceProduct ℚ S (archFiniteProductEquiv ℚ S)
  have hSlice (q : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
      ∀ᶠ z : FinitePlaceProduct ℚ S in 𝓝 0, ∀ x : InfiniteAdeleRing ℚ,
        q (Multiplicative.ofAdd ((x, z) : SAdeleRing ℚ S)) =
          q (Multiplicative.ofAdd ((x, 0) : SAdeleRing ℚ S)) := by
    obtain ⟨t, rfl⟩ := e.surjective q
    let P (t : SchwartzBruhat A ⊗[ℂ] SchwartzBruhat H) : Prop :=
      ∀ᶠ z : FinitePlaceProduct ℚ S in 𝓝 0, ∀ x : InfiniteAdeleRing ℚ,
        e t (Multiplicative.ofAdd ((x, z) : SAdeleRing ℚ S)) =
          e t (Multiplicative.ofAdd ((x, 0) : SAdeleRing ℚ S))
    change P t
    refine TensorProduct.inductionOn (motive := P) t ?_ ?_
    all_goals dsimp only [P]
    · intro f g
      have hg := (schwartzBruhat_locallyConstant_compactSupport
        (finitePlaceProduct_compact_subset_subgroup ℚ S) g).1.eventually_eq
          (Multiplicative.ofAdd (0 : FinitePlaceProduct ℚ S))
      filter_upwards [hg] with z hz x
      rw [he, he]
      exact congrArg (f (Multiplicative.ofAdd x) * ·) hz
    · intro t₁ t₂ h₁ h₂
      filter_upwards [h₁, h₂] with z hz₁ hz₂ x
      rw [show e (t₁ + t₂) = e t₁ + e t₂ from map_add e t₁ t₂]
      exact congrArg₂ (· + ·) (hz₁ x) (hz₂ x)
  let w := Rat.infinitePlace
  let : Unique (InfinitePlace ℚ) := ⟨⟨w⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let d : A ≃ₜ* Multiplicative w.Completion :=
    { Homeomorph.piUnique InfinitePlace.Completion with map_mul' := fun _ _ ↦ rfl }
  let : LocallyCompactSpace (Multiplicative w.Completion) :=
    inferInstanceAs (LocallyCompactSpace w.Completion)
  let : T2Space (Multiplicative w.Completion) := inferInstanceAs (T2Space w.Completion)
  let a₀ := infiniteStandardGaussian w 1
  let a : SchwartzBruhat A := ⟨a₀.val ∘ d, schwartzBruhat_mem_comp_equiv d a₀.property⟩
  obtain ⟨c, hc⟩ := finitePlaceProduct_indicator ℚ S
  let b := e (a ⊗ₜ[ℂ] c)
  refine ⟨b, fun h ↦ ?_⟩
  let Q : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S)) := ⟨_, h⟩
  obtain ⟨v, hv⟩ := hS
  have hSmall (j : S) : ∃ p : j.val.adicCompletion ℚ, p ≠ 0 ∧ ‖p‖ < 1 := by
    let val : Valuation (j.val.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨p, hp⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    refine ⟨p, hp.ne_zero, ?_⟩
    rw [norm_uniformizer_adicCompletion (K := ℚ) j.val (p : j.val.adicCompletion ℚ) hp]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm j.val)
  choose p hp0 hpNorm using hSmall
  have hTendsto : Tendsto (fun n : ℕ ↦ fun j : S ↦ p j ^ n) atTop
      (𝓝 (0 : FinitePlaceProduct ℚ S)) :=
    tendsto_pi_nhds.mpr fun j ↦ tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hpNorm j)
  obtain ⟨n, hn⟩ := (hTendsto.eventually (hSlice Q)).exists
  let z : FinitePlaceProduct ℚ S := fun j ↦ p j ^ n
  let N : ℝ := ∏ j : S, ‖z j‖
  have hN : 0 < N := Finset.prod_pos fun j _ ↦ norm_pos_iff.mpr (pow_ne_zero _ (hp0 j))
  have hZero : (∏ j : S, ‖(0 : FinitePlaceProduct ℚ S) j‖) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨v, hv⟩ : S)) (by simp)
  let iso := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let x : InfiniteAdeleRing ℚ :=
    Pi.single w (iso.symm (2 / N))
  have hx : (∏ j : InfinitePlace ℚ, ‖x j‖ ^ j.mult) = 2 / N := by
    rw [Finset.univ_unique, Finset.prod_singleton]
    change ‖x w‖ ^ w.mult = 2 / N
    have hm : w.mult = 1 := Rat.isReal_infinitePlace.mult_eq_one
    rw [hm, pow_one]
    have hxi : x w = iso.symm (2 / N) :=
      Pi.single_eq_same _ _
    have hi0 : iso (0 : w.Completion) = 0 :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).map_zero
    rw [hxi, ← iso.isometry.norm_map_of_map_zero hi0 _, iso.apply_symm_apply,
      Real.norm_of_nonneg (by positivity)]
  have hxlarge : (∏ j : InfinitePlace ℚ, ‖x j‖ ^ j.mult) * N = 2 := by
    rw [hx, div_mul_cancel₀ _ hN.ne']
  have hbzero : b (Multiplicative.ofAdd (-((x, 0) : SAdeleRing ℚ S))) ≠ 0 := by
    rw [he, archFiniteProductEquiv_fst]
    have hc0 : ((archFiniteProductEquiv ℚ S)
        (Multiplicative.ofAdd (-((x, 0) : SAdeleRing ℚ S)))).2 =
        Multiplicative.ofAdd (0 : FinitePlaceProduct ℚ S) := by
      change Multiplicative.ofAdd (-(0 : FinitePlaceProduct ℚ S)) = _
      rw [neg_zero]
    have hIntegral : ∀ j : S,
        (0 : FinitePlaceProduct ℚ S) j ∈ j.val.adicCompletionIntegers ℚ :=
      fun j ↦ (j.val.adicCompletionIntegers ℚ).zero_mem
    rw [hc0, hc, ite_eq_left hIntegral, mul_one]
    change infiniteStandardGaussianValue w 1 ((-x) w) ≠ 0
    simp [infiniteStandardGaussianValue, w, Rat.isReal_infinitePlace]
  have heq := hn x
  change
    (Real.smoothTransition (4 * (2 - (∏ j : InfinitePlace ℚ, ‖x j‖ ^ j.mult) * N)) : ℂ) *
        b (Multiplicative.ofAdd (-((x, z) : SAdeleRing ℚ S))) =
      (Real.smoothTransition (4 * (2 - (∏ j : InfinitePlace ℚ, ‖x j‖ ^ j.mult) *
        (∏ j : S, ‖(0 : FinitePlaceProduct ℚ S) j‖))) : ℂ) *
        b (Multiplicative.ofAdd (-((x, 0) : SAdeleRing ℚ S))) at heq
  rw [hxlarge, hZero, mul_zero,
    Real.smoothTransition.zero_of_nonpos (by norm_num : 4 * (2 - 2) ≤ (0 : ℝ)),
    Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 4 * (2 - 0))] at heq
  exact hbzero (by simpa using heq.symm)

/-- Paper: Theorem 12.4.1.1, Step II and (12.4.1.8), pp. 516–517.
Take `F = ℚ`, `S = {∞, 2}`, `L = 2` and `ε = 1/4`. For `β(t) = exp(−1/t)` at `t > 0`
and zero elsewhere, use `ρ(t) = β(2−t)/(β(2−t)+β(t−7/4))`. Take the test `b'' ⊗ 1_{ℤ₂ˣ}`,
where `b(x) = exp(−1/((x−1)(2−x)))` on `(1,2)` and zero elsewhere. The test vanishes
near either coordinate origin and has integral zero. Its Fourier transform has a nonzero
entire real factor and a finite factor equal to `1/2` on `ℤ₂`.
For any proposed period subgroup `2ᴺ ℤ₂`, choose `k ≥ max(N,0)` and compare the
frequencies `2ᵏ` and `2ᵏ⁺²`. For real frequencies near `3 · 2ᵏ`, the two product norms
lie on opposite plateaux, and the real Fourier factor is nonzero somewhere in that interval.
The multiplied transform has no common finite-place period. It is continuous and integrable,
so if its inverse transform were Schwartz–Bruhat, Fourier inversion would recover it pointwise
as a Schwartz–Bruhat transform. -/
theorem Printed.sLocalTraceFourierCutoff_preservesSchwartzBruhat_false :
    ¬ Printed.sLocalTraceFourierCutoff_preservesSchwartzBruhat := by
  intro h
  classical
  have hp : Prime ((2 : ℕ) : 𝓞 ℚ) := RatRingOfIntegers.prime_natCast_iff.mpr Nat.prime_two
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨Ideal.span {((2 : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp,
      fun h ↦ hp.ne_zero (Ideal.span_singleton_eq_bot.mp h)⟩
  obtain ⟨T, hT⟩ := eventually_trivial_sIdealClassGroup ℚ
  let S := insert v T
  have hv : v ∈ S := Finset.mem_insert_self _ _
  have hPic := hT S (Finset.subset_insert _ _)
  have hRam (w : HeightOneSpectrum (𝓞 ℚ)) (_hw : w ∉ S) :
      w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 := by
    exact Ideal.ramificationIdx_eq_one (R := 𝓞 ℚ) (q := w.asIdeal)
  obtain ⟨b, hNotMem⟩ := sLocalTraceFourierCutoff_frequency_witness ⟨v, hv⟩
  let f := sAdeleSchwartzFourier b
  let ρ : ℝ → ℝ := fun t ↦ Real.smoothTransition (4 * (2 - t))
  have hSmooth : ContDiff ℝ (∞ : ℕ∞ω) ρ :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
  have hBounds (t : ℝ) : 0 ≤ ρ t ∧ ρ t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hOne : EqOn ρ 1 (Icc 0 (2 - 1 / 4)) := by
    intro t ht
    exact Real.smoothTransition.one_of_one_le (by linarith [ht.2])
  have hZero (t : ℝ) (ht : 2 ≤ t) : ρ t = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hMem := h ℚ S hPic hRam 2 (1 / 4) (by norm_num) (by norm_num)
    (by norm_num) ρ hSmooth hBounds hOne hZero f
  let A := SAdeleRing ℚ S
  let G := Multiplicative A
  let μ : Measure G := sAdditiveTamagawaMeasure ℚ S
  let symbol (u : A) : ℂ :=
    ρ ((∏ w : InfinitePlace ℚ, ‖u.1 w‖ ^ w.mult) * ∏ w : S, ‖u.2 w‖)
  have hSymbol : Continuous symbol := by
    refine Complex.continuous_ofReal.comp (hSmooth.continuous.comp
      ((continuous_finsetProd _ fun w _ ↦ ?_).mul
        (continuous_finsetProd _ fun w _ ↦ ?_)))
    · exact (((continuous_apply w).comp continuous_fst).norm).pow _
    · exact ((continuous_apply w).comp continuous_snd).norm
  have hFourier : Continuous (fun u : A ↦ sAdeleSchwartzFourier f (Multiplicative.ofAdd u)) :=
    schwartzBruhat_continuous (sAdeleSchwartzFourier f)
  have hG := sAdele_fourierMeasure (F := ℚ) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  let : BorelSpace G := hG.2.2.1
  let : μ.IsHaarMeasure := hG.2.2.2.1
  let : μ.Regular := hG.2.2.2.2
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  have hIntegrable : Integrable (fun u : A ↦
      symbol u * sAdeleSchwartzFourier f (Multiplicative.ofAdd u)) μ := by
    have hBound : ∀ᵐ u ∂μ, ‖symbol u‖ ≤ 1 := .of_forall fun u ↦ by
      simp only [symbol, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hBounds _).1]
      exact (hBounds _).2
    have hSymbolG : Continuous (fun u : G ↦ symbol u.toAdd) := hSymbol
    exact (hfourier (sAdeleSchwartzFourier f)).1.bdd_mul hSymbolG.aestronglyMeasurable hBound
  apply hNotMem
  have hFrequency := sLocalTraceFourierCutoff_mem_of_inverse_mem _
    (hSymbol.mul hFourier) hIntegrable hMem
  have hEq : (fun u : G ↦ symbol u.toAdd * sAdeleSchwartzFourier f u) =
      fun u : G ↦ symbol u.toAdd * b (Multiplicative.ofAdd (-u.toAdd)) :=
    funext fun u ↦ congrArg (symbol u.toAdd * ·) (sLocal_fourier_inversion b u.toAdd)
  rw [← hEq]
  exact hFrequency

end RiemannMasullo
