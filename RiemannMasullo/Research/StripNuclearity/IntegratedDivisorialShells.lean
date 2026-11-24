module

public import RiemannMasullo.Ch11_ShellStructure.Sec3
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Integration of the primary divisorial shells

An idèle exits the nested strata at most once. On its exit shell the difference
of the kernels is the negative of the pulled-back kernel. Integration on these
disjoint measurable shells gives both the signed trace integral and an exact
sum of the L¹ masses. The measure may live on any space mapping to idèle pairs.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I𝔽" => IdeleGroup (𝓞 F) F
attribute [local instance] instIdeleMeasurableSpaceSec1a
local instance integratedShellBorel : BorelSpace I𝔽 := ⟨rfl⟩

private theorem iUnion_exit_shells {X : Type*} (E : ℕ → Set X) (h₀ : E 0 = univ) :
    (⋃ n, E n \ E (n+1)) = (⋂ n, E n)ᶜ := by
  ext x
  constructor
  · intro hx hall
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact hn.2 (mem_iInter.mp hall (n+1))
  · intro hx
    by_contra h
    apply hx
    refine mem_iInter.mpr (fun n ↦ ?_)
    induction n with
    | zero => simp [h₀]
    | succ n ih =>
      by_contra hn
      exact h (mem_iUnion.mpr ⟨n, ih, hn⟩)

private theorem pairwise_disjoint_exit_shells {X : Type*} (E : ℕ → Set X) (h : Antitone E) :
    Pairwise (Disjoint on fun n ↦ E n \ E (n+1)) := by
  have hlt {i j : ℕ} (hij : i < j) : Disjoint (E i \ E (i+1)) (E j \ E (j+1)) :=
    disjoint_left.mpr (fun _ hi hj ↦ hi.2 (h (Nat.succ_le_of_lt hij) hj.1))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact hlt h'
  · exact (hlt h').symm

/-- Paper: (11.3.1.4), p. 494, and the first diagonal decomposition on p. 520.
Pull back an idèlic kernel along a map to pairs of idèles. If the second
coordinate is measurable and the pulled-back kernel integrable, each shell is
integrable, the L¹ shell masses sum to the mass outside the limiting stratum,
and the shell integrals sum absolutely to the restricted integral minus the
full integral.
Deviation: The indicators are on idèles. The statement retains the chosen
pullback and does not identify its summands with traces of S-local operators. -/
theorem hasSum_integral_divisorialKernelDifference {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset V)
    (hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    (K : I𝔽 × I𝔽 → ℂ) (p : X → I𝔽 × I𝔽) (hp : Measurable fun x ↦ (p x).2)
    (hK : Integrable (fun x ↦ K (p x)) μ) :
    let D := (fun x ↦ (p x).2) ⁻¹' sLocalDivisorialStratum F S
    let Δ := fun k x ↦ divisorialKernelDifference S k K (p x)
    (∀ k, Integrable (Δ k) μ) ∧
      HasSum (fun k ↦ ∫ x, ‖Δ k x‖ ∂μ) (∫ x in Dᶜ, ‖K (p x)‖ ∂μ) ∧
      Summable (fun k ↦ ‖∫ x, Δ k x ∂μ‖) ∧
      HasSum (fun k ↦ ∫ x, Δ k x ∂μ) ((∫ x in D, K (p x) ∂μ) - ∫ x, K (p x) ∂μ) := by
  intro D Δ
  let E (n : ℕ) := (fun x ↦ (p x).2) ⁻¹' divisorialStratum F (primaryDivisorialPlaces F S n)
  let T (n : ℕ) := E n \ E (n+1)
  have hM (n) : MeasurableSet (E n) :=
    ((isClopen_divisorialStratum (F := F) _).isOpen.measurableSet.preimage hp)
  have hm (n) : MeasurableSet (T n) := (hM n).diff (hM (n+1))
  have hplaces : Monotone (primaryDivisorialPlaces F S) :=
    monotone_nat_of_le_succ fun k ↦ by rw [primaryDivisorialPlaces_succ]; exact Finset.subset_union_left
  have ha : Antitone E := fun i j hij x hx v hv ↦ hx v (hplaces hij hv)
  have hd : Pairwise (Disjoint on T) := pairwise_disjoint_exit_shells E ha
  have hi : (⋂ n, E n) = D := by
    dsimp only [D, E]
    rw [← iInter_primaryDivisorialStratum S hS, preimage_iInter]
  have hD : MeasurableSet D := hi ▸ MeasurableSet.iInter hM
  have hu : (⋃ n, T n) = Dᶜ := by
    rw [← hi]
    apply iUnion_exit_shells
    ext x
    simp [E, primaryDivisorialPlaces, divisorialStratum]
  have heq (n) : Δ n = (T n).indicator (fun x ↦ -(K (p x))) := by
    funext x
    by_cases h : x ∈ T n
    · rw [indicator_of_mem h]
      exact divisorialKernelDifference_eq_neg S n K (p x) h
    · rw [indicator_of_notMem h]
      change (divisorialIndicator _ _ - divisorialIndicator _ _) * _ = 0
      rw [divisorialIndicator_eq_indicator, divisorialIndicator_eq_indicator]
      by_cases hnew : x ∈ E (n+1)
      · have ho := ha (Nat.le_succ n) hnew
        change (p x).2 ∈ divisorialStratum F _ at hnew ho
        rw [indicator_of_mem hnew, indicator_of_mem ho, sub_self, zero_mul]
      · have hold : x ∉ E n := fun hx ↦ h ⟨hx,hnew⟩
        change (p x).2 ∉ divisorialStratum F _ at hnew hold
        rw [indicator_of_notMem hnew, indicator_of_notMem hold, sub_self, zero_mul]
  have hint (n) : Integrable (Δ n) μ := (heq n) ▸ hK.neg.indicator (hm n)
  have hnorm (n) : (∫ x, ‖Δ n x‖ ∂μ) = ∫ x in T n, ‖K (p x)‖ ∂μ := by
    rw [heq]
    simp only [norm_indicator_eq_indicator_norm, norm_neg, integral_indicator (hm n)]
  have hnormSum : HasSum (fun n ↦ ∫ x, ‖Δ n x‖ ∂μ) (∫ x in Dᶜ, ‖K (p x)‖ ∂μ) := by
    simpa only [hnorm, ← hu] using (hasSum_integral_iUnion hm hd hK.norm.integrableOn)
  have hsig (n) : (∫ x, Δ n x ∂μ) = ∫ x in T n, -K (p x) ∂μ := by
    rw [heq, integral_indicator (hm n)]
  refine ⟨hint, hnormSum, hnormSum.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_integral_le_integral_norm (Δ k)), ?_⟩
  have hs := hasSum_integral_iUnion (f := fun x ↦ -K (p x)) hm hd hK.neg.integrableOn
  rw [hu, integral_neg, setIntegral_compl hD hK, neg_sub] at hs
  simpa only [hsig] using hs

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "q𝔽" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

private theorem exists_principal_outside_divisorialStratum {T : Finset V} (hT : T.Nonempty) :
    ∃ g : I𝔽, q𝔽 g = 1 ∧ g ∉ divisorialStratum F T := by
  obtain ⟨v, hv⟩ := hT
  obtain ⟨r, hr, hr₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let u : Fˣ := Units.mk0 (r : F) (by exact_mod_cast hr₀)
  let g : I𝔽 := IdeleGroup.unitEmbedding (𝓞 F) F u
  have hval : Valued.v (g.val.2 v) < 1 := by
    change Valued.v (((algebraMap F (AdeleRing (𝓞 F) F)) (r : F)).2 v) < 1
    rw [AdeleRing.algebraMap_snd_apply]
    exact (HeightOneSpectrum.adicCompletion.valued_coe (K := F) (v := v) (r : F)) ▸
      (v.valuation_lt_one_iff_mem (K := F) r).mpr hr
  exact ⟨g, (QuotientGroup.eq_one_iff g).mpr ⟨u, rfl⟩, fun hg ↦ hval.ne (hg v hv)⟩

/-- Paper: (11.3.1.2), p. 492, and §12.3, p. 514. A nonempty finite set of
place conditions does not descend to a set of idèle classes: a nonzero
algebraic integer in one of the primes gives a principal idèle excluded from
the stratum, whereas its class also has the representative one. -/
theorem divisorialStratum_not_preimage_ideleClass {T : Finset V} (hT : T.Nonempty) :
    ¬ ∃ A : Set C𝔽, divisorialStratum F T = q𝔽 ⁻¹' A := by
  obtain ⟨g, hg, hout⟩ := exists_principal_outside_divisorialStratum hT
  rintro ⟨A, hA⟩
  have h1 : (1 : I𝔽) ∈ divisorialStratum F T := fun _ _ ↦ map_one _
  have hgmem : g ∈ divisorialStratum F T := by
    rw [hA, mem_preimage, hg, ← map_one q𝔽]
    rw [hA] at h1
    exact h1
  exact hout hgmem

private theorem clopen_indicator_not_ae_ideleClass (μ : Measure I𝔽) [μ.IsHaarMeasure]
    {A : Set I𝔽} (ho : IsClopen A) (h1 : 1 ∈ A) {g : I𝔽} (hg : q𝔽 g = 1) (hout : g ∉ A) :
    ¬ ∃ f : C𝔽 → ℂ, A.indicator (fun _ ↦ (1 : ℂ)) =ᵐ[μ] f ∘ q𝔽 := by
  let W := A ∩ (fun x : I𝔽 ↦ g * x) ⁻¹' Aᶜ
  have hw : IsOpen W := ho.isOpen.inter (ho.isClosed.isOpen_compl.preimage (continuous_const_mul g))
  have hn : W.Nonempty := ⟨1, h1, by simpa only [mem_preimage, mul_one, mem_compl_iff] using hout⟩
  rintro ⟨f, hf⟩
  have hfg := (measurePreserving_mul_left μ g).quasiMeasurePreserving.ae hf
  have hzero : Wᶜ ∈ ae μ := by
    filter_upwards [hf, hfg] with x hx hxt
    intro hmem
    have hm : x ∈ A ∧ g * x ∉ A := hmem
    change A.indicator (fun _ ↦ (1 : ℂ)) x = f (q𝔽 x) at hx
    change A.indicator (fun _ ↦ (1 : ℂ)) (g * x) = f (q𝔽 (g * x)) at hxt
    rw [indicator_of_mem hm.1] at hx
    rw [indicator_of_notMem hm.2, map_mul, hg, one_mul] at hxt
    exact one_ne_zero (hx.trans hxt.symm)
  exact (hw.measure_pos μ hn).ne' (compl_mem_ae_iff.mp hzero)

/-- Paper: (11.3.1.2), p. 492, and §12.3, p. 514. For every Haar measure on the
idèles, a nonempty finite divisorial indicator fails to descend to an idèle-class
function even almost everywhere.
Deviation: Changing the representative by a principal idèle changes the
indicator on a nonempty open set, which has positive Haar measure. -/
theorem divisorialIndicator_not_ae_ideleClass (μ : Measure I𝔽) [μ.IsHaarMeasure]
    {T : Finset V} (hT : T.Nonempty) :
    ¬ ∃ f : C𝔽 → ℂ, divisorialIndicator T =ᵐ[μ] f ∘ q𝔽 := by
  obtain ⟨g, hg, hout⟩ := exists_principal_outside_divisorialStratum hT
  rw [divisorialIndicator_eq_indicator]
  exact clopen_indicator_not_ae_ideleClass μ (isClopen_divisorialStratum T)
    (fun _ _ ↦ map_one _) hg hout

/-- Paper: §11.3.2, p. 495, and §12.3, p. 514. For every finite S, the
indicator of being an integral unit outside S also fails to descend almost
everywhere to the idèle classes. A prime outside S yields a principal translate
of this open subgroup disjoint from it. -/
theorem sLocalDivisorialStratum_indicator_not_ae_ideleClass (μ : Measure I𝔽) [μ.IsHaarMeasure]
    (S : Finset V) : ¬ ∃ f : C𝔽 → ℂ,
      (sLocalDivisorialStratum F S).indicator (fun _ ↦ (1 : ℂ)) =ᵐ[μ] f ∘ q𝔽 := by
  let : Infinite (HeightOneSpectrum (𝓞 ℚ)) := Infinite.of_injective
    Rat.HeightOneSpectrum.primesEquiv.symm Rat.HeightOneSpectrum.primesEquiv.symm.injective
  obtain ⟨p, hp⟩ := (S.image fun v ↦ v.under (𝓞 ℚ)).finite_toSet.infinite_compl.nonempty
  have := p.isMaximal
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p.asIdeal
  let v : V := ⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩
  have hv : v ∉ S := fun hv ↦ hp (Finset.mem_image.mpr ⟨v, hv, HeightOneSpectrum.ext hPp.over.symm⟩)
  obtain ⟨g, hg, hout⟩ := exists_principal_outside_divisorialStratum (Finset.singleton_nonempty v)
  have hbad : g ∉ sLocalDivisorialStratum F S := by
    intro h
    exact hout (fun w hw ↦ (Finset.mem_singleton.mp hw) ▸ h v hv)
  have hopen : IsOpen (sLocalDivisorialStratum F S) := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion]
    exact (integralIdeleInsertion_isOpenEmbedding F S).isOpen_range
  have hclosed : IsClosed (sLocalDivisorialStratum F S) := by
    rw [sLocalDivisorialStratum_eq_range_integralIdeleInsertion] at hopen ⊢
    exact (integralIdeleInsertion F S).range.isClosed_of_isOpen hopen
  exact clopen_indicator_not_ae_ideleClass μ ⟨hclosed,hopen⟩ (fun _ _ ↦ map_one _) hg hbad

end RiemannMasullo
