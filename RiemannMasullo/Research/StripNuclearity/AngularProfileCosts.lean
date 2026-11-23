module

public import RiemannMasullo.Research.StripNuclearity.AngularProfiles
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Absolute summability of radial derivatives over angular Fourier profiles
-/

@[expose] public noncomputable section

open MeasureTheory Function Set
open scoped FourierTransform ContDiff Topology

namespace RiemannMasullo.StripNuclearity

variable {K G : Type*}
  [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The real radial profile selected by the positive compact character. -/
def positiveAngularProfile (μK : Measure K) (e : K × Multiplicative ℝ ≃ₜ* G)
    (φ : G → ℂ) (ξ : PontryaginDual K) (t : ℝ) : ℂ :=
  ∫ k, φ (e (k,Multiplicative.ofAdd t)) * (ξ k : ℂ) ∂μK

/-- Each positive compact-character fiber has finite real Fourier moments.
The same moments sum absolutely over all fibers with any finite product of
squared real angular frequencies. The inverse compact character in the
joint Fourier transform preserves all these weights. -/
theorem positiveAngularProfile_fourier_moments (μK : Measure K) [μK.IsHaarMeasure]
    (e : K × Multiplicative ℝ ≃ₜ* G) (φ : SchwartzBruhat G) (j : ℕ)
    (ρs : List (PontryaginDual K →ₜ* Multiplicative ℝ)) :
    let p := positiveAngularProfile μK e φ.val
    (∀ ξ, Integrable (fun u : ℝ ↦ (1+u^2)^j * ‖𝓕 (p ξ) u‖)) ∧
      Summable (fun ξ : PontryaginDual K ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod *
        ∫ u : ℝ, (1+u^2)^j * ‖𝓕 (p ξ) u‖) := by
  intro p
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual K) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  let : Countable (PontryaginDual K) := countable_of_Lindelof_of_discrete
  let μ := (μK.prod (volume : Measure ℝ)).map e
  let : μ.IsHaarMeasure := split_log_chart_isHaarMeasure μK e
  let : μ.Regular := inferInstance
  obtain ⟨d,hd⟩ := exists_jointDual_chart e
  have hraw : Integrable (fun q : K × Multiplicative ℝ ↦ φ.val (e q)) (μK.prod (volume : Measure ℝ)) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mp (SchwartzBruhat.integrable μ φ)
  have hf (ξ : PontryaginDual K) (u : ℝ) : 𝓕 (p ξ) u = lcaFourier μ φ.val (d (ξ⁻¹,Multiplicative.ofAdd u)) :=
    fourier_angular_profile_eq μK e d hd φ.val hraw ξ u
  constructor
  · intro ξ
    simp only [hf]
    exact (angular_fourier_fiber_moments μ d j [] φ).1 ξ⁻¹
  let w := fun ξ : PontryaginDual K ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod
  have hinv (ξ : PontryaginDual K) : w ξ⁻¹ = w ξ := by
    simp only [w, map_inv,toAdd_inv,even_two.neg_pow]
  have hb := (angular_fourier_fiber_moments μ d j ρs φ).2.comp_injective inv_injective
  convert hb using 1
  ext ξ
  simp only [hf,Function.comp_apply]
  exact congrArg (· * _) (hinv ξ).symm

/-- The entire family of angular profiles of a compactly supported continuous
Schwartz–Bruhat test has common support and smooth radial derivatives. Their
physical L¹ norms are summable over all compact characters with arbitrarily
many polynomial weights coming from real frequencies on the compact dual. -/
theorem summable_positiveAngularProfile_derivatives (μK : Measure K) [μK.IsHaarMeasure]
    (e : K × Multiplicative ℝ ≃ₜ* G) (φ : SchwartzBruhat G) (hc : Continuous φ.val)
    (hs : HasCompactSupport φ.val) :
    ∃ J : Set ℝ, IsCompact J ∧
      (∀ ξ, tsupport (positiveAngularProfile μK e φ.val ξ) ⊆ J ∧
        ContDiff ℝ ∞ (positiveAngularProfile μK e φ.val ξ)) ∧
      ∀ (ρs : List (PontryaginDual K →ₜ* Multiplicative ℝ)) (j : ℕ),
        Summable (fun ξ : PontryaginDual K ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod *
          ∫ t : ℝ, ‖iteratedDeriv j (positiveAngularProfile μK e φ.val ξ) t‖) := by
  let J : Set ℝ := (fun g : G ↦ (e.symm g).2.toAdd) '' tsupport φ.val
  have hJ : IsCompact J := hs.image (continuous_toAdd.comp (continuous_snd.comp e.symm.continuous))
  let p := positiveAngularProfile μK e φ.val
  have hsupp (ξ : PontryaginDual K) : tsupport (p ξ) ⊆ J := by
    refine closure_minimal ?_ hJ.isClosed
    intro t ht
    by_contra h
    apply ht
    apply integral_eq_zero_of_ae
    refine .of_forall fun k ↦ ?_
    change φ.val (e (k,Multiplicative.ofAdd t)) * (ξ k : ℂ) = 0
    have hnot : e (k,Multiplicative.ofAdd t) ∉ tsupport φ.val := fun h' ↦
      h ⟨_,h',by simp⟩
    rw [image_eq_zero_of_notMem_tsupport hnot,zero_mul]
  have hpc (ξ : PontryaginDual K) : Continuous (p ξ) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k := (univ : Set K)) isCompact_univ
    · exact ((hc.comp (e.continuous.comp (continuous_snd.prodMk (continuous_ofAdd.comp continuous_fst)))).mul
        (continuous_subtype_val.comp (ξ.continuous.comp continuous_snd))).continuousOn
    · simp
  have hm (ξ : PontryaginDual K) (j : ℕ) : Integrable (fun u : ℝ ↦ (1+u^2)^j * ‖𝓕 (p ξ) u‖) :=
    (positiveAngularProfile_fourier_moments μK e φ j []).1 ξ
  have hcost (ξ : PontryaginDual K) :=
    smooth_physical_cost_of_fourier_moments hJ (p ξ) (hpc ξ) (hsupp ξ) (hm ξ)
  refine ⟨J,hJ,fun ξ ↦ ⟨hsupp ξ,(hcost ξ).1⟩,?_⟩
  intro ρs j
  let w := fun ξ : PontryaginDual K ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod
  have hpos (ξ : PontryaginDual K) : 0 ≤ w ξ :=
    List.prod_nonneg fun x hx ↦ by obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx; positivity
  have hS := (positiveAngularProfile_fourier_moments μK e φ j ρs).2
  let C := volume.real J * (2*Real.pi)^j
  refine (hS.mul_left C).of_nonneg_of_le (fun ξ ↦ mul_nonneg (hpos ξ) (integral_nonneg fun _ ↦ norm_nonneg _)) ?_
  intro ξ
  change w ξ * _ ≤ C * (w ξ * _)
  rw [mul_left_comm C]
  exact mul_le_mul_of_nonneg_left ((hcost ξ).2 j) (hpos ξ)
end RiemannMasullo.StripNuclearity
