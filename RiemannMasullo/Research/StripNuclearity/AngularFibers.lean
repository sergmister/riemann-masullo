module

public import RiemannMasullo.Research.StripNuclearity.AngularFourier
public import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier weights on all discrete angular fibers
-/

@[expose] public noncomputable section

open MeasureTheory Function Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

/-- A split compact-by-real group has dual coordinates given by restriction to
the compact factor and the ordinary real Fourier frequency. -/
theorem exists_jointDual_chart {K G : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : K × Multiplicative ℝ ≃ₜ* G) :
    ∃ d : (PontryaginDual K × Multiplicative ℝ) ≃ₜ* PontryaginDual G,
      ∀ ξ (u t : ℝ) (k : K), d (ξ,Multiplicative.ofAdd u) (e (k,Multiplicative.ofAdd t)) =
        ξ k * Real.fourierChar (u*t) := by
  let R := Multiplicative ℝ
  let n := (ContinuousMonoidHom.snd K R).comp (e.symm : G →ₜ* K × R)
  let r := (ContinuousMonoidHom.fst K R).comp (e.symm : G →ₜ* K × R)
  let i := (e : K × R →ₜ* G).comp (ContinuousMonoidHom.inl K R)
  let s := (e : K × R →ₜ* G).comp (ContinuousMonoidHom.inr K R)
  obtain ⟨d,hD⟩ := exists_realPontryaginDualEquiv
  let a : PontryaginDual K × R →ₜ* PontryaginDual G :=
    (PontryaginDual.map r).comp (ContinuousMonoidHom.fst _ _) *
      (PontryaginDual.map n).comp ((d : R →ₜ* _).comp (ContinuousMonoidHom.snd _ _))
  let b : PontryaginDual G →ₜ* PontryaginDual K × R :=
    (PontryaginDual.map i).prod ((d.symm : _ →ₜ* R).comp (PontryaginDual.map s))
  have ha (p : PontryaginDual K × R) (k : K) (t : R) : a p (e (k,t)) = p.1 k * d p.2 t := by
    change p.1 (e.symm (e (k,t))).1 * d p.2 (e.symm (e (k,t))).2 = _
    rw [e.symm_apply_apply]
  let c : (PontryaginDual K × R) ≃ₜ* PontryaginDual G :=
    { toFun := a, invFun := b, map_mul' := a.map_mul, continuous_toFun := a.continuous,
      continuous_invFun := b.continuous, left_inv := fun p ↦ by
        apply Prod.ext
        · apply PontryaginDual.ext
          intro k
          change a p (e (k,1)) = p.1 k
          rw [ha,map_one,mul_one]
        · apply d.injective
          change d (d.symm (PontryaginDual.map s (a p))) = d p.2
          rw [d.apply_symm_apply]
          apply PontryaginDual.ext
          intro t
          change a p (e (1,t)) = d p.2 t
          rw [ha,map_one,one_mul]
      right_inv := fun ψ ↦ by
        apply PontryaginDual.ext
        intro x
        obtain ⟨⟨k,t⟩,rfl⟩ := e.surjective x
        rw [ha]
        change ψ (e (k,1)) * d (d.symm (PontryaginDual.map s ψ)) t = _
        rw [d.apply_symm_apply]
        change ψ (e (k,1)) * ψ (e (1,t)) = _
        rw [← map_mul,← map_mul]
        simp }
  exact ⟨c,fun ξ u t k ↦ (ha _ k _).trans (congrArg (ξ k * ·) (hD u t))⟩

private abbrev dualRadialHaar : Measure (Multiplicative ℝ) := (volume : Measure ℝ)

private instance : dualRadialHaar.IsHaarMeasure := by
  let : IsFiniteMeasureOnCompacts dualRadialHaar := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  let : Measure.IsOpenPosMeasure dualRadialHaar := inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
  let : dualRadialHaar.IsMulLeftInvariant :=
    ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
  constructor

/-- Product Haar in a split logarithmic chart, with Lebesgue normalization
on the real factor. -/
theorem split_log_chart_isHaarMeasure {K G : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure K) [μ.IsHaarMeasure] (e : K × Multiplicative ℝ ≃ₜ* G) :
    ((μ.prod (volume : Measure ℝ)).map e).IsHaarMeasure :=
  e.isHaarMeasure_map (μ.prod dualRadialHaar)

/-- On any split dual the global Schwartz estimate sums weighted ordinary
Fourier mass across every angular fiber. Each character-independent real
frequency on the discrete angular group can be included with any multiplicity. -/
theorem angular_fourier_fiber_moments {G X : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [CommGroup X] [TopologicalSpace X] [DiscreteTopology X] [Countable X]
    (e : X × Multiplicative ℝ ≃ₜ* PontryaginDual G)
    (j : ℕ) (ρs : List (X →ₜ* Multiplicative ℝ)) (f : SchwartzBruhat G) :
    (∀ ξ : X, Integrable (fun u : ℝ ↦ (1+u^2)^j*‖lcaFourier μ f (e (ξ,Multiplicative.ofAdd u))‖)) ∧
      Summable (fun ξ : X ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod *
        ∫ u : ℝ, (1+u^2)^j*‖lcaFourier μ f (e (ξ,Multiplicative.ofAdd u))‖) := by
  let R := Multiplicative ℝ
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : (Measure.count : Measure X).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let η := (Measure.count : Measure X).prod dualRadialHaar
  let ν := η.map e
  let : ν.IsHaarMeasure := e.isHaarMeasure_map η
  let r := (ContinuousMonoidHom.fst X R).comp (e.symm : PontryaginDual G →ₜ* X × Multiplicative ℝ)
  let n := (ContinuousMonoidHom.snd X R).comp (e.symm : PontryaginDual G →ₜ* X × Multiplicative ℝ)
  let A := List.replicate j n ++ ρs.map (fun ρ ↦ ρ.comp r)
  let W := fun ξ : X ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod
  have hW (ξ : X) : 0 < W ξ :=
    List.prod_pos (fun x hx ↦ by obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx; positivity)
  have h := integrable_fourier_frequency_weights μ ν A f
  have hcomp := e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mp h
  have hp : Integrable (fun p : X × R ↦ W p.1 * ((1+p.2.toAdd^2)^j*‖lcaFourier μ f (e p)‖)) η := by
    apply hcomp.congr
    refine .of_forall fun p ↦ ?_
    simp only [Function.comp_apply,A,List.map_append,List.map_replicate,List.prod_append,List.prod_replicate,List.map_map]
    change (1+((e.symm (e p)).2.toAdd)^2)^j *
      (ρs.map (fun ρ ↦ 1+((ρ (e.symm (e p)).1).toAdd)^2)).prod * ‖lcaFourier μ f (e p)‖ = _
    rw [e.symm_apply_apply]
    ring
  constructor
  · intro ξ
    have hrow := Measure.ae_count_iff.mp (integrable_prod_iff hp.1 |>.mp hp).1 ξ
    change Integrable (fun u : ℝ ↦ W ξ*((1+u^2)^j*‖lcaFourier μ f (e (ξ,Multiplicative.ofAdd u))‖)) at hrow
    apply (hrow.const_mul (W ξ)⁻¹).congr
    exact .of_forall fun u ↦ by dsimp; rw [← mul_assoc,inv_mul_cancel₀ (hW ξ).ne',one_mul]
  have hi := integrable_count_iff.mp hp.integral_prod_left
  apply hi.congr
  intro ξ
  change ‖∫ u : ℝ, W ξ * ((1+u^2)^j*‖lcaFourier μ f (e (ξ,Multiplicative.ofAdd u))‖)‖ = _
  rw [integral_const_mul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hW ξ).le
    (integral_nonneg fun u ↦ mul_nonneg (by positivity) (norm_nonneg _)))]

/-- On any split dual the global Schwartz estimate sums weighted ordinary
Fourier mass across every angular fiber. Each character-independent real
frequency on the discrete angular group can be included with any multiplicity. -/
theorem summable_angular_fourier_fibers {G X : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [CommGroup X] [TopologicalSpace X] [DiscreteTopology X] [Countable X]
    (e : X × Multiplicative ℝ ≃ₜ* PontryaginDual G)
    (ρs : List (X →ₜ* Multiplicative ℝ)) (f : SchwartzBruhat G) :
    Summable fun ξ : X ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod *
      ∫ u : ℝ, (1+u^2)*‖lcaFourier μ f (e (ξ,Multiplicative.ofAdd u))‖ := by
  simpa only [pow_one] using (angular_fourier_fiber_moments μ e 1 ρs f).2

end RiemannMasullo.StripNuclearity
