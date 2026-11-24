module

public import RiemannMasullo.Research.StripNuclearity.AngularFibers
public import RiemannMasullo.Research.StripNuclearity.RadialFourierCost

/-!
# Positive angular profiles and ordinary radial Fourier transforms
-/

@[expose] public noncomputable section

open MeasureTheory Set Function
open scoped FourierTransform Topology ContDiff

namespace RiemannMasullo.StripNuclearity

variable {K G : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μK : Measure K) [SFinite μK]

/-- Partial Fourier inversion on a split group. The inverse compact character
in the dual argument exactly matches the positive character in the radial fiber
integral. Lebesgue measure on the second factor fixes the normalization. -/
theorem fourier_angular_profile_eq (e : K × Multiplicative ℝ ≃ₜ* G)
    (d : (PontryaginDual K × Multiplicative ℝ) ≃ₜ* PontryaginDual G)
    (hd : ∀ ξ (u t : ℝ) (k : K), d (ξ,Multiplicative.ofAdd u) (e (k,Multiplicative.ofAdd t)) =
      ξ k * Real.fourierChar (u*t)) (φ : G → ℂ)
    (hφ : Integrable (fun q : K × Multiplicative ℝ ↦ φ (e q)) (μK.prod (volume : Measure ℝ)))
    (ξ : PontryaginDual K) (u : ℝ) :
    let p (t : ℝ) := ∫ k, φ (e (k,Multiplicative.ofAdd t)) * (ξ k : ℂ) ∂μK
    𝓕 p u = lcaFourier ((μK.prod (volume : Measure ℝ)).map e) φ (d (ξ⁻¹,Multiplicative.ofAdd u)) := by
  intro p
  let ψ := d (ξ⁻¹,Multiplicative.ofAdd u)
  let H := fun q : K × Multiplicative ℝ ↦ φ (e q)*star (ψ (e q) : ℂ)
  have hH : Integrable H (μK.prod (volume : Measure ℝ)) := by
    apply hφ.norm.mono' (hφ.1.mul (continuous_star.comp
      (continuous_subtype_val.comp (ψ.continuous.comp e.continuous))).aestronglyMeasurable)
    exact .of_forall fun q ↦ by
      change ‖φ (e q)*star (ψ (e q) : ℂ)‖ ≤ ‖φ (e q)‖
      simp
  have he (t : ℝ) (k : K) : H (k,Multiplicative.ofAdd t) =
      (Real.fourierChar (-(t*u)) : ℂ) * (φ (e (k,Multiplicative.ofAdd t)) * (ξ k : ℂ)) := by
    have hinv : ξ⁻¹ k = (ξ k)⁻¹ := rfl
    simp only [H,ψ,hd,hinv,Circle.coe_mul,Complex.star_def,map_mul,Real.fourierChar.map_neg_eq_inv,
      Circle.coe_inv_eq_conj,Complex.conj_conj,mul_comm t u]
    ring
  have hm : lcaFourier ((μK.prod (volume : Measure ℝ)).map e) φ ψ =
      ∫ q : K × Multiplicative ℝ, H q ∂μK.prod (volume : Measure ℝ) :=
    e.toHomeomorph.isClosedEmbedding.integral_map _
  rw [Real.fourier_real_eq,hm]
  have hsplit : (∫ q : K × Multiplicative ℝ, H q ∂μK.prod (volume : Measure ℝ)) =
      ∫ t : ℝ, ∫ k, H (k,Multiplicative.ofAdd t) ∂μK :=
    integral_prod_symm (μ := μK) (ν := (volume : Measure ℝ)) (fun q : K × ℝ ↦ H (q.1,Multiplicative.ofAdd q.2)) hH
  rw [hsplit]
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  change (Real.fourierChar (-(t*u)) : ℂ) * (∫ k, φ (e (k,Multiplicative.ofAdd t)) * (ξ k : ℂ) ∂μK) =
    ∫ k, H (k,Multiplicative.ofAdd t) ∂μK
  rw [← integral_const_mul]
  exact integral_congr_ae (.of_forall fun k ↦ (he t k).symm)

end RiemannMasullo.StripNuclearity
