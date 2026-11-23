module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import Mathlib.Analysis.Fourier.Inversion

/-!
# Nuclear cost of a compactly masked real Fourier integral
-/

@[expose] public noncomputable section
open MeasureTheory Set Function
open scoped FourierTransform

namespace RiemannMasullo.StripNuclearity

/-- Two square-integrable masks turn a convolution given by absolute ordinary
Fourier inversion into a nuclear operator. The constant is the product of the
two mask norms; it is independent of the Fourier profile. -/
theorem exists_masked_scalar_kernel_traceNorm_le (ν : Measure ℝ) [SigmaFinite ν]
    (κ : ℝ → ℂ) (hc : Continuous κ) (hi : Integrable κ) (hF : Integrable (𝓕 κ))
    (l r : ℝ → ℂ) (hl : MemLp l 2 ν) (hr : MemLp r 2 ν) :
    ∃ (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hn : IsNuclearOperator T),
      traceNorm ⟨T,hn⟩ ≤ (‖hr.toLp r‖ * ‖hl.toLp l‖) * (∫ u : ℝ, ‖𝓕 κ u‖) ∧
      ∀ v, ∀ᵐ x ∂ν, T v x = ∫ y : ℝ, l x*κ (x-y)*star (r y)*v y ∂ν := by
  let G := Multiplicative ℝ
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨d,hd⟩ := exists_realPontryaginDualEquiv
  let : SecondCountableTopology (PontryaginDual G) := d.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let η : Measure (PontryaginDual G) := (volume : Measure ℝ).map d
  let f (ψ : PontryaginDual G) := 𝓕 κ (d.symm ψ).toAdd
  have hcomp (u : ℝ) : f (d (Multiplicative.ofAdd u)) = 𝓕 κ u := by simp [f]
  have hf : Integrable f η := by
    apply d.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr
    exact hF.congr (.of_forall fun u ↦ (hcomp u).symm)
  have hmap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : PontryaginDual G → E) :
      (∫ ψ, g ψ ∂η) = ∫ u : ℝ, g (d (Multiplicative.ofAdd u)) :=
    d.toHomeomorph.isClosedEmbedding.integral_map _
  have hκ (z : G) : κ z.toAdd = ∫ ψ, f ψ * (ψ z : ℂ) ∂η := by
    have hx := hi.fourierInv_fourier_eq hF (hc.continuousAt (x := z.toAdd))
    rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq] at hx
    apply hx.symm.trans
    refine Eq.trans ?_ (hmap (fun ψ ↦ f ψ * (ψ z : ℂ))).symm
    apply integral_congr_ae
    refine .of_forall fun u ↦ ?_
    change (Real.fourierChar (-(u * -z.toAdd)) : ℂ) * 𝓕 κ u =
      f (d (Multiplicative.ofAdd u)) * (d (Multiplicative.ofAdd u) z : ℂ)
    have he : d (Multiplicative.ofAdd u) z = Real.fourierChar (u*z.toAdd) := hd u z.toAdd
    rw [hcomp u,he]
    simp [mul_comm]
  have hη : SFinite η := by
    change SFinite ((volume : Measure ℝ).map (fun u : ℝ ↦ d (Multiplicative.ofAdd u)))
    infer_instance
  let hν : @SigmaFinite (Multiplicative ℝ) inferInstance ν := inferInstanceAs (SigmaFinite (ν : Measure ℝ))
  obtain ⟨T,hn,hcost,hrep,_⟩ := @masked_fourier_kernel_traceNorm_le (Multiplicative ℝ) _ _ _ _ _
    (inferInstanceAs (MeasurableSpace ℝ)) (inferInstanceAs (BorelSpace ℝ)) _ η ν hη hν _ _ f hf
    (fun z ↦ κ z.toAdd) hκ (fun z ↦ l z.toAdd) (fun z ↦ r z.toAdd) hl hr
  refine ⟨T,hn,?_,fun v ↦ ?_⟩
  · apply hcost.trans_eq
    congr 1
    exact (hmap (fun ψ ↦ ‖f ψ‖)).trans (integral_congr_ae (.of_forall fun u ↦ congrArg norm (hcomp u)))
  · refine (hrep v).mono fun x hx ↦ hx.trans ?_
    change (∫ y : ℝ, l x.toAdd*κ (x.toAdd + -y)*star (r y)*v y ∂ν) =
      ∫ y : ℝ, l x.toAdd*κ (x.toAdd-y)*star (r y)*v y ∂ν
    simp only [sub_eq_add_neg]

end RiemannMasullo.StripNuclearity
