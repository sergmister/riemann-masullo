module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Joint angular and radial Fourier moments

Invariance under a radial or archimedean one-parameter subgroup identifies its
frequency as a symbol on the full dual. Schwartz integrability of invariant
derivatives controls all the resulting polynomial weights simultaneously.
-/

@[expose] public noncomputable section

open MeasureTheory Function Filter
open scoped Topology

namespace RiemannMasullo.StripNuclearity

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
  (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure]

/-- The Fourier transform of a Schwartz–Bruhat test is integrable after
multiplication by any product of quadratic derivative-symbol weights. Each
direction may be repeated to increase the degree. -/
theorem integrable_fourier_symbol_weights (A : List (LCATopologicalLie G)) (f : SchwartzBruhat G) :
    Integrable (fun χ ↦ (A.map (fun a ↦ 1+‖bruhatDiffSymbol (bruhatDiffGenerator a) χ‖^2)).prod *
      ‖lcaFourier μ f χ‖) ν := by
  obtain ⟨B,hB⟩ := schwartzBruhat_fourier_continuousLinear μ
  induction A generalizing f with
  | nil =>
    simpa only [List.map_nil,List.prod_nil,one_mul] using
      ((SchwartzBruhat.integrable ν (B f)).norm.congr (.of_forall fun χ ↦ congrArg norm (hB f χ)))
  | cons a A ih =>
    obtain ⟨_,g,_,_,_,hg⟩ := lcaFourier_bruhatDiff μ (bruhatDiffWord [a,a]) f
    apply ((ih f).add (ih g)).congr
    apply ae_of_all
    intro χ
    have he : ‖lcaFourier μ g χ‖ = ‖bruhatDiffSymbol (bruhatDiffGenerator a) χ‖^2 * ‖lcaFourier μ f χ‖ := by
      rw [congrFun hg χ,Pi.mul_apply,bruhatDiffSymbol_word]
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,norm_mul,pow_two]
    simp only [Pi.add_apply, List.map_cons,List.prod_cons,he]
    ring

private theorem exists_frequency_direction (ρ : PontryaginDual G →ₜ* Multiplicative ℝ) :
    ∃ a : LCATopologicalLie G, ∀ χ, bruhatDiffSymbol (bruhatDiffGenerator a) χ =
      2*(Real.pi:ℂ)*Complex.I*((ρ χ).toAdd:ℂ) := by
  obtain ⟨e,_,_,he⟩ := bruhatDiffDegreeOne_frequency (G := G)
  let D := e.symm ρ
  obtain ⟨a,ha⟩ := (mem_bruhatDiffDegreeOneReal_iff D.val).mp D.property
  exact ⟨a,fun χ ↦ bruhatDiffSymbol_generator a χ (ρ χ).toAdd
    (fun t ↦ by simpa only [D,Equiv.apply_symm_apply] using he a D ha χ t)⟩

/-- Every finite list of continuous real frequencies on the Pontryagin dual
has integrable joint quadratic moments against the absolute Fourier transform.
This applies to the angular archimedean directions and the radial frequency
in the same product, without parametrizing the compact dual by a lattice. -/
theorem integrable_fourier_frequency_weights (ρs : List (PontryaginDual G →ₜ* Multiplicative ℝ))
    (f : SchwartzBruhat G) :
    Integrable (fun χ ↦ (ρs.map (fun ρ ↦ 1+((ρ χ).toAdd)^2)).prod * ‖lcaFourier μ f χ‖) ν := by
  choose a ha using (exists_frequency_direction (G := G))
  let A := ρs.map a
  have hle (ρ : PontryaginDual G →ₜ* Multiplicative ℝ) (χ : PontryaginDual G) :
      1+((ρ χ).toAdd)^2 ≤ 1+‖bruhatDiffSymbol (bruhatDiffGenerator (a ρ)) χ‖^2 := by
    rw [ha]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Complex.norm_I,mul_one,
      Real.norm_eq_abs,abs_of_nonneg Real.pi_pos.le]
    have hx : 0 ≤ |(ρ χ).toAdd| := abs_nonneg _
    have hh : |(ρ χ).toAdd| ≤ (2*Real.pi)*|(ρ χ).toAdd| :=
      le_mul_of_one_le_left hx (by linarith [Real.two_le_pi])
    linarith [sq_le_sq₀ hx (by positivity) |>.mpr hh, sq_abs (ρ χ).toAdd]
  have hprod (χ : PontryaginDual G) : (ρs.map (fun ρ ↦ 1+((ρ χ).toAdd)^2)).prod ≤
      (A.map (fun b ↦ 1+‖bruhatDiffSymbol (bruhatDiffGenerator b) χ‖^2)).prod := by
    dsimp [A]
    induction ρs with
    | nil => simp
    | cons ρ ρs ih =>
      simp only [List.map_cons,List.prod_cons]
      exact mul_le_mul (hle ρ χ) ih (List.prod_nonneg (fun x hx ↦ by
        obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx
        positivity)) (by positivity)
  have hw (ρs : List (PontryaginDual G →ₜ* Multiplicative ℝ)) :
      Continuous fun χ ↦ (ρs.map (fun ρ ↦ 1+((ρ χ).toAdd)^2)).prod := by
    induction ρs with
    | nil => exact continuous_const
    | cons ρ ρs ih => exact (continuous_const.add ((continuous_toAdd.comp ρ.continuous).pow 2)).mul ih
  have hnon (ρs : List (PontryaginDual G →ₜ* Multiplicative ℝ)) (χ : PontryaginDual G) :
      0 ≤ (ρs.map (fun ρ ↦ 1+((ρ χ).toAdd)^2)).prod :=
    List.prod_nonneg (fun x hx ↦ by obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx; positivity)
  have hF : Integrable (fun χ ↦ ‖lcaFourier μ f χ‖) ν := by
    simpa using integrable_fourier_symbol_weights μ ν [] f
  apply (integrable_fourier_symbol_weights μ ν A f).mono' ((hw ρs).aestronglyMeasurable.mul hF.1)
  exact .of_forall fun χ ↦ by
    simp only [Pi.mul_apply,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hnon _ _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hprod χ) (norm_nonneg _)

end RiemannMasullo.StripNuclearity
