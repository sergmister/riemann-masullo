module

public import RiemannMasullo.Research.StripNuclearity.Physical
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Weighted radial convolution on a compact test core

Differentiation of the compact test kernel implements the second-order numerator
for a smooth branch of the ambient reciprocal Sobolev weight.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Convolution

namespace RiemannMasullo.StripNuclearity

/-- For each smooth half-line branch of the reciprocal weight, the actual
compactly supported radial convolution factors on its test core through the
Mellin resolvent. Its numerator uses only convolution with the kernel and
its first two derivatives, and the bounded coefficients of the log-weight. -/
theorem weighted_convolution_resolvent_numerator {I : Set ℝ} (ho : IsOpen I) (hi : OrdConnected I)
    (hne : I.Nonempty) {c : ℝ} (hno : ∀ z : ℂ, z.re ∈ I → (c : ℂ)^2-z^2 ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (j : PositiveRealExponentialDecay I →L[ℂ] E) (R : E →L[ℂ] E)
    (hr : ∀ p, ∃ q : PositiveRealExponentialDecay I, R (j p) = j q ∧
      ∀ z, z.re ∈ I → mellin (fun t ↦ q.val (Real.log t)) z =
        ((c : ℂ)^2-z^2)⁻¹ * mellin (fun t ↦ p.val (Real.log t)) z)
    (b s : ℝ) (g κ : ℝ → ℂ) (hg : HasCompactSupport g) (hgi : LocallyIntegrable g volume)
    (hκ : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) :
    let v : ℝ → ℝ := fun x ↦ Real.exp (-b*x - (s/2)*Real.log (1+x^2))
    let p : ℝ → ℝ := fun x ↦ -b-s*x/(1+x^2)
    let q : ℝ → ℝ := fun x ↦ (p x)^2-s*(1-x^2)/(1+x^2)^2
    let H := fun (k : ℝ → ℂ) (x : ℝ) ↦
      (v x : ℂ) * (g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] k) x
    ∃ u d : PositiveRealExponentialDecay I,
      u.val = H κ ∧ (∀ x, d.val x = ((c : ℂ)^2 - (q x : ℂ))*H κ x -
        2*(p x : ℂ)*H (deriv κ) x - H (deriv (deriv κ)) x) ∧ R (j d) = j u := by
  intro v p q H
  let L := ContinuousLinearMap.mul ℝ ℂ
  let F (k : ℝ → ℂ) := g ⋆[L, volume] k
  have hBc := weight_log_derivatives b s
  have hF (k : ℝ → ℂ) (hc : HasCompactSupport k) (hk : ContDiff ℝ ∞ k) (x : ℝ) :
      HasDerivAt (F k) (F (deriv k) x) x :=
    hc.hasDerivAt_convolution_right L hgi (hk.of_le (by simp)) x
  have hdκ : ContDiff ℝ ∞ (deriv κ) := (contDiff_infty_iff_deriv.mp hκs).2
  have hFu : ContDiff ℝ ∞ (F κ) := hκ.contDiff_convolution_right L hgi hκs
  have hvs : ContDiff ℝ ∞ v := by
    dsimp [v]
    fun_prop (disch := intro x; positivity)
  have hus : ContDiff ℝ ∞ (H κ) := (Complex.ofRealCLM.contDiff.comp hvs).mul hFu
  have huc : HasCompactSupport (H κ) := (hg.convolution L hκ).mul_left
  have hu' : ContDiff ℝ ∞ (deriv (H κ)) := (contDiff_infty_iff_deriv.mp hus).2
  have hu'' : ContDiff ℝ ∞ (deriv (deriv (H κ))) := (contDiff_infty_iff_deriv.mp hu').2
  let U := H κ
  let D := fun x ↦ (c : ℂ)^2 * U x - deriv (deriv U) x
  have hDs : ContDiff ℝ ∞ D := (contDiff_const.mul hus).sub hu''
  have hDc : HasCompactSupport D := huc.mul_left.sub huc.deriv.deriv
  let u : PositiveRealExponentialDecay I := ⟨U,mem_logExponentialDecaySubmodule_of_hasCompactSupport I huc hus⟩
  let d : PositiveRealExponentialDecay I := ⟨D,mem_logExponentialDecaySubmodule_of_hasCompactSupport I hDc hDs⟩
  have hRdu : R (j d) = j u := resolvent_inverts_compact_test ho hi hne hno j R hr u d
    (deriv U) (deriv (deriv U)) (fun x ↦ (hus.differentiable (by simp) x).hasDerivAt)
    (fun x ↦ (hu'.differentiable (by simp) x).hasDerivAt) hu''.continuous huc huc.deriv
    huc.deriv.deriv (fun _ ↦ rfl)
  refine ⟨u,d,rfl,?_,hRdu⟩
  let V (x : ℝ) := ((p x*v x : ℝ) : ℂ)*F κ x + (v x : ℂ)*F (deriv κ) x
  have hV (x : ℝ) : HasDerivAt U (V x) x := by
    exact (hBc.1 x).ofReal_comp.mul (hF κ hκ hκs x)
  have hV' (x : ℝ) : HasDerivAt V
      ((((q x * v x : ℝ) : ℂ) * F κ x + ((p x*v x : ℝ) : ℂ)*F (deriv κ) x) +
        (((p x*v x : ℝ) : ℂ)*F (deriv κ) x + (v x : ℂ)*F (deriv (deriv κ)) x)) x :=
    ((hBc.2.1 x).ofReal_comp.mul (hF κ hκ hκs x)).add
      ((hBc.1 x).ofReal_comp.mul (hF (deriv κ) hκ.deriv hdκ x))
  intro x
  change (c : ℂ)^2 * U x - deriv (deriv U) x = _
  rw [show deriv U = V from funext fun y ↦ (hV y).deriv, (hV' x).deriv]
  change _ = ((c:ℂ)^2-(q x:ℂ))*((v x : ℂ)*F κ x) - 2*(p x : ℂ)*((v x : ℂ)*F (deriv κ) x) -
    (v x : ℂ)*F (deriv (deriv κ)) x
  dsimp only [U,H,F,L]
  push_cast
  ring

end RiemannMasullo.StripNuclearity
