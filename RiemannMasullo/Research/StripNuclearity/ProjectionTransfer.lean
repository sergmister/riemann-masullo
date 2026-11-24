module

public import RiemannMasullo.Research.StripNuclearity.Projective
public import RiemannMasullo.Research.PositiveStrip.Pairing

/-!
# Transport of the projected radial operator to an idèle-class component
-/

@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped Topology NumberField.AdeleRing InnerProductSpace ContDiff

namespace RiemannMasullo.StripNuclearity

/-- If a map sends one null space into another, its adjoint sends vectors
orthogonal to the second null space into the orthogonal complement of the first. -/
theorem projection_comp_adjoint_of_mapsTo {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : E →L[ℂ] H) (N : Submodule ℂ E) (Θ : Submodule ℂ H)
    (h : ∀ v ∈ N, L v ∈ Θ) :
    N.orthogonal.starProjection.comp (L.adjoint.comp Θ.orthogonal.starProjection) =
      L.adjoint.comp Θ.orthogonal.starProjection := by
  apply ContinuousLinearMap.ext
  intro u
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [Submodule.mem_orthogonal]
  intro v hv
  change inner ℂ v (L.adjoint (Θ.orthogonal.starProjection u)) = 0
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact Θ.inner_right_of_mem_orthogonal (h v hv) (Θ.orthogonal.starProjection_apply_mem u)

set_option quotPrecheck false
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "point(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
private theorem restrict_entire_profile (I : Set ℝ) (u : PositiveRealExponentialDecay univ) :
    ∃ v : PositiveRealExponentialDecay I, v.val = u.val := by
  refine ⟨⟨u.val,(Submodule.mem_iInf _).mpr fun a ↦ ?_⟩,rfl⟩
  exact (Submodule.mem_iInf _).mp u.property ⟨a.val,mem_univ _⟩

/-- The radial admitted Mellin jets for a fixed Hecke character are exactly the
angular component of the ambient moments. In particular the adjoint of the
inverse-character lift sends the range of the actual Chapter 10 spectral
projection into the range of the radial projection. -/
theorem radial_projector_comp_lift_adjoint_spectralProjection
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (ξ : PontryaginDual C₁) {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s)
    (L : Ws(α,s) →L[ℂ] W(α,s))
    (hL : ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ξ x : ℂ)⁻¹ * f (logNorm x))
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hlog : MeasurePreserving logNorm ν volume) :
    let D := MeromorphicOn.divisor (continuedCompletedHeckeL (χ ξ)) univ
    let Z := {z : ℂ // 0 < D z ∧ |z.re - 1/2| ≤ α}
    let w := fun z : Z ↦ (⟨z.val.re - 1/2, z.val.im⟩ : ℂ)
    let m := fun z : Z ↦ spectralStripMultiplicity α s (w z).re (D z.val).toNat
    let J := Σ z, Fin (m z)
    let I := Ioo (-(α+s+2)) (α+s+2)
    let P := spectralProjection (F := F) (1/2) ha (show 0 ≤ s by linarith)
    ∀ (j : PositiveRealExponentialDecay I →L[ℂ] Ws(α,s)) (Λ : J → StrongDual ℂ Ws(α,s)),
      (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) →
      (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
        (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) →
      (⨅ l, (Λ l).ker).orthogonal.starProjection.comp (L.adjoint.comp P) = L.adjoint.comp P := by
  intro D Z w m J I P j Λ hj hΛ
  have hs0 : 0 ≤ s := by linarith
  let N := ⨅ l, (Λ l).ker
  let Θ := globalThetaSobolev F (1/2) (neg_le_self ha) hs0
  apply projection_comp_adjoint_of_mapsTo L N Θ
  intro f hf
  apply spectralStripJet_reverse_synthesis χ hχ ha hs0
  intro i
  let b := i.val.2.1
  let t := i.val.2.2.1
  let k := i.val.2.2.2
  let q := point(b,t)
  let z₀ := point(1/2+b,t)
  have hq : q.re = b := by simp [q]
  have hz : z₀.re-1/2 = b := by simp [z₀]
  have hzq : (⟨z₀.re-1/2,z₀.im⟩ : ℂ) = q := by
    apply Complex.ext <;> simp [q,z₀]
  let N₀ := (meromorphicOrderAt (continuedCompletedHeckeL (χ i.val.1)) z₀).untop₀.toNat
  have hk : k < spectralStripMultiplicity α s q.re N₀ := by
    rw [hq]
    exact i.property
  have he := (SharpStripEval.lt_spectralStripMultiplicity_iff_bounded_eval α s ha hs0 N₀ k q).mp hk
  by_cases hξ : i.val.1 = ξ
  · have hD : (D z₀).toNat = N₀ := by
      change (MeromorphicOn.divisor (continuedCompletedHeckeL (χ ξ)) univ z₀).toNat = _
      rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (χ ξ)).1.meromorphicOn (mem_univ _)]
      simp only [N₀,hξ]
    have hpos : 0 < D z₀ := by
      have h := he.1
      rw [←hD] at h
      omega
    let z : Z := ⟨z₀,hpos,hz ▸ abs_le.mpr (i.mem_strip_order_pos ha).1⟩
    have hw : w z = q := hzq
    have hmk : k < m z := by
      dsimp only [m]
      rw [hw]
      simpa only [z,hD] using hk
    let l : J := ⟨z,⟨k,hmk⟩⟩
    have hv (p : PositiveRealExponentialDecay univ) (u : Ws(α,s))
        (hu : (u : ℝ → ℂ) =ᵐ[volume] p.val) :
        Λ l u = iteratedDeriv k (mellin (fun t ↦ p.val (Real.log t))) q := by
      obtain ⟨v,hv⟩ := restrict_entire_profile I p
      have rep : u = j v := Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq
        (hu.trans ((hj v).trans (hv ▸ Filter.EventuallyEq.rfl)).symm))
      rw [rep]
      exact (hΛ l v).trans (by simp only [l,hv,hw])
    have heq := spectralStripJet_pairing_radial_eval χ hχ ξ ha hs0 i L hL ν hlog (Λ l) hv f
    have hfl : Λ l f = 0 := (Submodule.mem_iInf _).mp hf l
    simpa only [ite_eq_left hξ,hfl,mul_zero] using heq
  · obtain ⟨Λ',hΛ'⟩ := he.2
    simpa only [ite_eq_right hξ] using
      spectralStripJet_pairing_radial_eval χ hχ ξ ha hs0 i L hL ν hlog Λ' hΛ' f

end RiemannMasullo.StripNuclearity
