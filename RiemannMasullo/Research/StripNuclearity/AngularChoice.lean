module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2

/-!
# Angular characters with trivial radial restriction

Normalizing on the canonical norm section makes products of compact characters
lift multiplicatively. It also identifies radial profiles of angular Fourier
coefficients without a character-dependent norm twist.
-/

@[expose] public noncomputable section

open Function NumberField
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo.StripNuclearity

/-- The extension of compact characters in §10.2 may be chosen as a group
homomorphism whose values are all trivial on the positive norm section. -/
theorem exists_spectralBasepointChoice_radially_trivial (F : Type*) [Field F] [NumberField F] :
    let C := IdeleClassGroup (𝓞 F) F
    let q : IdeleGroup (𝓞 F) F →ₜ* C := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
    let σ : ℝ≥0ˣ →ₜ* C := q.comp
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    ∃ χ : PontryaginDual (ideleClassNorm F).ker →* PontryaginDual C,
      IsSpectralBasepointChoice χ ∧ ∀ ξ t, χ ξ (σ t) = 1 := by
  intro C q σ
  let n : C →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hσ : RightInverse σ n := canonicalIdeleNormSection_rightInverse F
  let P : C →ₜ* C := ContinuousMonoidHom.id C / σ.comp n
  have hP (x : C) : P x ∈ (ideleClassNorm F).ker := by
    change n (x / σ (n x)) = 1
    rw [map_div, hσ, div_self']
  let r : C →ₜ* (ideleClassNorm F).ker :=
    ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  let χ : PontryaginDual (ideleClassNorm F).ker →* PontryaginDual C :=
    ⟨⟨fun ξ ↦ ξ.comp r, rfl⟩, fun _ _ ↦ rfl⟩
  refine ⟨χ, fun ξ ↦ ?_, fun ξ t ↦ ?_⟩
  · ext x : 1
    change ξ (r x.val) = ξ x
    congr 1
    apply Subtype.ext
    change x.val / σ (n x.val) = x.val
    rw [show n x.val = 1 from x.property, map_one, div_one]
  · have h : r (σ t) = 1 := by
      apply Subtype.ext
      change σ t / σ (n (σ t)) = 1
      rw [hσ, div_self']
    change ξ (r (σ t)) = 1
    rw [h, map_one]

end RiemannMasullo.StripNuclearity
