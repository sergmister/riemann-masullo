module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2

/-! # Character coordinates for a section of the idele class norm

Appendix B indexes the unitary characters that are trivial on its chosen norm
section. Restriction to the compact norm-one group identifies this index with
the angular index of the spectral trace.
-/

@[expose] public noncomputable section

open Function NumberField
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "incl" => (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)

/-- Paper: Theorem B.4.4.7, pp. 623–624, in the coordinates of (10.2.1.4),
p. 440. A character of the norm-one group extends uniquely to a unitary idele
class character trivial on a chosen continuous section of the norm.
Deviation: Equation (B.4.4.16) directly indexes the quasicharacters at zeros.
The section supplies the unitary character coordinate in that index. -/
def normSectionCharacterEquiv (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    PontryaginDual C₁ ≃ {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} := by
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let P := ContinuousMonoidHom.id C𝔽 / τ.comp n
  have hP (x : C𝔽) : P x ∈ C₁ := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, hτ, div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨P.toMonoidHom.codRestrict C₁ hP, P.continuous.subtype_mk _⟩
  have htriv (ξ : PontryaginDual C₁) (t : ℝ≥0ˣ) : ξ (r (τ t)) = 1 := by
    have h : r (τ t) = 1 := by
      apply Subtype.ext
      change τ t / τ (ideleClassNorm F (τ t)) = 1
      rw [hτ, div_self']
    exact (congrArg ξ h).trans (map_one ξ)
  refine ⟨fun ξ ↦ ⟨ξ.comp r, htriv ξ⟩, fun η ↦ η.val.comp incl, ?_, ?_⟩
  · intro ξ
    ext x : 1
    change ξ (r x.val) = ξ x
    congr 1
    apply Subtype.ext
    change x.val / τ (ideleClassNorm F x.val) = x.val
    rw [show ideleClassNorm F x.val = 1 from x.property, map_one, div_one]
  · intro η
    apply Subtype.ext
    ext x : 1
    change η.val (x / τ (ideleClassNorm F x)) = η.val x
    rw [map_div, η.property, div_one]

/-- The section-normalized extensions restrict to their original angular characters. -/
theorem isSpectralBasepointChoice_normSection (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    IsSpectralBasepointChoice (fun ξ ↦ (normSectionCharacterEquiv τ hτ ξ).val) :=
  (normSectionCharacterEquiv τ hτ).left_inv

end RiemannMasullo.StripNuclearity
