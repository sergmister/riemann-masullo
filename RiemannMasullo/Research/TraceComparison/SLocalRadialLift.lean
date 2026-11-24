module

public import RiemannMasullo.Ch03_IdelicZeta.Sec1
public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import RiemannMasullo.Research.StripNuclearity.ScalarKernel

/-! # An explicit radial lift to the S-idèles

For a finite projected group of S-units, the S-norm is proper. Dividing a
compact smooth log-norm profile by the group order then gives a compact
Bruhat test whose periodization is the restriction of the global radial test.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set
open scoped BigOperators ContDiff NNReal NumberField.AdeleRing Pointwise

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "N(" x ")" => ((sIdeleNorm F S (x : Iₛ)).val : ℝ)

attribute [local instance] instSIdeleLocallyCompactSec1 instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1
local instance radialLiftSIdeleT2 : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- Compactness of the projected S-units makes the S-idelic norm proper
already on the S-idèles themselves. -/
theorem isProperMap_sIdeleNorm_of_compact_projectedDiagonal (hH : IsCompact (Hₛ : Set Iₛ)) :
    IsProperMap (sIdeleNorm F S) := by
  have hq : IsProperMap (QuotientGroup.mk : Iₛ → SIdeleQuotient F S) := by
    refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe hH, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← image_singleton, QuotientGroup.preimage_image_mk_eq_mul]
    exact isCompact_singleton.mul hH
  exact (isProperMap_sIdeleQuotientNorm F S).comp hq

/-- Paper: (12.4.1.4), p. 515. If the projected S-units are finite, a smooth
compact global log-norm profile admits an explicit lift. Its value is the same
profile of the S-norm divided by the number of projected S-units, and its
periodization gives the restricted global test.
Deviation: This proves the finite projected-unit case for radial tests. -/
theorem exists_sLocalTraceLift_radial_of_finite [Finite Hₛ]
    (G : ℝ → ℂ) (hg : ContDiff ℝ (∞) G) (hc : HasCompactSupport G)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ x, φ.val x = G (Real.log ((ideleClassNorm F x).val : ℝ))) :
    ∃ f : BruhatCompactSupport Iₛ,
      (∀ x, f.val x = (Nat.card Hₛ : ℂ)⁻¹ * G (Real.log N(x))) ∧
      ∀ x : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * x))
        (φ.val (QuotientGroup.mk (sIdeleInsertion F S x))) := by
  classical
  let := Fintype.ofFinite Hₛ
  have hn := isProperMap_sIdeleNorm_of_compact_projectedDiagonal
    (F := F) (S := S) (finite_coe_iff.mp (inferInstance : Finite Hₛ)).isCompact
  let E := StripNuclearity.radialExponential
  let L := (E.symm : ℝ≥0ˣ →ₜ* Multiplicative ℝ).comp ⟨sIdeleNorm F S, hn.continuous⟩
  have hL : IsProperMap L := E.symm.toHomeomorph.isProperMap.comp hn
  obtain ⟨f₀, hf₀⟩ := exists_bruhatCompactSupport_of_proper_realHom L hL G hg hc
  let f := (Nat.card Hₛ : ℂ)⁻¹ • f₀
  have hf (x : Iₛ) : f.val x = (Nat.card Hₛ : ℂ)⁻¹ * G (Real.log N(x)) := by
    change (Nat.card Hₛ : ℂ)⁻¹ * f₀.val x = _
    rw [hf₀]
    congr 2
    change (E.symm (sIdeleNorm F S x)).toAdd = _
    obtain ⟨t, ht⟩ := E.surjective (sIdeleNorm F S x)
    rw [← ht, ContinuousMulEquiv.symm_apply_apply]
    exact (Real.log_exp t.toAdd).symm
  refine ⟨f, hf, fun x ↦ ?_⟩
  have he (ξ : Hₛ) : f.val (ξ.val * x) = (Nat.card Hₛ : ℂ)⁻¹ * G (Real.log N(x)) := by
    have hξ : (QuotientGroup.mk ξ.val : SIdeleQuotient F S) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ξ.property
    have hnξ : sIdeleNorm F S ξ.val = 1 := (congrArg (sIdeleQuotientNorm F S) hξ).trans (map_one _)
    rw [hf, map_mul, hnξ, one_mul]
  have hsum := hasSum_fintype (fun ξ : Hₛ ↦ f.val (ξ.val * x))
  have hz : (Nat.card Hₛ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hφ]
  change HasSum _ (G (Real.log ((ideleNorm F (sIdeleInsertion F S x)).val : ℝ)))
  rw [ideleNorm_sIdeleInsertion]
  convert hsum using 1
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

end RiemannMasullo
