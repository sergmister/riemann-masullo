module

public import RiemannMasullo.Research.StripNuclearity.AngularProfileCosts
public import RiemannMasullo.Research.StripNuclearity.ScalarKernel
public import RiemannMasullo.Research.StripNuclearity.AngularChoice

/-!
# Radial profile costs on an idèle class group

Use the canonical positive norm section to extract a compact character from
an actual compact Bruhat test. The positive angular sign agrees with the
inverse-character radial embedding in the Chapter 10 Hilbert space.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NumberField.AdeleRing NNReal FourierTransform ContDiff Topology

namespace RiemannMasullo.StripNuclearity

private theorem exists_normSection_logChart {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m) :
    ∃ e : m.toMonoidHom.ker × Multiplicative ℝ ≃ₜ* G,
      ∀ k t, e (k,t) = k.val * σ (radialExponential t) := by
  let r : ℝ≥0ˣ ≃ₜ m.toMonoidHom.range :=
    { toFun := fun t ↦ ⟨t,σ t,hσ t⟩, invFun := Subtype.val,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
      continuous_toFun := continuous_id.subtype_mk _, continuous_invFun := continuous_subtype_val }
  let d : m.toMonoidHom.ker × Multiplicative ℝ ≃ₜ* m.toMonoidHom.ker × m.toMonoidHom.range :=
    { (Homeomorph.refl m.toMonoidHom.ker).prodCongr (radialExponential.toHomeomorph.trans r) with
      map_mul' := fun x y ↦ Prod.ext rfl (Subtype.ext (radialExponential.map_mul x.2 y.2)) }
  let i : m.toMonoidHom.range →ₜ* ℝ≥0ˣ := ⟨m.toMonoidHom.range.subtype,continuous_subtype_val⟩
  obtain ⟨b,hb⟩ := hm.exists_prod_equiv (σ.comp i) fun t ↦ hσ t
  exact ⟨d.trans b,fun k t ↦ hb k (r (radialExponential t))⟩

/-- Fixed-support angular derivative estimates for a compact Bruhat test and
a section of any surjective modulation. -/
theorem normSection_summable_angularProfile_derivatives {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m)
    (μK : Measure m.toMonoidHom.ker) [μK.IsHaarMeasure] (φ : BruhatCompactSupport G) :
    let p (ξ : PontryaginDual m.toMonoidHom.ker) (t : ℝ) :=
      ∫ k : m.toMonoidHom.ker, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μK
    ∃ J : Set ℝ, IsCompact J ∧ (∀ ξ, tsupport (p ξ) ⊆ J ∧ ContDiff ℝ (∞) (p ξ)) ∧
      ∀ (ρs : List (PontryaginDual m.toMonoidHom.ker →ₜ* Multiplicative ℝ)) (j : ℕ),
        Summable (fun ξ : PontryaginDual m.toMonoidHom.ker ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod *
          ∫ t : ℝ, ‖iteratedDeriv j (p ξ) t‖) := by
  intro p
  let : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let : SecondCountableTopology m.toMonoidHom.ker := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hf : φ.val ∈ schwartzBruhatSubmodule G := by
    rw [← modulatedExponentialDecaySubmodule_singleton_zero m]
    exact bruhatCompactSupport_le_modulatedExponentialDecay m {0} hm hσ.surjective φ.property
  let f : SchwartzBruhat G := ⟨φ.val,hf⟩
  obtain ⟨e,he⟩ := exists_normSection_logChart m hm σ hσ
  have hprofile (ξ : PontryaginDual m.toMonoidHom.ker) : positiveAngularProfile μK e f.val ξ = p ξ := by
    funext t
    simp only [positiveAngularProfile,he,f,p]
  simpa only [hprofile] using summable_positiveAngularProfile_derivatives μK e f
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)) φ.property.2


variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

set_option quotPrecheck false

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "m𝔽" => (⟨ideleClassNorm F,(isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)

/-- Radial Fourier profiles of a compact Bruhat test on any number field.
The same compact set supports all profiles. Their radial derivative costs
sum with every finite product of squared real angular frequencies. The
positive section and the normalization of compact Haar are explicit. -/
theorem ideleClass_summable_angularProfile_derivatives (μK : Measure C₁) [μK.IsHaarMeasure]
    (φ : BruhatCompactSupport C𝔽) :
    let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _,continuous_quotient_mk'⟩
    let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp ⟨canonicalIdeleNormSection F,canonicalIdeleNormSection_continuous F⟩
    let p (ξ : PontryaginDual C₁) (t : ℝ) :=
      ∫ k : C₁, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μK
    ∃ J : Set ℝ, IsCompact J ∧ (∀ ξ, tsupport (p ξ) ⊆ J ∧ ContDiff ℝ (∞) (p ξ)) ∧
      ∀ (ρs : List (PontryaginDual C₁ →ₜ* Multiplicative ℝ)) (j : ℕ),
        Summable (fun ξ : PontryaginDual C₁ ↦ (ρs.map (fun ρ ↦ 1+((ρ ξ).toAdd)^2)).prod *
          ∫ t : ℝ, ‖iteratedDeriv j (p ξ) t‖) := by
  intro q σ
  exact normSection_summable_angularProfile_derivatives m𝔽
    ⟨isProperMap_ideleClassNorm F,ideleClassNorm_ne_one (F := F)⟩
    σ (canonicalIdeleNormSection_rightInverse F) μK φ

end RiemannMasullo.StripNuclearity
