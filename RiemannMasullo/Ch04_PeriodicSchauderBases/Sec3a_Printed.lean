module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a

import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # Chapter 4.3: printed isotypic transform norm bounds -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function MeasureTheory
open scoped CompactlySupported NNReal

/-- Paper: Equation (4.3.2.5), p. 178. As printed: for every second-countable
modulated group with a section to its module and choices of Haar measures,
each character component satisfies the displayed bound on compactly supported
continuous functions. The Hilbert sum transform in Lemma 4.3.2.2, p. 179, and
the restriction of each component to its isotype on p. 180 are isometries. These are the norm clauses. See
`regularIsotypicTransform_norm_sq` and ERRATA F211. -/
def Printed.regularIsotypicTransform_isometries : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    (ν : Measure G) [ν.IsHaarMeasure]
    (ν₁ : Measure m.toMonoidHom.ker) [ν₁.IsHaarMeasure]
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m),
    (∀ (ω : PontryaginDual m.toMonoidHom.ker) (φ : G →C_c ℂ),
      let f := (regularL2_memLp_compactlySupported ν φ).toLp φ
      ‖regularIsotypicComponent m hm ν ν₁ τ hτ ω f‖ ≤ ‖f‖) ∧
    Isometry (regularIsotypicTransform m hm ν ν₁ τ hτ) ∧
    ∀ ω : PontryaginDual m.toMonoidHom.ker,
      Isometry (fun f : {f : RegularL2 ν // ∀ k : m.toMonoidHom.ker,
          regularTranslate ν (k : G) f = (ω k : ℂ) • f} ↦
        regularIsotypicComponent m hm ν ν₁ τ hτ ω f.val)

/-- Paper: Equation (4.3.2.5), p. 178. Take G = ℝ₊ˣ, with identity module and
section, ν = dt/t and ν₁ = 2δ₁ on the trivial kernel. The unique isotype is all
of L², and the continuous test φ(t) = max(0, 1 − |log t|) has compact support and
positive L² norm. Both the component and the Hilbert sum transform double its norm.
Even with product normalization, the idele class group of ℚ(i) gives the norm
factor √(π/4) in the isometry of Lemma 4.3.2.2, p. 179, and in the isotype isometry on p. 180. -/
theorem Printed.regularIsotypicTransform_isometries_false :
    ¬ Printed.regularIsotypicTransform_isometries := by
  intro h
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  have hm : IsModulation m := ⟨isProperMap_id, exists_ne 1⟩
  have hsection : RightInverse m m := fun _ ↦ rfl
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let logHomeo := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have : LocallyCompactSpace ℝ≥0ˣ := logHomeo.isOpenEmbedding.locallyCompactSpace
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let K := m.toMonoidHom.ker
  have hk (k : K) : (k : ℝ≥0ˣ) = 1 := k.property
  have : Subsingleton K := ⟨fun a b ↦ Subtype.ext ((hk a).trans (hk b).symm)⟩
  let δ : Measure K := Measure.dirac 1
  have : δ.IsMulLeftInvariant := by
    rw [show δ = Measure.count from (Subsingleton.count_eq_dirac (1 : K)).symm]
    infer_instance
  have : δ.IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ hs.measure_lt_top
      open_pos := fun s _ hs ↦ by
        obtain ⟨k, hks⟩ := hs
        have h1 : (1 : K) ∈ s := Subsingleton.elim k 1 ▸ hks
        simp [δ, Measure.dirac_apply_of_mem h1] }
  let ν₁ := (2 : ENNReal) • δ
  have : ν₁.IsHaarMeasure := Measure.IsHaarMeasure.smul δ (by norm_num) (by simp)
  have hmass : ν₁ Set.univ = 2 := by simp [ν₁, δ]
  have hmap : (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ (z.1 : ℝ≥0ˣ) * m z.2) =
      (2 : ENNReal) • positiveRealHaar := by
    have hproj : (fun z : K × ℝ≥0ˣ ↦ (z.1 : ℝ≥0ˣ) * m z.2) = Prod.snd := by
      funext z
      exact (congrArg (· * z.2) (hk z.1)).trans (one_mul z.2)
    rw [hproj, Measure.map_snd_prod, hmass]
  obtain ⟨s, hs, hopen, hfinite⟩ := positiveRealHaar.exists_isOpen_measure_lt_top 1
  let f : RegularL2 positiveRealHaar := indicatorConstLp 2 hopen.measurableSet hfinite.ne (1 : ℂ)
  have hf : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos (hopen.measure_pos _ ⟨1, hs⟩).ne' hfinite.ne) _
  let T := regularIsotypicTransform m hm positiveRealHaar ν₁ m hsection
  have hT : Isometry T := (h ℝ≥0ˣ m hm positiveRealHaar ν₁ m hsection).2.1
  obtain ⟨L, hL⟩ := regularIsotypicTransform_continuousLinear m hm positiveRealHaar ν₁ m hsection
  have hzero : T 0 = 0 := (hL 0).symm.trans L.map_zero
  have hnorm : ‖T f‖ = ‖f‖ := by
    simpa only [hzero, dist_zero_right] using hT.dist_eq f 0
  have hsq : ‖T f‖ ^ 2 = 4 * ‖f‖ ^ 2 := by
    have hsq := regularIsotypicTransform_norm_sq m hm positiveRealHaar ν₁ m hsection 2 hmap f
    norm_num [T, hmass, measureReal_def] at hsq ⊢
    exact hsq
  rw [hnorm] at hsq
  nlinarith

end RiemannMasullo
