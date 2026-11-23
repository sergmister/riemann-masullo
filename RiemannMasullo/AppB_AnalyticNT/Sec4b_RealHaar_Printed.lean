module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # The printed real Haar normalization in §12.4 -/

@[expose] public noncomputable section

open MeasureTheory NumberField
open scoped NNReal

namespace RiemannMasullo

/-- Paper: Theorem 12.4.1.1, prose after (12.4.1.3), p. 514.
As printed: at every real place the multiplicative Tamagawa measure itself is the canonical
Haar measure for the local absolute value. This is the real-place clause of the list.
See `infiniteCanonicalHaar_eq_smul_tamagawa` and ERRATA F245. -/
def Printed.infiniteCanonicalHaar_eq_tamagawa_of_isReal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), w.IsReal →
    letI _completionSecondCountable : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    letI _unitsSecondCountable : SecondCountableTopology w.Completionˣ :=
      (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
    letI _completionMeasurable : MeasurableSpace w.Completion := borel _
    letI _completionBorel : BorelSpace w.Completion := ⟨rfl⟩
    letI _unitsBorel : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let m : w.Completionˣ →ₜ* ℝ≥0ˣ :=
      ⟨(Units.map nnNormHom.toMonoidHom) ^ w.mult, continuous_infiniteLocalModule w⟩
    ∃ hm : IsModulation m,
      canonicalModulatedHaar m hm = infiniteLocalMultiplicativeTamagawaMeasure F w

/-- Paper: Theorem 12.4.1.1, prose after (12.4.1.3), p. 514.
Take the real place of `ℚ`, with completion `ℝ` and local absolute value `|x|`.
The preimage of `[1/2, 2]` consists of the positive and negative copies of that interval.
The Tamagawa measure `dx/|x|` gives it mass `4 log 2`, whereas canonical Haar measure
gives it mass `2 log 2`, since its pushforward under `|x|` is `dt/t`. -/
theorem Printed.infiniteCanonicalHaar_eq_tamagawa_of_isReal_false :
    ¬ Printed.infiniteCanonicalHaar_eq_tamagawa_of_isReal := by
  intro h
  let w : InfinitePlace ℚ := Rat.infinitePlace
  have hw : w.IsReal := Rat.isReal_infinitePlace
  obtain ⟨hm, hc⟩ := h ℚ w hw
  obtain ⟨hm', hc'⟩ := infiniteCanonicalHaar_eq_smul_tamagawa w
  rw [ite_eq_left hw] at hc'
  have hT := hc.symm.trans hc'
  have hHaar := infiniteLocalMultiplicativeTamagawaMeasure_haar ℚ w
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : w.Completionˣ)
  have hpos :=
    (Measure.measure_pos_of_mem_nhds (infiniteLocalMultiplicativeTamagawaMeasure ℚ w) hK1).ne'
  have hfin := (hK.measure_lt_top (μ := infiniteLocalMultiplicativeTamagawaMeasure ℚ w)).ne
  have hTK := congrArg (fun μ ↦ μ K) hT
  simp only [smul_apply, smul_eq_mul] at hTK
  have hr := congrArg ENNReal.toReal hTK
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at hr
  have := ENNReal.toReal_pos hpos hfin
  linarith

end RiemannMasullo
