module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a

/-! # Appendix D.1.2: the printed existence claim for Haar fibre integrals -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory

universe u

/-- Paper: Theorem D.1.2.1, p. 747. As printed: for every μ_G-measurable
complex-valued function, the Haar integral over the translate of the closed
subgroup by x exists for μ_G-almost every x. This is the existence assertion in
the second sentence. See `weilQuotientMeasure_existsUnique`,
`weilQuotientIntegral_L1` and ERRATA F230. -/
def Printed.weilQuotientIntegral_measurable : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μG : Measure G) [μG.IsHaarMeasure] [μG.Regular]
      (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
      (f : G → ℂ), AEMeasurable f μG →
        ∀ᵐ x ∂μG, Integrable (fun h : H ↦ f (x * (h : G))) μH

/-- The top subgroup of `Multiplicative (ULift ℤ)` is not compact. -/
private theorem Printed.weilQuotientIntegral_measurable_false_noncompact :
    NoncompactSpace (⊤ : Subgroup (Multiplicative (ULift.{u} ℤ))) := by
  rw [← not_compactSpace_iff]
  intro _
  have h1 : Finite (⊤ : Subgroup (Multiplicative (ULift.{u} ℤ))) :=
    finite_of_compact_of_discrete
  have h2 : Finite (Multiplicative (ULift.{u} ℤ)) :=
    Finite.of_equiv _ Subgroup.topEquiv.toEquiv
  have h3 : Finite ℤ := Finite.of_equiv _ (Multiplicative.toAdd.trans Equiv.ulift)
  exact not_finite ℤ

private theorem Printed.weilQuotientIntegral_measurable_false_univ
    (h : Printed.weilQuotientIntegral_measurable.{u}) : False := by
  have := Printed.weilQuotientIntegral_measurable_false_noncompact.{u}
  let μG : Measure (Multiplicative (ULift.{u} ℤ)) := Measure.haar
  let μH : Measure (⊤ : Subgroup (Multiplicative (ULift.{u} ℤ))) := Measure.haar
  have key := h (Multiplicative (ULift.{u} ℤ)) ⊤ (by simp) μG μH (fun _ ↦ 1) aemeasurable_const
  have hfalse : ∀ᵐ _ ∂μG, False := key.mono fun _ hx ↦ by
    rcases integrable_const_iff.1 hx with h0 | hfin
    · exact one_ne_zero h0
    · exact (measure_lt_top μH Set.univ).ne (measure_univ_of_isMulLeftInvariant μH)
  exact NeZero.ne μG (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse))

/-- Paper: Theorem D.1.2.1, p. 747. Take G = H = ℝ under addition, with Lebesgue
Haar measures, and f identically one. The integral over each fibre has infinite
mass, so no fibre has a complex Haar integral. For the sign function both the
positive and negative parts have infinite mass on every fibre. -/
theorem Printed.weilQuotientIntegral_measurable_false :
    ¬ Printed.weilQuotientIntegral_measurable :=
  fun h ↦ Printed.weilQuotientIntegral_measurable_false_univ h

end RiemannMasullo
