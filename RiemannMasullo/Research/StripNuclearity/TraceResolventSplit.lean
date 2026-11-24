module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-!
# Trace-norm control for a projected resolvent split
-/

@[expose] public noncomputable section

namespace RiemannMasullo.StripNuclearity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Hilbert adjoint preserves the trace norm of a nuclear operator. -/
theorem traceNorm_adjoint_eq (T : H →L[ℂ] H) (hT : IsNuclearOperator T) :
    ∃ h : IsNuclearOperator T.adjoint, traceNorm ⟨T.adjoint,h⟩ = traceNorm ⟨T,hT⟩ := by
  have hTc := (mem_traceClassOperators_iff_isNuclearOperator T).mpr hT
  have hnum (n : ℕ) : approximationNumber T n = approximationNumber T.adjoint n := by
    by_cases hn : (n : Cardinal) < Module.rank ℂ H
    · exact approximationNumber_adjoint T hTc.1 n hn
    · have hle : Module.rank ℂ H ≤ (n : Cardinal) := le_of_not_gt hn
      have hzero (A : H →L[ℂ] H) : approximationNumber A n = 0 := by
        unfold approximationNumber
        refine le_antisymm ?_ (Real.sInf_nonneg ?_)
        · refine csInf_le ⟨0,?_⟩ ?_
          · rintro _ ⟨S,_,rfl⟩
            exact norm_nonneg _
          · exact ⟨A,(Submodule.rank_le _).trans hle, by simp⟩
        · rintro _ ⟨S,_,rfl⟩
          exact norm_nonneg _
      rw [hzero T,hzero T.adjoint]
  have hA : IsNuclearOperator T.adjoint :=
    (mem_traceClassOperators_iff_isNuclearOperator _).mp
      ⟨isCompactOperator_adjoint_of_compact T hTc.1,hTc.2.congr fun n ↦ congrArg (· ^ (1 : ℝ)) (hnum n)⟩
  refine ⟨hA,?_⟩
  rw [← schattenNorm_one_eq_traceNorm,← schattenNorm_one_eq_traceNorm]
  simp only [schattenNorm,Real.rpow_one,div_one]
  exact tsum_congr (fun n ↦ (hnum n).symm)

/-- A compactly localized term and two bounded factors of a projected
resolvent give an explicit trace-norm bound for their sum. -/
theorem traceNorm_resolvent_split_le (B U R P D₁ D₂ : H →L[ℂ] H)
    (hB : B = U.adjoint.comp P + D₁.adjoint.comp (R.adjoint.comp P) + D₂.adjoint.comp (R.adjoint.comp P))
    (hU : IsNuclearOperator U) (hR : IsNuclearOperator (R.adjoint.comp P)) :
    ∃ h : IsNuclearOperator B, traceNorm ⟨B,h⟩ ≤
      ‖P‖*traceNorm ⟨U,hU⟩ + (‖D₁‖+‖D₂‖)*traceNorm ⟨R.adjoint.comp P,hR⟩ := by
  obtain ⟨hUA,hUN⟩ := traceNorm_adjoint_eq U hU
  let Z := (⟨U.adjoint,hUA⟩ : nuclearEndomorphisms H)
  let V := (⟨R.adjoint.comp P,hR⟩ : nuclearEndomorphisms H)
  let L := (⟨_,mul_mem_nuclearEndomorphisms_right P Z⟩ : nuclearEndomorphisms H)
  let D (T : H →L[ℂ] H) := (⟨_,mul_mem_nuclearEndomorphisms_left T.adjoint V⟩ : nuclearEndomorphisms H)
  let S := L + D D₁ + D D₂
  have he : B = S.val := hB
  suffices hs : traceNorm S ≤ _ from ⟨he.symm ▸ S.property, (congrArg traceNorm (Subtype.ext he)).le.trans hs⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hc := traceNorm_normedSpaceCore (H := H)
  have hL : traceNorm L ≤ ‖P‖*traceNorm ⟨U,hU⟩ := (traceNorm_mul_right_le P Z).trans_eq (congrArg (‖P‖ * ·) hUN)
  have hD (T : H →L[ℂ] H) : traceNorm (D T) ≤ ‖T‖*traceNorm V :=
    (traceNorm_mul_left_le T.adjoint V).trans_eq (congrArg (· * traceNorm V) (ContinuousLinearMap.adjoint.norm_map T))
  have hsum : traceNorm S ≤ traceNorm L + traceNorm (D D₁) + traceNorm (D D₂) :=
    (hc.norm_triangle (L + D D₁) (D D₂)).trans (add_le_add (hc.norm_triangle L (D D₁)) le_rfl)
  exact hsum.trans ((add_le_add (add_le_add hL (hD D₁)) (hD D₂)).trans_eq (by dsimp [V]; ring))

end RiemannMasullo.StripNuclearity
