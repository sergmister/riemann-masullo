module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-!
# Trace-norm bounds between two Hilbert spaces
-/

@[expose] public noncomputable section

namespace RiemannMasullo.StripNuclearity

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace H] in
private theorem approximationNumber_sandwich_le (A : E →L[ℂ] E)
    (B : H →L[ℂ] E) (C : E →L[ℂ] H) (n : ℕ) :
    approximationNumber (C.comp (A.comp B)) n ≤ (‖C‖*‖B‖) * approximationNumber A n := by
  apply le_mul_of_forall_lt₀
  intro a ha b hb
  have hn : (0 : E →L[ℂ] E).toLinearMap.rank ≤ (n : Cardinal) := by simp
  unfold approximationNumber at hb
  obtain ⟨_,⟨S,hS,rfl⟩,herr⟩ := exists_lt_of_csInf_lt (by exact ⟨_,0,hn,rfl⟩) hb
  have hpre : (S.comp B).toLinearMap.rank ≤ (n : Cardinal) :=
    (LinearMap.rank_comp_le_left B.toLinearMap S.toLinearMap).trans hS
  have hpost : (C.comp (S.comp B)).toLinearMap.rank ≤ (n : Cardinal) := by
    apply Cardinal.lift_le.mp
    exact (LinearMap.lift_rank_comp_le_right (S.comp B).toLinearMap C.toLinearMap).trans
      (by simpa only [Cardinal.lift_natCast] using Cardinal.lift_le.mpr hpre)
  calc
    _ ≤ ‖C.comp (S.comp B) - C.comp (A.comp B)‖ := by
      unfold approximationNumber
      exact csInf_le ⟨0,fun _ ⟨_,_,h⟩ ↦ h ▸ norm_nonneg _⟩ ⟨_,hpost,rfl⟩
    _ = ‖C.comp ((S-A).comp B)‖ := by rw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]
    _ ≤ ‖C‖ * (‖S-A‖*‖B‖) :=
      (C.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ((S-A).opNorm_comp_le B) (norm_nonneg C))
    _ = (‖C‖*‖B‖) * ‖S-A‖ := by ring
    _ ≤ a*b := mul_le_mul ha.le herr.le (norm_nonneg _) ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans ha.le)

/-- Transport a nuclear endomorphism through two bounded maps connecting different
Hilbert spaces. The trace norm grows by at most the product of their operator norms. -/
theorem traceNorm_sandwich_le (A : E →L[ℂ] E) (hA : IsNuclearOperator A)
    (B : H →L[ℂ] E) (C : E →L[ℂ] H) :
    ∃ h : IsNuclearOperator (C.comp (A.comp B)), traceNorm ⟨C.comp (A.comp B),h⟩ ≤
      (‖C‖*‖B‖)*traceNorm ⟨A,hA⟩ := by
  let V := C.comp (A.comp B)
  have ht := (mem_traceClassOperators_iff_isNuclearOperator A).mpr hA
  have hs : Summable (approximationNumber A) := by simpa only [Real.rpow_one] using ht.2
  have hn (n : ℕ) : 0 ≤ approximationNumber V n :=
    Real.sInf_nonneg fun _ ⟨_,_,h⟩ ↦ h ▸ norm_nonneg _
  have hcomp (n : ℕ) := approximationNumber_sandwich_le A B C n
  have hv : Summable (approximationNumber V) :=
    (hs.mul_left (‖C‖*‖B‖)).of_nonneg_of_le hn hcomp
  have hV : IsNuclearOperator V := (mem_traceClassOperators_iff_isNuclearOperator V).mp
    ⟨(ht.1.comp_clm B).clm_comp C,by simpa only [Real.rpow_one] using hv⟩
  refine ⟨hV,?_⟩
  rw [← schattenNorm_one_eq_traceNorm,← schattenNorm_one_eq_traceNorm]
  simp only [schattenNorm,Real.rpow_one,div_one]
  exact (hv.tsum_le_tsum hcomp (hs.mul_left _)).trans_eq (tsum_mul_left)

/-- A scalar projection acting identically on the pulled-back ambient range can be
inserted before the adjoint lift. Its trace cost then transfers to the ambient endomorphism. -/
theorem projected_traceNorm_sandwich_le (L : E →L[ℂ] H) (A Q : E →L[ℂ] E)
    (P : H →L[ℂ] H) (h : IsNuclearOperator (A.comp Q))
    (hp : Q.comp (L.adjoint.comp P) = L.adjoint.comp P) :
    ∃ hn : IsNuclearOperator ((L.comp (A.comp L.adjoint)).comp P),
      traceNorm ⟨(L.comp (A.comp L.adjoint)).comp P,hn⟩ ≤
        (‖L‖*(‖L‖*‖P‖))*traceNorm ⟨A.comp Q,h⟩ := by
  have he : (L.comp (A.comp L.adjoint)).comp P = L.comp ((A.comp Q).comp (L.adjoint.comp P)) := by
    simp only [ContinuousLinearMap.comp_assoc,hp]
  rw [he]
  obtain ⟨hn,hb⟩ := traceNorm_sandwich_le (A.comp Q) h (L.adjoint.comp P) L
  refine ⟨hn,hb.trans (mul_le_mul_of_nonneg_right ?_ ?_)⟩
  · exact mul_le_mul_of_nonneg_left ((L.adjoint.opNorm_comp_le P).trans_eq
      (congrArg (· * ‖P‖) (ContinuousLinearMap.adjoint.norm_map L))) (norm_nonneg _)
  · let : Norm (nuclearEndomorphisms E) := ⟨traceNorm⟩
    exact (traceNorm_normedSpaceCore (H := E)).norm_nonneg ⟨_,h⟩

end RiemannMasullo.StripNuclearity
