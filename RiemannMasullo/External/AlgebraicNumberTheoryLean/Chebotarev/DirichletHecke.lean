/-
Vendored from jonhanke/algebraic-number-theory-lean, commit
5ea368e03a066197d53114efa8be66d351a9f060, file NumberFieldKB/Chebotarev/DirichletHecke.lean
(lines 216–227), under the Apache License 2.0 (see LICENSE in the project directory).
Copyright 2026 Jonathan Hanke (see NOTICE). Changes are listed in MODIFICATIONS.md.
-/
module

public import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHeckeRat

/-! # The rational Dirichlet character on idele classes -/

@[expose] public noncomputable section

open NumberField

namespace NumberFieldKB.Chebotarev.RatIdele

variable (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m)

/-- **The idelic Dirichlet character of $\mathbb Q$**: $\tilde\chi(x) = \chi(r(x))^{-1}$ on
$C_{\mathbb Q} = \mathbb A_{\mathbb Q}^\times/\mathbb Q^\times$ (`ideleChar`, `DirichletHeckeRat.lean`). -/
def ratDirichletChar : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℂˣ :=
  ⟨QuotientGroup.lift _ (ideleChar m χ) (by
      rintro _ ⟨a, rfl⟩
      exact (MonoidHom.mem_ker).mpr (ideleChar_diag m χ a)),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (continuous_ideleChar m χ)⟩

theorem ratDirichletChar_mk (x : IdeleGroup (𝓞 ℚ) ℚ) :
    ratDirichletChar m χ (x : IdeleClassGroup (𝓞 ℚ) ℚ) = ideleChar m χ x := rfl

end NumberFieldKB.Chebotarev.RatIdele
