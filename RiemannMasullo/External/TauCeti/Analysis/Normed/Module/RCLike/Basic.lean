/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Vendored from TauCetiProject/TauCeti at 8794ab329bb60340fa690a2902cf995f0571721b,
file TauCeti/Analysis/Normed/Module/RCLike/Basic.lean.
Changes are listed in MODIFICATIONS.md in the vendoring directory.
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.Linarith

/-!
# Half sums in normed spaces over `ℝ` or `ℂ`

In a normed space over an `RCLike` field, half the sum of two vectors of norm at most `B` has
norm at most `B`: the closed ball of radius `B` contains the midpoint of any two of its points.
-/

public section

namespace RiemannMasullo.External.TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Half the sum of two vectors of norm at most `B` has norm at most `B`. -/
theorem norm_two_inv_smul_add_le {a b : E} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖(2 : 𝕜)⁻¹ • (a + b)‖ ≤ B := by
  rw [norm_smul, norm_inv, RCLike.norm_two]
  linarith [norm_add_le a b]

end RiemannMasullo.External.TauCeti
