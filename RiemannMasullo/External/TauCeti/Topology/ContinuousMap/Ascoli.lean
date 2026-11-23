/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Vendored from TauCetiProject/TauCeti at 8794ab329bb60340fa690a2902cf995f0571721b,
file TauCeti/Topology/ContinuousMap/Ascoli.lean.
Changes are listed in MODIFICATIONS.md in the vendoring directory.
-/
module

public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# The Arzelà–Ascoli theorem in `C(X, Y)`

Mathlib proves the Arzelà–Ascoli theorem for a family of functions viewed inside a space of
uniform convergence on a family of compact sets
(`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`), and shows that an equicontinuous set of
continuous maps that is compact for pointwise convergence is compact
(`ArzelaAscoli.isCompact_of_equicontinuous`).
This file states it directly for subsets of the space `C(X, Y)` of continuous maps with its
compact-open topology, which is the space of continuous curves when `X` is a compact interval.

* An equicontinuous family in `C(X, Y)` whose values at each point lie in a common compact set has
  relatively compact range.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall 2000, §47 (Ascoli's theorem).
-/

public section

open Filter Set Topology Uniformity

variable {X Y : Type*} [TopologicalSpace X]

namespace ArzelaAscoli

/-- **The Arzelà–Ascoli theorem in `C(X, Y)`.** An equicontinuous family of continuous maps
whose values at each point lie in a common compact set has relatively compact range in the
compact-open topology. No assumption on the topology of `X` is needed. -/
theorem isCompact_closure_range_of_equicontinuous [UniformSpace Y]
    {ι : Type*} {f : ι → C(X, Y)} (hf : Equicontinuous fun i ↦ ⇑(f i))
    (hfpt : ∀ x, ∃ Q, IsCompact Q ∧ ∀ i, f i x ∈ Q) : IsCompact (closure (range f)) := by
  choose Q hQ hfQ using hfpt
  -- The pointwise closure `P` of the family is equicontinuous, and compact by Tychonoff.
  set P : Set (X → Y) := closure (range fun i ↦ ⇑(f i))
  have hPeq : P.Equicontinuous := by
    refine Set.Equicontinuous.closure ?_
    rw [Set.Equicontinuous, ← comp_rangeSplitting (fun i ↦ ⇑(f i))]
    exact hf.comp (rangeSplitting _)
  have hP : IsCompact P :=
    (isCompact_univ_pi fun x ↦ (hQ x).closure).of_isClosed_subset isClosed_closure
      (closure_minimal (range_subset_iff.2 fun i x _ ↦ subset_closure (hfQ x i))
        (isClosed_set_pi fun x _ ↦ isClosed_closure))
  -- The continuous maps whose underlying functions lie in `P` form a compact set, since
  -- pointwise and compact convergence agree on equicontinuous sets. It is closed and contains
  -- the family, hence contains its closure.
  set S : Set C(X, Y) := {g | ⇑g ∈ P}
  have hS : IsCompact S := by
    have himage : ContinuousMap.toFun '' S = P :=
      Subset.antisymm (image_subset_iff.2 fun _ hg ↦ hg)
        fun p hp ↦ ⟨⟨p, hPeq.continuous_of_mem hp⟩, hp, rfl⟩
    exact ArzelaAscoli.isCompact_of_equicontinuous S (himage ▸ hP)
      (hPeq.comp fun g : S ↦ (⟨⇑(g : C(X, Y)), g.property⟩ : P))
  exact hS.of_isClosed_subset isClosed_closure (closure_minimal
    (range_subset_iff.2 fun i ↦ subset_closure (mem_range_self i))
    (isClosed_closure.preimage (continuous_pi continuous_eval_const)))

end ArzelaAscoli
