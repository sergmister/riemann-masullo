/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Vendored from TauCetiProject/TauCeti at 8794ab329bb60340fa690a2902cf995f0571721b,
file TauCeti/Analysis/Complex/Conformal/Montel/Precompact.lean.
Changes are listed in MODIFICATIONS.md in the vendoring directory.
-/
module

public import RiemannMasullo.External.TauCeti.Analysis.Complex.Conformal.NormalFamilies
import RiemannMasullo.External.TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Montel's theorem: local boundedness and relative compactness

A family of holomorphic maps on an open set `Ω ⊆ ℂ` with values in a proper complex normed space
has relatively compact continuous restrictions in `C(↥Ω, E)` when it is locally bounded.
This space carries the compact-open topology, whose convergence is locally uniform convergence.
This compactness result supplies the input for the subsequence selection theorem in
`Basic.lean`.

The theorem takes an ambient family `F` and continuous restrictions `f`, related by
`⇑(f i) = Ω.domRestrict (F i)`. Given `hF : ∀ i, ContinuousOn (F i) Ω`, one can take
`f i = ⟨Ω.domRestrict (F i), (hF i).domRestrict⟩`, making this equality reflexive.

## Main results

* `isCompact_closure_range_of_isLocallyBoundedOn`: a locally bounded holomorphic family with
  proper target has relatively compact continuous restrictions.

The proof uses `ArzelaAscoli.isCompact_closure_range_of_equicontinuous` and the Cauchy
estimate in `IsLocallyBoundedOn.equicontinuousOn`. Properness turns the pointwise norm bounds
into pointwise relative compactness; for a complex normed space it is equivalent to
finite-dimensionality.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
* The Montel equicontinuity result in the Riemann mapping development
  [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
-/

public section

open Complex Metric Filter Topology Set

namespace RiemannMasullo.External.TauCeti

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω : Set ℂ} {F : ι → ℂ → E}
  {f : ι → C(Ω, E)}

/-- **Montel's theorem, relative-compactness form.** A locally bounded family of holomorphic
maps of an open set `Ω ⊆ ℂ` into a proper complex normed space `E` restricts to a relatively
compact family in the space `C(↥Ω, E)` of continuous maps with the compact-open topology.

The sequential selection theorem `montel` follows from this compactness result.
Properness of `E` is essential: a bounded family of constant maps can fail to be relatively
compact in an infinite-dimensional target. -/
theorem isCompact_closure_range_of_isLocallyBoundedOn [ProperSpace E] (hΩ : IsOpen Ω)
    (hF : ∀ i, DifferentiableOn ℂ (F i) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) :
    IsCompact (closure (Set.range f)) := by
  have heq : Equicontinuous fun i => (f i : Ω → E) := by
    rw [funext hf]
    exact (equicontinuous_restrict_iff F).mpr (hb.equicontinuousOn hΩ hF)
  -- Arzelà–Ascoli in the compact-open topology: equicontinuity comes from Cauchy's estimate and
  -- pointwise relative compactness from local boundedness.
  refine ArzelaAscoli.isCompact_closure_range_of_equicontinuous heq fun x => ?_
  obtain ⟨C, hC⟩ := hb.exists_forall_norm_le x.property
  refine ⟨closedBall 0 C, isCompact_closedBall _ _, fun i => ?_⟩
  simpa [hf i, mem_closedBall, dist_zero_right] using hC i

end RiemannMasullo.External.TauCeti
