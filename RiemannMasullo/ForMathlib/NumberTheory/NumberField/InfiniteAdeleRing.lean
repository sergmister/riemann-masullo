module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# Mixed coordinates on the infinite adele ring

Candidate for Mathlib. The homeomorphism uses the same real and complex completion
equivalences as `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace`, so continuity
is available in either direction for the existing ring equivalence.

The motivating example was emmgaml’s shifted-theta proof on Prove2Me (theorem
`b1cd0f9b-2b6a-420a-bdc7-fb8bd1a66978`). The construction below follows Mathlib’s
`ringEquiv_mixedSpace` factor by factor, using the associated homeomorphisms.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K]

open scoped Classical in
/-- The archimedean coordinates identify the infinite adeles with the product of the
real and complex factors, equipped with their product topologies. -/
def infiniteAdeleHomeomorphMixedSpace : InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd IsReal (fun v : InfinitePlace K ↦ v.Completion)).trans
    ((Homeomorph.piCongrRight fun v ↦
      (Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
      ((Homeomorph.piCongrRight fun v ↦
        (Completion.isometryEquivComplexOfIsComplex
          (not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
          (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex))))

@[simp] theorem infiniteAdeleHomeomorphMixedSpace_toEquiv :
    (infiniteAdeleHomeomorphMixedSpace K).toEquiv =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).toEquiv := rfl

@[simp] theorem infiniteAdeleHomeomorphMixedSpace_apply (x : InfiniteAdeleRing K) :
    infiniteAdeleHomeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

@[simp] theorem infiniteAdeleHomeomorphMixedSpace_symm_apply (x : mixedEmbedding.mixedSpace K) :
    (infiniteAdeleHomeomorphMixedSpace K).symm x =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x := rfl

@[fun_prop] theorem continuous_infiniteAdeleRingEquivMixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) :=
  (infiniteAdeleHomeomorphMixedSpace K).continuous

@[fun_prop] theorem continuous_infiniteAdeleRingEquivMixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :=
  (infiniteAdeleHomeomorphMixedSpace K).symm.continuous

end RiemannMasullo
