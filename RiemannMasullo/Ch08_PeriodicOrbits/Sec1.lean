module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

/-! # §8.1 On orbital supports I

The comparison maps are induced by inclusion of the restricted tests. The asserted
isomorphisms fail even with the corrected additive test spaces. The support and stack
interpretations announced in the chapter introduction belong to §§8.2–8.3.
-/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing TensorProduct

namespace RiemannMasullo
set_option quotPrecheck false
set_option maxHeartbeats 400000

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "B(" S ")" => ℬ(SAdeleRing F S)
local notation "J₁(" S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁" => (ideleClassNorm F).ker
local notation "PicTrivial(" S ")" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "RealPlaces" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces" => {w : InfinitePlace F // w.IsComplex}
local notation "ArchCoordinates" => ((RealPlaces → ℝ) × (ComplexPlaces → ℂ))
local notation "assemble(" x ")" =>
  (show InfiniteAdeleRing F from fun w ↦
    if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm ((x).1 ⟨w, hw⟩)
    else
      let hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm ((x).2 ⟨w, hw'⟩))

variable (F) in
/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
The common archimedean factor consists of Schwartz tests that are flat along every
archimedean coordinate hyperplane, expressed in the coordinates of §5.3.3. -/
def sLocalOrbitalArchimedeanFlatTests :
    Submodule ℂ ℬ(InfiniteAdeleRing F) :=
  let flat := (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
    ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _)
  let coords := LinearMap.funLeft ℂ ℂ (fun x : ArchCoordinates ↦ Multiplicative.ofAdd (assemble(x)))
  flat.comap (coords.comp (schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F))).subtype)

/-- The archimedean coordinates of the origin assemble to the origin. -/
private theorem sLocalOrbitalArchimedeanFlatTests_zero_assemble :
    assemble((0 : ArchCoordinates)) = 0 := by
  funext w
  by_cases hw : w.IsReal
  · simp only [hw, dite_true, Prod.fst_zero, Pi.zero_apply, map_zero]
    rfl
  · simp only [hw, dite_false, Prod.snd_zero, Pi.zero_apply, map_zero]
    rfl

/-- The origin of the archimedean coordinates lies on a coordinate hyperplane. -/
private theorem sLocalOrbitalArchimedeanFlatTests_zero_meetsWall :
    (∃ i, (0 : ArchCoordinates).1 i = 0) ∨ (∃ j, (0 : ArchCoordinates).2 j = 0) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  by_cases hw : w.IsReal
  · exact Or.inl ⟨⟨w, hw⟩, rfl⟩
  · exact Or.inr ⟨⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, rfl⟩

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
Every archimedean-flat test in the displayed tensor products vanishes at the origin. -/
theorem sLocalOrbitalArchimedeanFlatTests_zero
    (f : sLocalOrbitalArchimedeanFlatTests F) :
    f.val (Multiplicative.ofAdd 0) = 0 := by
  have hf := f.property
  unfold sLocalOrbitalArchimedeanFlatTests at hf
  obtain ⟨φ, hφ, hφf⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hf)
  have h0 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hφ
    ⟨0, sLocalOrbitalArchimedeanFlatTests_zero_meetsWall⟩) 0) Fin.elim0
  have hφ0 : (φ : ArchCoordinates → ℂ) 0 = 0 := by
    have := LinearMap.mem_ker.mp h0
    simpa only [IsLinearMap.mk'_apply, iteratedFDeriv_zero_apply] using this
  have hv : (φ : ArchCoordinates → ℂ) 0 =
      f.val (Multiplicative.ofAdd (assemble((0 : ArchCoordinates)))) := congrFun hφf 0
  rw [sLocalOrbitalArchimedeanFlatTests_zero_assemble] at hv
  exact hv.symm.trans hφ0

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
These are the restricted S-adelic tests, with the fibre or singleton entered as T.
The archimedean factor is flat and every finite factor outside T vanishes at zero.
Deviation: The punctured factors are the zero extensions of compactly supported locally
constant tests on the units, as in §5.3.4 and ERRATA R11. The subspace carries the inherited
S-adelic Schwartz–Bruhat topology of §2.1.4. Even for the corrected factors, the
printed projective tensor topology can be strictly coarser (ERRATA I156). -/
def sLocalOrbitalSupportTests (S T : Finset V) : Submodule ℂ B(S) :=
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  Submodule.span ℂ {f : B(S) |
    ∃ (a : sLocalOrbitalArchimedeanFlatTests F) (b : ∀ w : S, ℬ(w.val.adicCompletion F)),
      (∀ w : S, w.val ∉ T → b w (Multiplicative.ofAdd 0) = 0) ∧
      e (a.val ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) = f}

variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "U(" S ", " T ")" => sLocalOrbitalSupportTests (F := F) S T
local notation "Θ(" η ")" => SLocalHomogeneousThetaSpace F S η
local notation "q(" η ")" => (sLocalHomogeneousAdelicThetaLinearMap F S η).ker.mkQL
local notation "D(" hT ", " η ")" =>
  (sLocalHomogeneousThetaPrincipalValue (F := F) hT η).range

/-- On each finite fibre, a restricted test is archimedean-flat in the coordinates of §5.3.3. -/
private theorem sLocalOrbitalSupportTests_tmul_iff_fibre (g : B(S)) (hg : g ∈ U(S, T))
    (y : ∀ w : S, w.val.adicCompletion F) :
    (fun x : ArchCoordinates ↦ g (Multiplicative.ofAdd ((assemble(x), y) : SAdeleRing F S)))
      ∈ (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
        ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _) := by
  unfold sLocalOrbitalSupportTests at hg
  dsimp only at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, b, _, rfl⟩ := hg
    have ha := a.property
    unfold sLocalOrbitalArchimedeanFlatTests at ha
    have ha' := Submodule.mem_comap.mp ha
    have key : (fun x : ArchCoordinates ↦
        (sAdeleSchwartz_inductiveTensor_equiv F S).choose (a.val ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
          (Multiplicative.ofAdd ((assemble(x), y) : SAdeleRing F S))) =
        (∏ w : S, b w (Multiplicative.ofAdd (y w))) •
          (fun x : ArchCoordinates ↦ a.val (Multiplicative.ofAdd (assemble(x)))) := by
      funext x
      rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    rw [key]
    exact Submodule.smul_mem _ _ ha'
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/-- A restricted test vanishes wherever a finite coordinate outside T is zero. -/
private theorem sLocalOrbitalSupportTests_tmul_iff_zero (g : B(S)) (hg : g ∈ U(S, T))
    (x : SAdeleRing F S) (w : S) (hw : w.val ∉ T) (hx : x.2 w = 0) :
    g (Multiplicative.ofAdd x) = 0 := by
  unfold sLocalOrbitalSupportTests at hg
  dsimp only at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, b, hb, rfl⟩ := hg
    rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ w) ?_)
    rw [hx]
    exact hb w hw
  | zero => rfl
  | add f g _ _ hf hg =>
    rw [SchwartzBruhat.coe_add, Pi.add_apply, hf, hg, add_zero]
  | smul c f _ hf =>
    rw [SchwartzBruhat.coe_smul, Pi.smul_apply, hf, smul_zero]

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
For a pure tensor with nonzero factors, membership is precisely archimedean flatness
and vanishing at zero in each finite factor outside T. -/
theorem sLocalOrbitalSupportTests_tmul_iff
    (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F))
    (_ha : a ≠ 0) (_hb : ∀ w : S, b w ≠ 0) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ∈ U(S, T) ↔
      a ∈ sLocalOrbitalArchimedeanFlatTests F ∧
        ∀ w : S, w.val ∉ T → b w (Multiplicative.ofAdd 0) = 0 := by
  intro e
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a b
  constructor
  · intro h
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : InfiniteAdeleRing F, a (Multiplicative.ofAdd x₀) ≠ 0 := by
      by_contra! hn
      exact _ha (SchwartzBruhat.ext fun x ↦ hn x.toAdd)
    have hnon (w : S) : ∃ y : w.val.adicCompletion F, b w (Multiplicative.ofAdd y) ≠ 0 := by
      by_contra! hn
      exact _hb w (SchwartzBruhat.ext fun x ↦ hn x.toAdd)
    choose y hy using hnon
    refine ⟨?_, fun w hw ↦ ?_⟩
    · have hc : (∏ w : S, b w (Multiplicative.ofAdd (y w))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun w _ ↦ hy w
      have hf := sLocalOrbitalSupportTests_tmul_iff_fibre _ h y
      have key : (fun x : ArchCoordinates ↦ e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w))
            (Multiplicative.ofAdd ((assemble(x), y) : SAdeleRing F S))) =
          (∏ w : S, b w (Multiplicative.ofAdd (y w))) •
            (fun x : ArchCoordinates ↦ a (Multiplicative.ofAdd (assemble(x)))) := by
        funext x
        rw [he, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [key] at hf
      have hf' := Submodule.smul_mem _ (∏ w : S, b w (Multiplicative.ofAdd (y w)))⁻¹ hf
      rw [inv_smul_smul₀ hc] at hf'
      unfold sLocalOrbitalArchimedeanFlatTests
      exact Submodule.mem_comap.mpr hf'
    · by_contra hne
      let z := Function.update y w 0
      have hz := sLocalOrbitalSupportTests_tmul_iff_zero _ h
        ((x₀, z) : SAdeleRing F S) w hw (Function.update_self ..)
      rw [he] at hz
      refine mul_ne_zero hx₀ (Finset.prod_ne_zero_iff.mpr fun u _ ↦ ?_) hz
      by_cases hu : u = w
      · subst hu
        simpa only [z, Function.update_self] using hne
      · simpa only [z, Function.update_of_ne hu] using hy u
  · rintro ⟨ha, hb⟩
    exact Submodule.subset_span ⟨⟨a, ha⟩, b, hb, rfl⟩

/-- Over ℂ, a tensor whose contractions against a separating family of functionals on the
right factor all vanish is zero. -/
private theorem sLocalOrbitalSupportTests_isClosed_sep {X Y ι : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ε : ι → Y →ₗ[ℂ] ℂ)
    (hsep : ∀ y : Y, (∀ i, ε i y = 0) → y = 0) (u : X ⊗[ℂ] Y)
    (hu : ∀ i, TensorProduct.rid ℂ X (LinearMap.lTensor X (ε i) u) = 0) : u = 0 := by
  let b := Module.Basis.ofVectorSpace ℂ X
  have key (i : ι) (j) (v : X ⊗[ℂ] Y) :
      ε i (TensorProduct.lid ℂ Y (LinearMap.rTensor Y (b.coord j) v)) =
        b.coord j (TensorProduct.rid ℂ X (LinearMap.lTensor X (ε i) v)) := by
    induction v using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul,
        TensorProduct.rid_tmul, map_smul, smul_eq_mul, mul_comm]
    | add v w hv hw => simp only [map_add, hv, hw]
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  refine Finsupp.ext fun j ↦ ?_
  rw [Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  exact hsep _ fun i ↦ (key i j u).trans (by rw [hu i, map_zero])

/-- Contracting the right factor commutes with a linear map on the left factor. -/
private theorem sLocalOrbitalSupportTests_isClosed_natural {A B Y : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup Y] [Module ℂ Y]
    (g : A →ₗ[ℂ] B) (E : Y →ₗ[ℂ] ℂ) (u : A ⊗[ℂ] Y) :
    TensorProduct.rid ℂ B (LinearMap.lTensor B E (LinearMap.rTensor Y g u)) =
      g (TensorProduct.rid ℂ A (LinearMap.lTensor A E u)) := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- Over ℂ, `a ⊗ y = 0` with `a ≠ 0` forces `y = 0`. -/
private theorem sLocalOrbitalSupportTests_isClosed_cancel {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {a : X} (ha : a ≠ 0) {y : Y}
    (h : a ⊗ₜ[ℂ] y = 0) : y = 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ ha
  have h' := congrArg (fun u ↦ TensorProduct.lid ℂ Y (LinearMap.rTensor Y φ u)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h'
  exact (smul_eq_zero.mp h').resolve_left hφ

/-- Abstract span identity: a tensor whose contractions against the functionals `E y` lie in
`P`, and vanish for `y` in `Z`, lies in `P ⊗ Q`, when the `E y` separate points and the
`E y` with `y` in `Z` cut out exactly `Q`. -/
private theorem sLocalOrbitalSupportTests_isClosed_core {A W Y : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W]
    (P : Submodule ℂ A) (Q : Submodule ℂ W) (E : Y → W →ₗ[ℂ] ℂ) (Z : Y → Prop)
    (hsepW : ∀ w : W, (∀ y, E y w = 0) → w = 0)
    (hQ : ∀ y, Z y → Q ≤ LinearMap.ker (E y))
    (hsepQ : ∀ w : W, (∀ y, Z y → E y w = 0) → w ∈ Q)
    (t : A ⊗[ℂ] W) (hP : ∀ y, TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) t) ∈ P)
    (hZ : ∀ y, Z y → TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) t) = 0) :
    t ∈ LinearMap.range (TensorProduct.map P.subtype Q.subtype) := by
  have h1 : LinearMap.rTensor W P.mkQ t = 0 :=
    sLocalOrbitalSupportTests_isClosed_sep E hsepW _ fun y ↦ by
      rw [sLocalOrbitalSupportTests_isClosed_natural, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact hP y
  obtain ⟨s, rfl⟩ : t ∈ LinearMap.range (LinearMap.rTensor W P.subtype) := by
    rw [← LinearMap.exact_iff.mp
      (rTensor_exact W (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective)]
    exact h1
  let ε : {y // Z y} → (W ⧸ Q) →ₗ[ℂ] ℂ := fun y ↦ Q.liftQ (E y.1) (hQ y.1 y.2)
  have h2 : LinearMap.lTensor P Q.mkQ s = 0 := by
    refine sLocalOrbitalSupportTests_isClosed_sep ε (fun w hw ↦ ?_) _ fun y ↦ ?_
    · obtain ⟨w, rfl⟩ := Q.mkQ_surjective w
      exact (Submodule.Quotient.mk_eq_zero Q).mpr (hsepQ w fun y hy ↦ hw ⟨y, hy⟩)
    · rw [← LinearMap.lTensor_comp_apply]
      have hε : ε y ∘ₗ Q.mkQ = E y.1 := Q.liftQ_mkQ _ _
      rw [hε]
      apply P.injective_subtype
      rw [map_zero, ← sLocalOrbitalSupportTests_isClosed_natural]
      exact hZ y.1 y.2
  obtain ⟨r, rfl⟩ : s ∈ LinearMap.range (LinearMap.lTensor P Q.subtype) := by
    rw [← LinearMap.exact_iff.mp
      (lTensor_exact P (LinearMap.exact_subtype_mkQ Q) Q.mkQ_surjective)]
    exact h2
  refine ⟨r, ?_⟩
  rw [← LinearMap.rTensor_comp_lTensor]
  rfl

/-- Abstract form: a functional on `A ⊗ W` that is `E w * evx a` on pure tensors is `evx` of the
contraction of the right factor against `E`. -/
private theorem sLocalOrbitalSupportTests_isClosed_evalAux {A W : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W]
    (E : W →ₗ[ℂ] ℂ) (evx : A →ₗ[ℂ] ℂ) (L : A ⊗[ℂ] W →ₗ[ℂ] ℂ)
    (h : ∀ a w, L (a ⊗ₜ[ℂ] w) = E w * evx a) (t : A ⊗[ℂ] W) :
    L t = evx (TensorProduct.rid ℂ A (LinearMap.lTensor A E t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul a w =>
    rw [h, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul, smul_eq_mul]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The finite-place evaluation functionals on the finite tensor factor, and the value of an
S-adelic test through the tensor decomposition: it is the contraction of its finite factor
at `y`, evaluated at `x`. -/
private theorem sLocalOrbitalSupportTests_isClosed_eval :
    ∃ E : (∀ v : S, v.val.adicCompletion F) →
        FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F)) →ₗ[ℂ] ℂ,
      (∀ y (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        E y (PiTensorProduct.tprod ℂ g) = ∏ v, g v (Multiplicative.ofAdd (y v))) ∧
      (∀ (x : InfiniteAdeleRing F) (y : ∀ v : S, v.val.adicCompletion F)
        (a : ℬ(InfiniteAdeleRing F)) (w : FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F))),
        (sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] w)
            (Multiplicative.ofAdd ((x, y) : SAdeleRing F S)) = E y w * a (Multiplicative.ofAdd x)) ∧
      ∀ (x : InfiniteAdeleRing F) (y : ∀ v : S, v.val.adicCompletion F)
        (t : InductiveTensor ℬ(InfiniteAdeleRing F)
          (FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F)))),
        (sAdeleSchwartz_inductiveTensor_equiv F S).choose t
            (Multiplicative.ofAdd ((x, y) : SAdeleRing F S)) =
          TensorProduct.rid ℂ ℬ(InfiniteAdeleRing F)
            (LinearMap.lTensor ℬ(InfiniteAdeleRing F) (E y) t) (Multiplicative.ofAdd x) := by
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let A := ℬ(InfiniteAdeleRing F)
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F))
  let ev (y : ∀ v : S, v.val.adicCompletion F) (v : S) : ℬ(v.val.adicCompletion F) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd (y v))).comp (schwartzBruhatSubmodule _).subtype
  let E (y : ∀ v : S, v.val.adicCompletion F) : W →ₗ[ℂ] ℂ :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ S ℂ).compLinearMap (ev y))
  have hE (y : ∀ v : S, v.val.adicCompletion F) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
      E y (PiTensorProduct.tprod ℂ g) = ∏ v, g v (Multiplicative.ofAdd (y v)) := by
    erw [PiTensorProduct.lift.tprod]
    rfl
  have key (x : InfiniteAdeleRing F) (y : ∀ v : S, v.val.adicCompletion F) :
      let evp : B(S) →ₗ[ℂ] ℂ :=
        (LinearMap.proj (Multiplicative.ofAdd ((x, y) : SAdeleRing F S))).comp
          (schwartzBruhatSubmodule _).subtype
      let evx : A →ₗ[ℂ] ℂ :=
        (LinearMap.proj (Multiplicative.ofAdd x)).comp (schwartzBruhatSubmodule _).subtype
      let L : InductiveTensor A W →ₗ[ℂ] ℂ := evp.comp e.toLinearMap
      (∀ (a : A) (w : W), L (a ⊗ₜ[ℂ] w) = E y w * evx a) ∧
        ∀ t, L t = evx (TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) t)) := by
    intro evp evx L
    have h (a : A) (w : W) : L (a ⊗ₜ[ℂ] w) = E y w * evx a := by
      let M₁ : (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F)) →ₗ[ℂ] ℂ := L.comp (TensorProduct.mk ℂ A W a)
      let M₂ : (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F)) →ₗ[ℂ] ℂ := evx a • E y
      have hM : M₁ = M₂ := by
        refine PiTensorProduct.ext (MultilinearMap.ext fun g ↦ ?_)
        have h1 : M₁ (PiTensorProduct.tprod ℂ g) =
            e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g) (Multiplicative.ofAdd ((x, y) : SAdeleRing F S)) :=
          rfl
        have h2 : M₂ (PiTensorProduct.tprod ℂ g) = evx a * E y (PiTensorProduct.tprod ℂ g) := rfl
        change M₁ (PiTensorProduct.tprod ℂ g) = M₂ (PiTensorProduct.tprod ℂ g)
        refine h1.trans (Eq.trans ?_ h2.symm)
        exact (he a g (x, y)).trans (congrArg (a (Multiplicative.ofAdd x) * ·) (hE y g).symm)
      exact (LinearMap.congr_fun hM w).trans (mul_comm _ _)
    exact ⟨h, sLocalOrbitalSupportTests_isClosed_evalAux (E y) evx L h⟩
  exact ⟨E, hE, fun x y a w ↦ (key x y).1 a w, fun x y t ↦ (key x y).2 t⟩

/-- Abstract form: if `Φ (a₀ ⊗ w)` lies in a subspace whose preimage under the injective `Φ`
consists of tensors with right factor in `Q`, and `a₀ ≠ 0`, then `w ∈ Q`. -/
private theorem sLocalOrbitalSupportTests_isClosed_transfer {A W B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W] [AddCommGroup B] [Module ℂ B]
    (Q : Submodule ℂ W) (Φ : A ⊗[ℂ] W →ₗ[ℂ] B) (hΦ : Function.Injective Φ) (Z : Submodule ℂ B)
    (hZ : Z ≤ (LinearMap.range (LinearMap.lTensor A Q.subtype)).map Φ)
    {a₀ : A} (ha₀ : a₀ ≠ 0) (w : W) (hw : Φ (a₀ ⊗ₜ[ℂ] w) ∈ Z) : w ∈ Q := by
  obtain ⟨z, ⟨r, rfl⟩, hz⟩ := hZ hw
  have hr : LinearMap.lTensor A Q.subtype r = a₀ ⊗ₜ[ℂ] w := hΦ hz
  have hex := LinearMap.exact_iff.mp
    (lTensor_exact A (LinearMap.exact_subtype_mkQ Q) Q.mkQ_surjective)
  have h2 : a₀ ⊗ₜ[ℂ] w ∈ LinearMap.ker (LinearMap.lTensor A Q.mkQ) := by
    rw [hex, ← hr]
    exact ⟨r, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.lTensor_tmul] at h2
  exact (Submodule.Quotient.mk_eq_zero Q).mp (sLocalOrbitalSupportTests_isClosed_cancel ha₀ h2)

/-- Abstract form: a linear map sends `P ⊗ span s` into `U` once it sends every `p ⊗ w`, with
`p ∈ P` and `w ∈ s`, into `U`. -/
private theorem sLocalOrbitalSupportTests_isClosed_image {A W B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W] [AddCommGroup B] [Module ℂ B]
    (P : Submodule ℂ A) (s : Set W) (Φ : A ⊗[ℂ] W →ₗ[ℂ] B) (U : Submodule ℂ B)
    (hgen : ∀ p ∈ P, ∀ w ∈ s, Φ (p ⊗ₜ[ℂ] w) ∈ U) (t : A ⊗[ℂ] W)
    (ht : t ∈ LinearMap.range (TensorProduct.map P.subtype (Submodule.span ℂ s).subtype)) :
    Φ t ∈ U := by
  obtain ⟨r, rfl⟩ := ht
  induction r using TensorProduct.inductionOn with
  | tmul p q =>
    obtain ⟨q, hq⟩ := q
    rw [TensorProduct.map_tmul]
    change Φ (p.val ⊗ₜ[ℂ] q) ∈ U
    induction hq using Submodule.span_induction with
    | mem w hw => exact hgen p p.2 w hw
    | zero => rw [TensorProduct.tmul_zero, map_zero]; exact U.zero_mem
    | add w₁ w₂ _ _ h₁ h₂ => rw [TensorProduct.tmul_add, map_add]; exact U.add_mem h₁ h₂
    | smul c w _ h => rw [TensorProduct.tmul_smul, map_smul]; exact U.smul_mem c h
  | add r₁ r₂ h₁ h₂ => rw [map_add, map_add]; exact U.add_mem h₁ h₂

/-- A test vanishing wherever a finite coordinate in `R` is zero lies in the finite zero
subspace for `R`. -/
private theorem sLocalOrbitalSupportTests_isClosed_zeroMem (R : Finset V) (g : B(S))
    (h : ∀ x : SAdeleRing F S, (∃ v : S, v.val ∈ R ∧ x.2 v = 0) →
      g (Multiplicative.ofAdd x) = 0) :
    g ∈ sAdeleFiniteZeroSchwartz S R :=
  (Submodule.mem_iInf _).mpr fun x ↦ LinearMap.mem_ker.mpr (h x.val x.property)

/-- The span identity behind closedness: a test that is archimedean-flat on every finite
fibre and vanishes where a finite coordinate outside T is zero is a restricted test. -/
private theorem sLocalOrbitalSupportTests_isClosed_span (f : B(S))
    (hflat : ∀ y : (∀ v : S, v.val.adicCompletion F),
      (fun x : ArchCoordinates ↦ f (Multiplicative.ofAdd ((assemble(x), y) : SAdeleRing F S)))
        ∈ (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
          ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _))
    (hzero : f ∈ sAdeleFiniteZeroSchwartz S (S \ T)) : f ∈ U(S, T) := by
  obtain ⟨E, hE, hT, hF⟩ := sLocalOrbitalSupportTests_isClosed_eval (F := F) (S := S)
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let A := ℬ(InfiniteAdeleRing F)
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F))
  let s : Set W := {w | ∃ b : ∀ v : S, ℬ(v.val.adicCompletion F),
    (∀ v : S, v.val ∉ T → b v (Multiplicative.ofAdd 0) = 0) ∧ PiTensorProduct.tprod ℂ b = w}
  let Q : Submodule ℂ W := Submodule.span ℂ s
  by_cases hA : ∀ a : A, a = 0
  · have hf : f = 0 := SchwartzBruhat.ext fun p ↦ by
      have h1 := hF p.toAdd.1 p.toAdd.2 (e.symm f)
      have h2 := hA (TensorProduct.rid ℂ A (LinearMap.lTensor A (E p.toAdd.2) (e.symm f)))
      have h3 : f p = e (e.symm f) p := congrArg (fun g : B(S) ↦ g p) (e.apply_symm_apply f).symm
      exact h3.trans (h1.trans (congrArg (fun a : A ↦ a (Multiplicative.ofAdd p.toAdd.1)) h2))
    rw [hf]
    exact Submodule.zero_mem _
  obtain ⟨a₀, ha₀⟩ := not_forall.mp hA
  have hval (w : W) (y : ∀ v : S, v.val.adicCompletion F) (hw : E y w = 0)
      (x : InfiniteAdeleRing F) :
      e (a₀ ⊗ₜ[ℂ] w) (Multiplicative.ofAdd ((x, y) : SAdeleRing F S)) = 0 := by
    exact (hT x y a₀ w).trans (by rw [hw, zero_mul])
  have hsepW : ∀ w : W, (∀ y, E y w = 0) → w = 0 := by
    intro w hw
    refine sLocalOrbitalSupportTests_isClosed_cancel ha₀ (e.injective ?_)
    exact (SchwartzBruhat.ext fun p ↦ hval w p.toAdd.2 (hw _) p.toAdd.1).trans e.map_zero.symm
  have hQ : ∀ y : (∀ v : S, v.val.adicCompletion F), (∃ v : S, v.val ∉ T ∧ y v = 0) →
      Q ≤ LinearMap.ker (E y) := by
    rintro y ⟨v, hv, hyv⟩
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    change E y (PiTensorProduct.tprod ℂ b) = 0
    rw [hE]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hyv]; exact hb v hv)
  let Φ : A ⊗[ℂ] W →ₗ[ℂ] B(S) := e.toLinearMap
  have hΦ : Function.Injective Φ := e.injective
  have hZero : sAdeleFiniteZeroSchwartz S (S \ T) ≤
      (LinearMap.range (LinearMap.lTensor A Q.subtype)).map Φ := by
    have hspan := sAdeleFiniteZeroSchwartz_eq_span_tmul (F := F) (S := S) (S \ T)
    dsimp only at hspan
    rw [hspan, Submodule.span_le]
    rintro _ ⟨g₀, g, hg, rfl⟩
    exact ⟨LinearMap.lTensor A Q.subtype (g₀ ⊗ₜ[ℂ] ⟨PiTensorProduct.tprod ℂ g,
      Submodule.subset_span ⟨g, fun v hv ↦ hg v (Finset.mem_sdiff.mpr ⟨v.property, hv⟩), rfl⟩⟩),
      ⟨_, rfl⟩, rfl⟩
  have hsepQ : ∀ w : W,
      (∀ y : (∀ v : S, v.val.adicCompletion F), (∃ v : S, v.val ∉ T ∧ y v = 0) → E y w = 0) →
        w ∈ Q := by
    intro w hw
    exact sLocalOrbitalSupportTests_isClosed_transfer Q Φ hΦ _ hZero ha₀ w
      (sLocalOrbitalSupportTests_isClosed_zeroMem (S \ T) _ fun x ⟨v, hv, hxv⟩ ↦
        hval w x.2 (hw _ ⟨v, (Finset.mem_sdiff.mp hv).2, hxv⟩) x.1)
  have hP : ∀ y : (∀ v : S, v.val.adicCompletion F),
      TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) (e.symm f)) ∈
        sLocalOrbitalArchimedeanFlatTests F := by
    intro y
    unfold sLocalOrbitalArchimedeanFlatTests
    dsimp only
    refine Submodule.mem_comap.mpr ?_
    convert hflat y using 1
    funext x
    change TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) (e.symm f))
      (Multiplicative.ofAdd (assemble(x))) = _
    rw [← hF, e.apply_symm_apply]
  have hZ : ∀ y : (∀ v : S, v.val.adicCompletion F), (∃ v : S, v.val ∉ T ∧ y v = 0) →
      TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) (e.symm f)) = 0 := by
    rintro y ⟨v, hv, hyv⟩
    refine SchwartzBruhat.ext fun p ↦ ?_
    have h1 := hF p.toAdd y (e.symm f)
    have h3 : e (e.symm f) (Multiplicative.ofAdd ((p.toAdd, y) : SAdeleRing F S)) = 0 :=
      (congrArg (fun g : B(S) ↦ g (Multiplicative.ofAdd ((p.toAdd, y) : SAdeleRing F S)))
        (e.apply_symm_apply f)).trans (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hzero
          ⟨(p.toAdd, y), v, Finset.mem_sdiff.mpr ⟨v.property, hv⟩, hyv⟩))
    exact h1.symm.trans h3
  have hgen : ∀ p ∈ sLocalOrbitalArchimedeanFlatTests F, ∀ w ∈ s, Φ (p ⊗ₜ[ℂ] w) ∈ U(S, T) := by
    rintro p hp _ ⟨b, hb, rfl⟩
    unfold sLocalOrbitalSupportTests
    exact Submodule.subset_span ⟨⟨p, hp⟩, b, hb, rfl⟩
  have hfin := sLocalOrbitalSupportTests_isClosed_image _ s Φ U(S, T) hgen (e.symm f)
    (sLocalOrbitalSupportTests_isClosed_core (sLocalOrbitalArchimedeanFlatTests F)
      Q E _ hsepW hQ hsepQ (e.symm f) hP hZ)
  have hΦf : Φ (e.symm f) = f := e.apply_symm_apply f
  rw [hΦf] at hfin
  exact hfin

/-- The archimedean slice of an S-adelic test at a fixed finite coordinate is a classical
Schwartz function, continuously in the S-adelic topology. Same construction as the private
`sAdelePolarFree_slice` of Ch05 Sec3b, here for the coordinates of §5.3.3. -/
private theorem sLocalOrbitalSupportTests_isClosed_slice (y : ∀ v : S, v.val.adicCompletion F) :
    ∃ Φ : B(S) →L[ℂ] SchwartzMap ArchCoordinates ℂ,
      ∀ f x, Φ f x = f (Multiplicative.ofAdd ((assemble(x), y) : SAdeleRing F S)) := by
  obtain ⟨E, -, -, hF⟩ := sLocalOrbitalSupportTests_isClosed_eval (F := F) (S := S)
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let A := ℬ(InfiniteAdeleRing F)
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F))
  have hmix (x : ArchCoordinates) :
      InfiniteAdeleRing.ringEquiv_mixedSpace F (assemble(x)) = x := by
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_)
    · have hw : w.1.IsReal := w.2
      simp only [hw, ↓reduceDIte]
      exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply _
    · have hw : ¬ w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
      simp only [hw, ↓reduceDIte]
      exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex _).apply_symm_apply _
  let Q : A →L[ℂ] SchwartzMap ArchCoordinates ℂ := J.symm.toContinuousLinearMap
  have hQ (a : A) (x : ArchCoordinates) : Q a x = a (Multiplicative.ofAdd (assemble(x))) := by
    change J.symm a x = _
    conv_rhs => rw [← J.apply_symm_apply a]
    rw [hJ, hmix]
  let T : InductiveTensor A W →ₗ[ℂ] SchwartzMap ArchCoordinates ℂ :=
    Q.toLinearMap.comp ((TensorProduct.rid ℂ A).toLinearMap.comp (LinearMap.lTensor A (E y)))
  let : PolynormableSpace ℂ (SchwartzMap ArchCoordinates ℂ) :=
    (schwartz_withSeminorms ℂ ArchCoordinates ℂ).toPolynormableSpace
  let : T2Space A := schwartzBruhat_eval_t2
  let : T2Space W := finestLocallyConvex_t2 _
  have hT : Continuous T := by
    rw [continuous_inductiveTensor_iff]
    refine ⟨fun a ↦ ?_, fun w ↦ ?_⟩
    · exact continuous_of_finestLocallyConvex _ (T.comp (TensorProduct.mk ℂ A W a))
    · have hfun : (fun a : A ↦ T (a ⊗ₜ[ℂ] w)) = fun a ↦ E y w • Q a := by
        funext a
        change Q (TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) (a ⊗ₜ[ℂ] w))) = _
        rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul]
      rw [hfun]
      exact (continuous_const (y := E y w)).smul Q.continuous
  refine ⟨⟨T.comp e.symm.toLinearMap, hT.comp e.symm.continuous⟩, fun f x ↦ ?_⟩
  change Q (TensorProduct.rid ℂ A (LinearMap.lTensor A (E y) (e.symm f))) x = _
  rw [hQ, ← hF, e.apply_symm_apply]

/-- Paper: Theorem 8.1.0.1(1)–(2), p. 382.
The corrected test subspaces in (8.1.0.2) and (8.1.0.4) are closed in the S-adelic
Schwartz–Bruhat topology. -/
theorem sLocalOrbitalSupportTests_isClosed : IsClosed (↑U(S, T) : Set B(S)) := by
  choose Φ hΦ using sLocalOrbitalSupportTests_isClosed_slice (F := F) (S := S)
  have hset : (↑U(S, T) : Set B(S)) = ↑(sAdeleFiniteZeroSchwartz S (S \ T)) ∩
      ⋂ y, Φ y ⁻¹' (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces) : Set _) := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro hf
      refine ⟨(Submodule.mem_iInf _).mpr fun x ↦ ?_, fun y ↦ ?_⟩
      · obtain ⟨v, hv, hxv⟩ := x.property
        rw [LinearMap.mem_ker]
        exact sLocalOrbitalSupportTests_tmul_iff_zero f hf x.val v (Finset.mem_sdiff.mp hv).2 hxv
      · obtain ⟨h, hh, hfun⟩ :=
          Submodule.mem_map.mp (sLocalOrbitalSupportTests_tmul_iff_fibre f hf y)
        have hΦh : Φ y f = h :=
          SchwartzMap.ext fun x ↦ (hΦ y f x).trans (congrFun hfun x).symm
        rw [hΦh]
        exact hh
    · rintro ⟨hz, hflat⟩
      exact sLocalOrbitalSupportTests_isClosed_span f
        (fun y ↦ Submodule.mem_map.mpr ⟨Φ y f, hflat y, funext fun x ↦ hΦ y f x⟩) hz
  rw [hset]
  exact (sAdeleFiniteZeroSchwartz_isClosed (S \ T)).inter
    (isClosed_iInter fun y ↦ archimedeanFlatSchwartz_isClosed.preimage (Φ y).continuous)

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
Principal value on the selected places preserves the restricted test space. -/
theorem sLocalOrbitalSupportTests_principalValue (hT : T ⊆ S) (f : U(S, T)) :
    sAdelePrincipalValue F hT f.val ∈ U(S, T) := by
  obtain ⟨f, hf⟩ := f
  unfold sLocalOrbitalSupportTests at hf ⊢
  dsimp only at hf ⊢
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, b, hb, rfl⟩ := hg
    apply Submodule.subset_span
    refine ⟨a, fun w ↦ if w.val ∈ T then finitePlacePrincipalValue w.val (b w) else b w,
      fun w hw ↦ ?_, (sAdelePrincipalValue_tmul hT a.val b).symm⟩
    simp only [hw, ↓reduceIte]
    exact hb w hw
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The source quotient imposes the homogeneous theta kernel and the principal-value
image of the restricted tests. Its quotient topology is taken directly from those tests.
Deviation: In both source denominators the principal value acts on the same S-adelic
test space used in the numerator. -/
def sLocalOrbitalSupportRelations (hT : T ⊆ S) (η : PontryaginDual J₁(S)) :
    Submodule ℂ U(S, T) :=
  let tests : Submodule ℂ B(S) := U(S, T)
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S η
  let P : B(S) →ₗ[ℂ] B(S) := sAdelePrincipalValue F hT
  let restrictedPV : tests →ₗ[ℂ] tests :=
    LinearMap.codRestrict tests (P.domRestrict tests) (fun f ↦
      sLocalOrbitalSupportTests_principalValue (F := F) hT f)
  let K : Submodule ℂ tests := (θ.domRestrict tests).ker
  K ⊔ restrictedPV.range

/-- Abstract form: inside a subspace `U` stable under `P`, the sum of the kernel of `θ` and
the range of `P` consists of the vectors whose `θ`-class is the image of the class of
another vector of `U` under the induced map. -/
private theorem mem_sLocalOrbitalSupportRelations_iff_aux {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (U : Submodule ℂ M) (θ : M →ₗ[ℂ] N) (P : M →ₗ[ℂ] M)
    (hK : LinearMap.ker θ ≤ (LinearMap.ker θ).comap P) (hU : ∀ f : U, P f.val ∈ U) (f : U) :
    f ∈ LinearMap.ker (θ.domRestrict U) ⊔
        LinearMap.range (LinearMap.codRestrict U (P.domRestrict U) hU) ↔
      ∃ g : U, (LinearMap.ker θ).mkQ f.val =
        (LinearMap.ker θ).mapQ (LinearMap.ker θ) P hK ((LinearMap.ker θ).mkQ g.val) := by
  simp only [Submodule.mem_sup, LinearMap.mem_range, Submodule.mkQ_apply, Submodule.mapQ_apply,
    Submodule.Quotient.eq]
  constructor
  · rintro ⟨k, hk, _, ⟨g, rfl⟩, rfl⟩
    refine ⟨g, ?_⟩
    rw [LinearMap.mem_ker] at hk ⊢
    change θ (k.val + P g.val - P g.val) = 0
    rw [add_sub_cancel_right]
    exact hk
  · rintro ⟨g, hg⟩
    exact ⟨f - LinearMap.codRestrict U (P.domRestrict U) hU g, hg, _, ⟨g, rfl⟩,
      sub_add_cancel _ _⟩

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
A restricted test represents zero in the source quotient exactly when its theta class
is the principal value of the theta class of another restricted test. -/
theorem mem_sLocalOrbitalSupportRelations_iff (hT : T ⊆ S) (η : PontryaginDual J₁(S))
    (f : U(S, T)) :
    f ∈ sLocalOrbitalSupportRelations hT η ↔
      ∃ g : U(S, T), q(η) f.val = sLocalHomogeneousThetaPrincipalValue hT η (q(η) g.val) :=
  mem_sLocalOrbitalSupportRelations_iff_aux U(S, T) (sLocalHomogeneousAdelicThetaLinearMap F S η)
    (sAdelePrincipalValue F hT) (sAdelePrincipalValue_preserves_homogeneousThetaKernel hT η)
    (fun f ↦ sLocalOrbitalSupportTests_principalValue (F := F) hT f) f

local notation "π(" hT ", " η ")" => (D(hT, η)).mkQL.comp (q(η))

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The map to the ambient orbital quotient kills the source relations. -/
theorem sLocalOrbitalSupportRelations_le_ker (hT : T ⊆ S) (η : PontryaginDual J₁(S)) :
    sLocalOrbitalSupportRelations hT η ≤ ((π(hT, η)).comp (U(S, T)).subtypeL).ker := by
  intro f hf
  obtain ⟨g, hg⟩ := (mem_sLocalOrbitalSupportRelations_iff hT η f).mp hf
  change (D(hT, η)).mkQ (q(η) f.val) = 0
  rw [hg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self _ _

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The comparison is the continuous linear map induced by including restricted tests
in the full S-adelic test space. -/
def sLocalOrbitalSupportComparison (hT : T ⊆ S) (η : PontryaginDual J₁(S)) :
    (↥U(S, T) ⧸ sLocalOrbitalSupportRelations hT η) →L[ℂ] (Θ(η) ⧸ D(hT, η)) :=
  (sLocalOrbitalSupportRelations hT η).liftQL ((π(hT, η)).comp (U(S, T)).subtypeL)
    (sLocalOrbitalSupportRelations_le_ker hT η)

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The comparison sends the class of a restricted test to its ambient orbital class. -/
theorem sLocalOrbitalSupportComparison_mk (hT : T ⊆ S) (η : PontryaginDual J₁(S))
    (f : U(S, T)) :
    sLocalOrbitalSupportComparison hT η ((sLocalOrbitalSupportRelations hT η).mkQL f) =
      π(hT, η) f.val := rfl

-- TODO(paper-gap): On p. 383 the identity Λ/L_out = L_S omits the factor regularizing
-- the trivial norm-one component. Moreover the surjectivity argument on pp. 383–384
-- passes from zero-moment to unrestricted tests, and from archimedean entire Mellin
-- transforms to tests with the required finite punctured factors. Already (8.1.0.5)
-- gives the full pair space as the range for two-moment tests. For ℚ, S = {∞, 2},
-- the Gaussian pair has a double pole at zero, whose coefficient detects f(0).
-- In (8.1.0.9), L_S exp(s²) is nonzero at 1, whereas every left-hand member
-- vanishes there since L_out has a pole. On p. 384 insertion also needs the outside
-- Tamagawa masses (ERRATA I96). Both quotient comparisons fail in Sec1_Printed.

/-- Abstract form: the map induced on a quotient of a subspace `U` by a map on the ambient
space has the image of `U` as its range. -/
private theorem sLocalPrimaryOrbitalSupportComparison_range_aux {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (U : Submodule ℂ M) (R : Submodule ℂ U) (π : M →L[ℂ] N) (h : R ≤ (π.comp U.subtypeL).ker) :
    LinearMap.range (R.liftQL (π.comp U.subtypeL) h).toLinearMap = U.map π.toLinearMap := by
  rw [Submodule.toLinearMap_liftQL, Submodule.range_liftQ]
  exact (LinearMap.range_comp U.subtype π.toLinearMap).trans
    (congrArg (Submodule.map π.toLinearMap) (Submodule.range_subtype U))

/-- Paper: Theorem 8.1.0.1(1), p. 382.
The range of the primary comparison consists of the orbital classes that admit
representatives in the corrected test space (8.1.0.2).
Deviation: The comparison need not be a topological isomorphism. The unramified
character is expressed by its norm-one restriction, as in Theorem 6.2.1.1. -/
theorem sLocalPrimaryOrbitalSupportComparison_range (p : Vℚ)
    (_hp : ∀ v : V, v.under (𝓞 ℚ) = p → v ∈ S) (_hPic : PicTrivial(S))
    {ω : PontryaginDual C₁} (hω : NormOneCharacterUnramifiedOutside ω S) :
    let T := sLocalPrimaryPlaces S p
    let hT := sLocalPrimaryPlaces_subset S p
    let η := sLocalNormOneCharacter S ω hω
    let A : (↥U(S, T) ⧸ sLocalOrbitalSupportRelations hT η) →L[ℂ]
        SLocalPrimaryOrbitalQuotient p η := sLocalOrbitalSupportComparison hT η
    LinearMap.range A.toLinearMap = (U(S, T)).map (π(hT, η)).toLinearMap := by
  intro T hT η A
  exact sLocalPrimaryOrbitalSupportComparison_range_aux U(S, T)
    (sLocalOrbitalSupportRelations hT η) (π(hT, η)) (sLocalOrbitalSupportRelations_le_ker hT η)

/-- Paper: Theorem 8.1.0.1(2), p. 382.
The range of the single-place comparison consists of the orbital classes that admit
representatives in the corrected test space (8.1.0.4).
Deviation: The comparison need not be a topological isomorphism. The unramified
character is expressed by its norm-one restriction, as in Theorem 6.2.1.1. -/
theorem sLocalPlaceOrbitalSupportComparison_range (v : S) (_hPic : PicTrivial(S))
    {ω : PontryaginDual C₁} (hω : NormOneCharacterUnramifiedOutside ω S) :
    let T : Finset V := {v.val}
    let hT : T ⊆ S := Finset.singleton_subset_iff.mpr v.property
    let η := sLocalNormOneCharacter S ω hω
    LinearMap.range (sLocalOrbitalSupportComparison hT η).toLinearMap =
      (U(S, T)).map (π(hT, η)).toLinearMap := by
  intro T hT η
  exact sLocalPrimaryOrbitalSupportComparison_range_aux U(S, T)
    (sLocalOrbitalSupportRelations hT η) (π(hT, η)) (sLocalOrbitalSupportRelations_le_ker hT η)

-- TODO(later): needs §§8.2–8.3 for the announced stack description and the
-- support of the transposed dual basis elements (Theorem 8.3.0.1, p. 387).
-- TODO(paper-gap): The support assertion for ambient test functions on pp. 387–388
-- fails: the open set with every coordinate nonzero is dense, so an ambient
-- continuous function supported on its complement vanishes. On ℚ with S = {∞, 2},
-- the double-pole coefficient of the Gaussian at zero gives a nonzero orbital
-- functional. The support of that distribution and the support of its test
-- functions play different roles.

end RiemannMasullo
