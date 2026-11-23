module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # The polar-free multiplication claim in §5.3.4 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped BigOperators

namespace RiemannMasullo

local notation "RealPlaces(" F ")" => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "ComplexPlaces(" F ")" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

open Classical in
/-- Paper: Definition 5.3.4.1, p. 259. The function image of the tensor
product in (5.3.4.1) on the S-ideles is the span of the pure products with an
archimedean flat factor and multiplicative Schwartz–Bruhat finite factors. -/
def Printed.polarFreeTensorFunctions {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}) :
    Submodule ℂ ((SAdeleRing F S)ˣ → ℂ) :=
  Submodule.span ℂ {f | ∃ (h : archimedeanFlatSchwartz
      (ι := RealPlaces(F)) (κ := ComplexPlaces(F)))
    (k : ∀ v : S, SchwartzBruhat (v.val.adicCompletion F)ˣ),
    ∀ g, f g = h.val ((fun w ↦ (r w).val (g.val.1 w.val)),
      (fun w ↦ (c w).val (g.val.1 w.val))) *
        ∏ v : S, k v (Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom g)}

/-- Paper: Lemma 5.3.4.2(3), p. 260. As printed: For every number field and finite
set of places containing the archimedean places, multiplication by any continuous
quasi-character trivial on the diagonal S-units preserves the polar-free tensor
functions of (5.3.4.1). This is the closure under multiplication clause, on the
S-ideles where the quasi-character is defined. The finite factors are those on
the multiplicative local groups. See `sAdelePolarFree_quasiCharacter_mul` and ERRATA F236. -/
def Printed.sAdelePolarFreeTensor_quasiCharacter_mul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
    (b : QuasiCharacter (SIdeleQuotient F S)) (f : (SAdeleRing F S)ˣ → ℂ),
    f ∈ Printed.polarFreeTensorFunctions S r c →
      (fun g ↦ b (QuotientGroup.mk g) * f g) ∈ Printed.polarFreeTensorFunctions S r c

private theorem polarFreeTensor_schwartz_bounded {G : Type} [CommGroup G]
    [TopologicalSpace G] (f : SchwartzBruhat G) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  let B : Submodule ℂ (G → ℂ) :=
    { carrier := {g | ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C}
      zero_mem' := ⟨0, fun _ ↦ by simp⟩
      add_mem' := by
        intro g h hg hh
        obtain ⟨A, hA⟩ := hg
        obtain ⟨C, hC⟩ := hh
        exact ⟨A + C, fun x ↦ (norm_add_le _ _).trans (add_le_add (hA x) (hC x))⟩
      smul_mem' := by
        intro c g hg
        obtain ⟨C, hC⟩ := hg
        exact ⟨‖c‖ * C, fun x ↦ by
          change ‖c • g x‖ ≤ _
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩ }
  have hB : schwartzBruhatSubmodule G ≤ B := by
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s, rfl⟩
    refine ⟨elementarySchwartzSeminorm (0, 0, 0, 0) s, fun x ↦ ?_⟩
    rw [schwartzBruhatStageRealization_apply]
    split_ifs
    · change (‖s _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound s.val _).toReal
      apply ENNReal.toReal_mono (s.property.2 _).ne
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ENNReal)) _
    · exact norm_zero.trans_le (apply_nonneg _ _)
  exact hB f.property

open scoped ContDiff in
private theorem polarFreeTensor_geometric_stage (q : ℝ) (hq : 1 < q) :
    (fun y : ElementaryLieGroup 0 0 1 PUnit ↦
      if 0 ≤ y.2.2.1 0 then (q : ℂ)⁻¹ ^ (y.2.2.1 0).toNat else 0) ∈
      elementarySchwartzSubmodule 0 0 1 PUnit := by
  let f : ElementaryLieGroup 0 0 1 PUnit → ℂ := fun y ↦
    if 0 ≤ y.2.2.1 0 then (q : ℂ)⁻¹ ^ (y.2.2.1 0).toNat else 0
  have hconst (z : Fin 1 → ℤ) (b : PUnit)
      (x : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0)) :
      f (elementaryCover x z b) = f (0, 0, z, b) := rfl
  refine ⟨fun z b ↦ ?_, fun ⟨α, β, γ, δ⟩ ↦ ?_⟩
  · change ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x z b))
    simp only [hconst]
    exact contDiff_const
  obtain rfl : β = 0 := Subsingleton.elim _ _
  obtain rfl : γ = 0 := Subsingleton.elim _ _
  have hdecay := tendsto_pow_const_div_const_pow_of_one_lt (δ 0) hq
  obtain ⟨C, hC⟩ := hdecay.bddAbove_range
  change elementarySchwartzBound f (α, 0, 0, δ) < ⊤
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := max 0 C))
  simp only [elementarySchwartzBound, elementaryPartial_zero, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul, hconst]
  refine iSup_le fun x ↦ iSup_le fun z ↦ iSup_le fun b ↦ ?_
  simp only [f, Fin.prod_univ_one]
  split_ifs with h
  · have hcast (a : ℂ) : (‖a‖₊ : ENNReal) = ENNReal.ofReal ‖a‖ := (ofReal_norm a).symm
    rw [hcast]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (le_of_lt (zero_lt_one.trans hq)), Complex.norm_intCast,
      abs_of_nonneg (Int.cast_nonneg h), inv_pow, ← div_eq_mul_inv]
    have hz : (↑(z 0).toNat : ℝ) = (z 0 : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h
    rw [← hz]
    exact (hC (Set.mem_range_self (z 0).toNat)).trans (le_max_right _ _)
  · simp

open scoped Topology in
open Filter in
private theorem polarFreeTensor_geometric_valuation {G : Type} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (d : G →* Multiplicative ℤ) (π : G) (hπ : d π = Multiplicative.ofAdd 1)
    (ho : IsOpen (d.ker : Set G)) (hc : IsCompact (d.ker : Set G))
    (q : ℝ) (hq : 1 < q) :
    ∃ k : SchwartzBruhat G, ∀ n : ℕ, k (π ^ n) = (q : ℂ)⁻¹ ^ n := by
  classical
  have hgen : IsCompactlyGeneratedGroup G := by
    refine ⟨insert π (d.ker : Set G), mem_of_superset (ho.mem_nhds d.ker.one_mem)
      (Set.subset_insert _ _), hc.insert π, top_unique fun x _ ↦ ?_⟩
    let H := Subgroup.closure (insert π (d.ker : Set G))
    have hpH : π ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
    have hx : x * π ^ (-(d x).toAdd) ∈ d.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hπ]
      change Multiplicative.ofAdd ((d x).toAdd + (-(d x).toAdd) * 1) = 1
      simp
    have hxH : x * π ^ (-(d x).toAdd) ∈ H :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
    simpa [mul_assoc, ← zpow_add] using H.mul_mem hxH (H.zpow_mem hpH (d x).toAdd)
  let A : BruhatStructuralPair G := ⟨(⊤, OrderDual.toDual d.ker), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv
      (⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩ :
        G ≃ₜ* (⊤ : Subgroup G))
      hgen,
    ⟨hc.isClosed, isOpen_lcaAnnihilator _ hc, by
      let : CompactSpace (lcaAnnihilator d.ker) :=
        isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator _ ho)
      exact (isCompactlyGeneratedGroup_of_compact (G := lcaAnnihilator d.ker))⟩, le_top⟩
  let dTop : (⊤ : Subgroup G) →* Multiplicative ℤ := d.comp (⊤ : Subgroup G).subtype
  have hd : Function.Surjective dTop := by
    intro n
    refine ⟨⟨π ^ n.toAdd, trivial⟩, ?_⟩
    change d (π ^ n.toAdd) = n
    rw [map_zpow, hπ]
    change Multiplicative.ofAdd (n.toAdd * 1) = n
    simp
  let E : A.quotient ≃* Multiplicative ℤ := QuotientGroup.quotientKerEquivOfSurjective dTop hd
  let : DiscreteTopology A.quotient := QuotientGroup.discreteTopology
    (ho.preimage continuous_subtype_val)
  let L : ℤ ≃+ ElementaryLieGroup 0 0 1 PUnit :=
    { toFun := fun n ↦ (0, 0, fun _ ↦ n, PUnit.unit)
      invFun := fun y ↦ y.2.2.1 0
      left_inv := fun _ ↦ rfl
      right_inv := fun y ↦ Prod.ext (Subsingleton.elim _ _) (Prod.ext
        (Subsingleton.elim _ _) (Prod.ext (funext fun i ↦ congrArg y.2.2.1 (Subsingleton.elim 0 i))
          (Subsingleton.elim _ _)))
      map_add' := fun _ _ ↦ Prod.ext (Subsingleton.elim _ _)
        (Prod.ext (Subsingleton.elim _ _) rfl) }
  let e : ElementaryLCAPresentation A.quotient :=
    ⟨0, 0, 1, PUnit, ⟨E.trans L.toMultiplicative,
      continuous_of_discreteTopology, continuous_of_discreteTopology⟩⟩
  let s : SchwartzBruhatStage e := ⟨_, polarFreeTensor_geometric_stage q hq⟩
  refine ⟨schwartzBruhatStageInclusion A e s, fun n ↦ ?_⟩
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (show π ^ n ∈ A.val.1 from trivial)]
  have hn : (d (π ^ n)).toAdd = (n : ℤ) := by simp [map_pow, hπ]
  change (if 0 ≤ (d (π ^ n)).toAdd then (q : ℂ)⁻¹ ^ (d (π ^ n)).toAdd.toNat else 0) = _
  rw [hn, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]

private theorem polarFreeTensor_bounded_on_slice {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (r : (w : RealPlaces(F)) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : ComplexPlaces(F)) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
    (z : ℕ → (SAdeleRing F S)ˣ) (hz : ∀ n, (z n).val.1 = 1)
    (f : (SAdeleRing F S)ˣ → ℂ) (hf : f ∈ Printed.polarFreeTensorFunctions S r c) :
    ∃ C : ℝ, ∀ n, ‖f (z n)‖ ≤ C := by
  classical
  unfold Printed.polarFreeTensorFunctions at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨h, k, hk⟩ := hf
    choose B hB using fun w : S ↦ polarFreeTensor_schwartz_bounded (k w)
    let x : (RealPlaces(F) → ℝ) × (ComplexPlaces(F) → ℂ) := (1, 1)
    refine ⟨‖h.val x‖ * ∏ w, max 0 (B w), fun n ↦ ?_⟩
    rw [hk, norm_mul, norm_prod, hz]
    have harch : ((fun w : RealPlaces(F) ↦ (r w).val ((1 : InfiniteAdeleRing F) w.val)),
        (fun w : ComplexPlaces(F) ↦ (c w).val ((1 : InfiniteAdeleRing F) w.val))) = x := by
      exact Prod.ext (funext fun _ ↦ map_one _) (funext fun _ ↦ map_one _)
    rw [harch]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun w _ ↦
        (hB w _).trans (le_max_right _ _))) (norm_nonneg _)
  | zero => exact ⟨0, fun _ ↦ by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    exact ⟨A + B, fun n ↦ (norm_add_le _ _).trans (add_le_add (hA n) (hB n))⟩
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    exact ⟨‖a‖ * A, fun n ↦ by
      change ‖a • x (z n)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hA n) (norm_nonneg _)⟩

private theorem polarFreeTensor_finite_factor (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (π : (v.adicCompletion ℚ)ˣ) (k : SchwartzBruhat (v.adicCompletion ℚ)ˣ),
      ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ ∧
        ∀ n : ℕ, k (π ^ n) = (v.asIdeal.absNorm : ℂ)⁻¹ ^ n := by
  let K := v.adicCompletion ℚ
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨p, hp⟩ := V.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : Kˣ := Units.mk0 (p : K) hp.ne_zero
  have hπ : V.IsUniformizer π.val := hp
  have hvπ : V π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective ℚ)))
  let d : Kˣ →* Multiplicative ℤ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (-(WithZero.log (V x.val)))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), neg_add]
        rfl }
  have hdπ : d π = Multiplicative.ofAdd 1 := by
    change Multiplicative.ofAdd (-(WithZero.log (V π.val))) = _
    simp [hvπ]
  have hk : (d.ker : Set Kˣ) = (v.adicCompletionIntegers ℚ).units := by
    ext x
    change x ∈ d.ker ↔ x ∈ (v.adicCompletionIntegers ℚ).units
    rw [MonoidHom.mem_ker, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    change Multiplicative.ofAdd (-(WithZero.log (V x.val))) = Multiplicative.ofAdd 0 ↔
      V x.val = 1
    rw [Equiv.apply_eq_iff_eq, neg_eq_zero]
    exact ⟨fun h ↦ by simpa [h] using (WithZero.exp_log ((map_ne_zero V).2 x.ne_zero)).symm,
      fun h ↦ by simp [h]⟩
  have ho : IsOpen (d.ker : Set Kˣ) := hk ▸
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  have hc : IsCompact (d.ker : Set Kˣ) := hk ▸
    Submonoid.units_isCompact
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let : LocallyCompactSpace K := locallyCompactSpace_adicCompletion v
  let : LocallyCompactSpace Kˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  obtain ⟨k, hkn⟩ := polarFreeTensor_geometric_valuation d π hdπ ho hc _ hq
  exact ⟨π, k, norm_uniformizer_adicCompletion v _ hπ, by simpa using hkn⟩

open Function Set in
open scoped Topology in
private theorem polarFreeTensor_exists_flat_at_one (ι κ : Type*) [Fintype ι] [Fintype κ] :
    ∃ h : archimedeanFlatSchwartz (ι := ι) (κ := κ), h.val (1, 1) = 1 := by
  let U : Set ((ι → ℝ) × (κ → ℂ)) :=
    {x | (∀ i, x.1 i ≠ 0) ∧ (∀ j, x.2 j ≠ 0)}
  have hU : IsOpen U := by
    rw [show U = (⋂ i, {x : (ι → ℝ) × (κ → ℂ) | x.1 i ≠ 0}) ∩
      ⋂ j, {x : (ι → ℝ) × (κ → ℂ) | x.2 j ≠ 0} from by ext x; simp [U]]
    exact (isOpen_iInter_of_finite fun i ↦
      isOpen_ne_fun ((continuous_apply i).comp continuous_fst) continuous_const).inter
      (isOpen_iInter_of_finite fun j ↦
        isOpen_ne_fun ((continuous_apply j).comp continuous_snd) continuous_const)
  have h1 : ((1, 1) : (ι → ℝ) × (κ → ℂ)) ∈ U := by simp [U]
  obtain ⟨u, hsupport, hcompact, hsmooth, -, hvalue⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds h1)
  let g := Complex.ofRealCLM ∘ u
  have hgSupport : tsupport g ⊆ U := (tsupport_comp_subset rfl _).trans hsupport
  have hgCompact : HasCompactSupport g := hcompact.comp_left rfl
  let f := hgCompact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hsmooth)
  have hf : f ∈ archimedeanFlatSchwartz := by
    refine mem_archimedeanFlatSchwartz_of_tsupport f (Set.disjoint_left.mpr ?_)
    intro x hx hw
    have hxU := hgSupport hx
    rcases hw with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact hxU.1 i hi
    · exact hxU.2 j hj
  refine ⟨⟨f, hf⟩, ?_⟩
  change (u (1, 1) : ℂ) = 1
  simp [hvalue]

open scoped NNReal in
open Filter in
/-- Paper: Lemma 5.3.4.2(3), p. 260. Take ℚ with the real and 2-adic places.
Use a flat bump equal to one at the archimedean identity. At the finite
place, take a unit-invariant factor with value q⁻ⁿ on the nonnegative
valuation shells and zero on the negative shells, where q is the residue
field cardinality. The sequence decays rapidly on the valuation lattice.
Twisting by the inverse square of the S-idelic norm changes the values
on the slice through the archimedean identity to qⁿ. Every finite slice of
a tensor function is a finite linear combination of bounded Schwartz–Bruhat
functions. -/
theorem Printed.sAdelePolarFreeTensor_quasiCharacter_mul_false :
    ¬ Printed.sAdelePolarFreeTensor_quasiCharacter_mul := by
  classical
  intro hall
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨2, Nat.prime_two⟩
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v}
  let w : S := ⟨v, Finset.mem_singleton_self v⟩
  have hw (u : S) : u = w := Subtype.ext (Finset.mem_singleton.mp u.property)
  let : Unique S := ⟨⟨w⟩, hw⟩
  let r (u : RealPlaces(ℚ)) :
      {e : u.val.Completion ≃+* ℝ // IsHomeomorph (e : u.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal u.property,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal u.property).toHomeomorph.isHomeomorph⟩
  let c (u : ComplexPlaces(ℚ)) :
      {e : u.val.Completion ≃+* ℂ // IsHomeomorph (e : u.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex u.property,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex u.property).toHomeomorph.isHomeomorph⟩
  obtain ⟨h, hh⟩ := polarFreeTensor_exists_flat_at_one (RealPlaces(ℚ)) (ComplexPlaces(ℚ))
  obtain ⟨π, k₀, hπ, hk₀⟩ := polarFreeTensor_finite_factor v
  let z (n : ℕ) : (SAdeleRing ℚ S)ˣ :=
    MulEquiv.prodUnits.symm (1, MulEquiv.piUnits.symm (Pi.mulSingle w (π ^ n)))
  have hz (n : ℕ) : (z n).val.1 = 1 := rfl
  let k (u : S) : SchwartzBruhat (u.val.adicCompletion ℚ)ˣ :=
    (hw u).symm ▸ k₀
  have hkw : k w = k₀ := by dsimp only [k]
  let f (g : (SAdeleRing ℚ S)ˣ) :=
    h.val ((fun u ↦ (r u).val (g.val.1 u.val)), (fun u ↦ (c u).val (g.val.1 u.val))) *
      ∏ u : S, k u (Units.map ((Pi.evalRingHom _ u).comp (RingHom.snd _ _)).toMonoidHom g)
  have hf : f ∈ Printed.polarFreeTensorFunctions S r c :=
    Submodule.subset_span ⟨h, k, fun _ ↦ rfl⟩
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    change 1 < (v.asIdeal.absNorm : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans hq))
  have hπn (n : ℕ) :
      Units.map ((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).toMonoidHom (z n) = π ^ n := by
    apply Units.ext
    change (Pi.mulSingle (M := fun u : S ↦ (u.val.adicCompletion ℚ)ˣ) w (π ^ n) w).val = (π ^ n).val
    rw [Pi.mulSingle_eq_same]
  have hfz (n : ℕ) : f (z n) = (q : ℂ)⁻¹ ^ n := by
    change h.val ((fun u ↦ (r u).val ((z n).val.1 u.val)),
        (fun u ↦ (c u).val ((z n).val.1 u.val))) *
      ∏ u : S, k u (Units.map ((Pi.evalRingHom _ u).comp (RingHom.snd _ _)).toMonoidHom (z n)) = _
    rw [hz, Fintype.prod_subsingleton _ w, hπn, hkw]
    have hm : ((fun u : RealPlaces(ℚ) ↦ (r u).val ((1 : InfiniteAdeleRing ℚ) u.val)),
        (fun u : ComplexPlaces(ℚ) ↦ (c u).val ((1 : InfiniteAdeleRing ℚ) u.val))) =
        ((1, 1) : (RealPlaces(ℚ) → ℝ) × (ComplexPlaces(ℚ) → ℂ)) :=
      Prod.ext (funext fun _ ↦ map_one _) (funext fun _ ↦ map_one _)
    rw [hm, hh, one_mul, hk₀]
    simp [q]
  let m := sIdeleQuotientNorm ℚ S
  let b : QuasiCharacter (SIdeleQuotient ℚ S) :=
    quasiCharacterNormTwist m (isProperMap_sIdeleQuotientNorm ℚ S).continuous 1 (-2)
  have hmod (n : ℕ) : (((m (QuotientGroup.mk (z n)) : ℝ≥0) : ℝ) : ℂ) =
      (q : ℂ)⁻¹ ^ n := by
    rw [show m (QuotientGroup.mk (z n)) = sIdeleNorm ℚ S (z n) from
      sIdeleQuotientNorm_mk ℚ S (z n)]
    let ev : ((SAdeleRing ℚ S)ˣ →* ℝ≥0ˣ) →* ℝ :=
      NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval (z n)))
    change (ev (sIdeleNorm ℚ S) : ℂ) = _
    simp only [sIdeleNorm, map_mul, map_prod, map_pow]
    change (((∏ u : InfinitePlace ℚ, ‖(z n).val.1 u‖ ^ u.mult) *
      ∏ u : S, ‖(z n).val.2 u‖ : ℝ) : ℂ) = _
    rw [hz, Fintype.prod_subsingleton _ w]
    have hx : (z n).val.2 w = (π ^ n).val :=
      congrArg Units.val (hπn n)
    have harch (u : InfinitePlace ℚ) : ‖((1 : InfiniteAdeleRing ℚ) u)‖ = 1 :=
      norm_one
    simp only [harch, one_pow, Finset.prod_const_one, one_mul, hx,
      Units.val_pow_eq_pow_val, norm_pow, hπ, Complex.ofReal_pow, Complex.ofReal_inv]
    rfl
  obtain ⟨C, hC⟩ := polarFreeTensor_bounded_on_slice S r c z hz _
    (hall ℚ S r c b f hf)
  have hb (n : ℕ) : b (QuotientGroup.mk (z n)) * f (z n) = (q : ℂ) ^ n := by
    change (1 * (((m (QuotientGroup.mk (z n)) : ℝ≥0) : ℝ) : ℂ) ^ (-2 : ℂ)) * _ = _
    rw [one_mul, hmod, hfz, ← show ((-2 : ℤ) : ℂ) = -2 by norm_num,
      Complex.cpow_intCast, zpow_neg]
    change (((q : ℂ)⁻¹ ^ n) ^ (2 : ℕ))⁻¹ * (q : ℂ)⁻¹ ^ n = (q : ℂ) ^ n
    simp only [inv_pow, inv_inv]
    rw [pow_two, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]
  have hlarge := (tendsto_pow_atTop_atTop_of_one_lt hq).eventually (eventually_gt_atTop C)
  obtain ⟨n, hn⟩ := hlarge.exists
  have hbnd := hC n
  change ‖b (QuotientGroup.mk (z n)) * f (z n)‖ ≤ C at hbnd
  rw [hb, norm_pow, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (zero_lt_one.trans hq))] at hbnd
  exact (not_lt_of_ge hbnd) hn

end RiemannMasullo
