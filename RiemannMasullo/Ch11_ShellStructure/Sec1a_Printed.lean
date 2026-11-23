module

public import RiemannMasullo.Ch11_ShellStructure.Sec1a
import all RiemannMasullo.Ch11_ShellStructure.Sec1a
import all RiemannMasullo.AppA_AlgebraicNT.Sec1
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Printed convergence criteria in §11.1.1

The repaired statements are in Sec1a.lean.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField.AdeleRing nonZeroDivisors

namespace RiemannMasullo

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "N[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "Frac[" F "]" => FractionalIdeal (𝓞 F)⁰ F
local notation "principal[" F "]" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "ideleValue[" F "]" => fun (φ : ℬ[F]) (g : 𝕀[F]) ↦ φ (Multiplicative.ofAdd (Units.val g))
local notation "classOf[" F "]" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

local instance instIdeleMeasurableSpaceSec1aPrinted (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace 𝕀[F] := borel _

-- TODO(paper-gap): Proposition 11.1.1.2, p. 476, defines f and the finite
-- value J_F(α) on Z, then evaluates both on its saturation. It does not
-- specify an arbitrary extension of f. Extending J by its ideal-series
-- formula forces all f_k to vanish on the saturation (test at 2^n g).
-- The zero sequence with a nonzero extension of f refutes the arbitrary-
-- extension interpretation only. Sec1a states the criterion on the repaired domains.

/-- Paper: Corollary 11.1.1.4, p. 478. As printed, each absolute orbit sum
has a bound depending on the orbit alone, from which the paper claims
pointwise convergence on the idele class group.
Deviation: The orbit majorant is indexed by ξ, with ξ representing ξg.
The repeated g in (2)(b) refers to the representative with these witnesses,
as in the sentence immediately following (11.1.1.10). -/
def Printed.cond_adelicTheta_pointwiseConvergence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (e : (ℝ≥0ˣ × N[F]) ≃ₜ* 𝕀[F])
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (rep : CommRing.Pic (𝓞 F) → N[F]) (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ),
    let E₁ := ideleFundamentalDomain F b v₀ σ rep
    let Z := e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ E₁)
    (∀ t h, ideleNorm F (e (t, h)) = t) →
    (∀ h, e (1, h) = h.val) →
    rep 1 = 1 → (∀ c, ideleIdealClass F (rep c).val = c) →
    (∀ g, Tendsto (fun k ↦ ideleValue[F] (φ k) g) atTop (𝓝 (f g))) →
    (∀ g : 𝕀[F], ∃ (α : Fˣ → ℝ≥0) (I : Frac[F]),
      Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α ξ.val : ℝ)) ∧
      (g ∈ Z → ∀ (_ξ : Fˣ) k, (∑' ξ : Fˣ, ‖ideleValue[F] (φ k) (principal[F] ξ * g)‖) ≤
        ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α ξ.val : ℝ))) →
    (∀ g ∈ Z, Summable (fun ξ : Fˣ ↦ ‖f (principal[F] ξ * g)‖)) ∧
    ∃ Θ : C[F] → ℂ, (∀ g, Θ (classOf[F] g) = ideleThetaSum f g) ∧
      ∀ c, Tendsto (fun k ↦ adelicTheta (φ k) c) atTop (𝓝 (Θ c))

/-- Paper: Corollary 11.1.1.4, p. 478. Over ℚ let the archimedean factor be
B(x − (k + 1)), for a nonnegative smooth bump bounded by 1, supported in
(−1/4, 1/4), with B(0) = 1. The finite factor is the indicator of the
finite integral adeles. These functions tend pointwise to zero. On the standard
section times the domain, the finite factor restricts the sum to nonzero
integers and the archimedean coordinates are spaced by the norm t > 0.
Use the unit ideal and the orbit majorant supported at index 1 with value
2 + 1/t. The theta series at the identity is 1 for every k. -/
theorem Printed.cond_adelicTheta_pointwiseConvergence_false :
    ¬ Printed.cond_adelicTheta_pointwiseConvergence := by sorry

/-- Paper: Corollary 11.1.1.5, p. 479. As printed, a slice-integrable
majorant on the total absolute orbit sums is assumed to imply pointwise
convergence of the homogeneous theta averages.
The approximants use the Schwartz–Bruhat operator from Definition 2.2.5.1.
Deviation: In the new limit integral the character is extended trivially on
the norm section. Slice integrability is written by pullback to the domain. -/
def Printed.cond_homogeneousTheta_pointwiseConvergence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (e : (ℝ≥0ˣ × N[F]) ≃ₜ* 𝕀[F])
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (rep : CommRing.Pic (𝓞 F) → N[F]) (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ),
    let E₁ := ideleFundamentalDomain F b v₀ σ rep
    let Z := e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ E₁)
    let μ₁ := (normOneIdeleTamagawaMeasure F).restrict E₁
    (∀ t h, ideleNorm F (e (t, h)) = t) →
    (∀ h, e (1, h) = h.val) →
    rep 1 = 1 → (∀ c, ideleIdealClass F (rep c).val = c) →
    (∀ g, Tendsto (fun k ↦ ideleValue[F] (φ k) g) atTop (𝓝 (f g))) →
    (∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
      Measurable α ∧
      (∀ g, Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
        (α (principal[F] ξ.val * g) : ℝ))) ∧
      Measurable (fractionalIdealOrbitSum I α) ∧
      (∀ t, Integrable (fun h : N[F] ↦ fractionalIdealOrbitSum I α (e (t, h))) μ₁) ∧
      ∀ g ∈ Z, ∀ k,
        (∑' ξ : Fˣ, ‖ideleValue[F] (φ k) (principal[F] ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) →
    ∀ ω : PontryaginDual C₁[F],
      (∀ g : 𝕀[F], Integrable (fun h : N[F] ↦
        let h₀ := (e.symm (g * h.val)).2
        ideleThetaSum f (g * h.val) * (ω ⟨classOf[F] h₀.val, h₀.property⟩ : ℂ)) μ₁) ∧
      ∃ (A : C[F] ⧸ C₁[F] → ℂ) (Aₖ : ℕ → C[F] ⧸ C₁[F] → ℂ),
        (∀ g, A (QuotientGroup.mk' _ (classOf[F] g)) =
          homogeneousThetaSectionAverage e v₀ σ b rep ω f g) ∧
        (∀ k g, Aₖ k (QuotientGroup.mk' _ (classOf[F] g)) =
          homogeneousAdelicTheta ω (φ k) (classOf[F] g)) ∧
        ∀ q, Tendsto (fun k ↦ Aₖ k q) atTop (𝓝 (A q))

section CondHomogeneousThetaFalse

open IsDedekindDomain InfinitePlace.Completion
open scoped Pointwise ContDiff

local notation "principalℚ" => IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ

/-- The real coordinate of a rational adele. -/
private def condHT_inf : 𝔸[ℚ] →+* ℝ :=
  (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).comp
    ((Pi.evalRingHom (fun w : InfinitePlace ℚ ↦ w.Completion) Rat.infinitePlace).comp
      (RingHom.fst _ _))

private theorem condHT_inf_apply (x : 𝔸[ℚ]) :
    condHT_inf x = extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x.1 Rat.infinitePlace) :=
  rfl

private theorem condHT_inf_continuous : Continuous condHT_inf :=
  (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    ((continuous_apply _).comp continuous_fst)

private theorem condHT_inf_algebraMap (q : ℚ) : condHT_inf (algebraMap ℚ 𝔸[ℚ] q) = q := by
  have h := map_ratCast (condHT_inf.comp (algebraMap ℚ 𝔸[ℚ])) q
  rw [Rat.cast_id] at h
  exact h

private theorem condHT_inf_principal (ξ : ℚˣ) (g : 𝕀[ℚ]) :
    condHT_inf (principalℚ ξ * g).val = (ξ : ℚ) * condHT_inf g.val := by
  rw [Units.val_mul, map_mul]
  congr 1
  exact condHT_inf_algebraMap (ξ : ℚ)

private theorem condHT_pic : Subsingleton (CommRing.Pic (𝓞 ℚ)) := by
  have : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq Rat.classNumber_eq)
  exact (ClassGroup.equivPic (𝓞 ℚ)).symm.toEquiv.subsingleton

private theorem condHT_section (t : ℝ≥0ˣ) :
    condHT_inf (canonicalIdeleNormSection ℚ t).val = (t : ℝ) ∧
      (canonicalIdeleNormSection ℚ t).val ∈ integralAdelesOutside ℚ ∅ := by
  refine ⟨?_, ?_⟩
  · have h := canonicalIdeleNormSection_infinite ℚ t Rat.infinitePlace
    rw [← extensionEmbeddingOfIsReal_apply Rat.isReal_infinitePlace, Module.finrank_self,
      Nat.cast_one, inv_one, Real.rpow_one] at h
    rw [condHT_inf_apply]
    exact_mod_cast h
  · have h := canonicalIdeleNormSection_finite ℚ t
    simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      forall_const, Subring.mem_comap]
    intro v
    change (canonicalIdeleNormSection ℚ t).val.2 v ∈ v.adicCompletionIntegers ℚ
    rw [h]
    exact (v.adicCompletionIntegers ℚ).one_mem

private theorem condHT_E1
    (b : Module.Basis (Fin (Units.rank ℚ)) ℤ (Additive ((𝓞 ℚ)ˣ ⧸ Units.torsion ℚ)))
    (σ : ℂ ≃ₐ[ℝ] ℂ) (h : N[ℚ])
    (hh : h ∈ ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ]))) :
    condHT_inf h.val.val = 1 ∧ h.val.val ∈ integralAdelesOutside ℚ ∅ ∧
      (h.val⁻¹).val ∈ integralAdelesOutside ℚ ∅ := by
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hh
  have hc' : h ∈ (1 : N[ℚ]) • {g : N[ℚ] | g.val ∈ (Units.map (integralAdelesOutside ℚ ∅).subtype.toMonoidHom).range ∧
      (Units.map (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom) g.val ∈
        (infiniteIdeleNorm ℚ).ker.subtype '' infiniteIdeleFundamentalDomain ℚ b Rat.infinitePlace σ} := hc
  rw [one_smul] at hc'
  obtain ⟨⟨u, hu⟩, g, hgE, hg⟩ := hc'
  have hg' : g.val.val = h.val.val.1 := congrArg Units.val hg
  have hpos := (inTorsionSector_real ℚ Rat.infinitePlace σ Rat.isReal_infinitePlace _).mp hgE.2
  change 0 < extensionEmbeddingOfIsReal _ (g.val.val Rat.infinitePlace) at hpos
  have hnorm : ‖g.val.val Rat.infinitePlace‖ = 1 := by
    have h1 := congrArg (fun x : ℝ≥0ˣ ↦ ((x : ℝ≥0) : ℝ)) g.property
    simp only [infiniteIdeleNorm] at h1
    rw [MonoidHom.finsetProd_apply, Fintype.prod_subsingleton _ Rat.infinitePlace,
      InfinitePlace.mult_isReal ⟨_, Rat.isReal_infinitePlace⟩, pow_one] at h1
    simp at h1
    exact h1
  have hiso := (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) (g.val.val Rat.infinitePlace)
  refine ⟨?_, ?_, ?_⟩
  · rw [condHT_inf_apply, ← hg']
    rw [hnorm, Real.norm_eq_abs, abs_of_pos hpos] at hiso
    exact hiso
  · rw [← hu]
    exact u.val.property
  · rw [← hu, ← map_inv]
    exact (u⁻¹).val.property

private theorem condHT_Z (e : (ℝ≥0ˣ × N[ℚ]) ≃ₜ* 𝕀[ℚ])
    (he : ∀ t g, e (t, g) = canonicalIdeleNormSection ℚ t * g.val)
    (b : Module.Basis (Fin (Units.rank ℚ)) ℤ (Additive ((𝓞 ℚ)ˣ ⧸ Units.torsion ℚ)))
    (σ : ℂ ≃ₐ[ℝ] ℂ) (g : 𝕀[ℚ])
    (hg : g ∈ e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ
      ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ])))) :
    condHT_inf g.val = ((ideleNorm ℚ g : ℝ≥0) : ℝ) ∧ g.val ∈ integralAdelesOutside ℚ ∅ ∧
      (g⁻¹).val ∈ integralAdelesOutside ℚ ∅ := by
  obtain ⟨⟨t, h⟩, ⟨-, hh⟩, rfl⟩ := hg
  obtain ⟨h1, h2, h3⟩ := condHT_E1 b σ h hh
  obtain ⟨s1, s2⟩ := condHT_section t
  have hs3 : ((canonicalIdeleNormSection ℚ t)⁻¹).val ∈ integralAdelesOutside ℚ ∅ := by
    rw [← map_inv]
    exact (condHT_section t⁻¹).2
  have hn : ideleNorm ℚ (e (t, h)) = t := by
    rw [he, map_mul, canonicalIdeleNormSection_rightInverse ℚ t, MonoidHom.mem_ker.mp h.property,
      mul_one]
  rw [hn, he]
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, s1, h1, mul_one]
  · rw [Units.val_mul]
    exact Subring.mul_mem _ s2 h2
  · rw [mul_inv, Units.val_mul]
    exact Subring.mul_mem _ hs3 h3

private theorem condHT_int (ξ : ℚˣ) (g : 𝕀[ℚ])
    (h1 : (principalℚ ξ * g).val ∈ integralAdelesOutside ℚ ∅)
    (h2 : (g⁻¹).val ∈ integralAdelesOutside ℚ ∅) : ∃ n : ℤ, (ξ : ℚ) = n := by
  have hmem : algebraMap ℚ 𝔸[ℚ] ξ ∈ integralAdelesOutside ℚ ∅ := by
    have h := Subring.mul_mem _ h1 h2
    rw [← Units.val_mul, mul_inv_cancel_right] at h
    exact h
  rw [diagonal_mem_integralAdelesOutside] at hmem
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ (ξ : ℚ)
    (fun v ↦ hmem v (by simp))
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [Rat.ringOfIntegersEquiv_apply_coe, hr]⟩

private theorem condHT_norm_principal (η : ℚˣ) (g : 𝕀[ℚ]) :
    ideleNorm ℚ (principalℚ η * g) = ideleNorm ℚ g := by
  rw [map_mul, MonoidHom.mem_ker.mp ((ideleNorm_spec ℚ).2 ⟨η, rfl⟩), one_mul]

private theorem condHT_Z_unique (e : (ℝ≥0ˣ × N[ℚ]) ≃ₜ* 𝕀[ℚ])
    (he : ∀ t g, e (t, g) = canonicalIdeleNormSection ℚ t * g.val)
    (b : Module.Basis (Fin (Units.rank ℚ)) ℤ (Additive ((𝓞 ℚ)ˣ ⧸ Units.torsion ℚ)))
    (σ : ℂ ≃ₐ[ℝ] ℂ) (g : 𝕀[ℚ]) (ξ ξ' : ℚˣ)
    (h : principalℚ ξ * g ∈ e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ
      ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ]))))
    (h' : principalℚ ξ' * g ∈ e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ
      ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ])))) : ξ = ξ' := by
  have hq : principalℚ (ξ / ξ') * (principalℚ ξ' * g) = principalℚ ξ * g := by
    rw [← mul_assoc, ← map_mul, div_mul_cancel]
  have e1 := condHT_inf_principal (ξ / ξ') (principalℚ ξ' * g)
  rw [hq, (condHT_Z e he b σ _ h).1, (condHT_Z e he b σ _ h').1, condHT_norm_principal,
    condHT_norm_principal] at e1
  have hN : (0 : ℝ) < ((ideleNorm ℚ g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleNorm ℚ g).ne_zero)
  have hq1 : (((ξ / ξ' : ℚˣ) : ℚ) : ℝ) = 1 :=
    (mul_right_cancel₀ hN.ne' (e1.symm.trans (one_mul _).symm))
  have hq2 : ((ξ / ξ' : ℚˣ) : ℚ) = 1 := by exact_mod_cast hq1
  exact div_eq_one.mp (Units.val_eq_one.mp hq2)

private theorem condHT_bump {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] {K U : Set G} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ u : SchwartzBruhat G, tsupport u.val ⊆ U ∧ (∀ x ∈ K, u x = 1) ∧ ∀ x, ‖u x‖ ≤ 1 := by
  have key : ∃ u : SchwartzBruhat G, HasCompactSupport u.val ∧ tsupport u.val ⊆ U ∧
      ∀ x ∈ K, u x = 1 := by
    refine hK.induction_on (p := fun s ↦ ∃ u : SchwartzBruhat G, HasCompactSupport u.val ∧
      tsupport u.val ⊆ U ∧ ∀ x ∈ s, u x = 1) ?_ ?_ ?_ ?_
    · refine ⟨0, ?_, ?_, fun x hx ↦ hx.elim⟩
      · change HasCompactSupport (⇑(0 : SchwartzBruhat G))
        rw [SchwartzBruhat.coe_zero]
        exact HasCompactSupport.zero
      · change tsupport (⇑(0 : SchwartzBruhat G)) ⊆ U
        rw [SchwartzBruhat.coe_zero, tsupport_zero]
        exact Set.empty_subset _
    · rintro s t hst ⟨u, hu, hsu, h1⟩
      exact ⟨u, hu, hsu, fun x hx ↦ h1 x (hst hx)⟩
    · rintro s t ⟨u, hu, hsu, h1⟩ ⟨v, hv, hsv, h2⟩
      obtain ⟨M, hM⟩ := schwartzBruhat_compactMultiplier u hu
      have hw (x : G) : (u + v - M v) x = u x + v x - u x * v x := by
        rw [SchwartzBruhat.coe_sub, SchwartzBruhat.coe_add, Pi.sub_apply, Pi.add_apply, hM]
      have hsupp : tsupport (u + v - M v).val ⊆ tsupport u.val ∪ tsupport v.val := by
        refine closure_minimal (fun x hx ↦ ?_)
          ((isClosed_tsupport _).union (isClosed_tsupport _))
        by_contra hc
        simp only [Set.mem_union, not_or] at hc
        have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport hc.1
        have hv0 : v x = 0 := image_eq_zero_of_notMem_tsupport hc.2
        apply hx
        change (u + v - M v) x = 0
        rw [hw, hu0, hv0]
        ring
      refine ⟨u + v - M v, IsCompact.of_isClosed_subset (IsCompact.union hu hv)
        (isClosed_tsupport _) hsupp, hsupp.trans (Set.union_subset hsu hsv), ?_⟩
      rintro x (hx | hx)
      · rw [hw, h1 x hx]
        ring
      · rw [hw, h2 x hx]
        ring
    · intro x hx
      obtain ⟨u, hu, hsu, h1⟩ := schwartzBruhat_exists_local_unit hU (hKU hx)
      exact ⟨_, mem_nhdsWithin_of_mem_nhds h1, u, hu, hsu, fun y hy ↦ hy⟩
  obtain ⟨u, hu, hsu, h1⟩ := key
  let c (z : ℂ) : ℂ := ((2 * z.re / (1 + z.re ^ 2) : ℝ) : ℂ)
  have hc : ContDiff ℝ (∞) c := by
    refine Complex.ofRealCLM.contDiff.comp ?_
    refine ((contDiff_const.mul Complex.reCLM.contDiff).div
      (contDiff_const.add (Complex.reCLM.contDiff.pow 2)) fun x ↦ ?_)
    positivity
  have hc0 : c 0 = 0 := by simp [c]
  obtain ⟨w, hw⟩ := compact_schwartzBruhat_comp hu hc hc0
  have hs' : tsupport w.val ⊆ tsupport u.val := hw ▸ tsupport_comp_subset hc0 _
  refine ⟨w, hs'.trans hsu, fun x hx ↦ ?_, fun x ↦ ?_⟩
  · change w.val x = 1
    rw [hw, Function.comp_apply]
    change c (u x) = 1
    rw [h1 x hx]
    norm_num [c]
  · change ‖w.val x‖ ≤ 1
    rw [hw, Function.comp_apply]
    set r := (u.val x).re
    change ‖((2 * r / (1 + r ^ 2) : ℝ) : ℂ)‖ ≤ 1
    have hpos : 0 < 1 + r ^ 2 := by positivity
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_one hpos]
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (r + 1)], by nlinarith [sq_nonneg (r - 1)]⟩

private theorem condHT_seq
    (b : Module.Basis (Fin (Units.rank ℚ)) ℤ (Additive ((𝓞 ℚ)ˣ ⧸ Units.torsion ℚ)))
    (σ : ℂ ≃ₐ[ℝ] ℂ) :
    ∃ φ : ℕ → ℬ[ℚ], ∀ k,
      (∀ x : 𝔸[ℚ], φ k (Multiplicative.ofAdd x) ≠ 0 →
        |condHT_inf x - ((k : ℝ) + 1)| < 1 / 4 ∧ x ∈ integralAdelesOutside ℚ ∅) ∧
      (∀ y, ‖φ k y‖ ≤ 1) ∧
      ∀ h ∈ ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ])),
        φ k (Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] ((k : ℚ) + 1) * h.val.val)) = 1 := by
  let : LocallyCompactSpace (Multiplicative 𝔸[ℚ]) := adeleGroupLocallyCompact ℚ
  let : T2Space (Multiplicative 𝔸[ℚ]) := adeleGroupT2 ℚ
  have : Subsingleton (CommRing.Pic (𝓞 ℚ)) := condHT_pic
  have hcpt := ideleFundamentalDomain_precompact ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ])) rfl
    (fun _ ↦ Subsingleton.elim _ _)
  have hval : Continuous (fun h : N[ℚ] ↦ h.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  have hopen : IsOpen (integralAdelesOutside ℚ ∅ : Set 𝔸[ℚ]) := isOpen_integralAdelesOutside ℚ ∅
  have hclosed : closure (ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ]))) ⊆
      {h : N[ℚ] | condHT_inf h.val.val = 1 ∧ h.val.val ∈ integralAdelesOutside ℚ ∅} := by
    refine closure_minimal (fun h hh ↦ ⟨(condHT_E1 b σ h hh).1, (condHT_E1 b σ h hh).2.1⟩) ?_
    exact (isClosed_eq (condHT_inf_continuous.comp hval) continuous_const).inter
      ((AddSubgroup.isClosed_of_isOpen (integralAdelesOutside ℚ ∅).toAddSubgroup hopen).preimage
        hval)
  let U (k : ℕ) : Set (Multiplicative 𝔸[ℚ]) := Multiplicative.toAdd ⁻¹'
    ({x | |condHT_inf x - ((k : ℝ) + 1)| < 1 / 4} ∩ integralAdelesOutside ℚ ∅)
  let K (k : ℕ) : Set (Multiplicative 𝔸[ℚ]) :=
    (fun h : N[ℚ] ↦ Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] ((k : ℚ) + 1) * h.val.val)) ''
      closure (ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ])))
  have hK (k : ℕ) : IsCompact (K k) :=
    hcpt.image (continuous_ofAdd.comp (continuous_const.mul hval))
  have hU (k : ℕ) : IsOpen (U k) :=
    ((isOpen_lt (continuous_abs.comp (condHT_inf_continuous.sub continuous_const))
      continuous_const).inter hopen).preimage continuous_toAdd
  have hKU (k : ℕ) : K k ⊆ U k := by
    rintro _ ⟨h, hh, rfl⟩
    obtain ⟨h1, h2⟩ := hclosed hh
    refine ⟨?_, ?_⟩
    · change |condHT_inf (algebraMap ℚ 𝔸[ℚ] ((k : ℚ) + 1) * h.val.val) - ((k : ℝ) + 1)| < 1 / 4
      rw [map_mul, h1, condHT_inf_algebraMap]
      push_cast
      norm_num
    · change algebraMap ℚ 𝔸[ℚ] ((k : ℚ) + 1) * h.val.val ∈ integralAdelesOutside ℚ ∅
      refine Subring.mul_mem _ ?_ h2
      rw [map_add, map_natCast, map_one]
      exact Subring.add_mem _ (natCast_mem _ k) (Subring.one_mem _)
  have hex (k : ℕ) : ∃ u : ℬ[ℚ], tsupport u.val ⊆ U k ∧ (∀ x ∈ K k, u x = 1) ∧
      ∀ x, ‖u x‖ ≤ 1 := condHT_bump (hK k) (hU k) (hKU k)
  choose φ hφ using hex
  refine ⟨φ, fun k ↦ ⟨fun x hx ↦ (hφ k).1 (subset_tsupport _ hx), (hφ k).2.2, fun h hh ↦ ?_⟩⟩
  exact (hφ k).2.1 _ ⟨h, subset_closure hh, rfl⟩

private theorem condHT_lim (φ : ℕ → ℬ[ℚ])
    (hφ : ∀ k (x : 𝔸[ℚ]), φ k (Multiplicative.ofAdd x) ≠ 0 →
      |condHT_inf x - ((k : ℝ) + 1)| < 1 / 4) (g : 𝕀[ℚ]) :
    Tendsto (fun k ↦ φ k (Multiplicative.ofAdd g.val)) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈|condHT_inf g.val|⌉₊] with k hk
  by_contra hne
  have h1 := abs_lt.mp (hφ k _ (Ne.symm hne))
  have hk' : |condHT_inf g.val| ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have := le_abs_self (condHT_inf g.val)
  linarith [h1.1]

private theorem condHT_theta_E1
    (b : Module.Basis (Fin (Units.rank ℚ)) ℤ (Additive ((𝓞 ℚ)ˣ ⧸ Units.torsion ℚ)))
    (σ : ℂ ≃ₐ[ℝ] ℂ) (u : ℬ[ℚ]) (k : ℕ)
    (hsupp : ∀ x : 𝔸[ℚ], u (Multiplicative.ofAdd x) ≠ 0 →
        |condHT_inf x - ((k : ℝ) + 1)| < 1 / 4 ∧ x ∈ integralAdelesOutside ℚ ∅)
    (h : N[ℚ]) (hh : h ∈ ideleFundamentalDomain ℚ b Rat.infinitePlace σ (fun _ ↦ (1 : N[ℚ])))
    (hone : u (Multiplicative.ofAdd (algebraMap ℚ 𝔸[ℚ] ((k : ℚ) + 1) * h.val.val)) = 1) :
    ∑' ξ : ℚˣ, u (Multiplicative.ofAdd (principalℚ ξ * h.val).val) = 1 := by
  have hk0 : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [tsum_eq_single (Units.mk0 _ hk0)]
  · exact hone
  · intro ξ hξ
    by_contra hne
    obtain ⟨h1, h2⟩ := hsupp _ hne
    obtain ⟨e1, -, e3⟩ := condHT_E1 b σ h hh
    obtain ⟨n, hn⟩ := condHT_int ξ h.val h2 e3
    rw [condHT_inf_principal, e1, mul_one, hn] at h1
    push_cast at h1
    have h1' := abs_lt.mp h1
    have hlt : (n : ℝ) < ((k + 2 : ℤ) : ℝ) := by push_cast; linarith [h1'.2]
    have hgt : ((k : ℤ) : ℝ) < (n : ℝ) := by push_cast; linarith [h1'.1]
    have hlt' := Int.cast_lt.mp hlt
    have hgt' := Int.cast_lt.mp hgt
    have hnk : n = k + 1 := by omega
    apply hξ
    apply Units.ext
    rw [Units.val_mk0, hn, hnk]
    push_cast
    ring

private theorem condHT_count (u : ℬ[ℚ]) (k : ℕ)
    (hsupp : ∀ x : 𝔸[ℚ], u (Multiplicative.ofAdd x) ≠ 0 →
        |condHT_inf x - ((k : ℝ) + 1)| < 1 / 4 ∧ x ∈ integralAdelesOutside ℚ ∅)
    (hbound : ∀ y, ‖u y‖ ≤ 1) (g : 𝕀[ℚ]) (hg1 : 0 < condHT_inf g.val)
    (hg3 : (g⁻¹).val ∈ integralAdelesOutside ℚ ∅) :
    ∑' ξ : ℚˣ, ‖u (Multiplicative.ofAdd (principalℚ ξ * g).val)‖ ≤
      2 + (condHT_inf g.val)⁻¹ := by
  set t := condHT_inf g.val with ht
  let a : ℤ := ⌈((k : ℝ) + 1 - 1 / 4) / t⌉
  let b : ℤ := ⌊((k : ℝ) + 1 + 1 / 4) / t⌋
  let S : Finset ℤ := (Finset.Icc a b).filter (fun n ↦ n ≠ 0)
  let T : Finset ℚˣ := S.attach.image (fun n ↦ Units.mk0 ((n.1 : ℤ) : ℚ)
    (by exact_mod_cast (Finset.mem_filter.mp n.2).2))
  have hsub : ∀ ξ ∉ T, ‖u (Multiplicative.ofAdd (principalℚ ξ * g).val)‖ = 0 := by
    intro ξ hξ
    by_contra hne
    rw [norm_eq_zero] at hne
    obtain ⟨h1, h2⟩ := hsupp _ hne
    obtain ⟨n, hn⟩ := condHT_int ξ g h2 hg3
    rw [condHT_inf_principal, hn, ← ht] at h1
    push_cast at h1
    have h1' := abs_lt.mp h1
    apply hξ
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact ξ.ne_zero (by rw [hn]; simp)
    have hmem : n ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩, hn0⟩
      · rw [div_le_iff₀ hg1]
        linarith [h1'.1]
      · rw [le_div_iff₀ hg1]
        linarith [h1'.2]
    exact Finset.mem_image.mpr ⟨⟨n, hmem⟩, Finset.mem_attach _ _, Units.ext (by simp [hn])⟩
  rw [tsum_eq_sum hsub]
  have hcard : (T.card : ℝ) ≤ (Finset.Icc a b).card := by
    exact_mod_cast (Finset.card_image_le.trans (by rw [Finset.card_attach])).trans
      (Finset.card_filter_le _ _)
  calc ∑ ξ ∈ T, ‖u (Multiplicative.ofAdd (principalℚ ξ * g).val)‖
      ≤ ∑ _ξ ∈ T, (1 : ℝ) := Finset.sum_le_sum fun ξ _ ↦ hbound _
    _ = T.card := by simp
    _ ≤ (Finset.Icc a b).card := hcard
    _ ≤ 2 + t⁻¹ := by
      rw [Int.card_Icc]
      have hb : (b : ℝ) ≤ ((k : ℝ) + 1 + 1 / 4) / t := Int.floor_le _
      have ha : ((k : ℝ) + 1 - 1 / 4) / t ≤ a := Int.le_ceil _
      have hdiff : ((k : ℝ) + 1 + 1 / 4) / t - ((k : ℝ) + 1 - 1 / 4) / t = t⁻¹ / 2 := by
        field_simp
        ring
      have htinv : 0 < t⁻¹ := inv_pos.mpr hg1
      rcases le_or_gt (b + 1 - a) 0 with hle | hlt
      · rw [Int.toNat_of_nonpos hle]
        push_cast
        linarith
      · have hcast : (((b + 1 - a).toNat : ℕ) : ℝ) = (b : ℝ) + 1 - a := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hlt.le]
          push_cast
          ring
        rw [hcast]
        linarith

/-- Paper: Corollary 11.1.1.5, p. 479. Use the rational bumps from the
counterexample to Corollary 11.1.1.4 and the trivial character. Take the
unit ideal and set α(g) to 2 + 1/|g|_F on the section times the domain,
and zero elsewhere. Each orbit has one representative there, so the
majorant sum has at most one nonzero term and is Borel. It is constant on
each slice of the domain. On the norm-one slice the theta sums are
identically 1, giving averages equal to the positive Haar mass of the
domain, while the average of the zero limit vanishes. -/
theorem Printed.cond_homogeneousTheta_pointwiseConvergence_false :
    ¬ Printed.cond_homogeneousTheta_pointwiseConvergence := by
  intro H
  let : BorelSpace 𝕀[ℚ] := ⟨rfl⟩
  let : Countable ℚˣ := Units.val_injective.countable
  let : (normOneIdeleTamagawaMeasure ℚ).IsHaarMeasure :=
    (normOneIdeleTamagawaMeasure_existsUnique ℚ).exists.choose_spec.1
  have : Subsingleton (CommRing.Pic (𝓞 ℚ)) := condHT_pic
  obtain ⟨e, he⟩ := ideleNormSection_product ℚ (canonicalIdeleNormSection ℚ)
    (canonicalIdeleNormSection_continuous ℚ) (canonicalIdeleNormSection_rightInverse ℚ)
  let σ : ℂ ≃ₐ[ℝ] ℂ := AlgEquiv.refl
  let b := Units.basisModTorsion ℚ
  let rep : CommRing.Pic (𝓞 ℚ) → N[ℚ] := fun _ ↦ 1
  have hrep : ∀ c, ideleIdealClass ℚ (rep c).val = c := fun _ ↦ Subsingleton.elim _ _
  have he_norm : ∀ t h, ideleNorm ℚ (e (t, h)) = t := fun t h ↦ by
    rw [he, map_mul, canonicalIdeleNormSection_rightInverse ℚ t, MonoidHom.mem_ker.mp h.property,
      mul_one]
  have he_one : ∀ h, e (1, h) = h.val := fun h ↦ by rw [he, map_one, one_mul]
  obtain ⟨i, -, hi, -, -, -, -, -, -, -⟩ := normOne_idele_quotient ℚ
  let : Countable i.range := i.rangeRestrict_surjective.countable
  obtain ⟨hE, hD⟩ := homogeneousThetaSectionAverage_fundamentalDomain Rat.infinitePlace σ b rep
    rfl hrep i hi
  have hcpt := ideleFundamentalDomain_precompact ℚ b Rat.infinitePlace σ rep rfl hrep
  have hfinE : normOneIdeleTamagawaMeasure ℚ (ideleFundamentalDomain ℚ b Rat.infinitePlace σ rep)
      < ⊤ := (measure_mono subset_closure).trans_lt hcpt.measure_lt_top
  let : IsFiniteMeasure ((normOneIdeleTamagawaMeasure ℚ).restrict
      (ideleFundamentalDomain ℚ b Rat.infinitePlace σ rep)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfinE⟩
  obtain ⟨φ, hφ⟩ := condHT_seq b σ
  let Z := e '' ((Set.univ : Set ℝ≥0ˣ) ×ˢ ideleFundamentalDomain ℚ b Rat.infinitePlace σ rep)
  have hZm : MeasurableSet Z := measurableSet_normSection_fundamentalDomain e Rat.infinitePlace σ b rep
  have hNc : Continuous (fun g : 𝕀[ℚ] ↦ ((ideleNorm ℚ g : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (ideleGroup_topology ℚ).2.2.2.2.1)
  let α : 𝕀[ℚ] → ℝ≥0 := fun g ↦ if g ∈ Z then 2 + ((ideleNorm ℚ g⁻¹ : ℝ≥0)) else 0
  have hinvN (g : 𝕀[ℚ]) : (((ideleNorm ℚ g⁻¹ : ℝ≥0)) : ℝ) = ((ideleNorm ℚ g : ℝ≥0) : ℝ)⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hone : ((1 : ℚˣ) : ℚ) ∈ (1 : Frac[ℚ]) := by
    rw [Units.val_one]
    exact FractionalIdeal.one_mem_one _
  have horbit (g : 𝕀[ℚ]) : fractionalIdealOrbitSum 1 α g =
      if ∃ ξ : ℚˣ, (ξ : ℚ) ∈ (1 : Frac[ℚ]) ∧ principal[ℚ] ξ * g ∈ Z then
        2 + ((ideleNorm ℚ g : ℝ≥0) : ℝ)⁻¹ else 0 := by
    split_ifs with hex
    · obtain ⟨ξ₀, hξ₀, hZ₀⟩ := hex
      rw [fractionalIdealOrbitSum_eq_single 1 α g ξ₀ hξ₀ (fun ξ _ hne ↦
        ite_eq_right (fun hZ ↦ hne (condHT_Z_unique e he b σ g ξ ξ₀ hZ hZ₀)))]
      simp only [α, ite_eq_left hZ₀, NNReal.coe_add, NNReal.coe_ofNat, hinvN, condHT_norm_principal]
    · unfold fractionalIdealOrbitSum
      refine (tsum_congr fun ξ ↦ ?_).trans tsum_zero
      rw [show α (principal[ℚ] ξ.val * g) = 0 from ite_eq_right fun hZ ↦ hex ⟨ξ.val, ξ.property, hZ⟩,
        NNReal.coe_zero]
  have hmem1 (g : 𝕀[ℚ]) (hg : g ∈ Z) :
      ∃ ξ : ℚˣ, (ξ : ℚ) ∈ (1 : Frac[ℚ]) ∧ principal[ℚ] ξ * g ∈ Z :=
    ⟨1, hone, by rw [map_one, one_mul]; exact hg⟩
  have hαm : Measurable α := by
    refine Measurable.ite hZm ?_ measurable_const
    exact measurable_const.add ((Units.continuous_val.comp
      ((ideleGroup_topology ℚ).2.2.2.2.1.comp continuous_inv)).measurable)
  have hsum : ∀ g : 𝕀[ℚ], Summable (fun ξ : {ξ : ℚˣ // (ξ.val : ℚ) ∈ (1 : Frac[ℚ])} ↦
      (α (principal[ℚ] ξ.val * g) : ℝ)) := by
    intro g
    have hfin : (Function.support (fun ξ : {ξ : ℚˣ // (ξ.val : ℚ) ∈ (1 : Frac[ℚ])} ↦
        (α (principal[ℚ] ξ.val * g) : ℝ))).Finite := by
      refine Set.Subsingleton.finite ?_
      intro ξ hξ ξ' hξ'
      have hZ : principal[ℚ] ξ.val * g ∈ Z := by
        by_contra hc
        exact hξ (by simp only [α, ite_eq_right hc, NNReal.coe_zero])
      have hZ' : principal[ℚ] ξ'.val * g ∈ Z := by
        by_contra hc
        exact hξ' (by simp only [α, ite_eq_right hc, NNReal.coe_zero])
      exact Subtype.ext (condHT_Z_unique e he b σ g _ _ hZ hZ')
    exact summable_of_ne_finset_zero (s := hfin.toFinset)
      (fun x hx ↦ Function.notMem_support.mp (by simpa using hx))
  have hmeas : Measurable (fractionalIdealOrbitSum 1 α) := by
    rw [show fractionalIdealOrbitSum 1 α = _ from funext horbit]
    refine Measurable.ite ?_ (measurable_const.add (hNc.measurable.inv)) measurable_const
    rw [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun ξ ↦ ?_
    rw [Set.ofPred_and]
    exact (MeasurableSet.const _).inter (hZm.preimage (continuous_const_mul _).measurable)
  have hint : ∀ t, Integrable (fun h : N[ℚ] ↦ fractionalIdealOrbitSum 1 α (e (t, h)))
      ((normOneIdeleTamagawaMeasure ℚ).restrict
        (ideleFundamentalDomain ℚ b Rat.infinitePlace σ rep)) := by
    intro t
    refine (integrable_const (2 + ((t : ℝ≥0) : ℝ)⁻¹)).congr ?_
    refine (ae_restrict_iff' hE).mpr (Eventually.of_forall fun h hh ↦ ?_)
    change 2 + ((t : ℝ≥0) : ℝ)⁻¹ = fractionalIdealOrbitSum 1 α (e (t, h))
    rw [horbit, ite_eq_left (hmem1 _ ⟨(t, h), ⟨Set.mem_univ _, hh⟩, rfl⟩), he_norm]
  have hbound : ∀ g ∈ Z, ∀ k, (∑' ξ : ℚˣ,
      ‖φ k (Multiplicative.ofAdd (principal[ℚ] ξ * g).val)‖) ≤ fractionalIdealOrbitSum 1 α g := by
    intro g hg k
    obtain ⟨z1, -, z3⟩ := condHT_Z e he b σ g hg
    rw [horbit, ite_eq_left (hmem1 g hg), ← z1]
    have hpos : 0 < condHT_inf g.val :=
      z1 ▸ NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleNorm ℚ g).ne_zero)
    exact condHT_count (φ k) k (hφ k).1 (hφ k).2.1 g hpos z3
  have hlim : ∀ g : 𝕀[ℚ], Tendsto (fun k ↦ φ k (Multiplicative.ofAdd g.val)) atTop
      (𝓝 ((fun _ : 𝕀[ℚ] ↦ (0 : ℂ)) g)) :=
    condHT_lim φ (fun k x hx ↦ ((hφ k).1 x hx).1)
  obtain ⟨-, A, Aₖ, hA, hAk, hconv⟩ := H ℚ e Rat.infinitePlace σ b rep φ (fun _ ↦ 0) he_norm
    he_one rfl hrep hlim ⟨α, 1, hαm, hsum, hmeas, hint, hbound⟩ 1
  have h11 : e (1, 1) = 1 := by rw [he_one]; rfl
  let c : ℂ := (((normOneIdeleTamagawaMeasure ℚ).real
    (ideleFundamentalDomain ℚ b Rat.infinitePlace σ rep) : ℝ) : ℂ)
  have hA0 : A (QuotientGroup.mk' _ (classOf[ℚ] (e (1, 1)))) = 0 := by
    rw [hA]
    unfold homogeneousThetaSectionAverage ideleThetaSum
    simp only [tsum_zero, zero_mul, integral_zero]
  have hAk1 (k : ℕ) : Aₖ k (QuotientGroup.mk' _ (classOf[ℚ] (e (1, 1)))) = c := by
    rw [hAk, ← homogeneousThetaSectionAverage_schwartzBruhat e he_one Rat.infinitePlace σ b rep
      rfl hrep 1 (φ k) 1]
    unfold homogeneousThetaSectionAverage
    rw [setIntegral_congr_fun hE (g := fun _ ↦ (1 : ℂ)) ?_, setIntegral_const, Complex.real_smul,
      mul_one]
    intro h hh
    simp only [h11, one_mul, PontryaginDual.one_apply, Circle.coe_one, mul_one]
    unfold ideleThetaSum
    exact condHT_theta_E1 b σ (φ k) k (hφ k).1 h hh ((hφ k).2.2 h hh)
  have h3 := (hconv (QuotientGroup.mk' _ (classOf[ℚ] (e (1, 1))))).congr hAk1
  rw [hA0] at h3
  have hc0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds h3
  have hr0 : (normOneIdeleTamagawaMeasure ℚ).real
      (ideleFundamentalDomain ℚ b Rat.infinitePlace σ rep) = 0 := Complex.ofReal_eq_zero.mp hc0
  have hμ0 : normOneIdeleTamagawaMeasure ℚ (ideleFundamentalDomain ℚ b Rat.infinitePlace σ rep)
      = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hr0 with h | h
    · exact h
    · exact absurd h hfinE.ne
  have huniv := hD.measure_zero_of_invariant Set.univ (fun _ ↦ Set.smul_set_univ)
    (by rw [Set.univ_inter]; exact hμ0)
  exact (isOpen_univ.measure_ne_zero (normOneIdeleTamagawaMeasure ℚ) Set.univ_nonempty) huniv

end CondHomogeneousThetaFalse

end RiemannMasullo
