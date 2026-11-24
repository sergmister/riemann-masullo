module

public import RiemannMasullo.Research.StripNuclearity.RationalAngularSupport

/-!
# Finite angular decomposition of rational convolution

A compact Bruhat test has an open group of angular periods. Its translates
therefore factor through a finite abelian group. Finite Fourier inversion
writes the test itself as a sum of compact Bruhat tests of pure character.

For an abelian group acting continuously on a complex Banach space, the
regularized action of each summand has range in the corresponding isotype
and vanishes on every other one. The rational Hardy–Sobolev action in §9.3,
p. 419, satisfies these hypotheses. This finite decomposition supplies the
angular part of the projective-kernel question at (12.5.1.4), p. 520.
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

section FiniteAngularBlocks

variable {G K : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]

private theorem compact_test_translate (φ : BruhatCompactSupport G) (g : G) :
    ∃ ψ : BruhatCompactSupport G, ∀ x, ψ.val x = φ.val (g * x) := by
  obtain ⟨f, hf, _⟩ := bruhatFirstOrder_translate (1 : LCATopologicalLie G)
    (⟨φ.val, φ.property.1⟩ : bruhatSmoothSubmodule (G := G)) g⁻¹
  have hfun : f.val = fun x ↦ φ.val (g * x) := funext fun x ↦ by simpa using hf x
  exact ⟨⟨f.val, f.property, hfun ▸ φ.property.2.comp_homeomorph (Homeomorph.mulLeft g)⟩, congrFun hfun⟩

/-- Orthogonality of the full character group at a point of a finite abelian group. -/
private theorem finite_dual_character_sum {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    [DiscreteTopology Q] [Finite Q] (q : Q) [DecidableEq Q] :
    ∑ χ : PontryaginDual Q, (χ q : ℂ) =
      if q = 1 then (Fintype.card (PontryaginDual Q) : ℂ) else 0 := by
  classical
  by_cases hq : q = 1
  · simp [hq]
  simp only [hq, ↓reduceIte]
  obtain ⟨η, hη⟩ : ∃ η : PontryaginDual Q, η q ≠ 1 := by
    by_contra! h
    apply hq
    apply (pontryaginDual_pairing_separates (G := Q)).1
    exact funext fun χ ↦ (h χ).trans (map_one χ).symm
  let b : ℂ := ∑ χ : PontryaginDual Q, (χ q : ℂ)
  have h : (η q : ℂ) * b = b := by
    dsimp only [b]
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft η) _ _ (fun χ ↦ rfl)
  by_contra hb
  exact hη (Circle.ext ((mul_eq_right₀ hb).mp h))

/-- An angular period subgroup lets the translation orbit descend to the quotient. -/
private theorem compact_test_quotient_family (j : K →ₜ* G) (φ : BruhatCompactSupport G)
    (U : OpenSubgroup K) (hU : ∀ k ∈ U, ∀ x : G, φ.val (j k * x) = φ.val x) :
    ∃ A : K ⧸ U.toSubgroup → BruhatCompactSupport G,
      ∀ (k : K) x, (A (QuotientGroup.mk k)).val x = φ.val (j k * x) := by
  classical
  let Q := K ⧸ U.toSubgroup
  choose F hF using compact_test_translate φ
  let A (q : Q) := F (j q.out)
  refine ⟨A, fun k x ↦ (hF _ _).trans ?_⟩
  have he : (QuotientGroup.mk (QuotientGroup.mk k : Q).out : Q) = QuotientGroup.mk k := Quotient.out_eq _
  have hmem := QuotientGroup.eq.mp he
  have hp := hU _ hmem (j (QuotientGroup.mk k : Q).out * x)
  simp only [map_mul, map_inv] at hp
  refine hp.symm.trans (congrArg φ.val ?_)
  calc
    _ = (j (QuotientGroup.mk k : Q).out)⁻¹ * (j (QuotientGroup.mk k : Q).out * (j k * x)) := by ac_rfl
    _ = _ := inv_mul_cancel_left _ _

/-- Apply the finite Fourier transform to the translation orbit, in the space of compact tests. -/
private theorem compact_test_finite_angular_parts (j : K →ₜ* G) (φ : BruhatCompactSupport G)
    (U : OpenSubgroup K) (hU : ∀ k ∈ U, ∀ x : G, φ.val (j k * x) = φ.val x) :
    let Q := K ⧸ U.toSubgroup
    let _ : DiscreteTopology Q := QuotientGroup.discreteTopology U.isOpen
    ∃ F : PontryaginDual Q → BruhatCompactSupport G, (∑ χ, F χ) = φ ∧
      ∀ χ (k : K) x, (F χ).val ((j k)⁻¹ * x) = (χ (QuotientGroup.mk k) : ℂ) * (F χ).val x := by
  classical
  let Q := K ⧸ U.toSubgroup
  let : DiscreteTopology Q := QuotientGroup.discreteTopology U.isOpen
  let : Fintype Q := Fintype.ofFinite _
  obtain ⟨A, hA⟩ := compact_test_quotient_family j φ U hU
  let d : ℂ := Fintype.card (PontryaginDual Q)
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let F (χ : PontryaginDual Q) : BruhatCompactSupport G := d⁻¹ • ∑ q : Q, (χ q : ℂ) • A q
  let ev (x : G) : BruhatCompactSupport G →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : G ↦ ℂ) x).comp (bruhatCompactSupportSubmodule G).subtype
  have hF (χ : PontryaginDual Q) (x : G) : (F χ).val x = d⁻¹ * ∑ q : Q, (χ q : ℂ) * (A q).val x := by
    change ev x (d⁻¹ • ∑ q : Q, (χ q : ℂ) • A q) = _
    simp only [map_smul, map_sum, smul_eq_mul]
    rfl
  have hAshift (q : Q) (k : K) (x : G) :
      (A q).val ((j k)⁻¹ * x) = (A (q * (QuotientGroup.mk k : Q)⁻¹)).val x := by
    induction q using QuotientGroup.induction_on with
    | H q =>
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hA, hA, map_mul, map_inv, mul_assoc]
  refine ⟨F, ?_, ?_⟩
  · apply Subtype.ext
    funext x
    change ev x (∑ χ, F χ) = φ.val x
    rw [map_sum]
    change (∑ χ : PontryaginDual Q, (F χ).val x) = _
    simp_rw [hF]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.sum_mul, finite_dual_character_sum]
    have h1 : (A (1 : Q)).val x = φ.val x := by simpa using hA 1 x
    simp [h1, d, Fintype.card_ne_zero]
  · intro χ k x
    rw [hF, hF]
    let v : Q := QuotientGroup.mk k
    have hshift : ∑ q : Q, (χ q : ℂ) * (A q).val ((j k)⁻¹ * x) =
        ∑ r : Q, ((χ (r * v) : Circle) : ℂ) * (A r).val x := by
      refine Fintype.sum_equiv (Equiv.mulRight v⁻¹) _ _ (fun q ↦ ?_)
      change (χ q : ℂ) * _ = (χ ((q * v⁻¹) * v) : ℂ) * _
      rw [inv_mul_cancel_right, hAshift]
      rfl
    rw [hshift]
    change d⁻¹ * (∑ r : Q, (χ (r * v) : ℂ) * (A r).val x) =
      (χ v : ℂ) * (d⁻¹ * ∑ r : Q, (χ r : ℂ) * (A r).val x)
    have hv : (∑ r : Q, (χ (r * v) : ℂ) * (A r).val x) =
        (χ v : ℂ) * ∑ r : Q, (χ r : ℂ) * (A r).val x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [map_mul, Circle.coe_mul]
      ring
    rw [hv]
    ring

/-- A compact Bruhat test decomposes into finitely many compact Bruhat tests of pure
angular character for any profinite group of translations. -/
theorem bruhatCompactSupport_finite_angular_decomposition (j : K →ₜ* G)
    (φ : BruhatCompactSupport G) :
    ∃ (S : Finset (PontryaginDual K)) (P : PontryaginDual K → BruhatCompactSupport G),
      (∑ χ ∈ S, P χ) = φ ∧
      ∀ χ ∈ S, ∀ (k : K) (x : G), (P χ).val ((j k)⁻¹ * x) = (χ k : ℂ) * (P χ).val x := by
  classical
  have hφ : IsBruhatContDiff 0 φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 0
  obtain ⟨U, hU⟩ := hφ.exists_openSubgroup_periods j
  let Q := K ⧸ U.toSubgroup
  let : DiscreteTopology Q := QuotientGroup.discreteTopology U.isOpen
  obtain ⟨F, hsum, hcov⟩ := compact_test_finite_angular_parts j φ U hU
  let q : K →ₜ* Q := ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  let r (χ : PontryaginDual Q) : PontryaginDual K := χ.comp q
  have hr : Injective r := by
    intro ψ χ h
    ext t
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t
    exact congrArg (fun θ : PontryaginDual K ↦ (θ k : ℂ)) h
  let emb : PontryaginDual Q ↪ PontryaginDual K := ⟨r, hr⟩
  let P (χ : PontryaginDual K) : BruhatCompactSupport G :=
    if h : χ ∈ range r then F (Classical.choose h) else 0
  have hP (χ : PontryaginDual Q) : P (r χ) = F χ := by
    have hh : r χ ∈ range r := mem_range_self χ
    simp only [P, hh, ↓reduceDIte]
    exact congrArg F (hr (Classical.choose_spec hh))
  refine ⟨Finset.univ.map emb, P, ?_, ?_⟩
  · rw [Finset.sum_map]
    change (∑ χ : PontryaginDual Q, P (r χ)) = φ
    simpa only [hP] using hsum
  · intro χ hχ k x
    obtain ⟨ψ, _, rfl⟩ := Finset.mem_map.mp hχ
    change (P (r ψ)).val ((j k)⁻¹ * x) = ((r ψ) k : ℂ) * (P (r ψ)).val x
    rw [hP]
    exact hcov ψ k x

end FiniteAngularBlocks

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker

/-- Each rational convolution test is a finite sum of compact tests transforming
under specified characters of the norm-one idele classes. -/
theorem ratBruhatCompactSupport_finite_angular_decomposition (φ : BruhatCompactSupport Cℚ) :
    ∃ (S : Finset (PontryaginDual Kℚ)) (P : PontryaginDual Kℚ → BruhatCompactSupport Cℚ),
      (∑ χ ∈ S, P χ) = φ ∧
      ∀ χ ∈ S, ∀ (k : Kℚ) (x : Cℚ), (P χ).val (k.val⁻¹ * x) = (χ k : ℂ) * (P χ).val x := by
  let : CompactSpace Kℚ := (ideleClassGroup_finiteness ℚ).2.1
  let : TotallyDisconnectedSpace Kℚ := ratIdeleClassNormKer_totallyDisconnected
  exact bruhatCompactSupport_finite_angular_decomposition
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Kℚ →ₜ* Cℚ) φ

section RegularizedAction

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (μ : Measure G) [μ.IsHaarMeasure] (τ : G →* (E →L[ℂ] E))
  (hτ : Continuous (fun p : G × E ↦ τ p.1 p.2))

private theorem compact_test_orbit_integral (φ : BruhatCompactSupport G) (u : E) :
    Integrable (fun g ↦ φ.val g • τ g u) μ ∧
      bruhatRegularizedAction μ τ hτ φ u = ∫ g, φ.val g • τ g u ∂μ := by
  have hc : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have horbit : Continuous (fun g : G ↦ τ g u) := hτ.comp (Continuous.prodMk_left u)
  have hi : Integrable (fun g : G ↦ φ.val g • τ g u) μ :=
    (hc.smul horbit).integrable_of_hasCompactSupport φ.property.2.smul_right
  exact ⟨hi, (bruhatRegularizedAction_apply μ τ hτ φ u).unique (Integrable.hasPettisIntegral hi)⟩

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
  [CompactSpace K] [TotallyDisconnectedSpace K] (j : K →ₜ* G)

private theorem compact_test_isotype_range {χ : PontryaginDual K} (φ : BruhatCompactSupport G)
    (hφ : ∀ (k : K) (x : G), φ.val ((j k)⁻¹ * x) = (χ k : ℂ) * φ.val x) :
    ∀ u, bruhatRegularizedAction μ τ hτ φ u ∈ actionIsotype (τ.comp j.toMonoidHom) χ := by
  intro u
  rw [mem_actionIsotype]
  intro k
  obtain ⟨hi, he⟩ := compact_test_orbit_integral μ τ hτ φ u
  change τ (j k) (bruhatRegularizedAction μ τ hτ φ u) = (χ k : ℂ) • bruhatRegularizedAction μ τ hτ φ u
  rw [he, ← (τ (j k)).integral_comp_comm hi, ← integral_smul]
  calc
    _ = ∫ g : G, φ.val g • τ (j k * g) u ∂μ := by
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [map_smul, map_mul]
      rfl
    _ = ∫ g : G, φ.val ((j k)⁻¹ * g) • τ g u ∂μ := by
      rw [← integral_mul_left_eq_self (fun g : G ↦ φ.val ((j k)⁻¹ * g) • τ g u) (j k)]
      exact integral_congr_ae (.of_forall fun g ↦ by simp)
    _ = _ := integral_congr_ae (.of_forall fun g ↦ by
      change φ.val ((j k)⁻¹ * g) • τ g u = (χ k : ℂ) • (φ.val g • τ g u)
      rw [hφ, mul_smul])

private theorem compact_test_preserves_isotype (φ : BruhatCompactSupport G) (χ : PontryaginDual K)
    {u : E} (hu : u ∈ actionIsotype (τ.comp j.toMonoidHom) χ) :
    bruhatRegularizedAction μ τ hτ φ u ∈ actionIsotype (τ.comp j.toMonoidHom) χ := by
  rw [mem_actionIsotype] at hu ⊢
  intro k
  obtain ⟨hi, he⟩ := compact_test_orbit_integral μ τ hτ φ u
  change τ (j k) (bruhatRegularizedAction μ τ hτ φ u) = (χ k : ℂ) • bruhatRegularizedAction μ τ hτ φ u
  rw [he, ← (τ (j k)).integral_comp_comm hi, ← integral_smul]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  have hcomm : τ (j k) (τ g u) = τ g (τ (j k) u) := by
    change (τ (j k) * τ g) u = (τ g * τ (j k)) u
    rw [← τ.map_mul, ← τ.map_mul, mul_comm]
  have hk : τ (j k) u = (χ k : ℂ) • u := hu k
  rw [map_smul, hcomm, hk, map_smul, smul_comm]

/-- A regularized representation of an abelian group decomposes over a compact
totally disconnected group of translations into finitely many isotype operators.
Each summand has range in its own isotype and kills every other isotype. -/
theorem bruhatRegularizedAction_finite_angular_blocks (φ : BruhatCompactSupport G) :
    let A := bruhatRegularizedAction μ τ hτ
    let ρ := τ.comp j.toMonoidHom
    ∃ (S : Finset (PontryaginDual K)) (P : PontryaginDual K → BruhatCompactSupport G),
      (∑ χ ∈ S, P χ) = φ ∧ A φ = ∑ χ ∈ S, A (P χ) ∧
      ∀ χ ∈ S, (∀ u, A (P χ) u ∈ actionIsotype ρ χ) ∧
        ∀ η ≠ χ, ∀ u ∈ actionIsotype ρ η, A (P χ) u = 0 := by
  classical
  dsimp only
  obtain ⟨S, P, hsum, hcov⟩ := bruhatCompactSupport_finite_angular_decomposition j φ
  refine ⟨S, P, hsum, ?_, ?_⟩
  · rw [← hsum, map_sum]
  · intro χ hχ
    have hc := compact_test_isotype_range μ τ hτ j (P χ) (hcov χ hχ)
    refine ⟨hc, ?_⟩
    intro η hη u hu
    have hηrange := compact_test_preserves_isotype μ τ hτ j (P χ) η hu
    by_contra hn
    apply hη
    ext k
    exact smul_left_injective ℂ hn
      (((mem_actionIsotype _ _ _).mp hηrange k).symm.trans ((mem_actionIsotype _ _ _).mp (hc u) k))

/-- The regularized action annihilates all isotypes outside one finite set. -/
theorem bruhatRegularizedAction_zero_off_finite_isotypes (φ : BruhatCompactSupport G) :
    ∃ S : Finset (PontryaginDual K), ∀ η ∉ S, ∀ u ∈ actionIsotype (τ.comp j.toMonoidHom) η,
      bruhatRegularizedAction μ τ hτ φ u = 0 := by
  classical
  obtain ⟨S, P, _, hsum, hblocks⟩ := bruhatRegularizedAction_finite_angular_blocks μ τ hτ j φ
  refine ⟨S, fun η hη u hu ↦ ?_⟩
  rw [hsum, sum_apply]
  exact Finset.sum_eq_zero fun χ hχ ↦ (hblocks χ hχ).2 η (fun he ↦ hη (he ▸ hχ)) u hu

end RegularizedAction

local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "mℚ" =>
  (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "jℚ" =>
  (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Kℚ →ₜ* Cℚ)

/-- On the ambient rational Hardy–Sobolev space, compact convolution is a finite
sum of norm-one character blocks, each with its indicated range and kernel. -/
theorem ratHardySobolevTestAction_finite_angular_blocks {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport Cℚ) :
    let τ := hardySobolevTranslation μℚ mℚ l r s hI hs
    let ρ := τ.comp (ideleClassNorm ℚ).ker.subtype
    let A := hardySobolevTestAction μℚ mℚ l r s hI hs
    ∃ (S : Finset (PontryaginDual Kℚ)) (P : PontryaginDual Kℚ → BruhatCompactSupport Cℚ),
      (∑ χ ∈ S, P χ) = φ ∧ A φ = ∑ χ ∈ S, A (P χ) ∧
      ∀ χ ∈ S, (∀ u, A (P χ) u ∈ actionIsotype ρ χ) ∧
        ∀ η ≠ χ, ∀ u ∈ actionIsotype ρ η, A (P χ) u = 0 := by
  let : CompactSpace Kℚ := (ideleClassGroup_finiteness ℚ).2.1
  let : TotallyDisconnectedSpace Kℚ := ratIdeleClassNormKer_totallyDisconnected
  exact bruhatRegularizedAction_finite_angular_blocks μℚ (hardySobolevTranslation μℚ mℚ l r s hI hs)
    (exists_hardySobolevTranslation μℚ mℚ l r s hI hs).choose_spec.2 jℚ φ

/-- The rational Hardy–Sobolev convolution kills all norm-one character
isotypes outside one finite set, for every compact interval and every nonnegative order. -/
theorem ratHardySobolevTestAction_zero_off_finite_isotypes {l r s : ℝ} (hI : l ≤ r) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport Cℚ) :
    let τ := hardySobolevTranslation μℚ mℚ l r s hI hs
    let A := hardySobolevTestAction μℚ mℚ l r s hI hs
    ∃ S : Finset (PontryaginDual Kℚ), ∀ η ∉ S, ∀ u ∈ actionIsotype (τ.comp (ideleClassNorm ℚ).ker.subtype) η,
      A φ u = 0 := by
  let : CompactSpace Kℚ := (ideleClassGroup_finiteness ℚ).2.1
  let : TotallyDisconnectedSpace Kℚ := ratIdeleClassNormKer_totallyDisconnected
  exact bruhatRegularizedAction_zero_off_finite_isotypes μℚ (hardySobolevTranslation μℚ mℚ l r s hI hs)
    (exists_hardySobolevTranslation μℚ mℚ l r s hI hs).choose_spec.2 jℚ φ

end RiemannMasullo
