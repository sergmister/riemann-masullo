module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Finite angular support on the rational idele classes

A Bruhat function has a good group of periods. On a profinite angular group,
those periods contain an open subgroup whose annihilator is finite. The same
finite character set works on every translate of the angular group. For the
rational idele classes, the positive-real coordinate in the product
decomposition on p. 546 is trivial on the compact norm-one kernel.

These deductions separate the number of angular characters from the radial
trace-class estimate in the projective-kernel question on p. 520.
-/

@[expose] public noncomputable section
open Function Filter MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

section ProfinitePeriods

variable {G K : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [T2Space K] [TotallyDisconnectedSpace K]

section

variable [LocallyCompactSpace K]

/-- A good period subgroup contains the image of an open subgroup of a profinite source. -/
theorem IsBruhatGoodSubgroup.exists_openSubgroup_map_le {H : Subgroup G} (hH : IsBruhatGoodSubgroup H)
    (j : K →ₜ* G) : ∃ U : OpenSubgroup K, U.toSubgroup.map j.toMonoidHom ≤ H := by
  let A := lcaAnnihilator H
  let i : A →ₜ* PontryaginDual G := ⟨A.subtype, continuous_subtype_val⟩
  let E := (PontryaginDual.map i).comp ((pontryaginDual_eval (G := G)).comp j)
  obtain ⟨C, _, hC, hgen⟩ := hH.2.2
  let V : Set (PontryaginDual A) := {ψ | MapsTo ψ C (Circle.centeredArc (Real.pi / 2))}
  have hV : IsOpen V := isOpen_induced
    (ContinuousMap.isOpen_setOfPred_mapsTo hC (Circle.isOpen_centeredArc (Real.pi / 2)))
  have h1 : 1 ∈ V := by
    intro χ hχ
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨U, _, hU⟩ := exists_compact_openSubgroup_sub_mem_nhds
    (E.continuous.continuousAt.preimage_mem_nhds
      (hV.mem_nhds (show E 1 ∈ V by rwa [map_one])))
  refine ⟨U, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  rw [← lcaDualAnnihilator_annihilator H hH.1, mem_lcaDualAnnihilator_iff]
  have hkill : C ⊆ (E u).toMonoidHom.ker := by
    intro χ hχ
    apply MonoidHom.mem_ker.mpr
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    have h : E (u ^ n) χ ∈ Circle.centeredArc (Real.pi / 2) := hU (U.pow_mem hu n) hχ
    rw [map_pow] at h
    exact (ContinuousMonoidHom.pow_apply (E u) n χ) ▸ h
  have htop : ⊤ ≤ (E u).toMonoidHom.ker := hgen ▸ (Subgroup.closure_le _).mpr hkill
  exact fun χ ↦ MonoidHom.mem_ker.mp (htop (Subgroup.mem_top (x := χ)))

/-- The periods of a Bruhat function of class zero contain an open subgroup
of any locally compact totally disconnected angular group. -/
theorem IsBruhatContDiff.exists_openSubgroup_periods {φ : G → ℂ} (hφ : IsBruhatContDiff 0 φ)
    (j : K →ₜ* G) : ∃ U : OpenSubgroup K, ∀ k ∈ U, ∀ x : G, φ (j k * x) = φ x := by
  obtain ⟨H, hH, hinv, _⟩ := hφ
  obtain ⟨U, hU⟩ := hH.exists_openSubgroup_map_le j
  exact ⟨U, fun k hk ↦ hinv ⟨j k, hU ⟨k, hk, rfl⟩⟩⟩

end

variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Only finitely many angular characters contribute on all translated profinite fibers. -/
theorem IsBruhatContDiff.finite_angular_integrals {φ : G → ℂ} (hφ : IsBruhatContDiff 0 φ)
    (j : K →ₜ* G)
    (μ : Measure K) [μ.IsHaarMeasure] :
    ∃ S : Finset (PontryaginDual K), ∀ χ ∉ S, ∀ g : G,
      ∫ k : K, φ (j k * g) * (χ k : ℂ) ∂μ = 0 := by
  classical
  obtain ⟨U, hU⟩ := hφ.exists_openSubgroup_periods j
  have hS := (isCompact_lcaAnnihilator U.toSubgroup U.isOpen).finite_of_discrete
  refine ⟨hS.toFinset, ?_⟩
  intro χ hχ g
  have hn : χ ∉ lcaAnnihilator U.toSubgroup := by simpa using hχ
  obtain ⟨u, hu⟩ := not_forall.mp (mt (mem_lcaAnnihilator_iff U.toSubgroup χ).mpr hn)
  have hu' : (χ u.val : ℂ) ≠ 1 := fun h ↦ hu (Circle.ext h)
  let q : K → ℂ := fun k ↦ φ (j k * g) * (χ k : ℂ)
  have hmul (k : K) : q (u.val * k) = (χ u.val : ℂ) * q k := by
    dsimp only [q]
    rw [map_mul, mul_assoc, hU u.val u.property, map_mul, Circle.coe_mul]
    ring
  have heq := integral_mul_left_eq_self (μ := μ) q u.val
  simp_rw [hmul, integral_const_mul] at heq
  by_contra h
  exact hu' ((mul_eq_right₀ h).mp heq)

/-- A profinite compact group sees only finitely many characters in a
Schwartz–Bruhat function, uniformly over every fiber translate. -/
theorem schwartzBruhat_finite_angular_integrals (j : K →ₜ* G) (φ : SchwartzBruhat G)
    (μ : Measure K) [μ.IsHaarMeasure] :
    ∃ S : Finset (PontryaginDual K), ∀ χ ∉ S, ∀ g : G,
      ∫ k : K, φ (j k * g) * (χ k : ℂ) ∂μ = 0 :=
  (schwartzBruhat_isBruhatSmooth φ 0).finite_angular_integrals j μ

end ProfinitePeriods

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker

/-- The norm-one rational idele classes are totally disconnected. -/
theorem ratIdeleClassNormKer_totallyDisconnected : TotallyDisconnectedSpace Kℚ := by
  let U := (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ
  let (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
      TotallyDisconnectedSpace (v.adicCompletionIntegers ℚ)ˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let : TotallyDisconnectedSpace U := inferInstanceAs (TotallyDisconnectedSpace (∀ v, _))
  obtain ⟨e, _⟩ := ratIdeleClassGroup_decomposition
  let n : Cℚ →ₜ* ℝ≥0ˣ := ⟨(MonoidHom.fst ℝ≥0ˣ U).comp e.symm.toMonoidHom,
    continuous_fst.comp e.symm.continuous⟩
  have hn := compactSubgroup_le_modulation_ker n (ideleClassNorm ℚ).ker
    (isCompact_iff_compactSpace.mpr (ideleClassGroup_finiteness ℚ).2.1)
  let f : Kℚ → U := fun x ↦ (e.symm x.val).2
  have hf : Continuous f := (continuous_snd.comp e.symm.continuous).comp continuous_subtype_val
  have hi : Injective f := by
    intro x y h
    apply Subtype.ext
    apply e.symm.injective
    exact Prod.ext ((show (e.symm x.val).1 = 1 from hn x.property).trans (hn y.property).symm) h
  exact ⟨isTotallyDisconnected_of_image hf.continuousOn hi (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- A Schwartz–Bruhat convolution test on the rational idele classes involves finitely
many norm-one characters, uniformly on the positive-real fibers. -/
theorem ratSchwartzBruhat_finite_angular_integrals (φ : SchwartzBruhat Cℚ)
    (μ : Measure Kℚ) [μ.IsHaarMeasure] :
    ∃ S : Finset (PontryaginDual Kℚ), ∀ χ ∉ S, ∀ g : Cℚ,
      ∫ k : Kℚ, φ (k.val * g) * (χ k : ℂ) ∂μ = 0 := by
  let : CompactSpace Kℚ := (ideleClassGroup_finiteness ℚ).2.1
  let : TotallyDisconnectedSpace Kℚ := ratIdeleClassNormKer_totallyDisconnected
  exact schwartzBruhat_finite_angular_integrals ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ φ μ

/-- The positive-character convolution profile vanishes identically outside the same
finite set of restrictions, even when the ambient character is evaluated on the full fiber. -/
private theorem rat_finite_angular_profiles_of_bruhat {φ : Cℚ → ℂ} (hφ : IsBruhatContDiff 0 φ)
    (μ : Measure Kℚ) [μ.IsHaarMeasure] :
    ∃ S : Finset (PontryaginDual Kℚ), ∀ ψ : PontryaginDual Cℚ,
      ψ.comp ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ ∉ S → ∀ g : Cℚ,
        ∫ k : Kℚ, φ (k.val * g) * (ψ (k.val * g) : ℂ) ∂μ = 0 := by
  let : CompactSpace Kℚ := (ideleClassGroup_finiteness ℚ).2.1
  let : TotallyDisconnectedSpace Kℚ := ratIdeleClassNormKer_totallyDisconnected
  obtain ⟨S, hS⟩ := hφ.finite_angular_integrals
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Kℚ →ₜ* Cℚ) μ
  refine ⟨S, fun ψ hψ g ↦ ?_⟩
  let χ := ψ.comp (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : Kℚ →ₜ* Cℚ)
  have he (k : Kℚ) : φ (k.val * g) * (ψ (k.val * g) : ℂ) =
      (φ (k.val * g) * (χ k : ℂ)) * (ψ g : ℂ) := by
    rw [map_mul, Circle.coe_mul, ← mul_assoc]
    rfl
  calc
    _ = ∫ k : Kℚ, (φ (k.val * g) * (χ k : ℂ)) * (ψ g : ℂ) ∂μ :=
      integral_congr_ae (.of_forall he)
    _ = (∫ k : Kℚ, φ (k.val * g) * (χ k : ℂ) ∂μ) * (ψ g : ℂ) := integral_mul_const _ _
    _ = 0 := (congrArg (fun z : ℂ ↦ z * (ψ g : ℂ)) (hS χ hψ g)).trans (zero_mul _)

/-- Evaluate the full character on the fiber, with the positive sign for
the convolution action on the inverse-character radial lift. -/
theorem ratSchwartzBruhat_finite_angular_profiles (φ : SchwartzBruhat Cℚ)
    (μ : Measure Kℚ) [μ.IsHaarMeasure] :
    ∃ S : Finset (PontryaginDual Kℚ), ∀ ψ : PontryaginDual Cℚ,
      ψ.comp ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ ∉ S → ∀ g : Cℚ,
        ∫ k : Kℚ, φ (k.val * g) * (ψ (k.val * g) : ℂ) ∂μ = 0 :=
  rat_finite_angular_profiles_of_bruhat (schwartzBruhat_isBruhatSmooth φ 0) μ

/-- The same finite character support for an actual compact test of the
adelic Bruhat convolution algebra. -/
theorem ratBruhatCompactSupport_finite_angular_profiles (φ : BruhatCompactSupport Cℚ)
    (μ : Measure Kℚ) [μ.IsHaarMeasure] :
    ∃ S : Finset (PontryaginDual Kℚ), ∀ ψ : PontryaginDual Cℚ,
      ψ.comp ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ ∉ S → ∀ g : Cℚ,
        ∫ k : Kℚ, φ.val (k.val * g) * (ψ (k.val * g) : ℂ) ∂μ = 0 :=
  rat_finite_angular_profiles_of_bruhat ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 0) μ

end RiemannMasullo
