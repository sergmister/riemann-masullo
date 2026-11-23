module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Regular

/-! # Chapter 4.3: printed properties of averaging over subsets -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter MeasureTheory Set Topology

/-- Paper: Lemma 4.3.3.7(2)–(3), p. 186. As printed: under the stated
quasi-completeness and continuity hypotheses, the Pettis average over a
relatively compact locally closed subset of nonempty interior has range the
fixed subspace and becomes idempotent after division by the mass of the subset.
The weak closure of its kernel equals the weak closure of the span of all
differences u − ρ(g)u with g in the subset. See
`existsUnique_relativelyCompactActionAverage` and ERRATA F212. -/
def Printed.relativelyCompactActionAverage_properties : Prop :=
  ∀ (G E : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [QuasiCompleteSpace ℂ E]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (ρ : G →* (E →L[ℂ] E)),
    Continuous (fun p : G × E ↦ ρ p.1 p.2) →
    ∀ (X : Set G), IsCompact (closure X) → IsLocallyClosed X → (interior X).Nonempty →
      ((∀ K : Set G, IsCompact K →
          EquicontinuousAt (fun g : K ↦ (ρ g : E → E)) 0) ∨
        ((∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
            Continuous p) ∧
          ∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
            ∀ K : Set G, IsCompact K →
              TendstoUniformlyOn (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop K)) →
      ∀ P : E →L[ℂ] E, IsPettisIsotypicAverageOn μ X ρ 1 P →
        range P = {u | ∀ g ∈ X, ρ g u = u} ∧
        (let Q : E →L[ℂ] E := (μ.real X)⁻¹ • P
         Q.comp Q = Q) ∧
        closure (toWeakSpace ℂ E '' (P.ker : Set E)) =
          closure (toWeakSpace ℂ E '' (Submodule.span ℂ
            (range fun p : X × E ↦ p.2 - ρ p.1.val p.2) : Set E))

/-- Paper: Lemma 4.3.3.7(2)–(3), p. 186. Let the circle act by multiplication
on ℂ, use probability Haar measure dθ/(2π), and let X be the open arc |θ| < π/2.
The average multiplies by 1/π and the normalized average by 2/π. The fixed
subspace and the kernel of the average are both zero. Its range and the
weakly closed span of the differences are both ℂ. -/
theorem Printed.relativelyCompactActionAverage_properties_false :
    ¬ Printed.relativelyCompactActionAverage_properties := by
  let : MeasurableSpace ℤˣ := borel ℤˣ
  let : BorelSpace ℤˣ := ⟨rfl⟩
  let : Measure.IsHaarMeasure (Measure.count : Measure ℤˣ) := {}
  let ρ : ℤˣ →* (ℂ →L[ℂ] ℂ) :=
    { toFun := fun g ↦ (g.val : ℂ) • ContinuousLinearMap.id ℂ ℂ
      map_one' := by ext; simp
      map_mul' := by intro g h; ext; simp [mul_smul, mul_comm] }
  have hcont : Continuous (fun p : ℤˣ × ℂ ↦ ρ p.1 p.2) := by
    change Continuous (fun p : ℤˣ × ℂ ↦ (p.1.val : ℂ) * p.2)
    exact ((continuous_of_discreteTopology : Continuous (fun g : ℤˣ ↦ (g.val : ℂ))).comp continuous_fst).mul continuous_snd
  have hp : IsPettisIsotypicAverageOn Measure.count {(-1 : ℤˣ)} ρ 1 (ρ (-1)) := by
    intro u
    have hm : (Measure.count : Measure ℤˣ).restrict {(-1 : ℤˣ)} = Measure.dirac (-1) := by
      rw [Measure.restrict_singleton, Measure.count_singleton, one_smul]
    rw [hm]
    have hi : Integrable (fun g : ℤˣ ↦ star ((1 : PontryaginDual ℤˣ) g : ℂ) • ρ g u) (Measure.dirac (-1)) := by
      exact integrable_dirac (by simp)
    simpa using Integrable.hasPettisIntegral hi
  intro h
  have hr := (h ℤˣ ℂ Measure.count ρ hcont {(-1 : ℤˣ)}
    (by simp) (isOpen_discrete _).isLocallyClosed (by rw [(isOpen_discrete _).interior_eq]; exact ⟨-1, by simp⟩)
    (Or.inl (fun K hK ↦ equicontinuousAt_finite.mpr (fun g ↦ (ρ g).continuous.continuousAt)))
    (ρ (-1)) hp).1
  have hm : (-1 : ℂ) ∈ Set.range (ρ (-1)) := ⟨1, by simp [ρ]⟩
  rw [hr] at hm
  have hh := hm (-1) (by simp)
  norm_num [ρ] at hh

/-- Paper: Corollary 4.3.3.8(2)–(3), p. 188. As printed: for every continuous
character ω and every relatively compact subset of nonempty interior, under
the stated quasi-completeness, bornological and sequential continuity
hypotheses, the operator representing the integrals (4.3.3.17) has range the
ω-eigenspace for X. Dividing by the Haar mass of X makes the operator idempotent,
and the weak closure of its kernel equals the weak closure of the span of
u − conj(ω(g))ρ(g)u. Only the properties of an existing average are asserted.
The Pettis condition tests its zero-extended integrands against Haar measure. See
`existsUnique_relativelyCompactActionIsotypicAverage` and ERRATA F212. -/
def Printed.relativelyCompactActionIsotypicAverage_properties : Prop :=
  ∀ (G E : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [T2Space E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [QuasiCompleteSpace ℂ E]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (ρ : G →* (E →L[ℂ] E)),
    Continuous (fun p : G × E ↦ ρ p.1 p.2) →
    ∀ (X : Set G), IsCompact (closure X) → (interior X).Nonempty →
      (∀ p : Seminorm ℂ E, (∀ B : Set E, IsVonNBounded ℂ B → BddAbove (p '' B)) →
        Continuous p) →
      (∀ (u : ℕ → E) (v : E), Tendsto u atTop (𝓝 v) →
        ∀ K : Set G, IsCompact K →
          TendstoUniformlyOn (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop K) →
      ∀ (ω : PontryaginDual G) (P : E →L[ℂ] E),
        (∀ u : E, HasPettisIntegral (.positive μ)
          (X.indicator (fun g ↦ star (ω g : ℂ) • ρ g u)) (P u)) →
        range P = {u | ∀ g ∈ X, ρ g u = (ω g : ℂ) • u} ∧
        (let Q : E →L[ℂ] E := (μ.real X)⁻¹ • P
         Q.comp Q = Q) ∧
        closure (toWeakSpace ℂ E '' (P.ker : Set E)) =
          closure (toWeakSpace ℂ E '' (Submodule.span ℂ
            (range fun p : X × E ↦ p.2 - star (ω p.1.val : ℂ) • ρ p.1.val p.2) : Set E))

/-- Paper: Corollary 4.3.3.8(2)–(3), p. 188. Take ω = 1, the circle acting on
ℂ by multiplication, probability Haar measure dθ/(2π), and the open arc |θ| < π/2.
The normalized average multiplies by 2/π. The eigenspace and the kernel are
zero, while the range and the weakly closed span of the twisted differences are ℂ. -/
theorem Printed.relativelyCompactActionIsotypicAverage_properties_false :
    ¬ Printed.relativelyCompactActionIsotypicAverage_properties := by
  let : MeasurableSpace ℤˣ := borel ℤˣ
  let : BorelSpace ℤˣ := ⟨rfl⟩
  let : Measure.IsHaarMeasure (Measure.count : Measure ℤˣ) := {}
  let ρ : ℤˣ →* (ℂ →L[ℂ] ℂ) :=
    { toFun := fun g ↦ (g.val : ℂ) • ContinuousLinearMap.id ℂ ℂ
      map_one' := by ext; simp
      map_mul' := by intro g h; ext; simp [mul_smul, mul_comm] }
  have hcont : Continuous (fun p : ℤˣ × ℂ ↦ ρ p.1 p.2) := by
    change Continuous (fun p : ℤˣ × ℂ ↦ (p.1.val : ℂ) * p.2)
    exact ((continuous_of_discreteTopology : Continuous (fun g : ℤˣ ↦ (g.val : ℂ))).comp continuous_fst).mul continuous_snd
  have hborn (p : Seminorm ℂ ℂ) : Continuous p := by
    have he : (p : ℂ → ℝ) = fun z ↦ ‖z‖ * p 1 := by
      funext z
      change p.toAddGroupSeminorm z = ‖z‖ * p.toAddGroupSeminorm 1
      simpa using p.smul' z (1 : ℂ)
    rw [he]
    fun_prop
  have hseq (u : ℕ → ℂ) (v : ℂ) (hu : Tendsto u atTop (nhds v)) (K : Set ℤˣ) :
      TendstoUniformlyOn (fun n g ↦ ρ g (u n)) (fun g ↦ ρ g v) atTop K := by
    intro d hd
    have hh : ∀ g : ℤˣ, ∀ᶠ n in atTop, (ρ g v, ρ g (u n)) ∈ d := by
      intro g
      exact (tendsto_left_nhds_uniformity.comp ((ρ g).continuous.tendsto v |>.comp hu)) hd
    filter_upwards [Filter.eventually_all.mpr hh] with n hn
    exact fun g hg ↦ hn g
  have hp (u : ℂ) : HasPettisIntegral (.positive (Measure.count : Measure ℤˣ))
      (({(-1 : ℤˣ)} : Set ℤˣ).indicator (fun g ↦ star ((1 : PontryaginDual ℤˣ) g : ℂ) • ρ g u)) (ρ (-1) u) := by
    have hi : Integrable (fun g : ℤˣ ↦ star ((1 : PontryaginDual ℤˣ) g : ℂ) • ρ g u)
        ((Measure.count : Measure ℤˣ).restrict {(-1 : ℤˣ)}) := by
      rw [Measure.restrict_singleton, Measure.count_singleton, one_smul]
      exact integrable_dirac (by simp)
    have hind := (integrable_indicator_iff (measurableSet_singleton (-1))).mpr hi
    simpa using Integrable.hasPettisIntegral hind
  intro h
  have hr := (h ℤˣ ℂ Measure.count ρ hcont {(-1 : ℤˣ)}
    (by simp) (by rw [(isOpen_discrete _).interior_eq]; exact ⟨-1, by simp⟩)
    (fun p hp ↦ hborn p) (fun u v hu K hK ↦ hseq u v hu K) 1 (ρ (-1)) hp).1
  have hm : (-1 : ℂ) ∈ Set.range (ρ (-1)) := ⟨1, by simp [ρ]⟩
  rw [hr] at hm
  have hh := hm (-1) (by simp)
  norm_num [ρ] at hh

end RiemannMasullo
