module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Norm closure of Schwartz functions with prescribed finite jets

A dense Schwartz chart can impose any finite number of Taylor coefficients on compact
frequency intervals. Point-localizing multipliers isolate individual frequencies, and
multiplication by a local coordinate successively lowers the derivative order. This
identifies which finite sums of Taylor coefficients extend to the ambient normed space.
-/

@[expose] public noncomputable section
open Finset Set Function
namespace RiemannMasullo
section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A continuous linear combination of one finite Jordan chain can contain a highest
nonzero coefficient only if every jet up to and including that degree is continuous.
The lowering map models precomposition with a bounded smooth coordinate multiplier. -/
private theorem lineProfile_bounded_chain (B : Submodule ℂ V) (v : ℕ → V)
    (T : V →ₗ[ℂ] V) (hT : ∀ x ∈ B, T x ∈ B) (h0 : T (v 0) = 0)
    (hS : ∀ j, T (v (j + 1)) = ((j + 1 : ℕ) : ℂ) • v j)
    (n : ℕ) (c : ℕ → ℂ) (hL : (∑ k ∈ range (n+1), c k • v k) ∈ B) (hc : c n ≠ 0) :
    ∀ k ≤ n, v k ∈ B := by
  have hcancel {d : ℂ} {x : V} (hd : d ≠ 0) (h : d • x ∈ B) : x ∈ B := by
    simpa [smul_smul, hd] using B.smul_mem d⁻¹ h
  induction n generalizing c with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    exact hcancel hc (by simpa using hL)
  | succ n ih =>
    have drop : T (∑ k ∈ range (n + 1 + 1), c k • v k) =
        ∑ j ∈ range (n+1), (c (j+1) * (j+1 : ℕ)) • v j := by
      rw [Finset.sum_range_succ', map_add, map_sum, map_smul, h0, smul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, hS, smul_smul]
    have hprev := ih (fun j ↦ c (j+1) * (j+1 : ℕ))
      (drop ▸ hT _ hL) (mul_ne_zero hc (by exact_mod_cast Nat.succ_ne_zero n))
    intro k hk
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · exact hprev k (by omega)
    · apply hcancel hc
      have hlo : (∑ j ∈ Finset.range (n + 1), c j • v j) ∈ B :=
        B.sum_mem fun j hj ↦ B.smul_mem (c j) (hprev j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      simpa only [Finset.sum_range_succ (f := fun j ↦ c j • v j) (n := n+1),
        add_sub_cancel_left] using B.sub_mem hL hlo

/-- Vanishing higher coefficients do not affect the separation of the supported terms. -/
private theorem lineProfile_bounded_terms (B : Submodule ℂ V) (v : ℕ → V)
    (T : V →ₗ[ℂ] V) (hT : ∀ x ∈ B, T x ∈ B) (h0 : T (v 0) = 0)
    (hS : ∀ j, T (v (j + 1)) = ((j + 1 : ℕ) : ℂ) • v j)
    (n : ℕ) (c : ℕ → ℂ) (hL : (∑ k ∈ range n, c k • v k) ∈ B) :
    ∀ k < n, c k ≠ 0 → v k ∈ B := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : c n = 0
    · have hprev := ih (by simpa [Finset.sum_range_succ, hn] using hL)
      intro k hk hck
      have hkn : k ≠ n := fun e ↦ hck (e ▸ hn)
      exact hprev k (by omega) hck
    · exact fun k hk _ ↦ lineProfile_bounded_chain B v T hT h0 hS n c hL hn k (by omega)

/-- A bounded finite jet combination at multiple points can only use bounded individual
jets. The cutoff multiplier selects a single frequency and its coordinate multiple
lowers the ordinary derivative jet exactly by its integer degree. -/
private theorem lineProfile_bounded_multijets {Z : Type*} [Fintype Z] [DecidableEq Z]
    (B : Submodule ℂ V) (v : Z → ℕ → V) (d : Z → ℕ)
    (P T : Z → V →ₗ[ℂ] V)
    (hP : ∀ z x, x ∈ B → P z x ∈ B) (hT : ∀ z x, x ∈ B → T z x ∈ B)
    (hcut : ∀ z w k, P z (v w k) = if z = w then v w k else 0)
    (h0 : ∀ z, T z (v z 0) = 0)
    (hS : ∀ z k, T z (v z (k + 1)) = ((k + 1 : ℕ) : ℂ) • v z k)
    (c : Z → ℕ → ℂ) (hL : (∑ z, ∑ k ∈ range (d z), c z k • v z k) ∈ B) :
    ∀ z k, k < d z → c z k ≠ 0 → v z k ∈ B := by
  intro z
  have hproj : P z (∑ w, ∑ k ∈ range (d w), c w k • v w k) =
      ∑ k ∈ range (d z), c z k • v z k := by
    simp only [map_sum, map_smul, hcut]
    rw [Finset.sum_eq_single z]
    · simp
    · intro w _ hw
      simp [Ne.symm hw]
    · simp
  exact lineProfile_bounded_terms B (v z) (T z) (hT z) (h0 z) (hS z) (d z) (c z)
    (hproj ▸ hP z _ hL)
end

section FiniteJetClosure
variable {X E J : Type*} [AddCommGroup X] [Module ℂ X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype J]

/-- On a dense space of tests, if a bounded finite combination of unrestricted
jet evaluations uses only bounded individual jets, the closure of their common
test kernel is precisely the common kernel of those jets that extend continuously. -/
private theorem lineProfile_finite_jet_closure (i : X →ₗ[ℂ] E) (hi : DenseRange i)
    (D : J → X →ₗ[ℂ] ℂ)
    (hterms : ∀ (c : J → ℂ) (Λ : StrongDual ℂ E),
      (∑ j, c j • D j) = Λ.toLinearMap.comp i → ∀ j, c j ≠ 0 →
        ∃ L : StrongDual ℂ E, L.toLinearMap.comp i = D j)
    (y : E) :
    y ∈ (((⨅ j, LinearMap.ker (D j)).map i).topologicalClosure) ↔
      ∀ j (L : StrongDual ℂ E), L.toLinearMap.comp i = D j → L y = 0 := by
  let S := ⨅ j, LinearMap.ker (D j)
  let M := (S.map i).topologicalClosure
  let R : StrongDual ℂ E →ₗ[ℂ] (X →ₗ[ℂ] ℂ) := {
    toFun := fun L ↦ L.toLinearMap.comp i
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hR : Injective R := by
    intro L K h
    apply DFunLike.coe_injective
    refine hi.equalizer L.continuous K.continuous ?_
    funext x
    exact LinearMap.congr_fun h x
  constructor
  · intro hy j L hL
    have hle : S.map i ≤ L.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact (LinearMap.congr_fun hL x).trans ((Submodule.mem_iInf _).mp hx j)
    exact (S.map i).topologicalClosure_minimal hle L.isClosed_ker hy
  · intro hy
    change y ∈ M
    by_contra hn
    let : IsClosed (M : Set E) := (S.map i).isClosed_topologicalClosure
    have hq : M.mkQ y ≠ 0 := fun h ↦ hn ((Submodule.Quotient.mk_eq_zero M).mp h)
    obtain ⟨g,hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
    let Λ := g.comp M.mkQL
    have hker : S ≤ (R Λ).ker := by
      intro x hx
      have hxM : i x ∈ M := (S.map i).le_topologicalClosure (Submodule.mem_map.mpr ⟨x,hx,rfl⟩)
      exact (congrArg g ((Submodule.Quotient.mk_eq_zero M).mpr hxM)).trans g.map_zero
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (mem_span_of_iInf_ker_le_ker (L := D) hker)
    have hsel (j : J) : ∃ L : StrongDual ℂ E, c j • R L = c j • D j ∧ L y = 0 := by
      by_cases hj : c j = 0
      · exact ⟨0, by simp [hj], by simp⟩
      · obtain ⟨L,hL⟩ := hterms c Λ hc j hj
        exact ⟨L, congrArg (c j • ·) hL, hy j L hL⟩
    choose L hL hval using hsel
    have heq : ∑ j, c j • L j = Λ := by
      apply hR
      simpa only [map_sum, map_smul, hL] using hc
    apply hg
    change Λ y = 0
    rw [← heq]
    simp [hval]
end FiniteJetClosure


section SchwartzJets
open Filter
open scoped ContDiff Topology SchwartzMap

private def lineProfile_jet (a : ℝ) (k : ℕ) : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ :=
  ((TemperedDistribution.delta a).comp ((SchwartzMap.derivCLM ℂ ℂ)^k)).toLinearMap

private theorem lineProfile_jet_apply (a : ℝ) (k : ℕ) (p : 𝓢(ℝ, ℂ)) :
    lineProfile_jet a k p = iteratedDeriv k p a := by
  have hd : ⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) p) = iteratedDeriv k p := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', iteratedDeriv_succ]
      change deriv (⇑((SchwartzMap.derivCLM ℂ ℂ ^ k) p)) = _
      rw [ih]
  exact congrFun hd a

private theorem lineProfile_coordinate_jet (a : ℝ) (n : ℕ) (p : 𝓢(ℝ, ℂ)) :
    iteratedDeriv (n+1) (fun t : ℝ ↦ ((t : ℂ) - a) * p t) a =
      ((n+1 : ℕ) : ℂ) * iteratedDeriv n p a := by
  let ℓ (t : ℝ) : ℂ := (t : ℂ) - a
  have hd : deriv ℓ = fun _ ↦ 1 := by
    funext t
    exact (Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (a : ℂ) |>.deriv
  have hj (j : ℕ) : iteratedDeriv j ℓ a = if j = 1 then 1 else 0 := by
    cases j with
    | zero => simp [ℓ]
    | succ j =>
      rw [iteratedDeriv_succ', hd, iteratedDeriv_const]
      simp
  have hℓ : ContDiff ℝ (n+1 : ℕ) ℓ := Complex.ofRealCLM.contDiff.sub contDiff_const
  change iteratedDeriv (n+1) (ℓ * (p : ℝ → ℂ)) a = _
  rw [iteratedDeriv_mul hℓ.contDiffAt (p.smooth _).contDiffAt,
    Finset.sum_eq_single 1]
  · simp [hj]
  · intro j _ hj'
    simp [hj, hj']
  · simp

private def lineProfile_pullMul (h : 𝓢(ℝ, ℂ)) :
    Module.Dual ℂ 𝓢(ℝ, ℂ) →ₗ[ℂ] Module.Dual ℂ 𝓢(ℝ, ℂ) where
  toFun L := L.comp (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ)).toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every compactly supported smooth multiplier acts on Schwartz tests. When continuous
functionals in the completion are stable under these actions, their finite combinations
of actual real derivative jets cannot involve an unbounded derivative. -/
private theorem lineProfile_schwartz_bounded_multijets (I : Finset ℝ) (d : I → ℕ)
    (B : Submodule ℂ (Module.Dual ℂ 𝓢(ℝ, ℂ)))
    (hB : ∀ (h : 𝓢(ℝ, ℂ)), HasCompactSupport (h : ℝ → ℂ) → ∀ L ∈ B, lineProfile_pullMul h L ∈ B)
    (c : I → ℕ → ℂ) (hc : (∑ i, ∑ k ∈ range (d i), c i k • lineProfile_jet i k) ∈ B) :
    ∀ i k, k < d i → c i k ≠ 0 → lineProfile_jet i k ∈ B := by
  classical
  have hlocal (i : I) : ∃ b : 𝓢(ℝ, ℂ), HasCompactSupport (b : ℝ → ℂ) ∧
      (b : ℝ → ℂ) =ᶠ[𝓝 (i : ℝ)] 1 ∧ ∀ j : I, j ≠ i → (b : ℝ → ℂ) =ᶠ[𝓝 (j : ℝ)] 0 := by
    let U := (((I.erase (i : ℝ)) : Finset ℝ) : Set ℝ)ᶜ
    have hU : IsOpen U := (I.erase (i : ℝ)).finite_toSet.isClosed.isOpen_compl
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (by simp [U] : (i : ℝ) ∈ U))
    let A : ContDiffBump (i : ℝ) := ⟨r/4, r/2, by positivity, by linarith⟩
    let b (x : ℝ) := ((A x : ℝ) : ℂ)
    have hcomp : HasCompactSupport b := A.hasCompactSupport.comp_left Complex.ofReal_zero
    refine ⟨hcomp.toSchwartzMap (Complex.ofRealCLM.contDiff.comp A.contDiff), hcomp, ?_, ?_⟩
    · exact A.eventuallyEq_one.mono fun x hx ↦ by
        change (A x : ℂ) = 1
        rw [show A x = 1 from hx, Complex.ofReal_one]
    · intro j hji
      apply notMem_tsupport_iff_eventuallyEq.mp
      intro hj
      have hmem : (j : ℝ) ∈ U := by
        apply hball
        apply Metric.closedBall_subset_ball (by linarith : r/2 < r)
        rw [← A.tsupport_eq]
        exact tsupport_comp_subset Complex.ofReal_zero A hj
      exact hmem (Finset.mem_erase.mpr ⟨fun h ↦ hji (Subtype.ext h), j.property⟩)
  choose b hbc hone hoff using hlocal
  let D (i : I) (t : ℝ) := ((t : ℂ) - (i : ℝ)) * b i t
  have hD (i : I) : HasCompactSupport (D i) := (hbc i).mul_left
  let q (i : I) : 𝓢(ℝ, ℂ) := (hD i).toSchwartzMap
    ((Complex.ofRealCLM.contDiff.sub contDiff_const).mul ((b i).smooth ⊤))
  let v (i : I) := lineProfile_jet (i : ℝ)
  apply lineProfile_bounded_multijets B v d (fun i ↦ lineProfile_pullMul (b i)) (fun i ↦ lineProfile_pullMul (q i))
    (fun i ↦ hB _ (hbc i)) (fun i ↦ hB _ (hD i)) _ _ _ c hc
  · intro i j k
    by_cases h : i = j
    · subst j
      simp only [ite_true]
      apply LinearMap.ext
      intro p
      change lineProfile_jet i k (SchwartzMap.smulLeftCLM ℂ (b i : ℝ → ℂ) p) = lineProfile_jet i k p
      rw [lineProfile_jet_apply, lineProfile_jet_apply, SchwartzMap.smulLeftCLM_apply (b i).hasTemperateGrowth]
      have hfg : (fun t ↦ b i t • p t) =ᶠ[𝓝 (i : ℝ)] (p : ℝ → ℂ) := (hone i).mono fun t ht ↦ by
        change b i t • p t = p t
        rw [show b i t = 1 from ht, one_smul]
      exact hfg.iteratedDeriv_eq k
    · simp only [h, ↓reduceIte]
      apply LinearMap.ext
      intro p
      change lineProfile_jet j k (SchwartzMap.smulLeftCLM ℂ (b i : ℝ → ℂ) p) = 0
      rw [lineProfile_jet_apply, SchwartzMap.smulLeftCLM_apply (b i).hasTemperateGrowth]
      have hfg : (fun t ↦ b i t • p t) =ᶠ[𝓝 (j : ℝ)] (fun _ ↦ (0 : ℂ)) := (hoff i j (Ne.symm h)).mono fun t ht ↦ by
        change b i t • p t = 0
        rw [show b i t = 0 from ht, zero_smul]
      exact (hfg.iteratedDeriv_eq k).trans (by simp)
  · intro i
    apply LinearMap.ext
    intro p
    change lineProfile_jet i 0 (SchwartzMap.smulLeftCLM ℂ (q i : ℝ → ℂ) p) = 0
    rw [lineProfile_jet_apply, iteratedDeriv_zero, SchwartzMap.smulLeftCLM_apply_apply (q i).hasTemperateGrowth]
    change (((i : ℝ) : ℂ) - i) * b i i * p i = 0
    simp
  · intro i k
    apply LinearMap.ext
    intro p
    change lineProfile_jet i (k+1) (SchwartzMap.smulLeftCLM ℂ (q i : ℝ → ℂ) p) =
      ((k+1 : ℕ) : ℂ) * lineProfile_jet i k p
    rw [lineProfile_jet_apply, lineProfile_jet_apply, SchwartzMap.smulLeftCLM_apply (q i).hasTemperateGrowth]
    refine (?_ : _ =ᶠ[𝓝 (i : ℝ)] fun t : ℝ ↦ ((t : ℂ) - (i : ℝ)) * p t).iteratedDeriv_eq (k+1) |>.trans (lineProfile_coordinate_jet i k p)
    exact (hone i).mono fun t ht ↦ by
      change (((t : ℂ) - i) * b i t) * p t = ((t : ℂ) - i) * p t
      rw [show b i t = 1 from ht, mul_one]
end SchwartzJets

section ChartClosure
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Finite spectral synthesis on a real Schwartz frequency chart: if the chart
is dense and every smooth compact multiplier acts boundedly on the completion,
the closure of the full test jet ideal is cut out by the individually continuous
jet evaluations, including at critical Sobolev exponents. -/
private theorem lineProfile_schwartz_jet_closure (I : Finset ℝ) (d : I → ℕ)
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] E) (he : DenseRange e)
    (hact : ∀ (h : 𝓢(ℝ, ℂ)), HasCompactSupport (h : ℝ → ℂ) → ∃ T : E →L[ℂ] E,
      ∀ p : 𝓢(ℝ, ℂ), T (e p) = e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p))
    (y : E) :
    let D := fun j : (i : I) × Fin (d i) ↦ lineProfile_jet (j.1 : ℝ) (j.2 : ℕ)
    y ∈ (((⨅ j, LinearMap.ker (D j)).map e).topologicalClosure) ↔
      ∀ j (L : StrongDual ℂ E), L.toLinearMap.comp e = D j → L y = 0 := by
  intro D
  apply lineProfile_finite_jet_closure e he D _ y
  intro c Λ hc
  let R : StrongDual ℂ E →ₗ[ℂ] Module.Dual ℂ 𝓢(ℝ, ℂ) := {
    toFun := fun L ↦ L.toLinearMap.comp e
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  have hinv (h : 𝓢(ℝ, ℂ)) (hcomp : HasCompactSupport (h : ℝ → ℂ)) :
      ∀ L ∈ R.range, lineProfile_pullMul h L ∈ R.range := by
    obtain ⟨T,hT⟩ := hact h hcomp
    rintro L ⟨Φ,rfl⟩
    exact ⟨Φ.comp T, LinearMap.ext fun p ↦ congrArg Φ (hT p)⟩
  let b (i : I) (k : ℕ) := if h : k < d i then c ⟨i, ⟨k, h⟩⟩ else 0
  have hsum : ∑ i, ∑ k ∈ range (d i), b i k • lineProfile_jet (i : ℝ) k =
      ∑ j, c j • D j := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦ b i k • lineProfile_jet (i : ℝ) k)]
    apply Finset.sum_congr rfl
    intro k _
    simp [b, D, k.isLt]
  have hmem : (∑ i, ∑ k ∈ range (d i), b i k • lineProfile_jet (i : ℝ) k) ∈ R.range := ⟨Λ, (hsum.trans hc).symm⟩
  have h := lineProfile_schwartz_bounded_multijets I d R.range hinv b hmem
  rintro ⟨i,k⟩ hc'
  exact h i k k.isLt (by simpa [b, k.isLt] using hc')
end ChartClosure

section GlobalClosure
open Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Smooth compact-frequency ideal membership implies full norm approximation on
a chart with bounded compact multipliers and a strongly convergent compact
approximate unit. Only individual continuous jets survive the closure. -/
theorem schwartzMap_mem_closedSubmodule_of_vanishing_jets (m : ℝ → ℕ) (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (e : 𝓢(ℝ, ℂ) →ₗ[ℂ] E) (he : DenseRange e)
    (hact : ∀ (h : 𝓢(ℝ, ℂ)), HasCompactSupport (h : ℝ → ℂ) → ∃ T : E →L[ℂ] E,
      ∀ p : 𝓢(ℝ, ℂ), T (e p) = e (SchwartzMap.smulLeftCLM ℂ (h : ℝ → ℂ) p))
    (hfinite : ∀ K : Set ℝ, IsCompact K → {t ∈ K | 0 < m t}.Finite)
    (hcompact : ∀ p : 𝓢(ℝ, ℂ), HasCompactSupport (p : ℝ → ℂ) →
      (∀ t k, k < m t → iteratedDeriv k p t = 0) → e p ∈ S)
    (g : ℕ → 𝓢(ℝ, ℂ)) (hgc : ∀ n, HasCompactSupport (g n : ℝ → ℂ)) (T : ℕ → E →L[ℂ] E)
    (hT : ∀ n p, T n (e p) = e (SchwartzMap.smulLeftCLM ℂ (g n : ℝ → ℂ) p))
    (hlim : ∀ y, Tendsto (fun n ↦ T n y) atTop (𝓝 y)) (y : E)
    (hy : ∀ t k, k < m t → ∀ L : StrongDual ℂ E, (∀ p, L (e p) = iteratedDeriv k p t) → L y = 0) :
    y ∈ S := by
  classical
  apply hS.mem_of_tendsto (hlim y)
  refine .of_forall fun n ↦ ?_
  let I := (hfinite _ (hgc n)).toFinset
  let d (i : I) := m i
  let D (j : (i : I) × Fin (d i)) := lineProfile_jet (j.1 : ℝ) (j.2 : ℕ)
  let J := ⨅ j, LinearMap.ker (D j)
  have hyJ : y ∈ (J.map e).topologicalClosure := (lineProfile_schwartz_jet_closure I d e he hact y).2
    (fun j L hL ↦ hy j.1 j.2 j.2.isLt L (fun p ↦
      (LinearMap.congr_fun hL p).trans (lineProfile_jet_apply _ _ p)))
  have hsub : J.map e ≤ S.comap (T n).toLinearMap := by
    rintro _ ⟨p, hp, rfl⟩
    change T n (e p) ∈ S
    rw [hT]
    let q := SchwartzMap.smulLeftCLM ℂ (g n : ℝ → ℂ) p
    have hq : (q : ℝ → ℂ) = (g n : ℝ → ℂ) * (p : ℝ → ℂ) :=
      SchwartzMap.smulLeftCLM_apply (g n).hasTemperateGrowth p
    apply hcompact q
    · rw [hq]
      exact (hgc n).mul_right
    · intro t k hk
      rw [hq]
      by_cases ht : t ∈ tsupport (g n : ℝ → ℂ)
      · have hi : t ∈ I := (hfinite _ (hgc n)).mem_toFinset.mpr ⟨ht, (Nat.zero_le k).trans_lt hk⟩
        let i : I := ⟨t, hi⟩
        have hp' (j) (hj : j < m t) : iteratedDeriv j p t = 0 :=
          (lineProfile_jet_apply t j p).symm.trans ((Submodule.mem_iInf _).mp hp ⟨i, ⟨j, hj⟩⟩)
        rw [iteratedDeriv_mul ((g n).smooth _).contDiffAt (p.smooth _).contDiffAt]
        exact Finset.sum_eq_zero fun j _ ↦ by rw [hp' _ ((Nat.sub_le _ _).trans_lt hk), mul_zero]
      · have hz : (g n : ℝ → ℂ) * (p : ℝ → ℂ) =ᶠ[𝓝 t] (fun _ ↦ (0:ℂ)) :=
          (notMem_tsupport_iff_eventuallyEq.mp ht).mono fun x hx ↦ by
            change g n x * p x = 0
            rw [show g n x = 0 from hx, zero_mul]
        exact (hz.iteratedDeriv_eq k).trans (by simp)
  exact (J.map e).topologicalClosure_minimal hsub (hS.preimage (T n).continuous) hyJ
end GlobalClosure

end RiemannMasullo
