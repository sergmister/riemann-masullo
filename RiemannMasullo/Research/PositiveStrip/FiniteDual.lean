module
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
@[expose] public noncomputable section
open Filter Finset Set Function
open scoped Topology
namespace RiemannMasullo.StripDual
section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A continuous linear combination of one finite Jordan chain can contain a highest
nonzero coefficient only if every jet up to and including that degree is continuous.
The lowering map models precomposition with a bounded smooth coordinate multiplier. -/
private theorem stripBounded_chain (B : Submodule ℂ V) (v : ℕ → V)
    (T : V →ₗ[ℂ] V) (hT : ∀ x ∈ B, T x ∈ B) (h0 : T (v 0) = 0)
    (n : ℕ) (hS : ∀ j, j < n → T (v (j + 1)) = ((j + 1 : ℕ) : ℂ) • v j)
    (c : ℕ → ℂ) (hL : (∑ k ∈ range (n+1), c k • v k) ∈ B) (hc : c n ≠ 0) :
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
      intro j hj
      rw [map_smul, hS j (Finset.mem_range.mp hj), smul_smul]
    have hprev := ih (fun j hj ↦ hS j (by omega)) (fun j ↦ c (j+1) * (j+1 : ℕ))
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
private theorem stripBounded_terms (B : Submodule ℂ V) (v : ℕ → V)
    (T : V →ₗ[ℂ] V) (hT : ∀ x ∈ B, T x ∈ B) (h0 : T (v 0) = 0)
    (n : ℕ) (hS : ∀ j, j + 1 < n → T (v (j + 1)) = ((j + 1 : ℕ) : ℂ) • v j)
    (c : ℕ → ℂ) (hL : (∑ k ∈ range n, c k • v k) ∈ B) :
    ∀ k < n, c k ≠ 0 → v k ∈ B := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : c n = 0
    · have hprev := ih (fun j hj ↦ hS j (by omega)) (by simpa [Finset.sum_range_succ, hn] using hL)
      intro k hk hck
      have hkn : k ≠ n := fun e ↦ hck (e ▸ hn)
      exact hprev k (by omega) hck
    · exact fun k hk _ ↦ stripBounded_chain B v T hT h0 n (fun j hj ↦ hS j (by omega)) c hL hn k (by omega)

/-- A bounded finite jet combination at multiple points can only use bounded individual
jets. The cutoff multiplier selects a single frequency and its coordinate multiple
lowers the ordinary derivative jet exactly by its integer degree. -/
private theorem stripBounded_multijets {Z : Type*} [Fintype Z] [DecidableEq Z]
    (B : Submodule ℂ V) (v : Z → ℕ → V) (d : Z → ℕ)
    (P T : Z → V →ₗ[ℂ] V)
    (hP : ∀ z x, x ∈ B → P z x ∈ B) (hT : ∀ z x, x ∈ B → T z x ∈ B)
    (hcut : ∀ z w k, k < d w → P z (v w k) = if z = w then v w k else 0)
    (h0 : ∀ z, T z (v z 0) = 0)
    (hS : ∀ z k, k + 1 < d z → T z (v z (k + 1)) = ((k + 1 : ℕ) : ℂ) • v z k)
    (c : Z → ℕ → ℂ) (hL : (∑ z, ∑ k ∈ range (d z), c z k • v z k) ∈ B) :
    ∀ z k, k < d z → c z k ≠ 0 → v z k ∈ B := by
  intro z
  have hproj : P z (∑ w, ∑ k ∈ range (d w), c w k • v w k) =
      ∑ k ∈ range (d z), c z k • v z k := by
    simp only [map_sum, map_smul]
    rw [Finset.sum_eq_single z]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hcut z z k (Finset.mem_range.mp hk), ite_eq_left rfl]
    · intro w _ hw
      apply Finset.sum_eq_zero
      intro k hk
      rw [hcut z w k (Finset.mem_range.mp hk), ite_eq_right (Ne.symm hw), smul_zero]
    · simp
  exact stripBounded_terms B (v z) (T z) (hT z) (h0 z) (d z) (hS z) (c z)
    (hproj ▸ hP z _ hL)
end

abbrev Tests := ↥(schwartzBergmanSubmodule (Set.univ : Set ℝ))

theorem test_analytic (H : Tests) (w : ℂ) : AnalyticAt ℂ H.val w :=
  (differentiableOn_univ.mp (by simpa using H.property.2.1)).analyticAt w

def jet (w : ℂ) (k : ℕ) : Module.Dual ℂ Tests where
  toFun H := iteratedDeriv k H.val w
  map_add' H K := iteratedDeriv_fun_add (test_analytic H w).contDiffAt (test_analytic K w).contDiffAt
  map_smul' c H := iteratedDeriv_fun_const_smul_field c H.val

def timesTest (H : Tests) : Tests →ₗ[ℂ] Tests where
  toFun K := ⟨fun z ↦ H.val z * K.val z, by
    refine ⟨by simp, H.property.2.1.mul K.property.2.1, ?_⟩
    intro a b hab hsub n
    obtain ⟨C,hC⟩ := H.property.2.2 a b hab hsub n
    obtain ⟨D,hD⟩ := K.property.2.2 a b hab hsub 0
    refine ⟨max C 0 * max D 0, ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    change ‖z^n * (H.val z * K.val z)‖ ≤ _
    rw [← mul_assoc, norm_mul]
    apply mul_le_mul ((hC ⟨z,hz,rfl⟩).trans (le_max_left _ _)) _ (norm_nonneg _) (le_max_right _ _)
    simpa using (hD ⟨z,hz,rfl⟩).trans (le_max_left D 0)⟩
  map_add' K L := Subtype.ext (funext fun z ↦ mul_add (H.val z) (K.val z) (L.val z))
  map_smul' c K := Subtype.ext (funext fun z ↦ mul_left_comm (H.val z) c (K.val z))

private def pull (H : Tests) : Module.Dual ℂ Tests →ₗ[ℂ] Module.Dual ℂ Tests where
  toFun L := L.comp (timesTest H)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem jet_of_selector (H K : Tests) (w : ℂ) (n d : ℕ) (c : ℂ)
    (h : ∀ j ≤ n, iteratedDeriv j H.val w = if j = d then c else 0) :
    jet w n (timesTest H K) = n.choose d * c * jet w (n-d) K := by
  change iteratedDeriv n (fun z ↦ H.val z * K.val z) w = _
  rw [iteratedDeriv_fun_mul (test_analytic H w).contDiffAt (test_analytic K w).contDiffAt]
  by_cases hd : d ≤ n
  · rw [Finset.sum_eq_single d]
    · simp [h d hd, jet]
    · intro j hj hne
      simp [h j (by have := Finset.mem_range.mp hj; omega), hne]
    · simp [Finset.mem_range, show d < n+1 by omega]
  · rw [Finset.sum_eq_zero, Nat.choose_eq_zero_of_lt (lt_of_not_ge hd)]
    · simp
    · intro j hj
      have hj' : j ≤ n := by have := Finset.mem_range.mp hj; omega
      simp [h j hj', show j ≠ d by omega]

/-- In an invariant subspace of test functionals, every derivative with a
nonzero coefficient in a finite linear combination of jets of a single entire
generator belongs to the subspace. Only the jets on that finite set enter. -/
theorem schwartzBergman_finite_jet_isolation (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hGB : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖G z‖ ≤ C)
    (S : Finset ℂ) (m : S → ℕ) (hm : ∀ w, 0 < m w)
    (hord : ∀ w : S, analyticOrderAt G w.val = m w)
    (B : Submodule ℂ (Module.Dual ℂ Tests)) (hB : ∀ H L, L ∈ B → L.comp (timesTest H) ∈ B)
    (c : S → ℕ → ℂ) (hL : (∑ w, ∑ k ∈ Finset.range (m w), c w k • jet w k) ∈ B) :
    ∀ w k, k < m w → c w k ≠ 0 → jet w k ∈ B := by
  classical
  have near (w : S) (d : ℕ) : ∃ H : Tests, (∀ k < m w, iteratedDeriv k H.val w.val = if k = d then 1 else 0) ∧
      ∀ (v : S), w ≠ v → ∀ k < m v, iteratedDeriv k H.val v.val = 0 := by
    obtain ⟨H,hH,hZ⟩ := StripInterpolation.interpolate_transform hG hGB w.val (m w) (hord w)
      (fun i ↦ if i.val = d then 1 else 0)
    refine ⟨H, fun k hk ↦ hH ⟨k,hk⟩, fun v hv ↦ ?_⟩
    apply hZ v.val (fun e ↦ hv (Subtype.ext e.symm)) (m v)
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG.analyticAt v.val)).mp (hord v).ge
  choose H hH hZ using near
  apply stripBounded_multijets B (fun (w : S) ↦ jet w.val) m (fun w ↦ pull (H w 0)) (fun w ↦ pull (H w 1))
    (fun w L h ↦ hB _ L h) (fun w L h ↦ hB _ L h) _ _ _ c hL
  · intro w v k hk
    ext K
    by_cases e : w = v
    · subst v
      rw [ite_eq_left rfl]
      exact (jet_of_selector _ K w.val k 0 1 (fun j hj ↦ hH w 0 j (hj.trans_lt hk))).trans (by simp)
    · rw [ite_eq_right e]
      exact (jet_of_selector _ K v.val k 0 0 (fun j hj ↦ by simpa using hZ w 0 v e j (hj.trans_lt hk))).trans (by simp)
  · intro w
    ext K
    exact (jet_of_selector _ K w.val 0 1 1 (fun j hj ↦ hH w 1 j (hj.trans_lt (hm w)))).trans (by simp)
  · intro w k hk
    ext K
    exact (jet_of_selector _ K w.val (k+1) 1 1 (fun j hj ↦ hH w 1 j (hj.trans_lt hk))).trans (by simp)


section Synthesis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Finite analytic divisors and a strongly convergent multiplier family detect
the closure using precisely the bounded Taylor functionals annihilating the
whole test ideal. The exceptional finite sets can contain excess generator zeros. -/
theorem analytic_strip_synthesis
    (N : Submodule ℂ E) (hN : IsClosed (N : Set E)) (i : Tests →ₗ[ℂ] E) (hi : DenseRange i)
    (P : Submodule ℂ Tests) (hP : ∀ (H p : Tests), p ∈ P → timesTest H p ∈ P)
    (act : ∀ H : Tests, ∃ T : E →L[ℂ] E, ∀ p, T (i p) = i (timesTest H p))
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hGB : ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖G z‖ ≤ C)
    {ι : Type*} (l : Filter ι) [l.NeBot] (U : ι → E →L[ℂ] E) (hlim : ∀ y, Tendsto (fun n ↦ U n y) l (𝓝 y))
    (S : ι → Finset ℂ) (m : (n : ι) → S n → ℕ) (hm : ∀ n w, 0 < m n w)
    (horder : ∀ n w, analyticOrderAt G w.val = m n w)
    (hideal : ∀ n p, (∀ (w : S n) k, k < m n w → iteratedDeriv k p.val w.val = 0) → U n (i p) ∈ N)
    (hcompat : ∀ n p, p ∈ P → U n (i p) ∈ N)
    (y : E) (hy : ∀ (w : ℂ) (k : ℕ) (L : StrongDual ℂ E),
      (∀ p, L (i p) = iteratedDeriv k p.val w) → (∀ p ∈ P, iteratedDeriv k p.val w = 0) → L y = 0) :
    y ∈ N := by
  classical
  let R : StrongDual ℂ E →ₗ[ℂ] Module.Dual ℂ Tests :=
    { toFun L := L.toLinearMap.comp i, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have hR : Injective R := by
    intro L K e
    apply DFunLike.coe_injective
    refine hi.equalizer L.continuous K.continuous ?_
    funext p
    exact LinearMap.congr_fun e p
  let B := R.range ⊓ P.dualAnnihilator
  have stable (H : Tests) (f : Module.Dual ℂ Tests) (hf : f ∈ B) : f.comp (timesTest H) ∈ B := by
    obtain ⟨T,hT⟩ := act H
    obtain ⟨L,rfl⟩ := hf.1
    constructor
    · exact ⟨L.comp T, LinearMap.ext (fun p ↦ congrArg L (hT p))⟩
    · exact (Submodule.mem_dualAnnihilator _).mpr fun p hp ↦
        (Submodule.mem_dualAnnihilator _).mp hf.2 _ (hP H p hp)
  apply hN.mem_of_tendsto (hlim y)
  refine Eventually.of_forall fun n ↦ ?_
  by_contra hn
  let : IsClosed (N : Set E) := hN
  have hq : N.mkQ (U n y) ≠ 0 := fun h ↦ hn ((Submodule.Quotient.mk_eq_zero N).mp h)
  obtain ⟨g,hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hq
  let L := (g.comp N.mkQL).comp (U n)
  have hkill (x : E) (hx : x ∈ N) : g (N.mkQ x) = 0 :=
    (congrArg g ((Submodule.Quotient.mk_eq_zero N).mpr hx)).trans g.map_zero
  let J := (w : S n) × Fin (m n w)
  let D (j : J) := jet j.1.val j.2.val
  have hk : (⨅ j, LinearMap.ker (D j)) ≤ (R L).ker := by
    intro p hp
    exact hkill _ (hideal n p fun w k hk ↦ (Submodule.mem_iInf _).mp hp ⟨w,⟨k,hk⟩⟩)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (mem_span_of_iInf_ker_le_ker (L := D) hk)
  have hmem : R L ∈ B := ⟨⟨L,rfl⟩, (Submodule.mem_dualAnnihilator _).mpr fun p hp ↦ hkill _ (hcompat n p hp)⟩
  let b (w : S n) (k : ℕ) := if h : k < m n w then c ⟨w,⟨k,h⟩⟩ else 0
  have hsum : ∑ w, ∑ k ∈ Finset.range (m n w), b w k • jet w.val k = ∑ j, c j • D j := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Fin.sum_univ_eq_sum_range (fun k ↦ b w k • jet w.val k)]
    apply Finset.sum_congr rfl
    intro k _
    simp [b,D,k.isLt]
  have hsep := schwartzBergman_finite_jet_isolation G hG hGB (S n) (m n) (hm n) (horder n) B stable b
    ((hsum.trans hc).symm ▸ hmem)
  have hterms (j : J) : ∃ K : StrongDual ℂ E, c j • R K = c j • D j ∧ K y = 0 := by
    by_cases hj : c j = 0
    · exact ⟨0, by simp [hj], by simp⟩
    · have hjet := hsep j.1 j.2 j.2.isLt (by simpa [b,j.2.isLt] using hj)
      obtain ⟨K,hK⟩ := hjet.1
      exact ⟨K, congrArg (c j • ·) hK, hy j.1.val j.2.val K (LinearMap.congr_fun hK)
        ((Submodule.mem_dualAnnihilator _).mp hjet.2)⟩
  choose K hK hz using hterms
  have heq : ∑ j, c j • K j = L := by
    apply hR
    simpa only [map_sum, map_smul, hK] using hc
  apply hg
  change L y = 0
  rw [← heq]
  simp [hz]

end Synthesis

end RiemannMasullo.StripDual
