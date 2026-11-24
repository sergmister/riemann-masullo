module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero

/-! # False assertions in §10.4.3 -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "logNorm(" F ")" => (logIdeleClassNorm F)
local notation "h₀" => le_refl (0 : ℝ)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "w(" F ", " α ", " s ")" => (fun g : C𝔽(F) ↦
  intervalSobolevDensity (-α) α s (logNorm(F) g))
local notation "W(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s
local notation "W'(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s true
local notation "A(" F ", " hα ", " hs ", " φ ")" =>
  hardySobolevTestAction (μ(F)) m𝔽(F) _ _ _ (hStrip(hα)) hs φ
local notation "ν(" F ", " α ", " s ")" =>
  ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g))
local notation "ν'(" F ", " α ", " s ")" =>
  ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g)⁻¹)
local notation "sourceFirst(" F ", " α ", " s ")" =>
  Lp ℂ 2 ((ν'(F, α, s)).prod (ν(F, α, s)))
local notation "tensor(" F ", " α ", " s ")" =>
  Completion (ProjectiveTensor W'(F, α, s) W(F, α, s))
local notation "printedClass(" F ", " α ", " s ", " hα ", " hs ", " K ")" =>
  Lp.compMeasurePreserving Prod.swap
    (Measure.measurePreserving_swap (μ := ν'(F, α, s)) (ν := ν(F, α, s)))
    (sobolevProjectiveKernelClass (F := F) hα hs K)

/-- Paper: (10.4.3.1), p. 465. The displayed polynomial is claimed to
regularize the completed Hecke L-function for every unitary character.
Removable values are filled in according to the meromorphic convention of §7.1. -/
def Printed.unshiftedHeckeRegularization_entire : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)),
    Differentiable ℂ (toMeromorphicNFOn (fun z : ℂ ↦
      (z * (z - 1) / 2) ^ (if ∀ g : C₁(F), χ g.val = 1 then (1 : ℕ) else 0) *
        continuedCompletedHeckeL χ z) univ)

/-- Paper: (10.4.3.1), p. 465. For F = ℚ and χ = |·|^i the completed
L-function is completed zeta at z + i. Its pole at 1 − i survives
multiplication by z(z − 1)/2, which is nonzero there. -/
theorem Printed.unshiftedHeckeRegularization_entire_false :
    ¬ Printed.unshiftedHeckeRegularization_entire := by
  intro h
  let c := ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) Complex.I
  have hunit (g : C𝔽(ℚ)) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I)‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let χ : PontryaginDual C𝔽(ℚ) :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hunit g)⟩
      map_one' := Subtype.ext c.map_one
      map_mul' := fun g k ↦ Subtype.ext (c.map_mul g k)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hk (g : C₁(ℚ)) : χ g.val = 1 := by
    apply Subtype.ext
    change (1 : ℂ) * ((((ideleClassNorm ℚ g.val).val : ℝ) : ℂ) ^ Complex.I) = 1
    rw [MonoidHom.mem_ker.mp g.property]
    simp
  have htwist : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
      (-Complex.I * ((-1 : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one, neg_neg]
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hker : χ.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype = 1 := by
    ext1 g
    exact hk g
  obtain ⟨t, ht, -⟩ := completedHeckeL_continuation_simplePoles χ _ hL hEq hker
  have ht' := (existsUnique_ideleClassNormTwist χ hker).unique ht.1 htwist
  have hpole : meromorphicOrderAt (continuedCompletedHeckeL χ) (1 - Complex.I) = -1 := by
    simpa [ht', sub_eq_add_neg] using ht.2.2.1
  let P := fun z : ℂ ↦ z * (z - 1) / 2
  have hP : Differentiable ℂ P := by
    dsimp [P]
    fun_prop
  have hPne : P (1 - Complex.I) ≠ 0 := by
    dsimp [P]
    apply div_ne_zero (mul_ne_zero _ _) (by norm_num)
    · intro he
      have := congrArg Complex.re he
      norm_num at this
    · simp
  have hentire := h ℚ χ
  simp only [ite_eq_left hk, pow_one] at hentire
  change Differentiable ℂ (toMeromorphicNFOn (P * continuedCompletedHeckeL χ) univ) at hentire
  have hnonneg := (hentire.analyticAt (1 - Complex.I)).meromorphicOrderAt_nonneg
  have hm : MeromorphicOn P univ := fun z _ ↦ (hP.analyticAt z).meromorphicAt
  rw [meromorphicOrderAt_toMeromorphicNFOn (hm.mul hL.meromorphicOn) (mem_univ _),
    meromorphicOrderAt_mul_of_ne_zero (hP.analyticAt _) hPne, hpole] at hnonneg
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hnonneg

/-- Paper: (10.4.3.5), p. 466. For a fixed character and shift, a unique
family of isotypic exponential-decay tests is biorthogonal to the zero jets.
The functional label uses the unshifted zero, as in the displayed formula. -/
def Printed.spectralSchwartzBiorthogonal_unique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (a : ℝ),
    let ι : C₁(F) →ₜ* C𝔽(F) := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
    let E := ↥(modulatedDecayIsotype m𝔽(F) univ (mem_univ 0) (χ.comp ι))
    let J := {j : ℂ × ℕ // j.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + j.1)).untop₀.toNat}
    ∃! ψ : J → E, ∀ j j' : J,
      (∫ g, (ψ j').val.val g * ideleClassNormTwist χ ((a : ℂ) + j.val.1) g *
        (logNorm(F) g : ℂ) ^ j.val.2 ∂(μ(F))) = if j = j' then 1 else 0

/-- Haar translation acts on the Mellin moments through the binomial expansion
of the shifted logarithm. -/
private theorem translated_mellin_moment {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [IsTopologicalGroup G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (L : G → ℂ)
    (hL : ∀ x y, L (x * y) = L x + L y) (c : G →ₜ* ℂ) (f : G → ℂ)
    (hf : ∀ i : ℕ, Integrable (fun x ↦ f x * c x * (L x) ^ i) μ)
    (y : G) (k : ℕ) :
    (∫ x, f (y⁻¹ * x) * c x * (L x) ^ k ∂μ) =
      c y * ∑ i ∈ Finset.range (k + 1), (L y) ^ (k - i) * (k.choose i : ℂ) *
        (∫ x, f x * c x * (L x) ^ i ∂μ) := by
  let A (i : ℕ) := (L y) ^ (k - i) * (k.choose i : ℂ)
  let P (i : ℕ) (x : G) := f x * c x * (L x) ^ i
  have hchange :
      (∫ x, f (y⁻¹ * x) * c x * (L x) ^ k ∂μ) =
        ∫ x, f x * (c y * c x) * (L x + L y) ^ k ∂μ := by
    rw [← integral_mul_left_eq_self (μ := μ) (fun x ↦ f (y⁻¹ * x) * c x * (L x) ^ k) y]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by
      dsimp only
      rw [inv_mul_cancel_left, map_mul, hL, add_comm (L y)])
  rw [hchange]
  change _ = c y * ∑ i ∈ Finset.range (k + 1), A i * (∫ x, P i x ∂μ)
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ (hf i).const_mul (A i)), ← integral_const_mul]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  rw [add_pow, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by dsimp [A, P]; ring

/-- The two real twists at abscissas one unit to either side dominate
every fixed logarithmic moment of a rational decay test. -/
private theorem rational_decay_moment_integrable (f : ModulatedExponentialDecay m𝔽(ℚ) univ) (z : ℂ) (k : ℕ) :
    Integrable (fun x ↦ f.val x * ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) z x *
      (logNorm(ℚ) x : ℂ) ^ k) μ(ℚ) := by
  let m := m𝔽(ℚ)
  let c := ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) z
  let L (x : C𝔽(ℚ)) : ℂ := logNorm(ℚ) x
  let T (a : ℝ) := modulatedExponentialDecayTwist m univ ⟨a, mem_univ a⟩ f
  have h₁ := (SchwartzBruhat.integrable μ(ℚ) (T (z.re + 1))).norm
  have h₂ := (SchwartzBruhat.integrable μ(ℚ) (T (z.re - 1))).norm
  have hf0 : AEStronglyMeasurable f.val μ(ℚ) :=
    (SchwartzBruhat.integrable μ(ℚ) (T 0)).aestronglyMeasurable.congr (ae_of_all _ fun x ↦
      (modulatedExponentialDecayTwist_apply m univ ⟨0, mem_univ _⟩ f x).trans (by simp))
  have hL : Continuous L := by
    apply Complex.continuous_ofReal.comp
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  refine ((h₁.add h₂).const_mul (k.factorial : ℝ)).mono'
    ((hf0.mul c.continuous.aestronglyMeasurable).mul (hL.pow k).aestronglyMeasurable)
    (ae_of_all _ fun x ↦ ?_)
  let r : ℝ := (m x).val
  have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt (m x))
  have hTw (a : ℝ) : ‖(T a).val x‖ = r ^ a * ‖f.val x‖ := by
    refine (congrArg norm (modulatedExponentialDecayTwist_apply m univ ⟨a, mem_univ _⟩ f x)).trans ?_
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
  have hc : ‖c x‖ = r ^ z.re := by
    change ‖(1 : ℂ) * (r : ℂ) ^ z‖ = _
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  have hp : |Real.log r| ^ k ≤ (k.factorial : ℝ) * (r + r⁻¹) := by
    have h := Real.pow_div_factorial_le_exp |Real.log r| (abs_nonneg _) k
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hk] at h
    have he : Real.exp |Real.log r| ≤ r + r⁻¹ := by
      rcases le_total 0 (Real.log r) with h | h
      · rw [abs_of_nonneg h, Real.exp_log hr]
        exact le_add_of_nonneg_right (inv_nonneg.mpr hr.le)
      · rw [abs_of_nonpos h, Real.exp_neg, Real.exp_log hr]
        exact le_add_of_nonneg_left hr.le
    exact h.trans ((mul_le_mul_of_nonneg_right he hk.le).trans_eq (mul_comm _ _))
  change ‖f.val x * c x * (L x) ^ k‖ ≤
    (k.factorial : ℝ) * (‖(T (z.re + 1)).val x‖ + ‖(T (z.re - 1)).val x‖)
  rw [norm_mul, norm_mul, hc, norm_pow, Complex.norm_real, Real.norm_eq_abs, hTw, hTw,
    Real.rpow_add hr, Real.rpow_sub hr, Real.rpow_one]
  calc
    ‖f.val x‖ * r ^ z.re * |Real.log r| ^ k ≤
      ‖f.val x‖ * r ^ z.re * ((k.factorial : ℝ) * (r + r⁻¹)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- The rational order comparison is the one used for the strip index in
the proof of the ambient pairing refutation in Sec4a. -/
private theorem rational_biorthogonal_zero :
    ∃ z : ℂ, 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z).untop₀.toNat := by
  obtain ⟨t, _, ht⟩ := HardyFirstZero.first_zero_on_line
  let z : ℂ := 1 / 2 + t * Complex.I
  have hne : z ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    norm_num [z] at this
  have ha := analyticOn_riemannZeta z hne
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have he := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C𝔽(ℚ))
    hm (fun s ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property])
    (s := z) (by norm_num [z])
  have hz2 : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 := by
    have h := analyticOn_riemannZeta 2 (by norm_num : (2 : ℂ) ≠ 1)
    rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
    rfl
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [hz2]; simp)
  have hpos : analyticOrderAt riemannZeta z ≠ 0 := ha.analyticOrderAt_ne_zero.mpr ht
  refine ⟨z, ?_⟩
  rw [← he, ha.meromorphicOrderAt_eq]
  rw [ha.meromorphicOrderAt_eq] at hfin
  generalize analyticOrderAt riemannZeta z = k at hfin hpos ⊢
  cases k using ENat.recTopCoe with
  | top => simp at hfin
  | coe n =>
    have hn : n ≠ 0 := by simpa using hpos
    simpa using Nat.pos_of_ne_zero hn

private theorem rational_norm_haar_univ : μ(ℚ) univ = ⊤ := by
  let m := m𝔽(ℚ)
  let L := logNorm(ℚ)
  have hc : Continuous L := by
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hs : Surjective L := by
    intro r
    let a : ℝ≥0 := ⟨Real.exp r, (Real.exp_pos r).le⟩
    let u := Units.mk0 a (NNReal.coe_ne_zero.mp (Real.exp_pos r).ne')
    obtain ⟨x, hx⟩ := ratIdeleNormSection_class_rightInverse.surjective u
    refine ⟨x, ?_⟩
    change Real.log (((ideleClassNorm ℚ x).val : ℝ)) = r
    rw [hx]
    exact Real.log_exp r
  have : NoncompactSpace C𝔽(ℚ) := ⟨fun h ↦
    NoncompactSpace.noncompact_univ (X := ℝ)
      (by simpa only [image_univ, hs.range_eq] using h.image hc)⟩
  exact measure_univ_of_isMulLeftInvariant μ(ℚ)

/-- Paper: (10.4.3.5), p. 466. A normalized translate of the test for the
highest jet at a certified rational zeta zero has the same biorthogonal
pairings. Uniqueness would make the test times its norm character a constant
integrable function on the noncompact idele class group, contrary to the
nonzero pairing at the highest jet. -/
theorem Printed.spectralSchwartzBiorthogonal_unique_false :
    ¬ Printed.spectralSchwartzBiorthogonal_unique := by
  classical
  intro h
  obtain ⟨z, hz⟩ := rational_biorthogonal_zero
  let m := m𝔽(ℚ)
  let χ := ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
  let L (x : C𝔽(ℚ)) : ℂ := logNorm(ℚ) x
  let N (w : ℂ) :=
    (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) (0 + w)).untop₀.toNat
  let J := {j : ℂ × ℕ // j.2 < N j.1}
  let n := N z - 1
  have hzN : 0 < N z := by simpa [N] using hz
  let j₀ : J := ⟨(z, n), by
    change n < N z
    dsimp [n]
    omega⟩
  let ι : (ideleClassNorm ℚ).ker →ₜ* C𝔽(ℚ) := ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp ι
  let E := ↥(modulatedDecayIsotype m univ (mem_univ 0) ω)
  let M (f : C𝔽(ℚ) → ℂ) (w : ℂ) (k : ℕ) := ∫ g, f g * χ w g * (L g) ^ k ∂μ(ℚ)
  let P (ψ : J → E) := ∀ j j' : J, M (ψ j').val.val j.val.1 j.val.2 = if j = j' then 1 else 0
  have hex := h ℚ (1 : PontryaginDual C𝔽(ℚ)) 0
  simp only [Complex.ofReal_zero, zero_add] at hex
  change ∃! ψ : J → E, P ψ at hex
  obtain ⟨ψ, hψ, huniq⟩ := hex
  let f := (ψ j₀).val
  let c := χ z
  have hL (x y : C𝔽(ℚ)) : L (x * y) = L x + L y := by
    change (Real.log ((m (x * y)).val : ℝ) : ℂ) =
      (Real.log ((m x).val : ℝ) : ℂ) + (Real.log ((m y).val : ℝ) : ℂ)
    rw [map_mul, Units.val_mul, NNReal.coe_mul,
      Real.log_mul (NNReal.coe_ne_zero.mpr (m x).ne_zero)
        (NNReal.coe_ne_zero.mpr (m y).ne_zero), Complex.ofReal_add]
  have hc (w : ℂ) (y : C𝔽(ℚ)) : χ w y ≠ 0 :=
    ((Group.isUnit y).map (χ w)).ne_zero
  have hMtrans (y : C𝔽(ℚ)) (j : J) :
      M (fun x ↦ f.val (y⁻¹ * x)) j.val.1 j.val.2 = c y * (if j = j₀ then 1 else 0) := by
    rw [show M (fun x ↦ f.val (y⁻¹ * x)) j.val.1 j.val.2 =
        χ j.val.1 y * ∑ i ∈ Finset.range (j.val.2 + 1),
          (L y) ^ (j.val.2 - i) * (j.val.2.choose i : ℂ) * M f.val j.val.1 i
      from translated_mellin_moment μ(ℚ) L hL (χ j.val.1) f.val
        (rational_decay_moment_integrable f j.val.1) y j.val.2]
    have hlow (i : ℕ) (hi : i ∈ Finset.range (j.val.2 + 1)) :
        M f.val j.val.1 i =
          if (⟨(j.val.1, i), (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt j.property⟩ : J) =
            j₀ then 1 else 0 :=
      hψ ⟨(j.val.1, i), (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt j.property⟩ j₀
    by_cases hEq : j = j₀
    · subst j
      rw [ite_eq_left rfl]
      have hsum : (∑ i ∈ Finset.range (n + 1), (L y) ^ (n - i) *
          (n.choose i : ℂ) * M f.val z i) = 1 := by
        rw [Finset.sum_eq_single n]
        · have hn := hψ j₀ j₀
          change M f.val z n = _ at hn
          simp [hn]
        · intro i hi hni
          have hl := hlow i hi
          change M f.val z i = _ at hl
          rw [hl, ite_eq_right (fun he ↦ hni (congrArg (fun l : J ↦ l.val.2) he)), mul_zero]
        · simp
      change c y * (∑ i ∈ Finset.range (n + 1), (L y) ^ (n - i) *
        (n.choose i : ℂ) * M f.val z i) = c y * 1
      rw [hsum]
    · rw [ite_eq_right hEq, mul_zero]
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [hlow i hi, ite_eq_right ?_, mul_zero]
      intro he
      have hz' : j.val.1 = z := congrArg (fun l : J ↦ l.val.1) he
      have hi' : i = n := congrArg (fun l : J ↦ l.val.2) he
      have hj' : j.val.2 < N z := hz' ▸ j.property
      have hij := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      apply hEq
      have hn : j.val.2 = n := by
        apply le_antisymm _ (hi' ▸ hij)
        exact Nat.le_pred_of_lt hj'
      exact Subtype.ext (Prod.ext hz' hn)
  have himp (y : C𝔽(ℚ)) : f.val y * c y = f.val 1 := by
    have hm : IsModulation m := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
    let f' : ModulatedExponentialDecay m univ := ⟨fun x ↦ f.val (y⁻¹ * x),
      modulatedExponentialDecaySubmodule_translate m univ hm
        ratIdeleNormSection_class_rightInverse.surjective y f⟩
    have hf' : f' ∈ modulatedDecayIsotype m univ (mem_univ 0) ω := by
      apply (mem_modulatedDecayIsotype_iff m ω univ (mem_univ 0) f').mpr
      have hmem := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ 0) f).mp (ψ j₀).property
      intro u x
      change f.val (y⁻¹ * (u.val⁻¹ * x)) = _ * f.val (y⁻¹ * x)
      rw [mul_left_comm, hmem]
    let v : E := (c y)⁻¹ • (⟨f', hf'⟩ : E)
    let ψ' : J → E := Function.update ψ j₀ v
    have hψ' : P ψ' := by
      intro j j'
      by_cases hj : j' = j₀
      · subst j'
        rw [show ψ' j₀ = v from Function.update_self ..]
        change (∫ x, ((c y)⁻¹ * f.val (y⁻¹ * x)) * χ j.val.1 x * L x ^ j.val.2 ∂μ(ℚ)) = _
        simp_rw [mul_assoc ((c y)⁻¹), integral_const_mul]
        change (c y)⁻¹ * M (fun x ↦ f.val (y⁻¹ * x)) j.val.1 j.val.2 = _
        rw [hMtrans, ← mul_assoc, inv_mul_cancel₀ (hc z y), one_mul]
      · simpa only [ψ', Function.update_of_ne hj] using hψ j j'
    have heq := congrArg (fun φ : J → E ↦ (φ j₀).val.val y) (huniq ψ' hψ')
    rw [show ψ' j₀ = v from Function.update_self ..] at heq
    change (c y)⁻¹ * f.val (y⁻¹ * y) = f.val y at heq
    rw [inv_mul_cancel] at heq
    rw [← heq, mul_comm _ (c y), ← mul_assoc, mul_inv_cancel₀ (hc z y), one_mul]
  have hfi : Integrable (fun x : C𝔽(ℚ) ↦ f.val 1) μ(ℚ) := by
    exact (rational_decay_moment_integrable f z 0).congr
      (ae_of_all μ(ℚ) fun x ↦ by
        change f.val x * c x * L x ^ 0 = _
        simpa only [pow_zero, mul_one] using himp x)
  have h1 : f.val 1 = 0 := (integrable_const_iff.mp hfi).resolve_right
    (fun hfinite ↦ (measure_lt_top μ(ℚ) univ).ne rational_norm_haar_univ)
  have hzero (x : C𝔽(ℚ)) : f.val x = 0 := (mul_eq_zero.mp ((himp x).trans h1)).resolve_right (hc z x)
  have hval := hψ j₀ j₀
  change M f.val z n = _ at hval
  simp [M, hzero] at hval

local notation "represents(" F ", " α ", " s ", " B ", " k ")" =>
  (∀ u : W(F, α, s), ∀ᵐ x ∂(μ(F)),
    Integrable (fun y ↦ k (x, y) * u y) (μ(F)) ∧
      B u x = ∫ y, k (x, y) * u y ∂(μ(F)))
local notation "printedWeight(" F ", " α ", " s ", " ρ ", " k ")" =>
  (fun p : C𝔽(F) × C𝔽(F) ↦ (ρ p.1 * (w(F, α, s) p.2)⁻¹ ^ 2 : ℝ) • k p)

/-- Paper: (10.4.3.24)–(10.4.3.25), p. 470. The tensor image in the
source-first product is claimed to be the unique class whose displayed
weighted integral gives the spectral operator, with k evaluated at (x,y). -/
def Printed.spectralLineKernel_extraWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ φ : BruhatCompactSupport C𝔽(F),
      let B := (spectralProjection (F := F) a h₀ hs₀(hs)).comp (A(F, h₀, hs₀(hs), φ))
      ∃ K : tensor(F, 0, s), sobolevProjectiveKernelOperator (F := F) h₀ hs₀(hs) K = B ∧
        ∀ l : sourceFirst(F, 0, s),
          represents(F, 0, s, B, (fun p ↦ ((w(F, 0, s) p.2)⁻¹ : ℝ) • l p)) ↔
            l = printedClass(F, 0, s, h₀, hs₀(hs), K)

section ExtraKernelWeight

open scoped ENNReal

local notation "C" => C𝔽(ℚ)
local notation "mQ" => m𝔽(ℚ)
local notation "μC" => μ(ℚ)
local notation "logQ" => logNorm(ℚ)
local notation "d" => w(ℚ, 0, 2)
local notation "νp" => ν(ℚ, 0, 2)
local notation "νm" => ν'(ℚ, 0, 2)
local notation "W₂" => W(ℚ, 0, 2)
local notation "hs₂" => (show (0 : ℝ) ≤ 2 by norm_num)

private theorem extraWeight_density (g : C) : d g = 1 + logQ g ^ 2 := by
  norm_num [intervalSobolevDensity]

private theorem extraWeight_log_continuous : Continuous logQ := by
  have hn : Continuous (fun g : C ↦ (((ideleClassNorm ℚ g).val : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (mQ).continuous)
  exact hn.log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

private theorem extraWeight_density_continuous : Continuous d := by
  rw [funext extraWeight_density]
  exact continuous_const.add (extraWeight_log_continuous.pow 2)

private theorem extraWeight_one_le (g : C) : 1 ≤ d g := by
  rw [extraWeight_density]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem extraWeight_pos (g : C) : 0 < d g := zero_lt_one.trans_le (extraWeight_one_le g)

private theorem extraWeight_haar_ac : μC ≪ νp ∧ μC ≪ νm := by
  refine ⟨?_, ?_⟩
  · exact withDensity_absolutelyContinuous'
      extraWeight_density_continuous.measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (extraWeight_pos g)).ne')
  · exact withDensity_absolutelyContinuous'
      extraWeight_density_continuous.measurable.inv.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (extraWeight_pos g))).ne')

private theorem extraWeight_inverse_le (g : C) : (d g)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (extraWeight_one_le g)

private theorem extraWeight_measure_le : νm ≤ νp := by
  apply withDensity_mono
  exact ae_of_all _ fun g ↦ ENNReal.ofReal_le_ofReal
    ((extraWeight_inverse_le g).trans (extraWeight_one_le g))

private def extraWeight_nnreal (x : C) : ℝ≥0 := ⟨d x, (extraWeight_pos x).le⟩

local notation "wp" => extraWeight_nnreal
local notation "wm" => (wp⁻¹)

private theorem extraWeight_density_measurable : Measurable wp :=
  (extraWeight_density_continuous.subtype_mk _).measurable

private theorem extraWeight_measure_plus : νp = (μC).withDensity (fun g ↦ (wp g : ℝ≥0∞)) :=
  congrArg (μC).withDensity (funext fun g ↦ ENNReal.ofReal_eq_coe_nnreal (extraWeight_pos g).le)

private theorem extraWeight_measure_minus : νm = (μC).withDensity (fun g ↦ (wm g : ℝ≥0∞)) :=
  congrArg (μC).withDensity (funext fun g ↦ ENNReal.ofReal_eq_coe_nnreal (inv_pos.mpr (extraWeight_pos g)).le)

/-- Multiplying an L² input for the reciprocal measure by the reciprocal
density turns it into an input for the positive measure. -/
private theorem extraWeight_test_memLp (u : Lp ℂ 2 νm) :
    MemLp (fun y ↦ (d y)⁻¹ • u y) 2 νp := by
  have hac : νp ≪ νm := (withDensity_absolutelyContinuous μC _).trans extraWeight_haar_ac.2
  have hm := ((extraWeight_density_continuous.inv₀ (fun x ↦ (extraWeight_pos x).ne')).aestronglyMeasurable (μ := νp)).smul
    (AEStronglyMeasurable.mono_ac hac (Lp.aestronglyMeasurable u))
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have hi' : Integrable (fun x ↦ ‖u x‖ ^ 2)
      ((μC).withDensity fun y ↦ (wm y : ℝ≥0∞)) :=
    (congrArg (fun η ↦ Integrable (fun x ↦ ‖u x‖ ^ 2) η) extraWeight_measure_minus).mp hi
  have hi'' := (integrable_withDensity_iff_integrable_smul (μ := μC) extraWeight_density_measurable.inv).mp hi'
  rw [extraWeight_measure_plus, integrable_withDensity_iff_integrable_smul extraWeight_density_measurable]
  refine hi''.congr (ae_of_all _ fun y ↦ ?_)
  change (d y)⁻¹ * ‖u y‖ ^ 2 = d y * ‖(d y)⁻¹ • u y‖ ^ 2
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (extraWeight_pos y).le)]
  field_simp [(extraWeight_pos y).ne']

/-- On the product of the two reciprocal measures, L² kernels are unique for
the Haar row integrals on the positive Sobolev space. -/
private theorem extraWeight_kernel_unique
    (B : W₂ →L[ℂ] W₂) (k h : C × C → ℂ)
    (hk : MemLp k 2 ((νm).prod (νm))) (hh : MemLp h 2 ((νm).prod (νm)))
    (hBk : represents(ℚ, 0, 2, B, k)) (hBh : represents(ℚ, 0, 2, B, h)) :
    k =ᵐ[(νm).prod (νm)] h := by
  let : IsLocallyFiniteMeasure νm := by
    rw [extraWeight_measure_minus]
    exact IsLocallyFiniteMeasure.withDensity_coe
      (show Continuous wm from
        (show Continuous wp from extraWeight_density_continuous.subtype_mk _).inv₀
          (fun x hx ↦ (extraWeight_pos x).ne' (congrArg NNReal.toReal hx)))
  have hnorm (g : C → ℂ) : (∫ y, g y ∂νm) = ∫ y, (d y)⁻¹ • g y ∂μC := by
    rw [extraWeight_measure_minus]
    exact integral_withDensity_eq_integral_smul extraWeight_density_measurable.inv g
  let T := integralKernelOperator νm
  have hT : T (hk.toLp k) = T (hh.toLp h) := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro u
    let f : W₂ := (extraWeight_test_memLp u).toLp (fun y ↦ (d y)⁻¹ • u y)
    have hf := extraWeight_haar_ac.1.ae_le (extraWeight_test_memLp u).coeFn_toLp
    have he (j : C × C → ℂ) (hj : MemLp j 2 ((νm).prod (νm)))
        (hB : represents(ℚ, 0, 2, B, j)) :
        ∀ᵐ x ∂νm, (T (hj.toLp j)).val u x = B f x := by
      have hac : νm ≪ μC := withDensity_absolutelyContinuous _ _
      have hback := hac.ae_le (hB f)
      filter_upwards [integralKernelOperator_apply νm (hj.toLp j) u,
        Measure.ae_ae_of_ae_prod hj.coeFn_toLp, hback] with x hx hrow hBx
      rw [hx.2, hBx.2]
      calc
        _ = ∫ y, j (x, y) * u y ∂νm :=
          integral_congr_ae (hrow.mono fun y hy ↦ congrArg (· * u y) hy)
        _ = ∫ y, j (x, y) * f y ∂μC := by
          rw [hnorm]
          apply integral_congr_ae
          filter_upwards [hf] with y hy
          change f y = (d y)⁻¹ • u y at hy
          rw [hy, mul_smul_comm]
    apply Lp.ext
    filter_upwards [he k hk hBk, he h hh hBh] with x hx hy
    exact hx.trans hy.symm
  have he := (bijective_integralKernelOperator νm).injective hT
  exact hk.coeFn_toLp.symm.trans (he ▸ hh.coeFn_toLp)

/-- The logarithmic norm pushes Haar measure to a locally finite translation-invariant
measure. In particular its zero fiber is null. -/
private theorem extraWeight_log_ne_zero : ∀ᵐ x ∂μC, logQ x ≠ 0 := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he : (e ∘ mQ) = logQ := funext fun g ↦
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g)))).symm
  let n : C →* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (logQ g)
      map_one' := by change logQ 1 = 0; simp
      map_mul' := fun x y ↦ by
        change logQ (x * y) = logQ x + logQ y
        simp only [logIdeleClassNorm, map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
          (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'] }
  have hn : IsProperMap n := by
    change IsProperMap logQ
    rw [← he]
    exact e.isProperMap.comp (isProperMap_ideleClassNorm ℚ)
  have hsurj : Surjective n := by
    change Surjective logQ
    rw [← he]
    refine e.surjective.comp ?_
    intro t
    exact ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ t), canonicalIdeleNormSection_rightInverse ℚ t⟩
  let η : Measure (Multiplicative ℝ) := (μC).map (n : C → Multiplicative ℝ)
  have hm : Measurable (n : C → Multiplicative ℝ) := extraWeight_log_continuous.measurable
  let : η.IsMulLeftInvariant := by
    change ((μC).map (n : C → Multiplicative ℝ)).IsMulLeftInvariant
    exact isMulLeftInvariant_map (μ := μC) n.toMulHom hm hsurj
  let : IsFiniteMeasureOnCompacts η := ⟨fun K hK ↦ by
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    exact (hn.isCompact_preimage hK).measure_lt_top⟩
  let o : Multiplicative ℝ := Multiplicative.ofAdd 0
  have hnull : η {o} = 0 := by
    by_contra h
    let I : Set ℝ := Icc 0 1
    have hI : IsCompact I := isCompact_Icc
    have hIinf : I.Infinite := Icc_infinite (show (0 : ℝ) < 1 from zero_lt_one)
    let K : Set (Multiplicative ℝ) := I
    have hK : IsCompact K := hI
    have hInf : K.Infinite := hIinf
    have hpoints (x : Multiplicative ℝ) : η {x} = η {o} := by
      have hp : (x * ·) ⁻¹' {x} = {o} := by
        ext y
        change x * y = x ↔ y = o
        constructor
        · intro hy
          exact mul_left_cancel (hy.trans (mul_one x).symm)
        · rintro rfl
          exact mul_one x
      conv_lhs => rw [← map_mul_left_eq_self η x]
      rw [Measure.map_apply (measurable_const_mul x) (measurableSet_singleton x), hp]
    exact hK.measure_lt_top.ne (hInf.meas_eq_top ⟨η {o}, h, fun x _ ↦ (hpoints x).ge⟩)
  rw [Measure.map_apply hm (measurableSet_singleton o)] at hnull
  apply ae_iff.mpr
  have heq : {x : C | ¬ logQ x ≠ 0} = n ⁻¹' {o} := by
    ext x
    change (¬ logQ x ≠ 0) ↔ logQ x = 0
    exact not_not
  rwa [heq]

private theorem extraWeight_haar_repr_zero
    (B : W₂ →L[ℂ] W₂) {k : C × C → ℂ}
    (hzero : k =ᵐ[(μC).prod (μC)] 0) (hB : represents(ℚ, 0, 2, B, k)) : B = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  rw [zero_apply]
  apply Lp.ext
  have hB0 : ∀ᵐ x ∂μC, B u x = 0 := by
    filter_upwards [hB u, Measure.ae_ae_of_ae_prod hzero] with x hx hy
    rw [hx.2]
    apply integral_eq_zero_of_ae
    filter_upwards [hy] with y hy
    change k (x, y) = 0 at hy
    rw [hy, zero_mul, Pi.zero_apply]
  have hac : νp ≪ μC := withDensity_absolutelyContinuous _ _
  have h := hac.ae_le hB0
  filter_upwards [h, Lp.coeFn_zero ℂ 2 νp] with x hx hz
  exact hx.trans hz.symm

local notation "kH(" K ")" => sobolevProjectiveKernelClass (F := ℚ) h₀ hs₂ K
local notation "kS(" K ")" =>
  Lp.compMeasurePreserving Prod.swap
    (Measure.measurePreserving_swap (μ := νm) (ν := νp)) kH(K)
local notation "tilted(" k ")" => (fun p : C × C ↦ ((d p.2)⁻¹ : ℝ) • k p)

/-- The weighted transpose of a nonzero mixed-Haar kernel cannot represent
the same operator. -/
private theorem extraWeight_printed_operator_zero (K : tensor(ℚ, 0, 2))
    (B : W₂ →L[ℂ] W₂)
    (hK : sobolevProjectiveKernelOperator (F := ℚ) h₀ hs₂ K = B)
    (hS : represents(ℚ, 0, 2, B, tilted(kS(K)))) : B = 0 := by
  let k := kH(K)
  let l := kS(K)
  have hrep := (sobolevProjectiveKernelClass_spec (F := ℚ) h₀ hs₂ K k).2 rfl
  rw [hK] at hrep
  have hk := (Lp.memLp k).mono_measure (Measure.prod_mono extraWeight_measure_le le_rfl)
  have hl := (Lp.memLp l).mono_measure (Measure.prod_mono le_rfl extraWeight_measure_le)
  have hltilt : MemLp tilted(l) 2 ((νm).prod (νm)) := by
    have hm : Continuous (fun p : C × C ↦ (d p.2)⁻¹) :=
      (extraWeight_density_continuous.inv₀ (fun x ↦ (extraWeight_pos x).ne')).comp continuous_snd
    refine hl.norm.mono' (hm.aestronglyMeasurable.smul hl.aestronglyMeasurable) ?_
    exact ae_of_all _ fun p ↦ by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (extraWeight_pos _).le)]
      exact mul_le_of_le_one_left (norm_nonneg _) (extraWeight_inverse_le _)
  have hkg := extraWeight_kernel_unique B k tilted(l) hk hltilt hrep hS
  have hac : (μC).prod (μC) ≪ (νm).prod (νm) := extraWeight_haar_ac.2.prod extraWeight_haar_ac.2
  have hau : (μC).prod (μC) ≪ (νm).prod (νp) := extraWeight_haar_ac.2.prod extraWeight_haar_ac.1
  have hswap := hau.ae_le (Lp.coeFn_compMeasurePreserving k
    (Measure.measurePreserving_swap (μ := νm) (ν := νp)))
  have he : ∀ᵐ p ∂(μC).prod (μC), k p = (d p.2)⁻¹ • k p.swap := by
    filter_upwards [hac.ae_le hkg, hswap] with p hp hs
    change l p = k p.swap at hs
    change k p = (d p.2)⁻¹ • l p at hp
    rwa [hs] at hp
  have hf := (Measure.measurePreserving_swap (μ := μC) (ν := μC)).quasiMeasurePreserving.ae he
  have hfirst : ∀ᵐ p ∂(μC).prod (μC), logQ p.1 ≠ 0 := by
    have hm : MeasurableSet {p : C × C | logQ p.1 ≠ 0} :=
      ((measurableSet_singleton 0).preimage
        (extraWeight_log_continuous.measurable.comp measurable_fst)).compl
    exact (Measure.ae_prod_iff_ae_ae hm).2
      (extraWeight_log_ne_zero.mono fun _ hx ↦ ae_of_all _ fun _ ↦ hx)
  apply extraWeight_haar_repr_zero B ?_ hrep
  filter_upwards [he, hf, hfirst] with p hp hq hnon
  change k p.swap = (d p.1)⁻¹ • k p at hq
  rw [hq, smul_smul] at hp
  have hlt : 1 < d p.1 := by rw [extraWeight_density]; nlinarith [sq_pos_of_ne_zero hnon]
  have hi : (d p.2)⁻¹ * (d p.1)⁻¹ < 1 :=
    (mul_le_of_le_one_left (inv_nonneg.mpr (extraWeight_pos p.1).le) (extraWeight_inverse_le p.2)).trans_lt
      (inv_lt_one_of_one_lt₀ hlt)
  have hz : (1 - (d p.2)⁻¹ * (d p.1)⁻¹) • k p = 0 := by rw [sub_smul, one_smul, ← hp, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hi.ne')

section

local notation "hs" => (show (1 : ℝ) < 2 from one_lt_two)
local notation "Θ₂(" F ")" => globalThetaSobolev F (1/2) h₀ hs₂
local notation "Q₂(" F ")" => spectralSobolevQuotient F (1/2) h₀ hs₂
local notation "W₂(" F ")" => CompactIntervalSobolev (μ(F))
  (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) 0 0 2
local notation "τ₂(" F ")" => hardySobolevTranslation (μ(F)) (m𝔽(F)) 0 0 2 h₀ hs₂
local notation "A₂(" F ", " φ ")" =>
  hardySobolevTestAction (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂ φ
local notation "U₂(" F ", " φ ")" => spectralConvolution (F := F) (1/2) h₀ hs₂ φ
local notation "zetaPoint(" t ")" => ((1 : ℂ) / 2 + (t : ℂ) * Complex.I)
local notation "η(" χ ", " j ")" => ideleClassNormTwist (χ (Subtype.val j).1) (((Subtype.val j).2.1 : ℂ) * Complex.I)

/-- The strict Sobolev cutoff at weight two admits only order-zero evaluations. -/
private theorem extraWeight_jet_order_zero {F : Type} [Field F] [NumberField F]
    {χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)}
    (j : SpectralLineJetIndex χ (1/2) 2) : j.val.2.2 = 0 := by
  have h := ((lt_spectralBoundaryMultiplicity _ _ _).mp j.property).2
  by_contra hz
  have hb : 1 ≤ j.val.2.2 := Nat.one_le_iff_ne_zero.mpr hz
  have hb' : (1 : ℝ) ≤ (j.val.2.2 : ℝ) := by exact_mod_cast hb
  linarith

/-- Thomas Lince’s certified critical-line bracket gives a zero of the completed
Hecke function of the trivial rational character, using the rational comparison
as in the singleton Fourier-band refutation in §10.2. -/
private theorem extraWeight_critical_line_point :
    ∃ γ : ℝ, 0 < (meromorphicOrderAt
      (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) zetaPoint(γ)).untop₀.toNat := by
  obtain ⟨γ, -, hγ⟩ := HardyFirstZero.first_zero_on_line
  let z : ℂ := zetaPoint(γ)
  have hre : z.re = 1 / 2 := by simp [z]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  refine ⟨γ, ?_⟩
  change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z).untop₀.toNat
  rw [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]
  have hnot (u : ℂ) : meromorphicOrderAt riemannZeta u ≠ ⊤ := by
    refine hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (2 : ℂ))
      (mem_univ u) ?_
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm 2 (mem_univ _))).2
      (((differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.eventually_ne
        (riemannZeta_ne_zero_of_one_lt_re (by norm_num))).filter_mono nhdsWithin_le_nhds)
  have hpos : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at hγ
    rw [← hγ]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  rw [← Int.pos_iff_toNat_pos]
  exact (WithTop.coe_lt_coe.mp (by simpa only [WithTop.coe_untop₀_of_ne_top (hnot z), WithTop.coe_zero] using hpos))



private theorem extraWeight_test_nonzero {F : Type} [Field F] [NumberField F] (η : QuasiCharacter C𝔽(F)) :
    ∃ φ : BruhatCompactSupport C𝔽(F), Continuous φ.val ∧ (∫ g, φ.val g * η g ∂μ(F)) ≠ 0 := by
  let m := m𝔽(F)
  let hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m := by
    intro q
    exact ⟨QuotientGroup.mk (canonicalIdeleNormSection F q),
      canonicalIdeleNormSection_rightInverse F q⟩
  obtain ⟨b, hb⟩ := exists_smoothModulatedCutoff_radius_two m hm hms
  have hbc : HasCompactSupport b := by
    let e := Nonneg.unitsHomeomorphPos ℝ
    have hS : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc (2⁻¹ : ℝ) 2) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr]
      · exact isCompact_Icc
      · intro r hr
        exact (by norm_num : (0 : ℝ) < 2⁻¹).trans_le hr.1
    exact (hm.1.isCompact_preimage (e.isCompact_preimage.mpr hS)).of_isClosed_subset
      (isClosed_tsupport b) hb.1.support_subset
  have hbC : HasCompactSupport (fun g ↦ (b g : ℂ)) :=
    hbc.comp_left Complex.ofReal_zero
  let b₀ : BruhatCompactSupport C𝔽(F) :=
    ⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hb.2, hbC⟩
  let B := bruhatCompactSupportToModulatedExponentialDecay m univ hm hms b₀
  let ηInv := η.comp (ContinuousMonoidHom.inv _)
  obtain ⟨E, hE⟩ := modulatedExponentialDecay_mul_quasiCharacter m hm hms ηInv
  have hEB (g : C𝔽(F)) : (E B).val g = (η g)⁻¹ * (b g : ℂ) :=
    (hE B g).trans (by change η g⁻¹ * (b g : ℂ) = _; rw [map_inv])
  have hBs : HasCompactSupport (E B).val := by
    rw [funext hEB]
    exact hbC.mul_left (f := fun g ↦ (η g)⁻¹)
  let φ : BruhatCompactSupport C𝔽(F) :=
    ⟨_, modulatedExponentialDecay_mem_bruhatSmooth m univ univ_nonempty (E B), hBs⟩
  have hηne (g : C𝔽(F)) : η g ≠ 0 := ((Group.isUnit g).map η).ne_zero
  have hprod (g : C𝔽(F)) : φ.val g * η g = (b g : ℂ) := by
    change (E B).val g * η g = _
    rw [hEB, mul_right_comm, inv_mul_cancel₀ (hηne g), one_mul]
  refine ⟨φ, ?_, ?_⟩
  · change Continuous (E B).val
    rw [funext hEB]
    exact (η.continuous.inv₀ hηne).mul (Complex.continuous_ofReal.comp hb.continuous)
  simp_rw [hprod]
  rw [integral_complex_ofReal]
  exact Complex.ofReal_ne_zero.mpr (hb.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hbc hb.1.nonneg
    (show b 1 ≠ 0 from (IsModulatedCutoff.apply_one (m := m) (ρ := b) hb.1 (by norm_num) (by norm_num)).trans_ne one_ne_zero)).ne'

private theorem extraWeight_basepoint_jet :
    ∃ (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)), IsSpectralBasepointChoice χ ∧
      Nonempty (SpectralLineJetIndex χ (1/2) 2) := by
  classical
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice ℚ
  let χ := Function.update χ₀ 1 (1 : PontryaginDual C𝔽(ℚ))
  have hχ1 : χ 1 = 1 := Function.update_self ..
  have hχ : IsSpectralBasepointChoice χ := by
    intro ω₁
    by_cases h : ω₁ = 1
    · subst ω₁
      rw [hχ1]
      rfl
    · simpa [χ, Function.update_of_ne h] using hχ₀ ω₁
  obtain ⟨γ, hγ⟩ := extraWeight_critical_line_point
  let ι := SpectralLineJetIndex χ (1 / 2) 2
  let j₀ : ι := ⟨(1, γ, 0), by
    rw [lt_spectralBoundaryMultiplicity]
    refine ⟨?_, by norm_num⟩
    change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ 1))
      (((1/2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).untop₀.toNat
    simpa only [hχ1, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hγ⟩
  exact ⟨χ, hχ, ⟨j₀⟩⟩

/-- The order-zero eigenvalue calculation follows the conjugate-weight refutation in §10.3. -/
private theorem extraWeight_convolution_eigen {F : Type} [Field F] [NumberField F]
     (η : QuasiCharacter C𝔽(F)) (Λ : StrongDual ℂ W₂(F))
    (hΛ : ∀ f : W₂(F), Λ f = ∫ g, f g * η g ∂μ(F)) :
    (∀ k : C𝔽(F), ∀ f : W₂(F), Λ (τ₂(F) k f) = η k * Λ f) ∧
    ∀ φ : BruhatCompactSupport C𝔽(F), ∀ f : W₂(F),
      Λ (hardySobolevTestAction (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂ φ f) =
        (∫ g, φ.val g * η g ∂μ(F)) * Λ f := by
  have eig (k : C𝔽(F)) (f : W₂(F)) : Λ (τ₂(F) k f) = η k * Λ f := by
    have htr := hardySobolevTranslation_apply (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂ k f
    rw [hΛ, hΛ, integral_congr_ae (htr.mono fun g hg ↦ congrArg (· * η g) hg)]
    calc
      _ = ∫ g, f g * η (k * g) ∂μ(F) := by
        rw [← integral_mul_left_eq_self (fun g ↦ f (k⁻¹ * g) * η g) k]
        simp only [inv_mul_cancel_left]
      _ = η k * ∫ g, f g * η g ∂μ(F) := by
        rw [← integral_const_mul]
        congr with g
        rw [map_mul]
        ring
  refine ⟨eig, fun φ f ↦ ?_⟩
  let τ := τ₂(F)
  have hτ := (exists_hardySobolevTranslation (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂).choose_spec.2
  have hp := bruhatRegularizedAction_apply (μ(F)) τ hτ φ f
  have he := congrArg (fun z : PettisWeakCompletion W₂(F) ↦
    (show Module.Dual ℂ (StrongDual ℂ W₂(F)) from z) Λ) hp.2
  change Λ (hardySobolevTestAction (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂ φ f) =
    ∫ g, Λ (φ.val g • τ g f) ∂μ(F) at he
  rw [he, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change Λ (φ.val g • τ₂(F) g f) = φ.val g * η g * Λ f
  rw [map_smul, eig]
  simp only [smul_eq_mul, mul_assoc]


private theorem extraWeight_test_vector (φ : BruhatCompactSupport C𝔽(ℚ)) (hφ : Continuous φ.val) :
    ∃ f : W₂(ℚ), (f : C𝔽(ℚ) → ℂ) =ᵐ[μ(ℚ)] φ.val := by
  let ν := (μ(ℚ)).withDensity fun g ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 2 (logNorm(ℚ) g))
  let : IsLocallyFiniteMeasure ν := by
    simpa only [neg_zero] using sobolevKernelWeight_locallyFinite (F := ℚ) 0 2
  have hmem : MemLp φ.val 2 ν := hφ.memLp_of_hasCompactSupport φ.property.2
  have hac : μ(ℚ) ≪ ν := by simpa only [neg_zero] using extraWeight_haar_ac.1
  exact ⟨hmem.toLp _, hac.ae_eq hmem.coeFn_toLp⟩


private theorem extraWeight_jet_pair (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ))
    (j : SpectralLineJetIndex χ (1/2) 2) (f : W₂(ℚ)) :
    spectralSobolevPairing (F := ℚ) f ((spectralLineJet_memLp χ hs j).toLp _) =
      ∫ g, f g * η(χ, j) g ∂μ(ℚ) := by
  change (∫ g, f g * ((spectralLineJet_memLp χ hs j).toLp _ : C𝔽(ℚ) → ℂ) g ∂μ(ℚ)) = _
  have hac : μ(ℚ) ≪ (μ(ℚ)).withDensity (fun g ↦ ENNReal.ofReal
      ((intervalSobolevDensity 0 0 2 (logNorm(ℚ) g))⁻¹)) := by
    simpa only [neg_zero] using extraWeight_haar_ac.2
  apply integral_congr_ae
  filter_upwards [hac.ae_le (MemLp.coeFn_toLp (spectralLineJet_memLp χ hs j))] with g hg
  rw [hg]
  simp only [spectralZeroJet, extraWeight_jet_order_zero j, pow_zero, mul_one, Complex.ofReal_zero, zero_add]

private theorem extraWeight_mem_of_projected_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (N : Submodule ℂ E)
    [N.HasOrthogonalProjection] (B : E →L[ℂ] E)
    (h : N.orthogonal.starProjection.comp B = 0) (f : E) : B f ∈ N := by
  have hz : N.orthogonal.starProjection (B f) = 0 := DFunLike.congr_fun h f
  have hn := (N.orthogonal.starProjection_apply_eq_zero_iff).mp hz
  rwa [N.orthogonal_orthogonal] at hn

private theorem extraWeight_pair_vanish
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : IsSpectralBasepointChoice χ)
    (j : SpectralLineJetIndex χ (1/2) 2) (v : W₂(ℚ)) (hv : v ∈ Θ₂(ℚ)) :
    (∫ g, v g * η(χ, j) g ∂μ(ℚ)) = 0 :=
  (extraWeight_jet_pair χ j v).symm.trans
    (((spectralLineJet_commonKernel (a := (1/2 : ℝ)) χ hχ hs v).mp hv) j)

private theorem extraWeight_nonzero_line (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ))
    (hχ : IsSpectralBasepointChoice χ) (j : SpectralLineJetIndex χ (1/2) 2) :
    ∃ φ : BruhatCompactSupport C𝔽(ℚ), (Θ₂(ℚ)).orthogonal.starProjection.comp (A₂(ℚ, φ)) ≠ 0 := by
  let θ := η(χ,j)
  with_reducible refine (extraWeight_test_nonzero (F := ℚ) θ).elim fun φ htest ↦ ?_
  have hφ := htest.2
  with_reducible refine (extraWeight_test_vector φ htest.1).elim fun f hf ↦ ?_
  with_reducible refine (spectralLineJet_functional (a := (1/2 : ℝ)) χ hs j).elim fun Λ hL ↦ ?_
  have hΛ := hL.1
  have hΛeval (v : W₂(ℚ)) : Λ v = ∫ g, v g * θ g ∂μ(ℚ) := by
    simpa only [spectralZeroJet, extraWeight_jet_order_zero j, pow_zero, mul_one,
      Complex.ofReal_zero, zero_add, θ] using (hΛ v).2
  have hn : Λ f ≠ 0 := by
    rw [hΛeval, integral_congr_ae (hf.mono fun g hg ↦ congrArg (· * θ g) hg)]
    exact hφ
  refine ⟨φ, fun h ↦ ?_⟩
  have hΘ : A₂(ℚ, φ) f ∈ Θ₂(ℚ) := extraWeight_mem_of_projected_zero (Θ₂(ℚ)) (A₂(ℚ, φ)) h f
  have hzero := extraWeight_pair_vanish χ hχ j (A₂(ℚ, φ) f) hΘ
  have heq : Λ (A₂(ℚ, φ) f) = (∫ g, φ.val g * θ g ∂μ(ℚ)) * Λ f :=
    (extraWeight_convolution_eigen (F := ℚ) θ Λ hΛeval).2 φ f
  apply (mul_ne_zero hφ hn)
  exact heq.symm.trans ((hΛeval (A₂(ℚ, φ) f)).trans hzero)

private theorem extraWeight_projected_nonzero :
    ∃ φ : BruhatCompactSupport C𝔽(ℚ),
      (spectralProjection (F := ℚ) (1/2) h₀ hs₂).comp (A(ℚ, h₀, hs₂, φ)) ≠ 0 := by
  refine extraWeight_basepoint_jet.elim fun χ hχ ↦ ?_
  with_reducible refine (extraWeight_nonzero_line χ hχ.1 hχ.2.some).elim fun φ hφ ↦ ?_
  have h (l : ℝ) (hl : l ≤ 0) (he : l = 0) :
      (globalThetaSobolev ℚ (1/2) hl hs₂).orthogonal.starProjection.comp
        (hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) l 0 2 hl hs₂ φ) ≠ 0 := by subst l; exact hφ
  exact ⟨φ, h (-0) (hStrip(h₀)) neg_zero⟩

end

/-- Paper: (10.4.3.25), p. 470. Over the rationals at Sobolev exponent two,
the first certified positive zeta ordinate and a compact Bruhat test give
a nonzero spectral convolution. A kernel and its printed weighted transpose
cannot represent the same nonzero operator: swapping the variables twice
would fix the kernel while multiplying it by two reciprocal weights whose
product is strictly less than one almost everywhere. -/
theorem Printed.spectralLineKernel_extraWeight_false :
    ¬ Printed.spectralLineKernel_extraWeight := by
  intro hall
  obtain ⟨φ, hφ⟩ := extraWeight_projected_nonzero
  obtain ⟨K, hK, hrep⟩ := hall ℚ (1 / 2) 2 (by norm_num) (by norm_num) φ
  exact hφ (extraWeight_printed_operator_zero K _ hK ((hrep kS(K)).2 rfl))

end ExtraKernelWeight

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, second formula. The cutoff
spectral function is claimed to represent the geometric truncation.
The two reciprocal weights account for (10.4.3.26) and (10.4.3.30). -/
def Printed.spectralLineTruncatedKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ φ : BruhatCompactSupport C𝔽(F),
        let B := (spectralProjection (F := F) a h₀ hs₀(hs)).comp (A(F, h₀, hs₀(hs), φ))
        ∃ K : tensor(F, 0, s), sobolevProjectiveKernelOperator (F := F) h₀ hs₀(hs) K = B ∧
          IsSobolevHilbertSchmidtKernel (geometricTruncatedConvolution a h₀ hs₀(hs) hρ φ)
            (printedWeight(F, 0, s, ρ, printedClass(F, 0, s, h₀, hs₀(hs), K)))

section GeometricKernelCounterexample

local notation "C" => C𝔽(ℚ)
local notation "m" => m𝔽(ℚ)
local notation "μC" => μ(ℚ)
local notation "L" => logNorm(ℚ)
local notation "d(" α ")" => w(ℚ, α, 2)
local notation "νp(" α ")" => ν(ℚ, α, 2)
local notation "νm(" α ")" => ν'(ℚ, α, 2)
local notation "W₂(" α ")" => W(ℚ, α, 2)
local notation "hs₂" => (show (0 : ℝ) ≤ 2 by norm_num)

/-- To the right of the line of real part one, the strip jet family is
empty and its common kernel is the entire Sobolev space. -/
private theorem geometricKernel_theta_top {a α : ℝ} (hα : 0 ≤ α) (ha : 1 < a - α) :
    globalThetaSobolev ℚ a (hStrip(hα)) hs₂ = ⊤ := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  have hn (j : SpectralStripJetIndex χ a α 2) : False := by
    let z : ℂ := (a + j.val.2.1 : ℝ) + (j.val.2.2.1 : ℂ) * Complex.I
    let θ := χ j.val.1
    obtain ⟨hj, hp⟩ := j.mem_strip_order_pos hα
    have hz : 1 < z.re := by
      have hleft := hj.1
      simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith
    obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec θ
    change 0 < meromorphicOrderAt (continuedCompletedHeckeL θ) z at hp
    exact hz.not_gt (completedHeckeL_continuation_zeros θ _ hL hEq (zero_lt_one.trans hz) hp)
  apply top_unique
  intro u _
  exact (spectralStripJet_commonKernel (a := a) χ hχ hα hs₂ u).2 (fun j ↦ (hn j).elim)

/-- The spectral projection vanishes when the strip lies to the right of one. -/
private theorem geometricKernel_projection_zero {a α : ℝ} (hα : 0 ≤ α) (ha : 1 < a - α) :
    spectralProjection (F := ℚ) a hα hs₂ = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  let N := globalThetaSobolev ℚ a (hStrip(hα)) hs₂
  let v := spectralProjection (F := ℚ) a hα hs₂ u
  have hv : v ∈ N.orthogonal := N.orthogonal.starProjection_apply_mem u
  have hbot : N.orthogonal = ⊥ := by
    change (globalThetaSobolev ℚ a (hStrip(hα)) hs₂).orthogonal = ⊥
    rw [geometricKernel_theta_top hα ha, Submodule.top_orthogonal_eq_bot]
  rw [hbot] at hv
  change v = 0
  rwa [Submodule.mem_bot] at hv

private theorem geometricKernel_density (α : ℝ) (g : C) :
    d(α) g = max (Real.exp (2 * -α * L g)) (Real.exp (2 * α * L g)) * (1 + L g ^ 2) := by
  norm_num [intervalSobolevDensity]

private theorem geometricKernel_density_continuous (α : ℝ) : Continuous d(α) := by
  rw [funext (geometricKernel_density α)]
  have hn : Continuous (fun g : C ↦ (((ideleClassNorm ℚ g).val : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  have hlog : Continuous L := hn.log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  exact ((Real.continuous_exp.comp (continuous_const.mul hlog)).max
    (Real.continuous_exp.comp (continuous_const.mul hlog))).mul
    (continuous_const.add (hlog.pow 2))

private theorem geometricKernel_haar_ac (α : ℝ) :
    μC ≪ νp(α) ∧ μC ≪ νm(α) := by
  have hp (g : C) : 0 < d(α) g := by rw [geometricKernel_density]; positivity
  refine ⟨?_, ?_⟩
  · exact withDensity_absolutelyContinuous'
      (geometricKernel_density_continuous α).measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (hp g)).ne')
  · exact withDensity_absolutelyContinuous'
      (geometricKernel_density_continuous α).measurable.inv.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hp g))).ne')

/-- A smooth cutoff is a compact Bruhat test. Using its own Sobolev vector
as input exhibits a nonzero cutoff of its convolution action. -/
private theorem geometricKernel_cutoff_convolution_nonzero {α : ℝ} (hα : 0 ≤ α) :
    ∃ (ρ : C → ℝ) (hρ : IsModulatedCutoff m 2 (1 / 4) ρ)
      (φ : BruhatCompactSupport C),
      (modulatedCutoffOperator m νp(α) hρ).comp (A(ℚ, hα, hs₂, φ)) ≠ 0 := by
  let hm : IsModulation m := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  have hsurj : Surjective m := by
    intro q
    exact ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ q),
      canonicalIdeleNormSection_rightInverse ℚ q⟩
  obtain ⟨ρ, hρ⟩ := exists_smoothModulatedCutoff_radius_two m hm hsurj
  -- The proper-norm compactness calculation follows the conjugate-weight refutation in §10.3.
  have hK : HasCompactSupport ρ := by
    let e := Nonneg.unitsHomeomorphPos ℝ
    have hc : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc (2⁻¹ : ℝ) 2) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr]
      · exact isCompact_Icc
      · intro r hr
        exact (by norm_num : (0 : ℝ) < 2⁻¹).trans_le hr.1
    exact (hm.1.isCompact_preimage (e.isCompact_preimage.mpr hc)).of_isClosed_subset
      (isClosed_tsupport ρ) hρ.1.support_subset
  let b (g : C) : ℂ := ρ g
  have hbc : Continuous b := Complex.continuous_ofReal.comp hρ.continuous
  have hbK : HasCompactSupport b := hK.comp_left Complex.ofReal_zero
  let φ : BruhatCompactSupport C := ⟨b, (mem_bruhatSmoothSubmodule_iff _).mpr hρ.2, hbK⟩
  have h1 : ρ 1 = 1 := IsModulatedCutoff.apply_one m hρ.1 (by norm_num) (by norm_num)
  let : IsLocallyFiniteMeasure νp(α) := sobolevKernelWeight_locallyFinite (F := ℚ) α 2
  have hb : MemLp b 2 νp(α) := hbc.memLp_of_hasCompactSupport hbK
  let u : W₂(α) := hb.toLp b
  let Aφ := A(ℚ, hα, hs₂, φ)
  let G := (modulatedCutoffOperator m νp(α) hρ.1).comp Aφ
  refine ⟨ρ, hρ.1, φ, fun hG ↦ ?_⟩
  have hu : (u : C → ℂ) =ᵐ[μC] b := (geometricKernel_haar_ac α).1.ae_le hb.coeFn_toLp
  have hconv (x : C) :
      lcaConvolution μC φ.val u x = (∫ g, ρ g * ρ (g⁻¹ * x) ∂μC : ℝ) := by
    unfold lcaConvolution
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    have he (g : C) : x / g = g⁻¹ * x := by rw [div_eq_mul_inv, mul_comm]
    have hh := (Measure.measurePreserving_div_left μC x).quasiMeasurePreserving.ae_eq_comp hu
    filter_upwards [hh] with g hg
    change u (x / g) = b (x / g) at hg
    rw [he] at hg
    rw [hg, Complex.ofReal_mul]
  have hAe : (Aφ u : C → ℂ) =ᵐ[μC] fun x ↦
      ((∫ g, ρ g * ρ (g⁻¹ * x) ∂μC : ℝ) : ℂ) :=
    (hardySobolevTestAction_apply μC m (-α) α 2 (hStrip(hα)) hs₂ φ u).trans (ae_of_all μC hconv)
  have hmulAe := (geometricKernel_haar_ac α).1.ae_le
    (modulatedCutoffOperator_apply m νp(α) hρ.1 (Aφ u))
  have hzero : (G u : C → ℂ) =ᵐ[μC] 0 := by
    change G = 0 at hG
    rw [hG, zero_apply]
    exact (geometricKernel_haar_ac α).1.ae_le (Lp.coeFn_zero ℂ 2 νp(α))
  have hvanish : ∀ᵐ x ∂μC, ρ x * (∫ g, ρ g * ρ (g⁻¹ * x) ∂μC) = 0 := by
    filter_upwards [hAe, hmulAe, hzero] with x hAx hMx hZx
    change (modulatedCutoffOperator m νp(α) hρ.1 (Aφ u) : C → ℂ) x = 0 at hZx
    rw [hMx, hAx, ← Complex.ofReal_mul] at hZx
    exact Complex.ofReal_eq_zero.mp hZx
  let U := {x : C | 0 < ρ x}
  have hU : IsOpen U := isOpen_lt continuous_const hρ.continuous
  have hU1 : (1 : C) ∈ U := by change 0 < ρ 1; rw [h1]; norm_num
  have hpos (x : C) (hx : x ∈ U) : 0 < ∫ g, ρ g * ρ (g⁻¹ * x) ∂μC := by
    have hc : Continuous (fun g : C ↦ ρ g * ρ (g⁻¹ * x)) :=
      hρ.continuous.mul (hρ.continuous.comp (continuous_inv.mul continuous_const))
    apply hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero hK.mul_right
      (fun g ↦ mul_nonneg (hρ.1.nonneg g) (hρ.1.nonneg _)) (x := 1)
    simpa only [h1, inv_one, one_mul] using (ne_of_gt hx)
  have hnot : ∀ᵐ x ∂μC, x ∉ U := hvanish.mono fun x hz hx ↦ (mul_pos hx (hpos x hx)).ne' hz
  have hnull : μC U = 0 := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hnot
  exact (hU.measure_pos μC ⟨1, hU1⟩).ne' hnull

local notation "printedK(" α ", " hα ", " K ")" =>
  Lp.compMeasurePreserving Prod.swap
    (Measure.measurePreserving_swap (μ := νm(α)) (ν := νp(α)))
    (sobolevProjectiveKernelClass (F := ℚ) hα hs₂ K)

/-- The mixed Sobolev kernel of the zero spectral operator is zero. The
positive densities allow this to be read in the positive product measure. -/
private theorem geometricKernel_printed_zero {α : ℝ} (hα : 0 ≤ α)
    (K : tensor(ℚ, α, 2))
    (hK : sobolevProjectiveKernelOperator (F := ℚ) hα hs₂ K = 0)
    (r : C → ℝ) :
    printedWeight(ℚ, α, 2, r, printedK(α, hα, K))
      =ᵐ[(νp(α)).prod (νp(α))] 0 := by
  have hZero : (0 : Lp ℂ 2 ((νp(α)).prod (νm(α)))) =
      sobolevProjectiveKernelClass (F := ℚ) hα hs₂ K := by
    apply (sobolevProjectiveKernelClass_spec (F := ℚ) hα hs₂ K 0).1
    rw [hK]
    intro u
    have h0 := Lp.coeFn_zero ℂ 2 ((νp(α)).prod (νm(α)))
    have hAc : (μC).prod (μC) ≪ (νp(α)).prod (νm(α)) :=
      (geometricKernel_haar_ac α).1.prod (geometricKernel_haar_ac α).2
    have hrow := Measure.ae_ae_of_ae_prod (hAc.ae_le h0)
    have hzero := (geometricKernel_haar_ac α).1.ae_le (Lp.coeFn_zero ℂ 2 νp(α))
    filter_upwards [hrow, hzero] with x hx hzx
    have hh : (fun y ↦ (0 : Lp ℂ 2 ((νp(α)).prod (νm(α)))) (x, y) * u y) =ᵐ[μC] (0 : C → ℂ) := by
      filter_upwards [hx] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact ⟨(integrable_zero C ℂ μC).congr hh.symm, hzx.trans (by rw [integral_congr_ae hh]; simp)⟩
  have hk : printedK(α, hα, K) = 0 := by
    rw [← hZero, map_zero]
  have hAc : (νp(α)).prod (νp(α)) ≪ (νm(α)).prod (νp(α)) :=
    ((withDensity_absolutelyContinuous μC _).trans (geometricKernel_haar_ac α).2).prod
      (Measure.AbsolutelyContinuous.refl _)
  rw [hk]
  filter_upwards [hAc.ae_le (Lp.coeFn_zero ℂ 2 ((νm(α)).prod (νp(α))))] with x hx
  rw [hx]
  simp

/-- A representative vanishing almost everywhere gives the zero operator. -/
private theorem geometricKernel_operator_zero {α : ℝ}
    (B : W₂(α) →L[ℂ] W₂(α)) (k : C × C → ℂ)
    (hk : k =ᵐ[(νp(α)).prod (νp(α))] 0)
    (hB : IsSobolevHilbertSchmidtKernel B k) : B = 0 := by
  obtain ⟨hm, hrep⟩ := hB
  obtain ⟨h0, hzero⟩ := isSobolevHilbertSchmidtKernel_zero (F := ℚ) (α := α) (s := 2)
  have he : hm.toLp k = h0.toLp 0 := MemLp.toLp_congr _ _ hk
  rw [he] at hrep
  exact hrep.symm.trans hzero

private theorem geometricKernel_line_eq {r : C → ℝ}
    (hr : IsModulatedCutoff m 2 (1 / 4) r) (φ : BruhatCompactSupport C) :
    (modulatedCutoffOperator m νp(0) hr).comp (A(ℚ, h₀, hs₂, φ)) =
      geometricTruncatedConvolution (F := ℚ) 2 h₀ hs₂ hr φ := by
  apply ContinuousLinearMap.ext
  intro u
  symm
  apply geometricTruncatedConvolution_apply_of_mem
  rw [geometricKernel_theta_top h₀ (by norm_num : (1 : ℝ) < 2 - 0)]
  exact Submodule.mem_top

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471. Over the rationals on the
zero-free line a = 2, take s = 2 and the smooth cutoff of radius two and
width one quarter. The spectral kernel vanishes. The cutoff's
self-convolution gives a nonzero geometric truncation. -/
theorem Printed.spectralLineTruncatedKernel_geometric_false :
    ¬ Printed.spectralLineTruncatedKernel_geometric := by
  intro hall
  obtain ⟨r, hr, φ, hne⟩ := geometricKernel_cutoff_convolution_nonzero h₀
  obtain ⟨K, hK, hrep⟩ := hall ℚ 2 2 (by norm_num) (by norm_num)
    2 (1 / 4) r hr (by norm_num) (by norm_num) φ
  have hspec := geometricKernel_projection_zero h₀ (a := 2) (by norm_num)
  have hk : sobolevProjectiveKernelOperator (F := ℚ) h₀ hs₂ K = 0 := by
    rw [hK, hspec]
    exact ContinuousLinearMap.zero_comp _
  have hG := geometricKernel_operator_zero _ _ (geometricKernel_printed_zero h₀ K hk r) hrep
  exact hne ((geometricKernel_line_eq hr φ).trans hG)


-- TODO(paper-gap): (10.4.3.45) applies the ambient kernel map to the
-- quotient tensor from (10.4.3.42). The bounds in (10.4.3.40) and in
-- (10.4.3.42) use N_s, while (10.4.3.38) and (10.4.3.43) use N_{I,s}.
-- There is no single literal typed assertion fixing both choices. Any
-- ambient limit of the transposed rectangles has spectral output, also
-- when the quotient tensors are transported by the map of (10.4.3.20).

/-- Paper: Theorem 10.4.3.5(3), p. 473. A necessary consequence of the
operator identity is that convolution after spectral projection has
spectral range, since every displayed rectangle has spectral output.
Deviation: This records a consequence independent of the ambiguous index
bounds and tensor type in the display. -/
def spectralStripTransposeLimit_rangeConsequence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F)),
      ∀ u : W(F, α, s),
        A(F, hα, hs₀(hs), φ) (spectralProjection a hα hs₀(hs) u) ∈
          (globalThetaSobolev F a hStrip(hα) hs₀(hs)).orthogonal

/-- A unitary character times an imaginary power of the norm has absolute value one. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_norm
    (θ : PontryaginDual C𝔽(ℚ)) (t : ℝ) (g : C𝔽(ℚ)) :
    ‖ideleClassNormTwist θ ((t : ℂ) * Complex.I) g‖ = 1 := by
  change ‖(θ g : ℂ) * (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
    (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g)))]
  simp

/-- Every unitary norm twist is a continuous functional on the rational line
Sobolev space at exponent two, given by the Haar product integral. A surviving
line jet supplies the square-integrability for the reciprocal weight. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_functional
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (j : SpectralLineJetIndex χ (1 / 2) 2)
    (θ : PontryaginDual C𝔽(ℚ)) (t : ℝ) :
    ∃ Λ : StrongDual ℂ (CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2),
      ∀ f : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2,
        Integrable (fun g ↦ f g * ideleClassNormTwist θ ((t : ℂ) * Complex.I) g) μ(ℚ) ∧
          Λ f = ∫ g, f g * ideleClassNormTwist θ ((t : ℂ) * Complex.I) g ∂μ(ℚ) := by
  have hjet := spectralLineJet_memLp χ one_lt_two j
  have hmem : MemLp (ideleClassNormTwist θ ((t : ℂ) * Complex.I)) 2
      ((μ(ℚ)).withDensity fun g ↦
        ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm(ℚ) g))⁻¹) := by
    refine hjet.congr_norm
      (ideleClassNormTwist θ ((t : ℂ) * Complex.I)).continuous.aestronglyMeasurable
      (ae_of_all _ fun g ↦ ?_)
    rw [spectralStripTransposeLimit_rangeConsequence_false_norm]
    simp only [spectralZeroJet, extraWeight_jet_order_zero j, pow_zero, mul_one,
      Complex.ofReal_zero, zero_add]
    exact spectralStripTransposeLimit_rangeConsequence_false_norm _ _ g
  have hs0 : (0 : ℝ) ≤ 2 := by norm_num
  have hdual := modulatedIntervalSobolev_dual m𝔽(ℚ)
    ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ μ(ℚ) 0 0 2 le_rfl hs0
  let T := hdual.exists.choose
  have hT := hdual.exists.choose_spec
  let u : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2 true := hmem.toLp _
  have hac : μ(ℚ) ≪ (μ(ℚ)).withDensity (fun g ↦ ENNReal.ofReal
      ((intervalSobolevDensity 0 0 2 (logNorm(ℚ) g))⁻¹)) := by
    simpa only [neg_zero] using extraWeight_haar_ac.2
  have hae : (u : C𝔽(ℚ) → ℂ) =ᵐ[μ(ℚ)] ideleClassNormTwist θ ((t : ℂ) * Complex.I) :=
    hac.ae_le (MemLp.coeFn_toLp hmem)
  refine ⟨T.symm u, fun f ↦ ?_⟩
  have h := hT (T.symm u) f
  have hTu : T (T.symm u) = u := T.apply_symm_apply u
  have hc : (fun g ↦ f g * T (T.symm u) g) =ᵐ[μ(ℚ)]
      fun g ↦ f g * ideleClassNormTwist θ ((t : ℂ) * Complex.I) g := by
    rw [hTu]
    exact hae.mono fun g hg ↦ congrArg (f g * ·) hg
  exact ⟨h.1.congr hc, h.2.trans (integral_congr_ae hc)⟩

/-- The radius-two cutoff divided by a quasi-character is a compact Bruhat test. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_test
    (η : QuasiCharacter C𝔽(ℚ)) :
    ∃ (φ : BruhatCompactSupport C𝔽(ℚ)) (b : C𝔽(ℚ) → ℝ),
      Continuous b ∧ HasCompactSupport b ∧ (∀ g, 0 ≤ b g) ∧
        (∀ g, ((ideleClassNorm ℚ g).val : ℝ) = 3 / 2 → b g = 1) ∧
        ∀ g, φ.val g * η g = (b g : ℂ) := by
  let hm : IsModulation m𝔽(ℚ) :=
    ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  have hms : Surjective m𝔽(ℚ) := by
    intro q
    exact ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ q),
      canonicalIdeleNormSection_rightInverse ℚ q⟩
  obtain ⟨b, hb⟩ := exists_smoothModulatedCutoff_radius_two m𝔽(ℚ) hm hms
  have hbc : HasCompactSupport b := by
    let e := Nonneg.unitsHomeomorphPos ℝ
    have hS : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc (2⁻¹ : ℝ) 2) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr]
      · exact isCompact_Icc
      · intro r hr
        exact (by norm_num : (0 : ℝ) < 2⁻¹).trans_le hr.1
    exact (hm.1.isCompact_preimage (e.isCompact_preimage.mpr hS)).of_isClosed_subset
      (isClosed_tsupport b) hb.1.support_subset
  have hbC : HasCompactSupport (fun g ↦ (b g : ℂ)) := hbc.comp_left Complex.ofReal_zero
  let b₀ : BruhatCompactSupport C𝔽(ℚ) := ⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hb.2, hbC⟩
  let B := bruhatCompactSupportToModulatedExponentialDecay m𝔽(ℚ) univ hm hms b₀
  let ηInv := η.comp (ContinuousMonoidHom.inv _)
  obtain ⟨E, hE⟩ := modulatedExponentialDecay_mul_quasiCharacter m𝔽(ℚ) hm hms ηInv
  have hEB (g : C𝔽(ℚ)) : (E B).val g = (η g)⁻¹ * (b g : ℂ) :=
    (hE B g).trans (by change η g⁻¹ * (b g : ℂ) = _; rw [map_inv])
  have hBs : HasCompactSupport (E B).val := by
    rw [funext hEB]
    exact hbC.mul_left (f := fun g ↦ (η g)⁻¹)
  let φ : BruhatCompactSupport C𝔽(ℚ) :=
    ⟨_, modulatedExponentialDecay_mem_bruhatSmooth m𝔽(ℚ) univ univ_nonempty (E B), hBs⟩
  have hηne (g : C𝔽(ℚ)) : η g ≠ 0 := ((Group.isUnit g).map η).ne_zero
  refine ⟨φ, b, hb.continuous, hbc, hb.1.nonneg, fun g hg ↦ ?_, fun g ↦ ?_⟩
  · apply hb.1.eq_one
    change ((ideleClassNorm ℚ g).val : ℝ) ∈ Icc ((2 : ℝ)⁻¹ + 1 / 4) (2 - 1 / 4)
    rw [hg]
    norm_num
  · change (E B).val g * η g = _
    rw [hEB, mul_right_comm, inv_mul_cancel₀ (hηne g), one_mul]

/-- Two norm twists of one unitary character whose ordinates differ by a positive
amount at most one are separated by a compact Bruhat test. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_separate
    (θ : PontryaginDual C𝔽(ℚ)) (t δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ φ : BruhatCompactSupport C𝔽(ℚ),
      (∫ g, φ.val g * ideleClassNormTwist θ ((t : ℂ) * Complex.I) g ∂μ(ℚ)) ≠
        ∫ g, φ.val g * ideleClassNormTwist θ (((t + δ : ℝ) : ℂ) * Complex.I) g ∂μ(ℚ) := by
  obtain ⟨φ, b, hbc, hbs, hb0, hb1, hφ⟩ :=
    spectralStripTransposeLimit_rangeConsequence_false_test
      (ideleClassNormTwist θ ((t : ℂ) * Complex.I))
  refine ⟨φ, fun heq ↦ ?_⟩
  let r (g : C𝔽(ℚ)) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  have hr (g : C𝔽(ℚ)) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hrc : Continuous r := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)
  have hlog : Continuous fun g ↦ δ * Real.log (r g) :=
    continuous_const.mul (hrc.log fun g ↦ (hr g).ne')
  let k (g : C𝔽(ℚ)) : ℂ := Complex.exp (((δ * Real.log (r g) : ℝ) : ℂ) * Complex.I)
  have hk : Continuous k :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hlog).mul continuous_const)
  have htw (g : C𝔽(ℚ)) : φ.val g * ideleClassNormTwist θ (((t + δ : ℝ) : ℂ) * Complex.I) g =
      (b g : ℂ) * k g := by
    rw [← hφ g, mul_assoc]
    congr 1
    change (θ g : ℂ) * ((r g : ℝ) : ℂ) ^ (((t + δ : ℝ) : ℂ) * Complex.I) =
      (θ g : ℂ) * ((r g : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) * k g
    have hne : ((r g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr g).ne'
    rw [mul_assoc, Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
      ← Complex.exp_add, ← Complex.ofReal_log (hr g).le]
    congr 2
    push_cast
    ring
  have hbC : Continuous fun g ↦ (b g : ℂ) := Complex.continuous_ofReal.comp hbc
  have hbCs : HasCompactSupport fun g ↦ (b g : ℂ) := hbs.comp_left Complex.ofReal_zero
  have hi0 : Integrable (fun g ↦ (b g : ℂ)) μ(ℚ) := hbC.integrable_of_hasCompactSupport hbCs
  have hi1 : Integrable (fun g ↦ (b g : ℂ) * k g) μ(ℚ) :=
    (hbC.mul hk).integrable_of_hasCompactSupport hbCs.mul_right
  let h (g : C𝔽(ℚ)) : ℝ := b g * (1 - Real.cos (δ * Real.log (r g)))
  have hh : Continuous h := hbc.mul (continuous_const.sub (Real.continuous_cos.comp hlog))
  have hpos : 0 < ∫ g, h g ∂μ(ℚ) := by
    obtain ⟨g₀, hg₀⟩ : ∃ g₀ : C𝔽(ℚ), r g₀ = 3 / 2 := by
      let q : ℝ≥0ˣ := Units.mk0 (3 / 2) (by norm_num)
      refine ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ q), ?_⟩
      have hq : ideleClassNorm ℚ (QuotientGroup.mk (canonicalIdeleNormSection ℚ q)) = q :=
        canonicalIdeleNormSection_rightInverse ℚ q
      change ((ideleClassNorm ℚ (QuotientGroup.mk (canonicalIdeleNormSection ℚ q))).val : ℝ) =
        3 / 2
      rw [hq]
      simp [q]
    apply hh.integral_pos_of_hasCompactSupport_nonneg_ne_zero hbs.mul_right
      (fun g ↦ mul_nonneg (hb0 g) (sub_nonneg.mpr (Real.cos_le_one _))) (x := g₀)
    change b g₀ * (1 - Real.cos (δ * Real.log (r g₀))) ≠ 0
    rw [hb1 g₀ hg₀, one_mul, hg₀]
    have hl0 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
    have hl1 : Real.log (3 / 2 : ℝ) ≤ 1 / 2 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hx0 : 0 < δ * Real.log (3 / 2 : ℝ) := mul_pos hδ hl0
    have hx1 : δ * Real.log (3 / 2 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    intro hc
    exact hx0.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hx1).mp
      (sub_eq_zero.mp hc).symm)
  have hre : (∫ g, ((b g : ℂ) - (b g : ℂ) * k g) ∂μ(ℚ)).re = ∫ g, h g ∂μ(ℚ) := by
    refine (integral_re (hi0.sub hi1)).symm.trans
      (integral_congr_ae (ae_of_all _ fun g ↦ ?_))
    change ((b g : ℂ) - (b g : ℂ) * k g).re = b g * (1 - Real.cos (δ * Real.log (r g)))
    rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re, Complex.exp_ofReal_mul_I_re]
    ring
  rw [integral_sub hi0 hi1] at hre
  simp_rw [htw, hφ] at heq
  rw [heq, sub_self, Complex.zero_re] at hre
  exact hpos.ne hre

/-- Let a closed subspace be the common kernel of a family of functionals, and let a
vector be annihilated by all of them but one. Its projection to the orthogonal
complement has the same value under the remaining functional. Every operator that
scales each functional and keeps the projection in the orthogonal complement has
the projection as an eigenvector. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_eigen {E J : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (N : Submodule ℂ E)
    [N.HasOrthogonalProjection] (Λ : J → StrongDual ℂ E)
    (hN : ∀ f, (∀ j, Λ j f = 0) → f ∈ N) (hN' : ∀ f, f ∈ N → ∀ j, Λ j f = 0)
    (i : J) (x : E) (hx0 : ∀ j, j ≠ i → Λ j x = 0) :
    Λ i (N.orthogonal.starProjection x) = Λ i x ∧
      ∀ (B : E →L[ℂ] E) (c : J → ℂ), (∀ j f, Λ j (B f) = c j * Λ j f) →
        B (N.orthogonal.starProjection x) ∈ N.orthogonal →
        B (N.orthogonal.starProjection x) = c i • N.orthogonal.starProjection x := by
  have hxe : x - N.orthogonal.starProjection x ∈ N := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := N.orthogonal) x
    rwa [N.orthogonal_orthogonal] at h
  have hΛ (j : J) : Λ j (N.orthogonal.starProjection x) = Λ j x := by
    have h := hN' _ hxe j
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  refine ⟨hΛ i, fun B c hB hH ↦ ?_⟩
  have hd : B (N.orthogonal.starProjection x) - c i • N.orthogonal.starProjection x ∈
      N.orthogonal :=
    N.orthogonal.sub_mem hH (N.orthogonal.smul_mem _ (Submodule.starProjection_apply_mem _ _))
  have hdN : B (N.orthogonal.starProjection x) - c i • N.orthogonal.starProjection x ∈ N := by
    apply hN
    intro j
    rw [map_sub, map_smul, hB, hΛ, smul_eq_mul]
    by_cases hj : j = i
    · rw [hj, sub_self]
    · rw [hx0 j hj, mul_zero, mul_zero, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hdN hd))

/-- If every convolution after the spectral projection has spectral range, the
projected interpolant of the certified critical zero is an eigenvector of all
convolutions, with unit pairing against its own norm twist. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_eigenvector
    (H : ∀ (φ : BruhatCompactSupport C𝔽(ℚ))
      (u : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2),
      hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) 0 0 2 h₀ hs₂ φ
        ((globalThetaSobolev ℚ (1 / 2) h₀ hs₂).orthogonal.starProjection u) ∈
        (globalThetaSobolev ℚ (1 / 2) h₀ hs₂).orthogonal) :
    ∃ (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (i : SpectralLineJetIndex χ (1 / 2) 2)
      (e : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2),
      (∫ g, e g * ideleClassNormTwist (χ i.val.1) ((i.val.2.1 : ℂ) * Complex.I) g ∂μ(ℚ)) = 1 ∧
      ∀ φ : BruhatCompactSupport C𝔽(ℚ),
        hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) 0 0 2 h₀ hs₂ φ e =
          (∫ g, φ.val g * ideleClassNormTwist (χ i.val.1) ((i.val.2.1 : ℂ) * Complex.I) g ∂μ(ℚ)) •
            e := by
  refine extraWeight_basepoint_jet.elim fun χ hχi ↦ hχi.2.elim fun i ↦ ?_
  have hχ := hχi.1
  choose Λ hΛ using fun j : SpectralLineJetIndex χ (1 / 2) 2 ↦
    spectralStripTransposeLimit_rangeConsequence_false_functional χ j (χ j.val.1) j.val.2.1
  have hpair (j : SpectralLineJetIndex χ (1 / 2) 2)
      (f : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2) :
      spectralSobolevPairing (F := ℚ) f ((spectralLineJet_memLp χ one_lt_two j).toLp _) =
        Λ j f :=
    (extraWeight_jet_pair χ j f).trans (hΛ j f).2.symm
  have hK := spectralLineJet_commonKernel (a := (1 / 2 : ℝ)) χ hχ one_lt_two
  with_reducible refine (spectralLineJet_denseInterpolants (a := (1 / 2 : ℝ)) χ hχ
    one_lt_two).elim fun v hv ↦ ?_
  have hv1 := hv.1
  have hv0 := hv.2.1
  have hab := spectralStripTransposeLimit_rangeConsequence_false_eigen
    (globalThetaSobolev ℚ (1 / 2) h₀ hs₂) Λ
    (fun f hf ↦ (hK f).mpr fun j ↦ (hpair j f).trans (hf j))
    (fun f hf j ↦ (hpair j f).symm.trans ((hK f).mp hf j))
    i (v i) (fun j hj ↦ (hpair j (v i)).symm.trans (hv0 i j (Ne.symm hj)))
  refine ⟨χ, i, (globalThetaSobolev ℚ (1 / 2) h₀ hs₂).orthogonal.starProjection (v i), ?_,
    fun φ ↦ ?_⟩
  · exact (hΛ i _).2.symm.trans (hab.1.trans ((hpair i (v i)).symm.trans (hv1 i)))
  · exact hab.2 (hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) 0 0 2 h₀ hs₂ φ)
      (fun j ↦ ∫ g, φ.val g *
        ideleClassNormTwist (χ j.val.1) ((j.val.2.1 : ℂ) * Complex.I) g ∂μ(ℚ))
      (fun j f ↦ (extraWeight_convolution_eigen (F := ℚ) (ideleClassNormTwist (χ j.val.1)
        ((j.val.2.1 : ℂ) * Complex.I)) (Λ j) (fun f ↦ (hΛ j f).2)).2 φ f)
      (H φ (v i))

/-- A common eigenvector of all convolutions, with the eigenvalues of one norm
twist, pairs to zero with every nearby twist of the same character. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_vanish
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (i : SpectralLineJetIndex χ (1 / 2) 2)
    (e : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2)
    (he : ∀ φ : BruhatCompactSupport C𝔽(ℚ),
      hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) 0 0 2 h₀ hs₂ φ e =
        (∫ g, φ.val g * ideleClassNormTwist (χ i.val.1) ((i.val.2.1 : ℂ) * Complex.I) g ∂μ(ℚ)) •
          e)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    AEStronglyMeasurable (fun g ↦ e g * ideleClassNormTwist (χ i.val.1)
        (((i.val.2.1 + δ : ℝ) : ℂ) * Complex.I) g) μ(ℚ) ∧
      (∫ g, e g * ideleClassNormTwist (χ i.val.1)
        (((i.val.2.1 + δ : ℝ) : ℂ) * Complex.I) g ∂μ(ℚ)) = 0 := by
  refine (spectralStripTransposeLimit_rangeConsequence_false_functional χ i (χ i.val.1)
    (i.val.2.1 + δ)).elim fun Λ' hΛ' ↦ ?_
  refine (spectralStripTransposeLimit_rangeConsequence_false_separate (χ i.val.1)
    i.val.2.1 δ hδ hδ1).elim fun φ hφ ↦ ?_
  have h1 := (extraWeight_convolution_eigen (F := ℚ) (ideleClassNormTwist (χ i.val.1)
    (((i.val.2.1 + δ : ℝ) : ℂ) * Complex.I)) Λ' (fun f ↦ (hΛ' f).2)).2 φ e
  have h4 : Λ' (hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) 0 0 2 h₀ hs₂ φ e) =
      (∫ g, φ.val g * ideleClassNormTwist (χ i.val.1) ((i.val.2.1 : ℂ) * Complex.I) g ∂μ(ℚ)) *
        Λ' e :=
    (congrArg Λ' (he φ)).trans (map_smul Λ' _ e)
  have h2 : Λ' e = 0 := by
    by_contra hne
    exact hφ (mul_right_cancel₀ hne (h4.symm.trans h1))
  exact ⟨(hΛ' e).1.aestronglyMeasurable, (hΛ' e).2.symm.trans h2⟩

/-- If the pairings with the norm twists at ordinates decreasing to a limit all
vanish, so does the pairing at the limit ordinate, by dominated convergence. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_limit
    (θ : PontryaginDual C𝔽(ℚ)) (γ : ℝ) (e : C𝔽(ℚ) → ℂ)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun g ↦ e g * ideleClassNormTwist θ
      (((γ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) g) μ(ℚ))
    (hzero : ∀ n : ℕ, (∫ g, e g * ideleClassNormTwist θ
      (((γ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) g ∂μ(ℚ)) = 0) :
    (∫ g, e g * ideleClassNormTwist θ ((γ : ℂ) * Complex.I) g ∂μ(ℚ)) = 0 := by
  by_cases hint :
      Integrable (fun g ↦ e g * ideleClassNormTwist θ ((γ : ℂ) * Complex.I) g) μ(ℚ)
  · have ht : Tendsto (fun n : ℕ ↦ γ + 1 / ((n : ℝ) + 1)) atTop (𝓝 γ) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := γ)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ ↦ ∫ g, e g * ideleClassNormTwist θ
        (((γ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) g ∂μ(ℚ)) atTop
        (𝓝 (∫ g, e g * ideleClassNormTwist θ ((γ : ℂ) * Complex.I) g ∂μ(ℚ))) := by
      refine tendsto_integral_of_dominated_convergence
        (fun g ↦ ‖e g * ideleClassNormTwist θ ((γ : ℂ) * Complex.I) g‖)
        hmeas hint.norm (fun n ↦ ae_of_all _ fun g ↦ ?_) (ae_of_all _ fun g ↦ ?_)
      · rw [norm_mul, norm_mul, spectralStripTransposeLimit_rangeConsequence_false_norm,
          spectralStripTransposeLimit_rangeConsequence_false_norm]
      · refine Tendsto.const_mul _ ?_
        have hc : Continuous fun t : ℝ ↦ ideleClassNormTwist θ ((t : ℂ) * Complex.I) g := by
          change Continuous fun t : ℝ ↦ (θ g : ℂ) *
            (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)
          exact continuous_const.mul ((Complex.continuous_ofReal.mul continuous_const).const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr
              (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g))).ne')))
        exact (hc.tendsto γ).comp ht
    exact tendsto_nhds_unique hlim (by simp_rw [hzero]; exact tendsto_const_nhds)
  · exact integral_undef hint

/-- Over the rationals on the critical line at Sobolev exponent two, the range
consequence fails. The eigenvector of all convolutions that it would produce at
the certified zeta zero pairs to zero with the nearby norm twists, and then with
its own norm twist, against which its pairing is one. -/
private theorem spectralStripTransposeLimit_rangeConsequence_false_line
    (H : ∀ (φ : BruhatCompactSupport C𝔽(ℚ))
      (u : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) 0 0 2),
      hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) 0 0 2 h₀ hs₂ φ
        ((globalThetaSobolev ℚ (1 / 2) h₀ hs₂).orthogonal.starProjection u) ∈
        (globalThetaSobolev ℚ (1 / 2) h₀ hs₂).orthogonal) : False := by
  refine (spectralStripTransposeLimit_rangeConsequence_false_eigenvector H).elim
    fun χ hχ ↦ hχ.elim fun i hi ↦ hi.elim fun e he ↦ ?_
  have hz (n : ℕ) := spectralStripTransposeLimit_rangeConsequence_false_vanish χ i e he.2
    (1 / ((n : ℝ) + 1)) (by positivity)
    ((div_le_one (by positivity)).mpr (le_add_of_nonneg_left n.cast_nonneg))
  exact one_ne_zero (he.1.symm.trans
    (spectralStripTransposeLimit_rangeConsequence_false_limit (χ i.val.1) i.val.2.1 e
      (fun n ↦ (hz n).1) (fun n ↦ (hz n).2)))

/-- Paper: Theorem 10.4.3.5(3), p. 473. Over ℚ use α = 0, s = 4
and a nontrivial zeta zero a + iγ. Its order-zero Riesz vector on the
log-norm line is g(t) = exp(−iγt)/(1+t²)². Every printed finite section
has spectral output. Take the nonzero weighted theta vector q of the
polar-free rational test with finite factor 1_{ℤ̂} and real factor
exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²).
The Fourier transform of (1+t²)⁻² is everywhere positive, so pairing q
with translates of g cannot vanish identically. Choose a smooth bump
of integral one concentrated at such a shift as φ. Then A(φ)g has a
nonzero geometric component, whereas any limit of the printed tensors
has spectral output. -/
theorem spectralStripTransposeLimit_rangeConsequence_false :
    ¬ spectralStripTransposeLimit_rangeConsequence := by
  intro hall
  -- Specialize to ℚ with a = 1/2, α = 0 and s = 2, where only order-zero jets survive.
  -- The interval [-0, 0] is identified with [0, 0] before the line lemma applies.
  have h (l : ℝ) (hl : l ≤ 0) (he : l = 0)
      (H : ∀ (φ : BruhatCompactSupport C𝔽(ℚ))
        (u : CompactIntervalSobolev (μ(ℚ)) logNorm(ℚ) l 0 2),
        hardySobolevTestAction (μ(ℚ)) m𝔽(ℚ) l 0 2 hl hs₂ φ
          ((globalThetaSobolev ℚ (1 / 2) hl hs₂).orthogonal.starProjection u) ∈
          (globalThetaSobolev ℚ (1 / 2) hl hs₂).orthogonal) : False := by
    subst l
    exact spectralStripTransposeLimit_rangeConsequence_false_line H
  exact h (-0) (hStrip(h₀)) neg_zero (hall ℚ (1 / 2) 0 2 (by norm_num) h₀ one_lt_two)

/-- Paper: Theorem 10.4.3.6(2), p. 473, second formula. The cutoff
spectral function is claimed to represent the geometric restriction.
The two reciprocal weights account for (10.4.3.47) and (10.4.3.49).
The tensor is identified by the operator in (10.4.3.45).
Deviation: Interpret the unbound endpoint b using the cited interval [−α, α]. -/
def Printed.spectralStripRestrictionKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ)
      (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ φ : BruhatCompactSupport C𝔽(F),
        let B := (A(F, hα, hs₀(hs), φ)).comp (spectralProjection (F := F) a hα hs₀(hs))
        ∃ K : tensor(F, α, s), sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K = B ∧
          IsSobolevHilbertSchmidtKernel (geometricRestriction a hα hs₀(hs) hρ φ)
            (printedWeight(F, α, s, ρ, printedClass(F, α, s, hα, hs₀(hs), K)))

/-- Paper: Theorem 10.4.3.6(2), p. 473. Over the rationals, take a = 3,
α = 1 and s = 2. The strip lies to the right of one, so its spectral kernel
vanishes. The self-convolution of the smooth cutoff of radius two and
width one quarter gives a nonzero geometric restriction. -/
theorem Printed.spectralStripRestrictionKernel_geometric_false :
    ¬ Printed.spectralStripRestrictionKernel_geometric := by
  intro hall
  have hα : (0 : ℝ) ≤ 1 := by norm_num
  obtain ⟨r, hr, φ, hne⟩ := geometricKernel_cutoff_convolution_nonzero hα
  obtain ⟨K, hK, hrep⟩ := hall ℚ 3 1 2 (by norm_num) hα (by norm_num)
    2 (1 / 4) r hr (by norm_num) (by norm_num) φ
  have ha : (1 : ℝ) < 3 - 1 := by norm_num
  have hk : sobolevProjectiveKernelOperator (F := ℚ) hα hs₂ K = 0 := by
    rw [hK, geometricKernel_projection_zero hα ha]
    exact ContinuousLinearMap.comp_zero _
  have hG := geometricKernel_operator_zero _ _ (geometricKernel_printed_zero hα K hk r) hrep
  apply hne
  refine Eq.trans ?_ hG
  apply ContinuousLinearMap.ext
  intro u
  symm
  apply geometricRestriction_apply_of_mem
  rw [geometricKernel_theta_top hα ha]
  exact Submodule.mem_top

end GeometricKernelCounterexample

end RiemannMasullo
