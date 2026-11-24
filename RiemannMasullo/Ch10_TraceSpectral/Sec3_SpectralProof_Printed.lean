module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.ZetaZeros
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.HardyCriticalLine.CriticalLineZeroInfinitude
import RiemannMasullo.External.ZetaLab.HardyTenZeros.TenZeros
import Mathlib.Logic.Equiv.Nat

/-! # Further assertions in the proofs of §10.3 that are false as printed -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "orderAt(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "lineZeros(" χ ", " a ")" => {t : ℝ | 0 < orderAt(χ, shift(a, t))}
local notation "floorCut(" s ")" => Nat.floor ((s - 1) / 2 + 1)

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
As printed: the smallest interval containing the selected ordinates in each active character
can be enlarged at both ends by a common positive amount while still containing exactly
those zeros on the line. The finite selections are stated one character at a time.
See `spectralConvolutionFiniteSum` and ERRATA F178. -/
def Printed.spectralLineSelection_exists_isolatingInterval : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty),
      (K : Set ℝ) ⊆ lineZeros(χ ω, a) →
      ∃ ε : ℝ, 0 < ε ∧
        Icc (K.min' hK - ε) (K.max' hK + ε) ∩ lineZeros(χ ω, a) = (K : Set ℝ)

/-- Three ordered critical-line zeros of the ordinary Riemann zeta function suffice
for the interval counterexample. This is a finite consequence of Hardy's theorem. -/
private theorem spectralLineSelection_three_zeta_zeros :
    ∃ u v w : ℝ, u < v ∧ v < w ∧ riemannZeta (shift(1 / 2, u)) = 0 ∧
      riemannZeta (shift(1 / 2, v)) = 0 ∧ riemannZeta (shift(1 / 2, w)) = 0 := by
  obtain ⟨ts, hmono, hts⟩ := HardyTenZeros.ten_zeros_on_line_below_fifty
  have hz (k : Fin 10) : riemannZeta (shift(1 / 2, ts k)) = 0 := by
    have h := (hts k).2.2
    push_cast
    exact h
  exact ⟨ts 0, ts 1, ts 2, hmono (by decide), hmono (by decide), hz 0, hz 1, hz 2⟩

/-- On the critical line the order of the trivial rational completed L-function is
a finite natural number, positive exactly at the zeros of ordinary zeta. -/
private theorem spectralLineSelection_zeta_order (t : ℝ) :
    ∃ n : ℕ, orderAt((1 : PontryaginDual C𝔽(ℚ)), shift(1 / 2, t)) = ((n : ℤ) : WithTop ℤ) ∧
      (0 < n ↔ riemannZeta (shift(1 / 2, t)) = 0) := by
  let z : ℂ := shift(1 / 2, t)
  have hre : z.re = 1 / 2 := by simp [z]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have ha := analyticOn_riemannZeta z hne
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num)))
  have hfin := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (x := 2) (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (by simp) hne (by simp [htwo])
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  refine ⟨n, ?_, ?_⟩
  · change meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z = _
    rw [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
      (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
        (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num),
      ha.meromorphicOrderAt_eq, ← hn, ENat.map_natCast]
  · change 0 < n ↔ riemannZeta z = 0
    rw [← ha.analyticOrderAt_ne_zero, ← hn]
    simp [Nat.pos_iff_ne_zero]

/-- A critical-line zero of ordinary zeta has positive order for the completed
L-function of the trivial rational character, and conversely. -/
private theorem spectralLineSelection_mem_lineZeros (t : ℝ) :
    t ∈ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) ↔ riemannZeta (shift(1 / 2, t)) = 0 := by
  obtain ⟨n, hn, hz⟩ := spectralLineSelection_zeta_order t
  change 0 < orderAt((1 : PontryaginDual C𝔽(ℚ)), shift(1 / 2, t)) ↔ _
  rw [hn]
  simpa using hz

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
Use F = ℚ, the trivial base character and a = 1/2. Let K consist of the first and third
distinct positive critical-line zeta ordinates. The omitted second ordinate lies inside
the closed interval for every ε > 0. -/
theorem Printed.spectralLineSelection_exists_isolatingInterval_false :
    ¬ Printed.spectralLineSelection_exists_isolatingInterval := by
  classical
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let χ' := Function.update χ 1 (1 : PontryaginDual C𝔽(ℚ))
  have hχ' : IsSpectralBasepointChoice χ' := by
    intro ω
    by_cases h : ω = 1
    · subst ω
      rw [show χ' 1 = 1 from Function.update_self ..]
      rfl
    · simpa [χ', Function.update_of_ne h] using hχ ω
  obtain ⟨u, v, w, huv, hvw, hu, hv, hw⟩ := spectralLineSelection_three_zeta_zeros
  let K : Finset ℝ := {u, w}
  have huK : u ∈ K := by simp [K]
  have hwK : w ∈ K := by simp [K]
  have hzeros : (K : Set ℝ) ⊆ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) := by
    intro t ht
    rcases (show t = u ∨ t = w by simpa [K] using ht) with rfl | rfl
    · exact (spectralLineSelection_mem_lineZeros _).2 hu
    · exact (spectralLineSelection_mem_lineZeros _).2 hw
  have htriv : χ' 1 = 1 := Function.update_self ..
  obtain ⟨ε, hε, hK⟩ := hall ℚ χ' hχ' (1 / 2) 1 K ⟨u, huK⟩ (by simpa only [htriv] using hzeros)
  rw [htriv] at hK
  have hvK : v ∈ (K : Set ℝ) := by
    rw [← hK]
    refine ⟨⟨?_, ?_⟩, (spectralLineSelection_mem_lineZeros _).2 hv⟩
    · exact (sub_le_self _ hε.le).trans ((K.min'_le u huK).trans huv.le)
    · exact hvw.le.trans ((K.le_max' w hwK).trans (le_add_of_nonneg_right hε.le))
  simp [K, huv.ne', hvw.ne] at hvK

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
As printed: in each such interval the number of jets is at most the floor cutoff times the
logarithm of the greater of the absolute values of the endpoints. The count includes all
the orders below the truncated multiplicity of each zero in the interval.
See `spectralConvolutionFiniteSum` and ERRATA F180. -/
def Printed.spectralLineBand_jetCount_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty)
      (ε : ℝ), 0 < ε →
      let l := K.min' hK - ε
      let r := K.max' hK + ε
      Icc l r ∩ lineZeros(χ ω, a) = (K : Set ℝ) →
      ((∑ t ∈ K, min ((orderAt(χ ω, shift(a, t))).untop₀.toNat) floorCut(s) : ℕ) : ℝ) ≤
        (floorCut(s) : ℝ) * Real.log (max |l| |r|)

/-- The critical-line ordinates in (0, 50) form a finite set containing
the ten distinct certified ordinates. -/
private theorem spectralLineBand_jetCount_le_false_ordinates :
    ∃ K : Finset ℝ, 10 ≤ K.card ∧ ∀ t, t ∈ K ↔
      t ∈ Ioo (0 : ℝ) 50 ∧ riemannZeta (shift(1 / 2, t)) = 0 := by
  classical
  let z (t : ℝ) : ℂ := shift(1 / 2, t)
  have hcont : Continuous z := by dsimp [z]; fun_prop
  have hinj : Function.Injective z := fun _ _ h ↦ by simpa [z] using congrArg Complex.im h
  have hfin : (Ioo (0 : ℝ) 50 ∩ z ⁻¹' riemannZetaZeros).Finite := by
    have hc := (isCompact_Icc.image hcont : IsCompact (z '' Icc 0 50)).inter_riemannZetaZeros_finite
    exact (hc.preimage hinj.injOn).subset fun t ht ↦ ⟨⟨t, Ioo_subset_Icc_self ht.1, rfl⟩, ht.2⟩
  let K := hfin.toFinset
  have hmem (t : ℝ) : t ∈ K ↔ t ∈ Ioo (0 : ℝ) 50 ∧ riemannZeta (z t) = 0 :=
    hfin.mem_toFinset
  obtain ⟨ts, hmono, hts⟩ := HardyTenZeros.ten_zeros_on_line_below_fifty
  refine ⟨K, ?_, hmem⟩
  have hmap : MapsTo ts (Finset.univ : Finset (Fin 10)) K := by
    intro i _
    refine (hmem _).2 ⟨⟨(hts i).1, (hts i).2.1⟩, ?_⟩
    simpa [z] using (hts i).2.2
  simpa using Finset.card_le_card_of_injOn ts hmap hmono.injective.injOn

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
With cutoff one, the positive critical-line ordinates below 50 give at least ten
jets. A band enclosing them inside (0, 50) has logarithmic bound below four. -/
theorem Printed.spectralLineBand_jetCount_le_false :
    ¬ Printed.spectralLineBand_jetCount_le := by
  classical
  intro h
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice ℚ
  let χ := Function.update χ₀ 1 1
  have hχ : IsSpectralBasepointChoice χ := by
    intro ω
    by_cases hω : ω = 1
    · subst ω
      simp only [χ, Function.update_self]
      rfl
    · simpa only [χ, Function.update_of_ne hω] using hχ₀ ω
  have htriv : χ 1 = 1 := Function.update_self ..
  obtain ⟨K, hcard, hmem⟩ := spectralLineBand_jetCount_le_false_ordinates
  have hK : K.Nonempty := Finset.card_pos.mp (by omega)
  let a := K.min' hK
  let b := K.max' hK
  have ha : 0 < a := ((hmem a).1 (K.min'_mem hK)).1.1
  have hb : b < 50 := ((hmem b).1 (K.max'_mem hK)).1.2
  have hab : a ≤ b := K.min'_le _ (K.max'_mem hK)
  let ε := min a (50 - b) / 2
  have hε : 0 < ε := half_pos (lt_min ha (sub_pos.mpr hb))
  have hl : 0 < a - ε := by dsimp [ε]; linarith [min_le_left a (50 - b)]
  have hr : b + ε < 50 := by dsimp [ε]; linarith [min_le_right a (50 - b)]
  have hlr : a - ε ≤ b + ε := by linarith
  have hband : Icc (a - ε) (b + ε) ∩ lineZeros(χ 1, 1 / 2) = (K : Set ℝ) := by
    rw [htriv]
    ext t
    change (t ∈ Icc (a - ε) (b + ε) ∧ t ∈ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2)) ↔ t ∈ K
    rw [spectralLineSelection_mem_lineZeros]
    constructor
    · rintro ⟨⟨hlt, htr⟩, hz⟩
      exact (hmem t).2 ⟨⟨hl.trans_le hlt, htr.trans_lt hr⟩, hz⟩
    · intro ht
      exact ⟨⟨(sub_le_self a hε.le).trans (K.min'_le t ht),
        (K.le_max' t ht).trans (le_add_of_nonneg_right hε.le)⟩, ((hmem t).1 ht).2⟩
  have hbound := h ℚ χ hχ (1 / 2) 2 (by norm_num) 1 K hK ε hε hband
  have hcut : floorCut((2 : ℝ)) = 1 := (Nat.floor_eq_iff (by norm_num)).2 (by norm_num)
  have hterm (t : ℝ) (ht : t ∈ K) :
      min (orderAt(χ 1, shift(1 / 2, t))).untop₀.toNat floorCut((2 : ℝ)) = 1 := by
    obtain ⟨n, hn, hz⟩ := spectralLineSelection_zeta_order t
    rw [htriv, hn, hcut, WithTop.untop₀_coe, Int.toNat_natCast]
    exact min_eq_right (show 1 ≤ n from hz.mpr ((hmem t).1 ht).2)
  rw [Finset.sum_congr rfl hterm, hcut] at hbound
  have hle : (K.card : ℝ) ≤ Real.log (b + ε) := by
    change _ ≤ _ * Real.log (max |a - ε| |b + ε|) at hbound
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, Nat.cast_one,
      one_mul, abs_of_pos hl, abs_of_pos (hl.trans_le hlr), max_eq_right hlr] using hbound
  have hexp : (50 : ℝ) < Real.exp 4 := calc
    (50 : ℝ) < (2.7 : ℝ) ^ 4 := by norm_num
    _ < Real.exp 1 ^ 4 := by gcongr; linarith [Real.exp_one_gt_d9]
    _ = Real.exp 4 := by simp
  have hlog := (Real.log_lt_iff_lt_exp (hl.trans_le hlr)).2 (hr.trans hexp)
  have : (10 : ℝ) ≤ K.card := by exact_mod_cast hcard
  linarith

section Plancherel

local instance instNormOneLocallyCompactSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : LocallyCompactSpace C₁(F) := by
  have hc : IsCompact ((ideleClassNorm F).ker : Set C𝔽(F)) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  exact hc.isClosed.locallyCompactSpace

local instance instNormOneHaarSec3SpectralProofPrinted (F : Type) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1

local instance instIdeleClassDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C𝔽(F)) := borel _

local instance instNormOneDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C₁(F)) := borel _

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
As printed: in the coordinates induced by the norm section τ, the full Plancherel measure
is the product of ordinary Lebesgue measure in x and the Plancherel measure of the norm-one subgroup.
This is the radial normalization used in the proof of `spectralLineConvolution_trace`
and `spectralStripConvolution_trace` in the paper. See ERRATA F182. -/
def Printed.spectralPlancherelMeasure_eq_radialVolume_prod : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F)),
      (∀ (x : ℝ) (ω : PontryaginDual C₁(F)) (r : ℝ≥0ˣ) (k : C₁(F)),
        e (Multiplicative.ofAdd x, ω) (τ r * k.val) =
          ω k * Circle.exp (x * Real.log (r.val : ℝ))) →
      ∀ (ν₁ : Measure (PontryaginDual C₁(F))) (ν : Measure (PontryaginDual C𝔽(F))),
        IsLCAPlancherelMeasure (normOneIdeleClassTamagawaMeasure F) ν₁ →
        IsLCAPlancherelMeasure (ideleClassTamagawaMeasure F) ν →
        (volume.prod ν₁).map (fun p : ℝ × PontryaginDual C₁(F) ↦
          e (Multiplicative.ofAdd p.1, p.2)) = ν

/-- The norm section splits the dual of the idele class group into a real line and the dual
of the norm-one classes, with the kernel `exp(ixy)` in `y = log |g|`. -/
private theorem spectralPlancherel_exists_dualEquiv (F : Type) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)) (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    ∃ e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F),
      ∀ (x : ℝ) (ω : PontryaginDual C₁(F)) (r : ℝ≥0ˣ) (k : C₁(F)),
        e (Multiplicative.ofAdd x, ω) (τ r * k.val) =
          ω k * Circle.exp (x * Real.log (r.val : ℝ)) := by
  obtain ⟨eR, heR⟩ := exists_realPontryaginDualEquiv
  have hN : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hκmem (g : C𝔽(F)) : (τ (ideleClassNorm F g))⁻¹ * g ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτ]
    exact inv_mul_cancel _
  let κ : C𝔽(F) →ₜ* C₁(F) :=
    { toFun := fun g ↦ ⟨(τ (ideleClassNorm F g))⁻¹ * g, hκmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _)
      continuous_toFun :=
        ((τ.continuous.comp hN).inv.mul continuous_id).subtype_mk _ }
  have hκ (g : C𝔽(F)) : (κ g : C𝔽(F)) = (τ (ideleClassNorm F g))⁻¹ * g := rfl
  let ι : C₁(F) →ₜ* C𝔽(F) := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
  have hpos (g : C𝔽(F)) : (0 : ℝ) < ((ideleClassNorm F g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  let Lhom : C𝔽(F) →ₜ* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))
      map_one' := by simp
      map_mul' := fun g h ↦ by
        change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
        rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos g).ne' (hpos h).ne']
        rfl
      continuous_toFun := continuous_ofAdd.comp
        ((NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦ (hpos g).ne') }
  let expU : Multiplicative ℝ →ₜ* ℝ≥0ˣ :=
    { toFun := fun y ↦ Units.mk0 ⟨Real.exp y.toAdd, (Real.exp_pos _).le⟩
        (fun h ↦ (Real.exp_pos y.toAdd).ne' (congrArg Subtype.val h))
      map_one' := Units.ext (NNReal.eq (by
        change Real.exp 0 = (1 : ℝ)
        exact Real.exp_zero))
      map_mul' := fun y z ↦ Units.ext (NNReal.eq (by
        change Real.exp (y.toAdd + z.toAdd) = Real.exp y.toAdd * Real.exp z.toAdd
        exact Real.exp_add _ _))
      continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
        ((Real.continuous_exp.comp continuous_toAdd).subtype_mk _) }
  have hexpU (y : ℝ) : (((expU (Multiplicative.ofAdd y) : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp y := rfl
  have hexpU_log (t : ℝ≥0ˣ) : expU (Multiplicative.ofAdd (Real.log ((t : ℝ≥0) : ℝ))) = t :=
    Units.ext (NNReal.eq (by
      rw [hexpU]
      exact Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))))
  let Tex : Multiplicative ℝ →ₜ* C𝔽(F) := τ.comp expU
  let sc : Multiplicative ℝ →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (x.toAdd / (2 * Real.pi))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd ((x.toAdd + y.toAdd) / _) = Multiplicative.ofAdd (_ + _)
        rw [add_div]
        rfl
      continuous_toFun := continuous_ofAdd.comp (continuous_toAdd.div_const _) }
  let sc' : Multiplicative ℝ →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (x.toAdd * (2 * Real.pi))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd ((x.toAdd + y.toAdd) * _) = Multiplicative.ofAdd (_ + _)
        rw [add_mul]
        rfl
      continuous_toFun := continuous_ofAdd.comp (continuous_toAdd.mul continuous_const) }
  have hsc (x : Multiplicative ℝ) : sc (sc' x) = x := by
    change Multiplicative.ofAdd (x.toAdd * (2 * Real.pi) / (2 * Real.pi)) = x
    rw [mul_div_cancel_right₀ _ hπ]; rfl
  have hsc' (x : Multiplicative ℝ) : sc' (sc x) = x := by
    change Multiplicative.ofAdd (x.toAdd / (2 * Real.pi) * (2 * Real.pi)) = x
    rw [div_mul_cancel₀ _ hπ]; rfl
  let P : Multiplicative ℝ →ₜ* PontryaginDual C𝔽(F) :=
    (PontryaginDual.map Lhom).comp ((ContinuousMonoidHom.toContinuousMonoidHom eR).comp sc)
  have hP (x : ℝ) (g : C𝔽(F)) :
      P (Multiplicative.ofAdd x) g =
        Circle.exp (x * Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) := by
    change eR (Multiplicative.ofAdd (x / (2 * Real.pi)))
      (Multiplicative.ofAdd (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))) = _
    rw [heR]
    congr 1
    field_simp
  let fwd : Multiplicative ℝ × PontryaginDual C₁(F) →ₜ* PontryaginDual C𝔽(F) :=
    P.comp (ContinuousMonoidHom.fst _ _) *
      (PontryaginDual.map κ).comp (ContinuousMonoidHom.snd _ _)
  have hfwd (x : ℝ) (ω : PontryaginDual C₁(F)) (g : C𝔽(F)) :
      fwd (Multiplicative.ofAdd x, ω) g =
        Circle.exp (x * Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) * ω (κ g) := by
    change P (Multiplicative.ofAdd x) g * ω (κ g) = _
    rw [hP]
  let bwd : PontryaginDual C𝔽(F) →ₜ* Multiplicative ℝ × PontryaginDual C₁(F) :=
    ContinuousMonoidHom.prod
      (sc'.comp ((ContinuousMonoidHom.toContinuousMonoidHom eR.symm).comp
        (PontryaginDual.map Tex)))
      (PontryaginDual.map ι)
  have hleft : Function.LeftInverse bwd fwd := by
    rintro ⟨x, ω⟩
    obtain ⟨x, rfl⟩ : ∃ x' : ℝ, Multiplicative.ofAdd x' = x := ⟨x.toAdd, rfl⟩
    refine Prod.ext ?_ ?_
    · change sc' (eR.symm (PontryaginDual.map Tex (fwd (Multiplicative.ofAdd x, ω)))) = _
      have hmap : PontryaginDual.map Tex (fwd (Multiplicative.ofAdd x, ω)) =
          eR (sc (Multiplicative.ofAdd x)) := by
        ext1 y
        obtain ⟨y, rfl⟩ : ∃ y' : ℝ, Multiplicative.ofAdd y' = y := ⟨y.toAdd, rfl⟩
        rw [PontryaginDual.map_apply, hfwd]
        change _ = eR (Multiplicative.ofAdd (x / (2 * Real.pi))) (Multiplicative.ofAdd y)
        rw [heR]
        have hNT : ideleClassNorm F (Tex (Multiplicative.ofAdd y)) =
            expU (Multiplicative.ofAdd y) := hτ _
        have hκT : κ (Tex (Multiplicative.ofAdd y)) = 1 := Subtype.ext (by
          rw [hκ, hNT]
          exact inv_mul_cancel _)
        rw [hκT, map_one, mul_one, hNT, hexpU, Real.log_exp]
        congr 1
        field_simp
      rw [hmap, ContinuousMulEquiv.symm_apply_apply, hsc']
    · ext1 k
      change fwd (Multiplicative.ofAdd x, ω) (ι k) = ω k
      have hNk : ideleClassNorm F (ι k) = 1 := k.property
      have hκk : κ (ι k) = k := Subtype.ext (by
        rw [hκ, hNk, map_one, inv_one, one_mul]
        rfl)
      rw [hfwd, hNk, hκk]
      simp
  have hright : Function.RightInverse bwd fwd := by
    intro χ
    ext1 g
    set z := eR.symm (PontryaginDual.map Tex χ) with hz
    have hz' : eR z = PontryaginDual.map Tex χ := by
      rw [hz, ContinuousMulEquiv.apply_symm_apply]
    change P (sc' z) g * (PontryaginDual.map ι χ) (κ g) = χ g
    have hPz : P (sc' z) g = χ (τ (ideleClassNorm F g)) := by
      change eR (sc (sc' z)) (Lhom g) = _
      rw [hsc, hz', PontryaginDual.map_apply]
      change χ (τ (expU (Multiplicative.ofAdd (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))))) = _
      rw [hexpU_log]
    rw [hPz, PontryaginDual.map_apply, ← map_mul]
    congr 1
    change τ (ideleClassNorm F g) * ((τ (ideleClassNorm F g))⁻¹ * g) = g
    exact mul_inv_cancel_left _ _
  let e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F) :=
    { toFun := fwd
      invFun := bwd
      left_inv := hleft
      right_inv := hright
      map_mul' := map_mul fwd
      continuous_toFun := fwd.continuous
      continuous_invFun := bwd.continuous }
  refine ⟨e, fun x ω r k ↦ ?_⟩
  change fwd (Multiplicative.ofAdd x, ω) (τ r * k.val) = _
  have hNr : ideleClassNorm F (τ r * k.val) = r := by
    rw [map_mul, hτ, MonoidHom.mem_ker.mp k.property, mul_one]
  have hκr : κ (τ r * k.val) = k := Subtype.ext (by
    rw [hκ, hNr]
    exact inv_mul_cancel_left _ _)
  rw [hfwd, hNr, hκr, mul_comm]

/-- In logarithmic norm coordinates the idele class measure is the mass of the norm-one
classes times Lebesgue measure: Haar uniqueness on ℝ, normalized by Weil's formula. -/
private theorem spectralPlancherel_map_logNorm (F : Type) [Field F] [NumberField F] :
    (ideleClassTamagawaMeasure F).map (fun g ↦ Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) =
      normOneIdeleClassTamagawaMeasure F univ • volume := by
  let μ := ideleClassTamagawaMeasure F
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  let L : C𝔽(F) → ℝ := fun g ↦ Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hN : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hpos (g : C𝔽(F)) : (0 : ℝ) < ((ideleClassNorm F g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦ (hpos g).ne'
  have hLmul (g h : C𝔽(F)) : L (g * h) = L g + L h := by
    change Real.log _ = Real.log _ + Real.log _
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos g).ne' (hpos h).ne']
  obtain ⟨τ, hτc, hτ⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.2.1
  let expU : ℝ → ℝ≥0ˣ := fun y ↦ Units.mk0 ⟨Real.exp y, (Real.exp_pos y).le⟩
    (fun h ↦ (Real.exp_pos y).ne' (congrArg Subtype.val h))
  have hexpU : Continuous expU := Units.isEmbedding_val₀.continuous_iff.mpr
    (Real.continuous_exp.subtype_mk _)
  have hLτ (y : ℝ) : L (τ (expU y)) = y := by
    change Real.log (((ideleClassNorm F (τ (expU y)) : ℝ≥0ˣ) : ℝ≥0) : ℝ) = y
    rw [hτ]
    exact Real.log_exp y
  have hexpL (g : C𝔽(F)) : expU (L g) = ideleClassNorm F g :=
    Units.ext (NNReal.eq (Real.exp_log (hpos g)))
  -- Preimages of compact sets under the log norm are compact.
  have hLcpt {K : Set ℝ} (hK : IsCompact K) : IsCompact (L ⁻¹' K) := by
    refine ((isProperMap_ideleClassNorm F).isCompact_preimage (hK.image hexpU)).of_isClosed_subset
      (hK.isClosed.preimage hL) fun g hg ↦ ⟨L g, hg, hexpL g⟩
  -- The pushforward is translation invariant and finite on compacts.
  let μ' := μ.map L
  have hinv : μ'.IsAddLeftInvariant := ⟨fun a ↦ by
    change (μ.map L).map (a + ·) = μ.map L
    rw [Measure.map_map (measurable_const_add a) hL.measurable]
    have hcomp : (a + ·) ∘ L = L ∘ (τ (expU a) * ·) := funext fun g ↦ by
      change a + L g = L (τ (expU a) * g)
      rw [hLmul, hLτ]
    rw [hcomp, ← Measure.map_map hL.measurable (measurable_const_mul _), map_mul_left_eq_self]⟩
  have hfin : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK ↦ by
    rw [Measure.map_apply hL.measurable hK.measurableSet]
    exact (hLcpt hK).measure_lt_top⟩
  have hscale : μ' = Measure.addHaarScalarFactor μ' volume • volume :=
    Measure.isAddLeftInvariant_eq_smul μ' volume
  set c := Measure.addHaarScalarFactor μ' volume with hc
  -- A positive bump in log norm coordinates fixes the constant.
  let G : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hGc : Continuous G := G.continuous
  have hGs : HasCompactSupport G := G.hasCompactSupport
  have hGpos : 0 < ∫ y, G y := G.integral_pos
  let : μ₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : CompactSpace C₁(F) := (ideleClassGroup_finiteness F).2.1
  have hLker (k : C₁(F)) : L k.val = 0 := by
    change Real.log (((ideleClassNorm F k.val : ℝ≥0ˣ) : ℝ≥0) : ℝ) = 0
    rw [MonoidHom.mem_ker.mp k.property]
    simp
  let f : C(C𝔽(F), ℂ) := ⟨fun g ↦ ((G (L g) : ℝ) : ℂ), Complex.continuous_ofReal.comp (hGc.comp hL)⟩
  have hfs : HasCompactSupport f := by
    refine IsCompact.of_isClosed_subset (hLcpt hGs.isCompact) (isClosed_tsupport _) ?_
    refine closure_minimal (fun g hg ↦ subset_tsupport _ fun h ↦ hg ?_)
      ((isClosed_tsupport _).preimage hL)
    change ((G (L g) : ℝ) : ℂ) = 0
    rw [h, Complex.ofReal_zero]
  have hWeil := (normOneIdeleClassTamagawaMeasure_isWeil F).2.2 f hfs
  have hcoset (x : C𝔽(F)) : lcaCosetIntegral C₁(F) μ₁ f (x : C𝔽(F) ⧸ C₁(F)) =
      (μ₁.real univ : ℂ) * ((G (L x) : ℝ) : ℂ) := by
    have hconst : (fun k : C₁(F) ↦ f (x * k.val)) = fun _ ↦ ((G (L x) : ℝ) : ℂ) := by
      funext k
      change ((G (L (x * k.val)) : ℝ) : ℂ) = _
      rw [hLmul, hLker, add_zero]
    rw [lcaCosetIntegral_mk _ _ _ x (by rw [hconst]; exact integrable_const _), hconst,
      integral_const, Complex.real_smul]
  let φ : (C𝔽(F) ⧸ C₁(F)) ≃* ℝ≥0ˣ :=
    QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) τ hτ
  let E : (C𝔽(F) ⧸ C₁(F)) ≃ₜ ℝ≥0ˣ :=
    { φ.toEquiv with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hN
      continuous_invFun := QuotientGroup.continuous_mk.comp hτc }
  let : MeasurableSpace (C𝔽(F) ⧸ C₁(F)) := borel _
  let : BorelSpace (C𝔽(F) ⧸ C₁(F)) := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let Em := E.toMeasurableEquiv
  have hdt : Measure.comap (QuotientGroup.kerLift (ideleClassNorm F)) positiveRealHaar =
      positiveRealHaar.map Em.symm := Em.map_symm.symm
  let H : ℝ≥0ˣ → ℂ := fun t ↦ (μ₁.real univ : ℂ) * ((G (Real.log ((t : ℝ≥0) : ℝ)) : ℝ) : ℂ)
  have hcosetH (q : C𝔽(F) ⧸ C₁(F)) :
      lcaCosetIntegral C₁(F) μ₁ f q = H (QuotientGroup.kerLift (ideleClassNorm F) q) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hcoset, QuotientGroup.kerLift_mk]
  have hexpm : Measurable (fun x : ℝ ↦ Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hRHS : (∫ q, lcaCosetIntegral C₁(F) μ₁ f q ∂(Measure.comap
      (QuotientGroup.kerLift (ideleClassNorm F)) positiveRealHaar)) =
      (μ₁.real univ : ℂ) * ((∫ y, G y : ℝ) : ℂ) := by
    simp_rw [hcosetH]
    rw [hdt, integral_map_equiv]
    have hEm (t : ℝ≥0ˣ) : QuotientGroup.kerLift (ideleClassNorm F) (Em.symm t) = t :=
      φ.apply_symm_apply t
    simp_rw [hEm]
    rw [positiveRealHaar, integral_map hexpm.aemeasurable]
    · simp only [H]
      rw [integral_const_mul, integral_complex_ofReal]
      congr 2
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      change G (Real.log (Real.exp y).toNNReal) = G y
      rw [Real.coe_toNNReal _ (Real.exp_pos y).le, Real.log_exp]
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp (hGc.comp
        ((NNReal.continuous_coe.comp Units.continuous_val).log fun t ↦
          (NNReal.coe_pos.mpr (Units.zero_lt t)).ne')))).aestronglyMeasurable
  have hLHS : (∫ g, f g ∂μ) = ((c : ℝ) * ∫ y, G y : ℝ) := by
    change (∫ g, ((G (L g) : ℝ) : ℂ) ∂μ) = _
    rw [integral_complex_ofReal, ← integral_map hL.aemeasurable hGc.aestronglyMeasurable]
    change (((∫ y, G y ∂μ') : ℝ) : ℂ) = _
    rw [hscale, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hcr : (c : ℝ) = μ₁.real univ := by
    have h := hLHS.symm.trans (hWeil.trans hRHS)
    rw [← Complex.ofReal_mul, Complex.ofReal_inj] at h
    exact mul_right_cancel₀ hGpos.ne' h
  have hcE : (c : ENNReal) = μ₁ univ := by
    rw [← ENNReal.ofReal_coe_nnreal, hcr, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change μ' = _
  rw [hscale, ← hcE]
  rfl

/-- At a character that only sees the log norm with frequency `x`, the transform of the
Gaussian `exp(−y²/2)` in `y = log |g|` has squared norm `m² · 2π · exp(−x²)`, where `m` is
the mass of the norm-one classes. -/
private theorem spectralPlancherel_gaussian_fourier (F : Type) [Field F] [NumberField F]
    (x : ℝ) (χ : PontryaginDual C𝔽(F))
    (hχ : ∀ g, χ g = Circle.exp (x * Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))) :
    ‖lcaFourier (ideleClassTamagawaMeasure F) (fun g ↦ Complex.exp (-(1 / 2 : ℂ) *
        (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ 2)) χ‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal ((normOneIdeleClassTamagawaMeasure F).real univ ^ 2 * (2 * Real.pi) *
        Real.exp (-x ^ 2)) := by
  set r := (normOneIdeleClassTamagawaMeasure F).real univ with hr
  have hr0 : 0 ≤ r := measureReal_nonneg
  let L : C𝔽(F) → ℝ := fun g ↦ Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hN : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  let φ : ℝ → ℂ := fun y ↦ Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) *
    star ((Circle.exp (x * y) : Circle) : ℂ)
  have hφ : Continuous φ := by
    refine (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.pow 2))).mul (continuous_star.comp ?_)
    exact continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
  have hpt (y : ℝ) : φ y = Complex.exp (Complex.I * (-(x : ℂ)) * y) *
      Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) := by
    simp only [φ, Circle.coe_exp, Complex.star_def, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hF : lcaFourier (ideleClassTamagawaMeasure F) (fun g ↦ Complex.exp (-(1 / 2 : ℂ) *
        (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ 2)) χ =
      (r : ℂ) * (((Real.pi : ℂ) / (1 / 2)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(-(x : ℂ)) ^ 2 / (4 * (1 / 2)))) := by
    have h1 : lcaFourier (ideleClassTamagawaMeasure F) (fun g ↦ Complex.exp (-(1 / 2 : ℂ) *
        (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ 2)) χ =
        ∫ g, φ (L g) ∂ideleClassTamagawaMeasure F := by
      simp only [lcaFourier, φ, L, hχ]
    rw [h1, ← integral_map hL.aemeasurable hφ.aestronglyMeasurable,
      spectralPlancherel_map_logNorm, integral_smul_measure]
    simp_rw [hpt]
    rw [fourierIntegral_gaussian (by norm_num), Complex.real_smul, ← measureReal_def]
  rw [hF, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
  congr 1
  have h2π : ((Real.pi : ℂ) / (1 / 2)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  have hexp : Complex.exp (-(-(x : ℂ)) ^ 2 / (4 * (1 / 2))) = ((Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h2π, hexp, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Real.norm_of_nonneg hr0,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  norm_num
  rw [mul_pow, mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), sq (Real.exp _),
    ← Real.exp_add]
  ring_nf

/-- The Plancherel measure of the compact norm-one classes gives the trivial character the
reciprocal of their mass: the transform of the constant one is that mass at the trivial
character and vanishes elsewhere by orthogonality. -/
private theorem spectralPlancherel_normOneDual_one (F : Type) [Field F] [NumberField F]
    (ν₁ : Measure (PontryaginDual C₁(F)))
    (hν₁ : IsLCAPlancherelMeasure (normOneIdeleClassTamagawaMeasure F) ν₁) :
    ν₁ {1} * normOneIdeleClassTamagawaMeasure F univ = 1 := by
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace C₁(F) := (ideleClassGroup_finiteness F).2.1
  let : BorelSpace (PontryaginDual C₁(F)) := ⟨rfl⟩
  have hm0 : μ₁ univ ≠ 0 := (isOpen_univ.measure_pos μ₁ univ_nonempty).ne'
  have hmtop : μ₁ univ ≠ ⊤ := measure_ne_top _ _
  have hF : lcaFourier μ₁ (fun _ ↦ (1 : ℂ)) =
      ({1} : Set (PontryaginDual C₁(F))).indicator fun _ ↦ (μ₁.real univ : ℂ) := by
    funext ω
    simp only [lcaFourier, one_mul]
    by_cases hω : ω = 1
    · subst hω
      simp [PontryaginDual.one_apply, Complex.real_smul]
    · rw [Set.indicator_of_notMem (by simpa using hω)]
      obtain ⟨h₀, hh₀⟩ : ∃ h₀, ω h₀ ≠ 1 := not_forall.mp fun hc ↦
        hω (PontryaginDual.ext fun k ↦ (hc k).trans (PontryaginDual.one_apply k).symm)
      have hinv := integral_mul_left_eq_self (μ := μ₁) (fun k ↦ star (ω k : ℂ)) h₀
      simp only [map_mul, Circle.coe_mul, star_mul'] at hinv
      rw [integral_const_mul] at hinv
      have hne : star (ω h₀ : ℂ) ≠ 1 := by
        intro h
        apply hh₀
        apply Subtype.ext
        simpa using congrArg star h
      have : (star (ω h₀ : ℂ) - 1) * ∫ k, star (ω k : ℂ) ∂μ₁ = 0 := by
        rw [sub_mul, hinv, one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have hP := (hν₁.2.2 (fun _ ↦ (1 : ℂ)) (integrable_const _) (memLp_const _)).2
  rw [hF, eLpNorm_indicator_const (measurableSet_singleton _).nullMeasurableSet two_ne_zero
    ENNReal.ofNat_ne_top, eLpNorm_const _ two_ne_zero (Measure.measure_univ_ne_zero.mp hm0)] at hP
  have hnorm : ‖(μ₁.real univ : ℂ)‖ₑ = μ₁ univ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
      measureReal_def, ENNReal.ofReal_toReal hmtop]
  rw [hnorm, eNorm_one, one_mul] at hP
  have h2 := congrArg (· ^ (2 : ℝ)) hP
  simp only [ENNReal.toReal_ofNat] at h2
  rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  norm_num at h2
  have h3 : μ₁ univ * (μ₁ univ * ν₁ {1}) = μ₁ univ * 1 := by
    rw [mul_one, ← mul_assoc, ← pow_two]
    exact h2
  rw [mul_comm]
  exact (ENNReal.mul_right_inj hm0 hmtop).mp h3

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
Take F = ℚ with its norm section and induced dual isomorphism. Use the Gaussian exp(−y²/2)
in y = log |g|, constant on the norm-one subgroup. With the kernel exp(ixy) its radial
transform is √(2π) exp(−x²/2). The printed measure makes its squared norm 2π times the
original squared norm, since the fixed norm-one Plancherel measure already accounts for
the compact factor. The radial Plancherel measure is dx/(2π). -/
theorem Printed.spectralPlancherelMeasure_eq_radialVolume_prod_false :
    ¬ Printed.spectralPlancherelMeasure_eq_radialVolume_prod := by
  intro hall
  obtain ⟨τ₀, hτc, hτ⟩ := (ideleGroup_quotient.{0, 0} ℚ).2.2.2.2.2.2.2.2.2.2.1
  let τ : ℝ≥0ˣ →ₜ* C𝔽(ℚ) := ⟨τ₀, hτc⟩
  obtain ⟨e, he⟩ := spectralPlancherel_exists_dualEquiv ℚ τ hτ
  let μ := ideleClassTamagawaMeasure ℚ
  let μ₁ := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace C₁(ℚ) := (ideleClassGroup_finiteness ℚ).2.1
  let : μ.Regular := (ideleClassTamagawaMeasure_isWeil ℚ).2.1
  let : μ₁.Regular :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.2.1
  obtain ⟨ν₁, hν₁⟩ := (lcaPlancherelMeasure_existsUnique μ₁).exists
  obtain ⟨ν, hν⟩ := (lcaPlancherelMeasure_existsUnique μ).exists
  have hmap := hall ℚ τ hτ e he ν₁ ν hν₁ hν
  let : BorelSpace (PontryaginDual C𝔽(ℚ)) := ⟨rfl⟩
  let : BorelSpace (PontryaginDual C₁(ℚ)) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let Φ := fun p : ℝ × PontryaginDual C₁(ℚ) ↦ e (Multiplicative.ofAdd p.1, p.2)
  -- The pushforward is neither zero nor a point mass, since ν is a Haar measure.
  have hν0 : ν ≠ 0 := fun h ↦ isOpen_univ.measure_ne_zero ν univ_nonempty (by rw [h]; rfl)
  have hreg : SFinite ν₁ ∧ AEMeasurable Φ (volume.prod ν₁) := by
    by_contra hdeg
    have hprod : volume.prod ν₁ ≠ 0 := fun h ↦ hν0 (by
      rw [← hmap]
      change Measure.map Φ (volume.prod ν₁) = 0
      rw [h, Measure.map_zero])
    have hsf : SFinite ν₁ := by
      by_contra hs
      exact hprod (Measure.prod_eq_zero_of_not_sfinite hs)
    have hΦ : ¬ AEMeasurable Φ (volume.prod ν₁) := fun h ↦ hdeg ⟨hsf, h⟩
    obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀, ν = Measure.dirac χ₀ :=
      ⟨_, hmap.symm.trans (Measure.map_of_not_aemeasurable_of_ne_zero hΦ hprod)⟩
    let χ₁ := e (Multiplicative.ofAdd 1, 1)
    have hinv := map_mul_left_eq_self ν χ₁
    rw [hχ₀, Measure.map_dirac' (show Continuous fun x : PontryaginDual C𝔽(ℚ) ↦ χ₁ * x from
      continuous_const.mul continuous_id).measurable] at hinv
    have h1 := congrArg (fun m : Measure (PontryaginDual C𝔽(ℚ)) ↦ m {χ₀}) hinv
    simp only [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator,
      Set.mem_singleton_iff, mul_eq_right, Pi.one_apply] at h1
    have hχ₁ : χ₁ = 1 := by
      by_contra hne
      simp [hne] at h1
    have := congrArg Prod.fst (e.injective (hχ₁.trans (map_one e).symm))
    exact one_ne_zero (congrArg Multiplicative.toAdd this)
  obtain ⟨hsf, hΦ⟩ := hreg
  -- Constants.
  set m := μ₁ univ with hm
  set r := μ₁.real univ with hrdef
  have hm0 : m ≠ 0 := (isOpen_univ.measure_pos μ₁ univ_nonempty).ne'
  have hmtop : m ≠ ⊤ := measure_ne_top _ _
  have hmr : m = ENNReal.ofReal r := (ENNReal.ofReal_toReal hmtop).symm
  have hr : 0 < r := ENNReal.toReal_pos hm0 hmtop
  have hone : ν₁ {1} * m = 1 := spectralPlancherel_normOneDual_one ℚ ν₁ hν₁
  -- The Gaussian in log norm coordinates.
  let L : C𝔽(ℚ) → ℝ := fun g ↦ Real.log ((ideleClassNorm ℚ g : ℝ≥0) : ℝ)
  have hN : Continuous (ideleClassNorm ℚ) := (isProperMap_ideleClassNorm ℚ).continuous
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  let G : ℝ → ℂ := fun y ↦ Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2)
  have hG : Continuous G :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2))
  let f : C𝔽(ℚ) → ℂ := fun g ↦ G (L g)
  have hmapL : μ.map L = m • volume := spectralPlancherel_map_logNorm ℚ
  have hGnorm (y : ℝ) : ‖G y‖ = Real.exp (-1 / 2 * y ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [← Complex.ofReal_pow]
    ring
  have hGsq (y : ℝ) : ‖G y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Real.exp (-1 * y ^ 2)) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, hGnorm,
      Real.rpow_two, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hGint : Integrable G volume := integrable_cexp_neg_mul_sq (by norm_num)
  have hGL2 : MemLp G 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr ?_
    refine (integrable_exp_neg_mul_sq one_pos).congr (Filter.Eventually.of_forall fun y ↦ ?_)
    change Real.exp (-1 * y ^ 2) = ‖G y‖ ^ 2
    rw [hGnorm, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfi : Integrable f μ :=
    (integrable_map_measure hG.aestronglyMeasurable hL.aemeasurable).mp
      (by rw [hmapL]; exact hGint.smul_measure hmtop)
  have hfm : MemLp f 2 μ :=
    (memLp_map_measure_iff hG.aestronglyMeasurable hL.aemeasurable).mp
      (by rw [hmapL]; exact hGL2.smul_measure hmtop)
  obtain ⟨hFm, hP⟩ := hν.2.2 f hfi hfm
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hFm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hfi.aestronglyMeasurable] at hP
  simp only [ENNReal.toReal_ofNat] at hP
  have hAB := ENNReal.rpow_left_injective (by norm_num : (1 / 2 : ℝ) ≠ 0) hP
  -- The squared norm of the test.
  have hgauss : ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y ^ 2)) =
      ENNReal.ofReal (Real.sqrt Real.pi) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq one_pos)
      (Filter.Eventually.of_forall fun y ↦ (Real.exp_pos _).le), integral_gaussian, div_one]
  have hB : ∫⁻ g, ‖f g‖ₑ ^ (2 : ℝ) ∂μ = m * ENNReal.ofReal (Real.sqrt Real.pi) := by
    have hmeas : Measurable fun y : ℝ ↦ ‖G y‖ₑ ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const.comp hG.eNorm).measurable
    rw [show (∫⁻ g, ‖f g‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ y, ‖G y‖ₑ ^ (2 : ℝ) ∂(μ.map L) from
      (lintegral_map hmeas hL.measurable).symm, hmapL, lintegral_smul_measure, smul_eq_mul]
    simp_rw [hGsq]
    rw [hgauss]
  -- A lower bound for the squared norm of the transform from the trivial norm-one character.
  let h : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (r ^ 2 * (2 * Real.pi) * Real.exp (-x ^ 2))
  have hh : Continuous h := ENNReal.continuous_ofReal.comp
    (continuous_const.mul (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))))
  let R : Set (PontryaginDual C𝔽(ℚ)) := {χ | (e.symm χ).2 = 1}
  have hRm : MeasurableSet R :=
    (continuous_snd.comp e.symm.continuous).measurable (measurableSet_singleton _)
  let ψ : PontryaginDual C𝔽(ℚ) → ENNReal := R.indicator fun χ ↦ h (e.symm χ).1.toAdd
  have hψm : Measurable ψ :=
    (hh.comp (continuous_toAdd.comp (continuous_fst.comp e.symm.continuous))).measurable.indicator
      hRm
  have hψle (χ : PontryaginDual C𝔽(ℚ)) : ψ χ ≤ ‖lcaFourier μ f χ‖ₑ ^ (2 : ℝ) := by
    change R.indicator (fun χ ↦ h (e.symm χ).1.toAdd) χ ≤ _
    by_cases hχR : χ ∈ R
    · rw [Set.indicator_of_mem hχR]
      set x := (e.symm χ).1.toAdd
      have hχe : χ = e (Multiplicative.ofAdd x, 1) := by
        rw [← e.apply_symm_apply χ]
        congr 1
        exact Prod.ext rfl hχR
      refine (spectralPlancherel_gaussian_fourier ℚ x χ fun g ↦ ?_).symm.le
      have hk : (τ (ideleClassNorm ℚ g))⁻¹ * g ∈ (ideleClassNorm ℚ).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        exact (congrArg (·⁻¹ * _) (hτ _)).trans (inv_mul_cancel _)
      have := he x 1 (ideleClassNorm ℚ g) ⟨_, hk⟩
      rw [mul_inv_cancel_left, PontryaginDual.one_apply, one_mul] at this
      rw [hχe]
      exact this
    · rw [Set.indicator_of_notMem hχR]
      exact zero_le
  have hψΦ (p : ℝ × PontryaginDual C₁(ℚ)) :
      ψ (Φ p) = h p.1 * ({1} : Set (PontryaginDual C₁(ℚ))).indicator 1 p.2 := by
    have hs : e.symm (Φ p) = (Multiplicative.ofAdd p.1, p.2) := e.symm_apply_apply _
    change R.indicator (fun χ ↦ h (e.symm χ).1.toAdd) (Φ p) = _
    by_cases hp : p.2 = 1
    · rw [Set.indicator_of_mem (show Φ p ∈ R by simp [R, hs, hp]),
        Set.indicator_of_mem (show p.2 ∈ ({1} : Set _) from hp), hs]
      simp
    · rw [Set.indicator_of_notMem (show Φ p ∉ R by simp [R, hs, hp]),
        Set.indicator_of_notMem (show p.2 ∉ ({1} : Set _) from hp), mul_zero]
  have hlow : ENNReal.ofReal (r ^ 2 * (2 * Real.pi) * Real.sqrt Real.pi) * ν₁ {1} ≤
      ∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ (2 : ℝ) ∂ν := by
    refine le_trans (le_of_eq ?_) (lintegral_mono hψle)
    rw [← hmap, lintegral_map' hψm.aemeasurable hΦ]
    simp_rw [hψΦ]
    rw [lintegral_prod_mul hh.aemeasurable
      ((measurable_one.indicator (measurableSet_singleton _)).aemeasurable),
      lintegral_indicator_one (measurableSet_singleton _)]
    congr 1
    have hint : Integrable fun x : ℝ ↦ r ^ 2 * (2 * Real.pi) * Real.exp (-x ^ 2) := by
      simpa [neg_one_mul] using (integrable_exp_neg_mul_sq one_pos).const_mul (r ^ 2 * (2 * Real.pi))
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x ↦ by positivity), integral_const_mul]
    congr 2
    simpa [neg_one_mul] using (integral_gaussian 1).symm
  -- Compare: the transform has 2π times the squared norm of the test.
  rw [hAB, hB] at hlow
  have hle := mul_le_mul_left hlow m
  rw [mul_assoc, hone, mul_one, hmr, ← ENNReal.ofReal_mul hr.le,
    ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.sqrt_nonneg _)),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : 0 < r ^ 2 * Real.sqrt Real.pi := by positivity
  nlinarith [Real.pi_gt_three]

end Plancherel

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
As printed: for each norm-one character and any numbering of its line-zero ordinates by
the natural numbers, the Fourier–Mellin samples of every test decay rapidly. This is the
claim for an infinite zero set. See `spectralLineConvolution_trace` and ERRATA F183. -/
def Printed.spectralLineSamples_rapid_for_any_numbering : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (φ : BruhatCompactSupport C𝔽(F)) (ω : PontryaginDual C₁(F))
      (e : ℕ ≃ lineZeros(χ ω, a)) (k : ℕ),
      Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * ∫ g,
        φ.val g * ideleClassNormTwist (χ ω) (shift(0, (e n).val)) g
          ∂ideleClassTamagawaMeasure F) atTop (𝓝 0)

/-- A compact bump supported away from zero has an entire Mellin transform.
A single translate of this transform avoids zero on any countable set. -/
private theorem spectralLineSamples_mellin_shift (b : ContDiffBump (1 : ℝ))
    (hb : b.rOut = 1 / 2) (t : ℕ → ℝ) :
    ∃ c : ℂ, ∀ n, mellin (fun x : ℝ ↦ (b x : ℂ)) ((t n : ℂ) * Complex.I + c) ≠ 0 := by
  let B (x : ℝ) : ℂ := b x
  have hlow (x : ℝ) (hx : x ≤ 1 / 2) : b x = 0 := by
    apply b.zero_of_le_dist
    rw [hb, Real.dist_eq, abs_of_nonpos (by linarith : x - 1 ≤ 0)]
    linarith
  have htop : B =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    change (b x : ℂ) = 0
    rw [b.zero_of_le_dist, Complex.ofReal_zero]
    rw [hb, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ x - 1)]
    linarith
  have hbot : B =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx
    change (b x : ℂ) = 0
    simp [hlow x hx.le]
  have hM : Differentiable ℂ (mellin B) := by
    intro z
    apply mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1)
      ((Complex.continuous_ofReal.comp b.continuous).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    · exact htop.isBigO.trans (Asymptotics.isBigO_zero _ _)
    · linarith
    · exact hbot.isBigO.trans (Asymptotics.isBigO_zero _ _)
    · linarith
  have hne : mellin B 1 ≠ 0 := by
    simp only [mellin, sub_self, Complex.cpow_zero, one_smul, B]
    rw [show (∫ x : ℝ in Ioi 0, (b x : ℂ)) = ((∫ x : ℝ in Ioi 0, b x : ℝ) : ℂ) from integral_ofReal]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun x hx ↦
      hlow x ((not_lt.mp hx).trans (by norm_num)))]
    exact Complex.ofReal_ne_zero.mpr (b.integral_pos (μ := volume)).ne'
  let Z := (mellin B) ⁻¹' ({0} : Set ℂ)
  have hZ : Z.Countable := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp ((show AnalyticOnNhd ℂ (mellin B) univ from fun z _ ↦ hM.analyticAt z).preimage_zero_mem_codiscrete hne)).2
  let bad := ⋃ n, (fun c : ℂ ↦ (t n : ℂ) * Complex.I + c) ⁻¹' Z
  have hbad : bad.Countable := Set.countable_iUnion fun n ↦ hZ.preimage (add_right_injective _)
  obtain ⟨c, hc⟩ := (hbad.dense_compl ℂ).nonempty
  refine ⟨c, fun n hn ↦ hc (mem_iUnion.mpr ⟨n, ?_⟩)⟩
  exact hn

/-- Composition with a smooth scalar function preserves Bruhat smoothness in
each elementary quotient chart. -/
private theorem spectralLineSamples_smooth_comp {G : Type*} [CommGroup G] [TopologicalSpace G]
    {v : G → ℂ} (hv : IsBruhatSmooth v) {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsBruhatSmooth (fun x ↦ f (v x)) := by
  intro p
  obtain ⟨k, hk, hi, hd⟩ := hv p
  refine ⟨k, hk, fun h x ↦ congrArg f (hi h x), fun a ha ↦ ?_⟩
  obtain ⟨q, hq, hdiff⟩ := hd a ha
  exact ⟨fun y ↦ f (q y), fun x ↦ congrArg f (hq x),
    fun e z b ↦ (hf.of_le (by simp)).comp (hdiff e z b)⟩

/-- A compactly supported radial test can have all its Mellin samples at a
specified sequence of frequencies nonzero. -/
private theorem spectralLineSamples_nonvanishing (t : ℕ → ℝ) :
    ∃ φ : BruhatCompactSupport C𝔽(ℚ), ∀ n,
      (∫ g, φ.val g * ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
        (shift(0, t n)) g ∂ideleClassTamagawaMeasure ℚ) ≠ 0 := by
  let b : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  obtain ⟨c, hc⟩ := spectralLineSamples_mellin_shift b rfl t
  let f (x : ℝ) : ℂ := (x : ℂ) ^ c * (b x : ℂ)
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases h : 0 < x
    · have he : (fun y : ℝ ↦ (y : ℂ) ^ c) =ᶠ[𝓝 x]
          fun y ↦ Complex.exp ((Real.log y : ℂ) * c) := by
        filter_upwards [lt_mem_nhds h] with y hy
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.ofReal_log hy.le]
      apply ContDiffAt.mul _ (Complex.ofRealCLM.contDiff.comp b.contDiff).contDiffAt
      apply ContDiffAt.congr_of_eventuallyEq _ he
      exact Complex.contDiff_exp.contDiffAt.comp x
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr h.ne')).mul contDiffAt_const)
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      have he : ∀ᶠ y in 𝓝 x, y < 1 / 2 := gt_mem_nhds (by linarith)
      filter_upwards [he] with y hy
      have hy' : b y = 0 := b.zero_of_le_dist (by
        rw [Real.dist_eq, abs_of_nonpos (by linarith : y - 1 ≤ 0)]
        change (1 / 2 : ℝ) ≤ _
        linarith)
      simp [f, hy']
  let N (g : C𝔽(ℚ)) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  let χ : QuasiCharacter C𝔽(ℚ) :=
    { toFun := fun g ↦ (N g : ℂ)
      map_one' := by simp [N]
      map_mul' := fun x y ↦ by simp [N]
      continuous_toFun := Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)) }
  have hs : IsBruhatSmooth (fun g ↦ f (N g)) :=
    spectralLineSamples_smooth_comp (v := fun x ↦ χ x) (f := fun z ↦ f z.re)
      ((mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth (G := C𝔽(ℚ)) χ))
      (hfs.comp Complex.reCLM.contDiff)
  let e := (Nonneg.unitsHomeomorphPos ℝ).symm
  let K := Icc (⟨1 / 2, by norm_num⟩ : {x : ℝ // 0 < x}) ⟨3 / 2, by norm_num⟩
  have hK : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    change IsCompact (Subtype.val '' Icc (⟨1 / 2, by norm_num⟩ : Ioi (0 : ℝ)) ⟨3 / 2, by norm_num⟩)
    rw [image_subtype_val_Icc]
    exact isCompact_Icc
  have hcs : HasCompactSupport (fun g ↦ f (N g)) := by
    apply HasCompactSupport.intro ((isProperMap_ideleClassNorm ℚ).isCompact_preimage
      (hK.image e.continuous))
    intro g hg
    suffices hb : b (N g) = 0 by simp [f, hb]
    by_contra hn
    have hb := subset_tsupport _ hn
    rw [b.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hb
    change -(1 / 2 : ℝ) ≤ N g - 1 ∧ N g - 1 ≤ 1 / 2 at hb
    apply hg
    refine ⟨e.symm (ideleClassNorm ℚ g), ?_, e.apply_symm_apply _⟩
    change (1 / 2 : ℝ) ≤ N g ∧ N g ≤ 3 / 2
    constructor <;> linarith [hb.1, hb.2]
  let φ : BruhatCompactSupport C𝔽(ℚ) := ⟨_, (mem_bruhatSmoothSubmodule_iff _).2 hs, hcs⟩
  have hφ (g : C𝔽(ℚ)) : φ.val g = introTraceTest (1 : PontryaginDual C𝔽(ℚ)) f g := by
    simp [φ, introTraceTest, N]
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hvol : (ν univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨NeZero.ne _, measure_ne_top _ _⟩
  refine ⟨φ, fun n ↦ ?_⟩
  rw [(introTraceTest_mellin 1 f φ hφ _).2]
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr hvol)
  change mellin (fun x : ℝ ↦ (x : ℂ) ^ c • (b x : ℂ)) (shift(0, t n)) ≠ 0
  rw [mellin_cpow_smul]
  simpa only [Complex.ofReal_zero, zero_add] using hc n

/-- A permutation of any sequence of nonzero samples can move some samples far
enough out that multiplication by the index no longer tends to zero. -/
private theorem spectralLineSamples_bad_numbering (v : ℕ → ℂ) (hv : ∀ n, v n ≠ 0) :
    ∃ σ : Equiv.Perm ℕ, ¬ Tendsto (fun n : ℕ ↦ (n : ℂ) * v (σ n)) atTop (𝓝 0) := by
  let k (j : ℕ) := ⌈‖v (Nat.pair j 0)‖⁻¹⌉₊
  let σ := Nat.pairEquiv.symm.trans
    ((Equiv.prodCongrRight fun j ↦ Equiv.swap (k j) 0).trans Nat.pairEquiv)
  refine ⟨σ, fun h ↦ ?_⟩
  obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp h 1 zero_lt_one
  let n := Nat.pair j (k j)
  have he : σ n = Nat.pair j 0 := by
    change σ (Nat.pairEquiv (j, k j)) = _
    simp [σ, Equiv.prodCongrRight_apply, Nat.pairEquiv_apply]
  have hlt := hj n (Nat.left_le_pair j (k j))
  rw [dist_zero_right, norm_mul, Complex.norm_natCast, he] at hlt
  have hpos := norm_pos_iff.mpr (hv (Nat.pair j 0))
  have hle : ‖v (Nat.pair j 0)‖⁻¹ ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.right_le_pair j (k j))
  exact (not_lt_of_ge ((inv_le_iff_one_le_mul₀ hpos).mp hle)) (by simpa [mul_comm] using hlt)

/-- Paper: Theorem 10.3.1.1, p. 453. Hardy's theorem supplies infinitely many
ordinates of ordinary Riemann zeta zeros on the critical line. -/
private theorem spectralLineSamples_hardy :
    {t : ℝ | riemannZeta (shift(1 / 2, t)) = 0}.Infinite := by
  refine HardyCriticalLine.positiveHardyZeroHeights_infinite.mono fun t ht ↦ ?_
  change riemannZeta (shift(1 / 2, t)) = 0
  push_cast
  exact (HardyCriticalLine.hardyFunctionReal_eq_zero_iff t).mp ht.2

/-- The trivial rational row on the critical line admits a numbering by ℕ. -/
private theorem spectralLineSamples_enumeration :
    Nonempty (ℕ ≃ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2)) := by
  let χ : PontryaginDual C𝔽(ℚ) := 1
  let Z := {z : ℂ | 0 < orderAt(χ, z)}
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  have hfinite : orderAt(χ, (2 : ℂ)) ≠ ⊤ := by
    intro h
    have hp : 0 < orderAt(χ, (2 : ℂ)) := h ▸ WithTop.coe_lt_top (0 : ℤ)
    have := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at this
  have hdisc : Zᶜ ∈ codiscrete ℂ := by
    filter_upwards [hL.meromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
    rcases hz.2 with h | h
    · simp [Z, h]
    · exact (hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
        isPreconnected_univ (mem_univ _) (mem_univ z) hfinite h).elim
  have hZ := (HereditarilyLindelofSpace.isLindelof Z).countable_of_isDiscrete
    (compl_mem_codiscrete_iff.mp hdisc).2
  let U := lineZeros(χ, 1 / 2)
  let : Countable U := (hZ.preimage (f := fun t : ℝ ↦ shift(1 / 2, t))
    (by intro x y h; simpa using congrArg Complex.im h)).to_subtype
  let : Infinite U := (spectralLineSamples_hardy.mono fun t ht ↦
    (spectralLineSelection_mem_lineZeros t).2 ht).to_subtype
  exact nonempty_equiv_of_countable

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
Take F = ℚ, the trivial base character and a = 1/2. Modulate a nonzero smooth radial
bump in y = log |g| by exp(icy). Its entire transform has discrete real zeros. Avoid the
countably many frequencies c for which a sample is zero. Place infinitely many samples
vⱼ at increasing nonadjacent indices nⱼ ≥ 1/|vⱼ|, leaving infinitely many ordinates for
the other indices. Then nⱼ|vⱼ| ≥ 1, which violates decay at k = 1. -/
theorem Printed.spectralLineSamples_rapid_for_any_numbering_false :
    ¬ Printed.spectralLineSamples_rapid_for_any_numbering := by
  classical
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let χ' := Function.update χ 1 (1 : PontryaginDual C𝔽(ℚ))
  have htriv : χ' 1 = 1 := Function.update_self ..
  have hχ' : IsSpectralBasepointChoice χ' := by
    intro ω
    by_cases h : ω = 1
    · subst ω
      rw [htriv]
      rfl
    · simpa [χ', Function.update_of_ne h] using hχ ω
  obtain ⟨e⟩ := spectralLineSamples_enumeration
  obtain ⟨φ, hφ⟩ := spectralLineSamples_nonvanishing (fun n ↦ (e n).val)
  let v (n : ℕ) := ∫ g, φ.val g * ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
    (shift(0, (e n).val)) g ∂ideleClassTamagawaMeasure ℚ
  obtain ⟨σ, hσ⟩ := spectralLineSamples_bad_numbering v hφ
  apply hσ
  have h := hall ℚ χ' hχ' (1 / 2) φ 1
  rw [htriv] at h
  simpa only [pow_one, Equiv.trans_apply, v] using h (σ.trans e) 1

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
As printed: for each integration-by-parts order N > 1, one constant bounds all admitted
Mellin derivatives at nonreal strip zeros by the displayed falling factorial over |z|^N.
The order range on p. 455 includes the low orders in (10.3.2.7). The radial Mellin transform
uses the compact character coefficient for the selected component, as on p. 450 after
(10.3.1.17). See `spectralStripConvolution_traceCauchy` and ERRATA F185. -/
def Printed.spectralStripMellinJet_norm_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s → ∀ (φ : BruhatCompactSupport C𝔽(F)) (N : ℕ), 1 < N →
      let M (ω : PontryaginDual C₁(F)) (z : ℂ) :=
        ∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ z *
          (∫ k : C₁(F), (ω k : ℂ) * φ.val (τ r * k.val) ∂normOneIdeleClassTamagawaMeasure F)
          ∂positiveRealHaar
      ∃ C : ℝ, 0 < C ∧ ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ),
        b ∈ Icc (-α) α → t ≠ 0 → 0 < orderAt(χ ω, shift(a + b, t)) →
        let mult := (orderAt(χ ω, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min mult floorCut(s) else mult
        ∀ i : ℕ, i < count →
          ‖iteratedDeriv i (M ω) (shift(b, t))‖ ≤
            C * (∏ n ∈ Finset.range N, ((i : ℝ) - (n : ℝ))) / ‖shift(b, t)‖ ^ N

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
Over ℚ, changing the basepoint of the trivial norm-one character translates its
critical-line ordinates. Two distinct certified zeros have finite positive order,
and at least one translated ordinate is nonzero. -/
private theorem spectralStripMellinJet_norm_le_false_exists_zero
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : IsSpectralBasepointChoice χ) :
    ∃ (ω : PontryaginDual C₁(ℚ)) (t : ℝ), t ≠ 0 ∧
      0 < orderAt(χ ω, shift(1 / 2, t)) ∧
      0 < (orderAt(χ ω, shift(1 / 2, t))).untop₀.toNat := by
  obtain ⟨r, hr, -⟩ := globalConverse_existsUnique_normTwist (χ 1) (hχ 1)
  have hgauss : adelicStandardGaussian (χ 1) = adelicStandardGaussian (1 : PontryaginDual C𝔽(ℚ)) := by
    apply adelicStandardGaussian_eq_of_restriction
    ext g : 1
    have hg : (χ 1) g.val = 1 := DFunLike.congr_fun (hχ 1) g
    change ((χ 1) g.val : ℂ) * _ ^ (0 : ℂ) = (1 : ℂ) * _ ^ (0 : ℂ)
    simp [hg]
  have hshift : gaussianCompletedHeckeL (χ 1) =
      fun z ↦ gaussianCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ)) (z + r * Complex.I) := by
    funext z
    unfold gaussianCompletedHeckeL
    rw [hgauss]
    exact congrArg _ (by simpa only [zero_add, add_comm ((r : ℂ) * Complex.I) z] using
      ideleClassNormTwist_add_of_eq hr z)
  -- Over ℚ the Gaussian normalization has discriminant factor one.
  have horder (ψ : PontryaginDual C𝔽(ℚ)) (z : ℂ) :
      orderAt(ψ, z) = meromorphicOrderAt (gaussianCompletedHeckeL ψ) z := by
    have hC := continuedCompletedHeckeL_spec ψ
    have hG := globalIdelicZFunction_meromorphic (adelicStandardGaussian ψ) ψ
    apply meromorphicOrderAt_congr
    apply meromorphicContinuation_eventuallyEq hC.1.meromorphicOn hG.meromorphicOn _ z
    intro w hw
    change continuedCompletedHeckeL ψ w = gaussianCompletedHeckeL ψ w
    rw [hC.2 ⟨w, hw⟩, gaussianCompletedHeckeL_eq_completedHeckeL ψ w hw]
    norm_num [Rat.numberField_discr]
  obtain ⟨u, v, _, huv, _, hu, hv, _⟩ := spectralLineSelection_three_zeta_zeros
  obtain ⟨s, hsr, hs⟩ : ∃ s : ℝ, s ≠ r ∧ riemannZeta (shift(1 / 2, s)) = 0 := by
    by_cases h : u = r
    · exact ⟨v, h ▸ huv.ne', hv⟩
    · exact ⟨u, h, hu⟩
  have he : shift(1 / 2, (s - r : ℝ)) + (r : ℂ) * Complex.I = shift(1 / 2, s) := by
    push_cast
    ring
  obtain ⟨n, hn, hz⟩ := spectralLineSelection_zeta_order s
  refine ⟨1, s - r, sub_ne_zero.mpr hsr, ?_⟩
  rw [horder, hshift, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, he, ← horder, hn]
  simpa using hz.mpr hs

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
At any prescribed compact character and frequency, the Mellin integral is nonzero for some
Bruhat test. The norm section identifies the full character with the product of the compact
character and the radial oscillation. The inverse of this character times a smooth bump
in the log norm gives a test whose Mellin integral is the norm-one Haar mass times the
positive integral of the bump.
The map `τ` is a section of the idelic norm, as on p. 455; without that the statement fails
(for the constant map every test has Mellin value zero, #6741). -/
private theorem spectralStripMellinJet_norm_le_false_exists_mellin
    (τ : ℝ≥0ˣ →ₜ* C𝔽(ℚ)) (_hτ : Function.RightInverse τ (ideleClassNorm ℚ))
    (ω : PontryaginDual C₁(ℚ)) (t : ℝ) :
    ∃ φ : BruhatCompactSupport C𝔽(ℚ),
      (∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ (shift(0, t)) *
        (∫ k : C₁(ℚ), (ω k : ℂ) * φ.val (τ r * k.val)
          ∂normOneIdeleClassTamagawaMeasure ℚ) ∂positiveRealHaar) ≠ 0 := by
  obtain ⟨e, he⟩ := spectralPlancherel_exists_dualEquiv ℚ τ _hτ
  let η := e (Multiplicative.ofAdd t, ω)
  let B : ContDiffBump (0 : ℝ) := default
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := ℚ) η⁻¹ (fun y ↦ (B y : ℂ))
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
    (B.hasCompactSupport.comp_left Complex.ofReal_zero)
  let phase (r : ℝ≥0ˣ) := Circle.exp (t * Real.log (r.val : ℝ))
  have htest (r : ℝ≥0ˣ) (k : C₁(ℚ)) : (ω k : ℂ) * φ.val (τ r * k.val) =
      ((phase r)⁻¹ : Circle) * (B (Real.log (r.val : ℝ)) : ℂ) := by
    have hn : ideleClassNorm ℚ (τ r * k.val) = r := by
      rw [map_mul, _hτ r, MonoidHom.mem_ker.mp k.property, mul_one]
    have hk : ω k * η⁻¹ (τ r * k.val) = (phase r)⁻¹ := by
      change ω k * (e (Multiplicative.ofAdd t, ω) (τ r * k.val))⁻¹ = _
      rw [he, mul_inv, mul_inv_cancel_left]
    rw [hφ, hn, ← mul_assoc, ← Circle.coe_mul, hk]
  have hphase (r : ℝ≥0ˣ) : ((r.val : ℝ) : ℂ) ^ (shift(0, t)) = (phase r : ℂ) := by
    have hr := NNReal.coe_pos.mpr (Units.zero_lt r)
    dsimp only [phase]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
      ← Complex.ofReal_log hr.le, Complex.ofReal_zero, zero_add, Circle.coe_exp,
      Complex.ofReal_mul]
    congr 1
    ring
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace C₁(ℚ) := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  have hmass : ν.real univ ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨NeZero.ne _, measure_ne_top _ _⟩
  have hlog : (∫ r : ℝ≥0ˣ, (B (Real.log (r.val : ℝ)) : ℂ) ∂positiveRealHaar) =
      ((∫ y : ℝ, B y : ℝ) : ℂ) := by
    simpa only [sub_zero, mul_one, Complex.cpow_zero, zero_mul, Complex.exp_zero, one_mul,
      integral_complex_ofReal] using grh_shift_integral (fun y ↦ (B y : ℂ))
        (Complex.continuous_ofReal.comp B.continuous) (fun _ ↦ 1) (fun _ ↦ rfl) 0 0
  refine ⟨φ, ?_⟩
  simp_rw [htest, integral_const, hphase, mul_smul_comm, ← mul_assoc, ← Circle.coe_mul,
    mul_inv_cancel, Circle.coe_one, one_mul]
  rw [integral_smul, hlog, Complex.real_smul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hmass) (Complex.ofReal_ne_zero.mpr B.integral_pos.ne')

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
Take F = ℚ, any spectral basepoint choice, a = 1/2, α = 3, s = 2 and N = 2, and test the
bound at the interior parameter b = 0 and at order i = 0. The order-zero multiplicity is at
least one at the zero of `spectralStripMellinJet_norm_le_false_exists_zero`, and the factor
for n = 0 in the falling factorial vanishes, so the right-hand side is zero for every
constant C. A test as in `spectralStripMellinJet_norm_le_false_exists_mellin` has nonzero
Mellin value there. -/
theorem Printed.spectralStripMellinJet_norm_le_false :
    ¬ Printed.spectralStripMellinJet_norm_le := by
  intro h
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice (F := ℚ)
  let q : IdeleGroup (𝓞 ℚ) ℚ →ₜ* C𝔽(ℚ) :=
    ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽(ℚ) :=
    q.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : Function.RightInverse τ (ideleClassNorm ℚ) :=
    canonicalIdeleNormSection_rightInverse ℚ
  obtain ⟨ω, t, ht, hord, hmult⟩ := spectralStripMellinJet_norm_le_false_exists_zero χ hχ
  obtain ⟨φ, hφ⟩ := spectralStripMellinJet_norm_le_false_exists_mellin τ hτ ω t
  obtain ⟨C, hC, hbound⟩ :=
    h ℚ χ hχ τ hτ (1 / 2) 3 2 (by norm_num) (by norm_num) φ 2 (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Icc (-3 : ℝ) 3 := by norm_num
  have hshift : shift((1 : ℝ) / 2 + 0, t) = shift(1 / 2, t) := by norm_num
  have hord' : 0 < orderAt(χ ω, shift(1 / 2 + 0, t)) := by rw [hshift]; exact hord
  have hmult' : 0 < (orderAt(χ ω, shift(1 / 2 + 0, t))).untop₀.toNat := by
    rw [hshift]; exact hmult
  have hif : ¬ ((0 : ℝ) = -3 ∨ (0 : ℝ) = 3) := by norm_num
  have hcount : 0 < (if (0 : ℝ) = -3 ∨ (0 : ℝ) = 3 then
      min (orderAt(χ ω, shift(1 / 2 + 0, t))).untop₀.toNat (floorCut((2 : ℝ)))
      else (orderAt(χ ω, shift(1 / 2 + 0, t))).untop₀.toNat) := by
    simpa only [hif, ite_false] using hmult'
  have hle := hbound ω 0 t hmem ht hord' 0 hcount
  have hprod : (∏ n ∈ Finset.range 2, (((0 : ℕ) : ℝ) - ((n : ℕ) : ℝ))) = 0 := by
    simp [Finset.prod_range_succ]
  rw [hprod, mul_zero, zero_div] at hle
  have hnorm : ‖iteratedDeriv 0 ((fun (ω : PontryaginDual C₁(ℚ)) (z : ℂ) ↦
      ∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ z *
        (∫ k : C₁(ℚ), (ω k : ℂ) * φ.val (τ r * k.val)
          ∂normOneIdeleClassTamagawaMeasure ℚ) ∂positiveRealHaar) ω) (shift(0, t))‖ ≤ 0 := hle
  have hzero : (∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ (shift(0, t)) *
        (∫ k : C₁(ℚ), (ω k : ℂ) * φ.val (τ r * k.val)
          ∂normOneIdeleClassTamagawaMeasure ℚ) ∂positiveRealHaar) = 0 := by
    simpa using norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  exact hφ hzero

end RiemannMasullo
