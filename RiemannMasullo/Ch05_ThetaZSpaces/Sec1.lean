module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.UniformSpace.CompactConvergence
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WithSeminorms
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Barrelled
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Topological spaces of adelic theta functions and idelic Z-functions

Masullo, §5.1, pp. 221–230. The finite set in the S-local declarations indexes the
finite places. All archimedean places are included.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

set_option quotPrecheck false

section MeromorphicTarget

variable {X : Type*} [TopologicalSpace X]
variable (chart : X → ℂ → X) (orderBound : X → WithTop ℤ)

local notation "Regular" => {c : X // 0 ≤ orderBound c}

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
A function on the regular locus admits a continuation with bounded poles if it
extends in the complex coordinates with the prescribed lower bounds on order.
Deviation: The coordinates are centered at each point. The continuation is required
to be analytic at every point where the order bound permits no pole. -/
def HasMeromorphicContinuationWithPoleBound (u : C(Regular, ℂ)) : Prop :=
  ∃ Z : X → ℂ, (∀ c : Regular, Z c = u c) ∧ ∀ c : X,
    let germ := fun z ↦ Z (chart c z)
    MeromorphicAt germ 0 ∧ orderBound c ≤ meromorphicOrderAt germ 0 ∧
      (0 ≤ orderBound c → AnalyticAt ℂ germ 0)

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
The continuation condition is preserved by the complex vector space operations.
Deviation: These are the closure fields for the submodule of regular restrictions. -/
theorem meromorphicContinuationWithPoleBound_closed :
    let admissible := HasMeromorphicContinuationWithPoleBound chart orderBound
    admissible 0 ∧ (∀ u v, admissible u → admissible v → admissible (u + v)) ∧
      (∀ (a : ℂ) u, admissible u → admissible (a • u)) := by
  refine ⟨⟨0, fun _ ↦ rfl, fun c ↦ ?_⟩, ?_, ?_⟩
  · refine ⟨analyticAt_const.meromorphicAt, ?_, fun _ ↦ analyticAt_const⟩
    exact le_top.trans_eq (meromorphicOrderAt_eq_top_iff.2
      (Filter.Eventually.of_forall fun _ ↦ rfl)).symm
  · rintro u v ⟨Zu, hu, hZu⟩ ⟨Zv, hv, hZv⟩
    refine ⟨Zu + Zv, fun c ↦ by simp [hu, hv], fun c ↦ ?_⟩
    obtain ⟨mu, ou, au⟩ := hZu c
    obtain ⟨mv, ov, av⟩ := hZv c
    refine ⟨mu.add mv, ?_, fun h ↦ (au h).add (av h)⟩
    exact (le_min ou ov).trans (meromorphicOrderAt_add mu mv)
  · rintro a u ⟨Z, hu, hZ⟩
    refine ⟨a • Z, fun c ↦ by simp [hu], fun c ↦ ?_⟩
    obtain ⟨m, o, an⟩ := hZ c
    refine ⟨m.const_smul a, ?_, fun h ↦ (an h).const_smul⟩
    show orderBound c ≤ meromorphicOrderAt (a • fun z ↦ Z (chart c z)) 0
    by_cases ha : a = 0
    · subst ha
      exact le_top.trans_eq (meromorphicOrderAt_eq_top_iff.2
        (Filter.Eventually.of_forall fun _ ↦ zero_smul ℂ _)).symm
    · rwa [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt ha]

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
Meromorphic functions with bounded poles form a complex vector space with the
compact-open topology of their restrictions to the complement of the allowed poles.
Deviation: We represent the functions by their regular values and use the pole order
bounds and compact convergence topology specified in §5.1.3. -/
def meromorphicWithPoleBound : Submodule ℂ C(Regular, ℂ) where
  carrier := {u | HasMeromorphicContinuationWithPoleBound chart orderBound u}
  zero_mem' := (meromorphicContinuationWithPoleBound_closed chart orderBound).1
  add_mem' := fun hu hv ↦ (meromorphicContinuationWithPoleBound_closed chart orderBound).2.1
    _ _ hu hv
  smul_mem' := (meromorphicContinuationWithPoleBound_closed chart orderBound).2.2

/-- Paper: Definition 5.1.1.1(1)–(2), p. 223.
With the zero divisor, membership in the meromorphic target amounts to holomorphy.
Deviation: This checks the target in the case where no poles are allowed. -/
theorem mem_meromorphicWithPoleBound_zero_iff
    (u : C({c : X // 0 ≤ (0 : WithTop ℤ)}, ℂ)) :
    u ∈ meromorphicWithPoleBound chart (fun _ ↦ 0) ↔
      ∀ c : X, AnalyticAt ℂ (fun z ↦ u ⟨chart c z, le_rfl⟩) 0 := by
  constructor
  · rintro ⟨Z, hZ, h⟩ c
    have hZ' : Z = fun x ↦ u ⟨x, le_rfl⟩ := funext fun x ↦ hZ ⟨x, le_rfl⟩
    subst hZ'
    exact (h c).2.2 le_rfl
  · intro h
    refine ⟨fun x ↦ u ⟨x, le_rfl⟩, fun _ ↦ rfl, fun c ↦ ?_⟩
    exact ⟨(h c).meromorphicAt, (h c).meromorphicOrderAt_nonneg, fun _ ↦ h c⟩

end MeromorphicTarget

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ" => SIdeleQuotient F S
local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "X𝔽" => QuasiCharacter C𝔽
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "m𝔽" => ideleClassNorm F
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "normChart𝔽" => quasiCharacterNormTwist (G := C𝔽) m𝔽
  (isProperMap_ideleClassNorm F).continuous
local notation "normChartₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous

/-- Paper: Definition 5.1.1.1(1), p. 223.
The possible global poles are simple and occur at the trivial and norm characters.
Deviation: The simple-pole bound from §5.1.3 is built into the target here. -/
def globalIdelicOrderBound (c : X𝔽) : WithTop ℤ :=
  open Classical in
  if c = 1 ∨ c = ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 then -1 else 0

/-- Paper: Definition 5.1.1.1(1), p. 223.
The trivial character allows a simple pole and the squared norm character allows none. -/
theorem globalIdelicOrderBound_one_and_normSquared :
    globalIdelicOrderBound (1 : X𝔽) = -1 ∧
      globalIdelicOrderBound (ideleClassNormTwist (1 : PontryaginDual C𝔽) 2) = 0 := by
  refine ⟨ite_eq_left (Or.inl rfl), ite_eq_right ?_⟩
  obtain ⟨g, hg⟩ :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1 (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  have hval : ∀ s : ℂ, ideleClassNormTwist (1 : PontryaginDual C𝔽) s g = (2 : ℂ) ^ s := by
    intro s
    change (((1 : PontryaginDual C𝔽) g : Circle) : ℂ) *
      (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s = _
    rw [hg]
    simp
  rintro (h | h)
  · have := DFunLike.congr_fun h g
    rw [hval] at this
    norm_num at this
  · have := DFunLike.congr_fun h g
    rw [hval, hval] at this
    norm_num at this

local notation "globalMeromorphic" =>
  meromorphicWithPoleBound (X := X𝔽) normChart𝔽 (globalIdelicOrderBound (F := F))

section NormCoordinates

variable {G : Type*} [CommGroup G] [TopologicalSpace G] (m : G →* ℝ≥0ˣ)
local notation "unitaryChar" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)

/-- Subtracting the real abscissa from a quasi-character makes it unitary. -/
private theorem exists_unitary_normTwist [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    ∃ (χ : PontryaginDual G) (s : ℂ), quasiCharacterNormTwist m hm.continuous
      ((unitaryChar).comp χ) s = c := by
  let s := quasiCharacterAbscissa m hm hne c
  let d := quasiCharacterNormTwist m hm.continuous c (-(s : ℂ))
  have hpos (g : G) : 0 < ((m g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hd (g : G) : ‖d g‖ = 1 := by
    change ‖c g * (((m g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ))‖ = 1
    rw [norm_mul, norm_quasiCharacter_eq_rpow_abscissa m hm hne,
      Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
    exact (Real.rpow_add (hpos g) s (-s)).symm.trans (by simp)
  let χ : PontryaginDual G :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
      map_one' := Circle.ext (map_one d)
      map_mul' := fun x y ↦ Circle.ext (map_mul d x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, s, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  change c g * _ ^ (-(s : ℂ)) * _ ^ (s : ℂ) = c g
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hpos g).ne'),
    neg_add_cancel, Complex.cpow_zero, mul_one]

/-- Changing the center of the norm coordinate translates its complex argument. -/
private theorem normTwist_normTwist (hm : Continuous m) (c : QuasiCharacter G) (s z : ℂ) :
    quasiCharacterNormTwist m hm (quasiCharacterNormTwist m hm c s) z =
      quasiCharacterNormTwist m hm c (z + s) := by
  ext1 g
  let N : ℂ := (((m g : ℝ≥0) : ℝ) : ℂ)
  change c g * N ^ s * N ^ z = c g * N ^ (z + s)
  rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (m g).ne_zero)), mul_assoc]

/-- Continuity at zero in the centered norm chart gives continuity at its center. -/
private theorem continuousAt_of_normTwist (hm : Continuous m) (hchart : HasNormTwistCharts m)
    {Z : QuasiCharacter G → ℂ} (c : QuasiCharacter G)
    (h : ContinuousAt (fun z ↦ Z (quasiCharacterNormTwist m hm c z)) 0) :
    ContinuousAt Z c := by
  obtain ⟨e, hc, he, hinv⟩ := hchart c
  rw [← he] at h
  refine (h.comp (e.continuousAt hc)).congr ?_
  filter_upwards [e.open_source.mem_nhds hc] with x hx
  change Z (quasiCharacterNormTwist m hm c (e x)) = Z x
  congr 1
  exact (ContinuousMonoidHom.ext fun g ↦ (hinv _ (e.map_source hx) g).symm).trans (e.left_inv hx)

end NormCoordinates

private theorem exists_ideleClassNormTwist (c : X𝔽) :
    ∃ (χ : PontryaginDual C𝔽) (s : ℂ), ideleClassNormTwist χ s = c := by
  let : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  exact exists_unitary_normTwist m𝔽 (isProperMap_ideleClassNorm F) ideleClassNorm_ne_one c

private theorem globalZ_centered (f : ℬ𝔽) (c : X𝔽) :
    let Z := fun z ↦ globalIdelicZFunction f (normChart𝔽 c z)
    MeromorphicAt Z 0 ∧ globalIdelicOrderBound c ≤ meromorphicOrderAt Z 0 ∧
      (0 ≤ globalIdelicOrderBound c → AnalyticAt ℂ Z 0) := by
  obtain ⟨χ, s, rfl⟩ := exists_ideleClassNormTwist c
  let Z := fun z ↦ globalIdelicZFunction f (ideleClassNormTwist χ z)
  have hshift (z : ℂ) : normChart𝔽 (ideleClassNormTwist χ s) z = ideleClassNormTwist χ (z + s) :=
    normTwist_normTwist _ _ _ s z
  simp only [hshift]
  change MeromorphicAt (fun z ↦ Z (z + s)) 0 ∧ _ ∧ _
  have hnf : MeromorphicNFAt (fun z ↦ Z (z + s)) 0 :=
    meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr (by
      simpa only [zero_add] using globalIdelicZFunction_meromorphic f χ (Set.mem_univ s))
  have ho : globalIdelicOrderBound (ideleClassNormTwist χ s) ≤
      meromorphicOrderAt (fun z ↦ Z (z + s)) 0 := by
    rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, zero_add, globalIdelicOrderBound]
    split_ifs with hp
    · exact (globalIdelicZFunction_poles f χ).2 s
    · exact ((globalIdelicZFunction_poles f χ).1 s (not_or.mp hp)).meromorphicOrderAt_nonneg
  exact ⟨hnf.meromorphicAt, ho, fun h ↦ hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp (h.trans ho)⟩

/-- Paper: Definition 5.1.1.1(1), p. 223.
The global Z-function is continuous on the locus with no allowed pole. -/
theorem globalIdelicZFunction_continuous_regular (f : ℬ𝔽) :
    Continuous (fun c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c} ↦
      globalIdelicZFunction f c.val) := by
  refine continuous_iff_continuousAt.mpr fun c ↦ ?_
  exact (continuousAt_of_normTwist _ _ (ideleClass_hasNormTwistCharts F) c.val
    ((globalZ_centered f c.val).2.2 c.property).continuousAt).comp continuous_subtype_val.continuousAt

local notation "globalZValues" => fun f : ℬ𝔽 ↦
  (⟨fun c ↦ globalIdelicZFunction f c.val, globalIdelicZFunction_continuous_regular f⟩ :
    C({c : X𝔽 // 0 ≤ globalIdelicOrderBound c}, ℂ))

/-- Paper: Definition 5.1.1.1(1), p. 223.
The global Z-function satisfies the prescribed global pole bounds. -/
theorem globalIdelicZFunction_mem (f : ℬ𝔽) :
    globalZValues f ∈ globalMeromorphic := ⟨globalIdelicZFunction f, fun _ ↦ rfl, globalZ_centered f⟩

/-- Paper: Definition 5.1.1.1(1), p. 223.
The regular values of global Z-functions depend complex linearly on the test function. -/
theorem globalIdelicZFunction_isLinear :
    IsLinearMap ℂ (globalZValues : ℬ𝔽 → _) := by
  classical
  let : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have hpos (g : C𝔽) : 0 < ((ideleClassNorm F g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hne (g : C𝔽) : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hpos g).ne'
  -- Every quasi-character lies on a norm-twist chart of a unitary character.
  have hdecomp (c : X𝔽) : ∃ (χ : PontryaginDual C𝔽) (s : ℂ), ideleClassNormTwist χ s = c := by
    let s := quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) c
    let d := c * ideleClassNormTwist (1 : PontryaginDual C𝔽) (-(s : ℂ))
    have hd (g : C𝔽) : ‖d g‖ = 1 := by
      change ‖c g * (1 * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ)))‖ = 1
      rw [one_mul, norm_mul, norm_quasiCharacter_eq_rpow_abscissa _
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)),
        Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
      change ((ideleClassNorm F g : ℝ≥0) : ℝ) ^ s * ((ideleClassNorm F g : ℝ≥0) : ℝ) ^ (-s) = 1
      rw [← Real.rpow_add (hpos g), add_neg_cancel, Real.rpow_zero]
    let χ : PontryaginDual C𝔽 :=
      { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
        map_one' := Circle.ext (map_one d)
        map_mul' := fun g h ↦ Circle.ext (map_mul d g h)
        continuous_toFun := d.continuous.subtype_mk _ }
    refine ⟨χ, s, ?_⟩
    ext1 g
    change (c g * (1 * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ)))) *
      (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (s : ℂ) = c g
    rw [one_mul, mul_assoc, ← Complex.cpow_add _ _ (hne g), neg_add_cancel, Complex.cpow_zero,
      mul_one]
  -- The norm-twist chart centred at a point of such a chart is a translate of it.
  have hchart (χ : PontryaginDual C𝔽) (w z : ℂ) :
      normChart𝔽 (ideleClassNormTwist χ w) z = ideleClassNormTwist χ (w + z) := by
    ext1 g
    change ((χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ w) *
      (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ z =
        (χ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (w + z)
    rw [Complex.cpow_add _ _ (hne g), mul_assoc]
  have habs (χ : PontryaginDual C𝔽) (s : ℂ) :
      quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
        (ideleClassNorm_ne_one (F := F)) (ideleClassNormTwist χ s) = s.re :=
    quasiCharacterAbscissa_ideleClassNormTwist χ s
  have habs₁ : quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) (1 : X𝔽) = 0 := by
    have := quasiCharacterAbscissa_of_unitary_twist (ideleClassNorm F)
      (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) (1 : X𝔽)
      (1 : PontryaginDual C𝔽) 0 (fun g ↦ by simp)
    simpa using this
  -- To the right of one every quasi-character is regular.
  have hregular (χ : PontryaginDual C𝔽) (w : ℂ) (hw : 1 < w.re) :
      0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ w) := by
    have h₁ : ideleClassNormTwist χ w ≠ 1 := fun h ↦ by
      have := habs χ w
      rw [h, habs₁] at this
      linarith
    have h₂ : ideleClassNormTwist χ w ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 :=
      fun h ↦ by
        have := habs χ w
        rw [h, habs] at this
        simp only [Complex.one_re] at this
        linarith
    simp [globalIdelicOrderBound, h₁, h₂]
  -- Linear relations between zeta integrals to the right of one persist at regular points.
  have key (f₁ f₂ f₃ : ℬ𝔽) (a b : ℂ)
      (hI : ∀ c : X𝔽, c ∈ (relativeRightHalfPlane (G := C𝔽) (ideleClassNorm F)
        (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 1 : Set X𝔽) →
        globalIdelicZetaIntegral f₃ c =
          a * globalIdelicZetaIntegral f₁ c + b * globalIdelicZetaIntegral f₂ c)
      (c : X𝔽) (hc : 0 ≤ globalIdelicOrderBound c) :
      globalIdelicZFunction f₃ c =
        a * globalIdelicZFunction f₁ c + b * globalIdelicZFunction f₂ c := by
    obtain ⟨χ, s₀, rfl⟩ := hdecomp c
    obtain ⟨Z₁, hZ₁, h₁⟩ := globalIdelicZFunction_mem f₁
    obtain ⟨Z₂, hZ₂, h₂⟩ := globalIdelicZFunction_mem f₂
    obtain ⟨Z₃, hZ₃, h₃⟩ := globalIdelicZFunction_mem f₃
    have hM (Z : X𝔽 → ℂ)
        (hZ : ∀ c : X𝔽, MeromorphicAt (fun z ↦ Z (normChart𝔽 c z)) 0) (w : ℂ) :
        MeromorphicAt (fun w ↦ Z (ideleClassNormTwist χ w)) w := by
      have h := hZ (ideleClassNormTwist χ w)
      simp only [hchart] at h
      have h' : MeromorphicAt ((fun w ↦ Z (ideleClassNormTwist χ w)) ∘ (· + w)) 0 := by
        simpa only [Function.comp_def, add_comm] using h
      simpa using meromorphicAt_comp_add_const_iff_meromorphicAt.mp h'
    have hA (Z : X𝔽 → ℂ)
        (hZ : AnalyticAt ℂ (fun z ↦ Z (normChart𝔽 (ideleClassNormTwist χ s₀) z)) 0) :
        AnalyticAt ℂ (fun w ↦ Z (ideleClassNormTwist χ w)) s₀ := by
      simp only [hchart] at hZ
      have h := hZ.comp_of_eq
        (analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun w : ℂ ↦ w - s₀) s₀)
        (sub_self s₀)
      simpa only [Function.comp_def, Pi.sub_apply, id_eq, add_sub_cancel] using h
    let D : ℂ → ℂ := fun w ↦ Z₃ (ideleClassNormTwist χ w) -
      (a * Z₁ (ideleClassNormTwist χ w) + b * Z₂ (ideleClassNormTwist χ w))
    have hDM : MeromorphicOn D Set.univ := fun w _ ↦
      (hM Z₃ (fun c ↦ (h₃ c).1) w).sub
        ((analyticAt_const.meromorphicAt.mul (hM Z₁ (fun c ↦ (h₁ c).1) w)).add
          (analyticAt_const.meromorphicAt.mul (hM Z₂ (fun c ↦ (h₂ c).1) w)))
    have hDA : AnalyticAt ℂ D s₀ :=
      (hA Z₃ ((h₃ _).2.2 hc)).sub ((analyticAt_const.mul (hA Z₁ ((h₁ _).2.2 hc))).add
        (analyticAt_const.mul (hA Z₂ ((h₂ _).2.2 hc))))
    have hval (Z : X𝔽 → ℂ) (f : ℬ𝔽) (hZ : ∀ c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c},
        Z c = globalZValues f c) (c : X𝔽) (hc : 0 ≤ globalIdelicOrderBound c) :
        Z c = globalIdelicZFunction f c :=
      hZ ⟨c, hc⟩
    have hEq (w : ℂ) (hw : 1 < w.re) : D w = 0 := by
      have hm : ideleClassNormTwist χ w ∈ (relativeRightHalfPlane (G := C𝔽) (ideleClassNorm F)
          (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 1 : Set X𝔽) := by
        change 1 < quasiCharacterAbscissa _ _ _ _
        rwa [habs]
      have hr := hregular χ w hw
      simp only [D, hval Z₁ f₁ hZ₁ _ hr, hval Z₂ f₂ hZ₂ _ hr, hval Z₃ f₃ hZ₃ _ hr,
        globalIdelicZFunction_eq_integral _ hm, hI _ hm, sub_self]
    have hnear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have htop : meromorphicOrderAt D 2 = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr ((hnear.mono hEq).filter_mono nhdsWithin_le_nhds)
    have ho := hDM.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (2 : ℂ)) (Set.mem_univ s₀) htop
    have hloc : D =ᶠ[𝓝[≠] s₀] fun _ ↦ 0 := meromorphicOrderAt_eq_top_iff.mp ho
    have hD₀ : D s₀ = 0 :=
      tendsto_nhds_unique (hDA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' hloc.symm)
    rw [← hval Z₁ f₁ hZ₁ _ hc, ← hval Z₂ f₂ hZ₂ _ hc, ← hval Z₃ f₃ hZ₃ _ hc]
    exact sub_eq_zero.mp hD₀
  refine ⟨fun f g ↦ ?_, fun a f ↦ ?_⟩
  · ext c
    change globalIdelicZFunction (f + g) c.val =
      globalIdelicZFunction f c.val + globalIdelicZFunction g c.val
    have h := key f g (f + g) 1 1 (fun c hc ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        add_mul (f (Multiplicative.ofAdd x.val)) (g (Multiplicative.ofAdd x.val))
          (c (QuotientGroup.mk x)))).trans
        (integral_add (globalIdelicZetaIntegral_integrable f c hc)
          (globalIdelicZetaIntegral_integrable g c hc))).trans
        (congrArg₂ (· + ·) (one_mul _).symm (one_mul _).symm)) c.val c.property
    exact h.trans (congrArg₂ (· + ·) (one_mul _) (one_mul _))
  · ext c
    change globalIdelicZFunction (a • f) c.val = a * globalIdelicZFunction f c.val
    have h := key f f (a • f) a 0 (fun c hc ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        mul_assoc a (f (Multiplicative.ofAdd x.val)) (c (QuotientGroup.mk x)))).trans
        (integral_const_mul a _)).trans
        ((add_zero _).symm.trans (congrArg (_ + ·) (zero_mul _).symm))) c.val c.property
    exact h.trans ((congrArg (_ + ·) (zero_mul _)).trans (add_zero _))

/-- Paper: Definition 5.1.1.1(1), p. 223.
The global idelic Mellin transform sends a test function to its continued Z-function.
Deviation: The target uses the bounded-pole model of §5.1.3. -/
def globalIdelicMellin : ℬ𝔽 →ₗ[ℂ] ↥globalMeromorphic :=
  LinearMap.codRestrict globalMeromorphic
    (IsLinearMap.mk' globalZValues globalIdelicZFunction_isLinear) globalIdelicZFunction_mem

/-- Paper: Definition 5.1.1.1(1), p. 223.
At a regular character the global transform evaluates to the continued global zeta integral. -/
theorem globalIdelicMellin_apply (f : ℬ𝔽) (c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c}) :
    (globalIdelicMellin (F := F) f).val c = globalIdelicZFunction f c.val := rfl

/-- Paper: Definition 5.1.1.1(2), p. 223.
The allowed S-local pole multiplicity is that of the correcting factor.
Deviation: We use the nonpositive part of the meromorphic order, as in §3.3.1.
The bound is zero at the zeros of the correcting factor. -/
def sLocalIdelicOrderBound (c : Xₛ) : WithTop ℤ :=
  min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ c z)) 0)

open Filter Set in
/-- Paper: Definition 5.1.1.1(2), p. 223.
For the rational field with only the real place, the trivial character allows a simple pole
and the norm character allows no pole.
Deviation: This checks the order bound against the real Tate factor. -/
theorem sLocalIdelicOrderBound_rat_archimedean :
    sLocalIdelicOrderBound (F := ℚ) (S := ∅) 1 = -1 ∧
      sLocalIdelicOrderBound (F := ℚ) (S := ∅)
        (quasiCharacterNormTwist (G := SIdeleQuotient ℚ ∅) (sIdeleQuotientNorm ℚ ∅)
          (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous 1 1) = 0 := by
  let m := sIdeleQuotientNorm ℚ ∅
  let hm := (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
  let chart := quasiCharacterNormTwist (G := SIdeleQuotient ℚ ∅) m hm (1 : QuasiCharacter (SIdeleQuotient ℚ ∅))
  let ρ := fun z ↦ sLocalRhoFactor (chart z)
  have hΓ (z : ℂ) : sLocalHeckeL (chart z) = Complex.Gammaℝ z := by
    rw [sLocalHeckeL_archimedean, InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (by simp),
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (by simp), pow_one, pow_zero, mul_one]
  have hr : ρ =ᶠ[𝓝[≠] 0] fun z ↦ Complex.Gammaℝ z / Complex.Gammaℝ (1 - z) := by
    filter_upwards [nhdsNE_le_codiscrete (0 : ℂ)
      (sLocalRhoFactor_eq_epsilon_mul (1 : PontryaginDual (SIdeleQuotient ℚ ∅)))] with z hz
    let U := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
    have hdual : dualQuasiCharacter (G := SIdeleQuotient ℚ ∅) m hm (chart z) = chart (1 - z) :=
      (sLocal_dual_chart (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) z).trans
        (congrArg (fun χ ↦ quasiCharacterNormTwist (G := SIdeleQuotient ℚ ∅) m hm
          (U.comp χ) (1 - z)) inv_one)
    change ρ z = sLocalEpsilonFactor (chart z) * (sLocalHeckeL (chart z) /
      sLocalHeckeL (dualQuasiCharacter (G := SIdeleQuotient ℚ ∅) m hm (chart z))) at hz
    rw [hdual, hΓ, hΓ, show sLocalEpsilonFactor (chart z) = 1 from
      sLocalEpsilonFactor_archimedean_trivial z, one_mul] at hz
    exact hz
  have hden : ContinuousAt (fun z : ℂ ↦ Complex.Gammaℝ (1 - z)) 0 := by
    have h : ContinuousAt Complex.Gammaℝ (1 - (0 : ℂ)) := by
      simpa only [sub_zero] using Complex.hasDerivAt_Gammaℝ_one.continuousAt
    exact h.comp (continuous_const.sub continuous_id).continuousAt
  have hlim : Filter.Tendsto (id * ρ) (𝓝[≠] 0) (𝓝 (2 : ℂ)) := by
    have h := Complex.Gammaℝ_residue_zero.div (hden.tendsto.mono_left nhdsWithin_le_nhds)
      (by simp [Complex.Gammaℝ_one])
    apply Filter.Tendsto.congr' _ (by simpa [Complex.Gammaℝ_one] using h)
    exact hr.mono fun z hz ↦ by simp only [Pi.mul_apply, Pi.div_apply, id_eq, hz, mul_div_assoc]
  have hmρ : MeromorphicAt ρ 0 := sLocalRhoFactor_meromorphic
    (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) 0
  have ho := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    ((MeromorphicAt.id 0).mul hmρ)).mp ⟨2, two_ne_zero, hlim⟩
  rw [meromorphicOrderAt_mul (MeromorphicAt.id _) hmρ, meromorphicOrderAt_id] at ho
  have hp : meromorphicOrderAt ρ 0 = -1 := by
    generalize meromorphicOrderAt ρ 0 = k at *
    induction k using WithTop.recTopCoe with
    | top => simp at ho
    | coe k =>
      have he : (1 : ℤ) + k = 0 := WithTop.coe_injective ho
      exact congrArg (fun a : ℤ ↦ (a : WithTop ℤ)) (show k = -1 by omega)
  constructor
  · change min 0 (meromorphicOrderAt ρ 0) = -1
    rw [hp]
    exact min_eq_right (WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by decide))
  · change min 0 (meromorphicOrderAt
        (fun z ↦ sLocalRhoFactor (quasiCharacterNormTwist (G := SIdeleQuotient ℚ ∅) m hm (chart 1) z)) 0) = 0
    apply min_eq_left
    have ha := sLocalRhoFactor_iteratedDeriv_analyticOn
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) 0 1 (by norm_num)
    rw [iteratedDeriv_zero] at ha
    have h1 : AnalyticAt ℂ ρ (1 + 0) := by rw [add_zero]; exact ha
    have h := h1.comp (show AnalyticAt ℂ (fun z ↦ 1 + z) 0 by fun_prop)
    have shift (z : ℂ) : quasiCharacterNormTwist (G := SIdeleQuotient ℚ ∅) m hm (chart 1) z =
        chart (1 + z) := sLocal_chart_twist (1 : PontryaginDual (SIdeleQuotient ℚ ∅)) 1 z
    simp only [shift]
    exact h.meromorphicOrderAt_nonneg

local notation "sLocalMeromorphic" =>
  meromorphicWithPoleBound (X := Xₛ) normChartₛ (sLocalIdelicOrderBound (F := F) (S := S))

local notation "unitaryₛ(" χ ")" => normChartₛ
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)

private theorem exists_sLocalNormTwist (c : Xₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), unitaryₛ(χ) s = c := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  exact exists_unitary_normTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S)
    ⟨σ t, (hσ t).trans_ne ht⟩ c

private theorem sLocalOrderBound_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    sLocalIdelicOrderBound (unitaryₛ(χ) s) =
      min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (unitaryₛ(χ) z)) s) := by
  let ρ := fun z ↦ sLocalRhoFactor (unitaryₛ(χ) z)
  simp only [sLocalIdelicOrderBound, normTwist_normTwist]
  change min 0 (meromorphicOrderAt (fun z ↦ ρ (z + s)) 0) = min 0 (meromorphicOrderAt ρ s)
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, zero_add]

private theorem sLocalZ_centered (f : ℬₛ) (c : Xₛ) :
    let Z := fun z ↦ sLocalIdelicZFunction f (normChartₛ c z)
    MeromorphicAt Z 0 ∧ sLocalIdelicOrderBound c ≤ meromorphicOrderAt Z 0 ∧
      (0 ≤ sLocalIdelicOrderBound c → AnalyticAt ℂ Z 0) := by
  obtain ⟨χ, s, rfl⟩ := exists_sLocalNormTwist c
  let Z := fun z ↦ sLocalIdelicZFunction f (unitaryₛ(χ) z)
  have hnf : MeromorphicNFAt (fun z ↦ Z (z + s)) 0 :=
    meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr (by
      simpa only [zero_add] using sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ s))
  have ho : sLocalIdelicOrderBound (unitaryₛ(χ) s) ≤ meromorphicOrderAt (fun z ↦ Z (z + s)) 0 := by
    rw [sLocalOrderBound_chart, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt, zero_add]
    exact sLocalIdelicZFunction_poles f χ s
  simp only [normTwist_normTwist]
  exact ⟨hnf.meromorphicAt, ho, fun h ↦ hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp (h.trans ho)⟩

/-- Paper: Definition 5.1.1.1(2), p. 223.
The S-local Z-function is continuous on the locus with no allowed pole. -/
theorem sLocalIdelicZFunction_continuous_regular (f : ℬₛ) :
    Continuous (fun c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c} ↦
      sLocalIdelicZFunction f c.val) := by
  refine continuous_iff_continuousAt.mpr fun c ↦ ?_
  exact (continuousAt_of_normTwist _ _ (sIdeleQuotient_hasNormTwistCharts F S) c.val
    ((sLocalZ_centered f c.val).2.2 c.property).continuousAt).comp continuous_subtype_val.continuousAt

local notation "sLocalZValues" => fun f : ℬₛ ↦
  (⟨fun c ↦ sLocalIdelicZFunction f c.val, sLocalIdelicZFunction_continuous_regular f⟩ :
    C({c : Xₛ // 0 ≤ sLocalIdelicOrderBound c}, ℂ))

/-- Paper: Definition 5.1.1.1(2), p. 223.
The S-local Z-function satisfies the prescribed S-local pole bounds. -/
theorem sLocalIdelicZFunction_mem (f : ℬₛ) :
    sLocalZValues f ∈ sLocalMeromorphic := ⟨sLocalIdelicZFunction f, fun _ ↦ rfl, sLocalZ_centered f⟩

/-- Paper: Definition 5.1.1.1(2), p. 223.
The regular values of S-local Z-functions depend complex linearly on the test function. -/
theorem sLocalIdelicZFunction_isLinear :
    IsLinearMap ℂ (sLocalZValues : ℬₛ → _) := by
  classical
  let u : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  have : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hpos (g : Jₛ) : 0 < ((mₛ g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hne (g : Jₛ) : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hpos g).ne'
  have hm : ∃ x, mₛ x ≠ 1 := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨σ t, (hσ t).trans_ne ht⟩
  -- Every quasi-character lies on a norm-twist chart of a unitary character.
  have hdecomp (c : Xₛ) : ∃ (χ : PontryaginDual Jₛ) (s : ℂ), normChartₛ (u.comp χ) s = c := by
    let s := quasiCharacterAbscissa (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S) hm c
    let d := normChartₛ c (-(s : ℂ))
    have hd (g : Jₛ) : ‖d g‖ = 1 := by
      change ‖c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ))‖ = 1
      rw [norm_mul, norm_quasiCharacter_eq_rpow_abscissa (G := Jₛ) mₛ
        (isProperMap_sIdeleQuotientNorm F S) hm,
        Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
      change ((mₛ g : ℝ≥0) : ℝ) ^ s * ((mₛ g : ℝ≥0) : ℝ) ^ (-s) = 1
      rw [← Real.rpow_add (hpos g), add_neg_cancel, Real.rpow_zero]
    let χ : PontryaginDual Jₛ :=
      { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
        map_one' := Circle.ext (map_one d)
        map_mul' := fun g h ↦ Circle.ext (map_mul d g h)
        continuous_toFun := d.continuous.subtype_mk _ }
    refine ⟨χ, s, ?_⟩
    ext1 g
    change (c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (-(s : ℂ))) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (s : ℂ) =
      c g
    rw [mul_assoc, ← Complex.cpow_add _ _ (hne g), neg_add_cancel, Complex.cpow_zero, mul_one]
  -- The norm-twist chart centred at a point of a chart is a translate of it.
  have hchart (c : Xₛ) (w z : ℂ) : normChartₛ (normChartₛ c w) z = normChartₛ c (w + z) := by
    ext1 g
    change (c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ w) * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ z =
      c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (w + z)
    rw [Complex.cpow_add _ _ (hne g), mul_assoc]
  -- Linear relations between zeta integrals on the positive half-plane persist at regular points.
  have key (f₁ f₂ f₃ : ℬₛ) (a b : ℂ)
      (hI : ∀ (χ : PontryaginDual Jₛ) (s : ℂ), 0 < s.re →
        sLocalIdelicZetaIntegral f₃ (normChartₛ (u.comp χ) s) =
          a * sLocalIdelicZetaIntegral f₁ (normChartₛ (u.comp χ) s) +
            b * sLocalIdelicZetaIntegral f₂ (normChartₛ (u.comp χ) s))
      (c : Xₛ) (hc : 0 ≤ sLocalIdelicOrderBound c) :
      sLocalIdelicZFunction f₃ c =
        a * sLocalIdelicZFunction f₁ c + b * sLocalIdelicZFunction f₂ c := by
    obtain ⟨χ, s₀, rfl⟩ := hdecomp c
    have hρ : 0 ≤ min 0 (meromorphicOrderAt
        (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) z)) s₀) := by
      have h := hc
      simp only [sLocalIdelicOrderBound, hchart] at h
      have e : meromorphicOrderAt
          (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) (s₀ + z))) 0 =
          meromorphicOrderAt
            (fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) z)) s₀ := by
        have := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ)) (c := s₀)
          (f := fun z ↦ sLocalRhoFactor (F := F) (S := S) (normChartₛ (u.comp χ) z))
        simpa only [Function.comp_def, add_comm, zero_add, add_zero] using this
      rwa [e] at h
    have hA (f : ℬₛ) :
        AnalyticAt ℂ (fun w ↦ sLocalIdelicZFunction f (normChartₛ (u.comp χ) w)) s₀ :=
      (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ s₀)
        ).meromorphicOrderAt_nonneg_iff_analyticAt.mp
          (hρ.trans (sLocalIdelicZFunction_poles f χ s₀))
    let D : ℂ → ℂ := fun w ↦ sLocalIdelicZFunction f₃ (normChartₛ (u.comp χ) w) -
      (a * sLocalIdelicZFunction f₁ (normChartₛ (u.comp χ) w) +
        b * sLocalIdelicZFunction f₂ (normChartₛ (u.comp χ) w))
    have hM (f : ℬₛ) (w : ℂ) :
        MeromorphicAt (fun w ↦ sLocalIdelicZFunction f (normChartₛ (u.comp χ) w)) w :=
      (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ w)).meromorphicAt
    have hDM : MeromorphicOn D Set.univ := fun w _ ↦
      (hM f₃ w).sub ((analyticAt_const.meromorphicAt.mul (hM f₁ w)).add
        (analyticAt_const.meromorphicAt.mul (hM f₂ w)))
    have hDA : AnalyticAt ℂ D s₀ :=
      (hA f₃).sub ((analyticAt_const.mul (hA f₁)).add (analyticAt_const.mul (hA f₂)))
    have hEq (w : ℂ) (hw : 0 < w.re) : D w = 0 := by
      have hp : normChartₛ (u.comp χ) w ∈ {c : Xₛ | ∃ (χ : PontryaginDual Jₛ) (s : ℂ),
          s ∈ Complex.re ⁻¹' Set.Ioi (0 : ℝ) ∧ c = normChartₛ (u.comp χ) s} :=
        ⟨χ, w, hw, rfl⟩
      simp only [D, sLocalIdelicZFunction_eq_integral _ hp, hI χ w hw, sub_self]
    have hnear : ∀ᶠ z in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have htop : meromorphicOrderAt D 1 = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr ((hnear.mono hEq).filter_mono nhdsWithin_le_nhds)
    have ho := hDM.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ (1 : ℂ)) (Set.mem_univ s₀) htop
    have hloc : D =ᶠ[𝓝[≠] s₀] fun _ ↦ 0 := meromorphicOrderAt_eq_top_iff.mp ho
    have hD₀ : D s₀ = 0 :=
      tendsto_nhds_unique (hDA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' hloc.symm)
    exact sub_eq_zero.mp hD₀
  refine ⟨fun f g ↦ ?_, fun a f ↦ ?_⟩
  · ext c
    change sLocalIdelicZFunction (f + g) c.val =
      sLocalIdelicZFunction f c.val + sLocalIdelicZFunction g c.val
    have h := key f g (f + g) 1 1 (fun χ s hs ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        add_mul (f (Multiplicative.ofAdd x.val)) (g (Multiplicative.ofAdd x.val))
          (normChartₛ (u.comp χ) s (QuotientGroup.mk x)))).trans
        (integral_add (sLocalIdelicZetaIntegral_integrable f _ ⟨χ, s, hs, rfl⟩)
          (sLocalIdelicZetaIntegral_integrable g _ ⟨χ, s, hs, rfl⟩))).trans
        (congrArg₂ (· + ·) (one_mul _).symm (one_mul _).symm)) c.val c.property
    exact h.trans (congrArg₂ (· + ·) (one_mul _) (one_mul _))
  · ext c
    change sLocalIdelicZFunction (a • f) c.val = a * sLocalIdelicZFunction f c.val
    have h := key f f (a • f) a 0 (fun χ s _ ↦
      ((integral_congr_ae (Filter.Eventually.of_forall fun x ↦
        mul_assoc a (f (Multiplicative.ofAdd x.val))
          (normChartₛ (u.comp χ) s (QuotientGroup.mk x)))).trans
        (integral_const_mul a _)).trans
        ((add_zero _).symm.trans (congrArg (_ + ·) (zero_mul _).symm))) c.val c.property
    exact h.trans ((congrArg (_ + ·) (zero_mul _)).trans (add_zero _))

/-- Paper: Definition 5.1.1.1(2), p. 223.
The S-local idelic Mellin transform sends a test function to its continued Z-function.
Deviation: The target uses the bounded-pole model of §5.1.3. -/
def sLocalIdelicMellin : ℬₛ →ₗ[ℂ] ↥sLocalMeromorphic :=
  LinearMap.codRestrict sLocalMeromorphic
    (IsLinearMap.mk' sLocalZValues sLocalIdelicZFunction_isLinear) sLocalIdelicZFunction_mem

/-- Paper: Definition 5.1.1.1(2), p. 223.
At a regular character the S-local transform evaluates to the continued S-local zeta integral. -/
theorem sLocalIdelicMellin_apply (f : ℬₛ) (c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c}) :
    (sLocalIdelicMellin (F := F) (S := S) f).val c = sLocalIdelicZFunction f c.val := rfl

variable (F) in
/-- Paper: Definition 5.1.1.1(3), p. 223.
The global theta operator is the complex-linear map of §2.2.3. -/
def adelicThetaLinearMap : ℬ𝔽 →ₗ[ℂ] C(C𝔽, ℂ) :=
  IsLinearMap.mk' (adelicTheta (F := F)) (adelicTheta_isLinear (F := F))

/-- Paper: Definition 5.1.1.1(3), p. 223.
Evaluating the linear theta map returns the adelic theta function. -/
theorem adelicThetaLinearMap_apply (f : ℬ𝔽) :
    adelicThetaLinearMap F f = adelicTheta f := rfl

local notation "theta𝔽" => adelicThetaLinearMap F
local notation "thetaₛ" => sLocalAdelicTheta F S

variable (F) in
/-- Paper: Definition 5.1.1.1(3), p. 223.
The space of global adelic theta functions is the quotient by the global theta kernel,
with the quotient topology. -/
abbrev GlobalAdelicThetaSpace := ℬ𝔽 ⧸ LinearMap.ker theta𝔽

/-- Paper: Definition 5.1.1.1(3), p. 223.
Two test functions give the same global quotient class exactly when their theta functions agree. -/
theorem globalAdelicThetaSpace_mk_eq_iff (f g : ℬ𝔽) :
    (Submodule.Quotient.mk f : GlobalAdelicThetaSpace F) = Submodule.Quotient.mk g ↔
      adelicTheta f = adelicTheta g := by
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  rfl

variable (F S) in
/-- Paper: Definition 5.1.1.1(3), p. 223.
The space of S-local adelic theta functions is the quotient by the S-local theta kernel,
with the quotient topology.
Deviation: We take the kernel on S-ideles. The descended theta map has the same
kernel because the map from S-ideles to S-idele classes is surjective.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev SLocalAdelicThetaSpace := ℬₛ ⧸ LinearMap.ker thetaₛ

/-- Paper: Definition 5.1.1.1(3), p. 223.
Two test functions give the same S-local quotient class exactly when their class theta
functions agree. -/
theorem sLocalAdelicThetaSpace_mk_eq_iff (f g : ℬₛ) :
    (Submodule.Quotient.mk f : SLocalAdelicThetaSpace F S) = Submodule.Quotient.mk g ↔
      sLocalAdelicThetaOnClasses F S f = sLocalAdelicThetaOnClasses F S g := by
  rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]
  constructor
  · intro h
    refine ContinuousMap.ext fun x ↦ QuotientGroup.induction_on x fun g' ↦ ?_
    exact (sLocalAdelicThetaOnClasses_mk F S f g').trans
      ((DFunLike.congr_fun h g').trans (sLocalAdelicThetaOnClasses_mk F S g g').symm)
  · intro h
    refine ContinuousMap.ext fun x ↦ ?_
    exact (sLocalAdelicThetaOnClasses_mk F S f x).symm.trans
      ((DFunLike.congr_fun h _).trans (sLocalAdelicThetaOnClasses_mk F S g x))

/-- Two normalized meromorphic functions agreeing on a right half-plane agree everywhere. -/
private theorem eq_of_agree_rightHalf {U V : ℂ → ℂ} (hU : MeromorphicNFOn U Set.univ)
    (hV : MeromorphicNFOn V Set.univ) (a : ℝ) (h : ∀ z : ℂ, a < z.re → U z = V z) : U = V := by
  let b : ℂ := (a + 1 : ℝ)
  have hb : ∀ᶠ z : ℂ in 𝓝 b, a < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp [b])
  have ho : meromorphicOrderAt (U - V) b = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr ((hb.filter_mono nhdsWithin_le_nhds).mono
      fun z hz ↦ sub_eq_zero.mpr (h z hz))
  funext z
  have hz := (hU.meromorphicOn.sub hV.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ b) (Set.mem_univ z) ho
  exact (((hU (Set.mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hV (Set.mem_univ z))).mp (Filter.eventuallyEq_iff_sub.mpr
      (meromorphicOrderAt_eq_top_iff.mp hz))).eq_of_nhds

local notation "globalRightHalf" => relativeRightHalfPlane m𝔽 (isProperMap_ideleClassNorm F)
  (ideleClassNorm_ne_one (F := F)) 1

private theorem globalTwist_mem_rightHalf (χ : PontryaginDual C𝔽) {s : ℂ} (hs : 1 < s.re) :
    ideleClassNormTwist χ s ∈ globalRightHalf := by
  change 1 < quasiCharacterAbscissa _ _ _ _
  rwa [quasiCharacterAbscissa_ideleClassNormTwist]

private theorem globalZ_eq_zero_of_theta_eq_zero (f : ℬ𝔽) (hf : adelicTheta f = 0) (c : X𝔽) :
    globalIdelicZFunction f c = 0 := by
  obtain ⟨χ, s, rfl⟩ := exists_ideleClassNormTwist c
  refine congrFun (eq_of_agree_rightHalf (globalIdelicZFunction_meromorphic f χ)
    (V := 0) (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 1 fun z hz ↦ ?_) s
  have hr := globalTwist_mem_rightHalf χ hz
  rw [globalIdelicZFunction_eq_integral f hr, ← globalThetaMellinIntegral_eq_idelic f hr]
  simp [globalThetaMellinIntegral, hf]

/-- Paper: Definition 5.1.1.1(3), p. 223.
The global zeta continuation vanishes for every test function with zero theta function.
Deviation: This is the compatibility field for the quotient lift in (5.1.1.4). -/
theorem globalIdelicMellin_vanishes_on_theta_kernel :
    LinearMap.ker theta𝔽 ≤ LinearMap.ker (globalIdelicMellin (F := F)) := by
  intro f hf
  change adelicTheta f = 0 at hf
  apply Subtype.ext
  apply ContinuousMap.ext
  intro c
  exact (globalIdelicMellin_apply f c).trans (globalZ_eq_zero_of_theta_eq_zero f hf c.val)

/-- Paper: Definition 5.1.1.1(3), p. 223.
The S-local zeta continuation vanishes for every test function with zero S-local theta function.
Deviation: This is the compatibility field for the quotient lift in (5.1.1.4). -/
theorem sLocalIdelicMellin_vanishes_on_theta_kernel :
    LinearMap.ker thetaₛ ≤ LinearMap.ker (sLocalIdelicMellin (F := F) (S := S)) := by
  intro f hf
  have hθ (g : Jₛ) : sLocalAdelicThetaOnClasses F S f g = 0 := by
    induction g using QuotientGroup.induction_on with | H x => ?_
    exact (sLocalAdelicThetaOnClasses_mk F S f x).trans (DFunLike.congr_fun (LinearMap.mem_ker.mp hf) x)
  have hZ := sLocalIdelicZetaIntegral_exists_continuation f
  have hz : sLocalIdelicZFunction f = 0 :=
    hZ.unique hZ.exists.choose_spec ⟨fun _ _ _ ↦ analyticAt_const.meromorphicNFAt, fun c hc ↦ by
      rw [← sLocalThetaMellinIntegral_eq_zeta f hc]
      simp [sLocalThetaMellinIntegral, hθ]⟩
  refine LinearMap.mem_ker.mpr (Subtype.ext (ContinuousMap.ext fun c ↦ ?_))
  exact congrFun hz c.val

/-- Paper: Definition 5.1.1.1(3), p. 223.
The Mellin transform of global theta functions is the map induced on the theta quotient. -/
def globalThetaMellin : GlobalAdelicThetaSpace F →ₗ[ℂ] ↥globalMeromorphic :=
  (LinearMap.ker theta𝔽).liftQ (globalIdelicMellin (F := F))
    (globalIdelicMellin_vanishes_on_theta_kernel (F := F))

/-- Paper: Definition 5.1.1.1(3), p. 223.
The global quotient transform recovers the test-function transform on every representative. -/
theorem globalThetaMellin_mk (f : ℬ𝔽) :
    globalThetaMellin (F := F) (Submodule.Quotient.mk f) =
      globalIdelicMellin (F := F) f := rfl

/-- Paper: Definition 5.1.1.1(3), p. 223.
The Mellin transform of S-local theta functions is the map induced on the theta quotient. -/
def sLocalThetaMellin : SLocalAdelicThetaSpace F S →ₗ[ℂ] ↥sLocalMeromorphic :=
  (LinearMap.ker thetaₛ).liftQ (sLocalIdelicMellin (F := F) (S := S))
    (sLocalIdelicMellin_vanishes_on_theta_kernel (F := F) (S := S))

/-- Paper: Definition 5.1.1.1(3), p. 223.
The S-local quotient transform recovers the test-function transform on every representative. -/
theorem sLocalThetaMellin_mk (f : ℬₛ) :
    sLocalThetaMellin (F := F) (S := S) (Submodule.Quotient.mk f) =
      sLocalIdelicMellin (F := F) (S := S) f := rfl

variable (F) in
/-- Paper: Definition 5.1.1.1(4), p. 223.
The global idelic Z-space is the linear range of the Mellin transform of global theta functions. -/
def GlobalIdelicZSpace := ↥(globalThetaMellin (F := F)).range

/-- Paper: Definition 5.1.1.1(4), p. 223.
Addition and negation on the global Z-space are inherited from the linear range. -/
instance : AddCommGroup (GlobalIdelicZSpace F) :=
  inferInstanceAs (AddCommGroup ↥(globalThetaMellin (F := F)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The global Z-space inherits complex scalar multiplication from the linear range. -/
instance : Module ℂ (GlobalIdelicZSpace F) :=
  inferInstanceAs (Module ℂ ↥(globalThetaMellin (F := F)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The global Z-space carries the topology transported from the theta quotient by the transform. -/
instance : TopologicalSpace (GlobalIdelicZSpace F) :=
  TopologicalSpace.coinduced (globalThetaMellin (F := F)).rangeRestrict inferInstance

/-- Paper: Definition 5.1.1.1(4), p. 223.
The Mellin transform as a linear map from the global theta space onto the global Z-space.
Statements about the topology of the Z-space must go through this map: `GlobalIdelicZSpace F`
unfolds to a range subtype, and a map whose codomain is written as that subtype is given the
subspace topology of compact convergence, not the transported topology of the paper. -/
def globalThetaToZ : GlobalAdelicThetaSpace F →ₗ[ℂ] GlobalIdelicZSpace F :=
  (globalThetaMellin (F := F)).rangeRestrict

/-- Paper: Definition 5.1.1.1(4), p. 223.
The map from the global theta space onto its Z-space is a quotient map. -/
theorem globalThetaToZ_isQuotientMap : IsQuotientMap (globalThetaToZ (F := F)) :=
  { eq_coinduced := rfl, surjective := LinearMap.surjective_rangeRestrict _ }

variable (F S) in
/-- Paper: Definition 5.1.1.1(4), p. 223.
The S-local idelic Z-space is the linear range of the Mellin transform of S-local theta functions. -/
def SLocalIdelicZSpace := ↥(sLocalThetaMellin (F := F) (S := S)).range

/-- Paper: Definition 5.1.1.1(4), p. 223.
Addition and negation on the S-local Z-space are inherited from the linear range. -/
instance : AddCommGroup (SLocalIdelicZSpace F S) :=
  inferInstanceAs (AddCommGroup ↥(sLocalThetaMellin (F := F) (S := S)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The S-local Z-space inherits complex scalar multiplication from the linear range. -/
instance : Module ℂ (SLocalIdelicZSpace F S) :=
  inferInstanceAs (Module ℂ ↥(sLocalThetaMellin (F := F) (S := S)).range)

/-- Paper: Definition 5.1.1.1(4), p. 223.
The S-local Z-space carries the topology transported from the theta quotient by the transform. -/
instance : TopologicalSpace (SLocalIdelicZSpace F S) :=
  TopologicalSpace.coinduced (sLocalThetaMellin (F := F) (S := S)).rangeRestrict inferInstance

/-- Paper: Definition 5.1.1.1(4), p. 223.
The Mellin transform as a linear map from the S-local theta space onto the S-local Z-space.
As for `globalThetaToZ`, statements about the topology of the Z-space must go through this map. -/
def sLocalThetaToZ : SLocalAdelicThetaSpace F S →ₗ[ℂ] SLocalIdelicZSpace F S :=
  (sLocalThetaMellin (F := F) (S := S)).rangeRestrict

/-- Paper: Definition 5.1.1.1(4), p. 223.
The map from the S-local theta space onto its Z-space is a quotient map. -/
theorem sLocalThetaToZ_isQuotientMap :
    IsQuotientMap (sLocalThetaToZ (F := F) (S := S)) :=
  { eq_coinduced := rfl, surjective := LinearMap.surjective_rangeRestrict _ }

/-- Paper: Remark 5.1.1.2, p. 223.
The global theta quotient is locally convex. -/
theorem globalAdelicThetaSpace_polynormable : PolynormableSpace ℂ (GlobalAdelicThetaSpace F) :=
  let : PolynormableSpace ℂ ℬ𝔽 := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  polynormableSpace_quotient _

/-- Paper: Remark 5.1.1.2, p. 223.
The S-local theta quotient is locally convex. -/
theorem sLocalAdelicThetaSpace_polynormable : PolynormableSpace ℂ (SLocalAdelicThetaSpace F S) :=
  let : PolynormableSpace ℂ ℬₛ := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  polynormableSpace_quotient _

/-- Paper: Remark 5.1.1.2, p. 223.
The global theta quotient is Hausdorff if the global theta kernel is closed. -/
theorem globalAdelicThetaSpace_t2_of_isClosed
    (h : IsClosed (LinearMap.ker theta𝔽 : Set ℬ𝔽)) :
    T2Space (GlobalAdelicThetaSpace F) := by
  have : IsClosed (LinearMap.ker theta𝔽 : Set ℬ𝔽) := h
  infer_instance

/-- Paper: Remark 5.1.1.2, p. 223.
The S-local theta quotient is Hausdorff if the S-local theta kernel is closed. -/
theorem sLocalAdelicThetaSpace_t2_of_isClosed
    (h : IsClosed (LinearMap.ker thetaₛ : Set ℬₛ)) :
    T2Space (SLocalAdelicThetaSpace F S) := by
  have : IsClosed (LinearMap.ker thetaₛ : Set ℬₛ) := h
  infer_instance

section FourierUniqueness

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Testing a weighted continuous function against all characters recovers the function. -/
private theorem eq_zero_of_weighted_integrals (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (θ : C(G, ℂ)) (w : QuasiCharacter G) (hi : Integrable (fun x ↦ θ x * w x) μ)
    (hz : ∀ χ : PontryaginDual G, ∫ x, θ x * w x * (χ x : ℂ) ∂μ = 0) : θ = 0 := by
  let ev (x : G) : PontryaginDual G →* Circle :=
    { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  have hsep : Injective ev := fun _ _ h ↦
    pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun h))
  have hae := ae_eq_zero_of_integral_mul_circle_eq_zero ev (fun χ ↦ χ.continuous) hsep hi hz
  have heq := Measure.eq_of_ae_eq hae (θ.continuous.mul w.continuous) continuous_const
  exact ContinuousMap.ext fun g ↦ (mul_eq_zero.mp (congrFun heq g)).resolve_right
    ((Group.isUnit g).map w).ne_zero

end FourierUniqueness

private theorem globalOrderBound_rightHalf (χ : PontryaginDual C𝔽) {s : ℂ} (hs : 1 < s.re) :
    0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ s) := by
  have h0 : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext1 g
    change 1 * _ ^ (0 : ℂ) = (1 : ℂ)
    simp
  rw [globalIdelicOrderBound, ite_eq_right]
  rintro (h | h)
  · rw [← h0] at h
    have he := congrArg (quasiCharacterAbscissa m𝔽 (isProperMap_ideleClassNorm F)
      ideleClassNorm_ne_one) h
    rw [quasiCharacterAbscissa_ideleClassNormTwist, quasiCharacterAbscissa_ideleClassNormTwist,
      Complex.zero_re] at he
    linarith
  · have he := congrArg (quasiCharacterAbscissa m𝔽 (isProperMap_ideleClassNorm F)
      ideleClassNorm_ne_one) h
    rw [quasiCharacterAbscissa_ideleClassNormTwist, quasiCharacterAbscissa_ideleClassNormTwist,
      Complex.one_re] at he
    exact hs.ne' he

/-- Paper: Theorem 5.1.1.3, p. 223.
The Mellin transform is injective on the global theta quotient. -/
theorem globalThetaMellin_injective : Injective (globalThetaMellin (F := F)) := by
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let μ := ideleClassTamagawaMeasure F
  have : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have : μ.Regular := (ideleClassTamagawaMeasure_isWeil F).2.1
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun q ↦ ?_)
  refine Submodule.Quotient.induction_on _ q fun f hf ↦ (Submodule.Quotient.mk_eq_zero _).mpr ?_
  apply LinearMap.mem_ker.mpr
  let w := ideleClassNormTwist (1 : PontryaginDual C𝔽) 2
  have hs : 1 < (2 : ℂ).re := by norm_num
  refine eq_zero_of_weighted_integrals μ (adelicTheta f) w
    (globalThetaMellinIntegral_integrable f w (globalTwist_mem_rightHalf _ hs)) fun χ ↦ ?_
  let c := ideleClassNormTwist χ 2
  have heval : globalIdelicZFunction f c = 0 :=
    congrArg (fun Z : ↥globalMeromorphic ↦ Z.val ⟨c, globalOrderBound_rightHalf χ hs⟩) hf
  have hr := globalTwist_mem_rightHalf χ hs
  rw [globalIdelicZFunction_eq_integral f hr, ← globalThetaMellinIntegral_eq_idelic f hr] at heval
  refine (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)).trans heval
  change adelicTheta f g * (1 * _ ^ (2 : ℂ)) * (χ g : ℂ) =
    adelicTheta f g * ((χ g : ℂ) * _ ^ (2 : ℂ))
  rw [one_mul, mul_right_comm, mul_assoc]

private theorem sLocalOrderBound_positive (χ : PontryaginDual Jₛ) {s : ℂ} (hs : 0 < s.re) :
    0 ≤ sLocalIdelicOrderBound (unitaryₛ(χ) s) := by
  rw [sLocalOrderBound_chart, le_min_iff]
  have h := sLocalRhoFactor_iteratedDeriv_analyticOn χ 0 s hs
  rw [iteratedDeriv_zero] at h
  exact ⟨le_rfl, h.meromorphicOrderAt_nonneg⟩

/-- Paper: Theorem 5.1.1.3, p. 223.
The Mellin transform is injective on the S-local theta quotient. -/
theorem sLocalThetaMellin_injective : Injective (sLocalThetaMellin (F := F) (S := S)) := by
  let : MeasurableSpace Jₛ := borel _
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let μ := sLocalQuotientTamagawaMeasure F S
  have : μ.IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  have : μ.Regular := (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).2.1
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun q ↦ ?_)
  refine Submodule.Quotient.induction_on _ q fun f hf ↦ (Submodule.Quotient.mk_eq_zero _).mpr ?_
  let w := unitaryₛ((1 : PontryaginDual Jₛ)) 1
  have hθ : sLocalAdelicThetaOnClasses F S f = 0 := by
    refine eq_zero_of_weighted_integrals μ _ w
      (sLocalThetaMellinIntegral_integrable f w ⟨1, 1, by norm_num, rfl⟩) fun χ ↦ ?_
    let c := unitaryₛ(χ) 1
    have heval : sLocalIdelicZFunction f c = 0 :=
      congrArg (fun Z : ↥sLocalMeromorphic ↦ Z.val ⟨c, sLocalOrderBound_positive χ (by norm_num)⟩) hf
    have hr : ∃ (ψ : PontryaginDual Jₛ) (z : ℂ), 0 < z.re ∧ c = unitaryₛ(ψ) z :=
      ⟨χ, 1, by norm_num, rfl⟩
    rw [sLocalIdelicZFunction_eq_integral f hr, ← sLocalThetaMellinIntegral_eq_zeta f hr] at heval
    refine (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)).trans heval
    change sLocalAdelicThetaOnClasses F S f g * (1 * _ ^ (1 : ℂ)) * (χ g : ℂ) =
      sLocalAdelicThetaOnClasses F S f g * ((χ g : ℂ) * _ ^ (1 : ℂ))
    rw [one_mul, mul_right_comm, mul_assoc]
  exact LinearMap.mem_ker.mpr (ContinuousMap.ext fun g ↦
    (sLocalAdelicThetaOnClasses_mk F S f g).symm.trans (DFunLike.congr_fun hθ _))

open scoped ENNReal in
/-- Point evaluation is continuous in the Schwartz–Bruhat topology since its
norm is bounded on each stage by the zeroth Schwartz seminorm. -/
private theorem schwartzBruhat_eval_continuous {G : Type*} [CommGroup G] [TopologicalSpace G]
    (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (‖f y‖₊ : ℝ≥0∞).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖f z‖₊ : ℝ≥0∞)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

/-- At a fixed idele class, global theta is continuous in the test function. It is the
pointwise limit of the finite partial sums of point evaluations, and the global
Schwartz–Bruhat space is barrelled, so the Banach–Steinhaus theorem applies. -/
private theorem adelicTheta_eval_continuous (c : C𝔽) :
    Continuous (fun f : ℬ𝔽 ↦ adelicTheta f c) := by
  induction c using QuotientGroup.induction_on with | H g => ?_
  let : BarrelledSpace ℂ ℬ𝔽 := (adeleSchwartz_montel (F := F)).2.1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let pt (ξ : Fˣ) : Multiplicative 𝔸[F] :=
    Multiplicative.ofAdd (algebraMap F 𝔸[F] (ξ : F) * g.val)
  let ev (ξ : Fˣ) : ℬ𝔽 →L[ℂ] ℂ :=
    ⟨(LinearMap.proj (pt ξ)).comp (schwartzBruhatSubmodule _).subtype,
      schwartzBruhat_eval_continuous (pt ξ)⟩
  let L (s : Finset Fˣ) : ℬ𝔽 →L[ℂ] ℂ := ∑ ξ ∈ s, ev ξ
  have hL (s : Finset Fˣ) (f : ℬ𝔽) : L s f = ∑ ξ ∈ s, f (pt ξ) := by
    simp only [L, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rfl
  have hsum (f : ℬ𝔽) : HasSum (fun ξ ↦ f (pt ξ)) (adelicTheta f (QuotientGroup.mk g)) := by
    rw [adelicTheta_mk]
    refine Summable.hasSum ?_
    have hs := ((adelicAverage_summableUniformlyOn f {(g, 0)} isCompact_singleton).summable
      rfl).of_norm
    simpa only [add_zero, mul_comm g.val] using hs
  have hT : Filter.Tendsto (fun s f ↦ L s f) Filter.atTop
      (𝓝 fun f ↦ adelicTheta f (QuotientGroup.mk g)) :=
    tendsto_pi_nhds.mpr fun f ↦ by
      simp only [hL]
      exact hsum f
  exact (continuousLinearMapOfTendsto L hT).continuous

/-- Paper: Theorem 5.1.1.3(1), p. 224.
The global theta kernel is a closed subspace of the global Schwartz–Bruhat space. -/
theorem adelicTheta_ker_isClosed : IsClosed (LinearMap.ker theta𝔽 : Set ℬ𝔽) := by
  have hker : (⋂ c : C𝔽, (fun f : ℬ𝔽 ↦ adelicTheta f c) ⁻¹' {0}) =
      (LinearMap.ker theta𝔽 : Set ℬ𝔽) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun c ↦ Set.mem_singleton_iff).trans ?_)
    rw [SetLike.mem_coe, LinearMap.mem_ker, adelicThetaLinearMap_apply]
    exact ⟨fun h ↦ ContinuousMap.ext h, fun h c ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) h⟩
  exact (congrArg (IsClosed (X := ℬ𝔽)) hker).mp
    (isClosed_iInter fun c ↦ isClosed_singleton.preimage (adelicTheta_eval_continuous c))

/-- On a barrelled Schwartz–Bruhat space, a functional that is the sum of the values of
the test function at countably many points is continuous, by the Banach–Steinhaus theorem
applied to the finite partial sums of point evaluations. -/
private theorem schwartzBruhat_continuous_of_hasSum {G ι : Type*} [CommGroup G]
    [TopologicalSpace G] [Countable ι] [BarrelledSpace ℂ (SchwartzBruhat G)]
    (pt : ι → G) (φ : SchwartzBruhat G → ℂ)
    (h : ∀ f : SchwartzBruhat G, HasSum (fun i ↦ f (pt i)) (φ f)) :
    Continuous φ := by
  let ev (i : ι) : SchwartzBruhat G →L[ℂ] ℂ :=
    ⟨(LinearMap.proj (pt i)).comp (schwartzBruhatSubmodule _).subtype,
      schwartzBruhat_eval_continuous (pt i)⟩
  let L (s : Finset ι) : SchwartzBruhat G →L[ℂ] ℂ := ∑ i ∈ s, ev i
  have hL (s : Finset ι) (f : SchwartzBruhat G) : L s f = ∑ i ∈ s, f (pt i) := by
    simp only [L, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rfl
  have hT : Filter.Tendsto (fun s f ↦ L s f) Filter.atTop (𝓝 φ) :=
    tendsto_pi_nhds.mpr fun f ↦ by
      simp only [hL]
      exact h f
  exact (continuousLinearMapOfTendsto L hT).continuous

/-- Paper: Theorem 5.1.1.3(1), p. 224.
The S-local theta kernel is a closed subspace of the S-local Schwartz–Bruhat space. -/
theorem sLocalAdelicTheta_ker_isClosed : IsClosed (LinearMap.ker thetaₛ : Set ℬₛ) := by
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ :=
    Units.val_injective.countable
  have hcont (g : (SAdeleRing F S)ˣ) : Continuous (fun f : ℬₛ ↦ thetaₛ f g) :=
    schwartzBruhat_continuous_of_hasSum _ _ fun f ↦
      (sLocalAdelicTheta_hasSumUniformlyOn F S f {g} isCompact_singleton).hasSum rfl
  have hker : (⋂ g : (SAdeleRing F S)ˣ, (fun f : ℬₛ ↦ thetaₛ f g) ⁻¹' {0}) =
      (LinearMap.ker thetaₛ : Set ℬₛ) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun g ↦ Set.mem_singleton_iff).trans
        (Iff.trans ?_ (SetLike.mem_coe.trans LinearMap.mem_ker).symm))
    exact ⟨fun h ↦ ContinuousMap.ext h,
      fun h g ↦ congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ g) h⟩
  exact (congrArg (IsClosed (X := ℬₛ)) hker).mp
    (isClosed_iInter fun g ↦ isClosed_singleton.preimage (hcont g))

/-- On a barrelled space, the integral over a compact space against a finite measure of
a family of continuous linear functionals is continuous if each test vector gives a
continuous function of the parameter. The pointwise supremum of the absolute values of
the functionals is then a continuous seminorm, and the integral is bounded by the
total mass times this seminorm. -/
private theorem continuous_integral_of_continuous_eval {E H : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℂ E]
    [BarrelledSpace ℂ E] [TopologicalSpace H] [CompactSpace H] {m : MeasurableSpace H}
    (μ : Measure H) [IsFiniteMeasure μ]
    (Φ : E → H → ℂ) (hlin : ∀ h, IsLinearMap ℂ fun f ↦ Φ f h)
    (hE : ∀ h, Continuous fun f ↦ Φ f h) (hH : ∀ f, Continuous (Φ f))
    (hint : ∀ f, Integrable (Φ f) μ) : Continuous fun f ↦ ∫ h, Φ f h ∂μ := by
  let p (h : H) : Seminorm ℂ E := (normSeminorm ℂ ℂ).comp (IsLinearMap.mk' _ (hlin h))
  have hp (h : H) : Continuous (p h) := continuous_norm.comp (hE h)
  have hpt (f : E) : BddAbove (Set.range fun h ↦ p h f) :=
    (isCompact_range (hH f).norm).bddAbove
  have hbdd : BddAbove (Set.range p) := Seminorm.bddAbove_range_iff.mpr hpt
  have hsup : Continuous (⨆ h, p h : Seminorm ℂ E) :=
    (congrArg Continuous (Seminorm.coe_iSup_eq hbdd)).mpr (Seminorm.continuous_iSup p hp hbdd)
  let I : E →ₗ[ℂ] ℂ := IsLinearMap.mk' (fun f ↦ ∫ h, Φ f h ∂μ)
    ⟨fun f f' ↦ (integral_congr_ae (.of_forall fun h ↦ (hlin h).map_add f f')).trans
        (integral_add (hint f) (hint f')),
      fun c f ↦ (integral_congr_ae (.of_forall fun h ↦ (hlin h).map_smul c f)).trans
        (integral_smul c _)⟩
  have hq : Continuous ((μ Set.univ).toNNReal • ⨆ h, p h : Seminorm ℂ E) :=
    hsup.const_smul _
  refine (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp I fun _ ↦
    Seminorm.continuous_of_le hq fun f ↦ ?_
  have hle (h : H) : ‖Φ f h‖ ≤ (⨆ h, p h) f := by
    rw [Seminorm.coe_iSup_eq hbdd, iSup_apply]
    exact le_ciSup (hpt f) h
  exact (norm_integral_le_of_norm_le_const (.of_forall hle)).trans_eq
    (mul_comm _ ((μ Set.univ).toNNReal : ℝ))

local notation "homogeneousTheta𝔽" =>
  fun ω : PontryaginDual (MonoidHom.ker m𝔽) ↦
    IsLinearMap.mk' (homogeneousAdelicTheta (F := F) ω)
      (homogeneousAdelicTheta_isLinear (F := F) ω)

/-- Paper: Theorem 5.1.1.3(2), p. 224.
The kernel of global homogeneous theta at each norm-one character is closed. -/
theorem homogeneousAdelicTheta_ker_isClosed (ω : PontryaginDual (MonoidHom.ker m𝔽)) :
    IsClosed (LinearMap.ker (homogeneousTheta𝔽 ω) : Set ℬ𝔽) := by
  let : BarrelledSpace ℂ ℬ𝔽 := (adeleSchwartz_montel (F := F)).2.1
  let : MeasurableSpace C𝔽 := borel _
  let : CompactSpace (MonoidHom.ker m𝔽) := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hθ := adelicTheta_isLinear (F := F)
  have hlin (c : C𝔽) : IsLinearMap ℂ fun f : ℬ𝔽 ↦ adelicTheta f c :=
    ⟨fun f f' ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) (hθ.map_add f f'),
      fun a f ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ c) (hθ.map_smul a f)⟩
  have hcont (g : C𝔽) : Continuous (fun f : ℬ𝔽 ↦ homogeneousAdelicTheta ω f g) :=
    continuous_integral_of_continuous_eval (normOneIdeleClassTamagawaMeasure F)
      (fun f h ↦ adelicTheta f (h.val * g) * (ω h : ℂ))
      (fun h ↦ ⟨fun f f' ↦ (congrArg (· * (ω h : ℂ)) ((hlin _).map_add f f')).trans
          (add_mul _ _ _),
        fun a f ↦ (congrArg (· * (ω h : ℂ)) ((hlin _).map_smul a f)).trans
          (smul_mul_assoc _ _ _)⟩)
      (fun h ↦ (adelicTheta_eval_continuous (h.val * g)).mul continuous_const)
      (fun f ↦ ((adelicTheta f).continuous.comp
        (continuous_subtype_val.mul continuous_const)).mul
          (continuous_subtype_val.comp ω.continuous))
      (fun f ↦ homogeneousAdelicTheta_integrable ω f g)
  have hker : (⋂ g : C𝔽, (fun f : ℬ𝔽 ↦ homogeneousAdelicTheta ω f g) ⁻¹' {0}) =
      (LinearMap.ker (homogeneousTheta𝔽 ω) : Set ℬ𝔽) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun g ↦ Set.mem_singleton_iff).trans
        (Iff.trans ?_ (SetLike.mem_coe.trans LinearMap.mem_ker).symm))
    exact ⟨fun h ↦ ContinuousMap.ext h, fun h g ↦ congrArg (fun φ : C(C𝔽, ℂ) ↦ φ g) h⟩
  exact (congrArg (IsClosed (X := ℬ𝔽)) hker).mp
    (isClosed_iInter fun g ↦ isClosed_singleton.preimage (hcont g))

/-- Paper: Theorem 5.1.1.3(3), p. 224.
The norm-one S-idele quotient carries the Borel measurable structure used in §3.3. -/
local instance : MeasurableSpace (MonoidHom.ker mₛ) := borel _

/-- Paper: Theorem 5.1.1.3(3), p. 224.
The norm-one quotient Tamagawa measure of §3.3 is Haar. -/
local instance : Measure.IsHaarMeasure (sLocalNormOneQuotientMeasure F S) :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

local notation "homogeneousThetaₛ" =>
  sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S)

/-- Paper: Theorem 5.1.1.3(3), p. 224.
The kernel of S-local homogeneous theta at each norm-one character is closed. -/
theorem sLocalHomogeneousAdelicTheta_ker_isClosed (ω : PontryaginDual (MonoidHom.ker mₛ)) :
    IsClosed (LinearMap.ker (homogeneousThetaₛ ω) : Set ℬₛ) := by
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ :=
    Units.val_injective.countable
  have : CompactSpace (MonoidHom.ker mₛ) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  have hθ (c : Jₛ) : IsLinearMap ℂ (fun f : ℬₛ ↦ sLocalAdelicThetaOnClasses F S f c) ∧
      Continuous (fun f : ℬₛ ↦ sLocalAdelicThetaOnClasses F S f c) := by
    induction c using QuotientGroup.induction_on with | H x => ?_
    simp only [sLocalAdelicThetaOnClasses_mk]
    exact ⟨⟨fun f f' ↦ congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ x) (map_add thetaₛ f f'),
        fun a f ↦ congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ x) (map_smul thetaₛ a f)⟩,
      schwartzBruhat_continuous_of_hasSum _ _ fun f ↦
        (sLocalAdelicTheta_hasSumUniformlyOn F S f {x} isCompact_singleton).hasSum rfl⟩
  have hcont (g : Jₛ) : Continuous (fun f : ℬₛ ↦ homogeneousThetaₛ ω f g) :=
    continuous_integral_of_continuous_eval (sLocalNormOneQuotientMeasure F S)
      (fun f h ↦ sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ))
      (fun h ↦ ⟨fun f f' ↦ (congrArg (· * (ω h : ℂ)) ((hθ _).1.map_add f f')).trans
          (add_mul _ _ _),
        fun a f ↦ (congrArg (· * (ω h : ℂ)) ((hθ _).1.map_smul a f)).trans
          (smul_mul_assoc _ _ _)⟩)
      (fun h ↦ (hθ _).2.mul continuous_const)
      (fun f ↦ ((sLocalAdelicThetaOnClasses F S f).continuous.comp
        (continuous_const.mul continuous_subtype_val)).mul
          (continuous_subtype_val.comp ω.continuous))
      (fun f ↦ sLocalHomogeneousAdelicTheta_integrable F S _ ω f g)
  have hker : (⋂ g : Jₛ, (fun f : ℬₛ ↦ homogeneousThetaₛ ω f g) ⁻¹' {0}) =
      (LinearMap.ker (homogeneousThetaₛ ω) : Set ℬₛ) := by
    refine Set.ext fun f ↦ Set.mem_iInter.trans
      ((forall_congr' fun g ↦ Set.mem_singleton_iff).trans
        (Iff.trans ?_ (SetLike.mem_coe.trans LinearMap.mem_ker).symm))
    exact ⟨fun h ↦ ContinuousMap.ext h, fun h g ↦ congrArg (fun φ : C(Jₛ, ℂ) ↦ φ g) h⟩
  exact (congrArg (IsClosed (X := ℬₛ)) hker).mp
    (isClosed_iInter fun g ↦ isClosed_singleton.preimage (hcont g))

/-- Paper: Lemma 5.1.2.1(1), p. 224.
The kernels of the global zeta and global theta transforms agree. -/
theorem globalIdelicMellin_ker_eq :
    LinearMap.ker (globalIdelicMellin (F := F)) = LinearMap.ker theta𝔽 := by
  refine le_antisymm (fun f hf ↦ ?_) (globalIdelicMellin_vanishes_on_theta_kernel (F := F))
  have hinj : Injective (globalThetaMellin (F := F)) := globalThetaMellin_injective
  have h1 : globalThetaMellin (F := F) (Submodule.Quotient.mk f) = 0 :=
    (globalThetaMellin_mk f).trans (LinearMap.mem_ker.mp hf)
  have h2 : (Submodule.Quotient.mk f : GlobalAdelicThetaSpace F) = 0 :=
    hinj (h1.trans (map_zero (globalThetaMellin (F := F))).symm)
  exact (Submodule.Quotient.mk_eq_zero _).mp h2

section HomogeneousUniqueness

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  (m : G →* ℝ≥0ˣ) (hm : Continuous m)

local notation "unitaryChart(" χ ")" => quasiCharacterNormTwist m hm
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)

private theorem normOneRestriction_unitaryChart (χ : PontryaginDual G) (s : ℂ) (u : m.ker) :
    normOneRestriction m (unitaryChart(χ) s) u = (χ u.val : ℂ) := by
  change (χ u.val : ℂ) * (((m u.val : ℝ≥0) : ℝ) : ℂ) ^ s = _
  rw [u.prop]
  simp

include hm in
/-- A character on the norm-one group and one on the section determine a unitary character. -/
private theorem exists_character_on_split (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m)
    (ω : PontryaginDual m.ker) (η : PontryaginDual ℝ≥0ˣ) :
    ∃ χ : PontryaginDual G, (∀ u : m.ker, χ u.val = ω u) ∧ ∀ t, χ (σ t) = η t := by
  have hrker (g : G) : g / σ (m g) ∈ m.ker := by simp [MonoidHom.mem_ker, hσ (m g)]
  let r : G →ₜ* m.ker :=
    { toFun := fun g ↦ ⟨g / σ (m g), hrker g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by simp [mul_div_mul_comm])
      continuous_toFun := (continuous_id.div' (σ.continuous.comp hm)).subtype_mk hrker }
  refine ⟨(ω.comp r) * (η.comp ⟨m, hm⟩), fun u ↦ ?_, fun t ↦ ?_⟩
  · have hu : r u.val = u := Subtype.ext (by change _ / σ (m u.val) = _; rw [u.prop, map_one, div_one])
    change ω (r u.val) * η (m u.val) = _
    rw [hu, u.prop, map_one, mul_one]
  · have ht : r (σ t) = 1 := Subtype.ext (by change σ t / σ (m (σ t)) = 1; rw [hσ, div_self'])
    change ω (r (σ t)) * η (m (σ t)) = _
    rw [ht, hσ, map_one, one_mul]

/-- Fourier uniqueness on the norm section detects a homogeneous function on the entire group. -/
private theorem homogeneous_eq_zero_of_radial_integrals (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m)
    (ω : PontryaginDual m.ker) (θ : C(G, ℂ))
    (hθ : ∀ (u : m.ker) g, θ (u.val⁻¹ * g) = (ω u : ℂ) * θ g)
    (hI : ∀ χ : PontryaginDual G, (∀ u : m.ker, χ u.val = ω u) →
      let v := fun t ↦ θ (σ t) * unitaryChart(χ) 2 (σ t)
      Integrable v positiveRealHaar ∧ ∫ t, v t ∂positiveRealHaar = 0) : θ = 0 := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have : LocallyCompactSpace ℝ≥0ˣ := e.symm.isOpenEmbedding.locallyCompactSpace
  have : SecondCountableTopology ℝ≥0ˣ := e.symm.isEmbedding.secondCountableTopology
  let w := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 2
  let φ := θ.comp σ.toContinuousMap
  have hFourier (η : PontryaginDual ℝ≥0ˣ) :
      let v := fun t ↦ φ t * w t * (η t : ℂ)
      Integrable v positiveRealHaar ∧ ∫ t, v t ∂positiveRealHaar = 0 := by
    obtain ⟨χ, hu, ht⟩ := exists_character_on_split m hm σ hσ ω η
    have he : (fun t ↦ θ (σ t) * unitaryChart(χ) 2 (σ t)) = fun t ↦ φ t * w t * (η t : ℂ) := by
      funext t
      change θ (σ t) * ((χ (σ t) : ℂ) * (((m (σ t) : ℝ≥0) : ℝ) : ℂ) ^ (2 : ℂ)) =
        θ (σ t) * (1 * ((t.val : ℝ) : ℂ) ^ (2 : ℂ)) * (η t : ℂ)
      rw [hσ, ht, one_mul, mul_right_comm, mul_assoc]
    exact he ▸ hI χ hu
  have hφ : φ = 0 := eq_zero_of_weighted_integrals positiveRealHaar φ w
    (by simpa using (hFourier 1).1) fun η ↦ (hFourier η).2
  ext g
  let u : m.ker := ⟨σ (m g) / g, MonoidHom.mem_ker.mpr (by rw [map_div, hσ, div_self'])⟩
  have hu : u.val⁻¹ * σ (m g) = g := by change (_ / _)⁻¹ * _ = _; rw [inv_div, div_mul_cancel]
  have h := hθ u (σ (m g))
  rw [hu, show θ (σ (m g)) = 0 from DFunLike.congr_fun hφ (m g), mul_zero] at h
  exact h

end HomogeneousUniqueness

/-- A vanishing homogeneous theta function has zero integral on the norm section. -/
private theorem integral_zero_theta {G : Type*} [TopologicalSpace G] (σ : ℝ≥0ˣ → G)
    (c : G → ℂ) {θ : C(G, ℂ)} (hθ : θ = 0) :
    (∫ t, θ (σ t) * c (σ t) ∂positiveRealHaar) = 0 := by
  rw [hθ]
  simp only [ContinuousMap.zero_apply, zero_mul, integral_zero]

/-- Paper: Lemma 5.1.2.1(2), p. 224.
Global homogeneous theta vanishes exactly when the global Z-function vanishes on
the component indexed by the same norm-one character.
Deviation: Vanishing of the meromorphic restriction is tested on the complement of the
allowed poles. -/
theorem mem_homogeneousAdelicTheta_ker_iff (ω : PontryaginDual (MonoidHom.ker m𝔽)) (f : ℬ𝔽) :
    f ∈ LinearMap.ker (homogeneousTheta𝔽 ω) ↔
      ∀ c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c},
        (∀ h : MonoidHom.ker m𝔽, normOneRestriction m𝔽 c.val h = (ω h : ℂ)) →
        (globalIdelicMellin (F := F) f).val c = 0 := by
  change homogeneousAdelicTheta ω f = 0 ↔ ∀ c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c},
    (∀ u : MonoidHom.ker m𝔽, normOneRestriction m𝔽 c.val u = (ω u : ℂ)) →
      globalIdelicZFunction f c.val = 0
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let σ := q.comp τ
  have hσ : RightInverse σ m𝔽 := hτ
  have hres (χ : PontryaginDual C𝔽) (s : ℂ) (u : MonoidHom.ker m𝔽) :
      normOneRestriction m𝔽 (ideleClassNormTwist χ s) u = (χ u.val : ℂ) :=
    normOneRestriction_unitaryChart m𝔽 (isProperMap_ideleClassNorm F).continuous χ s u
  constructor
  · intro hθ c hc
    refine (exists_ideleClassNormTwist (F := F) c.val).elim fun χ hχ' ↦ hχ'.elim fun s hs ↦ ?_
    have hu (u : MonoidHom.ker m𝔽) : χ u.val = ω u :=
      Circle.ext ((hres χ s u).symm.trans (by rw [hs]; exact hc u))
    have he := (homogeneousThetaMellinIntegral_meromorphicContinuation τ ω f hτ χ hu 0).mp
      ⟨fun _ _ ↦ analyticAt_const.meromorphicNFAt, fun z _ ↦
        (integral_zero_theta σ (ideleClassNormTwist χ z) hθ).symm⟩
    change globalIdelicZFunction f c.val = 0
    exact hs ▸ (congrFun he s).symm
  · intro hv
    refine homogeneous_eq_zero_of_radial_integrals m𝔽 (isProperMap_ideleClassNorm F).continuous σ hσ
      ω (homogeneousAdelicTheta ω f) (homogeneousAdelicTheta_homogeneous ω f) fun χ hu ↦ ?_
    let c := ideleClassNormTwist χ 2
    have hs : 1 < (2 : ℂ).re := by norm_num
    have hc := globalTwist_mem_rightHalf χ hs
    have hω (u : MonoidHom.ker m𝔽) : normOneRestriction m𝔽 c u = (ω u : ℂ) :=
      (hres χ 2 u).trans (congrArg Subtype.val (hu u))
    refine ⟨homogeneousThetaMellinIntegral_integrable τ ω f hτ c ⟨hc, hω⟩, ?_⟩
    change homogeneousThetaMellinIntegral τ ω f c = 0
    exact ((globalThetaMellinIntegral_eq_homogeneous τ ω f hτ) ⟨hc, hω⟩).symm.trans
      ((globalThetaMellinIntegral_eq_idelic f hc).trans ((globalIdelicZFunction_eq_integral f hc).symm.trans
        (hv ⟨c, globalOrderBound_rightHalf χ hs⟩ hω)))

/-- Paper: Lemma 5.1.2.2(1), p. 225.
The kernels of the S-local zeta and S-local theta transforms agree. -/
theorem sLocalIdelicMellin_ker_eq :
    LinearMap.ker (sLocalIdelicMellin (F := F) (S := S)) = LinearMap.ker thetaₛ := by
  refine le_antisymm (fun f hf ↦ ?_)
    (sLocalIdelicMellin_vanishes_on_theta_kernel (F := F) (S := S))
  have hinj : Injective (sLocalThetaMellin (F := F) (S := S)) := sLocalThetaMellin_injective
  have h1 : sLocalThetaMellin (F := F) (S := S) (Submodule.Quotient.mk f) = 0 :=
    (sLocalThetaMellin_mk f).trans (LinearMap.mem_ker.mp hf)
  have h2 : (Submodule.Quotient.mk f : SLocalAdelicThetaSpace F S) = 0 :=
    hinj (h1.trans (map_zero (sLocalThetaMellin (F := F) (S := S))).symm)
  exact (Submodule.Quotient.mk_eq_zero _).mp h2

/-- Paper: Lemma 5.1.2.2(2), p. 225.
S-local homogeneous theta vanishes exactly when the S-local Z-function vanishes on
the component indexed by the same norm-one character.
Deviation: Vanishing of the meromorphic restriction is tested on the complement of the
allowed poles. -/
theorem mem_sLocalHomogeneousAdelicTheta_ker_iff (ω : PontryaginDual (MonoidHom.ker mₛ)) (f : ℬₛ) :
    f ∈ LinearMap.ker (homogeneousThetaₛ ω) ↔
      ∀ c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c},
        (∀ h : MonoidHom.ker mₛ, normOneRestriction mₛ c.val h = (ω h : ℂ)) →
        (sLocalIdelicMellin (F := F) (S := S) f).val c = 0 := by
  change homogeneousThetaₛ ω f = 0 ↔ ∀ c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c},
    (∀ u : MonoidHom.ker mₛ, normOneRestriction mₛ c.val u = (ω u : ℂ)) →
      sLocalIdelicZFunction f c.val = 0
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ := ⟨p.comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := thetaSection_rightInverse F S
  let q : (SAdeleRing F S)ˣ →ₜ* Jₛ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let σ := q.comp τ
  have hσ : RightInverse σ mₛ := hτ
  let res (χ : PontryaginDual Jₛ) := χ.comp
    (⟨Subgroup.subtype (MonoidHom.ker mₛ), continuous_subtype_val⟩ : (MonoidHom.ker mₛ) →ₜ* Jₛ)
  have hres (χ : PontryaginDual Jₛ) (s : ℂ) (u : MonoidHom.ker mₛ) :
      normOneRestriction mₛ (unitaryₛ(χ) s) u = (χ u.val : ℂ) :=
    normOneRestriction_unitaryChart mₛ (isProperMap_sIdeleQuotientNorm F S).continuous χ s u
  have hint (χ : PontryaginDual Jₛ) (z : ℂ) (hz : 0 < z.re) :
      sLocalRadialMellinIntegral τ f χ z = sLocalIdelicZFunction f (unitaryₛ(χ) z) := by
    have hr : ∃ (ψ : PontryaginDual Jₛ) (s : ℂ), 0 < s.re ∧ unitaryₛ(χ) z = unitaryₛ(ψ) s :=
      ⟨χ, z, hz, rfl⟩
    exact (sLocalRadialMellinIntegral_eq_theta τ hτ f χ z hz).trans
      ((sLocalThetaMellinIntegral_eq_zeta f hr).trans (sLocalIdelicZFunction_eq_integral f hr).symm)
  constructor
  · intro hθ c hc
    refine (exists_sLocalNormTwist (F := F) (S := S) c.val).elim fun χ hχ' ↦ hχ'.elim fun s hs ↦ ?_
    have hχ : res χ = ω := ContinuousMonoidHom.ext fun u ↦ Circle.ext
      ((hres χ s u).symm.trans (by rw [hs]; exact hc u))
    change sLocalIdelicZFunction f c.val = 0
    rw [← hs]
    have hzero : homogeneousThetaₛ (res χ) f = 0 :=
      (congrArg (fun ψ ↦ homogeneousThetaₛ ψ f) hχ).trans hθ
    have hv (z : ℂ) (hz : 0 < z.re) : sLocalIdelicZFunction f (unitaryₛ(χ) z) = 0 := by
      exact (hint χ z hz).symm.trans
        (integral_zero_theta σ (unitaryₛ(χ) z) (θ := homogeneousThetaₛ (res χ) f) hzero)
    exact congrFun (eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f χ)
      (V := 0) (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0 hv) s
  · intro hv
    refine homogeneous_eq_zero_of_radial_integrals mₛ (isProperMap_sIdeleQuotientNorm F S).continuous σ hσ
      ω (homogeneousThetaₛ ω f) (sLocalHomogeneousAdelicTheta_homogeneous F S
        (sLocalNormOneQuotientMeasure F S) ω f) fun χ hu ↦ ?_
    have he : res χ = ω := ContinuousMonoidHom.ext hu
    let c := unitaryₛ(χ) 2
    have hs : 0 < (2 : ℂ).re := by norm_num
    have hω (u : MonoidHom.ker mₛ) : normOneRestriction mₛ c u = (ω u : ℂ) :=
      (hres χ 2 u).trans (congrArg Subtype.val (hu u))
    have hi := sLocalRadialMellinIntegral_integrable τ hτ f χ 2 hs
    change Integrable (fun t ↦ homogeneousThetaₛ (res χ) f (σ t) * c (σ t)) positiveRealHaar at hi
    have hz := (hint χ 2 hs).trans (hv ⟨c, sLocalOrderBound_positive χ hs⟩ hω)
    change (∫ t, homogeneousThetaₛ (res χ) f (σ t) * c (σ t) ∂positiveRealHaar) = 0 at hz
    let P (ψ : PontryaginDual (MonoidHom.ker mₛ)) :=
      let v := fun t ↦ homogeneousThetaₛ ψ f (σ t) * c (σ t)
      Integrable v positiveRealHaar ∧ ∫ t, v t ∂positiveRealHaar = 0
    exact (congrArg P he).mp (show P (res χ) from ⟨hi, hz⟩)

private theorem globalUnitaryChart_injective (χ : PontryaginDual C𝔽) :
    Injective (ideleClassNormTwist χ) := by
  intro s t h
  let w := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s
  have hw (u : ℝ≥0ˣ) : w u = ((u.val : ℝ) : ℂ) ^ s := one_mul _
  apply (existsUnique_complexPower w).unique hw
  intro u
  let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hg : m𝔽 g = u := canonicalIdeleNormSection_rightInverse F u
  have he := DFunLike.congr_fun h g
  change (χ g : ℂ) * (((m𝔽 g : ℝ≥0) : ℝ) : ℂ) ^ s =
    (χ g : ℂ) * (((m𝔽 g : ℝ≥0) : ℝ) : ℂ) ^ t at he
  rw [hg] at he
  exact (hw u).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) he)

private theorem globalOrderBound_regular {c : X𝔽} (h : 0 ≤ globalIdelicOrderBound c) :
    c ≠ 1 ∧ c ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 := by
  apply not_or.mp
  intro hc
  rw [globalIdelicOrderBound, ite_eq_left hc] at h
  exact (by decide : ¬ (0 : ℤ) ≤ -1) (WithTop.coe_le_coe.mp h)

private theorem globalZ_rightHalf_evalCLM (χ : PontryaginDual C𝔽) {z : ℂ}
    (hz : 1 < z.re) : ∃ L : ℬ𝔽 →L[ℂ] ℂ,
      ∀ f, L f = globalIdelicZFunction f (ideleClassNormTwist χ z) := by
  let d := ideleClassNormTwist χ z
  let x : {d : X𝔽 // 0 ≤ globalIdelicOrderBound d} := ⟨d, globalOrderBound_rightHalf χ hz⟩
  let L : ℬ𝔽 →ₗ[ℂ] ℂ := (ContinuousMap.evalCLM ℂ x).toLinearMap.comp
    (IsLinearMap.mk' _ (globalIdelicZFunction_isLinear (F := F)))
  have hr := globalTwist_mem_rightHalf χ hz
  refine ⟨⟨L, ?_⟩, fun _ ↦ rfl⟩
  change Continuous (fun f : ℬ𝔽 ↦ globalIdelicZFunction f d)
  have he : (fun f : ℬ𝔽 ↦ globalIdelicZFunction f d) = fun f ↦ globalIdelicZetaIntegral f d :=
    funext fun f ↦ globalIdelicZFunction_eq_integral f hr
  exact (congrArg Continuous he).mpr (continuous_globalIdelicZetaIntegral d hr)

private theorem globalZ_chart_evalCLM (χ : PontryaginDual C𝔽) (s : ℂ)
    (hs : 0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ s)) :
    ∃ L : ℬ𝔽 →L[ℂ] ℂ, ∀ f, L f = globalIdelicZFunction f (ideleClassNormTwist χ s) := by
  classical
  let : BarrelledSpace ℂ ℬ𝔽 := (adeleSchwartz_montel (F := F)).2.1
  let bad := ideleClassNormTwist χ ⁻¹' ({1, ideleClassNormTwist (1 : PontryaginDual C𝔽) 1} : Set X𝔽)
  have hb : bad.Finite := ((Set.finite_singleton _).insert _).preimage (globalUnitaryChart_injective χ).injOn
  have hreg {z : ℂ} (h : 0 ≤ globalIdelicOrderBound (ideleClassNormTwist χ z)) : z ∈ badᶜ :=
    not_or.mpr (globalOrderBound_regular h)
  have hcon := hb.countable.isConnected_compl_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)
  have hpos : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact exists_continuousLinearMap_of_analytic_continuation
    (fun f : ℬ𝔽 ↦ fun z ↦ globalIdelicZFunction f (ideleClassNormTwist χ z))
    hb.isClosed.isOpen_compl hcon.isPreconnected (fun f z hz ↦ (globalIdelicZFunction_poles f χ).1 z
      (not_or.mp hz)) (b := 2) (hreg (globalOrderBound_rightHalf χ (by norm_num)))
    (hpos.mono fun _ ↦ globalZ_rightHalf_evalCLM χ)
    (hreg hs)

/-- Paper: Lemma 5.1.3.1(1), p. 227.
The global idelic Mellin transform is continuous for compact convergence away from
the trivial and norm characters. -/
theorem globalIdelicMellin_continuous :
    Continuous (globalIdelicMellin (F := F)) := by
  let : BarrelledSpace ℂ ℬ𝔽 := (adeleSchwartz_montel (F := F)).2.1
  let P (d : X𝔽) := 0 ≤ globalIdelicOrderBound d →
    ∃ L : ℬ𝔽 →L[ℂ] ℂ, ∀ f, L f = globalIdelicZFunction f d
  have hP (d : X𝔽) : P d := (exists_ideleClassNormTwist d).elim fun χ hχ ↦ hχ.elim fun s hs ↦
    (congrArg P hs).mp (globalZ_chart_evalCLM χ s)
  exact (continuous_of_continuous_eval_barrelled (globalZValues : ℬ𝔽 → _)
    (fun c ↦ hP c.val c.property)).subtype_mk globalIdelicZFunction_mem

section Translate

private theorem integral_translate_character {G : Type*} [Group G] {mG : MeasurableSpace G}
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (u : G → ℂ) (c : G →* ℂ) (g : G) :
    (∫ x, u (g⁻¹ * x) * c x ∂μ) = c g * ∫ x, u x * c x ∂μ := by
  rw [← integral_mul_left_eq_self (μ := μ) (fun x ↦ u (g⁻¹ * x) * c x) g, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun x ↦ by simp only [inv_mul_cancel_left, map_mul, mul_left_comm])

private theorem normTwist_eval_analytic {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →* ℝ≥0ˣ) (hm : Continuous m) (c : QuasiCharacter G) (g : G) (s : ℂ) :
    AnalyticAt ℂ (fun z ↦ quasiCharacterNormTwist m hm c z g) s := by
  let N : ℂ := (((m g : ℝ≥0) : ℝ) : ℂ)
  have hn : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m g).ne_zero)
  change AnalyticAt ℂ (fun z ↦ c g * N ^ z) s
  exact analyticAt_const.mul ((differentiable_id.const_cpow (Or.inl hn)).analyticAt s)

end Translate

/-- Paper: Lemma 5.1.3.1(1), p. 227.
Global Mellin evaluation at a regular character intertwines inverse left translation
with multiplication by that character on the class of the translating idele.
Deviation: Equality of the operators is stated by evaluation on every test function. -/
theorem globalIdelicMellin_unitTranslate (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽)
    (c : {c : X𝔽 // 0 ≤ globalIdelicOrderBound c}) :
    (globalIdelicMellin (F := F) (schwartzBruhatUnitTranslate g f)).val c =
      c.val (QuotientGroup.mk g) * (globalIdelicMellin (F := F) f).val c := by
  change globalIdelicZFunction (schwartzBruhatUnitTranslate g f) c.val =
    c.val (QuotientGroup.mk g) * globalIdelicZFunction f c.val
  obtain ⟨χ, s, hs⟩ := exists_ideleClassNormTwist c.val
  rw [← hs]
  let q := (QuotientGroup.mk g : C𝔽)
  let L := fun z ↦ ideleClassNormTwist χ z q
  let Z := fun z ↦ globalIdelicZFunction f (ideleClassNormTwist χ z)
  have hL (z : ℂ) : AnalyticAt ℂ L z := normTwist_eval_analytic m𝔽 (isProperMap_ideleClassNorm F).continuous _ q z
  have hn (z : ℂ) : L z ≠ 0 := ((Group.isUnit q).map (ideleClassNormTwist χ z)).ne_zero
  refine congrFun (eq_of_agree_rightHalf (globalIdelicZFunction_meromorphic _ χ)
    (V := L * Z) (fun z hz ↦ (meromorphicNFAt_mul_iff_right (hL z) (hn z)).mpr
      (globalIdelicZFunction_meromorphic f χ hz)) 1 fun z hz ↦ ?_) s
  have hr := globalTwist_mem_rightHalf χ hz
  simp only [L, Z, Pi.mul_apply, globalIdelicZFunction_eq_integral _ hr]
  let : MeasurableSpace (IdeleGroup (𝓞 F) F) := borel _
  let : BorelSpace (IdeleGroup (𝓞 F) F) := ⟨rfl⟩
  have : (multiplicativeTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.1
  exact integral_translate_character (multiplicativeTamagawaMeasure F)
    (fun x ↦ f (Multiplicative.ofAdd x.val))
    ((ideleClassNormTwist χ z).toMonoidHom.comp (QuotientGroup.mk' _)) g

-- TODO(paper-gap): Lemma 5.1.3.1(2) calls D_S the divisor of rho_S, whereas its
-- prelude uses the divisor of L_S. The full divisor of rho_S has positive coefficients
-- at its zeros. These are not vanishing conditions on the image of the transform.

private theorem sLocalZ_rightHalf_evalCLM (χ : PontryaginDual Jₛ) {z : ℂ}
    (hz : 0 < z.re) : ∃ L : ℬₛ →L[ℂ] ℂ,
      ∀ f, L f = sLocalIdelicZFunction f (unitaryₛ(χ) z) := by
  let d := unitaryₛ(χ) z
  have hd : ∃ (ψ : PontryaginDual Jₛ) (t : ℂ), 0 < t.re ∧ d = unitaryₛ(ψ) t := ⟨χ, z, hz, rfl⟩
  have h := sLocalIdelicZetaIntegral_tempered d hd
  exact ⟨h.choose, fun f ↦ (h.choose_spec f).trans (sLocalIdelicZFunction_eq_integral f hd).symm⟩

private theorem sLocalZ_chart_evalCLM (χ : PontryaginDual Jₛ) (s : ℂ)
    (hs : 0 ≤ sLocalIdelicOrderBound (unitaryₛ(χ) s)) :
    ∃ L : ℬₛ →L[ℂ] ℂ, ∀ f, L f = sLocalIdelicZFunction f (unitaryₛ(χ) s) := by
  classical
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  let ρ := fun z ↦ sLocalRhoFactor (unitaryₛ(χ) z)
  let U := {z : ℂ | 0 ≤ meromorphicOrderAt ρ z}
  have hr : Meromorphic ρ := sLocalRhoFactor_meromorphic χ
  have hU : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr fun z hz ↦ ?_
    rw [← nhdsNE_sup_pure z, Filter.mem_sup]
    exact ⟨(hr z).eventually_analyticAt.mono fun _ ha ↦ ha.meromorphicOrderAt_nonneg, hz⟩
  have ha : {z | AnalyticAt ℂ ρ z} ⊆ U := fun ⦃_⦄ hz ↦ hz.meromorphicOrderAt_nonneg
  have hb : Uᶜ.Countable := hr.countable_compl_analyticAt.mono (Set.compl_subset_compl.mpr ha)
  have hcon : IsPreconnected U := by
    simpa only [compl_compl] using (hb.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected
  have hreg {z : ℂ} (h : 0 ≤ sLocalIdelicOrderBound (unitaryₛ(χ) z)) : z ∈ U := by
    rw [sLocalOrderBound_chart, le_min_iff] at h
    exact h.2
  have hpos : ∀ᶠ z : ℂ in 𝓝 1, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact exists_continuousLinearMap_of_analytic_continuation
    (fun f : ℬₛ ↦ fun z ↦ sLocalIdelicZFunction f (unitaryₛ(χ) z))
    hU hcon (fun f z hz ↦ (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ z))
      |>.meromorphicOrderAt_nonneg_iff_analyticAt.mp
        ((le_min le_rfl hz).trans (sLocalIdelicZFunction_poles f χ z)))
    (b := 1) (hreg (sLocalOrderBound_positive χ (by norm_num)))
    (hpos.mono fun _ ↦ sLocalZ_rightHalf_evalCLM χ) (hreg hs)

/-- Paper: Lemma 5.1.3.1(2), p. 227.
The S-local idelic Mellin transform is continuous for compact convergence away from
the poles of the correcting factor.
Deviation: The source is the S-local Schwartz–Bruhat space, as in the displayed map.
The target uses only the pole part of the divisor, as in §3.3.1. -/
theorem sLocalIdelicMellin_continuous :
    Continuous (sLocalIdelicMellin (F := F) (S := S)) := by
  let : BarrelledSpace ℂ ℬₛ := (sAdeleSchwartz_montel (F := F) S).1
  let P (d : Xₛ) := 0 ≤ sLocalIdelicOrderBound d →
    ∃ L : ℬₛ →L[ℂ] ℂ, ∀ f, L f = sLocalIdelicZFunction f d
  have hP (d : Xₛ) : P d := (exists_sLocalNormTwist d).elim fun χ hχ ↦ hχ.elim fun s hs ↦
    (congrArg P hs).mp (sLocalZ_chart_evalCLM χ s)
  exact (continuous_of_continuous_eval_barrelled (sLocalZValues : ℬₛ → _)
    (fun c ↦ hP c.val c.property)).subtype_mk sLocalIdelicZFunction_mem

/-- Paper: Lemma 5.1.3.1(2), p. 227.
S-local Mellin evaluation at a regular character intertwines inverse left translation
with multiplication by that character on the class of the translating S-idele.
Deviation: Equality of the operators is stated by evaluation on every test function. -/
theorem sLocalIdelicMellin_unitTranslate (g : (SAdeleRing F S)ˣ) (f : ℬₛ)
    (c : {c : Xₛ // 0 ≤ sLocalIdelicOrderBound c}) :
    (sLocalIdelicMellin (F := F) (S := S) (schwartzBruhatUnitTranslate g f)).val c =
      c.val (QuotientGroup.mk g) * (sLocalIdelicMellin (F := F) (S := S) f).val c := by
  change sLocalIdelicZFunction (schwartzBruhatUnitTranslate g f) c.val =
    c.val (QuotientGroup.mk g) * sLocalIdelicZFunction f c.val
  obtain ⟨χ, s, hs⟩ := exists_sLocalNormTwist c.val
  rw [← hs]
  let q := (QuotientGroup.mk g : Jₛ)
  let L := fun z ↦ unitaryₛ(χ) z q
  let Z := fun z ↦ sLocalIdelicZFunction f (unitaryₛ(χ) z)
  have hL (z : ℂ) : AnalyticAt ℂ L z := normTwist_eval_analytic mₛ (isProperMap_sIdeleQuotientNorm F S).continuous _ q z
  have hn (z : ℂ) : L z ≠ 0 := ((Group.isUnit q).map (unitaryₛ(χ) z)).ne_zero
  refine congrFun (eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic _ χ)
    (V := L * Z) (fun z hz ↦ (meromorphicNFAt_mul_iff_right (hL z) (hn z)).mpr
      (sLocalIdelicZFunction_meromorphic f χ hz)) 0 fun z hz ↦ ?_) s
  have hr : ∃ (ψ : PontryaginDual Jₛ) (t : ℂ), 0 < t.re ∧ unitaryₛ(χ) z = unitaryₛ(ψ) t :=
    ⟨χ, z, hz, rfl⟩
  simp only [L, Z, Pi.mul_apply, sLocalIdelicZFunction_eq_integral _ hr]
  have := sIdeleGroup_borelSpace (F := F) (S := S)
  have := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  exact integral_translate_character (sMultiplicativeTamagawaMeasure F S)
    (fun x ↦ f (Multiplicative.ofAdd x.val))
    ((unitaryₛ(χ) z).toMonoidHom.comp (QuotientGroup.mk' _)) g

-- TODO(paper-gap): The polar denominators in (5.1.3.3) have the wrong sign on i x₀.
-- If χ = |·|^(i x₀), the exponent of c is s + i x₀.

-- TODO(paper-gap): Footnote 1 on p. 230 asks for a version with an I-exponentially
-- decaying target but gives no statement.

end RiemannMasullo
