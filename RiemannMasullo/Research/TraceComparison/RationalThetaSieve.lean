module
public import RiemannMasullo.Research.TraceComparison.RationalThetaSeries
public import RiemannMasullo.Research.TraceComparison.FiniteEulerRecovery

/-! # Finite Euler recovery in the rational geometric theta space

For a class of norm a rational prime p, left translation by its inverse evaluates a radial
function at px. On the half-twisted theta profile the factor p^(-1/2) cancels the square root
of p. The translated positive-integer series therefore consists of the terms indexed by positive
multiples of p. Subtracting it from the full series gives the usual unit sieve at p. -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField.AdeleRing NNReal SchwartzMap
namespace RiemannMasullo.StripNuclearity

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local instance : MeasurableSpace Cℚ := borel _
local instance : BorelSpace Cℚ := ⟨rfl⟩
local instance : T2Space Cℚ := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.1
local instance : LocallyCompactSpace Cℚ := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.1
attribute [local instance] instIdeleClassSecondCountableSec1
local instance : Measure.IsHaarMeasure (ideleClassTamagawaMeasure ℚ) := (ideleClassTamagawaMeasure_isWeil ℚ).1

local notation "μ" => ideleClassTamagawaMeasure ℚ
local notation "m" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "W(" a ", " b ", " s ")" => CompactIntervalSobolev μ (logIdeleClassNorm ℚ) a b s
local notation "I(" a ", " h ", " s ")" =>
  actionIsotype ((exists_globalThetaSobolevAction (F := ℚ) a h s).choose.comp (ideleClassNorm ℚ).ker.subtype) 1

/-- Ambient representatives of unbounded-band, even, polar-free real theta generators at the functional-equation center. -/
def ratCentralThetaTests (a b s : ℝ) : Set W(a, b, s) :=
  {w | ∃ f : SchwartzMap ℝ ℂ, Function.Even (f : ℝ → ℂ) ∧
    HasCompactSupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ∧ f 0 = 0 ∧ 𝓕 f 0 = 0 ∧
    (w : Cℚ → ℂ) =ᵐ[μ] ratRadialThetaProfile (1 / 2) f}

private theorem subtype_map_carrier {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H : Submodule ℂ E) (J : Submodule ℂ H) :
    ((J.map H.subtype) : Set E) = Set.range (fun z : J ↦ z.val.val) := by
  ext w
  exact ⟨fun ⟨y, hy, e⟩ ↦ ⟨⟨y, hy⟩, e⟩, fun ⟨y, e⟩ ↦ ⟨y.val, y.property, e⟩⟩

/-- Applying the fixed finite Euler factor to all standard rational theta generators
has exactly the original closed span inside the full idelic Hilbert space. -/
theorem ratCentralThetaTests_finiteEuler_closure {a b s : ℝ} (hab : a ≤ b) (hs : 0 ≤ s)
    (ha : -(1 / 2 : ℝ) < a) (q : Cℚ) (hq : 0 < logIdeleClassNorm ℚ q) :
    closure ((⇑(1 - finiteEulerTranslation μ m a b s hab hs q)) '' ratCentralThetaTests a b s) =
      Set.range (fun y : I(1/2, hab, hs) ↦ y.val.val) := by
  let H := globalThetaSobolev ℚ (1/2) hab hs
  let R := (exists_globalThetaSobolevAction (F := ℚ) (1/2) hab hs).choose
  let I₀ := actionIsotype (R.comp (ideleClassNorm ℚ).ker.subtype) 1
  let U : Submodule ℂ W(a,b,s) := I₀.map H.subtype
  let T := finiteEulerTranslation μ m a b s hab hs q
  let E := (1 - T)
  have hrange : (U : Set W(a,b,s)) = Set.range (fun y : I(1/2, hab, hs) ↦ y.val.val) :=
    subtype_map_carrier H I₀
  have hd : closure (ratCentralThetaTests a b s) = (U : Set W(a,b,s)) :=
    (ratRadialTheta_closure_eq_globalThetaSobolev_trivial (1/2) hab hs).trans hrange.symm
  have hclosed : IsClosed (U : Set W(a,b,s)) := (congrArg IsClosed hd).mp isClosed_closure
  have hinv : ∀ x ∈ U, T x ∈ U := by
    rintro _ ⟨y, hy, rfl⟩
    change (Real.exp (-logIdeleClassNorm ℚ q / 2)) •
      (hardySobolevTranslation μ m a b s hab hs q⁻¹ (y : W(a,b,s))) ∈ U
    apply U.smul_of_tower_mem
    refine ⟨R q⁻¹ y, ?_, (exists_globalThetaSobolevAction (F := ℚ) (1/2) hab hs).choose_spec.1 q⁻¹ y⟩
    apply (mem_actionIsotype _ _ _).2
    intro k
    have hk := (mem_actionIsotype _ _ _).1 hy k
    change R k.val (R q⁻¹ y) = ((1 : PontryaginDual (ideleClassNorm ℚ).ker) k : ℂ) • R q⁻¹ y
    change R k.val y = ((1 : PontryaginDual (ideleClassNorm ℚ).ker) k : ℂ) • y at hk
    rw [← mul_apply_eq_comp, ← map_mul, mul_comm, map_mul, mul_apply_eq_comp, hk, map_smul]
  have hrec := finiteEulerFactor_topologicalClosure μ m a b s hab hs ha q hq U hinv
  calc
    closure (E '' ratCentralThetaTests a b s) = closure (E '' closure (ratCentralThetaTests a b s)) :=
      (closure_image_closure E.continuous).symm
    _ = closure (E '' (U : Set W(a,b,s))) := congrArg (fun S ↦ closure (E '' S)) hd
    _ = (U.topologicalClosure : Set W(a,b,s)) := congrArg SetLike.coe hrec
    _ = U := hclosed.closure_eq
    _ = _ := hrange

end RiemannMasullo.StripNuclearity
