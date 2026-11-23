module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
public import Mathlib.Analysis.Distribution.TestFunction
import RiemannMasullo.ForMathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real

/-!
# Uniform Fourier–Mellin estimates, jump singularities and compactly supported tests

Masullo, Appendix D, §§D.3.4–D.3.6, pp. 815–821.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff Distributions NNReal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [hT2 : T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ)

section RiemannLebesgue

variable (I : Set ℝ) (hm : IsModulation m) (hms : Surjective m)

/-- A continuous real-valued additive character vanishes on a subgroup with open annihilator. -/
private theorem le_ker_of_isOpen_lcaAnnihilator
    (l : G →ₜ* Multiplicative ℝ) {k : Subgroup G}
    (hk : IsOpen (lcaAnnihilator k : Set (PontryaginDual G))) :
    k ≤ l.toMonoidHom.ker := by
  let χ (t : ℝ) : PontryaginDual G :=
    { toFun := fun x ↦ Circle.exp (t * Multiplicative.toAdd (l x))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [map_mul l]
        change Circle.exp (t * (Multiplicative.toAdd (l x) + Multiplicative.toAdd (l y))) = _
        rw [mul_add, Circle.exp_add]
      continuous_toFun := Circle.exp.continuous.comp
        (continuous_const.mul (continuous_toAdd.comp l.continuous)) }
  have hχ : Continuous χ :=
    ContinuousMonoidHom.continuous_of_continuous_uncurry χ
      (Circle.exp.continuous.comp
        (continuous_fst.mul ((continuous_toAdd.comp l.continuous).comp continuous_snd)))
  have hAll : χ ⁻¹' (lcaAnnihilator k : Set (PontryaginDual G)) = univ :=
    IsClopen.eq_univ ⟨((lcaAnnihilator k).isClosed_of_isOpen hk).preimage hχ, hk.preimage hχ⟩
      ⟨0, (mem_lcaAnnihilator_iff k (χ 0)).2 fun x ↦ by
        change Circle.exp (0 * Multiplicative.toAdd (l x.val)) = 1
        simp⟩
  intro x hx
  change Multiplicative.toAdd (l x) = 0
  by_contra h
  let t := Real.pi / Multiplicative.toAdd (l x)
  have ht : t ∈ χ ⁻¹' (lcaAnnihilator k : Set (PontryaginDual G)) := hAll.symm ▸ mem_univ t
  have hxχ := (mem_lcaAnnihilator_iff k (χ t)).1 ht ⟨x, hx⟩
  change Circle.exp (t * Multiplicative.toAdd (l x)) = 1 at hxχ
  exact Circle.exp_pi_ne_one (by simpa only [t, div_mul_cancel₀ _ h] using hxχ)

/-- In each discrete fibre, the lift of a continuous real-valued additive character
is an affine, smooth function of the real and torus cover coordinates. -/
private theorem contDiff_logHom_elementaryCover {d t r : ℕ} {F A : Type*}
    [AddCommGroup F] [TopologicalSpace F] [CommGroup A] [TopologicalSpace A]
    (e : Multiplicative (ElementaryLieGroup d t r F) ≃ₜ* A) (n : A →ₜ* Multiplicative ℝ)
    (z : Fin r → ℤ) (b : F) (p : ℕ∞ω) :
    ContDiff ℝ p (fun xt ↦ Multiplicative.toAdd
      (n (e (Multiplicative.ofAdd (elementaryCover xt z b))))) := by
  let l : ElementaryLieGroup d t r F →+ ℝ :=
    AddMonoidHom.mk' (fun y ↦ Multiplicative.toAdd (n (e (Multiplicative.ofAdd y)))) <| by
      intro x y
      rw [← toAdd_mul, ← map_mul n]
      exact congrArg (fun q ↦ Multiplicative.toAdd (n q))
        (e.map_mul' (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))
  have hl : Continuous l :=
    continuous_toAdd.comp (n.continuous.comp (e.continuous_toFun.comp continuous_ofAdd))
  change ContDiff ℝ p (fun xt ↦ l (elementaryCover xt z b))
  let cover : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin t)) →+
      ElementaryLieGroup d t r F :=
    { toFun := fun xt ↦ elementaryCover xt 0 0
      map_zero' := by simp [elementaryCover, Pi.zero_def]
      map_add' := by
        intro x y
        simp [elementaryCover, Pi.add_def, Pi.zero_def] }
  have hCover : Continuous cover :=
    continuous_fst.prodMk ((continuous_pi fun i ↦ ((AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd))).prodMk
        (continuous_const.prodMk continuous_const))
  let l₀ := l.comp cover
  have hLinear : ContDiff ℝ p l₀ := (l₀.toRealLinearMap (hl.comp hCover)).contDiff
  have hAffine : (fun xt ↦ l₀ xt + l (elementaryCover 0 z b)) =
      fun xt ↦ l (elementaryCover xt z b) := by
    funext xt
    change l (elementaryCover xt 0 0) + l (elementaryCover 0 z b) = _
    rw [← map_add]
    simp [elementaryCover, ← Pi.zero_def]
  rw [← hAffine]
  exact hLinear.add contDiff_const

/-- Untwisting by a real power of the modulation preserves every finite order
of Bruhat differentiability. The same good subgroup fixes both functions. -/
private theorem isBruhatContDiff_of_modulationWeight
    {p : ℕ} {a : ℝ} {f : G → ℂ} (hf : IsBruhatContDiff p (modulationWeight m a f)) :
    IsBruhatContDiff p f := by
  have hPos (x : G) : (0 : ℝ) < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  let l : G →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (Real.log ((m x).val : ℝ))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        simp only [map_mul, Units.val_mul, NNReal.coe_mul, ← ofAdd_add]
        rw [Real.log_mul (hPos x).ne' (hPos y).ne']
      continuous_toFun := continuous_ofAdd.comp
        ((NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
          fun x ↦ (hPos x).ne') }
  obtain ⟨k, hk, hInvariant, hDescend⟩ := hf
  have hKer := le_ker_of_isOpen_lcaAnnihilator l hk.2.1
  have hWeight (x : G) :
      modulationWeight m a f x = (Real.exp (Multiplicative.toAdd (l x) * a) : ℂ) * f x := by
    rw [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply, Real.rpow_def_of_pos (hPos x)]
    rfl
  have hUndo (x : G) :
      (Real.exp (Multiplicative.toAdd (l x) * -a) : ℂ) * modulationWeight m a f x = f x := by
    rw [hWeight, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp [mul_neg]
  refine ⟨k, hk, ?_, ?_⟩
  · intro h x
    have hh : l h.val = 1 := hKer h.property
    rw [← hUndo (h.val * x), ← hUndo x, hInvariant, map_mul, hh, one_mul]
  · intro s hs
    obtain ⟨g, hg, hSmooth⟩ := hDescend s hs
    let l' : s.val.1 →* Multiplicative ℝ := l.toMonoidHom.comp s.val.1.subtype
    have hKer' : (OrderDual.ofDual s.val.2).comap s.val.1.subtype ≤ l'.ker :=
      fun x hx ↦ hKer (hs ▸ hx)
    let lq : s.quotient →ₜ* Multiplicative ℝ :=
      { toMonoidHom := QuotientGroup.lift _ l' hKer'
        continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
          (l.continuous.comp continuous_subtype_val) }
    refine ⟨fun q ↦ (Real.exp (Multiplicative.toAdd (lq q) * -a) : ℂ) * g q,
      fun x ↦ ?_, fun e z b ↦ ?_⟩
    · dsimp only
      rw [hg]
      exact hUndo x.val
    · have hLog := contDiff_logHom_elementaryCover e.equiv.symm lq z b (p : ℕ∞)
      exact (Complex.ofRealCLM.contDiff.comp ((hLog.mul (contDiff_const (c := -a))).exp)).mul
        (hSmooth e z b)

/-- Paper: Remark D.3.4.1, p. 815. A function of prescribed exponential decay
is Bruhat smooth whenever the exponent interval is nonempty. -/
theorem modulatedExponentialDecay_mem_bruhatSmooth (hne : I.Nonempty)
    (f : ModulatedExponentialDecay m I) :
    f.val ∈ bruhatSmoothSubmodule := by
  obtain ⟨a, ha⟩ := hne
  have hw : modulationWeight m a f.val ∈ schwartzBruhatSubmodule G :=
    (Submodule.mem_iInf _).mp f.property ⟨a, ha⟩
  have hs := schwartzBruhat_isBruhatSmooth (⟨modulationWeight m a f.val, hw⟩ : SchwartzBruhat G)
  refine (Submodule.mem_iInf _).2 fun p ↦ ?_
  exact isBruhatContDiff_of_modulationWeight m (hs p)

/-- Twisting a first derivative gives the derivative of the twist minus a scalar multiple
of the twist itself. The scalar is independent of the function. -/
private theorem modulationWeight_firstOrder (b : LCATopologicalLie G) (a : ℝ) :
    ∃ z : ℂ, ∀ f : bruhatSmoothSubmodule (G := G),
      modulationWeight m a (bruhatFirstOrder b f).val =
        bruhatDirectionalDeriv b (modulationWeight m a f.val) - z • modulationWeight m a f.val := by
  let w (x : G) : ℝ := ((m x).val : ℝ) ^ a
  have hPos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  let logOrbit : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t ↦ Real.log ((m (b (Multiplicative.ofAdd t))).val : ℝ)) (by
      intro s t
      simp only [ofAdd_add, map_mul, Units.val_mul, NNReal.coe_mul]
      exact Real.log_mul (hPos _).ne' (hPos _).ne')
  have hLogContinuous : Continuous logOrbit :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (m.continuous.comp (b.continuous.comp continuous_ofAdd)))).log
      fun _ ↦ (hPos _).ne'
  have hLog (t : ℝ) : logOrbit t = t * logOrbit 1 := by
    simpa only [smul_eq_mul, mul_one] using map_real_smul logOrbit hLogContinuous t (1 : ℝ)
  let c := logOrbit 1 * a
  have hOrbit (x : G) (t : ℝ) :
      w (x * b (Multiplicative.ofAdd t)) = w x * Real.exp (t * c) := by
    unfold w
    rw [map_mul, Units.val_mul, NNReal.coe_mul,
      Real.mul_rpow (hPos x).le (hPos _).le, Real.rpow_def_of_pos (hPos (b _))]
    change _ * Real.exp (logOrbit t * a) = _
    rw [hLog, mul_assoc]
  have hw (x : G) : HasDerivAt (fun t : ℝ ↦ (w (x * b (Multiplicative.ofAdd t)) : ℂ))
      ((w x * c : ℝ) : ℂ) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const c).exp.const_mul (w x)).ofReal_comp
    simpa only [id, zero_mul, Real.exp_zero, one_mul, hOrbit] using h
  refine ⟨(c : ℂ), fun f ↦ ?_⟩
  let F := modulationWeight m a f.val
  funext x
  have h := ((hw x).fun_mul (hasDerivAt_bruhatDirectionalDeriv b
    ((mem_bruhatSmoothSubmodule_iff f.val).1 f.property 1) x)).deriv
  change bruhatDirectionalDeriv b F x =
    ((w x * c : ℝ) : ℂ) * f.val (x * b (Multiplicative.ofAdd 0)) +
      (w (x * b (Multiplicative.ofAdd 0)) : ℂ) * bruhatDirectionalDeriv b f.val x at h
  simp only [ofAdd_zero, map_one, mul_one, Complex.ofReal_mul] at h
  change (w x : ℂ) * bruhatDirectionalDeriv b f.val x =
    bruhatDirectionalDeriv b F x - (c : ℂ) * ((w x : ℂ) * f.val x)
  rw [h]
  ring

/-- Paper: Remark D.3.4.1, p. 815. First-order differentiation preserves each
exponential decay condition by the product rule for the modulation weight.
Deviation: If the modulation along the subgroup is exp(rt), the derivative
of the weight at exponent a has coefficient a * r. -/
private theorem bruhatFirstOrder_mem_modulatedExponentialDecay
    (b : LCATopologicalLie G) (f : bruhatSmoothSubmodule (G := G))
    (hf : f.val ∈ modulatedExponentialDecaySubmodule m I) :
    (bruhatFirstOrder b f).val ∈ modulatedExponentialDecaySubmodule m I := by
  refine (Submodule.mem_iInf _).2 fun a ↦ Submodule.mem_comap.2 ?_
  let F := modulationWeight m a f.val
  have hF : F ∈ schwartzBruhatSubmodule G :=
    modulationWeight_mem_schwartzBruhat m I a ⟨f.val, hf⟩
  obtain ⟨A, hA⟩ := bruhatFirstOrder_schwartz b
  have hDF : bruhatDirectionalDeriv b F ∈ schwartzBruhatSubmodule G := by
    have hEq : (A ⟨F, hF⟩).val = bruhatDirectionalDeriv b F := funext (hA ⟨F, hF⟩)
    exact hEq ▸ (A ⟨F, hF⟩).property
  obtain ⟨c, hc⟩ := modulationWeight_firstOrder m b a
  rw [hc f]
  exact (schwartzBruhatSubmodule G).sub_mem hDF ((schwartzBruhatSubmodule G).smul_mem c hF)

include hm hms in
/-- Paper: Remark D.3.4.1, p. 815. Invariant differential operators preserve
the Schwartz–Bruhat space with decay exponents in the given interval. -/
theorem modulatedExponentialDecay_invariantDiff (hInt : OrdConnected I) (hne : I.Nonempty)
    (D : bruhatDiffAlgebra G) (f : ModulatedExponentialDecay m I) :
    (D.val ⟨f.val, modulatedExponentialDecay_mem_bruhatSmooth m I hne f⟩).val ∈
      modulatedExponentialDecaySubmodule m I := by
  refine Algebra.adjoin_induction
    (p := fun (A : Module.End ℂ (bruhatSmoothSubmodule (G := G))) _ ↦
      ∀ (g : bruhatSmoothSubmodule (G := G)),
        g.val ∈ modulatedExponentialDecaySubmodule m I →
          (A g).val ∈ modulatedExponentialDecaySubmodule m I)
    ?_ ?_ ?_ ?_ D.property _ f.property
  · rintro _ ⟨b, rfl⟩ g hg
    exact bruhatFirstOrder_mem_modulatedExponentialDecay m I b g hg
  · intro z g hg
    rw [Module.algebraMap_end_apply, Submodule.coe_smul]
    exact (modulatedExponentialDecaySubmodule m I).smul_mem z hg
  · intro A B _ _ hA hB g hg
    rw [LinearMap.add_apply, Submodule.coe_add]
    exact (modulatedExponentialDecaySubmodule m I).add_mem (hA g hg) (hB g hg)
  · intro A B _ _ hA hB g hg
    exact hA (B g) (hB g hg)

/-- The unitary character obtained by dividing a quasi-character by its norm. -/
private def quasiCharacterUnitaryPart (c : QuasiCharacter G) : PontryaginDual G := by
  have hne (x : G) : ‖c x‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit x).map c).ne_zero
  exact
    { toFun := fun x ↦ ⟨c x / (‖c x‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self (hne x)])⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y ↦ Circle.ext (by
        change c (x * y) / (‖c (x * y)‖ : ℂ) = (c x / (‖c x‖ : ℂ)) * (c y / (‖c y‖ : ℂ))
        rw [map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm])
      continuous_toFun := (c.continuous.div (Complex.continuous_ofReal.comp c.continuous.norm)
        (fun x ↦ Complex.ofReal_ne_zero.mpr (hne x))).subtype_mk _ }

/-- Paper: Theorem D.3.4.2, p. 816. A continuous quasi-character is Bruhat smooth,
so the operator in the symbol formula can act on it. -/
theorem quasiCharacter_mem_bruhatSmooth (c : QuasiCharacter G) :
    (fun x : G ↦ c x) ∈ bruhatSmoothSubmodule := by
  let n : G →ₜ* ℝ≥0ˣ :=
    ⟨(nnNormHom.toMonoidHom.comp c.toMonoidHom).toHomUnits,
      Continuous.of_coeHom_comp c.continuous.nnNorm⟩
  let χ := quasiCharacterUnitaryPart c
  have hw : modulationWeight n (-1) (fun x ↦ c x) = fun x ↦ (χ x : ℂ) := by
    funext x
    change ((‖c x‖ ^ (-1 : ℝ) : ℝ) : ℂ) * c x = c x / (‖c x‖ : ℂ)
    rw [Real.rpow_neg_one, Complex.ofReal_inv, div_eq_inv_mul]
  apply (mem_bruhatSmoothSubmodule_iff _).2
  intro p
  apply isBruhatContDiff_of_modulationWeight n (a := -1)
  rw [hw]
  exact (mem_bruhatSmoothSubmodule_iff _).1 (pontryaginDual_mem_bruhatSmooth χ) p

/-- Paper: (D.3.4.1), p. 816. The symbol at a quasi-character is the evaluation
at the identity of the differential operator applied to that quasi-character. -/
def bruhatDiffQuasiCharacterSymbol (D : bruhatDiffAlgebra G) (c : QuasiCharacter G) : ℂ :=
  (D.val ⟨fun x : G ↦ c x, quasiCharacter_mem_bruhatSmooth c⟩).val 1

/-- Paper: Theorem D.3.4.2, p. 816. The extended symbol agrees with the
ordinary symbol on unitary characters. -/
theorem bruhatDiffQuasiCharacterSymbol_unitary (D : bruhatDiffAlgebra G) (χ : PontryaginDual G) :
    let coeCircle : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    bruhatDiffQuasiCharacterSymbol D (coeCircle.comp χ) = bruhatDiffSymbol D χ := rfl

variable [hSC : SecondCountableTopology G] [MeasurableSpace G] [hBorel : BorelSpace G]

section StripEstimates

variable (μ : Measure G) [μ.IsHaarMeasure]

private theorem quasiCharacter_mul_decay_mem_schwartz (f : modulatedExponentialDecaySubmodule m I)
    {c : QuasiCharacter G} (hc : c ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I) :
    (fun x ↦ f.val x * c x) ∈ schwartzBruhatSubmodule G := by
  let a : I := ⟨_, hc⟩
  let F := modulatedExponentialDecayTwist m I a f
  let χ := quasiCharacterUnitaryPart c
  have h := exists_schwartzBruhat_characterEquiv χ
  have hv : (h.choose F).val = fun x ↦ f.val x * c x := by
    funext x
    rw [show (h.choose F).val x = _ from h.choose_spec F x]
    change c x / (‖c x‖ : ℂ) * ((((m x).val : ℝ) ^ (a : ℝ) : ℝ) * f.val x) = _
    have hn : ((m x).val : ℝ) ^ (a : ℝ) = ‖c x‖ :=
      (norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2 c x).symm
    rw [hn, ← mul_assoc,
      div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit x).map c).ne_zero)),
      mul_comm]
  exact hv ▸ (h.choose F).property

private theorem deriv_quasiCharacter (b : LCATopologicalLie G) (c : QuasiCharacter G) (x : G) :
    bruhatDirectionalDeriv b c x =
      bruhatDiffQuasiCharacterSymbol (bruhatDiffGenerator b) c * c x := by
  change bruhatDirectionalDeriv b c x = bruhatDirectionalDeriv b c 1 * c x
  simp only [bruhatDirectionalDeriv, map_mul, one_mul, deriv_const_mul_field]
  exact mul_comm _ _

private theorem deriv_mul_quasiCharacter (b : LCATopologicalLie G) {f : G → ℂ}
    (hf : f ∈ bruhatSmoothSubmodule) (c : QuasiCharacter G) (x : G) :
    bruhatDirectionalDeriv b (fun y ↦ f y * c y) x =
      bruhatDirectionalDeriv b f x * c x +
        bruhatDiffQuasiCharacterSymbol (bruhatDiffGenerator b) c * (f x * c x) := by
  have h := ((hasDerivAt_bruhatDirectionalDeriv b ((mem_bruhatSmoothSubmodule_iff _).mp hf 1) x).fun_mul
    (hasDerivAt_bruhatDirectionalDeriv b ((mem_bruhatSmoothSubmodule_iff _).mp (quasiCharacter_mem_bruhatSmooth c) 1) x)).deriv
  change bruhatDirectionalDeriv b (fun y ↦ f y * c y) x = _ at h
  rw [h, deriv_quasiCharacter]
  simp only [ofAdd_zero, map_one, mul_one]
  ring

private def decayFirstOrder (hne : I.Nonempty) (b : LCATopologicalLie G)
    (f : modulatedExponentialDecaySubmodule m I) : modulatedExponentialDecaySubmodule m I :=
  let F := ⟨f.val, modulatedExponentialDecay_mem_bruhatSmooth m I hne f⟩
  ⟨(bruhatFirstOrder b F).val, bruhatFirstOrder_mem_modulatedExponentialDecay m I b F f.property⟩

/-- Integration by parts against a quasi-character follows by integrating the derivative
of the product, whose Fourier transform vanishes at the trivial character. -/
private theorem integral_decayFirstOrder (hne : I.Nonempty)
    (b : LCATopologicalLie G) (f : modulatedExponentialDecaySubmodule m I)
    {c : QuasiCharacter G} (hc : c ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I) :
    ∫ x, (decayFirstOrder m I hne b f).val x * c x ∂μ =
      -(bruhatDiffQuasiCharacterSymbol (bruhatDiffGenerator b) c *
        ∫ x, f.val x * c x ∂μ) := by
  let g : SchwartzBruhat G := ⟨_, quasiCharacter_mul_decay_mem_schwartz m I hm f hc⟩
  let f' := decayFirstOrder m I hne b f
  let g' : SchwartzBruhat G := ⟨_, quasiCharacter_mul_decay_mem_schwartz m I hm f' hc⟩
  let z := bruhatDiffQuasiCharacterSymbol (bruhatDiffGenerator b) c
  have hz : bruhatDiffSymbol (bruhatDiffGenerator b) (1 : PontryaginDual G) = 0 := by
    change bruhatDirectionalDeriv b (fun _ : G ↦ (1 : ℂ)) 1 = 0
    simp [bruhatDirectionalDeriv]
  obtain ⟨_, H, hH, hg, hHi, hF⟩ := lcaFourier_bruhatDiff μ (bruhatDiffGenerator b) g
  have hv (x : G) : H x = g' x + z * g x :=
    (congrFun hH x).trans (deriv_mul_quasiCharacter b (modulatedExponentialDecay_mem_bruhatSmooth m I hne f) c x)
  have hzero := congrFun hF 1
  rw [lcaFourier_one μ _ hHi, Pi.mul_apply, hz, zero_mul] at hzero
  simp_rw [hv] at hzero
  rw [integral_add ((schwartzBruhat_fourier_equiv μ).choose_spec g').1 (hg.const_mul z),
    integral_const_mul] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- On each Fréchet stage, Fatou's lemma gives lower semicontinuity of the L¹ seminorm.
Barrelledness then makes it continuous, so it is bounded on bounded Schwartz–Bruhat sets. -/
private theorem schwartzBruhat_L1_bounded {B : Set (SchwartzBruhat G)} (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, ∀ f ∈ B, ∫ x, ‖f x‖ ∂μ ≤ C := by
  have hi (f : SchwartzBruhat G) : Integrable (f : G → ℂ) μ :=
    ((schwartzBruhat_fourier_equiv μ).choose_spec f).1
  let L : schwartzBruhatSubmodule G →ₗ[ℂ] (G →₁[μ] ℂ) :=
    { toFun := fun f ↦ (hi f).toL1 f.val
      map_add' := fun f g ↦ Integrable.toL1_add f.val g.val (hi f) (hi g)
      map_smul' := fun z f ↦ Integrable.toL1_smul f.val (hi f) z }
  let p := (normSeminorm ℂ _).comp L
  have hp (f : SchwartzBruhat G) : p f = ∫ x, ‖f x‖ ∂μ := by
    change ‖(hi f).toL1 f.val‖ = _
    rw [Integrable.norm_toL1_eq_lintegral_eNorm, integral_norm_eq_lintegral_eNorm (hi f).aestronglyMeasurable]
  apply (schwartzBruhat_seminorm_bounded hB p ?_).imp
  · intro C h f hf
    exact hp f ▸ (h f hf).le
  intro a e
  let X := SchwartzBruhatStage e
  let i := schwartzBruhatStageInclusion a e
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  let _ : BarrelledSpace ℂ X := elementarySchwartz_barrelled
  let _ : MetrizableSpace X := elementarySchwartz_isFrechet.choose_spec.2.1
  apply (p.comp i).continuous_of_lowerSemicontinuous
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  apply IsSeqClosed.isClosed
  intro u f hu hf
  have hr : 0 ≤ r := (norm_nonneg (L (i (u 0)))).trans (hu 0)
  have hnorm (s : X) : ENNReal.ofReal (p (i s)) = eLpNorm (i s).val 1 μ := by
    rw [hp (i s), ofReal_integral_norm_eq_lintegral_eNorm (hi (i s)),
      eLpNorm_one_eq_lintegral_eNorm (hi (i s)).aestronglyMeasurable]
  apply (ENNReal.ofReal_le_ofReal_iff hr).mp
  change ENNReal.ofReal (p (i f)) ≤ _
  rw [hnorm]
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop (α := ℕ)) (f := fun n ↦ (i (u n)).val)
  · exact .of_forall fun n ↦ (hnorm _).symm ▸ ENNReal.ofReal_le_ofReal (hu n)
  · exact fun n ↦ (hi _).aestronglyMeasurable
  · exact (hi _).aestronglyMeasurable
  · exact .of_forall fun x ↦ (((continuous_schwartzBruhat_eval_forEndpoints x).comp
      (schwartzBruhatStage_isEmbedding a e).continuous).tendsto f).comp hf

private theorem bounded_image_of_intertwining {X Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (T : X → Y) (F : X → X) (L : Y →L[ℂ] Y)
    (heq : T ∘ F = L ∘ T) {B : Set X} (hB : IsVonNBounded ℂ (T '' B)) :
    IsVonNBounded ℂ (T '' (F '' B)) := by
  apply (hB.image L).subset
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨T x, ⟨x, hx, rfl⟩, (congrFun heq x).symm⟩

/-- Each twisted image of a differentiated bounded family is still Schwartz–Bruhat bounded. -/
private theorem bounded_twist_decayFirstOrder (hne : I.Nonempty) (b : LCATopologicalLie G)
    (B : Set (modulatedExponentialDecaySubmodule m I)) (a : I)
    (hB : IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B)) :
    IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' (decayFirstOrder m I hne b '' B)) := by
  have hweight := modulationWeight_firstOrder m b a
  let z := hweight.choose
  have hderiv := bruhatFirstOrder_schwartz b
  let A := hderiv.choose
  let L : SchwartzBruhat G →L[ℂ] SchwartzBruhat G := A - z • ContinuousLinearMap.id ℂ _
  let T := modulatedExponentialDecayTwist m I a
  have heq : T ∘ decayFirstOrder m I hne b = L ∘ T := by
    funext f
    apply Subtype.ext
    funext x
    change modulationWeight m a _ x = A (T f) x - z * T f x
    rw [hderiv.choose_spec]
    exact congrFun (hweight.choose_spec ⟨f.val, modulatedExponentialDecay_mem_bruhatSmooth m I hne f⟩) x
  exact bounded_image_of_intertwining T (decayFirstOrder m I hne b) L heq hB

/-- Inside the strip the absolute integral is dominated by the sum of the two endpoint
integrals, splitting according to whether the modulation is below or above one. -/
private theorem bounded_strip_integral (a b : I) (B : Set (modulatedExponentialDecaySubmodule m I))
    (hB : ∀ t : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I t '' B)) :
    ∃ C : ℝ, ∀ f ∈ B, ∀ c : QuasiCharacter G,
      quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c ∈ Icc (a : ℝ) b →
        ‖∫ x, f.val x * c x ∂μ‖ ≤ C := by
  let T := modulatedExponentialDecayTwist m I
  have ha := schwartzBruhat_L1_bounded μ (hB a)
  have hb := schwartzBruhat_L1_bounded μ (hB b)
  refine ⟨ha.choose + hb.choose, fun f hf c hs ↦ ?_⟩
  have hi (t : I) : Integrable (fun x ↦ ‖T t f x‖) μ :=
    ((schwartzBruhat_fourier_equiv μ).choose_spec (T t f)).1.norm
  have hpoint (x : G) : ‖f.val x * c x‖ ≤ ‖T a f x‖ + ‖T b f x‖ := by
    let r : ℝ := ((m x).val : ℝ)
    have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hnorm (t : I) : ‖T t f x‖ = ‖f.val x‖ * r ^ (t : ℝ) := by
      rw [show T t f x = _ from modulatedExponentialDecayTwist_apply m I t f x,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), mul_comm]
    rw [hnorm, hnorm, ← mul_add, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2 c x]
    rcases le_total r 1 with h | h
    · exact (Real.rpow_le_rpow_of_exponent_ge hr h hs.1).trans (le_add_of_nonneg_right (Real.rpow_nonneg hr.le _))
    · exact (Real.rpow_le_rpow_of_exponent_le h hs.2).trans (le_add_of_nonneg_left (Real.rpow_nonneg hr.le _))
  calc
    _ ≤ ∫ x, ‖T a f x‖ + ‖T b f x‖ ∂μ := norm_integral_le_of_norm_le ((hi a).add (hi b)) (.of_forall hpoint)
    _ = (∫ x, ‖T a f x‖ ∂μ) + ∫ x, ‖T b f x‖ ∂μ := integral_add (hi a) (hi b)
    _ ≤ _ := add_le_add (ha.choose_spec (T a f) ⟨f, hf, rfl⟩) (hb.choose_spec (T b f) ⟨f, hf, rfl⟩)

private theorem quasiSymbol_word_cons (b : LCATopologicalLie G) (w : List (LCATopologicalLie G))
    (c : QuasiCharacter G) :
    bruhatDiffQuasiCharacterSymbol (bruhatDiffWord (b :: w)) c =
      bruhatDiffQuasiCharacterSymbol (bruhatDiffWord w) c *
        bruhatDiffQuasiCharacterSymbol (bruhatDiffGenerator b) c := by
  let F : bruhatSmoothSubmodule (G := G) := ⟨_, quasiCharacter_mem_bruhatSmooth c⟩
  have hg : (bruhatDiffGenerator b).val F = bruhatDiffQuasiCharacterSymbol (bruhatDiffGenerator b) c • F :=
    Subtype.ext (funext (deriv_quasiCharacter b c))
  have hw : bruhatDiffWord (b :: w) = bruhatDiffWord w * bruhatDiffGenerator b := by
    simp [bruhatDiffWord, List.reverse_cons, List.prod_append]
  rw [hw]
  change ((bruhatDiffWord w).val ((bruhatDiffGenerator b).val F)).val 1 = _
  rw [hg, map_smul]
  exact mul_comm _ _

private theorem bounded_word_mellin_integral (hne : I.Nonempty) (a b : I) (w : List (LCATopologicalLie G))
    (B : Set (modulatedExponentialDecaySubmodule m I))
    (hB : ∀ t : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I t '' B)) :
    ∃ C : ℝ, ∀ f ∈ B, ∀ c ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I,
      quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c ∈ Icc (a : ℝ) b →
        ‖bruhatDiffQuasiCharacterSymbol (bruhatDiffWord w) c * ∫ x, f.val x * c x ∂μ‖ ≤ C := by
  induction w generalizing B with
  | nil =>
    obtain ⟨C, hC⟩ := bounded_strip_integral m I hm μ a b B hB
    refine ⟨C, fun f hf c _ hs ↦ ?_⟩
    simpa [bruhatDiffQuasiCharacterSymbol, bruhatDiffWord] using hC f hf c hs
  | cons d w ih =>
    let T := decayFirstOrder m I hne d
    obtain ⟨C, hC⟩ := ih (T '' B) (fun t ↦ bounded_twist_decayFirstOrder m I hne d B t (hB t))
    refine ⟨C, fun f hf c hc hs ↦ ?_⟩
    have h := hC (T f) ⟨f, hf, rfl⟩ c hc hs
    rw [show (∫ x, (T f).val x * c x ∂μ) = _ from integral_decayFirstOrder m I hm μ hne d f hc,
      mul_neg, norm_neg, ← mul_assoc, ← quasiSymbol_word_cons] at h
    exact h

/-- A differential operator involves finitely many words, even when the space of
one-parameter subgroups has no finite basis. -/
private theorem bounded_operator_mellin_integral (hne : I.Nonempty) (a b : I) (D : bruhatDiffAlgebra G)
    (B : Set (modulatedExponentialDecaySubmodule m I))
    (hB : ∀ t : I, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I t '' B)) :
    ∃ C : ℝ, ∀ f ∈ B, ∀ c ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I,
      quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c ∈ Icc (a : ℝ) b →
        ‖bruhatDiffQuasiCharacterSymbol D c * ∫ x, f.val x * c x ∂μ‖ ≤ C := by
  classical
  obtain ⟨d, hd⟩ := bruhatDiff_exists_presentation D
  choose C hC using fun w ↦ bounded_word_mellin_integral m I hm μ hne a b w B hB
  refine ⟨∑ w ∈ d.support, ‖d w‖ * C w, fun f hf c hc hs ↦ ?_⟩
  let σ : bruhatDiffAlgebra G →ₗ[ℂ] ℂ :=
    { toFun := (bruhatDiffQuasiCharacterSymbol · c)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hsum : bruhatDiffQuasiCharacterSymbol D c =
      ∑ w ∈ d.support, d w * bruhatDiffQuasiCharacterSymbol (bruhatDiffWord w) c := by
    change σ D = _
    rw [← hd, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun w _ ↦ σ.map_smul _ _
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ ↦ ?_)
  rw [mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC w f hf c hc hs) (norm_nonneg _)

/-- Each twist is continuous on every compact-quotient stage, hence on the final decay space. -/
private theorem isVonNBounded_twist {B : Set (ModulatedExponentialDecay m I)}
    (hB : IsVonNBounded ℂ B) (a : I) :
    IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B) := by
  let T : ModulatedExponentialDecay m I →ₗ[ℂ] SchwartzBruhat G := modulatedExponentialDecayTwist m I a
  suffices hT : Continuous T from hB.image (⟨T, hT⟩ : _ →L[ℂ] _)
  let P := {q : Seminorm ℂ (modulatedExponentialDecaySubmodule m I) //
    ∀ k, Continuous (q ∘ modulatedExponentialDecayStageInclusion m I k)}
  refine (PolynormableSpace.withSeminorms ℂ (SchwartzBruhat G)).continuous_of_continuous_comp T fun p ↦
    (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm (⟨p.val.comp T, ?_⟩ : P)
  intro k
  have h := continuous_schwartzBruhat_compactQuotient_pullback k.val k.property.1
  have hc := (continuous_apply a).comp (modulatedDecayStage_twists_isInducing m I k).continuous
  exact p.property.comp ((h.choose.continuous.comp hc).congr (fun f ↦ Subtype.ext (funext (h.choose_spec _))))

end StripEstimates

-- TODO(paper-gap): The proof of D.3.4.2 starts with a finite basis of the
-- space of one-parameter subgroups. For ℝ_{>0} × 𝕋^ℕ that space is infinite-dimensional.

include hSC hBorel hms in
/-- Paper: Theorem D.3.4.2, p. 816. On a component of the open strip, the
Fourier–Mellin transform of a bounded family in the closed-interval decay space
is bounded by a constant divided by the norm of the symbol above a positive threshold.
The threshold may depend on the component. -/
theorem modulatedFourierMellin_uniform_riemannLebesgue (hInt : OrdConnected I)
    (hne : I.Nonempty) (hOpen : IsOpen I) (hBound : IsBounded I)
    (μ : Measure G) [μ.IsHaarMeasure] (D : bruhatDiffAlgebra G)
    (B : Set (ModulatedExponentialDecay m (closure I))) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ ω₀ : PontryaginDual m.toMonoidHom.ker,
      ∃ M : ℝ, 0 < M ∧
        ∀ f ∈ B, ∀ c ∈ componentVerticalStrip m.toMonoidHom hm.1 hm.2 ω₀ I,
          M ≤ ‖bruhatDiffQuasiCharacterSymbol D c‖ →
          ‖modulatedFourierMellin m I hm μ f.val c‖ ≤
            C / ‖bruhatDiffQuasiCharacterSymbol D c‖ := by
  have htw := isVonNBounded_twist m (closure I) hB
  obtain ⟨hl, hu⟩ := isBounded_iff_bddBelow_bddAbove.mp hBound
  let a : closure I := ⟨sInf I, csInf_mem_closure hne hl⟩
  let b : closure I := ⟨sSup I, csSup_mem_closure hne hu⟩
  have hC := bounded_operator_mellin_integral m (closure I) hm μ hne.closure a b D B htw
  refine ⟨max 1 hC.choose, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun _ ↦ ⟨1, zero_lt_one, ?_⟩⟩
  intro f hf c hc hnorm
  have hs : quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c ∈ I := hc.1
  rw [modulatedFourierMellin, indicator_of_mem hc.1]
  apply (le_div_iff₀ (zero_lt_one.trans_le hnorm)).mpr
  rw [mul_comm, ← norm_mul]
  exact (hC.choose_spec f hf c (subset_closure hs) ⟨csInf_le hl hs, le_csSup hu hs⟩).trans (le_max_right _ _)

end RiemannLebesgue

section PoissonSummation

local notation "K" => m.toMonoidHom.ker

open Classical in
/-- Paper: (D.3.5.2), p. 818. In the coordinates of the chosen section, the
replacement equals the original function off the designated fibres and the
arithmetic mean of the two one-sided limits on them. -/
def modulatedJumpMidpointProfile (τ : ℝ≥0ˣ →ₜ* G) (f : G → ℂ) (S : Finset ℝ≥0ˣ)
    (hleft : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[<] t.val) (𝓝 a))
    (hright : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[>] t.val) (𝓝 a))
    (t : ℝ≥0ˣ) (g : K) : ℂ :=
  if ht : t ∈ S then ((hleft ⟨t, ht⟩ g).choose + (hright ⟨t, ht⟩ g).choose) / 2
  else f (τ t * g.val)

/-- Paper: (D.3.5.2), p. 818. The replacement at a designated fibre is the
midpoint of its given left and right limits. -/
theorem modulatedJumpMidpointProfile_eq_average (τ : ℝ≥0ˣ →ₜ* G) (f : G → ℂ)
    (S : Finset ℝ≥0ˣ)
    (hleft : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[<] t.val) (𝓝 a))
    (hright : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[>] t.val) (𝓝 a))
    (t : S) (g : K) (a b : ℂ)
    (ha : Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[<] t.val) (𝓝 a))
    (hb : Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[>] t.val) (𝓝 b)) :
    modulatedJumpMidpointProfile m τ f S hleft hright t.val g = (a + b) / 2 := by
  unfold modulatedJumpMidpointProfile
  rw [dif_pos t.property]
  let e : ℝ≥0ˣ ≃ₜ Set.Ioi (0 : ℝ) := Nonneg.unitsHomeomorphPos ℝ
  have : OrderTopology ℝ≥0ˣ := ⟨e.isInducing.eq_induced.trans
    ((show StrictMono e from fun _ _ h ↦ h).induced_topology_eq_preorder
      (e.surjective.range_eq ▸ Set.ordConnected_univ))⟩
  have h1 := tendsto_nhds_unique (hleft t g).choose_spec ha
  have h2 := tendsto_nhds_unique (hright t g).choose_spec hb
  rw [h1, h2]

-- TODO(paper-gap): Proposition D.3.5.1, (D.3.5.3), reverses the Fourier sign.
-- For γ = e, χ₀ = 1, and a bump in log coordinates supported in (1/8, 3/8)
-- with value 1 at 1/4, the left side at x = exp(1/4) is 1 and the right side
-- samples the periodization at -1/4, where it is 0. The t₀ shift is also spurious.
-- The reference to B.4.1.2 omits that proposition's derivative hypotheses.
-- TODO(paper-gap): The second equality of (D.3.5.5) is missing the factor
-- given by the log-coordinate integral.

/-- Paper: (D.3.5.4), p. 819. A unitary value at the lattice generator has a
unique phase in the half-open interval of length two pi divided by its log-module. -/
theorem existsUnique_modulatedCharacterPhase (γ : G) (hγ : 1 < (m γ).val)
    (χ : PontryaginDual G) :
    let L := Real.log ((m γ).val : ℝ)
    ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = χ γ := by
  intro L
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Circle.exp θ = χ γ := ⟨_, Circle.exp_arg _⟩
  have h (t : ℝ) : (t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = χ γ) ↔
      t = toIcoMod Real.two_pi_pos 0 θ / L := by
    rw [eq_div_iff hL.ne', eq_comm (b := toIcoMod _ _ _), toIcoMod_eq_iff, zero_add, ← hθ,
      eq_comm (a := Circle.exp (t * L)), Circle.exp_eq_exp, mem_Ico, mem_Ico, lt_div_iff₀ hL,
      mul_nonneg_iff_of_pos_right hL]
    simp only [zsmul_eq_mul]
  exact ⟨_, (h _).2 rfl, fun t ht ↦ (h t).1 ht⟩

/-- Paper: Remark D.3.5.2, p. 818. The cyclic subgroup generated by an element
of module greater than one is discrete, hence closed in the Hausdorff group. -/
theorem modulated_zpowers_discrete (γ : G) (hγ : 1 < (m γ).val) :
    DiscreteTopology (Subgroup.zpowers γ) := by
  have hL : 0 < Real.log ((m γ).val : ℝ) := Real.log_pos (by exact_mod_cast hγ)
  have hlog (k : ℤ) : Real.log ((m (γ ^ k)).val : ℝ) = k * Real.log ((m γ).val : ℝ) := by
    rw [map_zpow, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Real.log_zpow]
  have hcont : Continuous fun x : Subgroup.zpowers γ ↦ Real.log ((m x.val).val : ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (m.continuous.comp continuous_subtype_val))).log
      fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  refine discreteTopology_iff_isOpen_singleton_one.2 ?_
  convert (isOpen_Ioo (a := -Real.log ((m γ).val : ℝ))
    (b := Real.log ((m γ).val : ℝ))).preimage hcont
  ext ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  simp only [mem_singleton_iff, mem_preimage, mem_Ioo, hlog]
  constructor
  · intro h
    have hγk : γ ^ k = 1 := congrArg Subtype.val h
    have hk : (k : ℝ) * Real.log ((m γ).val : ℝ) = 0 := by
      rw [← hlog, hγk]
      simp
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    have h₁' : (-1 : ℝ) < k := by nlinarith
    have h₂' : (k : ℝ) < 1 := by nlinarith
    have hk : -1 < k ∧ k < 1 := by exact_mod_cast And.intro h₁' h₂'
    have hk0 : k = 0 := by omega
    exact Subtype.ext (by simp [hk0])

variable (hm : IsModulation m) (hms : Surjective m)

include hm hms in
/-- Paper: Remark D.3.5.2, p. 818. After choosing a unitary lift for each
norm-one character, a phase correction and an integer frequency parametrize
exactly the unitary characters that are trivial on the cyclic subgroup. -/
theorem modulatedCharacter_zpowers_annihilator (γ : G) (hγ : 1 < (m γ).val)
    (χ : PontryaginDual K → PontryaginDual G)
    (hχ : ∀ (ω₀ : PontryaginDual K) (g : K), χ ω₀ g.val = ω₀ g)
    (t : PontryaginDual K → ℝ)
    (ht : let L := Real.log ((m γ).val : ℝ)
      ∀ ω₀, t ω₀ ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t ω₀ * L) = χ ω₀ γ) :
    let L := Real.log ((m γ).val : ℝ)
    ∃ e : (PontryaginDual K × ℤ) ≃ lcaAnnihilator (Subgroup.zpowers γ),
      ∀ ω₀ n x, (e (ω₀, n)).val x =
        χ ω₀ x * Circle.exp
          ((2 * Real.pi * (n : ℝ) / L - t ω₀) * Real.log ((m x).val : ℝ)) := by
  intro L
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  let q : G →ₜ* Multiplicative ℝ :=
    ⟨positiveRealLogEquiv.toMulEquiv.toMonoidHom.comp m.toMonoidHom,
      positiveRealLogEquiv.continuous.comp m.continuous⟩
  have hq : IsQuotientMap q := positiveRealLogEquiv.toHomeomorph.isQuotientMap.comp
    (hm.1.isClosedMap.isQuotientMap m.continuous hms)
  obtain ⟨A, hA⟩ := exists_realPontryaginDualEquiv
  let phase (r : ℝ) : PontryaginDual G :=
    (A (Multiplicative.ofAdd (r / (2 * Real.pi)))).comp q
  have hp (r : ℝ) (x : G) : phase r x = Circle.exp (r * Real.log ((m x).val : ℝ)) := by
    change A _ (Multiplicative.ofAdd (q x).toAdd) = _
    rw [hA, show (q x).toAdd = _ from positiveRealLogEquiv_apply (m x)]
    congr 1
    field_simp
  have hpInj : Injective phase := by
    intro r s h
    have he : A (Multiplicative.ofAdd (r / (2 * Real.pi))) =
        A (Multiplicative.ofAdd (s / (2 * Real.pi))) := by
      apply PontryaginDual.ext
      intro y
      obtain ⟨x, rfl⟩ := hq.surjective y
      exact DFunLike.congr_fun h x
    exact (div_left_inj₀ Real.two_pi_pos.ne').mp
      (congrArg Multiplicative.toAdd (A.injective he))
  let restrictChar (ψ : PontryaginDual G) : PontryaginDual K := ψ.comp ⟨Subgroup.subtype K, continuous_subtype_val⟩
  let r (u : PontryaginDual K) (n : ℤ) := 2 * Real.pi * (n : ℝ) / L - t u
  let F (p : PontryaginDual K × ℤ) := χ p.1 * phase (r p.1 p.2)
  have hres (u : PontryaginDual K) (n : ℤ) : restrictChar (F (u, n)) = u := by
    apply PontryaginDual.ext
    intro x
    change χ u x.val * phase _ x.val = _
    rw [hp, show m x.val = 1 from x.property, hχ]
    simp
  have hgen (u : PontryaginDual K) (n : ℤ) : F (u, n) γ = 1 := by
    change χ u γ * phase _ γ = 1
    rw [hp, ← (ht u).2, ← Circle.exp_add]
    apply Circle.exp_eq_one.mpr
    exact ⟨n, by change t u * L + (2 * Real.pi * n / L - t u) * L = _; field_simp; ring⟩
  let f (p : PontryaginDual K × ℤ) : lcaAnnihilator (Subgroup.zpowers γ) :=
    ⟨F p, (mem_lcaAnnihilator_iff _ _).2 fun x ↦
      (Subgroup.zpowers_le.mpr (show γ ∈ (F p).toMonoidHom.ker from hgen p.1 p.2)) x.property⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, fun u n x ↦ congrArg (χ u x * ·) (hp _ x)⟩
  · rintro ⟨u, n⟩ ⟨v, j⟩ h
    have hf := congrArg Subtype.val h
    have huv := congrArg restrictChar hf
    change restrictChar (F (u, n)) = restrictChar (F (v, j)) at huv
    rw [hres, hres] at huv
    subst v
    have hr := hpInj (mul_left_cancel (show χ u * phase (r u n) = χ u * phase (r u j) from hf))
    have hn : (n : ℝ) = j := by
      change 2 * Real.pi * n / L - t u = 2 * Real.pi * j / L - t u at hr
      exact mul_left_cancel₀ Real.two_pi_pos.ne' ((div_left_inj₀ hL.ne').mp (sub_left_inj.mp hr))
    exact congrArg (u, ·) (by exact_mod_cast hn : n = j)
  · intro ψ
    let u := restrictChar ψ.val
    let δ := ψ.val / χ u
    -- The residual character factors continuously through the log of the modulation.
    have hker : q.toMonoidHom.ker ≤ δ.toMonoidHom.ker := by
      intro x hx
      have hx' : x ∈ K := positiveRealLogEquiv.injective
        ((show positiveRealLogEquiv (m x) = 1 from hx).trans (map_one _).symm)
      change ψ.val x / χ u x = 1
      rw [hχ u ⟨x, hx'⟩]
      exact div_self' _
    let Q := QuotientGroup.liftEquiv q.toMonoidHom.ker hq.surjective rfl
    let d := (QuotientGroup.lift q.toMonoidHom.ker δ.toMonoidHom hker).comp Q.symm.toMonoidHom
    have hd (x : G) : d (q x) = δ x := by
      change QuotientGroup.lift _ _ hker (Q.symm (Q (QuotientGroup.mk x))) = _
      rw [Q.symm_apply_apply]
      rfl
    let d' : PontryaginDual (Multiplicative ℝ) :=
      ⟨d, hq.continuous_iff.mpr (δ.continuous.congr fun x ↦ (hd x).symm)⟩
    obtain ⟨s, hs⟩ := A.surjective d'
    let a := 2 * Real.pi * s.toAdd
    have hδ : phase a = δ := by
      apply PontryaginDual.ext
      intro x
      change A (Multiplicative.ofAdd (a / (2 * Real.pi))) (q x) = _
      rw [show Multiplicative.ofAdd (a / (2 * Real.pi)) = s by
        change 2 * Real.pi * s.toAdd / (2 * Real.pi) = s.toAdd
        field_simp, hs]
      exact hd x
    have hψ : χ u * phase a = ψ.val := by simp [hδ, δ]
    have hγψ := (mem_lcaAnnihilator_iff _ _).1 ψ.property ⟨γ, Subgroup.mem_zpowers γ⟩
    have he : Circle.exp (t u * L + a * L) = 1 := by
      rw [Circle.exp_add, (ht u).2, ← hp]
      exact (DFunLike.congr_fun hψ γ).trans hγψ
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp he
    have hr : r u n = a := by
      change 2 * Real.pi * n / L - t u = a
      apply (sub_eq_iff_eq_add).mpr
      apply (div_eq_iff hL.ne').mpr
      linarith only [hn, mul_comm (n : ℝ) (2 * Real.pi), add_mul a (t u) L]
    exact ⟨(u, n), Subtype.ext (show χ u * phase (r u n) = ψ.val by rw [hr, hψ])⟩

end PoissonSummation

section CompactSupport

/-- Paper: Lemma D.3.6.1, p. 819. The test function submodule consists of
Bruhat smooth functions with compact support. -/
def bruhatCompactSupportSubmodule (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {f | f ∈ bruhatSmoothSubmodule ∧ HasCompactSupport f}
  zero_mem' := ⟨Submodule.zero_mem _, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨Submodule.add_mem _ hf.1 hg.1, hf.2.add hg.2⟩
  smul_mem' z _ hf := ⟨Submodule.smul_mem _ z hf.1, hf.2.smul_left⟩

/-- Paper: Lemma D.3.6.1, p. 819. For the additive real group the test
function submodule consists of ordinary smooth compactly supported functions.
Deviation: Sanity check in the real-line model. -/
theorem mem_bruhatCompactSupportSubmodule_real_iff (f : Multiplicative ℝ → ℂ) :
    f ∈ bruhatCompactSupportSubmodule (Multiplicative ℝ) ↔
      ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) ∧ HasCompactSupport (f ∘ Multiplicative.ofAdd) := by
  have hsm : f ∈ bruhatSmoothSubmodule ↔ ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) := by
    rw [mem_bruhatSmoothSubmodule_iff, contDiff_infty]
    exact forall_congr' fun p ↦ isBruhatContDiff_real_iff p f
  have hcs : HasCompactSupport f ↔ HasCompactSupport (f ∘ Multiplicative.ofAdd) :=
    ⟨fun h ↦ h.comp_homeomorph (Homeomorph.ofAdd (X := ℝ)), fun h ↦ by
      simpa [Function.comp_def] using h.comp_homeomorph (Homeomorph.ofAdd (X := ℝ)).symm⟩
  exact and_congr hsm hcs

/-- Paper: Lemma D.3.6.1, p. 819. A fixed-support stage consists of
Schwartz functions on an elementary quotient whose realizations vanish
off the designated compact set. It carries the induced Schwartz topology. -/
def bruhatCompactSupportStage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) :
    Submodule ℂ (SchwartzBruhatStage e) :=
  ⨅ x : {x : G // x ∉ (C : Set G)}, LinearMap.ker
    ((LinearMap.proj x.val).comp (schwartzBruhatStageRealization a e))

include hT2 in
/-- Paper: Lemma D.3.6.1, p. 819. An element of an elementary Schwartz
stage belongs to the fixed-support submodule exactly when the topological
support of its realization is contained in the designated compact set. -/
theorem mem_bruhatCompactSupportStage_iff (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) (f : SchwartzBruhatStage e) :
    f ∈ bruhatCompactSupportStage a e C ↔
      tsupport (schwartzBruhatStageRealization a e f) ⊆ (C : Set G) := by
  simp only [bruhatCompactSupportStage, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, Subtype.forall]
  constructor
  · intro h
    refine closure_minimal (fun x hx ↦ ?_) C.isCompact.isClosed
    by_contra hxC
    exact hx (h x hxC)
  · intro h x hx
    by_contra hne
    exact hx (h (subset_tsupport _ hne))

/-- Paper: Lemma D.3.6.1, p. 819. A function from a fixed-support
elementary stage realizes to a smooth compactly supported function on the group. -/
theorem bruhatCompactSupportStage_realization_mem (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G)
    (f : bruhatCompactSupportStage a e C) :
    schwartzBruhatStageRealization a e f.val ∈ bruhatCompactSupportSubmodule G := by
  refine ⟨?_, C.isCompact.of_isClosed_subset isClosed_closure
    ((mem_bruhatCompactSupportStage_iff a e C f.val).1 f.property)⟩
  rw [mem_bruhatSmoothSubmodule_iff]
  exact schwartzBruhat_isBruhatSmooth
    (show SchwartzBruhat G from schwartzBruhatStageInclusion a e f.val)

/-- Paper: Lemma D.3.6.1, p. 819. The stage inclusion is the Schwartz
realization by pullback and extension by zero, with values in the test space. -/
def bruhatCompactSupportStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) :
    bruhatCompactSupportStage a e C →ₗ[ℂ] bruhatCompactSupportSubmodule G :=
  ((schwartzBruhatStageRealization a e).domRestrict (bruhatCompactSupportStage a e C)).codRestrict
    (bruhatCompactSupportSubmodule G) (bruhatCompactSupportStage_realization_mem a e C)

/-- Paper: Lemma D.3.6.1, p. 819. A test function from a fixed-support stage
has the values of its Schwartz realization on the group. -/
theorem bruhatCompactSupportStageInclusion_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G)
    (f : bruhatCompactSupportStage a e C) (x : G) :
    (bruhatCompactSupportStageInclusion a e C f).val x =
      schwartzBruhatStageRealization a e f.val x := rfl

/-- Paper: Lemma D.3.6.1, p. 819. The topology of the test function space
is final locally convex for the fixed-support stage inclusions.
Deviation: We use all compact supports and elementary quotient stages
in place of choosing a cofinal countable presentation.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its seminorm family (#5398). -/
def BruhatCompactSupport (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] :=
  WithGeneratingSeminorms (bruhatCompactSupportSubmodule G)
    (Subtype.val : {p : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) (C : Compacts G),
        Continuous (p ∘ bruhatCompactSupportStageInclusion a e C)} → _)

namespace BruhatCompactSupport

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H]

instance instAddCommGroup : AddCommGroup (BruhatCompactSupport H) :=
  inferInstanceAs (AddCommGroup (WithGeneratingSeminorms
    (bruhatCompactSupportSubmodule H) _))

instance instModule : Module ℂ (BruhatCompactSupport H) :=
  inferInstanceAs (Module ℂ (WithGeneratingSeminorms
    (bruhatCompactSupportSubmodule H) _))

instance instTopologicalSpace : TopologicalSpace (BruhatCompactSupport H) :=
  inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms
    (bruhatCompactSupportSubmodule H) _))

instance instPolynormableSpace : PolynormableSpace ℂ (BruhatCompactSupport H) :=
  inferInstanceAs (PolynormableSpace ℂ (WithGeneratingSeminorms
    (bruhatCompactSupportSubmodule H) _))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (BruhatCompactSupport H) :=
  inferInstanceAs (IsTopologicalAddGroup (WithGeneratingSeminorms
    (bruhatCompactSupportSubmodule H) _))

instance instUniformSpace : UniformSpace (BruhatCompactSupport H) :=
  inferInstanceAs (UniformSpace (WithGeneratingSeminorms
    (bruhatCompactSupportSubmodule H) _))

instance instIsUniformAddGroup : IsUniformAddGroup (BruhatCompactSupport H) :=
  inferInstanceAs (IsUniformAddGroup (WithGeneratingSeminorms
    (bruhatCompactSupportSubmodule H) _))

end BruhatCompactSupport

section RealTestTopology

open scoped SchwartzMap

local notation "R" => Multiplicative ℝ
local notation "D" => 𝓓((⊤ : Opens ℝ), ℂ)
local notation "B" => BruhatCompactSupport R

/-- The fixed-support smooth topology is induced from the Schwartz topology. -/
private theorem fixedSupport_realSchwartz_isInducing (K : Compacts ℝ) :
    IsInducing (supportedToSchwartzCLM ℂ K : 𝓓_{K}(ℝ, ℂ) → 𝓢(ℝ, ℂ)) := by
  let J := (supportedToSchwartzCLM ℂ K : 𝓓_{K}(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  refine ⟨le_antisymm J.continuous.le_induced (continuous_id_iff_le.mp ?_)⟩
  exact (J.toLinearMap.withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ)).continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ ⊤ K) LinearMap.id (.of_real fun i ↦ by
      refine ⟨{(0, i)}, 1, fun f ↦ ?_⟩
      rw [Finset.sup_singleton, one_mul]
      exact (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg _ _) i f).mpr
        fun x _ ↦ (J f).norm_iteratedFDeriv_le_seminorm ℂ i x)

open scoped ComplexOrder in
private theorem polynormableSpace_realTests : PolynormableSpace ℂ D := by
  let L : D →L[ℂ] D := TestFunction.postcompCLM (Complex.I • ContinuousLinearMap.id ℂ ℂ)
  have h : Continuous (fun z : ℂ × D ↦ z.1.re • z.2 + z.1.im • L z.2) :=
    ((Complex.continuous_re.comp continuous_fst).smul continuous_snd).add
      ((Complex.continuous_im.comp continuous_fst).smul (L.continuous.comp continuous_snd))
  let : ContinuousSMul ℂ D := ⟨h.congr fun z ↦ TestFunction.ext fun x ↦ by
    change (z.1.re : ℂ) * z.2 x + (z.1.im : ℂ) * (Complex.I * z.2 x) = z.1 * z.2 x
    rw [← mul_assoc, ← add_mul, Complex.re_add_im]⟩
  let : LocallyConvexSpace ℂ D := .ofBasisZero ℂ D _ _ (LocallyConvexSpace.convex_basis_zero ℝ D)
    (fun _ hs ↦ convex_of_nonneg_surjective_algebraMap ℂ
      (fun _ hz ↦ RCLike.nonneg_iff_exists_ofReal.mp hz) hs.2)
  infer_instance

private def realTestsLinearEquiv : B ≃ₗ[ℂ] D where
  toFun f := ⟨f.val ∘ Multiplicative.ofAdd, ((mem_bruhatCompactSupportSubmodule_real_iff _).1 f.property).1,
    ((mem_bruhatCompactSupportSubmodule_real_iff _).1 f.property).2, subset_univ _⟩
  invFun f := ⟨fun x ↦ f x.toAdd, (mem_bruhatCompactSupportSubmodule_real_iff _).2
    ⟨f.contDiff, f.hasCompactSupport⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem realTests_stage_continuous (a : BruhatStructuralPair R)
    (d : ElementaryLCAPresentation a.quotient) (C : Compacts R)
    (S : 𝓢(ℝ, ℂ) ≃L[ℂ] SchwartzBruhat R) (hS : ∀ f x, S f x = f x.toAdd) :
    Continuous (realTestsLinearEquiv ∘ bruhatCompactSupportStageInclusion a d C) := by
  let X := bruhatCompactSupportStage a d C
  let J : SchwartzBruhatStage d →L[ℂ] SchwartzBruhat R :=
    ⟨schwartzBruhatStageInclusion a d, (schwartzBruhatStage_isEmbedding a d).continuous⟩
  let P : X →L[ℂ] 𝓢(ℝ, ℂ) := S.symm.toContinuousLinearMap.comp (J.comp X.subtypeL)
  have hP (f : X) (x : ℝ) : P f x = schwartzBruhatStageRealization a d f.val (Multiplicative.ofAdd x) :=
    (hS (P f) (Multiplicative.ofAdd x)).symm.trans <|
      congrArg (fun F : SchwartzBruhat R ↦ F (Multiplicative.ofAdd x)) (S.apply_symm_apply (J f.val))
  let K : Compacts ℝ := C
  let lift (f : X) : 𝓓_{K}(ℝ, ℂ) := ⟨P f, (P f).smooth _, fun x hx ↦ (hP f x).trans <|
    image_eq_zero_of_notMem_tsupport fun h ↦ hx ((mem_bruhatCompactSupportStage_iff a d C _).1 f.property h)⟩
  have hLift : Continuous lift := (fixedSupport_realSchwartz_isInducing K).continuous_iff.mpr P.continuous
  exact ((TestFunction.continuous_ofSupportedIn (Ω := (⊤ : Opens ℝ)) (subset_univ (K : Set ℝ))).comp hLift).congr
    (fun f ↦ TestFunction.ext (hP f))

private theorem realTests_from_fixedSupport (S : 𝓢(ℝ, ℂ) ≃L[ℂ] SchwartzBruhat R)
    (hS : ∀ f x, S f x = f x.toAdd) (a : BruhatStructuralPair R)
    (ha : ∀ b, b ≤ a) (d : ElementaryLCAPresentation a.quotient) (K : Compacts ℝ)
    (hK : (K : Set ℝ) ⊆ (⊤ : Opens ℝ)) :
    Continuous (realTestsLinearEquiv.symm ∘ TestFunction.ofSupportedIn hK) := by
  let J : SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhat R := schwartzBruhatStageInclusion a d
  have hJ := schwartzBruhatStage_isEmbedding a d
  have hsur := schwartzBruhat_maxStage_surjective a ha d
  let e := ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective J ⟨hJ.injective, hsur⟩)
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hJ, hsur⟩)
  let P : 𝓓_{K}(ℝ, ℂ) →L[ℂ] SchwartzBruhatStage d :=
    e.symm.toContinuousLinearMap.comp (S.toContinuousLinearMap.comp (supportedToSchwartzCLM ℂ K))
  have hP (f : 𝓓_{K}(ℝ, ℂ)) (x : R) : schwartzBruhatStageRealization a d (P f) x = f x.toAdd :=
    (congrArg (fun F : SchwartzBruhat R ↦ F x) (e.apply_symm_apply (S (supportedToSchwartzCLM ℂ K f)))).trans
      (hS _ x)
  let C : Compacts R := K
  have hmem (f : 𝓓_{K}(ℝ, ℂ)) : P f ∈ bruhatCompactSupportStage a d C := by
    apply (mem_bruhatCompactSupportStage_iff a d C _).mpr
    apply closure_minimal _ C.isCompact.isClosed
    intro x hx
    by_contra h
    exact hx ((hP f x).trans (f.zero_on_compl h))
  let lift (f : 𝓓_{K}(ℝ, ℂ)) : bruhatCompactSupportStage a d C := ⟨P f, hmem f⟩
  have hLift : Continuous lift := P.continuous.subtype_mk _
  let j : bruhatCompactSupportStage a d C →ₗ[ℂ] B := bruhatCompactSupportStageInclusion a d C
  have hj : Continuous j := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp j
    fun p ↦ p.property a d C
  exact (hj.comp hLift).congr fun f ↦ Subtype.ext (funext (hP f))

/-- Paper: Lemma D.3.6.1, p. 819. The test space topology recovers the
usual Mathlib topology of smooth compactly supported functions on the real line.
Deviation: Sanity check in the real-line model. -/
theorem bruhatCompactSupport_real_equiv :
    ∃ e : BruhatCompactSupport (Multiplicative ℝ) ≃L[ℂ] 𝓓((⊤ : Opens ℝ), ℂ),
      ∀ f x, e f x = f.val (Multiplicative.ofAdd x) := by
  let : SecondCountableTopology R := inferInstanceAs (SecondCountableTopology ℝ)
  let c := ContinuousMulEquiv.refl R
  have hreal := schwartzBruhat_realCoordinate_equiv c
  let S := hreal.choose
  have hS (f : 𝓢(ℝ, ℂ)) (x : R) : S f x = f x.toAdd := hreal.choose_spec f x
  let : PolynormableSpace ℂ D := polynormableSpace_realTests
  let Seminorms := {p : Seminorm ℂ (bruhatCompactSupportSubmodule R) //
    ∀ (a : BruhatStructuralPair R) (d : ElementaryLCAPresentation a.quotient) (C : Compacts R),
      Continuous (p ∘ bruhatCompactSupportStageInclusion a d C)}
  have gen := withGeneratingSeminorms_spec _ (Subtype.val : Seminorms → _)
  have hforward : Continuous realTestsLinearEquiv := by
    refine (PolynormableSpace.withSeminorms ℂ D).continuous_of_continuous_comp realTestsLinearEquiv.toLinearMap
      fun p ↦ gen.continuous_seminorm (⟨p.val.comp realTestsLinearEquiv.toLinearMap, ?_⟩ : Seminorms)
    exact fun a d C ↦ p.property.comp (realTests_stage_continuous a d C S hS)
  let : Module ℝ B := Module.restrictScalars ℝ ℂ B
  let : IsScalarTower ℝ ℂ B := IsScalarTower.restrictScalars ℝ ℂ B
  let : ContinuousSMul ℂ B := gen.continuousSMul
  let : ContinuousSMul ℝ B := IsScalarTower.continuousSMul ℂ
  let : LocallyConvexSpace ℝ B := gen.toLocallyConvexSpace
  have hback : Continuous realTestsLinearEquiv.symm := by
    refine (TestFunction.continuous_iff_continuous_comp realTestsLinearEquiv.symm.toLinearMap).mpr ?_
    let line := (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
    have hp := realCoordinate_bruhatPresentation.{0, 0} c line
    exact realTests_from_fixedSupport S hS hp.choose hp.choose_spec.1 (Classical.choice hp.choose.elementary)
  exact ⟨⟨realTestsLinearEquiv, hforward, hback⟩, fun _ _ ↦ rfl⟩

end RealTestTopology

open scoped ENNReal

section ElementaryDescent
variable {m n r m' n' r' : ℕ} {F F' : Type*}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F']

/-- On a neighborhood of the origin the elementary cover is injective. -/
private theorem elementaryCoverZeroHom_injOn_nhds :
    ∃ W ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      InjOn (elementaryCoverZeroHom (r := r) (F := F)) W := by
  let W := ⋂ i : Fin n, (fun v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) ↦ v.2 i) ⁻¹'
    Ioo (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)
  have hW : IsOpen W := isOpen_iInter_of_finite fun i ↦ isOpen_Ioo.preimage
    ((PiLp.continuous_apply 2 _ i).comp continuous_snd)
  have hzero : 0 ∈ W := by simp [W]; norm_num
  refine ⟨W, hW.mem_nhds hzero, fun x hx y hy h ↦ Prod.ext (congrArg (fun v : ElementaryLieGroup m n r F ↦ v.1) h) ?_⟩
  apply PiLp.ext
  intro i
  apply AddCircle.injOn_coe_Ico (1 : ℝ) (-(1 / 2 : ℝ))
    (Ioo_subset_Ico_self (mem_iInter.mp hx i)) (Ioo_subset_Ico_self (mem_iInter.mp hy i))
  exact congrArg (fun v : ElementaryLieGroup m n r F ↦ v.2.1 i) h

/-- Openness of the homomorphism makes its linear lift between universal covers surjective. -/
private theorem elementaryHom_cover_rightInverse
    (a : ElementaryLieGroup m n r F →+ ElementaryLieGroup m' n' r' F')
    (ha : Continuous a) (hao : IsOpenMap a) :
    ∃ J : (EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      ∀ v, a (elementaryCover (J v) 0 0) = elementaryCover v 0 0 := by
  let c := elementaryCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  let d := elementaryCoverZeroHom (m := m') (n := n') (r := r') (F := F')
  let A := a.comp c
  have hA : Continuous A := ha.comp elementaryCoverZeroHom_continuous_isOpenMap.1
  let R := (AddMonoidHom.fst _ _).comp A
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp A)
  choose l hl using fun i : Fin n' ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hA.snd.fst)
  let L := (R.toRealLinearMap hA.fst).prod ((EuclideanSpace.equiv (Fin n') ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi l))
  have hL (v) : d (L v) = A v := by
    refine Prod.ext rfl (Prod.ext (funext fun i ↦ hl i v) ?_)
    have h := hA.snd.snd.isConst_of_preconnectedSpace v 0
    rw [map_zero A] at h
    exact h.symm
  obtain ⟨W, hW, hi⟩ := elementaryCoverZeroHom_injOn_nhds (m := m') (n := n') (r := r') (F := F')
  have hpre : L ⁻¹' W ∈ 𝓝 0 := L.continuous.continuousAt.preimage_mem_nhds (L.map_zero.symm ▸ hW)
  have hopen : IsOpenMap A := hao.comp elementaryCoverZeroHom_continuous_isOpenMap.2
  have him : A '' (L ⁻¹' W) ∈ 𝓝 0 := A.map_zero ▸ hopen.image_mem_nhds hpre
  have hd : Continuous d := elementaryCoverZeroHom_continuous_isOpenMap.1
  have hV : d ⁻¹' (A '' (L ⁻¹' W)) ∈ 𝓝 0 := hd.continuousAt.preimage_mem_nhds (d.map_zero.symm ▸ him)
  have hs : L.range = ⊤ := L.range.eq_top_of_nonempty_interior' ⟨0, mem_interior_iff_mem_nhds.mpr (by
    filter_upwards [hW, hV] with x hx hdx
    rcases hdx with ⟨u, hu, he⟩
    exact ⟨u, hi hu hx ((hL u).trans he)⟩)⟩
  obtain ⟨J, hJ⟩ := L.exists_rightInverse_of_surjective hs
  refine ⟨J, fun x ↦ (hL (J x)).symm.trans (congrArg d ?_)⟩
  exact DFunLike.congr_fun hJ x

/-- Smoothness on the cover descends through an open surjective elementary homomorphism. -/
private theorem contDiff_of_comp_elementaryHom [Finite F] {p : ℕ∞}
    (a : ElementaryLieGroup m n r F →+ ElementaryLieGroup m' n' r' F')
    (ha : Continuous a) (hao : IsOpenMap a) (hs : Surjective a)
    {f : ElementaryLieGroup m' n' r' F' → ℂ}
    (hf : ∀ z b, ContDiff ℝ p (fun u ↦ f (a (elementaryCover u z b))))
    (z : Fin r' → ℤ) (b : F') : ContDiff ℝ p (fun v ↦ f (elementaryCover v z b)) := by
  obtain ⟨J, hJ⟩ := elementaryHom_cover_rightInverse a ha hao
  obtain ⟨u, hu⟩ := hs (elementaryCover 0 z b)
  obtain ⟨t, ht⟩ := elementaryCover_surjective u.2.2.1 u.2.2.2 u.1 u.2.1
  have hshift (v) : elementaryCover (J v + (u.1,t)) u.2.2.1 u.2.2.2 = elementaryCover (J v) 0 0 + u := by
    rw [← show elementaryCover (u.1, t) u.2.2.1 u.2.2.2 = u from ht]
    simp [elementaryCover, Pi.add_def, Pi.zero_def]
  have he (v) : a (elementaryCover (J v + (u.1, t)) u.2.2.1 u.2.2.2) = elementaryCover v z b := by
    rw [hshift, map_add, hJ, hu]
    simp [elementaryCover, Pi.add_def, Pi.zero_def]
  simp_rw [← he]
  exact (hf u.2.2.1 u.2.2.2).comp (J.contDiff.add contDiff_const)
end ElementaryDescent
/-- Compact support bounds every polynomially weighted partial on an elementary group.
The lift in the torus coordinates need not be compactly supported. -/
private theorem elementarySchwartz_of_compactSupport {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (f : ElementaryLieGroup m n r F → ℂ) (hc : HasCompactSupport f)
    (hf : ∀ a b, ContDiff ℝ ∞ (fun u ↦ f (elementaryCover u a b))) :
    f ∈ elementarySchwartzSubmodule m n r F := by
  classical
  refine ⟨hf, fun ⟨α, β, γ, δ⟩ ↦ ?_⟩
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let D := (Fin r → ℤ) × F
  let q : X × D → ElementaryLieGroup m n r F := fun p ↦ elementaryCover p.1 p.2.1 p.2.2
  have hqW : IsOpenQuotientMap (fun u : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ (u i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  have hq : IsOpenQuotientMap q :=
    (Homeomorph.prodAssoc _ _ D).isOpenQuotientMap.comp
      ((IsOpenQuotientMap.id.prodMap hqW).prodMap IsOpenQuotientMap.id)
  let P (u : X) (a : Fin r → ℤ) (b : F) :=
    ((∏ i, (u.1 i : ℂ) ^ α i) * (∏ i, (a i : ℂ) ^ δ i)) * elementaryPartial f β γ u a b
  have hP (a : Fin r → ℤ) (b : F) : Continuous (fun u : X ↦ P u a b) := by
    have hpartial := (elementaryPartial_descends f β γ a b (hf a b)).1.continuous
    exact ((continuous_finsetProd _ fun i _ ↦ ((Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_fst)).pow _)).mul continuous_const).mul hpartial
  let W (y : ElementaryLieGroup m n r F) := P (y.1,
    (elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1).choose) y.2.2.1 y.2.2.2
  have hW (u : X) (a : Fin r → ℤ) (b : F) : W (elementaryCover u a b) = P u a b := by
    apply congrArg (fun z : ℂ ↦ ((∏ i, (u.1 i : ℂ) ^ α i) * (∏ i, (a i : ℂ) ^ δ i)) * z)
    apply (elementaryPartial_descends f β γ a b (hf a b)).2
    exact (elementaryCover_surjective a b u.1 (fun i ↦ (u.2 i : AddCircle (1 : ℝ)))).choose_spec
  have hcont : Continuous W := hq.continuous_comp_iff.mp (continuous_prod_of_discrete_right.mpr
    fun d ↦ (hP d.1 d.2).congr (fun u ↦ (hW u d.1 d.2).symm))
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn hcont.continuousOn
  apply lt_of_le_of_lt (b := (R.toNNReal : ℝ≥0∞)) _ ENNReal.coe_lt_top
  refine iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ENNReal.coe_le_coe.mpr ?_
  change ‖P u a b‖₊ ≤ R.toNNReal
  by_cases hx : elementaryCover u a b ∈ tsupport f
  · exact_mod_cast (show ‖P u a b‖ ≤ (R.toNNReal : ℝ) from
      (hW u a b) ▸ (hR _ hx).trans (Real.le_coe_toNNReal R))
  · have hcq : Continuous (fun v : X ↦ elementaryCover v a b) :=
      hq.continuous.comp (continuous_id.prodMk (continuous_const (y := (a,b))))
    have hu : u ∉ tsupport (fun v : X ↦ f (elementaryCover v a b)) :=
      fun h ↦ hx (tsupport_comp_subset_preimage f hcq h)
    have h0 (j : ℕ) : iteratedFDeriv ℝ j (fun v : X ↦ f (elementaryCover v a b)) u = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hu (tsupport_iteratedFDeriv_subset j h))
    have hdirs (v : List X) : iteratedFDeriv ℝ v.length (fun x : X ↦ f (elementaryCover x a b)) u v.get = 0 := by
      rw [h0 v.length]
      rfl
    have hz : elementaryPartial f β γ u a b = 0 := hdirs _
    simp [P, hz]

section FixedQuotient
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- On any structural quotient to which a smooth function descends, its descent is smooth
at every order, even when the original finite-order witnesses use different kernels. -/
private theorem bruhatSmooth_fixed_quotient {f : G → ℂ} (hf : IsBruhatSmooth f)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    {f₀ : a.quotient → ℂ} (h₀ : ∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val)
    (z : Fin e.latticeRank → ℤ) (t : e.finiteFactor) :
    ContDiff ℝ ∞ (fun v ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover v z t)))) := by
  apply contDiff_infty.mpr
  intro p
  obtain ⟨k, hk, _, hd⟩ := hf p
  let k₀ := OrderDual.ofDual a.val.2
  let b : BruhatStructuralPair G := ⟨(a.val.1, OrderDual.toDual (k₀ ⊓ k)), a.property.1, a.property.2.1,
    isBruhatGoodSubgroup_inf a.property.2.2.1 hk, inf_le_left.trans a.property.2.2.2⟩
  obtain ⟨g, hg, hgd⟩ := bruhatContDiff_descend_of_le hk hd b (show k₀ ⊓ k ≤ k from inf_le_right)
  let d := Classical.choice b.elementary
  let q : b.quotient →* a.quotient := QuotientGroup.map _ _ (MonoidHom.id a.val.1) (fun _ h ↦ h.1)
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk.of_comp_iff.mp
    (show IsOpenQuotientMap (QuotientGroup.mk : a.val.1 → a.quotient) from QuotientGroup.isOpenQuotientMap_mk)
  let A := AddMonoidHom.toMultiplicative.symm
    (e.equiv.toMonoidHom.comp (q.comp d.equiv.symm.toMonoidHom))
  have hc : Continuous A := e.equiv.continuous.comp (hq.continuous.comp d.equiv.symm.continuous)
  have ho : IsOpenMap A := e.equiv.toHomeomorph.isOpenMap.comp
    (hq.isOpenMap.comp d.equiv.symm.toHomeomorph.isOpenMap)
  have hsur : Surjective A := e.equiv.surjective.comp (hq.surjective.comp d.equiv.symm.surjective)
  let F := fun v ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd v))
  apply contDiff_of_comp_elementaryHom A hc ho hsur (f := F) _ z t
  intro z' t'
  have hdesc (v : b.quotient) : f₀ (q v) = g v := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    exact (h₀ x).trans (hg x).symm
  have heq (v) : F (A v) = g (d.equiv.symm (Multiplicative.ofAdd v)) := by
    change f₀ (e.equiv.symm (e.equiv _)) = _
    rw [e.equiv.symm_apply_apply]
    exact hdesc _
  simp_rw [heq]
  exact hgd d z' t'
/-- Every smooth compactly supported function is the realization of an elementary Schwartz stage. -/
private theorem bruhatCompactSupport_mem_schwartz {f : G → ℂ} (hf : f ∈ bruhatCompactSupportSubmodule G) :
    f ∈ schwartzBruhatSubmodule G := by
  classical
  have h := (mem_bruhatSmoothSubmodule_iff f).mp hf.1
  obtain ⟨k, hk, _, hd⟩ := h 0
  have hkC : IsCompact (k : Set G) := (lcaDualAnnihilator_annihilator k hk.1) ▸
    isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains (hf.2.union hkC)
  let a : BruhatStructuralPair G := ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk,
    fun _ hx ↦ hH (Or.inr hx)⟩
  let e := Classical.choice a.elementary
  obtain ⟨f₀, h₀, _⟩ := hd a rfl
  let φ := fun y ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd y))
  let q : a.val.1 → ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
    fun x ↦ (e.equiv (QuotientGroup.mk x)).toAdd
  have hq : Continuous q := continuous_toAdd.comp (e.equiv.continuous.comp QuotientGroup.continuous_mk)
  have hs : Surjective q := fun y ↦ (e.equiv.surjective.comp QuotientGroup.mk_surjective) (Multiplicative.ofAdd y)
  have he (x : a.val.1) : φ (q x) = f x.val := by
    change f₀ (e.equiv.symm (e.equiv _)) = _
    rw [e.equiv.symm_apply_apply, h₀]
  have hc : HasCompactSupport φ := by
    have hc' := (H.val.isClosed_of_isOpen H.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hf.2
    apply HasCompactSupport.intro (hc'.image hq)
    intro y hy
    obtain ⟨x, rfl⟩ := hs y
    exact (he x).trans (image_eq_zero_of_notMem_tsupport fun hx ↦ hy ⟨x, hx, rfl⟩)
  let s : SchwartzBruhatStage e := ⟨φ, elementarySchwartz_of_compactSupport φ hc
    (bruhatSmooth_fixed_quotient h a e h₀)⟩
  refine (mem_schwartzBruhatSubmodule_iff f).mpr ⟨a, e, s, funext fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs with hx
  · exact he ⟨x, hx⟩
  · exact (image_eq_zero_of_notMem_tsupport fun ht ↦ hx (hH (Or.inl ht))).symm
end FixedQuotient

section StrictTestTopology

variable [SecondCountableTopology G]
local notation "B" => BruhatCompactSupport G

/-- The test topology makes the identity map to the Schwartz–Bruhat space continuous. -/
private theorem continuous_compactSupport_to_schwartz :
    Continuous (show B →ₗ[ℂ] SchwartzBruhat G from Submodule.inclusion
        (fun _ hf ↦ bruhatCompactSupport_mem_schwartz hf)) := by
  let J : B →ₗ[ℂ] SchwartzBruhat G := Submodule.inclusion (fun _ hf ↦ bruhatCompactSupport_mem_schwartz hf)
  let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) (C : Compacts G),
      Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
  refine (PolynormableSpace.withSeminorms ℂ (SchwartzBruhat G)).continuous_of_continuous_comp J fun p ↦
    (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm (⟨p.val.comp J, ?_⟩ : P)
  intro a e C
  exact p.property.comp ((schwartzBruhatStage_isEmbedding a e).continuous.comp continuous_subtype_val)

private theorem compactSupport_stage_embedding (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) :
    IsEmbedding (show bruhatCompactSupportStage a e C →ₗ[ℂ] B from bruhatCompactSupportStageInclusion a e C) := by
  let i : bruhatCompactSupportStage a e C →ₗ[ℂ] B := bruhatCompactSupportStageInclusion a e C
  have hi : Continuous i := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp i
    (fun p ↦ p.property a e C)
  exact IsEmbedding.of_comp hi continuous_compactSupport_to_schwartz
    ((schwartzBruhatStage_isEmbedding a e).comp IsEmbedding.subtypeVal)

/-- A closed linear embedding in a Fréchet space gives completeness and metrizability
for the induced uniform structure. -/
private theorem frechet_of_closed_embedding {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [PolynormableSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (hY : IsFrechetTVS Y)
    (L : X →ₗ[ℂ] Y) (hL : IsClosedEmbedding L) : IsFrechetTVS X := by
  obtain ⟨hadd, hpoly, hmetr, hcomplete⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have hU := AddMonoidHom.isUniformInducing_of_isInducing (f := L.toAddMonoidHom) hL.isInducing
  refine ⟨inferInstance, inferInstance, hL.isEmbedding.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := X)]
  exact hU.completeSpace hL.isClosed_range.isComplete

private theorem compactSupport_stage_range_frechet (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) :
    let i : bruhatCompactSupportStage a e C →ₗ[ℂ] B := bruhatCompactSupportStageInclusion a e C
    IsFrechetTVS i.range := by
  let X := bruhatCompactSupportStage a e C
  let i : X →ₗ[ℂ] B := bruhatCompactSupportStageInclusion a e C
  change IsFrechetTVS i.range
  have h : IsEmbedding i := compactSupport_stage_embedding a e C
  let d := LinearEquiv.ofInjective i h.injective
  have hd : IsEmbedding d := h.codRestrict _ _
  let E := ContinuousLinearEquiv.ofIsHomeomorph d (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hd, d.surjective⟩)
  have hc : IsClosed (X : Set (SchwartzBruhatStage e)) := by
    simp only [X, bruhatCompactSupportStage, Submodule.coe_iInf]
    apply isClosed_iInter
    intro x
    have heval := (continuous_schwartzBruhat_eval_forEndpoints x.val).comp (schwartzBruhatStage_isEmbedding a e).continuous
    exact isClosed_singleton.preimage heval
  let : UniformSpace i.range := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup i.range := isUniformAddGroup_of_addCommGroup
  exact frechet_of_closed_embedding (X := i.range) elementarySchwartz_isFrechet (X.subtype.comp E.symm.toLinearMap)
    ((X.isClosedEmbedding_subtype hc).comp E.symm.toHomeomorph.isClosedEmbedding)

omit [SecondCountableTopology G] in
/-- A transition between elementary stages restricts to any enlargement of the compact support. -/
private theorem compactSupport_stage_transition {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient)
    {C K : Compacts G} (hC : C ≤ K) :
    ∃ L : bruhatCompactSupportStage a e C →L[ℂ] bruhatCompactSupportStage b d K,
      ∀ f, bruhatCompactSupportStageInclusion b d K (L f) = bruhatCompactSupportStageInclusion a e C f := by
  have htrans := schwartzBruhatStage_transition h e d
  let T := htrans.choose
  have hT := htrans.choose_spec.1
  let X := bruhatCompactSupportStage a e C
  have hm (f : X) : T f.val ∈ bruhatCompactSupportStage b d K :=
    (mem_bruhatCompactSupportStage_iff b d K _).mpr ((hT f.val).symm ▸
      ((mem_bruhatCompactSupportStage_iff a e C _).mp f.property).trans hC)
  exact ⟨(T.comp X.subtypeL).codRestrict _ hm, fun f ↦ Subtype.ext (hT f.val)⟩

omit [SecondCountableTopology G] in
/-- Support of a test function supplies the compact set for its Schwartz stage. -/
private theorem compactSupport_exists_stage (f : B) :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (J : Compacts G) (u : bruhatCompactSupportStage a e J),
      bruhatCompactSupportStageInclusion a e J u = f := by
  obtain ⟨a, e, u, hu⟩ := (mem_schwartzBruhatSubmodule_iff (G := G) f.val).mp
    (bruhatCompactSupport_mem_schwartz f.property)
  let J : Compacts G := ⟨tsupport f.val, f.property.2⟩
  have hm : u ∈ bruhatCompactSupportStage a e J := (mem_bruhatCompactSupportStage_iff a e J u).mpr
    (hu.symm ▸ (Subset.rfl : tsupport f.val ⊆ (J : Set G)))
  exact ⟨a, e, J, ⟨u, hm⟩, Subtype.ext hu⟩

/-- Passing to the ranges of a cofinal sequence of embedded stages preserves the final
locally convex topology. -/
private theorem finalTopology_cofinal_ranges {E : Type*} [AddCommGroup E] [Module ℂ E]
    [t : TopologicalSpace E] {ι : Type*} {X : ι → Type*}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)]
    (i : ∀ a, X a →ₗ[ℂ] E) (s : ℕ → ι)
    (ht : t = locallyConvexFinalTopology i) (he : ∀ n, IsEmbedding (i (s n)))
    (hfactor : ∀ a, ∃ n, ∃ T : X a →L[ℂ] X (s n), ∀ f, i (s n) (T f) = i a f) :
    t = locallyConvexFinalTopology (fun n ↦ (i (s n)).range.subtype) := by
  have htests : (fun p : Seminorm ℂ E ↦ ∀ a, Continuous (p ∘ i a)) =
      (fun p : Seminorm ℂ E ↦ ∀ n, Continuous (p ∘ (i (s n)).range.subtype)) := by
    funext p
    apply propext
    constructor
    · intro hp n
      have hr : IsInducing (i (s n)).rangeRestrict := (he n).isInducing.codRestrict _
      exact (hr.isQuotientMap_of_surjective (i (s n)).surjective_rangeRestrict).continuous_iff.mpr (hp (s n))
    · intro hp a
      obtain ⟨n, T, hT⟩ := hfactor a
      have hr : Continuous (i (s n)).rangeRestrict := (he n).continuous.subtype_mk _
      exact ((hp n).comp (hr.comp T.continuous)).congr fun f ↦ congrArg p (hT f)
  exact ht.trans (congrArg (fun pred : Seminorm ℂ E → Prop ↦
    (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype pred → Seminorm ℂ E)).topology) htests)

private theorem strictLF_of_ranges {E : Type*} [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    {ι : Type*} {X : ι → Type*} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, TopologicalSpace (X a)] (i : ∀ a, X a →ₗ[ℂ] E) (s : ℕ → ι)
    (hT : T2Space E) (ht : t = locallyConvexFinalTopology i)
    (he : ∀ n, IsEmbedding (i (s n))) (hF : ∀ n, IsFrechetTVS (i (s n)).range)
    (hmono : ∀ l n, l ≤ n → ∃ L : X (s l) →L[ℂ] X (s n), ∀ f, i (s n) (L f) = i (s l) f)
    (hcover : ∀ f : E, ∃ a, ∃ u : X a, i a u = f)
    (hfactor : ∀ a, ∃ n, ∃ L : X a →L[ℂ] X (s n), ∀ f, i (s n) (L f) = i a f) :
    IsStrictLFSpace E := by
  refine ⟨hT, fun n ↦ (i (s n)).range, ?_, hF, ?_, finalTopology_cofinal_ranges i s ht he hfactor⟩
  · rintro l n h _ ⟨f, rfl⟩
    obtain ⟨L, hL⟩ := hmono l n h
    exact ⟨L f, hL f⟩
  · intro f
    obtain ⟨a, u, rfl⟩ := hcover f
    obtain ⟨n, L, hL⟩ := hfactor a
    exact ⟨n, L u, hL u⟩

private abbrev TestStageIndex (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient × Compacts G

local notation "Idx" => TestStageIndex G
private abbrev TestStage (a : Idx) := ↥(bruhatCompactSupportStage a.1 a.2.1 a.2.2)

local notation "Stage" => TestStage (G := G)

private def testStageMap (a : Idx) : Stage a →ₗ[ℂ] B :=
  bruhatCompactSupportStageInclusion a.1 a.2.1 a.2.2

private theorem testTopology_final :
    (inferInstance : TopologicalSpace B) = locallyConvexFinalTopology (X := Stage) (testStageMap (G := G)) := by
  have htests : (fun p : Seminorm ℂ (bruhatCompactSupportSubmodule G) ↦ ∀ (a : BruhatStructuralPair G)
      (e : ElementaryLCAPresentation a.quotient) (J : Compacts G), Continuous (p ∘ bruhatCompactSupportStageInclusion a e J)) =
      (fun p : Seminorm ℂ B ↦ ∀ a : Idx, Continuous (p ∘ testStageMap a)) := by
    funext p
    exact propext ⟨fun h a ↦ h a.1 a.2.1 a.2.2, fun h a e J ↦ h ⟨a, e, J⟩⟩
  exact congrArg (fun pred : Seminorm ℂ B → Prop ↦
    (SeminormFamily.moduleFilterBasis (Subtype.val : Subtype pred → Seminorm ℂ B)).topology) htests

private theorem compactSupport_t2 : T2Space B := by
  let J : B →ₗ[ℂ] SchwartzBruhat G := Submodule.inclusion (p := bruhatCompactSupportSubmodule G)
    (p' := schwartzBruhatSubmodule G) (fun _ hf ↦ bruhatCompactSupport_mem_schwartz (G := G) hf)
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  exact T2Space.of_injective_continuous (f := J) (Submodule.inclusion_injective _) continuous_compactSupport_to_schwartz

private theorem compactSupport_stage_cover (f : B) : ∃ a : Idx, ∃ u : Stage a, testStageMap a u = f :=
  (compactSupport_exists_stage f).elim fun a ha ↦ ha.elim fun e he ↦ he.elim fun J hJ ↦
    hJ.elim fun u hu ↦ ⟨⟨a, e, J⟩, u, hu⟩

private theorem testStageMap_transition (a b : Idx) (h : a.1 ≤ b.1) (hJ : a.2.2 ≤ b.2.2) :
    ∃ L : Stage a →L[ℂ] Stage b, ∀ f, testStageMap b (L f) = testStageMap a f :=
  compactSupport_stage_transition h a.2.1 b.2.1 hJ

end StrictTestTopology

/-- Paper: Lemma D.3.6.1, p. 819. For a second-countable group the test
function topology admits a countable strict presentation by Fréchet stages. -/
theorem bruhatCompactSupport_strictLF [SecondCountableTopology G] :
    IsStrictLFSpace (BruhatCompactSupport G) := by
  have hseq := exists_cofinal_bruhatStructuralPairs (G := G)
  let b := hseq.choose
  let K := CompactExhaustion.choice G
  let s (n : ℕ) : TestStageIndex G := ⟨b n, Classical.choice (b n).elementary, ⟨K n, K.isCompact n⟩⟩
  apply strictLF_of_ranges (X := TestStage (G := G)) testStageMap s compactSupport_t2 testTopology_final
    (fun n ↦ compactSupport_stage_embedding (s n).1 (s n).2.1 (s n).2.2)
    (fun n ↦ compactSupport_stage_range_frechet (s n).1 (s n).2.1 (s n).2.2)
    (fun l n h ↦ testStageMap_transition (s l) (s n) (hseq.choose_spec.1 h) (K.subset h))
    compactSupport_stage_cover
  intro a
  let r := (hseq.choose_spec.2 a.1).choose
  have hr := (hseq.choose_spec.2 a.1).choose_spec
  let j := (K.exists_superset_of_isCompact a.2.2.isCompact).choose
  have hj := (K.exists_superset_of_isCompact a.2.2.isCompact).choose_spec
  exact ⟨max r j, testStageMap_transition a (s _) (hr.trans (hseq.choose_spec.1 (le_max_left r j)))
    (hj.trans (K.subset (le_max_right r j)))⟩

variable (I : Set ℝ) (hm : IsModulation m) (hms : Surjective m)

include hm hms in
/-- Paper: Lemma D.3.6.1, p. 819. The compactly supported smooth test
functions form a subspace of the exponential-decay space. -/
theorem bruhatCompactSupport_le_modulatedExponentialDecay :
    bruhatCompactSupportSubmodule G ≤ modulatedExponentialDecaySubmodule m I := by
  intro f hf
  refine (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr (bruhatCompactSupport_mem_schwartz ?_)
  have hcancel : modulationWeight m (-(a : ℝ)) (modulationWeight m a f) = f := by
    funext x
    have hx : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    simp only [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero,
      Complex.ofReal_one, one_mul]
  refine ⟨(mem_bruhatSmoothSubmodule_iff _).mpr (fun p ↦
    isBruhatContDiff_of_modulationWeight m (a := -(a : ℝ)) ?_), hf.2.mul_left⟩
  rw [hcancel]
  exact (mem_bruhatSmoothSubmodule_iff _).mp hf.1 p

/-- Paper: Lemma D.3.6.1, p. 819. The canonical inclusion into the
exponential-decay space is the identity on the underlying functions. -/
def bruhatCompactSupportToModulatedExponentialDecay :
    BruhatCompactSupport G →ₗ[ℂ] ModulatedExponentialDecay m I :=
  Submodule.inclusion (bruhatCompactSupport_le_modulatedExponentialDecay m I hm hms)

-- Avoid the unused-section-variable linter traversing the large seminorm-family types.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.3.6.1, p. 819. Applying the inclusion preserves every
pointwise value of the test function. -/
theorem bruhatCompactSupportToModulatedExponentialDecay_apply (f : BruhatCompactSupport G) (x : G) :
    (bruhatCompactSupportToModulatedExponentialDecay m I hm hms f).val x = f.val x := rfl

variable [hSC : SecondCountableTopology G] (hInt : OrdConnected I) (hne : I.Nonempty)

/-- Truncate an exponential outside a compact set without changing its values there. -/
private theorem exists_smooth_compact_exp (K : Set ℝ) (hK : IsCompact K) (a : ℝ) :
    ∃ φ : ℝ → ℂ, ContDiff ℝ ∞ φ ∧ (∀ j : ℕ, ∃ D, ∀ t, ‖iteratedFDeriv ℝ j φ t‖ ≤ D) ∧
      ∀ t ∈ K, φ t = (Real.exp (t * a) : ℂ) := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, lt_add_one R⟩
  let φ (t : ℝ) : ℂ := ((b t * Real.exp (t * a) : ℝ) : ℂ)
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp
    (b.contDiff.mul ((contDiff_id.mul contDiff_const).exp))
  have hr : HasCompactSupport (fun t : ℝ ↦ b t * Real.exp (t * a)) := b.hasCompactSupport.mul_right
  have hs : HasCompactSupport φ := hr.comp_left Complex.ofReal_zero
  refine ⟨φ, hφ, fun j ↦ (hφ.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
    (hs.iteratedFDeriv j), fun t ht ↦ ?_⟩
  have hbt : b t = 1 := b.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound t ht)
  simp only [φ, hbt, one_mul]

set_option linter.unusedSectionVars false in
/-- On a prescribed compact set, a weight acts by a continuous Schwartz multiplier. -/
private theorem exists_schwartz_multiplier_on_compact (C : Compacts G) (a : ℝ) :
    ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ (f : SchwartzBruhat G),
      tsupport f.val ⊆ (C : Set G) → ∀ x, (M f).val x = modulationWeight m a f.val x := by
  let logM (g : G) := Real.log ((m g).val : ℝ)
  have hpos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hcont : Continuous logM :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log fun x ↦ (hpos x).ne'
  have h := exists_smooth_compact_exp (logM '' (C : Set G)) (C.isCompact.image hcont) a
  have hM := logModulation_mul_schwartzBruhat_continuousLinear m h.choose_spec.1 h.choose_spec.2.1
  refine ⟨hM.choose, fun f hf x ↦ (hM.choose_spec f x).trans ?_⟩
  change h.choose (logM x) * f.val x = (((m x).val : ℝ) ^ a : ℝ) * f.val x
  by_cases hx : x ∈ (C : Set G)
  · rw [h.choose_spec.2.2 _ ⟨x, hx, rfl⟩, Real.rpow_def_of_pos (hpos x)]
  · have hz : f.val x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hf h))
    rw [hz, mul_zero, mul_zero]

set_option linter.unusedSectionVars false in
/-- Each fixed-support stage descends to a single compact-subgroup decay stage.
Its twists are continuous Schwartz multipliers on the quotient. -/
private theorem continuous_fixedSupport_to_decay (b : BruhatStructuralPair G)
    (d : ElementaryLCAPresentation b.quotient) (C : Compacts G) :
    Continuous ((bruhatCompactSupportToModulatedExponentialDecay m I hm hms) ∘
      bruhatCompactSupportStageInclusion b d C) := by
  let k₀ := OrderDual.ofDual b.val.2
  let k := (⟨k₀, isCompact_of_isBruhatGoodSubgroup_aux k₀ b.property.2.2.1,
    b.property.2.2.1.2.2⟩ : {k : Subgroup G // IsCompact (k : Set G) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator k)})
  let : IsClosed (k₀ : Set G) := k.property.1.isClosed
  let Q := G ⧸ k₀
  let n := quotientModulation m k₀ k.property.1
  let X := bruhatCompactSupportStage b d C
  let D : Compacts Q := ⟨QuotientGroup.mk '' (C : Set G), C.isCompact.image QuotientGroup.continuous_mk⟩
  have hd := schwartzBruhatStage_compactQuotient_descent b d
  let P : X →L[ℂ] SchwartzBruhat Q := hd.choose.comp (bruhatCompactSupportStage b d C).subtypeL
  have hP (s : X) (g : G) : P s (g : Q) = schwartzBruhatStageRealization b d s.val g :=
    hd.choose_spec s.val g
  have hsupp (s : X) : tsupport (P s : Q → ℂ) ⊆ D := by
    apply closure_minimal _ D.isCompact.isClosed
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have h := (mem_bruhatCompactSupportStage_iff b d C _).mp s.property
    exact ⟨g, h (subset_tsupport _ (show schwartzBruhatStageRealization b d s.val g ≠ 0 from
      (hP s g) ▸ hx)), rfl⟩
  have hM (a : I) := exists_schwartz_multiplier_on_compact n D (a : ℝ)
  have htwist (s : X) (a : I) : modulationWeight n a (P s) = ((hM a).choose (P s)).val :=
    funext fun x ↦ ((hM a).choose_spec (P s) (hsupp s) x).symm
  let L (s : X) : ModulatedExponentialDecayStage m I k :=
    ⟨(P s).val, (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr
      ((htwist s a).symm ▸ ((hM a).choose (P s)).property)⟩
  have hL : Continuous L := by
    apply (modulatedDecayStage_twists_isInducing m I k).continuous_iff.mpr
    apply continuous_pi
    intro a
    exact ((hM a).choose.continuous.comp P.continuous).congr fun s ↦
      Subtype.ext (htwist s a).symm
  let j : ModulatedExponentialDecayStage m I k →ₗ[ℂ] ModulatedExponentialDecay m I :=
    modulatedExponentialDecayStageInclusion m I k
  have hj : Continuous j := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp
    j fun p ↦ p.property k
  exact (hj.comp hL).congr fun s ↦ Subtype.ext (funext (hP s))

set_option linter.unusedSectionVars false in
include hSC hInt hne in
/-- Paper: Lemma D.3.6.1, p. 819. The inclusion of smooth compactly
supported functions is continuous from the test function topology. -/
theorem bruhatCompactSupport_continuous_modulatedExponentialDecay :
    Continuous (bruhatCompactSupportToModulatedExponentialDecay m I hm hms) := by
  let j := bruhatCompactSupportToModulatedExponentialDecay m I hm hms
  let TestSeminorms := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
    ∀ (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) (C : Compacts G),
      Continuous (q ∘ bruhatCompactSupportStageInclusion b d C)}
  have hE := PolynormableSpace.withSeminorms ℂ (ModulatedExponentialDecay m I)
  refine hE.continuous_of_continuous_comp j fun p ↦ ?_
  let q := p.val.comp j
  have hq (b : BruhatStructuralPair G) (d : ElementaryLCAPresentation b.quotient) (C : Compacts G) :
      Continuous (q ∘ bruhatCompactSupportStageInclusion b d C) :=
    p.property.comp (continuous_fixedSupport_to_decay m I hm hms b d C)
  exact (withGeneratingSeminorms_spec _ (Subtype.val : TestSeminorms → _)).continuous_seminorm ⟨q, hq⟩

-- TODO(paper-gap): The proof of continuity invokes the global projective topology
-- for arbitrary I. Theorem D.3.3.7(4) identifies it with the stage limit for compact I.
-- TODO(paper-gap): The seminorms ν_{a,k} in the proof omit polynomial weights.
-- In (D.3.6.2) the r = k term still has ψ(x/m) as a factor. The estimates
-- (D.3.6.3)–(D.3.6.4) omit the resulting cutoff tail even at k = 0.

/-- Rescaling one smooth cutoff approximates a log profile in every Schwartz twist. -/
private theorem dense_compactSupport_logProfiles (hI : I.Nonempty) :
    Dense {f : PositiveRealExponentialDecay I | HasCompactSupport f.val} := by
  intro f
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let cut (ε x : ℝ) := b (ε • x)
  have htemp (ε : ℝ) : (cut ε).HasTemperateGrowth := by
    have hb := b.hasCompactSupport.hasTemperateGrowth b.contDiff
    exact hb.comp (f := fun x : ℝ ↦ ε • x) (by fun_prop)
  let F (ε : ℝ) (x : ℝ) := cut ε x • f.val x
  let T (ε : ℝ) (a : I) := SchwartzMap.smulLeftCLM ℂ (cut ε) (logExponentialDecayTwist I a f)
  have hT (ε : ℝ) (a : I) : realSchwartzCoe (T ε a) = logExponentialWeight a (F ε) := by
    funext x
    change SchwartzMap.smulLeftCLM ℂ (cut ε) (logExponentialDecayTwist I a f) x = _
    rw [SchwartzMap.smulLeftCLM_apply (htemp ε)]
    change cut ε x • (logExponentialDecayTwist I a f x) =
      (Real.exp ((a : ℝ) * x) : ℂ) • (cut ε x • f.val x)
    rw [logExponentialDecayTwist_apply I a f x]
    exact smul_comm (cut ε x) (Real.exp ((a : ℝ) * x) : ℂ) (f.val x)
  let g (ε : ℝ) : PositiveRealExponentialDecay I :=
    ⟨F ε, (Submodule.mem_iInf _).2 fun a ↦ ⟨T ε a, hT ε a⟩⟩
  have hg (ε : ℝ) (a : I) : logExponentialDecayTwist I a (g ε) = T ε a := by
    ext x
    exact (logExponentialDecayTwist_apply I a (g ε) x).trans (congrFun (hT ε a) x).symm
  have hlim : Tendsto g (𝓝 0) (𝓝 f) := by
    apply (positiveRealExponentialDecay_isEmbedding I hI).isInducing.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro a
    change Tendsto (fun ε ↦ logExponentialDecayTwist I a (g ε)) _ _
    simp_rw [hg]
    exact SchwartzMap.tendsto_smulLeftCLM_comp_smul b.contDiff b.hasCompactSupport b.eventuallyEq_one _
  apply mem_closure_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ)))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (b.hasCompactSupport.comp_smul hε).smul_right

include hm in
/-- Properness of the modulation pulls compact support in the log coordinate back to the group. -/
private theorem hasCompactSupport_of_split_profile (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    {φ : ℝ → ℂ} (hφ : HasCompactSupport φ) {F : G → ℂ}
    (hF : ∀ (u : m.toMonoidHom.ker) t, φ (Real.log ((t : ℝ≥0ˣ).val : ℝ)) = 0 →
      F (u.val * τ t) = 0) : HasCompactSupport F := by
  let logM (x : G) := (positiveRealLogEquiv (m x)).toAdd
  have hproper : IsProperMap logM :=
    ((Homeomorph.ofAdd (X := ℝ)).symm.isProperMap.comp
      positiveRealLogEquiv.toHomeomorph.isProperMap).comp hm.1
  apply HasCompactSupport.intro (hproper.isCompact_preimage hφ)
  intro x hx
  let u : m.toMonoidHom.ker := ⟨x / τ (m x), by
    change m (x / τ (m x)) = 1
    rw [map_div, hτ, div_self']⟩
  have hzero : φ (Real.log ((m x).val : ℝ)) = 0 :=
    image_eq_zero_of_notMem_tsupport (by
      simpa only [logM, positiveRealLogEquiv_apply, mem_compl_iff, mem_preimage] using hx)
  exact (congrArg F (div_mul_cancel x (τ (m x)))).symm.trans (hF u (m x) hzero)

set_option linter.unusedSectionVars false in
/-- A decay function with a compactly supported profile in split coordinates is a test. -/
private theorem mem_test_range_of_split_profile (hI : I.Nonempty)
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) (F : ModulatedExponentialDecay m I)
    (h : m.toMonoidHom.ker → ℂ) (f : ℝ → ℂ) (hf : HasCompactSupport f)
    (he : ∀ (u : m.toMonoidHom.ker) t, F.val (u.val * τ t) = h u * f (Real.log (t.val : ℝ))) :
    F ∈ Set.range (bruhatCompactSupportToModulatedExponentialDecay m I hm hms) := by
  have hcs : HasCompactSupport F.val := hasCompactSupport_of_split_profile m hm τ hτ hf
    fun u t ht ↦ (he u t).trans ((congrArg (h u * ·) ht).trans (mul_zero _))
  let g : BruhatCompactSupport G := ⟨F.val, modulatedExponentialDecay_mem_bruhatSmooth m I hI F, hcs⟩
  refine ⟨g, Subtype.ext (funext fun x ↦ ?_)⟩
  exact bruhatCompactSupportToModulatedExponentialDecay_apply m I hm hms g x

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

open UniformSpace
open scoped TensorProduct

-- Use the scalar action of the completed tensor equivalence in §D.3.3.
attribute [local instance] instContinuousSMulComplexWithGeneratingSeminorms_1

universe u

/-- It suffices to hit pure tensors whose second factor belongs to a dense set. -/
private theorem denseRange_of_dense_right_tensors {X E A : Type u} {Y : Type}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul ℂ E] [AddCommGroup A] [Module ℂ A]
    (j : A →ₗ[ℂ] E) {B : Set Y} (hB : Dense B)
    (e : Completion (InductiveTensor X Y) ≃L[ℂ] E)
    (hpure : ∀ x y, y ∈ B → e (Completion.coe' (α := InductiveTensor X Y)
      (x ⊗ₜ[ℂ] y)) ∈ Set.range j) : DenseRange j := by
  let T := InductiveTensor X Y
  let S := j.range.topologicalClosure
  let L : T →ₗ[ℂ] E :=
    e.toLinearEquiv.toLinearMap.comp (Completion.toComplL : T →L[ℂ] Completion T).toLinearMap
  have hT (x : X) (y : Y) : L (x ⊗ₜ[ℂ] y) ∈ S := by
    have generating := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
      (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
        (∀ x : X, Continuous (fun y : Y ↦ p (x ⊗ₜ[ℂ] y))) ∧
        (∀ y : Y, Continuous (fun x : X ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
    have hc : @Continuous Y T _ _ (fun z ↦ x ⊗ₜ[ℂ] z) :=
      generating.continuous_of_continuous_comp
        (TensorProduct.mk ℂ X Y x) fun p ↦ p.property.1 x
    have hclosed : IsClosed {z : Y | L (x ⊗ₜ[ℂ] z) ∈ S} :=
      j.range.isClosed_topologicalClosure.preimage
        (e.continuous.comp ((Completion.continuous_coe T).comp hc))
    exact (closure_minimal (s := B) (t := {z : Y | L (x ⊗ₜ[ℂ] z) ∈ S})
      (fun z hz ↦ j.range.le_topologicalClosure (hpure x z hz)) hclosed) (hB y)
  have hL (x : T) : L x ∈ S := by
    exact TensorProduct.inductionOn (motive := fun z ↦ L z ∈ S) x hT
      (fun _ _ hx hy ↦ (S.comap L).add_mem hx hy)
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact Completion.induction_on (p := fun z ↦ e z ∈ S) z
    (j.range.isClosed_topologicalClosure.preimage e.continuous) hL

set_option linter.unusedSectionVars false in
private theorem dense_test_range_of_tensor_equiv (hI : I.Nonempty)
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (e : Completion (InductiveTensor (SchwartzBruhat m.toMonoidHom.ker)
      (PositiveRealExponentialDecay I)) ≃L[ℂ] ModulatedExponentialDecay m I)
    (he : ∀ (h : SchwartzBruhat m.toMonoidHom.ker) (f : PositiveRealExponentialDecay I)
      (u : m.toMonoidHom.ker) t, (e (Completion.coe' (α := InductiveTensor
        (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)) (h ⊗ₜ[ℂ] f))).val
        (u.val * τ t) = h u * f.val (Real.log (t.val : ℝ))) :
    DenseRange (bruhatCompactSupportToModulatedExponentialDecay m I hm hms) := by
  refine denseRange_of_dense_right_tensors (X := SchwartzBruhat m.toMonoidHom.ker)
    (bruhatCompactSupportToModulatedExponentialDecay m I hm hms)
    (dense_compactSupport_logProfiles I hI) e ?_
  intro h f hf
  have hresult := mem_test_range_of_split_profile m I hm hms hI τ hτ
    (e (Completion.coe' (α :=
    InductiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)) (h ⊗ₜ[ℂ] f))) (fun u ↦ h u) f.val hf (he h f)
  exact hresult

set_option linter.unusedSectionVars false in
include hSC hInt hne in
/-- Paper: Lemma D.3.6.1, p. 819. Smooth compactly supported functions are
dense in the exponential-decay space with its locally convex topology. -/
theorem bruhatCompactSupport_dense_modulatedExponentialDecay :
    DenseRange (bruhatCompactSupportToModulatedExponentialDecay m I hm hms) := by
  let σ := (IsModulation.exists_section hm).choose
  have hσ := (IsModulation.exists_section hm).choose_spec
  let τ : ℝ≥0ˣ →ₜ* G := σ.comp
    ⟨MonoidHom.codRestrict (MonoidHom.id _) m.toMonoidHom.range (fun t ↦ hms t),
      continuous_id.subtype_mk _⟩
  have hτ : RightInverse τ m := fun t ↦ hσ ⟨t, hms t⟩
  have htensor := modulatedExponentialDecay_tensor_equiv m I hm hInt hne τ hτ
  exact dense_test_range_of_tensor_equiv m I hm hms hne τ hτ htensor.choose htensor.choose_spec

end CompactSupport

end RiemannMasullo
