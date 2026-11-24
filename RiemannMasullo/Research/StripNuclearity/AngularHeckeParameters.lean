module

public import RiemannMasullo.Research.StripNuclearity.HeckeArchimedean
public import RiemannMasullo.Research.StripNuclearity.AngularChoice

/-! # Archimedean Hecke parameters as angular frequencies

At each infinite place the imaginary radial exponent is additive in the
unitary character. At each complex place the signed integer angular order
is additive as well. On the discrete dual of the norm-one class group these
give continuous homomorphisms to the additive real line.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
set_option quotPrecheck false in
local notation "X" => PontryaginDual (ideleClassNorm F).ker

private theorem archRestriction_mul (χ ψ : U) (v : InfinitePlace F) (u : v.Completionˣ) :
    infinitePlaceRestriction F v (ideleClassNormTwist (χ * ψ) 0) u =
      infinitePlaceRestriction F v (ideleClassNormTwist χ 0) u *
        infinitePlaceRestriction F v (ideleClassNormTwist ψ 0) u := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v u
  change ((χ g * ψ g : Circle) : ℂ) * _ ^ (0 : ℂ) =
    ((χ g : ℂ) * _ ^ (0 : ℂ)) * ((ψ g : ℂ) * _ ^ (0 : ℂ))
  simp

private theorem realRadial_mul (χ ψ : U) (v : InfinitePlace F) (hv : v.IsReal) :
    (realHeckeCharacter_parameters (χ * ψ) v hv).exists.choose.1 =
      (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        (realHeckeCharacter_parameters ψ v hv).exists.choose.1 := by
  let a := (realHeckeCharacter_parameters χ v hv).exists.choose
  let b := (realHeckeCharacter_parameters ψ v hv).exists.choose
  have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
  have hb := (realHeckeCharacter_parameters ψ v hv).exists.choose_spec
  have hsign (r s : Fin 2) (x : ℝ) :
      (if 0 < x then (1 : ℂ) else -1) ^ (r+s).val =
        (if 0 < x then (1 : ℂ) else -1) ^ r.val * (if 0 < x then (1 : ℂ) else -1) ^ s.val := by
    split <;> fin_cases r <;> fin_cases s <;> norm_num
  have h := (realHeckeCharacter_parameters (χ * ψ) v hv).unique
    (realHeckeCharacter_parameters (χ * ψ) v hv).exists.choose_spec
    (y₂ := (a.1+b.1, a.2+b.2)) (by
      refine ⟨(congrArg₂ (· + ·) ha.1 hb.1).trans (zero_add 0), fun x ↦ ?_⟩
      have hn : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      rw [archRestriction_mul, ha.2 x, hb.2 x]
      dsimp only
      rw [Complex.cpow_add _ _ hn, hsign]
      dsimp [a,b]
      ring)
  exact congrArg Prod.fst h

private theorem complexParameters_mul (χ ψ : U) (v : InfinitePlace F) (hv : v.IsComplex) :
    (complexHeckeCharacter_parameters (χ * ψ) v hv).exists.choose =
      ((complexHeckeCharacter_parameters χ v hv).exists.choose.1 +
        (complexHeckeCharacter_parameters ψ v hv).exists.choose.1,
       (complexHeckeCharacter_parameters χ v hv).exists.choose.2 +
        (complexHeckeCharacter_parameters ψ v hv).exists.choose.2) := by
  have ha := (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
  have hb := (complexHeckeCharacter_parameters ψ v hv).exists.choose_spec
  apply (complexHeckeCharacter_parameters (χ * ψ) v hv).unique
    (complexHeckeCharacter_parameters (χ * ψ) v hv).exists.choose_spec
  refine ⟨(congrArg₂ (· + ·) ha.1 hb.1).trans (zero_add 0), fun x ↦ ?_⟩
  have hn : (‖(x : ℂ)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
  have hq : (((‖(x : ℂ)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.ne_zero))
  rw [archRestriction_mul, ha.2 x, hb.2 x]
  dsimp only
  rw [Complex.cpow_add _ _ hq, zpow_add₀ (div_ne_zero x.ne_zero hn)]
  ring

/-- Paper: Equation (3.2.1.5), p. 123. The signed angular order of the local
complex character. Real places are assigned zero since their sign parity is
already bounded by one. -/
def heckeArchimedeanAngularOrder (χ : U) (v : InfinitePlace F) : ℤ :=
  open Classical in
  if hv : v.IsReal then 0 else
    (complexHeckeCharacter_parameters χ v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2

private theorem radial_im_mul (χ ψ : U) (v : InfinitePlace F) :
    (heckeArchimedeanShift (χ * ψ) v).im =
      (heckeArchimedeanShift χ v).im + (heckeArchimedeanShift ψ v).im := by
  by_cases hv : v.IsReal
  · simp only [heckeArchimedeanShift, dite_eq_left hv, Complex.add_im, Complex.natCast_im, add_zero]
    exact congrArg Complex.im (realRadial_mul χ ψ v hv)
  · simp only [heckeArchimedeanShift, dite_eq_right hv, Complex.add_im, Complex.div_ofNat_im,
      Complex.natCast_im, zero_div, add_zero]
    exact congrArg (fun a : ℂ × ℤ ↦ a.1.im)
      (complexParameters_mul χ ψ v (InfinitePlace.not_isReal_iff_isComplex.mp hv))

private theorem archOrder_mul (χ ψ : U) (v : InfinitePlace F) :
    heckeArchimedeanAngularOrder (χ * ψ) v =
      heckeArchimedeanAngularOrder χ v + heckeArchimedeanAngularOrder ψ v := by
  by_cases hv : v.IsReal
  · simp [heckeArchimedeanAngularOrder, hv]
  · simp only [heckeArchimedeanAngularOrder, dite_eq_right hv]
    exact congrArg Prod.snd (complexParameters_mul χ ψ v (InfinitePlace.not_isReal_iff_isComplex.mp hv))

/-- Each infinite place supplies a real angular frequency for the radial
exponent and one for the signed complex angular order. The gamma shift grows
at most linearly in their absolute values. -/
theorem exists_angular_frequencies_heckeArchimedeanShift (χ : X →* U) (v : InfinitePlace F) :
    ∃ ρ θ : X →ₜ* Multiplicative ℝ, ∀ ξ : X,
      (ρ ξ).toAdd = (heckeArchimedeanShift (χ ξ) v).im ∧
      (θ ξ).toAdd = (heckeArchimedeanAngularOrder (χ ξ) v : ℝ) ∧
      ‖heckeArchimedeanShift (χ ξ) v‖ ≤ 1 + |(ρ ξ).toAdd| + |(θ ξ).toAdd| := by
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let r : X →* Multiplicative ℝ := MonoidHom.mk'
    (fun ξ ↦ Multiplicative.ofAdd (heckeArchimedeanShift (χ ξ) v).im) (fun ξ η ↦ by
      change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
      rw [map_mul, radial_im_mul]
      rfl)
  let a : X →* Multiplicative ℝ := MonoidHom.mk'
    (fun ξ ↦ Multiplicative.ofAdd (heckeArchimedeanAngularOrder (χ ξ) v : ℝ)) (fun ξ η ↦ by
      change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
      rw [map_mul, archOrder_mul, Int.cast_add]
      rfl)
  refine ⟨⟨r, continuous_of_discreteTopology⟩, ⟨a, continuous_of_discreteTopology⟩,
    fun ξ ↦ ⟨rfl, rfl, ?_⟩⟩
  change ‖heckeArchimedeanShift (χ ξ) v‖ ≤ 1 + |(heckeArchimedeanShift (χ ξ) v).im| +
    |(heckeArchimedeanAngularOrder (χ ξ) v : ℝ)|
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  rw [abs_of_nonneg (heckeArchimedeanShift_re_nonneg _ _)]
  by_cases hv : v.IsReal
  · let b := (realHeckeCharacter_parameters (χ ξ) v hv).exists.choose
    have ha : b.1.re = 0 := (realHeckeCharacter_parameters (χ ξ) v hv).exists.choose_spec.1
    simp only [heckeArchimedeanShift, heckeArchimedeanAngularOrder, dite_eq_left hv,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, Int.cast_zero,
      abs_zero, add_zero]
    change b.1.re + (b.2.val : ℝ) + |b.1.im| ≤ 1 + |b.1.im|
    rw [ha, zero_add]
    have hle : (b.2.val : ℝ) ≤ 1 := by exact_mod_cast (show b.2.val ≤ 1 by have := b.2.isLt; omega)
    linarith
  · let b := (complexHeckeCharacter_parameters (χ ξ) v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    have ha : b.1.re = 0 := (complexHeckeCharacter_parameters (χ ξ) v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
    simp only [heckeArchimedeanShift, heckeArchimedeanAngularOrder, dite_eq_right hv,
      Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.natCast_re,
      Complex.natCast_im, zero_div, add_zero]
    change b.1.re + (b.2.natAbs : ℝ) / 2 + |b.1.im| ≤ 1 + |b.1.im| + |(b.2 : ℝ)|
    rw [ha, zero_add, Nat.cast_natAbs, Int.cast_abs]
    linarith [abs_nonneg (b.2 : ℝ)]


private theorem member_le_product_of_one_le (l : List ℝ) (hl : ∀ x ∈ l, 1 ≤ x)
    {x : ℝ} (hx : x ∈ l) : x ≤ l.prod := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    have ha : 1 ≤ a := hl a (by simp)
    have ht : ∀ y ∈ l, 1 ≤ y := fun y hy ↦ hl y (List.mem_cons_of_mem a hy)
    have hprod := List.one_le_prod ht
    rw [List.prod_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_mul_of_one_le_right (zero_le_one.trans ha) hprod
    · exact (ih ht h).trans (le_mul_of_one_le_left (zero_le_one.trans hprod) ha)

/-- The sum of the norms of the genuine archimedean shifts is bounded by a
fixed multiple of one product of squared real frequencies on the compact dual. -/
theorem exists_angular_weight_heckeArchimedeanShifts (χ : X →* U) :
    ∃ fs : List (X →ₜ* Multiplicative ℝ), ∀ ξ : X,
      let W := (fs.map (fun f ↦ 1 + ((f ξ).toAdd) ^ 2)).prod
      1 ≤ W ∧ (∑ v : InfinitePlace F, ‖heckeArchimedeanShift (χ ξ) v‖) ≤
        3 * (Fintype.card (InfinitePlace F) : ℝ) * W := by
  classical
  choose r θ h using exists_angular_frequencies_heckeArchimedeanShift χ
  let vs := (Finset.univ : Finset (InfinitePlace F)).toList
  let fs := vs.map r ++ vs.map θ
  refine ⟨fs, fun ξ ↦ ?_⟩
  let factor (f : X →ₜ* Multiplicative ℝ) := 1 + ((f ξ).toAdd) ^ 2
  let W := (fs.map factor).prod
  have hf (x) (hx : x ∈ fs.map factor) : 1 ≤ x := by
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    dsimp [factor]
    linarith [sq_nonneg ((f ξ).toAdd)]
  have hw : 1 ≤ W := List.one_le_prod hf
  have hc (f : X →ₜ* Multiplicative ℝ) (hmem : f ∈ fs) : |(f ξ).toAdd| ≤ W := by
    apply le_trans _ (member_le_product_of_one_le _ hf (List.mem_map_of_mem hmem))
    change |(f ξ).toAdd| ≤ 1 + ((f ξ).toAdd) ^ 2
    nlinarith [sq_nonneg (|(f ξ).toAdd| - 1 / 2), sq_abs ((f ξ).toAdd)]
  have hsum (v : InfinitePlace F) : ‖heckeArchimedeanShift (χ ξ) v‖ ≤ 3 * W := by
    have hv : v ∈ vs := by simp [vs]
    have hr := hc (r v) (List.mem_append_left _ (List.mem_map_of_mem hv))
    have hθ := hc (θ v) (List.mem_append_right _ (List.mem_map_of_mem hv))
    linarith [(h v ξ).2.2]
  refine ⟨hw, (Finset.sum_le_sum (fun v _ ↦ hsum v)).trans_eq ?_⟩
  simp [W, factor, mul_left_comm, mul_assoc]

end RiemannMasullo.StripNuclearity
