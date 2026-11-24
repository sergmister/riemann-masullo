module
public import RiemannMasullo.Research.StripNuclearity.ScalarFourierTrace
public import RiemannMasullo.Research.StripNuclearity.HeckeComponent

/-!
# Smooth compact convolutions after a single Hecke spectral projection
-/

@[expose] public noncomputable section
open Function MeasureTheory NumberField Set
open scoped Topology ContDiff Convolution ComplexConjugate NumberField.AdeleRing

namespace RiemannMasullo.StripNuclearity

/-- Reciprocal-square mass of the admitted jets of a completed Hecke function on
one closed strip centered at one-half. The boundary multiplicity is the minimum
of the arithmetic order and the strict Sobolev cutoff. -/
def admittedHeckeDivisorMass {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (α s : ℝ) : ℝ :=
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
  let Z := {z : ℂ // 0 < D z ∧ |z.re - 1/2| ≤ α}
  ∑' z : Z, (spectralStripMultiplicity α s (z.val.re - 1/2) (D z.val).toNat : ℝ)/(1+|z.val.im|)^2

/-- A bounded operator on the logarithmic weighted line is convolution with the
specified radial profile, using ordinary Lebesgue measure. -/
def HasRadialConvolutionKernel (α s : ℝ) (κ : ℝ → ℂ)
    (A : CompactIntervalSobolev volume id (-α) α s →L[ℂ] CompactIntervalSobolev volume id (-α) α s) : Prop :=
  ∀ f, ∀ᵐ x ∂volume, A f x = ∫ t : ℝ, κ t * f (x-t)

/-- Each unitary Hecke character uses the same exponential test chart and the same
compact-support estimate. The only character dependence in the projected trace norm
is the square of one plus the weighted admitted divisor mass. The Hardy order uses
the strict boundary jet cutoff of Chapter 10. -/
theorem exists_projected_hecke_convolution_uniform {F : Type*} [Field F] [NumberField F]
    {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) :
    let d := α+s+2
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (C : {K : Set ℝ // IsCompact K} → ℝ),
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧ (∀ K, 0 ≤ C K) ∧
      ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
        let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
        let Z := {z : ℂ // 0 < D z ∧ |z.re - 1/2| ≤ α}
        let w := fun z : Z ↦ (⟨z.val.re - 1/2, z.val.im⟩ : ℂ)
        let m := fun z : Z ↦ spectralStripMultiplicity α s (w z).re (D z.val).toNat
        let J := Σ z, Fin (m z)
        let W : ℝ := admittedHeckeDivisorMass χ α s
        ∃ Λ : J → StrongDual ℂ E,
          (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
            (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) ∧
          let Q := (⨅ l, (Λ l).ker).orthogonal.starProjection
          ∀ (K : {K : Set ℝ // IsCompact K}) (κ : ℝ → ℂ), tsupport κ ⊆ K.val →
            ContDiff ℝ (∞) κ → ∀ A : E →L[ℂ] E,
              HasRadialConvolutionKernel α s κ A →
              ∃ hn : IsNuclearOperator (A.comp Q),
                traceNorm ⟨A.comp Q,hn⟩ ≤ C K * (1+W)^(2:ℕ) * radialQuadraticFourierCost κ := by
  intro d E I
  obtain ⟨j,R,B,hB,hdense,hj,hR,hu⟩ := exists_projected_hecke_resolvent_uniform (F := F) ha hs
  have hd : 0 < d := by dsimp [d]; linarith
  have hn (z : ℂ) (hz : z.re ∈ I) : (((d+1 : ℝ) : ℂ)^2-z^2) ≠ 0 := by
    have hx := (sq_le_sq₀ (abs_nonneg z.re) hd.le).mpr (abs_le.mpr ⟨hz.1.le,hz.2.le⟩)
    rw [sq_abs] at hx
    have hpos : 0 < (((d+1 : ℝ) : ℂ)^2-z^2).re := by
      simp [sq,Complex.mul_re]
      nlinarith [sq_nonneg z.im]
    exact fun hx ↦ (ne_of_gt hpos) (congrArg Complex.re hx)
  let data (K : {K : Set ℝ // IsCompact K}) :=
    scalar_projected_convolution_traceNorm_le ha (by linarith) isOpen_Ioo ordConnected_Ioo
      ⟨0,(show -(d:ℝ) < 0 by linarith),hd⟩ (d+1) hn K.property j R hj hR
  let C (K : {K : Set ℝ // IsCompact K}) := (data K).choose
  have hC (K) : 0 ≤ C K := (data K).choose_spec.1
  refine ⟨j,fun K ↦ C K*(1+B),hdense,hj,fun K ↦ mul_nonneg (hC K) (by linarith),?_⟩
  intro χ D Z w m J W
  obtain ⟨Λ,hΛ,hQ⟩ := hu χ
  refine ⟨Λ,hΛ,?_⟩
  intro Q K κ hκ hsκ A hA
  obtain ⟨hN,hNle⟩ := hQ
  obtain ⟨hAq,hAqle⟩ := (data K).choose_spec.2 κ hκ hsκ A Q hN hA
  have hW : 0 ≤ W := tsum_nonneg fun _ ↦ by positivity
  have hone : 1 ≤ (1+W)^(2:ℕ) := by nlinarith [sq_nonneg W]
  have hQn : ‖Q‖ ≤ 1 := Submodule.starProjection_norm_le _
  have hsum : ‖Q‖ + traceNorm ⟨R.adjoint.comp Q,hN⟩ ≤ (1+B)*(1+W)^(2:ℕ) := by
    calc
      _ ≤ (1+W)^(2:ℕ) + B*(1+W)^(2:ℕ) := add_le_add (hQn.trans hone) hNle
      _ = _ := by ring
  refine ⟨hAq,hAqle.trans ?_⟩
  calc
    _ ≤ C K * radialQuadraticFourierCost κ * ((1+B)*(1+W)^(2:ℕ)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (hC K) (radialQuadraticFourierCost_nonneg κ))
    _ = _ := by ring

/-- For any fixed unitary Hecke character and closed strip centered at one-half,
all smooth compactly supported radial convolution operators are trace class
after projection onto the admitted Mellin jet space. No zero spacing or
rectangular basis convergence is assumed. -/
theorem exists_projected_hecke_convolution {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {α s : ℝ} (ha : 0 ≤ α) (hs : 1 < s) :
    let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ
    let Z := {z : ℂ // 0 < D z ∧ |z.re - 1/2| ≤ α}
    let w := fun z : Z ↦ (⟨z.val.re - 1/2, z.val.im⟩ : ℂ)
    let m := fun z : Z ↦ spectralStripMultiplicity α s (w z).re (D z.val).toNat
    let d := α+s+2
    let E := CompactIntervalSobolev volume id (-α) α s
    let I := Ioo (-d) d
    let J := Σ z, Fin (m z)
    ∃ (j : PositiveRealExponentialDecay I →L[ℂ] E) (Λ : J → StrongDual ℂ E),
      DenseRange j ∧ (∀ p, (j p : ℝ → ℂ) =ᵐ[volume] p.val) ∧
      (∀ (l : J) p, Λ l (j p) = iteratedDeriv l.2.val
        (mellin (fun t ↦ p.val (Real.log t))) (w l.1)) ∧
      ∀ (κ : ℝ → ℂ), HasCompactSupport κ → ContDiff ℝ (∞) κ →
        ∀ A : E →L[ℂ] E, (∀ f, ∀ᵐ x ∂volume, A f x = ∫ t : ℝ, κ t * f (x-t)) →
          IsNuclearOperator (A.comp ((⨅ l, (Λ l).ker).orthogonal.starProjection)) := by
  intro D Z w m d E I J
  obtain ⟨j,C,hdense,hj,_,hu⟩ := exists_projected_hecke_convolution_uniform (F := F) ha hs
  obtain ⟨Λ,hΛ,hQ⟩ := hu χ
  refine ⟨j,Λ,hdense,hj,hΛ,?_⟩
  intro κ hk hsκ A hA
  exact (hQ ⟨tsupport κ,hk⟩ κ Subset.rfl hsκ A hA).choose

end RiemannMasullo.StripNuclearity
