module

public import RiemannMasullo.Ch01_Introduction.Sec4
public import RiemannMasullo.Research.TraceComparison.RationalCutoffComparison
public import RiemannMasullo.Research.TraceComparison.RadialConvolutionSpectrum
public import RiemannMasullo.Research.PositiveStrip.Solution
public import RiemannMasullo.Research.StripNuclearity.HeckePairedDivisor

/-! # Quotient convolution on rational real-place annihilating tests

A compact log profile can kill the archimedean principal value and both
polar moments while acting nontrivially at a specified retained zeta zero.
On a wide strip its smoothed diagonal integral still vanishes. This tests
an operator-level strengthening of the comparison on pp. 514 and 520.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped ContDiff NumberField.AdeleRing Topology SchwartzMap
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "Dℚ" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "hI(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "Q(" hα "," hs ")" => spectralSobolevQuotient ℚ (1/2) (hI(hα)) (hs₀(hs))
local notation "A(" φ "," hα "," hs ")" => spectralConvolution (F := ℚ) (1/2) (hI(hα)) (hs₀(hs)) φ
local notation "radial(" φ "," g ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))

/-- One can prescribe a nonzero Mellin value in the open critical strip
within the differential family annihilating the real-place functional. -/
theorem exists_boundedRealAnnihilator_mellin_ne_zero {a b : ℝ} (hab : a < b)
    (w : ℂ) (hw : w.re ∈ Ioo (0 : ℝ) 1) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Icc a b ∧
      compactLogMellin (boundedRealAnnihilator f) w ≠ 0 := by
  have hsep : w ∉ ({w-2} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  obtain ⟨f,hf,hc,hI,hn,hz⟩ := exists_compactLogMellin_vanishing_on_finset w {w-2} hsep hab
  refine ⟨f,hf,hc,hI,?_⟩
  rw [compactLogMellin_boundedRealAnnihilator f hf hc, hz _ (Finset.mem_singleton_self _), mul_zero, sub_zero]
  apply mul_ne_zero _ hn
  unfold boundedRealAnnihilatorSymbol
  simp only [mul_ne_zero_iff]
  have h₀ : w ≠ 0 := fun h ↦ (by simpa [h] using hw.1 : False)
  have h₂ : w + 2 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.add_re] at he
    linarith [hw.1]
  have h₁ : w - 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.sub_re] at he
    linarith [hw.2]
  have hadd : w + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num [Complex.add_re] at he
    linarith [hw.1]
  exact ⟨⟨⟨h₀,h₂⟩,h₁⟩,hadd⟩

/-- An interior positive divisor of the trivial rational character gives a
nonzero continuous eigenfunctional of the actual quotient convolution. Its
eigenvalue for a centered radial test includes the norm-one Tamagawa volume. -/
theorem rational_spectralConvolution_has_mellin_eigenfunctional {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (w : ℂ) (hw : 0 < Dℚ w) (hi : |w.re - 1/2| < α) :
    ∃ l : StrongDual ℂ Q(hα,hs), l ≠ 0 ∧
      ∀ (g : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ), radial(φ,g) →
        ∀ u, l (A(φ,hα,hs) u) = (Vℚ * compactLogMellin g w) * l u := by
  classical
  let choices := exists_spectralBasepointChoice_radially_trivial ℚ
  let χ := choices.choose
  obtain ⟨-,x,f,hbasis,hjet⟩ := spectralStripMarkushevichBasis_direct χ choices.choose_spec.1
    (a := (1/2:ℝ)) hα (hs₀(hs))
  have he : (((1 / 2 + (w.re - 1 / 2) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I) = w := by
    apply Complex.ext <;> simp
  have hshift : (((w.re - 1 / 2 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I) = w - 1/2 := by
    apply Complex.ext <;> simp
  let L := continuedCompletedHeckeL (F := ℚ) 1
  have hord : 0 < (meromorphicOrderAt L w).untop₀ := by
    rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (F := ℚ) 1).1.meromorphicOn (mem_univ w)] at hw
    exact hw
  have hpos : 0 < meromorphicOrderAt L w := by
    cases h : meromorphicOrderAt L w with
    | top => simp
    | coe n => rw [h, WithTop.untop₀_coe] at hord; exact_mod_cast hord
  let z : {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-α) α ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1))
        (((1/2 + z.2.1 : ℝ) : ℂ) + (z.2.2 : ℂ) * Complex.I)} :=
    ⟨(1,w.re-1/2,w.im), ⟨(abs_lt.mp hi).1.le,(abs_lt.mp hi).2.le⟩, by simpa only [map_one, he] using hpos⟩
  let N := spectralStripMultiplicity α s z.val.2.1
    (meromorphicOrderAt (continuedCompletedHeckeL (χ z.val.1))
      (((1/2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)).untop₀.toNat
  have hN : 0 < N := by
    simpa only [N, z, map_one, he, spectralStripMultiplicity, ite_eq_left (abs_lt.mp hi)] using
      (show 0 < (meromorphicOrderAt L w).untop₀.toNat by omega)
  let j : SpectralStripJetIndex χ (1/2) α s := ⟨(1,w.re-1/2,w.im,0), hN⟩
  refine ⟨f j, fun hz ↦ ?_, fun g φ hφ u ↦ ?_⟩
  · have h := hbasis.1 j
    simp [hz] at h
  · have h := spectralStripConvolution_zeroJet (F := ℚ) (1/2) hα hs χ f hjet φ z hN u
    rw [← rationalCenteredNormTest_mellin g φ hφ w]
    simpa only [z, map_one, hshift, j] using h

local notation "strong(" hs ")" => (lt_of_lt_of_le (Nat.one_lt_ofNat : (1:ℝ)<3) hs)
local notation "diagonal(" φ "," hα "," hs "," U ")" =>
  (∫ x : Cℚ, dSequenceKernelSmoothening μℚ U
    (globalStripGeometricKernel (F := ℚ) (1/2) (hα).le strong(hs) φ
      (exists_numberField_projectiveKernel_comp_spectralProjection (F := ℚ) (hα).le strong(hs) φ)) (x,x) ∂μℚ)

/-- In a wide strip every ordinary zero is interior, so the geometric
diagonal of each real-place annihilating test vanishes unconditionally. -/
theorem rational_wide_realAnnihilator_diagonal_eq_zero (f : ℝ → ℂ) (hf : ContDiff ℝ (∞) f)
    (hc : HasCompactSupport f) {a b α s : ℝ} (ha : 0 < a) (hb : b < Real.log 2)
    (hI : tsupport f ⊆ Icc a b) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,boundedRealAnnihilator f))
    (hα : 0 < α) (hwide : 1/2 ≤ α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μℚ U)
    (hm : ∀ n, MeasurableSet (U n)) : diagonal(φ,hα,hs,U) = 0 := by
  let : IsEmpty (rationalWindowOmittedZeros α s) := ⟨fun z ↦ by
    have hi := lt_of_lt_of_le (abs_re_shiftedZetaZero_lt z.val) hwide
    have hi' : -α < z.val.val.re - 1/2 ∧ z.val.val.re - 1/2 < α := by
      simpa only [shiftedZetaZero,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re] using abs_lt.mp hi
    have hpos := z.property
    change 0 < zetaZeroOrder z.val - spectralStripMultiplicity α s (z.val.val.re-1/2) (zetaZeroOrder z.val) at hpos
    rw [spectralStripMultiplicity,ite_eq_left hi',Nat.sub_self] at hpos
    exact (Nat.lt_irrefl 0 hpos)⟩
  have h := rational_realAnnihilator_missingJets_hasSum f hf hc ha hb hI φ hφ hα hs U hU hm
  exact h.unique hasSum_empty

private theorem radial_intertwiner_killed_by_eigenfunctional {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] (A : H →L[ℂ] H) (l : StrongDual ℂ H) (hL : l ≠ 0)
    (c : ℂ) (hne : c ≠ 0) (heig : ∀ u, l (A u) = c * l u)
    (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g) (h0 : compactLogMellin g 0 = 0)
    (C : ℂ) (k : 𝓢(ℝ,ℂ)) (hk : ∀ x, k x = C * rationalCenteredLogProfile g x)
    (J : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] H)
    (hJ : ∀ h : 𝓢(ℝ,ℂ), J ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k h).toLp 2) =
       A (J (h.toLp 2))) : l.comp J = 0 ∧ ¬ DenseRange J := by
  have h (v : 𝓢(ℝ,ℂ)) :
      (l.comp J) ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k v).toLp 2) =
        c * (l.comp J) (v.toLp 2) := by
    rw [ContinuousLinearMap.comp_apply,hJ,heig]
    rfl
  have hzero := centered_radial_convolution_no_eigenfunctional g hg hc h0 C k hk _
    hne (l.comp J) h
  refine ⟨hzero,fun hd ↦ hL ?_⟩
  ext v
  apply hd.induction_on (p := fun v ↦ l v = 0) v (isClosed_eq l.continuous continuous_const)
  intro x
  exact DFunLike.congr_fun hzero x

/-- For an annihilating radial test with a nonzero moment at a retained zero,
the range of a bounded intertwiner from ordinary radial L² convolution
lies in the kernel of the corresponding quotient coordinate. It suffices to
intertwine on Schwartz inputs. The scalar allows the local Haar normalization. -/
theorem rational_spectralConvolution_radial_intertwiner_killed_by_zeroJet {α s : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (w : ℂ) (hw : 0 < Dℚ w) (hi : |w.re - 1/2| < α)
    (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (h0 : compactLogMellin g 0 = 0) (hn : compactLogMellin g w ≠ 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,g)) :
    ∃ l : StrongDual ℂ Q(hα,hs), l ≠ 0 ∧
      ∀ (C : ℂ) (k : 𝓢(ℝ,ℂ)), (∀ x, k x = C * rationalCenteredLogProfile g x) →
      ∀ (J : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Q(hα,hs)),
      (∀ h : 𝓢(ℝ,ℂ), J ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k h).toLp 2) =
        A(φ,hα,hs) (J (h.toLp 2))) → l.comp J = 0 ∧ ¬ DenseRange J := by
  obtain ⟨l,hL,hA⟩ := rational_spectralConvolution_has_mellin_eigenfunctional hα hs w hw hi
  refine ⟨l,hL,fun C k hk J hJ ↦ ?_⟩
  exact radial_intertwiner_killed_by_eigenfunctional _ l hL _ (mul_ne_zero rationalNormOneTamagawaVolume_ne_zero hn)
    (hA g φ hφ) g hg hc h0 C k hk J hJ

local notation "S₀" => (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)))
local notation "J₀" => SIdeleQuotient ℚ S₀
local notation "μ₀" => sLocalQuotientTamagawaMeasure ℚ S₀
local notation "v₀" => (((sLocalNormOneQuotientMeasure ℚ S₀) univ).toReal : ℂ)
local notation "logJ" => (fun y : J₀ ↦ Real.log (((sIdeleQuotientNorm ℚ S₀ y).val):ℝ))

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

/-- In every rational prime-free log interval there is a test with zero wide
geometric diagonal and a nonzero eigenvalue on the dual of the quotient
convolution. The ordinary convolution in the statement is the actual
S-local quotient action on radial Schwartz inputs. Any bounded intertwiner
annihilates this specific quotient coordinate, so its range cannot be dense.
The statement concerns the action before the spatial and Fourier cutoffs. -/
theorem exists_rational_primeFree_realAnnihilator_no_dense_radial_intertwiner {a b α s : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hα : 0 < α) (hwide : 1/2 ≤ α) (hs : 3 ≤ s) :
    ∃ (f : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (k : 𝓢(ℝ,ℂ)) (c : ℂ) (l : StrongDual ℂ Q(hα.le,strong(hs))),
      ContDiff ℝ (∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Icc a b ∧
      (radial(φ,boundedRealAnnihilator f)) ∧ c ≠ 0 ∧ l ≠ 0 ∧
      (∀ u, l (A(φ,hα.le,strong(hs)) u) = c * l u) ∧
      (∀ h : 𝓢(ℝ,ℂ), ∀ y : J₀,
        lcaConvolution μ₀ ((rationalCenteredLogProfile (boundedRealAnnihilator f)) ∘ logJ) (h ∘ logJ) y =
          SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k h (logJ y)) ∧
      (∀ J : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Q(hα.le,strong(hs)),
        (∀ h : 𝓢(ℝ,ℂ), J ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k h).toLp 2) =
          A(φ,hα.le,strong(hs)) (J (h.toLp 2))) → l.comp J = 0 ∧ ¬ DenseRange J) ∧
      ∀ (U : ℕ → Set Cℚ), IsDPrimeSequence μℚ U → (∀ n, MeasurableSet (U n)) → diagonal(φ,hα,hs,U) = 0 := by
  let : Infinite {z : ℂ // 0 < Dℚ z} := introTrace_rat_positive_divisor_infinite
  obtain ⟨⟨w,hw⟩⟩ := Infinite.nonempty {z : ℂ // 0 < Dℚ z}
  have hstrip := heckePositiveDivisor_open_strip (F := ℚ) 1 hw
  have hi : |w.re-1/2| < α := by rw [abs_lt]; constructor <;> linarith [hstrip.1,hstrip.2]
  obtain ⟨f,hf,hc,hI,hm⟩ := exists_boundedRealAnnihilator_mellin_ne_zero hab w hstrip
  let g := boundedRealAnnihilator f
  obtain ⟨hd,hgc,-⟩ := boundedRealAnnihilator_regularity f hf hc
  obtain ⟨φ,hφ⟩ := exists_rationalCenteredNormTest _ hd hgc
  obtain ⟨l,hn,he⟩ := rational_spectralConvolution_has_mellin_eigenfunctional hα.le strong(hs) w hw hi
  have hG : ContDiff ℝ (∞) (rationalCenteredLogProfile g) :=
    (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.div_const 2)).mul hd
  have hkc : HasCompactSupport (fun t ↦ v₀ * rationalCenteredLogProfile g t) := hgc.mul_left.mul_left
  let k := hkc.toSchwartzMap (contDiff_const.mul hG)
  have hne := mul_ne_zero rationalNormOneTamagawaVolume_ne_zero hm
  refine ⟨f,φ,k,_,l,hf,hc,hI,hφ,hne,hn,he _ φ hφ,
    sLocal_radial_schwartz_convolution (F := ℚ) (S := S₀) _ hG.continuous k (fun _ ↦ rfl),?_,
    rational_wide_realAnnihilator_diagonal_eq_zero f hf hc ha hb hI φ hφ hα hwide hs⟩
  exact radial_intertwiner_killed_by_eigenfunctional _ l hn _ hne (he _ φ hφ) g hd.continuous hgc
    (boundedRealAnnihilator_polarMoments f hf hc).1 v₀ k (fun _ ↦ rfl)

end RiemannMasullo.StripNuclearity
