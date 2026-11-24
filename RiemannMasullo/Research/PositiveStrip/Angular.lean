module
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "W'(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s true
local notation "Θ(" a ", " hI ", " hs ")" => globalThetaSobolev F a hI hs
local notation "ρ(" l ", " r ", " s ", " hI ", " hs ")" =>
  (hardySobolevTranslation μ𝔽 m𝔽 l r s hI hs).comp (ideleClassNorm F).ker.subtype
local notation "Wω(" hI ", " hs ", " ω ")" => actionIsotype (ρ(_, _, _, hI, hs)) ω
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)

local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

open scoped SchwartzMap
local notation "nuTheta" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "rad(" χ ", " u ")" => (fun x : C𝔽 ↦ ((χ⁻¹ x : Circle) : ℂ) * u (logNorm x))
local instance thetaStripCanonicalHaar : (nuTheta : Measure C𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

local notation "Ws(" α ", " s ")" => CompactIntervalSobolev volume id (-α) α s
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "uJet(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
local notation "L2μ'(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logNorm g))⁻¹)

/-- Compact character averaging takes each pure vector back onto its character
component. Totality extends this observation from pure vectors to all vectors. -/
private theorem stripAngular_compact_assembly {G E J : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (κ : Measure G) [κ.IsHaarMeasure] [κ.WeaklyRegular] (τ : G →* (E →L[ℂ] E))
    (hτ : Continuous (fun p : G × E ↦ τ p.1 p.2))
    (R : PontryaginDual G → Submodule ℂ E) (hR : ∀ ξ, IsClosed (R ξ : Set E))
    (hE : ∀ ξ (x : E), x ∈ R ξ → ∀ g, τ g x = (ξ g : ℂ) • x)
    (htotal : ∀ (V : Submodule ℂ E), IsClosed (V : Set E) → (∀ ξ, R ξ ≤ V) → ∀ x, x ∈ V)
    (ω : J → PontryaginDual G) (Λ : J → StrongDual ℂ E)
    (heigen : ∀ j g x, Λ j (τ g x) = (ω j g : ℂ)*Λ j x)
    (N : Submodule ℂ E) (hN : IsClosed (N : Set E))
    (hRker : ∀ ξ (x : E), x ∈ R ξ → (∀ j, ω j = ξ → Λ j x = 0) → x ∈ N)
    (y : E) (hy : ∀ j, Λ j y = 0) : y ∈ N := by
  classical
  by_contra hny
  obtain ⟨φ,hne,hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem N hN hny
  let u (g : G) := φ (τ g y)
  have hu : Continuous u := φ.continuous.comp (hτ.comp (continuous_id.prodMk continuous_const))
  have hcoeff (ξ : PontryaginDual G) : ∫ g, star (ξ g : ℂ)*u g ∂κ = 0 := by
    let A (g : G) := star (ξ g : ℂ) • τ g
    have hA : Continuous (fun q : G × E ↦ A q.1 q.2) :=
      (show Continuous (fun q : G × E ↦ star (ξ q.1 : ℂ)) from by fun_prop).smul hτ
    obtain ⟨P,hP,-⟩ := existsUnique_pettisIntegral_continuousFamily κ isCompact_univ
      (.of_forall fun _ ↦ mem_univ _) A hA
    have hP' : IsPettisIsotypicAverageOn κ univ τ ξ P := by
      simpa only [IsPettisIsotypicAverageOn,Measure.restrict_univ,A,smul_apply] using hP
    have hsum (x : E) (δ : StrongDual ℂ E) := compactActionAverage_dual_apply κ τ ξ P hP' x δ
    have hproj (θ : PontryaginDual G) (x : E) (hx : x ∈ R θ) :
        P x = (if ξ = θ then (κ.real univ : ℂ) else 0) • x := by
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
      intro δ
      rw [hsum, map_smul,smul_eq_mul,←integral_character_pair κ ξ θ,←integral_mul_const]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      rw [hE θ x hx g,map_smul,smul_eq_mul,mul_assoc]
    have hPx (x : E) : P x ∈ R ξ := by
      apply htotal ((R ξ).comap P.toLinearMap) ((hR ξ).preimage P.continuous) _ x
      intro θ w hw
      change P w ∈ R ξ
      rw [hproj θ w hw]
      split_ifs with h
      · exact (R ξ).smul_mem _ (h ▸ hw)
      · rw [zero_smul]; exact (R ξ).zero_mem
    have hPy := hRker ξ (P y) (hPx y) (fun j _ ↦ by
      rw [hsum]
      exact integral_eq_zero_of_ae (.of_forall fun g ↦ by
        change star (ξ g : ℂ)*Λ j (τ g y) = 0
        rw [heigen,hy,mul_zero,mul_zero]))
    exact (hsum y φ).symm.trans (hzero _ hPy)
  have he := ae_eq_zero_of_character_integral_eq_zero κ (hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hcoeff
  have heq := Measure.eq_of_ae_eq he hu continuous_const
  exact hne (by simpa [u] using congrFun heq 1)

/-- The canonical log pullback is an isometry even after multiplication by an
arbitrary unitary character; changing Haar normalization preserves closed range. -/
private theorem stripAngular_closed_radial (ξ : PontryaginDual C𝔽) (α s : ℝ) :
    ∃ L : Ws(α, s) →L[ℂ] W(-α, α, s), IsClosed (range L) ∧
      ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ξ x : ℂ)⁻¹ * f (logNorm x) := by
  let ρ := intervalSobolevDensity (-α) α s
  let η := volume.withDensity (fun t : ℝ ↦ ENNReal.ofReal (ρ t))
  let ν := nuTheta
  let μw := ν.withDensity (fun x : C𝔽 ↦ ENNReal.ofReal (ρ (logNorm x)))
  have hρ : Continuous ρ := continuous_intervalSobolevDensity' _ _ _
  have hl : MeasurePreserving logNorm ν (volume : Measure ℝ) := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hw : MeasurePreserving logNorm μw η := by
    refine ⟨hl.measurable,?_⟩
    ext X hX
    rw [Measure.map_apply hl.measurable hX,withDensity_apply _ (hl.measurable hX),withDensity_apply _ hX]
    exact hl.setLIntegral_comp_preimage hX hρ.measurable.ennreal_ofReal
  let v (x : C𝔽) := (ξ x : ℂ)⁻¹
  have hv : Continuous v := (continuous_subtype_val.comp ξ.continuous).inv₀ fun x ↦ Circle.coe_ne_zero _
  have hvn (x : C𝔽) : ‖v x‖ = 1 := by simp [v]
  obtain ⟨U,hU⟩ := sobolev_unitary_mul μw v hv.measurable hvn
  let T := Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ logNorm hw
  let V := U.comp T.toContinuousLinearMap
  have hUV (f : Lp ℂ 2 η) : ‖V f‖ = ‖f‖ := by
    have he : ‖U (T f)‖ = ‖T f‖ := by
      rw [Lp.norm_def,Lp.norm_def]
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      filter_upwards [hU (T f)] with x hx
      rw [hx,norm_mul,hvn,one_mul]
    exact he.trans (T.norm_map f)
  let I : Lp ℂ 2 η →ₗᵢ[ℂ] Lp ℂ 2 μw := {V.toLinearMap with norm_map' := hUV}
  have hclosed : IsClosed (range V) := I.isometry.isClosedEmbedding.isClosed_range
  let E := globalThetaAmbient_equiv_canonical (F := F) hm𝔽 (-α) α s
  let B := E.choose
  let L : Ws(α, s) →L[ℂ] W(-α, α, s) := B.symm.toContinuousLinearMap.comp V
  have hBV (f : Ws(α, s)) : B (L f) = V f := B.apply_symm_apply _
  have heq : range L = B ⁻¹' range V := by
    ext y
    constructor
    · rintro ⟨f,rfl⟩
      exact ⟨f,(hBV f).symm⟩
    · rintro ⟨f,hf⟩
      exact ⟨f,B.injective ((hBV f).trans hf)⟩
  refine ⟨L, heq ▸ hclosed.preimage B.continuous,fun f ↦ ?_⟩
  have habs : ν ≪ μw := withDensity_absolutelyContinuous' (hρ.measurable.comp hl.measurable).ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos _ _ _ _)).ne')
  have hBrep := (E.choose_spec (L f)).1.symm
  rw [show E.choose (L f) = V f from hBV f] at hBrep
  apply hBrep.trans
  apply (Measure.absolutelyContinuous_isHaarMeasure μ𝔽 nuTheta).ae_eq
  apply habs.ae_eq
  filter_upwards [hU (T f), Lp.coeFn_compMeasurePreserving (f : Lp ℂ 2 η) hw] with x h₁ h₂
  exact h₁.trans (congrArg (v x * ·) h₂)

/-- The logarithm of the idèle norm is measure preserving for normalized
modulated Haar measure. Inverse-character pullback sends the radial scalar
space continuously onto a closed subspace of the Tamagawa Sobolev space. -/
theorem exists_normalized_idele_log_haar_and_radial_lift (ψ : PontryaginDual C𝔽) (α s : ℝ) :
    ∃ (ν : Measure C𝔽) (_ : ν.IsHaarMeasure), MeasurePreserving logNorm ν volume ∧
      ∃ L : Ws(α, s) →L[ℂ] W(-α, α, s), IsClosed (range L) ∧
        ∀ f, (L f : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (ψ x : ℂ)⁻¹ * f (logNorm x) :=
  ⟨nuTheta, thetaStripCanonicalHaar, sobolev_log_preserving m𝔽 hm𝔽 hms𝔽,
    stripAngular_closed_radial ψ α s⟩

private theorem stripAngular_radial_eigen (χ : PontryaginDual C𝔽) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (f : Ws(α, s)) (y : W(-α, α, s))
    (hy : (y : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ x : ℂ)⁻¹ * f (logNorm x)) (k : C₁) :
    hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs k.val y = (χ k.val : ℂ) • y := by
  have ha : μ𝔽 ≪ (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm x))) :=
    withDensity_absolutelyContinuous' (((continuous_intervalSobolevDensity' (-α) α s).measurable.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).measurable.log).ennreal_ofReal.aemeasurable)
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos _ _ _ _)).ne')
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have hsml := ha.ae_eq (Lp.coeFn_smul (χ k.val : ℂ) y)
  have hpre := (measurePreserving_mul_left μ𝔽 k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hy
  filter_upwards [hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs k.val y,hpre,hy,hsml] with x h₁ h₂ h₃ h₄
  refine h₁.trans (h₂.trans (h₄.symm ▸ ?_))
  change (χ (k.val⁻¹*x) : ℂ)⁻¹ * f (logNorm (k.val⁻¹*x)) = (χ k.val : ℂ) * y x
  have hM : ideleClassNorm F (k.val⁻¹*x) = ideleClassNorm F x := by rw [map_mul,map_inv,k.property,inv_one,one_mul]
  change (χ (k.val⁻¹*x) : ℂ)⁻¹ * f (Real.log (((ideleClassNorm F (k.val⁻¹*x)).val):ℝ)) = _
  rw [hM,h₃,map_mul,map_inv,Circle.coe_mul,Circle.coe_inv,mul_inv_rev,inv_inv]
  ring

private theorem stripAngular_raw_normOne (χ : PontryaginDual C𝔽) (b t : ℝ) (n : ℕ) (g : C₁) (x : C𝔽) :
    spectralZeroJet χ b t n (g.val*x) = (χ g.val : ℂ) * spectralZeroJet χ b t n x := by
  have hm : ideleClassNorm F (g.val*x) = ideleClassNorm F x := by rw [map_mul,g.property,one_mul]
  have hl : logIdeleClassNorm F (g.val*x) = logIdeleClassNorm F x := congrArg (fun z : ℝ≥0ˣ ↦ Real.log (z.val : ℝ)) hm
  rw [stripProfile_jet,stripProfile_jet,hl,map_mul,Circle.coe_mul]
  ring

private theorem stripAngular_integral_eigen {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (r f : G → ℂ) (g : G) (c : ℂ)
    (hr : ∀ x, r (g*x) = c*r x) :
    (∫ x, f (g⁻¹*x)*r x ∂μ) = c*∫ x, f x*r x ∂μ := by
  rw [← integral_const_mul]
  refine (integral_mul_left_eq_self (μ := μ) (fun x ↦ f (g⁻¹*x)*r x) g).symm.trans ?_
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change f (g⁻¹*(g*x))*r (g*x) = c*(f x*r x)
  rw [inv_mul_cancel_left,hr]
  ring

private theorem stripAngular_jet_normOne_dual (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s) :
    ∃ Λ : StrongDual ℂ W(-α, α, s),
      (∀ u, Λ u = spectralSobolevPairing u (uJet(χ, hα, hs, j))) ∧
      ∀ (g : C₁) u, Λ (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g.val u) = (j.val.1 g : ℂ)*Λ u := by
  let v : W'(-α, α, s) := uJet(χ, hα, hs, j)
  let T := (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-α) α s (neg_le_self hα) hs).exists.choose
  let Λ := T.symm v
  have hp (y : W(-α, α, s)) : Λ y = spectralSobolevPairing y v :=
    (spectralSobolevPairing_dual (neg_le_self hα) hs Λ y).2.trans (congrArg (spectralSobolevPairing y) (T.apply_symm_apply v))
  have habs : μ𝔽 ≪ L2μ'(-α, α, s) :=
    withDensity_absolutelyContinuous' (symmIntervalSobolevDensity_inv_continuous hα s).measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (symmIntervalSobolevDensity_pos hα s (logNorm g))))
  have hrep : (v : C𝔽 → ℂ) =ᵐ[μ𝔽] stripJet(χ, j) := habs.ae_le (MemLp.coeFn_toLp _)
  have hΛ (y : W(-α, α, s)) : Λ y = ∫ x, y x*stripJet(χ, j) x ∂μ𝔽 := (hp y).trans (integral_congr_ae (EventuallyEq.rfl.mul hrep))
  refine ⟨Λ,hp,fun g y ↦ ?_⟩
  rw [hΛ,hΛ]
  have he : χ j.val.1 g.val = j.val.1 g := DFunLike.congr_fun (hχ _) g
  rw [←he]
  have htr := hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g.val y
  exact (integral_congr_ae (htr.mul EventuallyEq.rfl)).trans
    (stripAngular_integral_eigen μ𝔽 (stripJet(χ, j)) y g.val _ (stripAngular_raw_normOne _ _ _ _ g))

/-- The reverse common-kernel inclusion on a strip follows from its matching
admitted moments for each inverse-character radial Sobolev vector. -/
theorem spectralStripJet_reverse_of_radial_lifts (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hpure : ∀ (ω : PontryaginDual C₁) (f : Ws(α, s)) (v : W(-α, α, s)),
      ((v : C𝔽 → ℂ) =ᵐ[μ𝔽] fun x ↦ (χ ω x : ℂ)⁻¹ * f (logNorm x)) →
      (∀ j : SpectralStripJetIndex χ a α s, j.val.1 = ω → spectralSobolevPairing v (uJet(χ, hα, hs, j)) = 0) →
      v ∈ Θ(a, neg_le_self hα, hs))
    (y : W(-α, α, s)) (hy : ∀ j : SpectralStripJetIndex χ a α s, spectralSobolevPairing y (uJet(χ, hα, hs, j)) = 0) :
    y ∈ Θ(a, neg_le_self hα, hs) := by
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let κ : Measure C₁ := Measure.haar
  let : κ.IsHaarMeasure := inferInstanceAs (Measure.haar (G := C₁)).IsHaarMeasure
  let τ := (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs).comp (ideleClassNorm F).ker.subtype
  have hτ : Continuous (fun p : C₁ × W(-α, α, s) ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs).choose_spec.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let J := SpectralStripJetIndex χ a α s
  choose L hclosed hrep using fun ξ : PontryaginDual C₁ ↦ stripAngular_closed_radial (χ ξ) α s
  let R (ξ : PontryaginDual C₁) := (L ξ).toLinearMap.range
  choose Λ hΛ hΛg using fun j : J ↦ stripAngular_jet_normOne_dual χ hχ hα hs j
  apply stripAngular_compact_assembly κ τ hτ R hclosed _ _ (fun j : J ↦ j.val.1) Λ hΛg
    _ (Submodule.isClosed_topologicalClosure _) _ y (fun j ↦ (hΛ j y).trans (hy j))
  · rintro ξ _ ⟨f,rfl⟩ g
    change hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g.val _ = _
    have hξ := DFunLike.congr_fun (hχ ξ) g
    exact (stripAngular_radial_eigen (χ ξ) hα hs f _ (hrep ξ f) g).trans
      (congrArg (fun z : Circle ↦ (z : ℂ) • L ξ f) hξ)
  · intro V hV hRV
    apply stripTail_angular_total χ hχ hα hs V hV
    intro ξ f z hz
    have h : L ξ f = z := Lp.ext ((withDensity_absolutelyContinuous μ𝔽 _).ae_eq ((hrep ξ f).trans hz.symm))
    exact h ▸ hRV ξ (LinearMap.mem_range_self _ _)
  · rintro ξ z ⟨f,hf⟩ hz
    subst z
    exact hpure ξ f _ (hrep ξ f) (fun j hj ↦ (hΛ j _).symm.trans (hz j hj))

end RiemannMasullo
