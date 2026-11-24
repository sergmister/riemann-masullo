module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.GDelta
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # §8.2. Stack-theoretic periodic orbits and fixed points

The parameter `S` records the finite part of the paper's set of places. Every
infinite place is already included in `SAdeleRing`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField TopologicalSpace Topology
open scoped NNReal NumberField.AdeleRing

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "N₁" => MonoidHom.ker (ideleNorm F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point $e_v$ has zero at $v$
and one elsewhere. The index `none` denotes the ordinary base point 1. -/
def adeleOrbitBasepoint : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) → 𝔸[F]
  | none => 1
  | some (.inl v) => AdeleRing.ofCompletion (𝓞 F) F v 0
  | some (.inr v) => AdeleRing.ofAdicCompletion (𝓞 F) F v 0

/-- Paper: Definition 8.2.0.1(1), p. 384. Coordinate formulas for the global base points. -/
theorem adeleOrbitBasepoint_coordinates :
    adeleOrbitBasepoint F none = 1 ∧
      (∀ v : InfinitePlace F,
        (adeleOrbitBasepoint F (some (.inl v))).1 v = 0 ∧
        (∀ w : InfinitePlace F, w ≠ v → (adeleOrbitBasepoint F (some (.inl v))).1 w = 1) ∧
        (adeleOrbitBasepoint F (some (.inl v))).2 = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        (adeleOrbitBasepoint F (some (.inr v))).1 = 1 ∧
        (adeleOrbitBasepoint F (some (.inr v))).2 v = 0 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
          (adeleOrbitBasepoint F (some (.inr v))).2 w = 1) := by
  classical
  refine ⟨rfl, ?_, ?_⟩
  · intro v
    refine ⟨?_, ?_, rfl⟩
    · show Pi.mulSingle v (0 : v.Completion) v = 0
      exact Pi.mulSingle_eq_same v 0
    · intro w hw
      show Pi.mulSingle v (0 : v.Completion) w = 1
      exact Pi.mulSingle_eq_of_ne hw 0
  · intro v
    refine ⟨rfl, ?_, ?_⟩
    · show Pi.mulSingle v (0 : v.adicCompletion F) v = 0
      exact Pi.mulSingle_eq_same v 0
    · intro w hw
      show Pi.mulSingle v (0 : v.adicCompletion F) w = 1
      exact Pi.mulSingle_eq_of_ne hw 0

/-- Paper: Definition 8.2.0.1(1), p. 384. The S-local base points keep all infinite
places and the finite places in S. -/
def sAdeleOrbitBasepoint (i : Option (InfinitePlace F ⊕ S)) : Aₛ :=
  adeleProjection F S (adeleOrbitBasepoint F (i.map (Sum.map id Subtype.val)))

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point at a selected finite place
has zero at that place, including after projection to the S-adeles. -/
theorem sAdeleOrbitBasepoint_finite (v : S) :
    (sAdeleOrbitBasepoint F S (some (.inr v))).2 v = 0 := by
  exact ((adeleOrbitBasepoint_coordinates F).2.2 v.val).2.1

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_{F,S}$ in (8.2.0.1)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def sAdeleOrbitBasepoints : Set Aₛ :=
  Set.range (sAdeleOrbitBasepoint F S)

/-- The index `none` gives the ordinary base point, since the projection is a ring hom. -/
private theorem sAdeleOrbitBasepoint_none : sAdeleOrbitBasepoint F S none = 1 := by
  simp [sAdeleOrbitBasepoint, adeleOrbitBasepoint]

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_{F,S}$. -/
theorem one_mem_sAdeleOrbitBasepoints : 1 ∈ sAdeleOrbitBasepoints F S :=
  ⟨none, sAdeleOrbitBasepoint_none F S⟩

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_F$ in (8.2.0.2)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def adeleOrbitBasepoints : Set 𝔸[F] :=
  Set.range (adeleOrbitBasepoint F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_F$. -/
theorem one_mem_adeleOrbitBasepoints : 1 ∈ adeleOrbitBasepoints F :=
  ⟨none, rfl⟩

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.3) consists of the
S-local full-idele orbits with their adelic subspace topologies. -/
def sAdeleFullOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit 𝕀ₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary S-local orbit consists of
the $S$-adeles that are units. -/
theorem mem_sAdeleFullOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbit F S none ↔ IsUnit x := by
  rw [sAdeleFullOrbit, sAdeleOrbitBasepoint_none F S, MulAction.mem_orbit_iff]
  simp only [Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.4) consists of the
global full-idele orbits with their adelic subspace topologies. -/
def adeleFullOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) : Set 𝔸[F] :=
  MulAction.orbit 𝔸[F]ˣ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary global orbit consists of
the adeles that are units. -/
theorem mem_adeleFullOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbit F none ↔ IsUnit x := by
  have h1 : adeleOrbitBasepoint F none = 1 := rfl
  rw [adeleFullOrbit, h1, MulAction.mem_orbit_iff]
  simp only [Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local set $D_{F,S}$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def sAdeleFullOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleFullOrbit F S i

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local full-orbit union is the
set of translates of the special S-adeles by full ideles. -/
theorem mem_sAdeleFullOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbitUnion F S ↔
      ∃ (g : 𝕀ₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  simp only [sAdeleFullOrbitUnion, Set.mem_iUnion, sAdeleFullOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Definition 8.2.0.1(3), p. 385. The global set $D_F$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def adeleFullOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleFullOrbit F i

/-- Paper: Definition 8.2.0.1(3), p. 385. The global full-orbit union is the
set of translates of the special adeles by full ideles. -/
theorem mem_adeleFullOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbitUnion F ↔
      ∃ (g : 𝔸[F]ˣ) (z : adeleOrbitBasepoints F), g • z.val = x := by
  simp only [adeleFullOrbitUnion, Set.mem_iUnion, adeleFullOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

-- Read the full-group stability sentence on p. 385 with (8.2.0.3)–(8.2.0.5).
-- The norm-one orbits in (8.2.0.6)–(8.2.0.8) are stable under the norm kernel.

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.6) consists of the
S-local norm-one orbits with their adelic subspace topologies. -/
def sAdeleNormOneOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit Nₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary S-local norm-one orbit
is the image of the norm kernel in the S-adeles. -/
theorem mem_sAdeleNormOneOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbit F S none ↔
      ∃ g : 𝕀ₛ, sIdeleNorm F S g = 1 ∧ g.val = x := by
  rw [sAdeleNormOneOrbit, sAdeleOrbitBasepoint_none F S, MulAction.mem_orbit_iff]
  simp only [MulAction.subgroup_smul_def, Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, MonoidHom.mem_ker.mp g.property, hg⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, MonoidHom.mem_ker.mpr hg⟩, rfl⟩

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.7) consists of the
global norm-one orbits with their adelic subspace topologies. -/
def adeleNormOneOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) :
    Set 𝔸[F] :=
  MulAction.orbit N₁ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary global norm-one orbit is the
image of the norm kernel in the adeles. -/
theorem mem_adeleNormOneOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbit F none ↔ ∃ g : 𝔸[F]ˣ, ideleNorm F g = 1 ∧ g.val = x := by
  have h1 : adeleOrbitBasepoint F none = 1 := rfl
  rw [adeleNormOneOrbit, h1, MulAction.mem_orbit_iff]
  simp only [MulAction.subgroup_smul_def, Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, MonoidHom.mem_ker.mp g.property, hg⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, MonoidHom.mem_ker.mpr hg⟩, rfl⟩

/-- Paper: Definition 8.2.0.2(2), p. 385. The S-local set $D^1_{F,S}$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def sAdeleNormOneOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleNormOneOrbit F S i

/-- Paper: Definition 8.2.0.2(2), p. 385. An S-adele lies in the union exactly when
it is a norm-one translate of a special S-adele. -/
theorem mem_sAdeleNormOneOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbitUnion F S ↔
      ∃ (g : Nₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  simp only [sAdeleNormOneOrbitUnion, Set.mem_iUnion, sAdeleNormOneOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Definition 8.2.0.2(2), p. 385. The global set $D^1_F$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def adeleNormOneOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleNormOneOrbit F i

/-- Paper: Definition 8.2.0.2(2), p. 385. An adele lies in the union exactly when
it is a norm-one translate of a special adele. -/
theorem mem_adeleNormOneOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbitUnion F ↔
      ∃ (g : N₁) (z : adeleOrbitBasepoints F), g • z.val = x := by
  simp only [adeleNormOneOrbitUnion, Set.mem_iUnion, adeleNormOneOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The S-local orbit map applies the norm-one
idele to the given special S-adele. -/
def sAdeleNormOneOrbitMap (gz : Nₛ × sAdeleOrbitBasepoints F S) :
    sAdeleNormOneOrbitUnion F S :=
  ⟨gz.1 • gz.2.val, (mem_sAdeleNormOneOrbitUnion_iff F S _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The underlying S-adele of the orbit map
is given by the norm-one action. -/
theorem sAdeleNormOneOrbitMap_val (g : Nₛ) (z : sAdeleOrbitBasepoints F S) :
    (sAdeleNormOneOrbitMap F S (g, z)).val = g • z.val := by
  rfl

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map applies the norm-one
idele to the given special adele. -/
def adeleNormOneOrbitMap (gz : N₁ × adeleOrbitBasepoints F) : adeleNormOneOrbitUnion F :=
  ⟨gz.1 • gz.2.val, (mem_adeleNormOneOrbitUnion_iff F _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(2), p. 385. The underlying adele of the orbit map is
given by the norm-one action. -/
theorem adeleNormOneOrbitMap_val (g : N₁) (z : adeleOrbitBasepoints F) :
    (adeleNormOneOrbitMap F (g, z)).val = g • z.val := by
  rfl

/-- The coordinates of an S-local base point: zero at its own place and one elsewhere. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_coord (k : Option (InfinitePlace F ⊕ S)) :
    (∀ w : InfinitePlace F, (k = some (.inl w) → (sAdeleOrbitBasepoint F S k).1 w = 0) ∧
      (k ≠ some (.inl w) → (sAdeleOrbitBasepoint F S k).1 w = 1)) ∧
    ∀ v : S, (k = some (.inr v) → (sAdeleOrbitBasepoint F S k).2 v = 0) ∧
      (k ≠ some (.inr v) → (sAdeleOrbitBasepoint F S k).2 v = 1) := by
  obtain ⟨-, hinl, hinr⟩ := adeleOrbitBasepoint_coordinates F
  have h1 (k : Option (InfinitePlace F ⊕ S)) (w : InfinitePlace F) :
      (sAdeleOrbitBasepoint F S k).1 w =
        (adeleOrbitBasepoint F (k.map (Sum.map id Subtype.val))).1 w := rfl
  have h2 (k : Option (InfinitePlace F ⊕ S)) (v : S) :
      (sAdeleOrbitBasepoint F S k).2 v =
        (adeleOrbitBasepoint F (k.map (Sum.map id Subtype.val))).2 v.val := rfl
  rcases k with _ | w₀ | v₀
  · exact ⟨fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩, fun v ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩⟩
  · refine ⟨fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun v ↦ ⟨fun h ↦ (by cases h), fun _ ↦ ?_⟩⟩
    · cases h
      rw [h1]
      exact (hinl _).1
    · rw [h1]
      exact (hinl w₀).2.1 w (fun e ↦ h (e ▸ rfl))
    · rw [h2]
      change (adeleOrbitBasepoint F (some (.inl w₀))).2 v.val = 1
      rw [(hinl w₀).2.2]
      rfl
  · refine ⟨fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ ?_⟩, fun v ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · rw [h1]
      change (adeleOrbitBasepoint F (some (.inr v₀.val))).1 w = 1
      rw [(hinr v₀.val).1]
      rfl
    · cases h
      rw [h2]
      exact (hinr _).2.1
    · rw [h2]
      exact (hinr v₀.val).2.2 v.val (fun e ↦ h (congrArg (some ∘ Sum.inr) (Subtype.ext e).symm))

/-- The coordinates of an S-idele are nonzero. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_ne_zero (g : 𝕀ₛ) :
    (∀ w : InfinitePlace F, g.val.1 w ≠ 0) ∧ ∀ v : S, g.val.2 v ≠ 0 :=
  ⟨fun w ↦ ((g.isUnit.map (RingHom.fst _ _)).map (Pi.evalRingHom _ w)).ne_zero,
    fun v ↦ ((g.isUnit.map (RingHom.snd _ _)).map (Pi.evalRingHom _ v)).ne_zero⟩

/-- An S-adele whose coordinates are all nonzero is a unit. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_isUnit (y : Aₛ)
    (h1 : ∀ w : InfinitePlace F, y.1 w ≠ 0) (h2 : ∀ v : S, y.2 v ≠ 0) : IsUnit y :=
  Prod.isUnit_iff.mpr ⟨(Pi.isUnit_iff (x := (y.1 : (w : InfinitePlace F) → w.Completion))).mpr
    fun w ↦ (h1 w).isUnit, Pi.isUnit_iff.mpr fun v ↦ (h2 v).isUnit⟩

/-- The S-idelic norm is the product of the normalized local norms. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_norm (g : 𝕀ₛ) :
    ((sIdeleNorm F S g : ℝ≥0)) =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖₊ := by
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]
  rfl

/-- A point of the S-local union with no zero coordinate other than at `c`, and with norm
product less than one, lies in the orbit of the base point at `c`. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_piece (y : Aₛ)
    (hy : y ∈ sAdeleNormOneOrbitUnion F S) (c : InfinitePlace F ⊕ S)
    (hne1 : ∀ w : InfinitePlace F, Sum.inl w ≠ c → y.1 w ≠ 0)
    (hne2 : ∀ v : S, Sum.inr v ≠ c → y.2 v ≠ 0)
    (hP : (∏ w : InfinitePlace F, ‖y.1 w‖₊ ^ w.mult) * ∏ v : S, ‖y.2 v‖₊ < 1) :
    ∃ h : Nₛ, h • sAdeleOrbitBasepoint F S (some c) = y := by
  simp only [sAdeleNormOneOrbitUnion, Set.mem_iUnion, sAdeleNormOneOrbit,
    MulAction.mem_orbit_iff] at hy
  obtain ⟨i, h, rfl⟩ := hy
  have hco := sAdeleNormOneOrbitMap_isQuotientMap_coord F S
  rcases i with _ | d
  · exfalso
    have hval : h • sAdeleOrbitBasepoint F S none = h.val.val := by
      change h.val.val * sAdeleOrbitBasepoint F S none = _
      rw [sAdeleOrbitBasepoint_none, mul_one]
    rw [hval, ← sAdeleNormOneOrbitMap_isQuotientMap_norm,
      MonoidHom.mem_ker.mp h.property, Units.val_one] at hP
    exact lt_irrefl _ hP
  · by_cases hdc : d = c
    · exact ⟨h, by rw [hdc]⟩
    · exfalso
      rcases d with w | v
      · apply hne1 w hdc
        change h.val.val.1 w * (sAdeleOrbitBasepoint F S (some (.inl w))).1 w = 0
        rw [((hco _).1 w).1 rfl, mul_zero]
      · apply hne2 v hdc
        change h.val.val.2 v * (sAdeleOrbitBasepoint F S (some (.inr v))).2 v = 0
        rw [((hco _).2 v).1 rfl, mul_zero]

/-- A point of the S-local union with no zero coordinate is a norm-one S-idele. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_unit (y : Aₛ)
    (hy : y ∈ sAdeleNormOneOrbitUnion F S)
    (hne1 : ∀ w : InfinitePlace F, y.1 w ≠ 0) (hne2 : ∀ v : S, y.2 v ≠ 0) :
    ∃ h : Nₛ, h.val.val = y := by
  simp only [sAdeleNormOneOrbitUnion, Set.mem_iUnion, sAdeleNormOneOrbit,
    MulAction.mem_orbit_iff] at hy
  obtain ⟨i, h, rfl⟩ := hy
  have hco := sAdeleNormOneOrbitMap_isQuotientMap_coord F S
  rcases i with _ | d
  · refine ⟨h, ?_⟩
    change _ = h.val.val * sAdeleOrbitBasepoint F S none
    rw [sAdeleOrbitBasepoint_none, mul_one]
  · exfalso
    rcases d with w | v
    · apply hne1 w
      change h.val.val.1 w * (sAdeleOrbitBasepoint F S (some (.inl w))).1 w = 0
      rw [((hco _).1 w).1 rfl, mul_zero]
    · apply hne2 v
      change h.val.val.2 v * (sAdeleOrbitBasepoint F S (some (.inr v))).2 v = 0
      rw [((hco _).2 v).1 rfl, mul_zero]

/-- Near a norm-one S-idele, every point of the S-local union is a norm-one S-idele lying in
any given neighborhood: the S-ideles are open in the S-adeles, and the other orbits have a
zero coordinate. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_nhds_none (g : Nₛ) (U : Set Aₛ)
    (hU : U ∈ 𝓝 (g.val.val)) :
    ∃ t ∈ 𝓝 (g • sAdeleOrbitBasepoint F S none),
      ∀ y ∈ sAdeleNormOneOrbitUnion F S, y ∈ t →
        ∃ h : Nₛ, h.val.val ∈ U ∧ h • sAdeleOrbitBasepoint F S none = y := by
  have hx : g • sAdeleOrbitBasepoint F S none = g.val.val := by
    change g.val.val * sAdeleOrbitBasepoint F S none = _
    rw [sAdeleOrbitBasepoint_none, mul_one]
  obtain ⟨hg1, hg2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_ne_zero F S g.val
  have hev : ∀ᶠ y in 𝓝 (g.val.val), y ∈ U ∧ (∀ w : InfinitePlace F, y.1 w ≠ 0) ∧
      ∀ v : S, y.2 v ≠ 0 := by
    refine Filter.Eventually.and hU (Filter.Eventually.and ?_ ?_)
    · exact Filter.eventually_all.mpr fun w ↦
        ((continuous_apply w).comp continuous_fst).continuousAt.eventually_ne (hg1 w)
    · exact Filter.eventually_all.mpr fun v ↦
        ((continuous_apply v).comp continuous_snd).continuousAt.eventually_ne (hg2 v)
  rw [hx]
  obtain ⟨t, ht, htp⟩ := hev.exists_mem
  refine ⟨t, ht, fun y hy hyt ↦ ?_⟩
  obtain ⟨hyU, hy1, hy2⟩ := htp y hyt
  obtain ⟨h, rfl⟩ := sAdeleNormOneOrbitMap_isQuotientMap_unit F S y hy hy1 hy2
  refine ⟨h, hyU, ?_⟩
  change h.val.val * sAdeleOrbitBasepoint F S none = _
  rw [sAdeleOrbitBasepoint_none, mul_one]

/-- Near a point of the orbit of the base point at a finite place `v₀`, every point of the
S-local union is the translate of that base point by a norm-one S-idele lying in any given
neighborhood of the original one. The coordinate at `v₀` can be kept, because the norm of a
finite completion changes by a factor of at least two. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_nhds_inr (v₀ : S) (g : Nₛ) (U : Set Aₛ)
    (hU : U ∈ 𝓝 (g.val.val)) :
    ∃ t ∈ 𝓝 (g • sAdeleOrbitBasepoint F S (some (.inr v₀))),
      ∀ y ∈ sAdeleNormOneOrbitUnion F S, y ∈ t →
        ∃ h : Nₛ, h.val.val ∈ U ∧ h • sAdeleOrbitBasepoint F S (some (.inr v₀)) = y := by
  classical
  have hco := sAdeleNormOneOrbitMap_isQuotientMap_coord F S (some (.inr v₀))
  let e := sAdeleOrbitBasepoint F S (some (.inr v₀))
  have he1 (w : InfinitePlace F) : e.1 w = 1 := (hco.1 w).2 (by simp)
  have he2 (v : S) : e.2 v = if v = v₀ then 0 else 1 := by
    split_ifs with hv
    · exact (hco.2 v).1 (by rw [hv])
    · exact (hco.2 v).2 (fun h ↦ hv (Sum.inr_injective (Option.some_injective _ h)).symm)
  -- Coordinates of a translate of the base point.
  have hsmul1 (k : Nₛ) (w : InfinitePlace F) : (k • e).1 w = k.val.val.1 w := by
    change k.val.val.1 w * e.1 w = _
    rw [he1, mul_one]
  have hsmul2 (k : Nₛ) (v : S) : (k • e).2 v = if v = v₀ then 0 else k.val.val.2 v := by
    change k.val.val.2 v * e.2 v = _
    rw [he2]
    split_ifs <;> simp
  let P : Aₛ → ℝ≥0 := fun y ↦ (∏ w : InfinitePlace F, ‖y.1 w‖₊ ^ w.mult) * ∏ v : S, ‖y.2 v‖₊
  let Q : Aₛ → ℝ≥0 := fun y ↦
    (∏ w : InfinitePlace F, ‖y.1 w‖₊ ^ w.mult) * ∏ v ∈ Finset.univ.erase v₀, ‖y.2 v‖₊
  have hPQ (y : Aₛ) : P y = ‖y.2 v₀‖₊ * Q y := by
    simp only [P, Q]
    rw [← Finset.mul_prod_erase Finset.univ (fun v ↦ ‖y.2 v‖₊) (Finset.mem_univ v₀)]
    ring
  -- `Q` only sees the coordinates away from `v₀`.
  have hQ (y z : Aₛ) (h1 : ∀ w, y.1 w = z.1 w) (h2 : ∀ v, v ≠ v₀ → y.2 v = z.2 v) :
      Q y = Q z := by
    simp only [Q]
    congr 1
    · exact Finset.prod_congr rfl fun w _ ↦ by rw [h1]
    · exact Finset.prod_congr rfl fun v hv ↦ by rw [h2 v (Finset.ne_of_mem_erase hv)]
  have hQcont : Continuous Q := by
    simp only [Q]
    fun_prop
  have hnorm (k : Nₛ) : P k.val.val = 1 := by
    have := sAdeleNormOneOrbitMap_isQuotientMap_norm F S k.val
    rw [MonoidHom.mem_ker.mp k.property, Units.val_one] at this
    exact this.symm
  let x := g • e
  let g₀ := g.val.val.2 v₀
  obtain ⟨hg1, hg2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_ne_zero F S g.val
  let H : Aₛ → Aₛ := fun y ↦ (y.1, Function.update y.2 v₀ g₀)
  have hHcont : Continuous H := continuous_fst.prodMk (continuous_snd.update v₀ continuous_const)
  have hHx : H x = g.val.val := by
    refine Prod.ext (funext fun w ↦ hsmul1 g w) (funext fun v ↦ ?_)
    by_cases hv : v = v₀
    · subst hv
      exact Function.update_self _ _ _
    · change Function.update x.2 v₀ g₀ v = _
      rw [Function.update_of_ne hv, hsmul2, ite_eq_right hv]
  have hQx : ‖g₀‖₊ * Q x = 1 := by
    rw [hQ x g.val.val (hsmul1 g) (fun v hv ↦ by rw [hsmul2, ite_eq_right hv]), ← hPQ, hnorm]
  have hPx : P x = 0 := by
    rw [hPQ, show x.2 v₀ = 0 by rw [hsmul2, ite_eq_left rfl], nnNorm_zero, zero_mul]
  have hev : ∀ᶠ y in 𝓝 x, H y ∈ U ∧ (∀ w : InfinitePlace F, y.1 w ≠ 0) ∧
      (∀ v : S, v ≠ v₀ → y.2 v ≠ 0) ∧ P y < 1 ∧
      (1 / 2 < ‖g₀‖₊ * Q y ∧ ‖g₀‖₊ * Q y < 2) := by
    refine Filter.Eventually.and (hHcont.continuousAt.preimage_mem_nhds (by rwa [hHx]))
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))
    · refine Filter.eventually_all.mpr fun w ↦
        ((continuous_apply w).comp continuous_fst).continuousAt.eventually_ne ?_
      change x.1 w ≠ 0
      rw [hsmul1]
      exact hg1 w
    · refine Filter.eventually_all.mpr fun v ↦ ?_
      by_cases hv : v = v₀
      · exact Filter.Eventually.of_forall fun y h ↦ absurd hv h
      · refine (((continuous_apply v).comp continuous_snd).continuousAt.eventually_ne ?_).mono
          fun y hy _ ↦ hy
        change x.2 v ≠ 0
        rw [hsmul2, ite_eq_right hv]
        exact hg2 v
    · have hPcont : Continuous P := by
        simp only [P]
        fun_prop
      exact hPcont.continuousAt.eventually_lt continuousAt_const (by rw [hPx]; exact one_pos)
    · have hc : Continuous fun y ↦ ‖g₀‖₊ * Q y := continuous_const.mul hQcont
      refine (hc.continuousAt.eventually_lt continuousAt_const ?_).and
        (continuousAt_const.eventually_lt hc.continuousAt ?_) |>.mono fun y hy ↦ ⟨hy.2, hy.1⟩
      · rw [hQx]
        norm_num
      · rw [hQx]
        norm_num
  obtain ⟨t, ht, htp⟩ := hev.exists_mem
  refine ⟨t, ht, fun y hyD hyt ↦ ?_⟩
  obtain ⟨hyU, hy1, hy2, hyP, hyr1, hyr2⟩ := htp y hyt
  obtain ⟨h, rfl⟩ := sAdeleNormOneOrbitMap_isQuotientMap_piece F S y hyD (.inr v₀)
    (fun w _ ↦ hy1 w) (fun v hv ↦ hy2 v (fun e ↦ hv (e ▸ rfl))) hyP
  -- The norm at `v₀` of the new idele equals that of `g`.
  let h₀ := h.val.val.2 v₀
  obtain ⟨-, hh2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_ne_zero F S h.val
  have hQh : Q (h • e) = Q h.val.val :=
    hQ _ _ (hsmul1 h) (fun v hv ↦ by rw [hsmul2, ite_eq_right hv])
  have hhQ : ‖h₀‖₊ * Q (h • e) = 1 := by rw [hQh, ← hPQ, hnorm]
  have hgh : ‖g₀‖ = ‖h₀‖ := by
    have hr1 : (1 / 2 : ℝ) < ‖g₀‖ * (Q (h • e) : ℝ) := by
      have := NNReal.coe_lt_coe.mpr hyr1
      push_cast at this
      exact this
    have hr2 : ‖g₀‖ * (Q (h • e) : ℝ) < 2 := by
      have := NNReal.coe_lt_coe.mpr hyr2
      push_cast at this
      exact this
    have hh : ‖h₀‖ * (Q (h • e) : ℝ) = 1 := by
      have := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) hhQ
      push_cast at this
      exact this
    have hh0 : 0 < ‖h₀‖ := norm_pos_iff.mpr (hh2 v₀)
    have hg0 : 0 < ‖g₀‖ := norm_pos_iff.mpr (hg2 v₀)
    rcases lt_trichotomy ‖g₀‖ ‖h₀‖ with hlt | heq | hgt
    · exfalso
      have h1 : 1 < ‖h₀ * g₀⁻¹‖ := by
        rw [norm_mul, norm_inv, ← div_eq_mul_inv, one_lt_div hg0]
        exact hlt
      have h2 := FinitePlace.two_le_norm_of_one_lt_norm (K := F) (v := v₀.val) _ h1
      rw [norm_mul, norm_inv, ← div_eq_mul_inv, le_div_iff₀ hg0] at h2
      nlinarith
    · exact heq
    · exfalso
      have h1 : 1 < ‖g₀ * h₀⁻¹‖ := by
        rw [norm_mul, norm_inv, ← div_eq_mul_inv, one_lt_div hh0]
        exact hgt
      have h2 := FinitePlace.two_le_norm_of_one_lt_norm (K := F) (v := v₀.val) _ h1
      rw [norm_mul, norm_inv, ← div_eq_mul_inv, le_div_iff₀ hh0] at h2
      nlinarith
  -- The modified S-adele is a norm-one S-idele.
  have hH1 (w : InfinitePlace F) : (H (h • e)).1 w ≠ 0 := hy1 w
  have hH2 (v : S) : (H (h • e)).2 v ≠ 0 := by
    by_cases hv : v = v₀
    · subst hv
      change Function.update (h • e).2 v g₀ v ≠ 0
      rw [Function.update_self]
      exact hg2 v
    · change Function.update (h • e).2 v₀ g₀ v ≠ 0
      rw [Function.update_of_ne hv]
      exact hy2 v hv
  have hunit := sAdeleNormOneOrbitMap_isQuotientMap_isUnit F S _ hH1 hH2
  have hHnorm : P (H (h • e)) = 1 := by
    rw [hPQ, hQ (H (h • e)) (h • e) (fun _ ↦ rfl)
      (fun v hv ↦ Function.update_of_ne hv _ _)]
    change ‖Function.update (h • e).2 v₀ g₀ v₀‖₊ * _ = 1
    rw [Function.update_self, ← hhQ]
    congr 1
    exact Subtype.ext hgh
  let k : Nₛ := ⟨hunit.unit, MonoidHom.mem_ker.mpr (Units.ext (by
    rw [sAdeleNormOneOrbitMap_isQuotientMap_norm, Units.val_one]
    exact hHnorm))⟩
  refine ⟨k, hyU, Prod.ext (funext fun w ↦ ?_) (funext fun v ↦ ?_)⟩
  · change (H (h • e)).1 w * e.1 w = (h • e).1 w
    rw [he1, mul_one]
  · change Function.update (h • e).2 v₀ g₀ v * e.2 v = (h • e).2 v
    by_cases hv : v = v₀
    · subst hv
      rw [he2, ite_eq_left rfl, mul_zero, hsmul2, ite_eq_left rfl]
    · rw [Function.update_of_ne hv, he2, ite_eq_right hv, mul_one]

/-- Near a point of the orbit of the base point at an infinite place `w₀`, every point of the
S-local union is the translate of that base point by a norm-one S-idele lying in any given
neighborhood of the original one. The coordinate at `w₀` is rescaled by a positive real
close to one, chosen to bring the S-norm back to one. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_nhds_inl (w₀ : InfinitePlace F) (g : Nₛ)
    (U : Set Aₛ) (hU : U ∈ 𝓝 (g.val.val)) :
    ∃ t ∈ 𝓝 (g • sAdeleOrbitBasepoint F S (some (.inl w₀))),
      ∀ y ∈ sAdeleNormOneOrbitUnion F S, y ∈ t →
        ∃ h : Nₛ, h.val.val ∈ U ∧ h • sAdeleOrbitBasepoint F S (some (.inl w₀)) = y := by
  classical
  have hco := sAdeleNormOneOrbitMap_isQuotientMap_coord F S (some (.inl w₀))
  let e := sAdeleOrbitBasepoint F S (some (.inl w₀))
  have he1 (w : InfinitePlace F) : e.1 w = if w = w₀ then 0 else 1 := by
    split_ifs with hw
    · exact (hco.1 w).1 (by rw [hw])
    · exact (hco.1 w).2 (fun h ↦ hw (Sum.inl_injective (Option.some_injective _ h)).symm)
  have he2 (v : S) : e.2 v = 1 := (hco.2 v).2 (by simp)
  -- Coordinates of a translate of the base point.
  have hsmul1 (k : Nₛ) (w : InfinitePlace F) :
      (k • e).1 w = if w = w₀ then 0 else k.val.val.1 w := by
    change k.val.val.1 w * e.1 w = _
    rw [he1]
    split_ifs <;> simp
  have hsmul2 (k : Nₛ) (v : S) : (k • e).2 v = k.val.val.2 v := by
    change k.val.val.2 v * e.2 v = _
    rw [he2, mul_one]
  have hm : w₀.mult ≠ 0 := InfinitePlace.mult_ne_zero
  let P : Aₛ → ℝ≥0 := fun y ↦ (∏ w : InfinitePlace F, ‖y.1 w‖₊ ^ w.mult) * ∏ v : S, ‖y.2 v‖₊
  let Q : Aₛ → ℝ≥0 := fun y ↦
    (∏ w ∈ Finset.univ.erase w₀, ‖y.1 w‖₊ ^ w.mult) * ∏ v : S, ‖y.2 v‖₊
  have hPQ (y : Aₛ) : P y = ‖y.1 w₀‖₊ ^ w₀.mult * Q y := by
    simp only [P, Q]
    rw [← Finset.mul_prod_erase Finset.univ (fun w ↦ ‖y.1 w‖₊ ^ w.mult) (Finset.mem_univ w₀)]
    ring
  -- `Q` only sees the coordinates away from `w₀`.
  have hQ (y z : Aₛ) (h1 : ∀ w, w ≠ w₀ → y.1 w = z.1 w) (h2 : ∀ v, y.2 v = z.2 v) :
      Q y = Q z := by
    simp only [Q]
    congr 1
    · exact Finset.prod_congr rfl fun w hw ↦ by rw [h1 w (Finset.ne_of_mem_erase hw)]
    · exact Finset.prod_congr rfl fun v _ ↦ by rw [h2]
  have hQcont : Continuous Q := by
    simp only [Q]
    fun_prop
  have hnorm (k : Nₛ) : P k.val.val = 1 := by
    have := sAdeleNormOneOrbitMap_isQuotientMap_norm F S k.val
    rw [MonoidHom.mem_ker.mp k.property, Units.val_one] at this
    exact this.symm
  let x := g • e
  let g₀ := g.val.val.1 w₀
  obtain ⟨hg1, hg2⟩ := sAdeleNormOneOrbitMap_isQuotientMap_ne_zero F S g.val
  have hQx : ‖g₀‖₊ ^ w₀.mult * Q x = 1 := by
    rw [hQ x g.val.val (fun w hw ↦ by rw [hsmul1, ite_eq_right hw]) (hsmul2 g), ← hPQ, hnorm]
  have hQxR : ‖g₀‖ ^ w₀.mult * (Q x : ℝ) = 1 := by
    have := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) hQx
    push_cast at this
    exact this
  have hQx0 : (0 : ℝ) < Q x := by
    refine lt_of_le_of_ne (Q x).coe_nonneg fun h ↦ ?_
    rw [← h, mul_zero] at hQxR
    exact zero_ne_one hQxR
  have hPx : P x = 0 := by
    rw [hPQ, show x.1 w₀ = 0 by rw [hsmul1, ite_eq_left rfl], nnNorm_zero, zero_pow hm,
      zero_mul]
  -- The rescaling factor at `w₀`, a positive real root of `Q x / Q y`.
  let T : Aₛ → ℝ≥0ˣ := fun y ↦ Units.mk0
    ⟨Real.exp (Real.log (Q x : ℝ) - Real.log (Q y : ℝ)), (Real.exp_pos _).le⟩ (NNReal.coe_ne_zero.mp (Real.exp_pos _).ne')
  let μ : Aₛ → w₀.Completion := fun y ↦
    (infinitePlaceRealPower F w₀ (w₀.mult : ℝ)⁻¹ (T y)).val
  have hμ (y : Aₛ) : InfinitePlace.Completion.extensionEmbedding w₀ (μ y) =
      ((Real.exp (Real.log (Q x : ℝ) - Real.log (Q y : ℝ)) ^ (w₀.mult : ℝ)⁻¹ : ℝ) : ℂ) :=
    infinitePlaceRealPower_apply F w₀ _ (T y)
  have hμnorm (y : Aₛ) :
      ‖μ y‖ = Real.exp (Real.log (Q x : ℝ) - Real.log (Q y : ℝ)) ^ (w₀.mult : ℝ)⁻¹ := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w₀).norm_map_of_map_zero
      (map_zero _), hμ, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)]
  have hμx : μ x = 1 := by
    refine (InfinitePlace.Completion.extensionEmbedding w₀).injective ?_
    rw [hμ, map_one, sub_self, Real.exp_zero, Real.one_rpow, Complex.ofReal_one]
  have hμcont : ContinuousAt μ x := by
    rw [(InfinitePlace.Completion.isometry_extensionEmbedding w₀).isEmbedding.isInducing
      |>.continuousAt_iff]
    have hfun : (InfinitePlace.Completion.extensionEmbedding w₀ ∘ μ) = fun y ↦
        ((Real.exp (Real.log (Q x : ℝ) - Real.log (Q y : ℝ)) ^ (w₀.mult : ℝ)⁻¹ : ℝ) : ℂ) :=
      funext hμ
    rw [hfun]
    have hlog : ContinuousAt (fun y : Aₛ ↦ Real.log (Q y : ℝ)) x :=
      (NNReal.continuous_coe.comp hQcont).continuousAt.log hQx0.ne'
    exact Complex.continuous_ofReal.continuousAt.comp
      (((continuousAt_const.sub hlog).rexp).rpow_const (Or.inl (Real.exp_pos _).ne'))
  let H : Aₛ → Aₛ := fun y ↦
    ((Function.update (y.1 : (w : InfinitePlace F) → w.Completion) w₀ (g₀ * μ y) :
      InfiniteAdeleRing F), y.2)
  have hHcont : ContinuousAt H x :=
    (continuous_fst.continuousAt.update w₀ (continuousAt_const.mul hμcont)).prodMk
      continuous_snd.continuousAt
  have hHx : H x = g.val.val := by
    refine Prod.ext (funext fun w ↦ ?_) (funext fun v ↦ hsmul2 g v)
    by_cases hw : w = w₀
    · rw [hw]
      change Function.update (x.1 : (w : InfinitePlace F) → w.Completion) w₀ (g₀ * μ x) w₀ = _
      rw [Function.update_self, hμx, mul_one]
    · change Function.update (x.1 : (w : InfinitePlace F) → w.Completion) w₀ (g₀ * μ x) w = _
      rw [Function.update_of_ne hw, hsmul1, ite_eq_right hw]
  have hev : ∀ᶠ y in 𝓝 x, H y ∈ U ∧ (∀ w : InfinitePlace F, w ≠ w₀ → y.1 w ≠ 0) ∧
      (∀ v : S, y.2 v ≠ 0) ∧ P y < 1 ∧ (0 : ℝ) < Q y := by
    refine Filter.Eventually.and (hHcont.preimage_mem_nhds (by rwa [hHx]))
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))
    · refine Filter.eventually_all.mpr fun w ↦ ?_
      by_cases hw : w = w₀
      · exact Filter.Eventually.of_forall fun y h ↦ absurd hw h
      · refine (((continuous_apply w).comp continuous_fst).continuousAt.eventually_ne ?_).mono
          fun y hy _ ↦ hy
        change x.1 w ≠ 0
        rw [hsmul1, ite_eq_right hw]
        exact hg1 w
    · refine Filter.eventually_all.mpr fun v ↦
        ((continuous_apply v).comp continuous_snd).continuousAt.eventually_ne ?_
      change x.2 v ≠ 0
      rw [hsmul2]
      exact hg2 v
    · have hPcont : Continuous P := by
        simp only [P]
        fun_prop
      exact hPcont.continuousAt.eventually_lt continuousAt_const (by rw [hPx]; exact one_pos)
    · exact continuousAt_const.eventually_lt (NNReal.continuous_coe.comp hQcont).continuousAt
        hQx0
  obtain ⟨t, ht, htp⟩ := hev.exists_mem
  refine ⟨t, ht, fun y hyD hyt ↦ ?_⟩
  obtain ⟨hyU, hy1, hy2, hyP, hyQ⟩ := htp y hyt
  obtain ⟨h, rfl⟩ := sAdeleNormOneOrbitMap_isQuotientMap_piece F S y hyD (.inl w₀)
    (fun w hw ↦ hy1 w (fun e ↦ hw (congrArg Sum.inl e))) (fun v _ ↦ hy2 v) hyP
  -- The rescaled S-adele is a norm-one S-idele.
  have hH1 (w : InfinitePlace F) : (H (h • e)).1 w ≠ 0 := by
    by_cases hw : w = w₀
    · rw [hw]
      change Function.update ((h • e).1 : (w : InfinitePlace F) → w.Completion) w₀
        (g₀ * μ (h • e)) w₀ ≠ 0
      rw [Function.update_self]
      exact mul_ne_zero (hg1 w₀) (Units.ne_zero _)
    · change Function.update ((h • e).1 : (w : InfinitePlace F) → w.Completion) w₀
        (g₀ * μ (h • e)) w ≠ 0
      rw [Function.update_of_ne hw]
      exact hy1 w hw
  have hH2 (v : S) : (H (h • e)).2 v ≠ 0 := hy2 v
  have hunit := sAdeleNormOneOrbitMap_isQuotientMap_isUnit F S _ hH1 hH2
  have hHnorm : P (H (h • e)) = 1 := by
    apply NNReal.eq
    rw [hPQ, hQ (H (h • e)) (h • e) (fun w hw ↦ Function.update_of_ne hw _ _) (fun _ ↦ rfl)]
    change ((‖Function.update ((h • e).1 : (w : InfinitePlace F) → w.Completion) w₀
      (g₀ * μ (h • e)) w₀‖₊ ^ w₀.mult * Q (h • e) : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ)
    rw [Function.update_self]
    push_cast
    rw [norm_mul, mul_pow, hμnorm, Real.rpow_inv_natCast_pow (Real.exp_pos _).le hm,
      Real.exp_sub, Real.exp_log hQx0, Real.exp_log hyQ, ← hQxR]
    field_simp
    rfl
  let k : Nₛ := ⟨hunit.unit, MonoidHom.mem_ker.mpr (Units.ext (by
    rw [sAdeleNormOneOrbitMap_isQuotientMap_norm, Units.val_one]
    exact hHnorm))⟩
  refine ⟨k, hyU, Prod.ext (funext fun w ↦ ?_) (funext fun v ↦ ?_)⟩
  · change (H (h • e)).1 w * e.1 w = (h • e).1 w
    by_cases hw : w = w₀
    · rw [he1, ite_eq_left hw, mul_zero, hsmul1, ite_eq_left hw]
    · rw [he1, ite_eq_right hw, mul_one]
      change Function.update ((h • e).1 : (w : InfinitePlace F) → w.Completion) w₀
        (g₀ * μ (h • e)) w = _
      rw [Function.update_of_ne hw]
  · change (H (h • e)).2 v * e.2 v = (h • e).2 v
    rw [he2, mul_one]

/-- Near any point of the orbit of a base point, every point of the S-local union is the
translate of that base point by a norm-one S-idele lying in any given neighborhood of the
original one. -/
private theorem sAdeleNormOneOrbitMap_isQuotientMap_nhds (i : Option (InfinitePlace F ⊕ S))
    (g : Nₛ) (U : Set Aₛ) (hU : U ∈ 𝓝 (g.val.val)) :
    ∃ t ∈ 𝓝 (g • sAdeleOrbitBasepoint F S i),
      ∀ y ∈ sAdeleNormOneOrbitUnion F S, y ∈ t →
        ∃ h : Nₛ, h.val.val ∈ U ∧ h • sAdeleOrbitBasepoint F S i = y := by
  rcases i with _ | (w | v)
  · exact sAdeleNormOneOrbitMap_isQuotientMap_nhds_none F S g U hU
  · exact sAdeleNormOneOrbitMap_isQuotientMap_nhds_inl F S w g U hU
  · exact sAdeleNormOneOrbitMap_isQuotientMap_nhds_inr F S v g U hU

/-- The S-local orbit map is open. -/
private theorem sAdeleNormOneOrbitMap_isOpenMap : IsOpenMap (sAdeleNormOneOrbitMap F S) := by
  intro W hW
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨⟨g, _, i, rfl⟩, hgW, rfl⟩
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp (hW.mem_nhds hgW)
  have hind : IsInducing (fun k : Nₛ ↦ k.val.val) :=
    (sIdeleGroup_description F S).1.comp IsInducing.subtypeVal
  rw [hind.nhds_eq_comap, Filter.mem_comap] at hu
  obtain ⟨U, hU, hUu⟩ := hu
  obtain ⟨t, ht, hts⟩ := sAdeleNormOneOrbitMap_isQuotientMap_nhds F S i g U hU
  rw [mem_nhds_subtype]
  refine ⟨t, ht, fun y hy ↦ ?_⟩
  obtain ⟨h, hhU, hhy⟩ := hts y.val y.property hy
  exact ⟨(h, ⟨_, i, rfl⟩), huv ⟨hUu hhU, mem_of_mem_nhds hv⟩, Subtype.ext hhy⟩

/-- The S-local orbit map is continuous. -/
private theorem sAdeleNormOneOrbitMap_continuous : Continuous (sAdeleNormOneOrbitMap F S) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

/-- The S-local orbit map is surjective. -/
private theorem sAdeleNormOneOrbitMap_surjective :
    Function.Surjective (sAdeleNormOneOrbitMap F S) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, z, rfl⟩ := (mem_sAdeleNormOneOrbitUnion_iff F S y).mp hy
  exact ⟨(g, z), rfl⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The adelic subspace topology on the S-local
norm-one orbit union is the quotient topology of the S-local orbit map. -/
theorem sAdeleNormOneOrbitMap_isQuotientMap : IsQuotientMap (sAdeleNormOneOrbitMap F S) :=
  (sAdeleNormOneOrbitMap_isOpenMap F S).isQuotientMap (sAdeleNormOneOrbitMap_continuous F S)
    (sAdeleNormOneOrbitMap_surjective F S)

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is continuous for the
adelic subspace topology on the target.
Deviation: The adelic subspace topology is coarser than the quotient topology.
The equality of topologies fails by ERRATA R12. -/
theorem adeleNormOneOrbitMap_continuous : Continuous (adeleNormOneOrbitMap F) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

/-- Paper: Lemma 8.2.0.3(2), p. 385. Every point in the global norm-one orbit union
has a preimage under the orbit map. -/
theorem adeleNormOneOrbitMap_surjective : Surjective (adeleNormOneOrbitMap F) := by
  rintro ⟨x, hx⟩
  simp only [adeleNormOneOrbitUnion, Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  simp only [adeleNormOneOrbit, MulAction.mem_orbit_iff] at hi
  obtain ⟨g, hg⟩ := hi
  exact ⟨(g, ⟨adeleOrbitBasepoint F i, Set.mem_range_self i⟩), Subtype.ext hg⟩

/-- The coordinates of a unit adele are nonzero. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_ne_zero (u : 𝔸[F]ˣ) :
    (∀ w : InfinitePlace F, u.val.1 w ≠ 0) ∧ ∀ w : HeightOneSpectrum (𝓞 F), u.val.2 w ≠ 0 := by
  constructor
  · intro w h
    have hc : u.val.1 w * u.inv.1 w = 1 := congrArg (fun a : 𝔸[F] ↦ a.1 w) u.val_inv
    rw [h, zero_mul] at hc
    exact zero_ne_one hc
  · intro w h
    have hc : u.val.2 w * u.inv.2 w = 1 := congrArg (fun a : 𝔸[F] ↦ a.2 w) u.val_inv
    rw [h, zero_mul] at hc
    exact zero_ne_one hc

/-- The coordinates of a base point are zero at its own place and one elsewhere. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_coord
    (k : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) :
    (∀ w : InfinitePlace F, (k = some (.inl w) → (adeleOrbitBasepoint F k).1 w = 0) ∧
      (k ≠ some (.inl w) → (adeleOrbitBasepoint F k).1 w = 1)) ∧
    ∀ w : HeightOneSpectrum (𝓞 F), (k = some (.inr w) → (adeleOrbitBasepoint F k).2 w = 0) ∧
      (k ≠ some (.inr w) → (adeleOrbitBasepoint F k).2 w = 1) := by
  classical
  rcases k with _ | v | v
  · exact ⟨fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩, fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩⟩
  · refine ⟨fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩⟩
    · cases h
      exact Pi.mulSingle_eq_same (M := fun u : InfinitePlace F ↦ u.Completion) _ _
    · have hvw : w ≠ v := fun e ↦ h (e ▸ rfl)
      exact Pi.mulSingle_eq_of_ne (M := fun u : InfinitePlace F ↦ u.Completion) hvw _
  · refine ⟨fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩, fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · cases h
      exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v 0 v).trans (Pi.mulSingle_eq_same _ _)
    · have hvw : w ≠ v := fun e ↦ h (e ▸ rfl)
      exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v 0 w).trans
        (Pi.mulSingle_eq_of_ne hvw _)

/-- Two base points in the same idele orbit are equal. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_eq (u : 𝔸[F]ˣ)
    (i j : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)))
    (h : u • adeleOrbitBasepoint F i = adeleOrbitBasepoint F j) : i = j := by
  obtain ⟨hu1, hu2⟩ := adeleNormOneOrbitMap_isOpenQuotientMap_ne_zero F u
  have hco := adeleNormOneOrbitMap_isOpenQuotientMap_coord F
  have k1 : ∀ w, (adeleOrbitBasepoint F j).1 w = u.val.1 w * (adeleOrbitBasepoint F i).1 w :=
    fun w ↦ by rw [← h]; rfl
  have k2 : ∀ w, (adeleOrbitBasepoint F j).2 w = u.val.2 w * (adeleOrbitBasepoint F i).2 w :=
    fun w ↦ by rw [← h]; rfl
  rcases j with _ | w | w
  · rcases i with _ | v | v
    · rfl
    · exfalso
      have hc := k1 v
      rw [((hco none).1 v).2 (by simp), ((hco _).1 v).1 rfl, mul_zero] at hc
      exact one_ne_zero hc
    · exfalso
      have hc := k2 v
      rw [((hco none).2 v).2 (by simp), ((hco _).2 v).1 rfl, mul_zero] at hc
      exact one_ne_zero hc
  · have hc := k1 w
    rw [((hco _).1 w).1 rfl] at hc
    by_contra hne
    rw [((hco i).1 w).2 hne, mul_one] at hc
    exact hu1 w hc.symm
  · have hc := k2 w
    rw [((hco _).2 w).1 rfl] at hc
    by_contra hne
    rw [((hco i).2 w).2 hne, mul_one] at hc
    exact hu2 w hc.symm

/-- The saturation of an open set under the norm-one orbit relation is open. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_sat (U : Set (N₁ × adeleOrbitBasepoints F))
    (hU : IsOpen U) :
    IsOpen {p : N₁ × adeleOrbitBasepoints F | ∃ q ∈ U, q.1 • q.2.val = p.1 • p.2.val} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨q, hqU, hqp⟩
  obtain ⟨i, hi⟩ := p.2.prop
  obtain ⟨j, hj⟩ := q.2.prop
  have hk : (p.1.val⁻¹ * q.1.val) • q.2.val = p.2.val := by
    rw [mul_smul]
    change p.1.val⁻¹ • (q.1 • q.2.val) = _
    rw [hqp]
    exact inv_smul_smul p.1.val _
  have hji : j = i := adeleNormOneOrbitMap_isOpenQuotientMap_eq F _ j i (by rw [hj, hi]; exact hk)
  have hq2 : q.2 = p.2 := Subtype.ext (by rw [← hj, ← hi, hji])
  have hfix := hk
  rw [hq2] at hfix
  rcases i with _ | pl
  · have h1 : ((p.1.val⁻¹ * q.1.val : 𝔸[F]ˣ) : 𝔸[F]) * 1 = 1 := by
      rw [← hi] at hfix
      exact hfix
    rw [mul_one] at h1
    have hpq : q = p := Prod.ext (Subtype.ext (inv_mul_eq_one.mp (Units.ext h1)).symm) hq2
    exact Filter.mem_of_superset (hU.mem_nhds (hpq ▸ hqU)) fun u hu ↦ ⟨u, hu, rfl⟩
  · obtain ⟨O, hOo, hpO, hOu⟩ : ∃ O : Set 𝔸[F], IsOpen O ∧ p.2.val ∈ O ∧
        ∀ y : adeleOrbitBasepoints F, y.val ∈ O → y = p.2 := by
      rcases pl with w | w
      · refine ⟨{y | y.1 w ≠ 1},
          isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const, ?_, ?_⟩
        · show (p.2.val).1 w ≠ 1
          rw [← hi, ((adeleNormOneOrbitMap_isOpenQuotientMap_coord F _).1 w).1 rfl]
          exact zero_ne_one
        · intro y hy
          obtain ⟨k, hk⟩ := y.prop
          have hy' : (adeleOrbitBasepoint F k).1 w ≠ 1 := by
            rw [hk]
            exact hy
          have hkw : k = some (.inl w) := by
            by_contra hne
            exact hy' (((adeleNormOneOrbitMap_isOpenQuotientMap_coord F k).1 w).2 hne)
          exact Subtype.ext (by rw [← hk, ← hi, hkw])
      · refine ⟨{y | y.2 w ≠ 1}, isOpen_ne_fun
          ((RestrictedProduct.continuous_eval w).comp continuous_snd) continuous_const, ?_, ?_⟩
        · show (p.2.val).2 w ≠ 1
          rw [← hi, ((adeleNormOneOrbitMap_isOpenQuotientMap_coord F _).2 w).1 rfl]
          exact zero_ne_one
        · intro y hy
          obtain ⟨k, hk⟩ := y.prop
          have hy' : (adeleOrbitBasepoint F k).2 w ≠ 1 := by
            rw [hk]
            exact hy
          have hkw : k = some (.inr w) := by
            by_contra hne
            exact hy' (((adeleNormOneOrbitMap_isOpenQuotientMap_coord F k).2 w).2 hne)
          exact Subtype.ext (by rw [← hk, ← hi, hkw])
    let k : N₁ := p.1⁻¹ * q.1
    have hcont : Continuous fun x : N₁ × adeleOrbitBasepoints F ↦ (x.1 * k, x.2) := by
      refine Continuous.prodMk ?_ continuous_snd
      refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
      show Continuous fun x : N₁ × adeleOrbitBasepoints F ↦ x.1.val * k.val
      exact (continuous_subtype_val.comp continuous_fst).mul continuous_const
    have hV : IsOpen ((fun x : N₁ × adeleOrbitBasepoints F ↦ (x.1 * k, x.2)) ⁻¹' U ∩
        {x | x.2.val ∈ O}) :=
      (hU.preimage hcont).inter (hOo.preimage (continuous_subtype_val.comp continuous_snd))
    refine Filter.mem_of_superset (hV.mem_nhds ⟨?_, hpO⟩) ?_
    · show (p.1 * k, p.2) ∈ U
      rw [show p.1 * k = q.1 from mul_inv_cancel_left p.1 q.1, ← hq2]
      exact hqU
    · rintro x ⟨hxU, hxO⟩
      have hx2 : x.2 = p.2 := hOu x.2 hxO
      refine ⟨(x.1 * k, x.2), hxU, ?_⟩
      change (x.1.val * k.val) • x.2.val = x.1.val • x.2.val
      rw [mul_smul, hx2, show (k : 𝔸[F]ˣ) • p.2.val = p.2.val from hfix]

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is an open quotient map
for its coinduced topology.
Deviation: The target carries the quotient topology of the global orbit map.
ERRATA R12 distinguishes this topology from the adelic subspace topology. -/
theorem adeleNormOneOrbitMap_isOpenQuotientMap :
    @IsOpenQuotientMap _ _ inferInstance
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance)
      (adeleNormOneOrbitMap F) := by
  refine @IsOpenQuotientMap.mk _ _ _
    (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) (adeleNormOneOrbitMap F)
    (adeleNormOneOrbitMap_surjective F) continuous_coinduced_rng fun U hU ↦ ?_
  rw [isOpen_coinduced]
  convert adeleNormOneOrbitMap_isOpenQuotientMap_sat F U hU using 1
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, hq, congrArg Subtype.val hqp⟩
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, hq, Subtype.ext hqp⟩

/-- The S-adele ring is Hausdorff: it is a product of Hausdorff completions of `F`.
The instance has to be routed through the definition, exactly as in
`AppA_AlgebraicNT/Sec1.lean` (`adeleHausdorff_ideleLocallyCompact`). -/
private theorem t2Space_sAdeleRing : T2Space (SAdeleRing F S) := by
  change T2Space (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is Hausdorff. -/
theorem sAdeleNormOneOrbitUnion_t2Space : T2Space (sAdeleNormOneOrbitUnion F S) := by
  have := t2Space_sAdeleRing F S
  infer_instance

/-- The adele ring is Hausdorff: a product of the infinite part with the restricted
product of the finite part. The restricted product instance only fires after unfolding,
so it is written out (`Πʳ` is not in scope in this file). -/
private theorem t2Space_adeleRing : T2Space 𝔸[F] :=
  inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) ×
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite))

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is Hausdorff. -/
theorem adeleNormOneOrbitUnion_t2Space : T2Space (adeleNormOneOrbitUnion F) := by
  have := t2Space_adeleRing F
  infer_instance

/-- The S-adele ring is metrizable: a finite product of metrizable completions of `F`,
routed through the definition as for `t2Space_sAdeleRing`. -/
private theorem metrizableSpace_sAdeleRing : MetrizableSpace (SAdeleRing F S) := by
  change MetrizableSpace (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is metrizable. -/
theorem sAdeleNormOneOrbitUnion_metrizableSpace :
    MetrizableSpace (sAdeleNormOneOrbitUnion F S) := by
  have := metrizableSpace_sAdeleRing F S
  infer_instance

/-- The nonzero prime ideals of the ring of integers form a countable type: the ring is
countable, its ideals are finitely generated, and a height-one spectrum element is
determined by its underlying ideal. -/
private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : Countable (𝓞 F) := RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact HeightOneSpectrum.asIdeal_injective.countable

/-- A restricted product over a countable index type, with open distinguished subsets,
is second countable: the pieces where the coordinates lie in the distinguished subsets
outside a fixed finite set form a countable open cover by second countable subspaces. -/
private theorem secondCountableTopology_restrictedProduct_cofinite
    {ι : Type*} [Countable ι] (R : ι → Type*) [∀ i, TopologicalSpace (R i)]
    [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (RestrictedProduct R A Filter.cofinite) := by
  have hS (T : Finset ι) : Filter.cofinite ≤ Filter.principal ((T : Set ι)ᶜ) :=
    Filter.le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  haveI (T : Finset ι) : SecondCountableTopology
      (RestrictedProduct R A (Filter.principal ((T : Set ι)ᶜ))) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he (T : Finset ι) : IsOpenEmbedding (RestrictedProduct.inclusion R A (hS T)) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  haveI (T : Finset ι) : SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) :=
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := Filter.eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa [Set.Finite.mem_toFinset] using h)

/-- The finite adele ring is second countable: the local completions are proper metric
spaces, hence second countable, and the restricted product is taken over a countable
index with open integer subrings. -/
private theorem secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := countable_heightOneSpectrum F
  haveI (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  change SecondCountableTopology (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    Filter.cofinite)
  exact secondCountableTopology_restrictedProduct_cofinite
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

/-- The adele ring is metrizable. The infinite part is a finite product of metrizable
completions. The finite part is second countable and weakly locally compact (the integer
subrings are compact open), hence regular; with T0 this gives T3, and Urysohn's
metrization theorem applies. -/
private theorem metrizableSpace_adeleRing : MetrizableSpace 𝔸[F] := by
  haveI (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  haveI (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI : SecondCountableTopology (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite) :=
    secondCountableTopology_finiteAdeleRing F
  exact inferInstanceAs (MetrizableSpace (((w : InfinitePlace F) → w.Completion) ×
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite))

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is metrizable. -/
theorem adeleNormOneOrbitUnion_metrizableSpace : MetrizableSpace (adeleNormOneOrbitUnion F) := by
  have := metrizableSpace_adeleRing F
  infer_instance

/-- The S-adele ring is second countable: the archimedean completions embed isometrically
into `ℂ`, and the finite completions in `S` are proper metric spaces. -/
private theorem secondCountableTopology_sAdeleRing :
    SecondCountableTopology (SAdeleRing F S) := by
  change SecondCountableTopology (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  haveI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  haveI (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is second-countable. -/
theorem sAdeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (sAdeleNormOneOrbitUnion F S) := by
  have := secondCountableTopology_sAdeleRing F S
  infer_instance

/-- The adele ring is second countable: the archimedean factor is a finite product of
completions that embed isometrically into `ℂ`, and the finite adele ring is second
countable by `secondCountableTopology_finiteAdeleRing`. -/
private theorem secondCountableTopology_adeleRing :
    SecondCountableTopology 𝔸[F] := by
  haveI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite) :=
    secondCountableTopology_finiteAdeleRing F
  exact inferInstanceAs (SecondCountableTopology (((w : InfinitePlace F) → w.Completion) ×
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite))

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is second-countable. -/
theorem adeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (adeleNormOneOrbitUnion F) := by
  have := secondCountableTopology_adeleRing F
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is perfectly normal. -/
theorem sAdeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (sAdeleNormOneOrbitUnion F S) := by
  have := sAdeleNormOneOrbitUnion_metrizableSpace F S
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is perfectly normal. -/
theorem adeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (adeleNormOneOrbitUnion F) := by
  have := adeleNormOneOrbitUnion_metrizableSpace F
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is separable. -/
theorem sAdeleNormOneOrbitUnion_separableSpace : SeparableSpace (sAdeleNormOneOrbitUnion F S) := by
  have := sAdeleNormOneOrbitUnion_secondCountable F S
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is separable. -/
theorem adeleNormOneOrbitUnion_separableSpace : SeparableSpace (adeleNormOneOrbitUnion F) := by
  have := adeleNormOneOrbitUnion_secondCountable F
  infer_instance

/-- The domain of the S-local orbit map is locally compact: the norm-one S-ideles are a
closed subgroup of the locally compact S-ideles, and the base points are finitely many. -/
private theorem sAdeleNormOneOrbitUnion_locallyCompactSpace_domain :
    LocallyCompactSpace (Nₛ × sAdeleOrbitBasepoints F S) := by
  have hc : Continuous fun g : 𝕀ₛ ↦ ((sIdeleNorm F S g : ℝ≥0)) := by
    have : (fun g : 𝕀ₛ ↦ ((sIdeleNorm F S g : ℝ≥0))) = fun g ↦
        (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖₊ :=
      funext (sAdeleNormOneOrbitMap_isQuotientMap_norm F S)
    rw [this]
    fun_prop
  have hclosed : IsClosed (Nₛ : Set 𝕀ₛ) := by
    have : (Nₛ : Set 𝕀ₛ) = (fun g : 𝕀ₛ ↦ ((sIdeleNorm F S g : ℝ≥0))) ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker, Units.val_eq_one]
    rw [this]
    exact isClosed_singleton.preimage hc
  have := (sIdeleGroup_description F S).2.2.1
  have : LocallyCompactSpace Nₛ := hclosed.locallyCompactSpace
  have : Finite (sAdeleOrbitBasepoints F S) := (Set.finite_range _).to_subtype
  have : LocallyCompactSpace (sAdeleOrbitBasepoints F S) :=
    ⟨fun _ n hn ↦ ⟨n, hn, subset_rfl, n.toFinite.isCompact⟩⟩
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is locally compact. -/
theorem sAdeleNormOneOrbitUnion_locallyCompactSpace :
    LocallyCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  have := sAdeleNormOneOrbitUnion_locallyCompactSpace_domain F S
  exact (IsOpenQuotientMap.mk (sAdeleNormOneOrbitMap_surjective F S)
    (sAdeleNormOneOrbitMap_continuous F S) (sAdeleNormOneOrbitMap_isOpenMap F S)).locallyCompactSpace

/-- The adele ring is locally compact: the archimedean factor is a finite product of
completions, and the finite adele ring is a restricted product of locally compact fields
with respect to their compact open valuation rings. -/
private theorem adeleNormOneOrbitUnion_locallyCompactSpace_adeleRing :
    LocallyCompactSpace 𝔸[F] := by
  have (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  have (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  have : LocallyCompactSpace (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) =>
      v.adicCompletion F) (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
      Filter.cofinite) := inferInstance
  exact inferInstanceAs (LocallyCompactSpace (((w : InfinitePlace F) → w.Completion) ×
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite))

/-- The special adeles form a closed subset of the adele ring. A point outside it either has
a coordinate outside `{0, 1}` or two coordinates different from one; both conditions are
open and exclude every special adele. A point with neither property is special. -/
private theorem adeleNormOneOrbitUnion_locallyCompactSpace_isClosed :
    IsClosed (adeleOrbitBasepoints F) := by
  classical
  have hco := adeleNormOneOrbitMap_isOpenQuotientMap_coord F
  -- `one x c` says that the coordinate of `x` at the place `c` is one.
  let one : 𝔸[F] → InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F) → Prop := fun x ↦
    Sum.elim (fun w ↦ x.1 w = 1) (fun v ↦ x.2 v = 1)
  let zero : 𝔸[F] → InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F) → Prop := fun x ↦
    Sum.elim (fun w ↦ x.1 w = 0) (fun v ↦ x.2 v = 0)
  have hcw (w : InfinitePlace F) : Continuous fun y : 𝔸[F] ↦ y.1 w :=
    (continuous_apply w).comp continuous_fst
  have hcv (v : HeightOneSpectrum (𝓞 F)) : Continuous fun y : 𝔸[F] ↦ y.2 v :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  have hopen_one (c : InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) :
      IsOpen {y : 𝔸[F] | ¬ one y c} := by
    rcases c with w | v
    · exact isOpen_ne_fun (hcw w) continuous_const
    · exact isOpen_ne_fun (hcv v) continuous_const
  have hopen_zero (c : InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) :
      IsOpen {y : 𝔸[F] | ¬ zero y c} := by
    rcases c with w | v
    · exact isOpen_ne_fun (hcw w) continuous_const
    · exact isOpen_ne_fun (hcv v) continuous_const
  -- Coordinates of a special adele: zero at its own place, one elsewhere.
  have hbase (k : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)))
      (c : InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) :
      (k = some c → zero (adeleOrbitBasepoint F k) c) ∧
        (k ≠ some c → one (adeleOrbitBasepoint F k) c) := by
    rcases c with w | v
    · exact ((hco k).1 w)
    · exact ((hco k).2 v)
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  by_cases hA : ∃ c, ¬ one x c ∧ ¬ zero x c
  · obtain ⟨c, h1, h0⟩ := hA
    refine Filter.mem_of_superset (((hopen_one c).inter (hopen_zero c)).mem_nhds ⟨h1, h0⟩) ?_
    rintro y ⟨hy1, hy0⟩ ⟨k, rfl⟩
    by_cases hk : k = some c
    · exact hy0 ((hbase k c).1 hk)
    · exact hy1 ((hbase k c).2 hk)
  push Not at hA
  by_cases hB : ∃ a b, a ≠ b ∧ ¬ one x a ∧ ¬ one x b
  · obtain ⟨a, b, hab, ha, hb⟩ := hB
    refine Filter.mem_of_superset (((hopen_one a).inter (hopen_one b)).mem_nhds ⟨ha, hb⟩) ?_
    rintro y ⟨hya, hyb⟩ ⟨k, rfl⟩
    by_cases hka : k = some a
    · exact hyb ((hbase k b).2 (fun h ↦ hab (Option.some_injective _ (hka.symm.trans h))))
    · exact hya ((hbase k a).2 hka)
  push Not at hB
  -- Now `x` is special, contradicting `hx`.
  exfalso
  apply hx
  have hext (k : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)))
      (h : ∀ c, (k = some c → zero x c) ∧ (k ≠ some c → one x c)) :
      x = adeleOrbitBasepoint F k := by
    refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext F fun v ↦ ?_)
    · by_cases hk : k = some (.inl w)
      · exact ((h (.inl w)).1 hk).trans ((hbase k (.inl w)).1 hk).symm
      · exact ((h (.inl w)).2 hk).trans ((hbase k (.inl w)).2 hk).symm
    · by_cases hk : k = some (.inr v)
      · exact ((h (.inr v)).1 hk).trans ((hbase k (.inr v)).1 hk).symm
      · exact ((h (.inr v)).2 hk).trans ((hbase k (.inr v)).2 hk).symm
  by_cases hD : ∃ c, ¬ one x c
  · obtain ⟨c, hc⟩ := hD
    refine ⟨some c, (hext (some c) fun d ↦ ⟨fun hd ↦ ?_, fun hd ↦ ?_⟩).symm⟩
    · rw [Option.some_injective _ hd] at hc
      exact hA _ hc
    · exact hB c d (fun h ↦ hd (congrArg some h)) hc
  · push Not at hD
    exact ⟨none, (hext none fun d ↦ ⟨fun hd ↦ absurd hd (by simp), fun _ ↦ hD d⟩).symm⟩

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally compact
in the quotient topology of the orbit map.
Deviation: The adelic subspace topology fails to be locally compact by ERRATA R13. -/
theorem adeleNormOneOrbitUnion_locallyCompactSpace :
    @LocallyCompactSpace (adeleNormOneOrbitUnion F)
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) := by
  have : LocallyCompactSpace 𝔸[F]ˣ := (ideleGroup_topology F).2.1
  have : LocallyCompactSpace N₁ := (ideleGroup_topology F).2.2.2.2.2.locallyCompactSpace
  have := adeleNormOneOrbitUnion_locallyCompactSpace_adeleRing F
  have : LocallyCompactSpace (adeleOrbitBasepoints F) :=
    (adeleNormOneOrbitUnion_locallyCompactSpace_isClosed F).locallyCompactSpace
  exact @IsOpenQuotientMap.locallyCompactSpace _ _ _
    (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) _ _
    (adeleNormOneOrbitMap_isOpenQuotientMap F)

/-- The S-idelic norm is continuous: it is a finite product of powers of coordinate norms. -/
private theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace_continuous
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (sIdeleNorm F S) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun g : (SAdeleRing F S)ˣ ↦ ((sIdeleNorm F S g).val))
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]
  change Continuous (fun g : (SAdeleRing F S)ˣ ↦
    (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖₊)
  fun_prop

/-- The S-adele ring is second countable: each infinite completion embeds isometrically
in the complex numbers, and each finite completion is a proper metric space. -/
private theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace_secondCountable
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SecondCountableTopology (SAdeleRing F S) := by
  have h1 (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have h2 (v : S) : SecondCountableTopology (v.val.adicCompletion F) := by
    have := properSpace_adicCompletion (K := F) v.val
    infer_instance
  change SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  infer_instance

/-- The norm-one subgroup of the S-ideles is σ-compact: it is closed in the S-idele group,
which is locally compact and second countable. -/
private theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace_kernel
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SigmaCompactSpace (MonoidHom.ker (sIdeleNorm F S)) := by
  have h2 := sAdeleNormOneOrbitUnion_sigmaCompactSpace_secondCountable F S
  have hd := sIdeleGroup_description F S
  have h3 : SecondCountableTopology (SAdeleRing F S)ˣ := hd.1.secondCountableTopology
  have h4 : LocallyCompactSpace (SAdeleRing F S)ˣ := hd.2.2.1
  have h5 : SigmaCompactSpace (SAdeleRing F S)ˣ := inferInstance
  have hcl : IsClosed ((MonoidHom.ker (sIdeleNorm F S) : Subgroup (SAdeleRing F S)ˣ) :
      Set (SAdeleRing F S)ˣ) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage
      (sAdeleNormOneOrbitUnion_sigmaCompactSpace_continuous F S)
  exact hcl.sigmaCompactSpace

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is σ-compact. -/
theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  have h1 := sAdeleNormOneOrbitUnion_sigmaCompactSpace_kernel F S
  have h2 : Finite (sAdeleOrbitBasepoints F S) :=
    (Set.finite_range (sAdeleOrbitBasepoint F S)).to_subtype
  have hc : Continuous (sAdeleNormOneOrbitMap F S) := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)
  have hs : Surjective (sAdeleNormOneOrbitMap F S) := by
    rintro ⟨x, hx⟩
    obtain ⟨g, z, hgz⟩ := (mem_sAdeleNormOneOrbitUnion_iff F S x).mp hx
    exact ⟨(g, z), Subtype.ext hgz⟩
  have hr := isSigmaCompact_range hc
  rw [hs.range_eq] at hr
  exact isSigmaCompact_univ_iff.mp hr

/-- The finite places of a number field form a countable set, since every prime ideal is
finitely generated over the countable ring of integers. -/
private theorem adeleNormOneOrbitUnion_sigmaCompactSpace_countable_places :
    Countable (HeightOneSpectrum (𝓞 F)) := by
  have hF : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hO : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have h : Surjective (fun s : Finset (𝓞 F) ↦ Ideal.span (s : Set (𝓞 F))) :=
    fun I ↦ IsNoetherian.noetherian I
  have hI : Countable (Ideal (𝓞 F)) := h.countable
  exact (show Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) from fun _ _ h ↦
    HeightOneSpectrum.ext h).countable

/-- The adele ring is second countable. The finite adeles are covered by countably many open
sets, each consisting of the adeles that are integral outside a finite set of places, and
each of these embeds into the countable product of the second countable local fields. -/
private theorem adeleNormOneOrbitUnion_sigmaCompactSpace_adeleRing :
    SecondCountableTopology 𝔸[F] := by
  classical
  let I := HeightOneSpectrum (𝓞 F)
  let K (w : I) := w.adicCompletion F
  let O (w : I) : Set (K w) := w.adicCompletionIntegers F
  have hopen (w : I) : IsOpen (O w) := Valued.isOpen_valuationSubring (K w)
  have hI : Countable I := adeleNormOneOrbitUnion_sigmaCompactSpace_countable_places F
  have hproper (w : I) : ProperSpace (K w) := properSpace_adicCompletion w
  have hK (w : I) : SecondCountableTopology (K w) := secondCountable_of_proper
  let U (s : Finset I) := {a : FiniteAdeleRing (𝓞 F) F | ∀ w ∉ s, a w ∈ O w}
  have hU (s : Finset I) : SecondCountableTopology (U s) := by
    have hs : Filter.cofinite ≤ Filter.principal (s : Set I)ᶜ :=
      Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have he := RestrictedProduct.isEmbedding_inclusion_principal (R := K) (A := O) hs
    have h2 : SecondCountableTopology
        (RestrictedProduct K O (Filter.principal (s : Set I)ᶜ)) :=
      (RestrictedProduct.isEmbedding_coe_of_principal (R := K) (A := O)).secondCountableTopology
    have hrange : Set.range (RestrictedProduct.inclusion K O hs) = U s := by
      rw [RestrictedProduct.range_inclusion]
      ext a
      exact Filter.eventually_principal
    exact hrange ▸ he.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hfin : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
    refine secondCountableTopology_of_countable_cover (U := U)
      (fun _ ↦ RestrictedProduct.isOpen_forall_imp_mem hopen) (Set.eq_univ_of_forall fun a ↦ ?_)
    have he := Filter.eventually_cofinite.mp a.2
    exact Set.mem_iUnion.mpr ⟨he.toFinset, fun w hw ↦ by
      by_contra h
      exact hw (he.mem_toFinset.mpr h)⟩
  have hinf (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × FiniteAdeleRing (𝓞 F) F))

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is σ-compact
in the adelic subspace topology. -/
theorem adeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (adeleNormOneOrbitUnion F) := by
  obtain ⟨-, hlc, -, -, -, hker⟩ := ideleGroup_topology F
  have h2 := adeleNormOneOrbitUnion_sigmaCompactSpace_adeleRing F
  have hop : SecondCountableTopology 𝔸[F]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have hu : SecondCountableTopology 𝔸[F]ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have hs : SigmaCompactSpace 𝔸[F]ˣ := inferInstance
  have hN : SigmaCompactSpace N₁ := hker.sigmaCompactSpace
  have hc : Countable (HeightOneSpectrum (𝓞 F)) :=
    adeleNormOneOrbitUnion_sigmaCompactSpace_countable_places F
  rw [← isSigmaCompact_iff_sigmaCompactSpace]
  refine isSigmaCompact_iUnion _ fun i ↦ ?_
  exact isSigmaCompact_range (f := fun g : N₁ ↦ g • adeleOrbitBasepoint F i)
    (continuous_subtype_val.smul continuous_const)

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is paracompact. -/
theorem sAdeleNormOneOrbitUnion_paracompactSpace :
    ParacompactSpace (sAdeleNormOneOrbitUnion F S) := by
  have h1 := sAdeleNormOneOrbitUnion_t2Space F S
  have h2 := sAdeleNormOneOrbitUnion_locallyCompactSpace F S
  have h3 := sAdeleNormOneOrbitUnion_sigmaCompactSpace F S
  infer_instance

/-- A regular second countable space is paracompact: shrink the cover to countably many open
sets whose closures lie in members of the cover, and remove from each chosen member the
closures of the earlier sets. -/
private theorem adeleNormOneOrbitUnion_paracompactSpace_of_regular_secondCountable
    {X : Type*} [TopologicalSpace X] [RegularSpace X] [SecondCountableTopology X] :
    ParacompactSpace X := by
  classical
  refine ⟨fun α s ho hc ↦ ?_⟩
  have hx : ∀ x : X, ∃ a, x ∈ s a := fun x ↦ Set.mem_iUnion.mp (hc ▸ Set.mem_univ x)
  choose a ha using hx
  have hV : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ closure V ⊆ s (a x) := by
    intro x
    obtain ⟨K, hK, hKc, hKs⟩ := exists_mem_nhds_isClosed_subset ((ho (a x)).mem_nhds (ha x))
    exact ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hK,
      (closure_minimal interior_subset hKc).trans hKs⟩
  choose V hVo hVx hVs using hV
  obtain ⟨T, hT, hTcov⟩ := isOpen_iUnion_countable V hVo
  have hTc : Countable T := hT.to_subtype
  obtain ⟨f, hf⟩ := exists_injective_nat T
  have hmem : ∀ x : X, ∃ i : T, x ∈ V i := by
    intro x
    have h1 : x ∈ ⋃ i ∈ T, V i := by
      rw [hTcov]
      exact Set.mem_iUnion.mpr ⟨x, hVx x⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h1
    exact ⟨⟨i, hi⟩, hxi⟩
  have hfin : ∀ n : ℕ, {j : T | f j < n}.Finite := fun n ↦
    (Set.finite_Iio n).preimage hf.injOn
  have hfin' : ∀ n : ℕ, {j : T | f j ≤ n}.Finite := fun n ↦
    (Set.finite_Iic n).preimage hf.injOn
  refine ⟨T, fun i ↦ s (a i) \ ⋃ j ∈ {j : T | f j < f i}, closure (V j), fun i ↦ ?_, ?_, ?_,
    fun i ↦ ⟨a i, Set.sdiff_subset⟩⟩
  · exact (ho _).sdiff ((hfin (f i)).isClosed_biUnion fun j _ ↦ isClosed_closure)
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    have hex : ∃ n, ∃ i : T, f i = n ∧ x ∈ s (a i) := by
      obtain ⟨i, hi⟩ := hmem x
      exact ⟨f i, i, rfl, hVs i (subset_closure hi)⟩
    obtain ⟨i, hi, hxi⟩ := Nat.find_spec hex
    refine Set.mem_iUnion.mpr ⟨i, hxi, fun hmem' ↦ ?_⟩
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem'
    have hlt : f j < Nat.find hex := by
      rw [← hi]
      exact hj
    exact Nat.find_min hex hlt ⟨j, rfl, hVs j hxj⟩
  · intro x
    obtain ⟨m, hm⟩ := hmem x
    refine ⟨V m, (hVo m).mem_nhds hm, (hfin' (f m)).subset ?_⟩
    rintro i ⟨y, hy, hyV⟩
    by_contra hlt
    have hlt' : f m < f i := not_le.mp hlt
    exact hy.2 (Set.mem_iUnion₂.mpr ⟨m, hlt', subset_closure hyV⟩)

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is paracompact. -/
theorem adeleNormOneOrbitUnion_paracompactSpace : ParacompactSpace (adeleNormOneOrbitUnion F) := by
  have h2 := adeleNormOneOrbitUnion_sigmaCompactSpace_adeleRing F
  have ht2 := t2Space_adeleRing F
  have ht3 : T3Space 𝔸[F] := inferInstance
  exact adeleNormOneOrbitUnion_paracompactSpace_of_regular_secondCountable

/-- Paper: Proposition 8.2.0.4, p. 386. The subgroup of global ideles obtained by
inserting the units of the local valuation ring at the specified finite place. -/
def embeddedFiniteLocalUnits (v : HeightOneSpectrum (𝓞 F)) : Subgroup 𝔸[F]ˣ :=
  ((IdeleGroup.ofAdicCompletion (𝓞 F) F v).comp
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom)).range

/-- Paper: Proposition 8.2.0.4, p. 386. The inserted local units have norm one at
the specified place and value one at all other places. -/
theorem mem_embeddedFiniteLocalUnits_iff (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g ∈ embeddedFiniteLocalUnits F v ↔
      g.val.1 = 1 ∧ ‖g.val.2 v‖ = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → g.val.2 w = 1 := by
  classical
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = 1
      rw [AdeleRing.ofAdicCompletion_apply]
    · have h := FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val v
      have hval := h.trans (Pi.mulSingle_eq_same v _)
      refine (congrArg norm hval).trans ?_
      rw [Valued.toNormedField.norm_eq_one_iff]
      exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := F) (v := v)).mp u.isUnit
    · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans
        (Pi.mulSingle_eq_of_ne (i := v) (i' := w) hw _)
  · rintro ⟨h1, h2, h3⟩
    let x : v.adicCompletion F := g.val.2 v
    have hxval : Valued.v x = 1 := Valued.toNormedField.norm_eq_one_iff.mp h2
    have hxne : x ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hxval]; exact one_ne_zero)
    have hxm : x ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxval]
    have hxim : x⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hxval, inv_one]
    let u : (v.adicCompletionIntegers F)ˣ :=
      Units.mk ⟨x, hxm⟩ ⟨x⁻¹, hxim⟩
        (Subtype.ext (mul_inv_cancel₀ hxne)) (Subtype.ext (inv_mul_cancel₀ hxne))
    refine ⟨u, Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext F fun w => ?_))⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = g.val.1
      rw [AdeleRing.ofAdicCompletion_apply, h1]
    · refine (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans ?_
      obtain rfl | hw := eq_or_ne w v
      · exact Pi.mulSingle_eq_same _ _
      · rw [Pi.mulSingle_eq_of_ne hw, h3 w hw]

/-- Paper: Equation (8.2.0.9), p. 386. The S-local section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def sAdeleFiniteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) : Set Aₛ :=
  (fun t : ℝ≥0ˣ ↦ τ t • sAdeleOrbitBasepoint F S (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.val.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.9), p. 386. The included left endpoint gives the S-local
single-zero base point. -/
theorem sAdeleOrbitBasepoint_mem_finiteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) :
    sAdeleOrbitBasepoint F S (some (.inr v)) ∈ sAdeleFiniteOrbitSection F S v τ := by
  have hN : (1 : ℝ≥0) < (v.val.asIdeal.absNorm : ℝ≥0) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val
  refine ⟨1, ⟨by rw [Units.val_one], by rw [Units.val_one]; exact hN⟩, ?_⟩
  change τ 1 • sAdeleOrbitBasepoint F S (some (.inr v)) = _
  rw [map_one, one_smul]

/-- Paper: Equation (8.2.0.10), p. 386. The global section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def adeleFiniteOrbitSection (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    Set 𝔸[F] :=
  (fun t : ℝ≥0ˣ ↦ τ t • adeleOrbitBasepoint F (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.10), p. 386. The included left endpoint gives the global
single-zero base point. -/
theorem adeleOrbitBasepoint_mem_finiteOrbitSection (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    adeleOrbitBasepoint F (some (.inr v)) ∈ adeleFiniteOrbitSection F v τ := by
  have hN : (1 : ℝ≥0) < (v.asIdeal.absNorm : ℝ≥0) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine ⟨1, ⟨by rw [Units.val_one], by rw [Units.val_one]; exact hN⟩, ?_⟩
  change τ 1 • adeleOrbitBasepoint F (some (.inr v)) = _
  rw [map_one, one_smul]

/-- A uniformizer at a finite place, as a unit, with norm the reciprocal of the absolute norm. -/
private theorem sAdeleFiniteOrbit_transporter_uniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : (v.adicCompletion F)ˣ, ‖(π : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 (π : v.adicCompletion F) hπ.ne_zero, norm_uniformizer_adicCompletion v _ hπ⟩

/-- The norm of a unit at a finite place is an integer power of the absolute norm. -/
private theorem sAdeleFiniteOrbit_transporter_norm_zpow (v : HeightOneSpectrum (𝓞 F))
    (y : (v.adicCompletion F)ˣ) :
    ∃ m : ℤ, ‖(y : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ) ^ m := by
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v
  obtain ⟨e, he1, he2⟩ := finitePlace_unitDecomposition v π hπ
  let ι := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom
  have hy : y = π ^ (e y).1.toAdd * ι (e y).2 := by
    apply e.injective
    rw [map_mul, map_zpow, he1, he2]
    apply Prod.ext
    · show (e y).1 = Multiplicative.ofAdd (1 : ℤ) ^ (e y).1.toAdd * 1
      rw [mul_one, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
    · simp
  obtain ⟨m, u, hmu⟩ : ∃ (m : ℤ) (u : (v.adicCompletionIntegers F)ˣ), y = π ^ m * ι u :=
    ⟨_, _, hy⟩
  refine ⟨-m, ?_⟩
  have hu : ‖((ι u : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
    rw [Valued.toNormedField.norm_eq_one_iff]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := F) (v := v)).mp u.isUnit
  rw [hmu, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, hπ, hu, mul_one,
    inv_zpow, zpow_neg]

/-- The idele inserted at a finite place has the norm of the inserted unit. -/
private theorem sAdeleFiniteOrbit_transporter_ideleNorm (v : HeightOneSpectrum (𝓞 F))
    (w : (v.adicCompletion F)ˣ) :
    ((ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v w) : ℝ≥0) : ℝ) =
      ‖(w : v.adicCompletion F)‖ := by
  classical
  rw [((ideleNorm_spec F).1 _).2]
  change (∏ u : InfinitePlace F, ‖(1 : u.Completion)‖ ^ u.mult) *
    (∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖FiniteAdeleRing.ofAdicCompletion F v w.val u‖) = _
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_single _ v (fun u hu ↦ by
    rw [show FiniteAdeleRing.ofAdicCompletion F v w.val u = 1 from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ u).trans (Pi.mulSingle_eq_of_ne hu _),
      norm_one])]
  rw [show FiniteAdeleRing.ofAdicCompletion F v w.val v = w.val from
    (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ v).trans (Pi.mulSingle_eq_same _ _)]

/-- An S-idele fixes the S-local base point at a finite place of S exactly when it is the
projection of an idele inserted at that place. -/
private theorem sAdeleFiniteOrbit_transporter_smul (v : S) (g : (SAdeleRing F S)ˣ) :
    g • sAdeleOrbitBasepoint F S (some (.inr v)) = sAdeleOrbitBasepoint F S (some (.inr v)) ↔
      ∃ w : (v.val.adicCompletion F)ˣ, g = Units.map (adeleProjection F S).toMonoidHom
        (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    have h1 : g.val.1 = 1 := by
      have hc := congrArg Prod.fst h
      change g.val.1 * 1 = 1 at hc
      rwa [mul_one] at hc
    have h2 : ∀ u : S, u ≠ v → g.val.2 u = 1 := by
      intro u hu
      have hb : (sAdeleOrbitBasepoint F S (some (.inr v))).2 u = 1 :=
        (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val 0 u.val).trans
          (Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)) _)
      have hc : g.val.2 u * (sAdeleOrbitBasepoint F S (some (.inr v))).2 u =
          (sAdeleOrbitBasepoint F S (some (.inr v))).2 u :=
        congrArg (fun a : SAdeleRing F S ↦ a.2 u) h
      rwa [hb, mul_one] at hc
    let w : (v.val.adicCompletion F)ˣ := ⟨g.val.2 v, g.inv.2 v,
      congrArg (fun a : SAdeleRing F S ↦ a.2 v) g.val_inv,
      congrArg (fun a : SAdeleRing F S ↦ a.2 v) g.inv_val⟩
    refine ⟨w, Units.ext (Prod.ext h1 (funext fun u ↦ ?_))⟩
    refine Eq.trans ?_ (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val (g.val.2 v) u.val).symm
    obtain rfl | hu := eq_or_ne u v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)), h2 u hu]
  · rintro ⟨w, rfl⟩
    rw [Units.smul_def]
    change adeleProjection F S (AdeleRing.ofAdicCompletion (𝓞 F) F v.val w.val) *
        adeleProjection F S (AdeleRing.ofAdicCompletion (𝓞 F) F v.val 0) =
      adeleProjection F S (AdeleRing.ofAdicCompletion (𝓞 F) F v.val 0)
    rw [← map_mul, ← map_mul, mul_zero]

/-- The projection of an idele inserted at a finite place of S has the same S-norm as
global norm. -/
private theorem sAdeleFiniteOrbit_transporter_sIdeleNorm (v : S) (w : (v.val.adicCompletion F)ˣ) :
    sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w)) =
      ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) := by
  classical
  let A := integralAdelesOutside F S
  let s := IdeleGroup.ofAdicCompletion (𝓞 F) F v.val
  have hmem (y : (v.val.adicCompletion F)ˣ) : (s y).val ∈ A := by
    change (s y).val ∈ integralAdelesOutside F S
    delta integralAdelesOutside
    rw [Subring.mem_iInf]
    intro u
    rw [Subring.mem_iInf]
    intro hu
    have h1 : FiniteAdeleRing.ofAdicCompletion F v.val y.val u = 1 :=
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val _ u).trans
        (Pi.mulSingle_eq_of_ne (by rintro rfl; exact hu v.prop) _)
    change FiniteAdeleRing.ofAdicCompletion F v.val y.val u ∈ u.adicCompletionIntegers F
    rw [h1]
    exact (u.adicCompletionIntegers F).one_mem
  have ht : s w ∈ A.toSubmonoid.units :=
    ⟨hmem w, by
      change ((s w)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem w⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s w, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm

/-- Two S-local norm-one transporters into the half-open section differ by the projection
of an embedded local unit. -/
private theorem sAdeleFiniteOrbit_transporter_unique (v : S) (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : SAdeleRing F S) (g h : Nₛ)
    (hg : g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ)
    (hh : h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ) :
    g.val⁻¹ * h.val ∈ (embeddedFiniteLocalUnits F v.val).map
      (Units.map (adeleProjection F S).toMonoidHom) := by
  classical
  obtain ⟨t, ht, hgt⟩ := hg
  obtain ⟨t', ht', hht⟩ := hh
  dsimp only at hgt hht
  have e1 : (g.val * τ t) • sAdeleOrbitBasepoint F S (some (.inr v)) = x := by
    rw [mul_smul]
    change g.val • (τ t • sAdeleOrbitBasepoint F S (some (.inr v))) = x
    rw [hgt]
    exact smul_inv_smul g.val x
  have e2 : (h.val * τ t') • sAdeleOrbitBasepoint F S (some (.inr v)) = x := by
    rw [mul_smul]
    change h.val • (τ t' • sAdeleOrbitBasepoint F S (some (.inr v))) = x
    rw [hht]
    exact smul_inv_smul h.val x
  have hfix : ((g.val * τ t)⁻¹ * (h.val * τ t')) • sAdeleOrbitBasepoint F S (some (.inr v)) =
      sAdeleOrbitBasepoint F S (some (.inr v)) := by
    rw [mul_smul, e2, ← e1, inv_smul_smul]
  obtain ⟨w, hw⟩ := (sAdeleFiniteOrbit_transporter_smul F S v _).mp hfix
  have hgn : sIdeleNorm F S g.val = 1 := g.prop
  have hhn : sIdeleNorm F S h.val = 1 := h.prop
  have hN : ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) = t⁻¹ * t' := by
    rw [← sAdeleFiniteOrbit_transporter_sIdeleNorm F S v w, ← hw, map_mul, map_inv, map_mul,
      map_mul, hgn, hhn, hsection t, hsection t', one_mul, one_mul]
  have hwn : ‖(w : v.val.adicCompletion F)‖ = ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := by
    rw [← sAdeleFiniteOrbit_transporter_ideleNorm F v.val w, hN, Units.val_mul,
      Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv, inv_mul_eq_div]
  have hq : (1 : ℝ) < v.val.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have ha1 : (1 : ℝ) ≤ ((t : ℝ≥0) : ℝ) := by exact_mod_cast ht.1
  have ha2 : ((t : ℝ≥0) : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast ht.2
  have hb1 : (1 : ℝ) ≤ ((t' : ℝ≥0) : ℝ) := by exact_mod_cast ht'.1
  have hb2 : ((t' : ℝ≥0) : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast ht'.2
  have ha0 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by linarith
  obtain ⟨m, hm⟩ := sAdeleFiniteOrbit_transporter_norm_zpow F v.val w
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt'
    · exfalso
      have h1 : (v.val.asIdeal.absNorm : ℝ) ^ m ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_neg_one] at h1
      have h2 : (v.val.asIdeal.absNorm : ℝ)⁻¹ < ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) :=
        calc (v.val.asIdeal.absNorm : ℝ)⁻¹ = 1 / (v.val.asIdeal.absNorm : ℝ) := (one_div _).symm
          _ < 1 / ((t : ℝ≥0) : ℝ) := one_div_lt_one_div_of_lt ha0 ha2
          _ ≤ ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := div_le_div_of_nonneg_right hb1 ha0.le
      rw [← hwn, hm] at h2
      linarith
    · exact heq
    · exfalso
      have h1 : (v.val.asIdeal.absNorm : ℝ) ^ (1 : ℤ) ≤ (v.val.asIdeal.absNorm : ℝ) ^ m :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_one] at h1
      have h2 : ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) < v.val.asIdeal.absNorm :=
        lt_of_le_of_lt (div_le_self (by linarith) ha1) hb2
      rw [← hwn, hm] at h2
      linarith
  have hw1 : ‖(w : v.val.adicCompletion F)‖ = 1 := by rw [hm, hm0, zpow_zero]
  have htt : t' = t := by
    rw [hwn, div_eq_one_iff_eq ha0.ne'] at hw1
    exact Units.ext (NNReal.eq hw1)
  subst htt
  have hgh : g.val⁻¹ * h.val = Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) := by
    rw [← hw, mul_inv, mul_mul_mul_comm, inv_mul_cancel, mul_one]
  rw [hgh]
  refine ⟨IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_embeddedFiniteLocalUnits_iff]
  refine ⟨rfl, ?_, fun w' hw' ↦ ?_⟩
  · rw [show (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w).val.2 v.val = w.val from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val _ v.val).trans
        (Pi.mulSingle_eq_same _ _)]
    exact hw1
  · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val _ w').trans
      (Pi.mulSingle_eq_of_ne hw' _)

/-- Every point of the full S-local orbit has a norm-one transporter into the half-open
section. -/
private theorem sAdeleFiniteOrbit_transporter_exists (v : S) (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : SAdeleRing F S)
    (hx : x ∈ sAdeleFullOrbit F S (some (.inr v))) :
    ∃ g : Nₛ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v.val
  have hq : (1 : ℝ) < v.val.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hq0 : (0 : ℝ) < v.val.asIdeal.absNorm := by linarith
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (x := ((sIdeleNorm F S a : ℝ≥0) : ℝ))
    (y := (v.val.asIdeal.absNorm : ℝ))
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (sIdeleNorm F S a).ne_zero)) hq
  let s := Units.map (adeleProjection F S).toMonoidHom
    (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val (π ^ j))
  let t := sIdeleNorm F S (a * s)
  have hs : s⁻¹ • sAdeleOrbitBasepoint F S (some (.inr v)) =
      sAdeleOrbitBasepoint F S (some (.inr v)) :=
    (sAdeleFiniteOrbit_transporter_smul F S v s⁻¹).mpr ⟨(π ^ j)⁻¹, by rw [map_inv, map_inv]⟩
  refine ⟨⟨a * s * (τ t)⁻¹, ?_⟩, t, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hsection t]
    exact mul_inv_cancel _
  · have htv : ((t : ℝ≥0) : ℝ) =
        ((sIdeleNorm F S a : ℝ≥0) : ℝ) * (v.val.asIdeal.absNorm : ℝ) ^ (-j) := by
      change ((sIdeleNorm F S (a * s) : ℝ≥0) : ℝ) = _
      rw [map_mul, Units.val_mul, NNReal.coe_mul, sAdeleFiniteOrbit_transporter_sIdeleNorm,
        sAdeleFiniteOrbit_transporter_ideleNorm, Units.val_zpow_eq_zpow_val, norm_zpow, hπ,
        inv_zpow, zpow_neg]
    change (t : ℝ≥0) ∈ Set.Ico 1 (v.val.asIdeal.absNorm : ℝ≥0)
    rw [Set.mem_Ico, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, htv, NNReal.coe_one,
      NNReal.coe_natCast, zpow_neg, ← div_eq_mul_inv]
    constructor
    · rw [le_div_iff₀ (zpow_pos hq0 j), one_mul]
      exact hj.1
    · rw [div_lt_iff₀ (zpow_pos hq0 j), mul_comm, ← zpow_add_one₀ hq0.ne']
      exact hj.2
  · change τ t • sAdeleOrbitBasepoint F S (some (.inr v)) =
      (a * s * (τ t)⁻¹)⁻¹ • a • sAdeleOrbitBasepoint F S (some (.inr v))
    rw [← mul_smul, show (a * s * (τ t)⁻¹)⁻¹ * a = τ t * s⁻¹ by group, mul_smul, hs]

/-- Paper: Proposition 8.2.0.4(1), p. 386. Every point in the full S-local finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem sAdeleFiniteOrbit_transporter (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) (hτ : Continuous τ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : Aₛ)
    (hx : x ∈ sAdeleFullOrbit F S (some (.inr v))) :
    ∃ g : Nₛ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ ∧
      ∀ h : Nₛ, h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ →
        g.val⁻¹ * h.val ∈ (embeddedFiniteLocalUnits F v.val).map
          (Units.map (adeleProjection F S).toMonoidHom) := by
  obtain ⟨g, hg⟩ := sAdeleFiniteOrbit_transporter_exists F S v τ hsection x hx
  exact ⟨g, hg, fun h hh ↦ sAdeleFiniteOrbit_transporter_unique F S v τ hsection x g h hg hh⟩

/-- A global idele fixes the base point at a finite place exactly when it is inserted
at that place. -/
private theorem adeleFiniteOrbit_transporter_smul (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g • adeleOrbitBasepoint F (some (.inr v)) = adeleOrbitBasepoint F (some (.inr v)) ↔
      ∃ w : (v.adicCompletion F)ˣ, g = IdeleGroup.ofAdicCompletion (𝓞 F) F v w := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    change g.val * AdeleRing.ofAdicCompletion (𝓞 F) F v 0 =
      AdeleRing.ofAdicCompletion (𝓞 F) F v 0 at h
    have h1 : g.val.1 = 1 := by
      have hc := congrArg Prod.fst h
      change g.val.1 * 1 = 1 at hc
      rwa [mul_one] at hc
    have h2 : ∀ w, w ≠ v → g.val.2 w = 1 := by
      intro w hw
      have hb : (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w = 1 :=
        (FiniteAdeleRing.ofAdicCompletion_apply_coe F v 0 w).trans (Pi.mulSingle_eq_of_ne hw _)
      have hc : g.val.2 w * (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w =
          (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w := congrArg (fun a : 𝔸[F] ↦ a.2 w) h
      rwa [hb, mul_one] at hc
    let u : (v.adicCompletion F)ˣ := ⟨g.val.2 v, g.inv.2 v,
      congrArg (fun a : 𝔸[F] ↦ a.2 v) g.val_inv, congrArg (fun a : 𝔸[F] ↦ a.2 v) g.inv_val⟩
    refine ⟨u, Units.ext (Prod.ext h1 (FiniteAdeleRing.ext F fun w ↦ ?_))⟩
    refine Eq.trans ?_ (FiniteAdeleRing.ofAdicCompletion_apply_coe F v (g.val.2 v) w).symm
    obtain rfl | hw := eq_or_ne w v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hw, h2 w hw]
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change AdeleRing.ofAdicCompletion (𝓞 F) F v u.val * AdeleRing.ofAdicCompletion (𝓞 F) F v 0 =
      AdeleRing.ofAdicCompletion (𝓞 F) F v 0
    rw [← map_mul, mul_zero]

/-- Two norm-one transporters into the half-open section differ by an embedded local unit. -/
private theorem adeleFiniteOrbit_transporter_unique (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F]) (g h : N₁)
    (hg : g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ)
    (hh : h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ) :
    g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  classical
  obtain ⟨t, ht, hgt⟩ := hg
  obtain ⟨t', ht', hht⟩ := hh
  dsimp only at hgt hht
  have e1 : (g.val * τ t) • adeleOrbitBasepoint F (some (.inr v)) = x := by
    rw [mul_smul]
    change g.val • (τ t • adeleOrbitBasepoint F (some (.inr v))) = x
    rw [hgt]
    exact smul_inv_smul g.val x
  have e2 : (h.val * τ t') • adeleOrbitBasepoint F (some (.inr v)) = x := by
    rw [mul_smul]
    change h.val • (τ t' • adeleOrbitBasepoint F (some (.inr v))) = x
    rw [hht]
    exact smul_inv_smul h.val x
  have hfix : ((g.val * τ t)⁻¹ * (h.val * τ t')) • adeleOrbitBasepoint F (some (.inr v)) =
      adeleOrbitBasepoint F (some (.inr v)) := by
    rw [mul_smul, e2, ← e1, inv_smul_smul]
  obtain ⟨w, hw⟩ := (adeleFiniteOrbit_transporter_smul F v _).mp hfix
  have hgn : ideleNorm F g.val = 1 := g.prop
  have hhn : ideleNorm F h.val = 1 := h.prop
  have hN : ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v w) = t⁻¹ * t' := by
    rw [← hw, map_mul, map_inv, map_mul, map_mul, hgn, hhn, hsection t, hsection t', one_mul,
      one_mul]
  have hwn : ‖(w : v.adicCompletion F)‖ = ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := by
    rw [← sAdeleFiniteOrbit_transporter_ideleNorm F v w, hN, Units.val_mul,
      Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv, inv_mul_eq_div]
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have ha1 : (1 : ℝ) ≤ ((t : ℝ≥0) : ℝ) := by exact_mod_cast ht.1
  have ha2 : ((t : ℝ≥0) : ℝ) < v.asIdeal.absNorm := by exact_mod_cast ht.2
  have hb1 : (1 : ℝ) ≤ ((t' : ℝ≥0) : ℝ) := by exact_mod_cast ht'.1
  have hb2 : ((t' : ℝ≥0) : ℝ) < v.asIdeal.absNorm := by exact_mod_cast ht'.2
  have ha0 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by linarith
  obtain ⟨m, hm⟩ := sAdeleFiniteOrbit_transporter_norm_zpow F v w
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt'
    · exfalso
      have h1 : (v.asIdeal.absNorm : ℝ) ^ m ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_neg_one] at h1
      have h2 : (v.asIdeal.absNorm : ℝ)⁻¹ < ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) :=
        calc (v.asIdeal.absNorm : ℝ)⁻¹ = 1 / (v.asIdeal.absNorm : ℝ) := (one_div _).symm
          _ < 1 / ((t : ℝ≥0) : ℝ) := one_div_lt_one_div_of_lt ha0 ha2
          _ ≤ ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := div_le_div_of_nonneg_right hb1 ha0.le
      rw [← hwn, hm] at h2
      linarith
    · exact heq
    · exfalso
      have h1 : (v.asIdeal.absNorm : ℝ) ^ (1 : ℤ) ≤ (v.asIdeal.absNorm : ℝ) ^ m :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_one] at h1
      have h2 : ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) < v.asIdeal.absNorm :=
        lt_of_le_of_lt (div_le_self (by linarith) ha1) hb2
      rw [← hwn, hm] at h2
      linarith
  have hw1 : ‖(w : v.adicCompletion F)‖ = 1 := by rw [hm, hm0, zpow_zero]
  have htt : t' = t := by
    rw [hwn, div_eq_one_iff_eq ha0.ne'] at hw1
    exact Units.ext (NNReal.eq hw1)
  subst htt
  have hgh : g.val⁻¹ * h.val = IdeleGroup.ofAdicCompletion (𝓞 F) F v w := by
    rw [← hw, mul_inv, mul_mul_mul_comm, inv_mul_cancel, mul_one]
  rw [hgh, mem_embeddedFiniteLocalUnits_iff]
  refine ⟨rfl, ?_, fun w' hw' ↦ ?_⟩
  · rw [show (IdeleGroup.ofAdicCompletion (𝓞 F) F v w).val.2 v = w.val from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ v).trans (Pi.mulSingle_eq_same _ _)]
    exact hw1
  · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ w').trans
      (Pi.mulSingle_eq_of_ne hw' _)

/-- Every point of the full orbit has a norm-one transporter into the half-open section. -/
private theorem adeleFiniteOrbit_transporter_exists (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (x := ((ideleNorm F a : ℝ≥0) : ℝ))
    (y := (v.asIdeal.absNorm : ℝ))
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleNorm F a).ne_zero)) hq
  let s := IdeleGroup.ofAdicCompletion (𝓞 F) F v (π ^ j)
  let t := ideleNorm F (a * s)
  have hs : s⁻¹ • adeleOrbitBasepoint F (some (.inr v)) = adeleOrbitBasepoint F (some (.inr v)) :=
    (adeleFiniteOrbit_transporter_smul F v s⁻¹).mpr ⟨(π ^ j)⁻¹, by rw [map_inv]⟩
  refine ⟨⟨a * s * (τ t)⁻¹, ?_⟩, t, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hsection t]
    exact mul_inv_cancel _
  · have htv : ((t : ℝ≥0) : ℝ) =
        ((ideleNorm F a : ℝ≥0) : ℝ) * (v.asIdeal.absNorm : ℝ) ^ (-j) := by
      change ((ideleNorm F (a * s) : ℝ≥0) : ℝ) = _
      rw [map_mul, Units.val_mul, NNReal.coe_mul, sAdeleFiniteOrbit_transporter_ideleNorm,
        Units.val_zpow_eq_zpow_val, norm_zpow, hπ, inv_zpow, zpow_neg]
    change (t : ℝ≥0) ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)
    rw [Set.mem_Ico, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, htv, NNReal.coe_one,
      NNReal.coe_natCast, zpow_neg, ← div_eq_mul_inv]
    constructor
    · rw [le_div_iff₀ (zpow_pos hq0 j), one_mul]
      exact hj.1
    · rw [div_lt_iff₀ (zpow_pos hq0 j), mul_comm, ← zpow_add_one₀ hq0.ne']
      exact hj.2
  · change τ t • adeleOrbitBasepoint F (some (.inr v)) =
      (a * s * (τ t)⁻¹)⁻¹ • a • adeleOrbitBasepoint F (some (.inr v))
    rw [← mul_smul, show (a * s * (τ t)⁻¹)⁻¹ * a = τ t * s⁻¹ by group, mul_smul, hs]

/-- Paper: Proposition 8.2.0.4(2), p. 386. Every point in the full global finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem adeleFiniteOrbit_transporter (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ)
    (hτ : Continuous τ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ ∧
      ∀ h : N₁, h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ →
        g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  obtain ⟨g, hg⟩ := adeleFiniteOrbit_transporter_exists F v τ hsection x hx
  exact ⟨g, hg, fun h hh ↦ adeleFiniteOrbit_transporter_unique F v τ hsection x g h hg hh⟩

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full S-local orbit is
already the norm-one orbit of the distinguished base point. -/
theorem sAdeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    sAdeleNormOneOrbit F S (some (.inl v)) = sAdeleFullOrbit F S (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let s := singlePlaceIdeleNormSection F v
    let p := Units.map (adeleProjection F S).toMonoidHom
    have hτ (t : ℝ≥0ˣ) : sIdeleNorm F S (p (s t)) = t := by
      let A := integralAdelesOutside F S
      have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
        change (s u).val ∈ integralAdelesOutside F S
        delta integralAdelesOutside
        rw [Subring.mem_iInf]
        intro w
        rw [Subring.mem_iInf]
        intro _
        exact (w.adicCompletionIntegers F).one_mem
      have ht : s t ∈ A.toSubmonoid.units :=
        ⟨hmem t, by
          change ((s t)⁻¹).val ∈ A
          rw [← map_inv]
          exact hmem t⁻¹⟩
      let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
      exact ((sIdeleNorm_spec F S).1 g).symm.trans
        (singlePlaceIdeleNormSection_rightInverse F v t)
    let c := p (s (sIdeleNorm F S g)⁻¹)
    have hfix : c • sAdeleOrbitBasepoint F S (some (.inl v)) =
        sAdeleOrbitBasepoint F S (some (.inl v)) := by
      rw [Units.smul_def]
      change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (sIdeleNorm F S g)⁻¹).val) *
          adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
      rw [← map_mul, ← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hτ, mul_inv_cancel]
    · change (g * c) • sAdeleOrbitBasepoint F S (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full global orbit is
already the norm-one orbit of the distinguished base point. -/
theorem adeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    adeleNormOneOrbit F (some (.inl v)) = adeleFullOrbit F (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let c := singlePlaceIdeleNormSection F v (ideleNorm F g)⁻¹
    have hc : ideleNorm F c = (ideleNorm F g)⁻¹ :=
      singlePlaceIdeleNormSection_rightInverse F v _
    have hfix : c • adeleOrbitBasepoint F (some (.inl v)) =
        adeleOrbitBasepoint F (some (.inl v)) := by
      rw [Units.smul_def]
      change AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (ideleNorm F g)⁻¹).val *
          AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0
      rw [← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hc, mul_inv_cancel]
    · change (g * c) • adeleOrbitBasepoint F (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- The idele inserted at an infinite place has norm one exactly when the inserted
unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    ideleNorm F (IdeleGroup.ofCompletion (𝓞 F) F v u) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  classical
  rw [Units.ext_iff, Units.val_one, ← NNReal.coe_eq_one, ((ideleNorm_spec F).1 _).2]
  change (∏ w : InfinitePlace F, ‖Pi.mulSingle v (u : v.Completion) w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(1 : w.adicCompletion F)‖) = 1 ↔ _
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ _), Pi.mulSingle_eq_same]
  · exact pow_eq_one_iff_of_nonneg (norm_nonneg _) InfinitePlace.mult_pos.ne'
  · intro w _ hw
    simp only [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]

/-- At a real place the units of norm one are the two signs. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_unit (v : InfinitePlace F)
    (hv : v.IsReal) (u : v.Completionˣ) : ‖u.val‖ = 1 ↔ (u.val = 1 ∨ u.val = -1) := by
  let φ := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv
  rw [← hiso.norm_map_of_map_zero (map_zero φ) u.val, Real.norm_eq_abs, abs_eq zero_le_one]
  constructor
  · rintro (h | h)
    · exact Or.inl (hiso.injective (h.trans (map_one φ).symm))
    · exact Or.inr (hiso.injective (h.trans (by rw [map_neg, map_one])))
  · rintro (h | h)
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h, map_neg, map_one])

/-- An S-idele fixes the S-local base point at an infinite place exactly when it is the
projection of an idele inserted at that place. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : (SAdeleRing F S)ˣ) :
    g • sAdeleOrbitBasepoint F S (some (.inl v)) = sAdeleOrbitBasepoint F S (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = Units.map (adeleProjection F S).toMonoidHom
        (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : ∀ w : S, g.val.2 w = 1 := by
      intro w
      have hc := congrFun (congrArg Prod.snd h) w
      change g.val.2 w * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_))⟩
    · change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
    · change g.val.2 w = 1
      exact h2 w
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v u.val) *
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
      adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
    rw [← map_mul, ← map_mul, mul_zero]

/-- The projected idele inserted at an infinite place has S-norm one exactly when the
inserted unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofCompletion (𝓞 F) F v u)) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  let A := integralAdelesOutside F S
  let s := IdeleGroup.ofCompletion (𝓞 F) F v
  have hmem (y : v.Completionˣ) : (s y).val ∈ A := by
    change (s y).val ∈ integralAdelesOutside F S
    delta integralAdelesOutside
    rw [Subring.mem_iInf]
    intro w
    rw [Subring.mem_iInf]
    intro _
    exact (w.adicCompletionIntegers F).one_mem
  have ht : s u ∈ A.toSubmonoid.units :=
    ⟨hmem u, by
      change ((s u)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem u⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s u, ht⟩
  have hg : sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom (s u)) =
      ideleNorm F (s u) := ((sIdeleNorm_spec F S).1 g).symm
  rw [hg]
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u

/-- At an infinite place the S-local norm-one stabilizer of an orbit point consists of
the projected ideles inserted at that place with a unit of norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : SAdeleRing F S) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v)))
    (g : (SAdeleRing F S)ˣ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  obtain ⟨h, rfl⟩ := hx
  change sIdeleNorm F S g = 1 ∧ g • h • sAdeleOrbitBasepoint F S (some (.inl v)) =
    h • sAdeleOrbitBasepoint F S (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    sAdeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the S-local orbit is the image of the two local signs. -/
theorem sAdeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  rw [sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- A global idele fixes the base point at an infinite place exactly when it is inserted
at that place. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : 𝔸[F]ˣ) :
    g • adeleOrbitBasepoint F (some (.inl v)) = adeleOrbitBasepoint F (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    change g.val * AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0 at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : g.val.2 = 1 := by
      have hc := congrArg Prod.snd h
      change g.val.2 * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) h2)⟩
    change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
    obtain rfl | hw := eq_or_ne w v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change AdeleRing.ofCompletion (𝓞 F) F v u.val * AdeleRing.ofCompletion (𝓞 F) F v 0 =
      AdeleRing.ofCompletion (𝓞 F) F v 0
    rw [← map_mul, mul_zero]

/-- At an infinite place the global norm-one stabilizer of an orbit point consists of
the ideles inserted at that place with a unit of norm one. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧ g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  obtain ⟨h, rfl⟩ := hx
  change ideleNorm F g = 1 ∧ g • h • adeleOrbitBasepoint F (some (.inl v)) =
    h • adeleOrbitBasepoint F (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    adeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the global orbit is the image of the two local signs. -/
theorem adeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  rw [adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the S-local orbit is the image of the local unit circle. -/
theorem sAdeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the global orbit is the image of the local unit circle. -/
theorem adeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  exact adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g

/-- Paper: Proposition 8.2.0.6(1), p. 387. The closure of the positive section ray
relative to the S-local full-orbit union adds the single-zero base point. -/
theorem sAdeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set Aₛ := Set.range fun t : ℝ≥0ˣ ↦
      adeleProjection F S (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ sAdeleFullOrbitUnion F S =
      ray ∪ {sAdeleOrbitBasepoint F S (some (.inl v))} := by
  classical
  intro ray
  let ψ := InfinitePlace.Completion.extensionEmbedding v
  have hψ : Isometry ψ := InfinitePlace.Completion.isometry_extensionEmbedding v
  let φ : v.Completion → SAdeleRing F S := fun x ↦
    adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v x)
  have hp : Continuous (adeleProjection F S) :=
    continuous_fst.prodMk (continuous_pi fun u : S ↦
      (RestrictedProduct.continuous_eval u.val).comp continuous_snd)
  have hφ0 : Continuous fun x : v.Completion ↦ AdeleRing.ofCompletion (𝓞 F) F v x :=
    (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  have hφ : Continuous φ := hp.comp hφ0
  let e : ℝ := (v.mult : ℝ)⁻¹
  have he0 : 0 < e := inv_pos.mpr (by exact_mod_cast InfinitePlace.mult_pos)
  let r : ℝ≥0ˣ → v.Completion := fun t ↦ (infinitePlaceRealPower F v e t).val
  have hray : ∀ t, adeleProjection F S (singlePlaceIdeleNormSection F v t).val = φ (r t) :=
    fun t ↦ rfl
  have hψr : ∀ t, ψ (r t) = (((t.val : ℝ) ^ e : ℝ) : ℂ) := fun t ↦
    infinitePlaceRealPower_apply F v e t
  let K : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}
  have hK : IsClosed K :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  let C : Set (SAdeleRing F S) :=
    {y | y.2 = 1} ∩ (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y | y.1 w = 1}) ∩
      {y | ψ (y.1 v) ∈ K}
  have hC0 : IsClosed {y : SAdeleRing F S | y.2 = 1} := isClosed_eq continuous_snd continuous_const
  have hC1 : IsClosed (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y : SAdeleRing F S | y.1 w = 1}) :=
    isClosed_biInter fun w _ ↦
      isClosed_eq ((continuous_apply w).comp continuous_fst) continuous_const
  have hC2 : IsClosed {y : SAdeleRing F S | ψ (y.1 v) ∈ K} :=
    hK.preimage (hψ.continuous.comp ((continuous_apply v).comp continuous_fst))
  have hC : IsClosed C := (hC0.inter hC1).inter hC2
  have hrayC : ray ⊆ C := by
    rintro _ ⟨t, rfl⟩
    change adeleProjection F S (singlePlaceIdeleNormSection F v t).val ∈ C
    rw [hray]
    refine ⟨⟨rfl, Set.mem_iInter₂.mpr fun w hw ↦ ?_⟩, ?_⟩
    · exact Pi.mulSingle_eq_of_ne hw _
    · change ψ (Pi.mulSingle v (r t) v) ∈ K
      rw [Pi.mulSingle_eq_same, hψr]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩
  have hbase : sAdeleOrbitBasepoint F S (some (.inl v)) ∈ closure ray := by
    let tn : ℕ → ℝ≥0ˣ := fun n ↦ Units.mk0 ((n : ℝ≥0) + 1)⁻¹ (by positivity)
    have hn : ∀ n : ℕ, ‖r (tn n)‖ = ((n : ℝ) + 1)⁻¹ ^ e := by
      intro n
      rw [← hψ.norm_map_of_map_zero (map_zero ψ), hψr, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      simp [tn]
    have hlim : Filter.Tendsto (fun n ↦ r (tn n)) Filter.atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hn]
      have h1 : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ one_div _
      have h0 : (0 : ℝ) ^ e = 0 := Real.zero_rpow he0.ne'
      rw [← h0]
      exact (Real.continuousAt_rpow_const 0 e (Or.inr he0.le)).tendsto.comp h1
    have hlim' : Filter.Tendsto
        (fun n ↦ adeleProjection F S (singlePlaceIdeleNormSection F v (tn n)).val)
        Filter.atTop (𝓝 (sAdeleOrbitBasepoint F S (some (.inl v)))) := by
      simp_rw [hray]
      exact (hφ.tendsto 0).comp hlim
    exact mem_closure_of_tendsto hlim' (Filter.Eventually.of_forall fun n ↦ ⟨tn n, rfl⟩)
  ext y
  constructor
  · rintro ⟨hy, -⟩
    obtain ⟨⟨h2, h1⟩, him, hre⟩ := closure_minimal hrayC hC hy
    have hyφ : y = φ (y.1 v) := by
      refine Prod.ext (funext fun w ↦ ?_) h2
      change y.1 w = Pi.mulSingle v (y.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw]
        exact Set.mem_iInter₂.mp h1 w hw
    have hψy : ψ (y.1 v) = (((ψ (y.1 v)).re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
    rcases hre.eq_or_lt with h0 | hpos
    · right
      have hy0 : y.1 v = 0 := by
        apply hψ.injective
        rw [hψy, ← h0, Complex.ofReal_zero, map_zero]
      rw [Set.mem_singleton_iff, hyφ, hy0]
      rfl
    · left
      set s := (ψ (y.1 v)).re with hs
      let t : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (s ^ (v.mult : ℝ))) (by
        rw [ne_eq, Real.toNNReal_eq_zero, not_le]
        positivity)
      have ht : r t = y.1 v := by
        apply hψ.injective
        rw [hψr, hψy]
        congr 1
        change ((Real.toNNReal (s ^ (v.mult : ℝ)) : ℝ)) ^ e = s
        rw [Real.coe_toNNReal _ (by positivity), Real.rpow_rpow_inv hpos.le
          (by exact_mod_cast InfinitePlace.mult_pos.ne')]
      exact ⟨t, by
        change adeleProjection F S (singlePlaceIdeleNormSection F v t).val = y
        rw [hray, ht, ← hyφ]⟩
  · rintro (⟨t, rfl⟩ | hy)
    · refine ⟨subset_closure ⟨t, rfl⟩, Set.mem_iUnion.mpr ⟨none,
        Units.map (adeleProjection F S).toMonoidHom (singlePlaceIdeleNormSection F v t), ?_⟩⟩
      change _ • adeleProjection F S (1 : 𝔸[F]) = _
      rw [map_one, Units.smul_def, smul_eq_mul, mul_one]
      rfl
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hbase, Set.mem_iUnion.mpr ⟨some (.inl v), MulAction.mem_orbit_self _⟩⟩

/-- Paper: Proposition 8.2.0.6(2), p. 387. The closure of the positive section ray
relative to the global full-orbit union adds the single-zero base point. -/
theorem adeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set 𝔸[F] := Set.range fun t : ℝ≥0ˣ ↦ (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ adeleFullOrbitUnion F = ray ∪ {adeleOrbitBasepoint F (some (.inl v))} := by
  classical
  intro ray
  let ψ := InfinitePlace.Completion.extensionEmbedding v
  have hψ : Isometry ψ := InfinitePlace.Completion.isometry_extensionEmbedding v
  let φ : v.Completion → 𝔸[F] := fun x ↦ AdeleRing.ofCompletion (𝓞 F) F v x
  have hφ : Continuous φ :=
    (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  let e : ℝ := (v.mult : ℝ)⁻¹
  have he0 : 0 < e := inv_pos.mpr (by exact_mod_cast InfinitePlace.mult_pos)
  let r : ℝ≥0ˣ → v.Completion := fun t ↦ (infinitePlaceRealPower F v e t).val
  have hray : ∀ t, (singlePlaceIdeleNormSection F v t).val = φ (r t) := fun t ↦ rfl
  have hψr : ∀ t, ψ (r t) = (((t.val : ℝ) ^ e : ℝ) : ℂ) := fun t ↦
    infinitePlaceRealPower_apply F v e t
  let K : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}
  have hK : IsClosed K :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  let C : Set 𝔸[F] :=
    (⋂ w : HeightOneSpectrum (𝓞 F), {y | y.2 w = 1}) ∩
      (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y | y.1 w = 1}) ∩ {y | ψ (y.1 v) ∈ K}
  have hC0 : IsClosed (⋂ w : HeightOneSpectrum (𝓞 F), {y : 𝔸[F] | y.2 w = 1}) :=
    isClosed_iInter fun w ↦
      isClosed_eq ((RestrictedProduct.continuous_eval w).comp continuous_snd) continuous_const
  have hC1 : IsClosed (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y : 𝔸[F] | y.1 w = 1}) :=
    isClosed_biInter fun w _ ↦
      isClosed_eq ((continuous_apply w).comp continuous_fst) continuous_const
  have hC2 : IsClosed {y : 𝔸[F] | ψ (y.1 v) ∈ K} :=
    hK.preimage (hψ.continuous.comp ((continuous_apply v).comp continuous_fst))
  have hC : IsClosed C := (hC0.inter hC1).inter hC2
  have hrayC : ray ⊆ C := by
    rintro _ ⟨t, rfl⟩
    change (singlePlaceIdeleNormSection F v t).val ∈ C
    rw [hray]
    refine ⟨⟨Set.mem_iInter.mpr fun w ↦ ?_, Set.mem_iInter₂.mpr fun w hw ↦ ?_⟩, ?_⟩
    · rfl
    · exact Pi.mulSingle_eq_of_ne hw _
    · change ψ (Pi.mulSingle v (r t) v) ∈ K
      rw [Pi.mulSingle_eq_same, hψr]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩
  have hbase : adeleOrbitBasepoint F (some (.inl v)) ∈ closure ray := by
    let tn : ℕ → ℝ≥0ˣ := fun n ↦ Units.mk0 ((n : ℝ≥0) + 1)⁻¹ (by positivity)
    have hn : ∀ n : ℕ, ‖r (tn n)‖ = ((n : ℝ) + 1)⁻¹ ^ e := by
      intro n
      rw [← hψ.norm_map_of_map_zero (map_zero ψ), hψr, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      simp [tn]
    have hlim : Filter.Tendsto (fun n ↦ r (tn n)) Filter.atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hn]
      have h1 : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ one_div _
      have h0 : (0 : ℝ) ^ e = 0 := Real.zero_rpow he0.ne'
      rw [← h0]
      exact (Real.continuousAt_rpow_const 0 e (Or.inr he0.le)).tendsto.comp h1
    have hlim' : Filter.Tendsto (fun n ↦ (singlePlaceIdeleNormSection F v (tn n)).val) Filter.atTop
        (𝓝 (adeleOrbitBasepoint F (some (.inl v)))) := by
      simp_rw [hray]
      exact (hφ.tendsto 0).comp hlim
    exact mem_closure_of_tendsto hlim' (Filter.Eventually.of_forall fun n ↦ ⟨tn n, rfl⟩)
  ext y
  constructor
  · rintro ⟨hy, -⟩
    obtain ⟨⟨h2', h1⟩, him, hre⟩ := closure_minimal hrayC hC hy
    have h2 : y.2 = 1 := FiniteAdeleRing.ext F fun w ↦ Set.mem_iInter.mp h2' w
    have hyφ : y = φ (y.1 v) := by
      refine Prod.ext (funext fun w ↦ ?_) h2
      change y.1 w = Pi.mulSingle v (y.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw]
        exact Set.mem_iInter₂.mp h1 w hw
    have hψy : ψ (y.1 v) = (((ψ (y.1 v)).re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
    rcases hre.eq_or_lt with h0 | hpos
    · right
      have hy0 : y.1 v = 0 := by
        apply hψ.injective
        rw [hψy, ← h0, Complex.ofReal_zero, map_zero]
      rw [Set.mem_singleton_iff, hyφ, hy0]
      rfl
    · left
      set s := (ψ (y.1 v)).re with hs
      let t : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (s ^ (v.mult : ℝ))) (by
        rw [ne_eq, Real.toNNReal_eq_zero, not_le]
        positivity)
      have ht : r t = y.1 v := by
        apply hψ.injective
        rw [hψr, hψy]
        congr 1
        change ((Real.toNNReal (s ^ (v.mult : ℝ)) : ℝ)) ^ e = s
        rw [Real.coe_toNNReal _ (by positivity), Real.rpow_rpow_inv hpos.le
          (by exact_mod_cast InfinitePlace.mult_pos.ne')]
      exact ⟨t, by
        change (singlePlaceIdeleNormSection F v t).val = y
        rw [hray, ht, ← hyφ]⟩
  · rintro (⟨t, rfl⟩ | hy)
    · refine ⟨subset_closure ⟨t, rfl⟩,
        Set.mem_iUnion.mpr ⟨none, singlePlaceIdeleNormSection F v t, ?_⟩⟩
      change singlePlaceIdeleNormSection F v t • (1 : 𝔸[F]) = _
      rw [Units.smul_def, smul_eq_mul, mul_one]
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hbase, Set.mem_iUnion.mpr ⟨some (.inl v), MulAction.mem_orbit_self _⟩⟩

end RiemannMasullo
