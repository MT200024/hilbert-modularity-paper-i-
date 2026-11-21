/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.PrincipalUnitCharacter
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Group.Units

/-! # Integral characters of compact groups

A continuous character of a compact group into a local field takes values in
its integer units. The integral lift uses the actual valuation ring and is
canonical, supplying the residual character in [TripathiGoswami,
prime ordinary lemma].
-/

@[expose] public noncomputable section

namespace MonoidHom

variable {K G : Type*} [NormedField K] [Group G] [TopologicalSpace G] [CompactSpace G]

/-- A continuous character of a compact group has norm at most one. -/
theorem norm_coe_le_one_of_compact (χ : G →* Kˣ) (hχ : Continuous χ) (g : G) :
    ‖(χ g : K)‖ ≤ 1 := by
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_norm.comp (Units.continuous_val.comp hχ)).continuousOn
  have h := ha (Set.mem_univ (g * a))
  change ‖(χ (g * a) : K)‖ ≤ ‖(χ a : K)‖ at h
  rw [map_mul, Units.val_mul, norm_mul] at h
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr (χ a).ne_zero)).mp
    (by simpa only [one_mul] using h)

/-- A continuous character of a compact group takes values on the unit sphere. -/
theorem norm_coe_eq_one_of_compact (χ : G →* Kˣ) (hχ : Continuous χ) (g : G) :
    ‖(χ g : K)‖ = 1 := by
  apply le_antisymm (norm_coe_le_one_of_compact χ hχ g)
  have h := norm_coe_le_one_of_compact χ hχ g⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h
  exact (inv_le_one₀ (norm_pos_iff.mpr (χ g).ne_zero)).mp h

end MonoidHom

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel
open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
  [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]
  {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]

/-- A continuous compact-group character has integral values for the native valuation. -/
theorem character_vle_one (χ : G →* Kˣ) (hχ : Continuous χ) (g : G) :
    (χ g : K) ≤ᵥ 1 := by
  let : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let := Valued.toNormedField K (ValueGroupWithZero K)
  exact ((Valued.v (R := K)).vle_one_iff).mpr
    (Valued.toNormedField.norm_le_one_iff.mp (χ.norm_coe_le_one_of_compact hχ g))

/-- The canonical integral lift of a continuous character of a compact group. -/
def integerCharacter (χ : G →* Kˣ) (hχ : Continuous χ) : G →* 𝒪[K]ˣ where
  toFun g :=
    { val := ⟨(χ g : K), (valuation K).vle_one_iff.mp (character_vle_one K χ hχ g)⟩
      inv := ⟨(χ g⁻¹ : K), (valuation K).vle_one_iff.mp (character_vle_one K χ hχ g⁻¹)⟩
      val_inv := Subtype.ext (by simp)
      inv_val := Subtype.ext (by simp) }
  map_one' := Units.ext (Subtype.ext (by simp))
  map_mul' g h := Units.ext (Subtype.ext (by simp))

/-- Extension of the integral character recovers the original character exactly. -/
@[simp] theorem map_integerCharacter (χ : G →* Kˣ) (hχ : Continuous χ) :
    (Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)).comp (integerCharacter K χ hχ) = χ := by
  ext g
  rfl

/-- The canonical integral character is continuous for the native integer-ring topology. -/
theorem continuous_integerCharacter (χ : G →* Kˣ) (hχ : Continuous χ) :
    Continuous (integerCharacter K χ hχ) := by
  have he : Topology.IsEmbedding (Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (algebraMap 𝒪[K] K)).units_map
  apply he.isInducing.continuous_iff.mpr
  change Continuous ((Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)).comp
    (integerCharacter K χ hχ))
  rw [map_integerCharacter]
  exact hχ

/-- The actual integer ring is a full stable lattice in the character line. -/
def integerCharacterLattice (χ : G →* Kˣ) (hχ : Continuous χ) :
    Subrepresentation ((Representation.ofCharacter χ).restrictScalars 𝒪[K]) where
  toSubmodule := (Algebra.linearMap 𝒪[K] K).range
  apply_mem_toSubmodule g := by
    rintro x ⟨r, rfl⟩
    refine ⟨(integerCharacter K χ hχ g : 𝒪[K]) * r, ?_⟩
    change algebraMap 𝒪[K] K ((integerCharacter K χ hχ g : 𝒪[K]) * r) =
      (χ g : K) * algebraMap 𝒪[K] K r
    rw [map_mul]
    rfl

/-- The canonical integral character lattice is finitely generated and spans the actual field line. -/
instance integerCharacterLattice_isLattice (χ : G →* Kˣ) (hχ : Continuous χ) :
    Submodule.IsLattice K (integerCharacterLattice K χ hχ).toSubmodule where
  fg := Submodule.fg_range (Algebra.linearMap 𝒪[K] K)
  span_eq_top := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    have h1 : (1 : K) ∈ (integerCharacterLattice K χ hχ).toSubmodule :=
      ⟨1, map_one (algebraMap 𝒪[K] K)⟩
    simpa only [smul_eq_mul, mul_one] using
      (Submodule.span K ((integerCharacterLattice K χ hχ).toSubmodule : Set K)).smul_mem x
        (Submodule.subset_span h1)

/-- The determinant character of the canonical lattice is the canonical integral character. -/
theorem determinantCharacter_integerCharacterLattice (χ : G →* Kˣ) (hχ : Continuous χ) :
    Representation.determinantCharacter (integerCharacterLattice K χ hχ).toRepresentation =
      integerCharacter K χ hχ := by
  apply MonoidHom.ext
  intro g
  apply Units.map_injective (IsFractionRing.injective 𝒪[K] K)
  exact congrArg (fun f : G →* Kˣ => f g)
    ((Representation.map_determinantCharacter_characterLattice χ (integerCharacterLattice K χ hχ)).trans
      (map_integerCharacter K χ hχ).symm)

/-- Every continuous compact-group character has a full integral lattice whose
Teichmüller-normalized image is profinite pro-p. Finite image on a given subgroup
is preserved by this same normalization. -/
theorem exists_lattice_normalized_character
    (p : ℕ) [Fact p.Prime] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
    (χ : G →* Kˣ) (hχ : Continuous χ) (I : Subgroup G)
    (hI : (Set.range (χ.comp I.subtype)).Finite) :
    ∃ S : Subrepresentation ((Representation.ofCharacter χ).restrictScalars 𝒪[K]),
      ∃ hS : Submodule.IsLattice K S.toSubmodule,
      letI := hS
      Continuous (normalizedCharacterOfLattice K p χ S) ∧
      CompactSpace (normalizedCharacterOfLattice K p χ S).range ∧
      TotallyDisconnectedSpace (normalizedCharacterOfLattice K p χ S).range ∧
      (∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H]
        (f : (normalizedCharacterOfLattice K p χ S).range →* H),
        Continuous f → IsPGroup p f.range) ∧
      (Set.range ((normalizedCharacterOfLattice K p χ S).comp I.subtype)).Finite := by
  let S := integerCharacterLattice K χ hχ
  refine ⟨S, inferInstance, ?_⟩
  let P := normalizedCharacterLatticeImage K p χ S hχ
  refine ⟨continuous_normalizedCharacterOfLattice K p χ S hχ,
    inferInstanceAs (CompactSpace P), inferInstanceAs (TotallyDisconnectedSpace P), ?_, ?_⟩
  · intro H _ _ _ f hf
    exact isPGroup_range_normalizedCharacterOfLattice K p χ S f hf
  · exact finite_range_normalizedCharacterOfLattice_comp K p χ S I.subtype hI

end IsNonarchimedeanLocalField
