/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.TeichmullerCharacter
public import HilbertModularity.RepresentationTheory.CharacterComparison
public import HilbertModularity.RepresentationTheory.DeterminantCharacter
public import HilbertModularity.RepresentationTheory.ResidualDeterminant

/-! # Principal-unit normalization from an actual stable lattice

A full stable lattice in a character representation supplies its integral
unit-valued character through the determinant of the lattice action. Its
characteristic-zero and residual realizations are the genuine scalar
extensions of that same lattice. This connects Teichmüller normalization to
the rank-one quotient in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {K G : Type*} [Field K] [Group G]

/-- The determinant character of a character line is the original character. -/
@[simp]
theorem determinantCharacter_ofCharacter (χ : G →* Kˣ) :
    determinantCharacter (ofCharacter χ) = χ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change LinearMap.det ((χ g : K) • (1 : Module.End K K)) = (χ g : K)
  simp

/-- On an actual one-dimensional representation, the determinant is its scalar action. -/
theorem apply_eq_determinantCharacter_smul
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (hV : Module.finrank K V = 1) (g : G) (v : V) :
    ρ g v = (determinantCharacter ρ g : K) • v := by
  obtain ⟨a, ha, _⟩ := (ρ g).existsUnique_eq_smul_id_of_finrank_eq_one hV
  have hd : LinearMap.det (ρ g) = a := by
    rw [ha, LinearMap.det_smul]
    simp [hV]
  rw [determinantCharacter_coe, hd, ha]
  rfl

/-- Every actual rank-one representation is the representation of its determinant character. -/
def equivDeterminantCharacter
    {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (hV : Module.finrank K V = 1) :
    ρ.Equiv (ofCharacter (determinantCharacter ρ)) :=
  let e : V ≃ₗ[K] K := (Module.nonempty_linearEquiv_of_finrank_eq_one hV).some.symm
  Representation.Equiv.mk e fun g => by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      apply_eq_determinantCharacter_smul ρ hV, map_smul,
      ofCharacter_apply, smul_eq_mul]

section RankOneLattice

variable {R V : Type*} [CommRing R] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (ρ : Representation K G V) (hV : Module.finrank K V = 1)
  (S : Subrepresentation (ρ.restrictScalars R))

/-- Transport the given stable lattice to the actual determinant-character line. -/
def determinantCharacterLattice :
    Subrepresentation ((ofCharacter (determinantCharacter ρ)).restrictScalars R) where
  toSubmodule := S.toSubmodule.map
    ((equivDeterminantCharacter ρ hV).toLinearEquiv.restrictScalars R).toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨ρ g v, S.apply_mem_toSubmodule g hv, ?_⟩
    exact IntertwiningMap.isIntertwining ρ (ofCharacter (determinantCharacter ρ))
      (equivDeterminantCharacter ρ hV).toIntertwiningMap g v

/-- Transport preserves the finite-generation and full-span conditions of the given lattice. -/
instance isLattice_determinantCharacterLattice [Submodule.IsLattice K S.toSubmodule] :
    Submodule.IsLattice K (determinantCharacterLattice ρ hV S).toSubmodule where
  fg := Submodule.IsLattice.fg.map _
  span_eq_top := by
    change Submodule.span K (S.toSubmodule.map
      ((equivDeterminantCharacter ρ hV).toLinearEquiv.restrictScalars R).toLinearMap : Set K) = ⊤
    rw [Submodule.map_coe]
    change Submodule.span K ((equivDeterminantCharacter ρ hV).toLinearEquiv.toLinearMap ''
      (S.toSubmodule : Set V)) = ⊤
    rw [← Submodule.map_span, Submodule.IsLattice.span_eq_top]
    simpa only [Submodule.map_top] using
      LinearMap.range_eq_top.mpr (equivDeterminantCharacter ρ hV).toLinearEquiv.surjective

/-- The transported lattice carries exactly the original integral representation. -/
def determinantCharacterLatticeEquiv :
    S.toRepresentation.Equiv (determinantCharacterLattice ρ hV S).toRepresentation :=
  Representation.Equiv.mk
    (((equivDeterminantCharacter ρ hV).toLinearEquiv.restrictScalars R).submoduleMap
      S.toSubmodule) fun g => by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact IntertwiningMap.isIntertwining ρ (ofCharacter (determinantCharacter ρ))
      (equivDeterminantCharacter ρ hV).toIntertwiningMap g v

end RankOneLattice

section Lattice

variable {R V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (ρ : Representation K G V) (S : Subrepresentation (ρ.restrictScalars R))
  [Submodule.IsLattice K S.toSubmodule]

/-- The canonical integral determinant of any full stable lattice realizes the field determinant. -/
theorem map_determinantCharacter_lattice :
    (Units.map (algebraMap R K : R →* K)).comp (determinantCharacter S.toRepresentation) =
      determinantCharacter ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  exact (det_latticeScalarExtension ρ S (Module.Free.chooseBasis R S.toSubmodule) g).symm

/-- The same integral character reduces to the determinant of the actual reduced lattice action. -/
theorem map_determinantCharacter_latticeReduction
    (k : Type*) [CommRing k] [Algebra R k] :
    (Units.map (algebraMap R k : R →* k)).comp (determinantCharacter S.toRepresentation) =
      determinantCharacter (S.toRepresentation.baseChange k) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  exact (det_latticeReduction ρ S (Module.Free.chooseBasis R S.toSubmodule) k g).symm

end Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Algebra R K] [IsFractionRing R K]
  (χ : G →* Kˣ) (S : Subrepresentation ((ofCharacter χ).restrictScalars R))
  [Submodule.IsLattice K S.toSubmodule]

/-- Any full stable lattice in a character line gives an integral lift of that exact character. -/
theorem map_determinantCharacter_characterLattice :
    (Units.map (algebraMap R K : R →* K)).comp (determinantCharacter S.toRepresentation) = χ := by
  rw [map_determinantCharacter_lattice, determinantCharacter_ofCharacter]

/-- The actual reduction of a full stable character lattice is one dimensional. -/
theorem finrank_characterLattice_reduction (k : Type*) [Field k] [Algebra R k] :
    Module.finrank k (k ⊗[R] S.toSubmodule) = 1 := by
  let b := Module.Free.chooseBasis R S.toSubmodule
  have h := (latticeScalarExtensionEquiv (ofCharacter χ) S b).toLinearEquiv.finrank_eq
  simpa [Module.finrank_baseChange] using h

/-- Continuity of the field character induces continuity of its integral lattice character
through the actual embedding of coefficient rings. -/
theorem continuous_determinantCharacter_characterLattice
    [TopologicalSpace R] [TopologicalSpace K] [TopologicalSpace G]
    (hR : Topology.IsEmbedding (algebraMap R K)) (hχ : Continuous χ) :
    Continuous (determinantCharacter S.toRepresentation) := by
  have he : Topology.IsEmbedding (Units.map (algebraMap R K : R →* K)) := hR.units_map
  apply he.isInducing.continuous_iff.mpr
  change Continuous ((Units.map (algebraMap R K : R →* K)).comp
    (determinantCharacter S.toRepresentation))
  rw [map_determinantCharacter_characterLattice]
  exact hχ

/-- Finite image of the original character on a specified subgroup implies finite image of the
actual integral lattice character on that same subgroup. -/
theorem finite_range_determinantCharacter_characterLattice_comp
    {H : Type*} [Group H] (i : H →* G) (hχ : (Set.range (χ.comp i)).Finite) :
    (Set.range ((determinantCharacter S.toRepresentation).comp i)).Finite := by
  let f := Units.map (algebraMap R K : R →* K)
  have he : f ∘ ((determinantCharacter S.toRepresentation).comp i) = χ.comp i :=
    funext fun h => congrArg (fun f : G →* Kˣ => f (i h))
      (map_determinantCharacter_characterLattice χ S)
  apply Set.Finite.of_finite_image (f := f) ?_
    (Units.map_injective (IsFractionRing.injective R K)).injOn
  rw [← Set.range_comp, he]
  exact hχ

/-- Transport to the rank-one character line preserves the original integral character,
and therefore its actual residual character. -/
theorem determinantCharacter_determinantCharacterLattice
    {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (ρ : Representation K G V) (hV : Module.finrank K V = 1)
    (T : Subrepresentation (ρ.restrictScalars R)) [Submodule.IsLattice K T.toSubmodule] :
    determinantCharacter (determinantCharacterLattice ρ hV T).toRepresentation =
      determinantCharacter T.toRepresentation := by
  apply MonoidHom.ext
  intro g
  apply Units.map_injective (IsFractionRing.injective R K)
  have h₁ := congrArg (fun f : G →* Kˣ => f g) (map_determinantCharacter_lattice ρ T)
  have h₂ := congrArg (fun f : G →* Kˣ => f g)
    (map_determinantCharacter_characterLattice (determinantCharacter ρ)
      (determinantCharacterLattice ρ hV T))
  exact h₂.trans h₁.symm

end Representation

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
  [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]
  (p : ℕ) [Fact p.Prime] [CharP (𝒪[K] ⧸ 𝓂[K]) p]
  {G : Type*} [Group G]
  (χ : G →* Kˣ)
  (S : Subrepresentation ((Representation.ofCharacter χ).restrictScalars 𝒪[K]))

/-- The field-valued Teichmüller lift of the actual residual character of a stable character lattice. -/
def teichmullerCharacterOfLattice : G →* Kˣ :=
  letI : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  (Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)).comp
    (Ideal.teichmullerCharacter 𝓂[K] p
      ((Units.map (Ideal.Quotient.mk 𝓂[K] : 𝒪[K] →* 𝒪[K] ⧸ 𝓂[K])).comp
        (Representation.determinantCharacter S.toRepresentation)))

/-- The original field character divided by the actual Teichmüller lift from its lattice. -/
def normalizedCharacterOfLattice : G →* Kˣ :=
  χ * (teichmullerCharacterOfLattice K p χ S)⁻¹

variable [Submodule.IsLattice K S.toSubmodule]

/-- The field normalization is exactly the image of the integral principal-unit normalization. -/
theorem map_normalizedCharacterOfLattice :
    (Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)).comp
      (normalizedCharacter K p (Representation.determinantCharacter S.toRepresentation)) =
      normalizedCharacterOfLattice K p χ S := by
  apply MonoidHom.ext
  intro g
  change Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)
      (Representation.determinantCharacter S.toRepresentation g *
        (Ideal.teichmullerCharacter 𝓂[K] p
          ((Units.map (Ideal.Quotient.mk 𝓂[K] : 𝒪[K] →* 𝒪[K] ⧸ 𝓂[K])).comp
            (Representation.determinantCharacter S.toRepresentation)) g)⁻¹) = _
  rw [map_mul, map_inv]
  have hg := congrArg (fun f : G →* Kˣ => f g)
    (Representation.map_determinantCharacter_characterLattice χ S)
  change Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)
    (Representation.determinantCharacter S.toRepresentation g) = χ g at hg
  rw [hg]
  rfl

omit [IsUniformAddGroup K] in
/-- Continuity of the original character gives continuity on every actual full stable lattice. -/
theorem continuous_characterLattice [TopologicalSpace G] (hχ : Continuous χ) :
    Continuous (Representation.determinantCharacter S.toRepresentation) :=
  Representation.continuous_determinantCharacter_characterLattice χ S
    Topology.IsEmbedding.subtypeVal hχ

/-- Teichmüller normalization of a continuous field character is continuous. -/
theorem continuous_normalizedCharacterOfLattice [TopologicalSpace G] (hχ : Continuous χ) :
    Continuous (normalizedCharacterOfLattice K p χ S) := by
  let : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  let : DiscreteTopology (𝒪[K] ⧸ 𝓂[K]) :=
    QuotientAddGroup.discreteTopology (IsLocalRing.isOpen_maximalIdeal 𝒪[K])
  rw [← map_normalizedCharacterOfLattice K p χ S]
  exact (Continuous.units_map (algebraMap 𝒪[K] K : 𝒪[K] →* K) continuous_subtype_val).comp
    (Ideal.continuous_teichmullerNormalizedCharacter 𝓂[K] p
      (Representation.determinantCharacter S.toRepresentation)
      (continuous_characterLattice K χ S hχ))

/-- The field-normalized image is the image of the integral normalized subgroup under inclusion. -/
theorem range_normalizedCharacterOfLattice :
    Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K) ''
      Set.range (normalizedCharacter K p (Representation.determinantCharacter S.toRepresentation)) =
      Set.range (normalizedCharacterOfLattice K p χ S) := by
  rw [← Set.range_comp]
  exact congrArg (fun f : G →* Kˣ => Set.range f) (map_normalizedCharacterOfLattice K p χ S)

/-- Integral and field-valued normalized images have the same actual topology. -/
def normalizedLatticeImageHomeomorph :
    (normalizedCharacter K p (Representation.determinantCharacter S.toRepresentation)).range ≃ₜ
      (normalizedCharacterOfLattice K p χ S).range :=
  ((Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (algebraMap 𝒪[K] K)).units_map.homeomorphImage
        (Set.range (normalizedCharacter K p
          (Representation.determinantCharacter S.toRepresentation)))).trans
    (Homeomorph.setCongr (range_normalizedCharacterOfLattice K p χ S))

/-- The actual field-valued normalized image of a continuous character of a compact group
is profinite, for every full stable lattice. -/
def normalizedCharacterLatticeImage
    [TopologicalSpace G] [CompactSpace G] (hχ : Continuous χ) : ProfiniteGrp :=
  letI := totallyDisconnectedSpace_integerUnits K
  letI : CompactSpace
      (normalizedCharacter K p (Representation.determinantCharacter S.toRepresentation)).range :=
    isCompact_iff_compactSpace.mp (isCompact_range_normalizedCharacter K p _
      (continuous_characterLattice K χ S hχ))
  let e := normalizedLatticeImageHomeomorph K p χ S
  letI := e.compactSpace
  letI := e.totallyDisconnectedSpace
  ProfiniteGrp.of (normalizedCharacterOfLattice K p χ S).range

/-- Every continuous discrete image of the actual field-valued normalized image is a p-group. -/
theorem isPGroup_range_normalizedCharacterOfLattice
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : (normalizedCharacterOfLattice K p χ S).range →* H) (hf : Continuous f) :
    IsPGroup p f.range := by
  let e := normalizedLatticeImageHomeomorph K p χ S
  let φ : (normalizedCharacter K p
      (Representation.determinantCharacter S.toRepresentation)).range →*
      (normalizedCharacterOfLattice K p χ S).range :=
    { toFun := e
      map_one' := Subtype.ext (map_one (Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)))
      map_mul' := fun x y =>
        Subtype.ext (map_mul (Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K)) (x : 𝒪[K]ˣ) (y : 𝒪[K]ˣ)) }
  have hp := isPGroup_range_normalizedCharacter_image K p
    (Representation.determinantCharacter S.toRepresentation) (f.comp φ) (hf.comp e.continuous)
  rw [MonoidHom.range_comp, φ.range_eq_top_of_surjective e.surjective, Subgroup.map_top] at hp
  exact hp

/-- Every continuous discrete quotient of the actual normalized profinite image is a p-group. -/
theorem isPGroup_range_normalizedCharacterLatticeImage
    [TopologicalSpace G] [CompactSpace G] (hχ : Continuous χ)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : normalizedCharacterLatticeImage K p χ S hχ →* H) (hf : Continuous f) :
    IsPGroup p f.range :=
  isPGroup_range_normalizedCharacterOfLattice K p χ S f hf

/-- Finite image on a specified subgroup survives Teichmüller normalization for every full
stable lattice. Applied to inertia, the finite-image premise remains the separate arithmetic input. -/
theorem finite_range_normalizedCharacterOfLattice_comp
    {H : Type*} [Group H] (i : H →* G) (hχ : (Set.range (χ.comp i)).Finite) :
    (Set.range ((normalizedCharacterOfLattice K p χ S).comp i)).Finite := by
  let : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  have hi := Representation.finite_range_determinantCharacter_characterLattice_comp χ S i hχ
  have hn := Ideal.finite_range_teichmullerNormalizedCharacter_comp 𝓂[K] p i
    (Representation.determinantCharacter S.toRepresentation) hi
  have he : Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K) ∘
      ((normalizedCharacter K p (Representation.determinantCharacter S.toRepresentation)).comp i) =
      (normalizedCharacterOfLattice K p χ S).comp i :=
    funext fun h => congrArg (fun f : G →* Kˣ => f (i h))
      (map_normalizedCharacterOfLattice K p χ S)
  change (Set.range ((normalizedCharacter K p
    (Representation.determinantCharacter S.toRepresentation)).comp i)).Finite at hn
  have hm := hn.image (Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K))
  rw [← Set.range_comp, he] at hm
  exact hm

end IsNonarchimedeanLocalField
