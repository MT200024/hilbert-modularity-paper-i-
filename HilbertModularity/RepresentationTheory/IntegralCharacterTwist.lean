/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.RepresentationTheory.CoefficientMap
public import HilbertModularity.RepresentationTheory.IntegralBaseChange
public import HilbertModularity.RepresentationTheory.Products
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Integral character twists and scalar extension

An integral character acts on a free stable lattice. Extending scalars gives
the corresponding character twist of its rational representation.
-/

public noncomputable section

open scoped TensorProduct

namespace Representation

variable {R G V : Type*} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V]

/-- Multiply an integral representation by a character valued in the units
of its coefficient ring. -/
def integralCharacterTwist (ρ : Representation R G V) (χ : G →* Rˣ) :
    Representation R G V where
  toFun g := (χ g : R) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

@[simp]
theorem integralCharacterTwist_apply (ρ : Representation R G V)
    (χ : G →* Rˣ) (g : G) (v : V) :
    ρ.integralCharacterTwist χ g v = (χ g : R) • ρ g v := (rfl)

/-- Rationalization of an integral twist is the twist of the rationalized
action by the same unit character. -/
def integralCharacterTwistBaseChangeEquiv
    (K : Type*) [Field K] [Algebra R K]
    (ρ : Representation R G V) (χ : G →* Rˣ) :
    ((ρ.integralCharacterTwist χ).baseChange K).Equiv
      ((ρ.baseChange K).characterTwist
        ((Units.map (algebraMap R K).toMonoidHom).comp χ)) := by
  refine .mk (LinearEquiv.refl K _) ?_
  intro g
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
      simp only [LinearMap.comp_apply,
        Representation.baseChange_tmul, integralCharacterTwist_apply,
        characterTwist_apply, MonoidHom.comp_apply, Units.coe_map]
      simp
  | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw

end Representation

namespace Representation

variable {R K k G V W : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Field k] [Finite k] [Algebra R k] [Group G]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

/- Swapping the factors preserves a product representation. -/
private def prodCommEquiv {F H U X : Type*} [Field F] [Group H]
    [AddCommGroup U] [Module F U] [AddCommGroup X] [Module F X]
    (ρ : Representation F H U) (σ : Representation F H X) :
    (ρ.prod σ).Equiv (σ.prod ρ) :=
  .mk (LinearEquiv.prodComm F U X) (by
    intro g
    apply LinearMap.ext
    intro x
    rfl)

/-- The *unordered* Jordan–Hölder factors of the reduction of a finite free
stable lattice over a discrete valuation ring are independent of the lattice.
Serre proves lattice independence for finite groups over a complete DVR in
[SerreFiniteGroups, Chapter 15, §15.2, Theorem 32, p. 125]. Its proof uses only
commensurability of the two stable lattices, so applies to an arbitrary group
when the stable lattices are already given; completeness is not used there.
The common map from the DVR to the finite field has maximal-ideal kernel,
and scalar extension from the residue field preserves equality of
Grothendieck classes.
This associated-graded product equivalence does not identify the character
on the chosen invariant subrepresentation. -/
theorem residualFactors_independent_of_freeLattice
    (ρ₁ : Representation R G V) (ρ₂ : Representation R G W)
    (e : (ρ₁.baseChange K).Equiv (ρ₂.baseChange K))
    (χ₁ χ₂ : G →* kˣ)
    (h₁ : ∃ S : Subrepresentation (ρ₁.baseChange k),
      Nonempty ((S.toRepresentation.prod
        ((ρ₁.baseChange k).quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((ofCharacter χ₁).prod (ofCharacter χ₂)))) :
    (∃ T : Subrepresentation (ρ₂.baseChange k),
      Nonempty ((T.toRepresentation.prod
        ((ρ₂.baseChange k).quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((ofCharacter χ₁).prod (ofCharacter χ₂)))) ∨
    (∃ T : Subrepresentation (ρ₂.baseChange k),
      Nonempty ((T.toRepresentation.prod
        ((ρ₂.baseChange k).quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((ofCharacter χ₂).prod (ofCharacter χ₁)))) := by
  sorry

/-- Write the lattice-independent associated graded in one fixed direct-sum
order. This normalizes the two cases of the cited source input by swapping
product summands; it makes no assertion about the invariant line itself. -/
theorem residualSemisimplification_independent_of_freeLattice
    (ρ₁ : Representation R G V) (ρ₂ : Representation R G W)
    (e : (ρ₁.baseChange K).Equiv (ρ₂.baseChange K))
    (χ₁ χ₂ : G →* kˣ)
    (h₁ : ∃ S : Subrepresentation (ρ₁.baseChange k),
      Nonempty ((S.toRepresentation.prod
        ((ρ₁.baseChange k).quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((ofCharacter χ₁).prod (ofCharacter χ₂)))) :
    ∃ T : Subrepresentation (ρ₂.baseChange k),
      Nonempty ((T.toRepresentation.prod
        ((ρ₂.baseChange k).quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((ofCharacter χ₁).prod (ofCharacter χ₂))) := by
  rcases residualFactors_independent_of_freeLattice ρ₁ ρ₂ e χ₁ χ₂ h₁ with
    ⟨T, hT⟩ | ⟨T, ⟨eT⟩⟩
  · exact ⟨T, hT⟩
  · exact ⟨T, ⟨eT.trans (prodCommEquiv (ofCharacter χ₂) (ofCharacter χ₁))⟩⟩

end Representation

namespace Representation.Equiv

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K G V} {τ : Representation K G W}

/-- An equivariant isomorphism identifies the actions on corresponding
invariant subspaces. -/
def subrepresentationCongr (e : ρ.Equiv τ) (S : Subrepresentation ρ) :
    S.toRepresentation.Equiv (e.subrepresentationOrderIso S).toRepresentation :=
  .mk (e.toLinearEquiv.submoduleMap S.toSubmodule) (by
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact e.toIntertwiningMap.isIntertwining ρ τ g v)

/-- The associated graded of a two-step invariant flag is transported by an
equivariant isomorphism, including its actual quotient representation. -/
def associatedGradedCongr (e : ρ.Equiv τ) (S : Subrepresentation ρ) :
    (S.toRepresentation.prod
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
      ((e.subrepresentationOrderIso S).toRepresentation.prod
        (τ.quotient (e.subrepresentationOrderIso S).toSubmodule
          (e.subrepresentationOrderIso S).apply_mem_toSubmodule)) :=
  Representation.Equiv.prod (subrepresentationCongr e S) (e.quotientCongr S)

end Representation.Equiv

namespace Representation

variable {R K G V W : Type*} [CommRing R] [Field K] [Algebra R K]
  [Group G] [AddCommGroup V] [Module R V] [Module.Finite R V]
  [AddCommGroup W] [Module K W]

/-- An integral model and an equivariant rationalization select an actual
stable lattice in the target coefficient-space action. -/
def transportedIntegralLattice (ρ₀ : Representation R G V)
    {ρ : Representation K G W} (e : (ρ₀.baseChange K).Equiv ρ) :
    letI : Module R W := Module.compHom W (algebraMap R K)
    letI : IsScalarTower R K W := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    Subrepresentation (ρ.restrictScalars R) := by
  letI : Module R W := Module.compHom W (algebraMap R K)
  letI : IsScalarTower R K W := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (e.toIntertwiningMap.restrictScalars R).mapSubrepresentation
    (integralBaseChangeLattice R R K ρ₀)

/-- The transported stable lattice is finite and spans the target
coefficient space. -/
theorem transportedIntegralLattice_isLattice (ρ₀ : Representation R G V)
    {ρ : Representation K G W} (e : (ρ₀.baseChange K).Equiv ρ) :
    letI : Module R W := Module.compHom W (algebraMap R K)
    letI : IsScalarTower R K W := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    Submodule.IsLattice K (transportedIntegralLattice ρ₀ e).toSubmodule := by
  let : Module R W := Module.compHom W (algebraMap R K)
  let : IsScalarTower R K W := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact IntertwiningMap.mapSubrepresentation_isLattice
    e.toIntertwiningMap e.toLinearEquiv.surjective
    (integralBaseChangeLattice R R K ρ₀)

end Representation

namespace Representation

variable {R K G : Type*} [CommRing R] [Field K] [Algebra R K] [Group G]

/-- Tensor extension of an integral action in its standard two-coordinate
basis is entrywise extension of its matrices. -/
def baseChangeIntegralCoordinatesEquiv
    (ρ : Representation R G (Fin 2 → R)) :
    (ρ.baseChange K).Equiv (ρ.mapCoefficients (algebraMap R K)) := by
  let b := Pi.basisFun R (Fin 2)
  refine .mk (b.baseChange K).equivFun ?_
  intro g
  apply (b.baseChange K).ext
  intro i
  have hb : (b.baseChange K).equivFun ((b.baseChange K) i) = Pi.single i 1 := by
    ext j
    simp only [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  change (b.baseChange K).equivFun ((ρ.baseChange K g) ((b.baseChange K) i)) =
    ρ.mapCoefficients (algebraMap R K) g
      ((b.baseChange K).equivFun ((b.baseChange K) i))
  rw [hb]
  ext j
  rw [mapCoefficients_apply_single, Module.Basis.baseChange_apply]
  change (b.baseChange K).repr (1 ⊗ₜ[R] (ρ g (b i))) j =
    algebraMap R K (ρ g (Pi.single i 1) j)
  rw [Module.Basis.baseChange_repr_tmul]
  simp [b, Algebra.smul_def]

/-- Reducing an integral character twist maps both the action and its
character through the same coefficient homomorphism. -/
theorem mapCoefficients_integralCharacterTwist
    (k : Type*) [Field k] (f : R →+* k)
    (ρ : Representation R G (Fin 2 → R)) (χ : G →* Rˣ) :
    (ρ.integralCharacterTwist χ).mapCoefficients f =
      (ρ.mapCoefficients f).characterTwist ((Units.map f.toMonoidHom).comp χ) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrixAlgEquiv'.injective
  ext i j
  simp only [LinearMap.toMatrixAlgEquiv'_apply,
    mapCoefficients_apply_single, integralCharacterTwist_apply,
    characterTwist_apply, MonoidHom.comp_apply, Units.coe_map]
  simp [smul_eq_mul]

omit [Algebra R K] in
/-- Entrywise scalar extension acts on an entrywise extended vector exactly
as the original action followed by the coefficient map. -/
theorem mapCoefficients_apply_map
    (f : R →+* K) (ρ : Representation R G (Fin 2 → R))
    (g : G) (v : Fin 2 → R) :
    ρ.mapCoefficients f g (fun i => f (v i)) = fun i => f (ρ g v i) := by
  ext i
  have hm : LinearMap.toMatrix' (ρ.mapCoefficients f g) =
      (LinearMap.toMatrix' (ρ g)).map f :=
    toMatrix_mapCoefficients f ρ g
  rw [← LinearMap.toMatrix'_mulVec]
  rw [hm]
  calc
    _ = f (((LinearMap.toMatrix' (ρ g)).mulVec v) i) := by
      simp [Matrix.mulVec, dotProduct, map_mul]
    _ = f ((ρ g v) i) := by rw [LinearMap.toMatrix'_mulVec]

/-- Entrywise coefficient changes compose in the same order as their ring
homomorphisms. -/
theorem mapCoefficients_comp
    {S T : Type*} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (ρ : Representation R G (Fin 2 → R)) :
    (ρ.mapCoefficients f).mapCoefficients g =
      ρ.mapCoefficients (g.comp f) := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.toMatrixAlgEquiv'.injective
  rw [toMatrix_mapCoefficients, toMatrix_mapCoefficients,
    toMatrix_mapCoefficients, Matrix.map_map]
  rfl

end Representation
