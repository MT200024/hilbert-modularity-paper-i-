/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.LatticeImage
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import HilbertModularity.RepresentationTheory.CoefficientDecomposition
public import HilbertModularity.RepresentationTheory.ScalarRestriction

/-! # Stable lattices in coefficient-labelled summands

Images of actual stable lattices under the canonical coefficient projections
are full stable lattices in the corresponding labelled representations. No
integrality of the primitive idempotents in the original lattice is assumed.
This supplies labelled integral constituents for the determinant argument in
[TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation.IntertwiningMap

variable {A G V W : Type*} [Semiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {τ : Representation A G W}

/-- An intertwiner carries an invariant submodule to an invariant submodule. -/
def mapSubrepresentation (f : ρ.IntertwiningMap τ) (S : Subrepresentation ρ) :
    Subrepresentation τ where
  toSubmodule := S.toSubmodule.map f.toLinearMap
  apply_mem_toSubmodule g := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨ρ g v, S.apply_mem_toSubmodule g hv, congrArg (fun l : V →ₗ[A] W => l v) (f.isIntertwining' g)⟩

@[simp]
theorem mapSubrepresentation_toSubmodule (f : ρ.IntertwiningMap τ) (S : Subrepresentation ρ) :
    (mapSubrepresentation f S).toSubmodule = S.toSubmodule.map f.toLinearMap := rfl

end Representation.IntertwiningMap

namespace Representation.IntertwiningMap

variable {R K G V W : Type*} [CommRing R] [CommRing K] [Algebra R K] [Monoid G]
  [AddCommMonoid V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommMonoid W] [Module K W] [Module R W] [IsScalarTower R K W]
  {ρ : Representation K G V} {τ : Representation K G W}

/-- A surjective intertwiner sends a full stable lattice to a full stable lattice. -/
theorem mapSubrepresentation_isLattice (f : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) (S : Subrepresentation (ρ.restrictScalars R))
    [Submodule.IsLattice K S.toSubmodule] :
    Submodule.IsLattice K ((f.restrictScalars R).mapSubrepresentation S).toSubmodule :=
  Submodule.IsLattice.map_of_surjective S.toSubmodule f.toLinearMap hf

end Representation.IntertwiningMap

namespace Representation

open Algebra.TensorProduct

variable (F K L : Type*) {G V : Type*} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L] [FiniteDimensional F K] [Algebra.IsSeparable F K]
  [Monoid G] [AddCommGroup V] [Module L V]
  [Module (L ⊗[F] K) V] [IsScalarTower L (L ⊗[F] K) V]
  (hL : ∀ x : K, ((minpoly F x).map (algebraMap F L)).Splits)
  (ρ : Representation L G V)
  (hρ : ∀ (g : G) (a : L ⊗[F] K) (v : V), ρ g (a • v) = a • ρ g v)

/-- The canonical coefficient projection, with codomain its actual labelled subrepresentation. -/
def coefficientProjectionIntertwiner (σ : K →ₐ[F] L) :
    ρ.IntertwiningMap (coefficientSubrepresentation F K L hL ρ hρ σ).toRepresentation where
  toLinearMap := (coefficientProjection F K L V hL σ).rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact (hρ g (embeddingIdempotent F K L hL σ) v).symm

/-- Every labelled vector is the projection of an ambient vector. -/
theorem coefficientProjectionIntertwiner_surjective (σ : K →ₐ[F] L) :
    Function.Surjective (coefficientProjectionIntertwiner F K L hL ρ hρ σ) := by
  rintro ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

variable (R : Type*) [CommRing R] [Algebra R L] [Module R V] [IsScalarTower R L V]
  (S : Subrepresentation (ρ.restrictScalars R))

/-- The image of the ambient integral lattice under a coefficient projection. -/
def coefficientLattice (σ : K →ₐ[F] L) :
    Subrepresentation ((coefficientSubrepresentation F K L hL ρ hρ σ).toRepresentation.restrictScalars R) :=
  ((coefficientProjectionIntertwiner F K L hL ρ hρ σ).restrictScalars R).mapSubrepresentation S

/-- Projecting an actual full stable lattice gives a full stable labelled lattice. -/
instance coefficientLattice_isLattice [Submodule.IsLattice L S.toSubmodule] (σ : K →ₐ[F] L) :
    Submodule.IsLattice L (coefficientLattice F K L hL ρ hρ R S σ).toSubmodule :=
  IntertwiningMap.mapSubrepresentation_isLattice
    (coefficientProjectionIntertwiner F K L hL ρ hρ σ)
    (coefficientProjectionIntertwiner_surjective F K L hL ρ hρ σ) S

variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R L]
  [Submodule.IsLattice L S.toSubmodule]

/-- The integral labelled lattice has the dimension of the labelled coefficient representation. -/
theorem coefficientLattice_finrank (σ : K →ₐ[F] L) :
    Module.finrank R (coefficientLattice F K L hL ρ hρ R S σ).toSubmodule =
      Module.finrank L (coefficientSubrepresentation F K L hL ρ hρ σ).toSubmodule :=
  congrArg Cardinal.toNat (Submodule.IsLattice.rank' L
    (coefficientLattice F K L hL ρ hρ R S σ).toSubmodule)

/-- A finite free basis of the actual integral coefficient-labelled lattice. -/
def coefficientLatticeBasis (σ : K →ₐ[F] L) :
    Module.Basis (Fin (Module.finrank R (coefficientLattice F K L hL ρ hρ R S σ).toSubmodule))
      R (coefficientLattice F K L hL ρ hρ R S σ).toSubmodule :=
  Module.finBasis R (coefficientLattice F K L hL ρ hρ R S σ).toSubmodule

/-- Reduction of a labelled full lattice preserves the characteristic-zero dimension. -/
theorem coefficientLattice_reduction_finrank (k : Type*) [Field k] [Algebra R k]
    (σ : K →ₐ[F] L) :
    Module.finrank k (k ⊗[R] (coefficientLattice F K L hL ρ hρ R S σ).toSubmodule) =
      Module.finrank L (coefficientSubrepresentation F K L hL ρ hρ σ).toSubmodule := by
  rw [Module.finrank_baseChange, coefficientLattice_finrank]

end Representation
