/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.CoefficientLattice
public import HilbertModularity.RepresentationTheory.IntegralBaseChange
public import HilbertModularity.RepresentationTheory.ResidualDeterminant

/-! # Geometric Tate lattices from the integral inverse limit

The actual integral Tate representation supplies an ambient lattice after
coefficient extension whenever its integral module is finitely generated.
Projecting this lattice gives integral labelled factors. Finite generation is
an explicit geometric input; it is not asserted here for the chosen Darmon
scheme of [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (p : ℕ) [Fact p.Prime]
  (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L]
  (R : Type*) [CommRing R] [Algebra ℤ_[p] R] [Algebra R L]
  [IsScalarTower ℤ_[p] R L]

/-- The actual ambient integral Tate lattice after extending coefficients. -/
def integralTateLattice :
    Subrepresentation (((tateRepresentation K A p).baseChange L).restrictScalars R) :=
  Representation.iteratedIntegralBaseChangeLattice ℤ_[p] R L
    (integralTateRepresentation K A p) ℚ_[p]

/-- Finite generation of the integral Tate module gives a full stable ambient lattice. -/
instance integralTateLattice_isLattice [Module.Finite ℤ_[p] (integralTate K A p)] :
    Submodule.IsLattice L (integralTateLattice K A p L R).toSubmodule :=
  Representation.iteratedIntegralBaseChangeLattice_isLattice ℤ_[p] R L
    (integralTateRepresentation K A p) ℚ_[p]

variable (F : Type*) [Field F] [NumberField F] [Algebra ℚ L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    φ a = pointsMap K (AlgebraicClosure K) f)

/-- The labelled lattice obtained directly from the actual integral Tate module. -/
def labelledIntegralTateLattice (σ : F →ₐ[ℚ] L) :
    Subrepresentation
      ((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation.restrictScalars R) :=
  labelledTateLattice K A p F L hL φ hφ R (integralTateLattice K A p L R) σ

/-- Every labelled factor has a constructed full stable integral lattice when the integral Tate module is finite. -/
instance labelledIntegralTateLattice_isLattice [Module.Finite ℤ_[p] (integralTate K A p)]
    (σ : F →ₐ[ℚ] L) :
    Submodule.IsLattice L (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule :=
  labelledTateLattice_isLattice K A p F L hL φ hφ R (integralTateLattice K A p L R) σ

variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R L]
  [Module.Finite ℤ_[p] (integralTate K A p)]

/-- Reduction of the constructed labelled integral Tate lattice preserves the labelled dimension. -/
theorem labelledIntegralTateLattice_reduction_finrank (k : Type*) [Field k] [Algebra R k]
    (σ : F →ₐ[ℚ] L) :
    Module.finrank k (k ⊗[R] (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule) =
      Module.finrank L (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule :=
  labelledTateLattice_reduction_finrank K A p F L hL φ hφ R (integralTateLattice K A p L R) k σ

/-- One actual integral determinant realizes both the labelled geometric Tate determinant and its residual value. -/
theorem labelledIntegralTateLattice_determinant (k : Type*) [CommRing k] [Algebra R k]
    (σ : F →ₐ[ℚ] L) (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    ∃ d : R,
      algebraMap R L d =
        LinearMap.det (M := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
          ((labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation g) ∧
      algebraMap R k d =
        LinearMap.det (((labelledIntegralTateLattice K A p L R F hL φ hφ σ).toRepresentation.baseChange k) g) :=
  Representation.exists_integral_lattice_determinant (R := R) (K := L)
    (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
    (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation
    (labelledIntegralTateLattice K A p L R F hL φ hφ σ)
    (labelledTateLatticeBasis K A p F L hL φ hφ R (integralTateLattice K A p L R) σ) k g

end AlgebraicGeometry.GroupScheme
