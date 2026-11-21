/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.IntegralLattice
public import HilbertModularity.Geometry.TateModule.CoefficientDual
public import HilbertModularity.RepresentationTheory.DualLattice

/-! # Integral lattices in same-labelled dual Tate factors

The integral dual of the constructed labelled Tate lattice is stable in the
same-labelled contragredient factor. Its reduction is the contragredient of the
covariant reduction, so determinants are inverted. This implements the integral
covariant/cohomological convention of [TripathiGoswami], without asserting
an etale-cohomology comparison or finite generation for the chosen Darmon scheme.
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
  [IsScalarTower ℤ_[p] R L] [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R L]
  [Module.Finite ℤ_[p] (integralTate K A p)]
  (F : Type*) [Field F] [NumberField F] [Algebra ℚ L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    φ a = pointsMap K (AlgebraicClosure K) f)

/-- The constructed integral labelled lattice is free over the coefficient PID. -/
local instance labelledIntegralTateLattice_free (σ : F →ₐ[ℚ] L) :
    Module.Free R (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule :=
  Submodule.IsLattice.free (K := L)
    (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
    (labelledIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule

/-- The actual integral dual lattice inside the same-labelled contragredient Tate factor. -/
def labelledDualIntegralTateLattice (σ : F →ₐ[ℚ] L) :
    Subrepresentation ((labelledDualTateFactor K A p F L hL φ hφ σ).restrictScalars R) := by
  let ρ := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation
  let S := labelledIntegralTateLattice K A p L R F hL φ hφ σ
  let : Module.Free R S.toSubmodule := labelledIntegralTateLattice_free K A p L R F hL φ hφ σ
  change Subrepresentation (ρ.dual.restrictScalars R)
  exact Representation.dualLatticeSubrepresentation (R := R) (K := L)
    (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
    (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation
    (labelledIntegralTateLattice K A p L R F hL φ hφ σ)

/-- The constructed integral dual is a full stable lattice in the labelled dual Tate factor. -/
instance labelledDualIntegralTateLattice_isLattice (σ : F →ₐ[ℚ] L) :
    Submodule.IsLattice L (labelledDualIntegralTateLattice K A p L R F hL φ hφ σ).toSubmodule := by
  let S := labelledIntegralTateLattice K A p L R F hL φ hφ σ
  let : Module.Free R S.toSubmodule := labelledIntegralTateLattice_free K A p L R F hL φ hφ σ
  let result := Representation.dualLatticeSubrepresentation_isLattice (R := R) (K := L)
    (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
    (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation
    (labelledIntegralTateLattice K A p L R F hL φ hφ σ)
  exact result

/-- Reduction of the actual labelled integral dual equals the dual of the covariant reduction. -/
def labelledDualIntegralTateLatticeReductionEquiv (k : Type*) [CommRing k] [Algebra R k]
    (σ : F →ₐ[ℚ] L) :
    ((labelledDualIntegralTateLattice K A p L R F hL φ hφ σ).toRepresentation.baseChange k).Equiv
      ((labelledIntegralTateLattice K A p L R F hL φ hφ σ).toRepresentation.baseChange k).dual := by
  let S := labelledIntegralTateLattice K A p L R F hL φ hφ σ
  let : Module.Free R S.toSubmodule := labelledIntegralTateLattice_free K A p L R F hL φ hφ σ
  let result := Representation.dualLatticeReductionEquiv (R := R) (K := L)
    (V := (labelledTateSubrepresentation K A p F L hL φ hφ σ).toSubmodule)
    (labelledTateSubrepresentation K A p F L hL φ hφ σ).toRepresentation
    (labelledIntegralTateLattice K A p L R F hL φ hφ σ) k
  exact result


end AlgebraicGeometry.GroupScheme
