/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.RealMultiplicationPairing
public import HilbertModularity.Geometry.GroupScheme.Fiber
public import HilbertModularity.Geometry.ProjectiveLine.RationalCoordinate

/-! # Specializing self-adjoint real multiplication

The generic endomorphism ring is required to be full. Special fibres retain
the specified self-adjoint action, even when they acquire extra endomorphisms.
-/

public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField

namespace AlgebraicGeometry.GroupScheme

/-- Relative polarization and Weil pairing, specialized to the punctured line.
This is the standard relative consequence of [MilneAV, Chapter I, Theorem 6.4,
Proposition 6.6(d), Section 13 Lemma 13.1 and Proposition 13.2(a),(d), and
Section 14 Theorem 14.3], together with [MilneAbelianMotives, Theorem 3.5].
The latter extends homomorphisms of generic abelian fibres uniquely over a
connected noetherian normal base; our punctured line is such a base.

Choose a generic polarization. Full totally real generic endomorphisms force
its Rosati involution to fix the specified RM action. Extend the polarization
to the dual abelian scheme, and extend an integral multiple of its inverse.
Uniqueness extends both multiplication identities, symmetry and RM
self-adjointness. The specialized map is therefore a symmetric isogeny at
every fibre. Its rational Weil pairing is alternating, nondegenerate and
cyclotomic-equivariant. Self-adjointness makes distinct split coefficient
summands orthogonal, so each labelled restriction is nondegenerate.

This named input includes those standard relative-duality and pairing
consequences, not a verbatim assertion of Theorem 3.5. It assumes neither rank
two nor any determinant identity. Fullness is imposed only at the generic
point; no fullness of specialized endomorphisms is asserted. The convention
is covariant Tate modules and arithmetic cyclotomic action. -/
theorem exists_fiberLabelledTatePairing_of_generic_full_realMultiplication
    (K : Type) [Field K] [CharZero K]
    (A : CommGrp (Over (ProjectiveLine.punctured K)))
    [IsProper A.X.hom] [Smooth A.X.hom] [GeometricallyConnected A.X.hom]
    (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F]
    (L : Type) [NormedField L] [NormedAlgebra ℚ_[p] L] [Algebra ℚ L]
    [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : F, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (φ : 𝓞 F →+* End A) (hreal : NumberField.IsTotallyReal F)
    (hφ : Function.Bijective
      ((fiberEndomorphismMap (RatFunc K) A
        (ProjectiveLine.puncturedRationalPoint K)).comp φ))
    (E : Type) [Field E] [CharZero E]
    (x : Spec (CommRingCat.of E) ⟶ ProjectiveLine.punctured K) (σ : F →ₐ[ℚ] L) :
    ∃ B : (endomorphismLabelledTate E (fiber E A x) p F L hL
        ((fiberEndomorphismMap E A x).comp φ) σ).toSubmodule →ₗ[L]
      Module.Dual L (endomorphismLabelledTate E (fiber E A x) p F L hL
        ((fiberEndomorphismMap E A x).comp φ) σ).toSubmodule,
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      ∀ g v w,
        B ((endomorphismLabelledTate E (fiber E A x) p F L hL
            ((fiberEndomorphismMap E A x).comp φ) σ).toRepresentation g v)
          ((endomorphismLabelledTate E (fiber E A x) p F L hL
            ((fiberEndomorphismMap E A x).comp φ) σ).toRepresentation g w) =
        (Field.cyclotomicCharacterWithCoefficients E p L g : L) * B v w := by
  sorry

end AlgebraicGeometry.GroupScheme
