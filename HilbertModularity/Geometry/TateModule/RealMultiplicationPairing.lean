/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.Endomorphism
public import HilbertModularity.Geometry.TateModule.CoefficientDecomposition
public import HilbertModularity.NumberTheory.CyclotomicCharacter
public import HilbertModularity.RepresentationTheory.AlternatingDeterminant
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Polarized Tate pairings for full real multiplication

The named literature input supplies a pairing on the actual coefficient-labelled
Tate summand. Its determinant consequence is proved separately. Fullness is a
hypothesis on the endomorphisms of this abelian variety over its ground field;
it must not be inferred for a special fibre from fullness at the generic point.
-/

public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

section Algebraic

variable (K : Type u) [Field K] [CharZero K]
  (A : CommGrp (Over (Spec (CommRingCat.of K))))
  (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
  (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[p] L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* End A)

omit [CharZero K] [NumberField F] in
/-- The points action of a specified integral endomorphism is geometric. -/
theorem pointsEndomorphismAction_realized (a : 𝓞 F) :
    ∃ (f : A.X ⟶ A.X) (_ : IsMonHom f),
      ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ) a =
        pointsMap K (AlgebraicClosure K) f := by
  exact ⟨(φ a).hom.hom.hom, inferInstance, rfl⟩

/-- The native labelled Galois factor for the specified integral RM action. -/
@[expose] def endomorphismLabelledTate :=
  labelledTateSubrepresentation K A.X p F L hL
    ((pointsEndomorphismMap K (AlgebraicClosure K) A).comp φ)
    (pointsEndomorphismAction_realized K A F φ)

attribute [irreducible] endomorphismLabelledTate

end Algebraic

variable (K : Type u) [Field K] [CharZero K]
  (A : CommGrp (Over (Spec (CommRingCat.of K))))
  (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]
  (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] [Algebra ℚ L]
  [IsScalarTower ℚ ℚ_[p] L]
  (hL : ∀ x : F, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
  (φ : 𝓞 F →+* End A)

/-- Polarization and Weil-pairing input for **full totally real** endomorphisms.
The underlying proper smooth geometrically connected group is an abelian
variety. Its projectivity and an ample line bundle over `K` follow from
[MilneAV, Chapter I, Theorem 6.4 and Proposition 6.6(d), pp. 29–31].
Choose this line bundle and its polarization. The canonical
pairing, its nondegeneracy and Galois equivariance are [MilneAV, Chapter I,
Section 13, pp. 57--58, Lemma 13.1 and Proposition 13.2(a),(d)]. Rationalizing
removes the finite polarization kernel. The Rosati adjointness identity is in
Section 14, p. 61, and positivity is Theorem 14.3, p. 62.

Here `φ` identifies the full endomorphism ring with `𝓞 F`, so Rosati acts on
`F`. A positive involution on a totally real field is the identity: otherwise
`y = a - a† ≠ 0` has `y† = -y`, contradicting positivity of
`Tr(y y†) = -Tr(y²)`. Thus the specified RM action is self-adjoint. After
splitting coefficients, distinct embedding summands are orthogonal, and the
restriction to each summand is nondegenerate. Choosing a basis of the Tate
twist writes its Galois action as the cyclotomic multiplier below.

These standard consequences of the cited pairing and Rosati theorems are
included in this named admission; they are not a verbatim theorem of Milne.
No rank, determinant, manuscript comparison or specialized fullness is admitted.
The convention is covariant Tate modules and arithmetic cyclotomic action. -/
theorem exists_labelledTatePairing_of_full_realMultiplication
    [IsProper A.X.hom] [Smooth A.X.hom] [GeometricallyConnected A.X.hom]
    (hreal : NumberField.IsTotallyReal F) (hφ : Function.Bijective φ)
    (σ : F →ₐ[ℚ] L) :
    ∃ B : (endomorphismLabelledTate K A p F L hL φ σ).toSubmodule →ₗ[L]
        Module.Dual L (endomorphismLabelledTate K A p F L hL φ σ).toSubmodule,
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      ∀ g v w,
        B ((endomorphismLabelledTate K A p F L hL φ σ).toRepresentation g v)
          ((endomorphismLabelledTate K A p F L hL φ σ).toRepresentation g w) =
        (Field.cyclotomicCharacterWithCoefficients K p L g : L) * B v w := by
  sorry

/-- In rank two the native fixed-label determinant is exactly cyclotomic.
This is a deduction from the pairing input, not a determinant admission. -/
theorem det_labelledTate_of_full_realMultiplication
    [IsProper A.X.hom] [Smooth A.X.hom] [GeometricallyConnected A.X.hom]
    (hreal : NumberField.IsTotallyReal F) (hφ : Function.Bijective φ)
    (σ : F →ₐ[ℚ] L)
    (b : Module.Basis (Fin 2) L (endomorphismLabelledTate K A p F L hL φ σ).toSubmodule)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (LinearMap.toMatrix b b
      ((endomorphismLabelledTate K A p F L hL φ σ).toRepresentation g)).det =
        (Field.cyclotomicCharacterWithCoefficients K p L g : L) := by
  let h := exists_labelledTatePairing_of_full_realMultiplication K A p F L hL φ hreal hφ σ
  with_reducible
    exact HilbertModularity.det_eq_of_exists_alternating_similitude
      (K := L) (V := (endomorphismLabelledTate K A p F L hL φ σ).toSubmodule) b
      (fun g => (endomorphismLabelledTate K A p F L hL φ σ).toRepresentation g)
      (fun g => (Field.cyclotomicCharacterWithCoefficients K p L g : L))
      h g

end AlgebraicGeometry.GroupScheme
