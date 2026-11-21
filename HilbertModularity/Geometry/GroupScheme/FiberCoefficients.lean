/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GroupObjectTorsion
public import HilbertModularity.Geometry.GroupScheme.Endomorphism
public import HilbertModularity.Geometry.TateModule.Multiplication
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Integral coefficients and multiplication on actual fibres

An integral endomorphism action on a commutative group scheme pulls back as
a ring action on its actual fibre. Finite, étale and surjective multiplication
are preserved by this pullback. These supply the fibre hypotheses for the
canonical-prime Tate/kernel comparison in [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable {S : Scheme.{u}} (K : Type u) [Field K]
  (A : CommGrp (Over S)) (x : Spec (CommRingCat.of K) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- A finite family endomorphism induces a finite endomorphism on every actual fibre. -/
theorem fiberEndomorphismMap_isFinite (f : End A) [IsFinite f.hom.hom.hom.left] :
    IsFinite (fiberEndomorphismMap K A x f).hom.hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @IsFinite) x f.hom.hom.hom inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- An étale family endomorphism induces an étale endomorphism on every actual fibre. -/
theorem fiberEndomorphismMap_etale (f : End A) [Etale f.hom.hom.hom.left] :
    Etale (fiberEndomorphismMap K A x f).hom.hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @Etale) x f.hom.hom.hom inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- A surjective family endomorphism induces a surjective endomorphism on every actual fibre. -/
theorem fiberEndomorphismMap_surjective (f : End A) [Surjective f.hom.hom.hom.left] :
    Surjective (fiberEndomorphismMap K A x f).hom.hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @Surjective) x f.hom.hom.hom inferInstance

/-- The actual pointwise multiplication map is the underlying categorical multiple of the identity. -/
theorem multiplicationMap_eq_nsmul (B : CommGrp (Over (Spec (CommRingCat.of K)))) (n : ℕ) :
    multiplicationMap K B.X n = (n • 𝟙 B).hom.hom.hom := by
  rw [CommGrp.nsmul_id_hom, multiplicationMap, Mon.Hom.hom_pow]
  rfl

/-- Actual multiplication on the fibre is the pullback of multiplication on the family. -/
theorem fiber_multiplicationMap (n : ℕ) :
    multiplicationMap K (fiber K A x).X n =
      (fiberEndomorphismMap K A x (n • 𝟙 A)).hom.hom.hom := by
  rw [multiplicationMap_eq_nsmul]
  congr 3
  change n • (1 : End (fiber K A x)) = fiberEndomorphismMap K A x (n • (1 : End A))
  rw [map_nsmul, map_one]

/-- Finite multiplication on a family remains finite on every actual fibre. -/
instance fiber_multiplication_isFinite (n : ℕ) [IsFinite (n • 𝟙 A).hom.hom.hom.left] :
    IsFinite (multiplicationMap K (fiber K A x).X n).left := by
  rw [fiber_multiplicationMap]
  exact fiberEndomorphismMap_isFinite K A x (n • 𝟙 A)

/-- Étale multiplication on a family remains étale on every actual fibre. -/
instance fiber_multiplication_etale (n : ℕ) [Etale (n • 𝟙 A).hom.hom.hom.left] :
    Etale (multiplicationMap K (fiber K A x).X n).left := by
  rw [fiber_multiplicationMap]
  exact fiberEndomorphismMap_etale K A x (n • 𝟙 A)

/-- Surjective multiplication on a family remains surjective on every actual fibre. -/
instance fiber_multiplication_surjective (n : ℕ) [Surjective (n • 𝟙 A).hom.hom.hom.left] :
    Surjective (multiplicationMap K (fiber K A x).X n).left := by
  rw [fiber_multiplicationMap]
  exact fiberEndomorphismMap_surjective K A x (n • 𝟙 A)

end AlgebraicGeometry.GroupScheme
