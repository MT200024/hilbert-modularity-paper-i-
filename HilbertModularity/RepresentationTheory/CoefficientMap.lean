/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.Topology.Continuous

/-! # Coefficient maps in fixed coordinates

Apply a coefficient homomorphism to the matrices of a representation on a
finite coordinate space. This realizes the coefficient enlargement in
[TripathiGoswamiRevised, Lemma `lem:promotion`] without choosing a new
representation with prescribed Frobenius polynomials.
-/

public noncomputable section

namespace Representation

variable {R S G n : Type*} [CommRing R] [CommRing S] [Monoid G]
  [Fintype n] [DecidableEq n]

/-- The representation obtained by mapping every matrix coefficient. -/
def mapCoefficients (f : R →+* S) (ρ : Representation R G (n → R)) :
    Representation S G (n → S) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    (f.mapMatrix.toMonoidHom.comp (LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp ρ))

/-- The coordinate matrix is the entrywise image of the original matrix. -/
@[simp] theorem toMatrix_mapCoefficients (f : R →+* S)
    (ρ : Representation R G (n → R)) (g : G) :
    LinearMap.toMatrixAlgEquiv' (ρ.mapCoefficients f g) =
      (LinearMap.toMatrixAlgEquiv' (ρ g)).map f := by
  exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _

/-- The identity coefficient map preserves the representation. -/
@[simp] theorem mapCoefficients_id (ρ : Representation R G (n → R)) :
    ρ.mapCoefficients (RingHom.id R) = ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrixAlgEquiv'.injective
  simp

/-- Coefficient enlargement preserves each labelled matrix entry. -/
@[simp] theorem mapCoefficients_apply_single (f : R →+* S)
    (ρ : Representation R G (n → R)) (g : G) (i j : n) :
    ρ.mapCoefficients f g (Pi.single j 1) i = f (ρ g (Pi.single j 1) i) := by
  have h := congrArg (fun M : Matrix n n S => M i j)
    (toMatrix_mapCoefficients f ρ g)
  simpa only [LinearMap.toMatrixAlgEquiv'_apply, Matrix.map_apply] using h

/-- The characteristic polynomial is mapped through the specified coefficients. -/
theorem charpoly_mapCoefficients (f : R →+* S)
    (ρ : Representation R G (n → R)) (g : G) :
    (ρ.mapCoefficients f g).charpoly = (ρ g).charpoly.map f := by
  rw [← LinearMap.charpoly_toMatrix (ρ.mapCoefficients f g) (Pi.basisFun S n),
    ← LinearMap.charpoly_toMatrix (ρ g) (Pi.basisFun R n)]
  change (LinearMap.toMatrixAlgEquiv' (ρ.mapCoefficients f g)).charpoly =
    (LinearMap.toMatrixAlgEquiv' (ρ g)).charpoly.map f
  rw [toMatrix_mapCoefficients, Matrix.charpoly_map]

/-- Continuous coefficient maps preserve the entrywise continuity convention. -/
theorem continuous_mapCoefficients [TopologicalSpace R] [TopologicalSpace S]
    [TopologicalSpace G] (f : R →+* S) (hf : Continuous f)
    (ρ : Representation R G (n → R))
    (hρ : ∀ i j, Continuous (fun g : G => ρ g (Pi.single j 1) i)) (i j : n) :
    Continuous (fun g : G => ρ.mapCoefficients f g (Pi.single j 1) i) := by
  simpa only [mapCoefficients_apply_single, Function.comp_def] using hf.comp (hρ i j)

/-- Trivial action remains trivial after coefficient enlargement. -/
theorem mapCoefficients_eq_one (f : R →+* S)
    (ρ : Representation R G (n → R)) (g : G) (h : ρ g = 1) :
    ρ.mapCoefficients f g = 1 := by
  change Matrix.toLinAlgEquiv' (f.mapMatrix (LinearMap.toMatrixAlgEquiv' (ρ g))) = 1
  rw [h, map_one, map_one, map_one]

end Representation
