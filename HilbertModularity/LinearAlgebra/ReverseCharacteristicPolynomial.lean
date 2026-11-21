/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Intrinsic reverse characteristic polynomials

The reverse characteristic polynomial can be transported through a linear
equivalence without transferring a dependent basis. Its matrix expression is
`det(1 - X * f)`, including when its degree is smaller than the dimension.
The proof reuses [mathlib_5ed296525643, `LinearEquiv.charpoly_conj` and
`Matrix.reverse_charpoly`].
-/

public noncomputable section

namespace LinearMap

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The intrinsic reverse characteristic polynomial of an endomorphism. -/
def charpolyRev (f : Module.End K V) : Polynomial K := f.charpoly.reverse

/-- A finite basis computes the same intrinsic reverse polynomial. -/
theorem charpolyRev_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (f : Module.End K V) :
    (toMatrix b b f).charpolyRev = f.charpolyRev := by
  rw [charpolyRev, ← Matrix.reverse_charpoly, charpoly_toMatrix]

/-- Conjugation preserves the intrinsic polynomial without a choice of bases. -/
theorem charpolyRev_conj (e : V ≃ₗ[K] W) (f : Module.End K V) :
    (e.conj f).charpolyRev = f.charpolyRev := by
  simp only [charpolyRev, LinearEquiv.charpoly_conj]

end LinearMap
