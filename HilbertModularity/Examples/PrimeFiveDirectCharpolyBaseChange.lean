/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.ReverseCharacteristicPolynomial
public import HilbertModularity.RepresentationTheory.DualLattice
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import HilbertModularity.RepresentationTheory.CompatiblePolynomials
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Intrinsic dual characteristic polynomials under scalar extension -/

public noncomputable section

namespace HilbertModularity.Examples

/-- The intrinsic reverse polynomial agrees with the reverse of the
intrinsic characteristic polynomial, using the public matrix formula. -/
theorem charpolyRev_eq_charpoly_reverse
    {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) :
    f.charpolyRev = f.charpoly.reverse := by
  let b := Module.finBasis K V
  have h := LinearMap.charpolyRev_toMatrix b f
  rw [← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix] at h
  exact h.symm

/-- Polynomial reversal commutes with an injective field extension map. -/
theorem polynomial_reverse_map_field
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Polynomial K) :
    (p.map (algebraMap K L)).reverse =
      p.reverse.map (algebraMap K L) := by
  simp only [Polynomial.reverse, Polynomial.natDegree_map,
    Polynomial.reflect_map]

/-- The dual representation has the same intrinsic reverse polynomial
after extending scalars, with the algebra map applied to coefficients. -/
theorem dualRepresentation_charpolyRev_baseChange_direct
    {K L G V : Type*} [Field K] [Field L] [Algebra K L]
    [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) :
    ((ρ.baseChange L).dual g).charpolyRev =
      ((ρ.dual g).charpolyRev).map (algebraMap K L) := by
  let e := Representation.dualBaseChangeEquiv L ρ
  have he := e.charpoly_eq g
  have hbc := LinearMap.charpoly_baseChange (A := L) (ρ.dual g)
  have hbc' : ((ρ.dual.baseChange L) g).charpoly =
      (ρ.dual g).charpoly.map (algebraMap K L) := by
    change ((ρ.dual g).baseChange L).charpoly = _
    exact hbc
  simp only [charpolyRev_eq_charpoly_reverse]
  calc
    ((ρ.baseChange L).dual g).charpoly.reverse =
        ((ρ.dual.baseChange L) g).charpoly.reverse :=
      congrArg Polynomial.reverse he.symm
    _ = (((ρ.dual g).charpoly).map (algebraMap K L)).reverse := by
      exact congrArg Polynomial.reverse hbc'
    _ = ((ρ.dual g).charpoly.reverse).map (algebraMap K L) :=
      polynomial_reverse_map_field (ρ.dual g).charpoly

/-- Carry an established dual polynomial through scalar extension using
the direct characteristic-polynomial map theorem. -/
theorem dualRepresentation_charpolyRev_baseChange_direct_of_polynomial
    {K L G V : Type*} [Field K] [Field L] [Algebra K L]
    [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) (R : Polynomial K)
    (hR : (ρ.dual g).charpolyRev = R) :
    ((ρ.baseChange L).dual g).charpolyRev = R.map (algebraMap K L) := by
  exact (dualRepresentation_charpolyRev_baseChange_direct (L := L) ρ g).trans
    (congrArg (fun P : Polynomial K => P.map (algebraMap K L)) hR)

end HilbertModularity.Examples
