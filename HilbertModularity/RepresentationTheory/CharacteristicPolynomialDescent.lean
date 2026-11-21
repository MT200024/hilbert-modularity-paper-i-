/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CompatiblePolynomials
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Characteristic polynomials descend from a coefficient extension

An equivariant equivalence after scalar extension identifies characteristic
polynomials before scalar extension, because the coefficient field embeds in
the extension. The specified algebra structure records the embedding used in
the comparison. This is a reusable prerequisite for Frobenius detection;
it does not construct an arithmetic comparison or a coefficient embedding.
-/

public noncomputable section

namespace Representation.Equiv

variable {K L G V W : Type*} [Field K] [Field L] [Algebra K L] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {ρ : Representation K G V} {σ : Representation K G W}

/-- If two representations become equivalent over a specified coefficient
extension, their characteristic polynomials were already equal over the
smaller field. -/
theorem charpoly_eq_of_baseChange
    (e : (ρ.baseChange L).Equiv (σ.baseChange L)) (g : G) :
    (ρ g).charpoly = (σ g).charpoly := by
  apply Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective
  calc
    (ρ g).charpoly.map (algebraMap K L) = ((ρ.baseChange L) g).charpoly := by
      symm
      exact LinearMap.charpoly_baseChange (ρ g) L
    _ = ((σ.baseChange L) g).charpoly := e.charpoly_eq g
    _ = (σ g).charpoly.map (algebraMap K L) :=
      LinearMap.charpoly_baseChange (σ g) L

end Representation.Equiv
