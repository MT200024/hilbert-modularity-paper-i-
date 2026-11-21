/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarConjugation
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Polynomial invariants of coefficient conjugates

The actual scalar-conjugate tensor representation has the coefficient-conjugate
characteristic polynomial and determinant. These formulas transport the exact
determinant between local RM labels in [TripathiGoswami, prime determinant].
-/

@[expose] public noncomputable section
namespace Rep
variable {K G : Type*} [Field K] [Monoid G]
  (σ : K ≃+* K) (V : Rep K G) [Module.Finite K V]

/-- The characteristic polynomial of the actual conjugate tensor is coefficientwise conjugate. -/
theorem charpoly_scalarConjugate (g : G) :
    ((scalarConjugate σ V).ρ g).charpoly = (V.ρ g).charpoly.map σ.toRingHom := by
  let : Algebra K K := σ.toRingHom.toAlgebra
  let : Module K K := Algebra.toModule
  exact LinearMap.charpoly_baseChange (V.ρ g) K

/-- The determinant of the actual conjugate tensor is the conjugate determinant. -/
theorem det_scalarConjugate (g : G) :
    LinearMap.det ((scalarConjugate σ V).ρ g) = σ (LinearMap.det (V.ρ g)) := by
  let : Algebra K K := σ.toRingHom.toAlgebra
  let : Module K K := Algebra.toModule
  exact LinearMap.det_baseChange (V.ρ g)

end Rep

namespace Representation.Equiv
variable {K G V W : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K G V} {τ : Representation K G W}

/-- Equivariant linear equivalences preserve the determinant of every action operator. -/
theorem det_eq (e : ρ.Equiv τ) (g : G) : LinearMap.det (τ g) = LinearMap.det (ρ g) := by
  have he : e.toLinearEquiv.toLinearMap ∘ₗ ρ g ∘ₗ e.toLinearEquiv.symm.toLinearMap = τ g := by
    apply LinearMap.ext
    intro v
    change e (ρ g (e.symm v)) = τ g v
    simpa using e.toIntertwiningMap.isIntertwining ρ τ g (e.symm v)
  rw [← he, LinearMap.det_conj]

end Representation.Equiv
