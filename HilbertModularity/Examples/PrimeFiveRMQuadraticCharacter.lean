/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveRMQuadraticProduct
public import HilbertModularity.Examples.PrimeFiveRMMatrixTrace

/-! # Quadratic factors expressed by a representation character -/

public noncomputable section

namespace HilbertModularity.Examples

open Polynomial

/-- A rank-two trace factor written with the intrinsic character of the
representation, independently of the basis used for its matrix. -/
theorem quadraticTraceFactor_eq_character
    {L G V : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) (g : G)
    (b : Module.Basis (Fin 2) L V) (q : L) :
    quadraticTraceFactor (LinearMap.toMatrix b b (ρ g)) q =
      1 - C (ρ.character g) * X + C q * X ^ 2 := by
  rw [quadraticTraceFactor_formula]
  rw [representation_matrixTrace_eq_character ρ g b]

/-- Replace both matrix traces in a two-factor polynomial by the characters
of the same labelled representations. -/
theorem characterFactors_of_quadraticProduct
    {L G V₀ V₁ : Type*} [Field L] [Group G]
    [AddCommGroup V₀] [Module L V₀] [FiniteDimensional L V₀]
    [AddCommGroup V₁] [Module L V₁] [FiniteDimensional L V₁]
    (ρ₀ : Representation L G V₀) (ρ₁ : Representation L G V₁)
    (g : G) (q : L) (R : L[X])
    (b₀ : Module.Basis (Fin 2) L V₀)
    (b₁ : Module.Basis (Fin 2) L V₁)
    (hpoly : quadraticTraceFactor (LinearMap.toMatrix b₀ b₀ (ρ₀ g)) q *
      quadraticTraceFactor (LinearMap.toMatrix b₁ b₁ (ρ₁ g)) q = R) :
    (1 - C (ρ₀.character g) * X + C q * X ^ 2) *
      (1 - C (ρ₁.character g) * X + C q * X ^ 2) = R := by
  rw [quadraticTraceFactor_eq_character ρ₀ g b₀ q,
    quadraticTraceFactor_eq_character ρ₁ g b₁ q] at hpoly
  exact hpoly

/-- Transport a product of two character quadratics across an equality of
the two character values at two Galois elements. -/
theorem characterFactors_transfer
    {L G V₀ V₁ : Type*} [Field L] [Group G]
    [AddCommGroup V₀] [Module L V₀] [FiniteDimensional L V₀]
    [AddCommGroup V₁] [Module L V₁] [FiniteDimensional L V₁]
    (ρ₀ : Representation L G V₀) (ρ₁ : Representation L G V₁)
    (g h : G) (D R : L[X])
    (hpoly : (1 - C (ρ₀.character h) * X + D) *
      (1 - C (ρ₁.character h) * X + D) = R)
    (h₀ : ρ₀.character g = ρ₀.character h)
    (h₁ : ρ₁.character g = ρ₁.character h) :
    (1 - C (ρ₀.character g) * X + D) *
      (1 - C (ρ₁.character g) * X + D) = R := by
  rw [h₀, h₁]
  exact hpoly

end HilbertModularity.Examples
