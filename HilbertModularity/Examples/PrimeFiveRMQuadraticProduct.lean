/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveRMBlockFactorization

/-! # Two quadratic reverse-characteristic-polynomial factors -/

public noncomputable section

namespace HilbertModularity.Examples

open Polynomial

/-- The rank-two Frobenius factor written in terms of its trace and a
specified determinant. -/
def quadraticTraceFactor {L : Type*} [Field L]
    (M : Matrix (Fin 2) (Fin 2) L) (q : L) : Polynomial L :=
  1 - C M.trace * X + C q * X ^ 2

/-- The quadratic factor has the manuscript's literal normalization. -/
theorem quadraticTraceFactor_formula {L : Type*} [Field L]
    (M : Matrix (Fin 2) (Fin 2) L) (q : L) :
    quadraticTraceFactor M q = 1 - C M.trace * X + C q * X ^ 2 := (rfl)

/-- The displayed factor is the reverse characteristic polynomial when
the matrix determinant is the supplied residue cardinality. -/
theorem quadraticTraceFactor_eq_charpolyRev {L : Type*} [Field L]
    (M : Matrix (Fin 2) (Fin 2) L) (q : L)
    (hdet : M.det = q) : quadraticTraceFactor M q = M.charpolyRev := by
  rw [charpolyRev_fin_two_general, hdet]
  rfl

/-- Once the full polynomial is the product of two rank-two factors,
their determinant identities turn that product into the displayed
quadratic trace formula. -/
theorem quadratic_factorization_of_charpolyRev_product
    {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι L) (M₀ M₁ : Matrix (Fin 2) (Fin 2) L)
    (q : L) (R : L[X])
    (hprod : M.charpolyRev = M₀.charpolyRev * M₁.charpolyRev)
    (hdet₀ : M₀.det = q) (hdet₁ : M₁.det = q)
    (hfull : M.charpolyRev = R) :
    (1 - C M₀.trace * X + C q * X ^ 2) *
      (1 - C M₁.trace * X + C q * X ^ 2) = R := by
  rw [charpolyRev_fin_two_general M₀,
    charpolyRev_fin_two_general M₁, hdet₀, hdet₁] at hprod
  exact hprod.symm.trans hfull

end HilbertModularity.Examples
