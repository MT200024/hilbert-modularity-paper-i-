/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# Dimension calculations for real multiplication

A quotient preserved by a unital action of a coefficient field is a vector space
over that field. Comparing dimensions in the scalar tower determines its rank.
This is the algebraic step used for the period-lattice quotient in §4.3.

## Main results

* `finrank_eq_one_of_finrank_eq`: an extension-field module whose base-field
  dimension equals the degree of the extension has rank one.
-/

namespace HilbertModularity

/-- A module with base-field dimension equal to the coefficient-field degree
has dimension one over the coefficient field. -/
theorem finrank_eq_one_of_finrank_eq
    (F L Q : Type*) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [AddCommGroup Q] [Module F Q] [Module L Q] [IsScalarTower F L Q]
    (h : Module.finrank F Q = Module.finrank F L) : Module.finrank L Q = 1 := by
  have hdeg : Module.finrank F L ≠ 0 := Module.finrank_pos.ne'
  have htower := Module.finrank_mul_finrank F L Q
  rw [h] at htower
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hdeg) (by simpa using htower)

end HilbertModularity
