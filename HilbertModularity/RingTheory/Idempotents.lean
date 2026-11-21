/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Maps from a product algebra determined by an idempotent

An idempotent defines the algebra map from the two constant components. Evaluating
it at a field-valued point selects exactly one of the two projections.
-/

@[expose] public section
namespace IsIdempotentElem
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {e : A} (he : IsIdempotentElem e)

/-- An idempotent defines the map from the two-component constant algebra. -/
def prodAlgHom : R × R →ₐ[R] A where
  toFun x := algebraMap R A x.1 * e + algebraMap R A x.2 * (1 - e)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    have he2 : e ^ 2 = e := he.pow_eq (by decide)
    ring_nf
    rw [he2]
    ring
  commutes' r := by
    change algebraMap R A r * e + algebraMap R A r * (1 - e) = algebraMap R A r
    ring

/-- A point where the idempotent is one selects the first constant component. -/
theorem comp_prodAlgHom_of_eq_one (φ : A →ₐ[R] B) (h : φ e = 1) :
    φ.comp he.prodAlgHom = (Algebra.ofId R B).comp (AlgHom.fst R R R) := by
  ext x
  simp [prodAlgHom, h]

/-- A point where the idempotent is zero selects the second constant component. -/
theorem comp_prodAlgHom_of_eq_zero (φ : A →ₐ[R] B) (h : φ e = 0) :
    φ.comp he.prodAlgHom = (Algebra.ofId R B).comp (AlgHom.snd R R R) := by
  ext x
  simp [prodAlgHom, h]

/-- Every idempotent is integral over the coefficient ring, with equation `X² - X`. -/
theorem isIntegral (he : IsIdempotentElem e) : IsIntegral R e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X,
    Polynomial.monic_X_pow_sub (lt_of_le_of_lt Polynomial.degree_X_le (by decide)), ?_⟩
  change Polynomial.aeval e (Polynomial.X ^ 2 - Polynomial.X : Polynomial R) = 0
  simpa only [map_sub, map_pow, map_mul, Polynomial.aeval_X, pow_two] using (sub_eq_zero.mpr he.eq)

end IsIdempotentElem
