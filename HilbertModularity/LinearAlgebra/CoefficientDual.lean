/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.CoefficientDecomposition
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Dual coefficient actions and projector images

Coefficient endomorphisms act on linear duals by transpose. A commutative
coefficient algebra therefore acts on the dual with the same embedding labels.
The image of a transposed idempotent is canonically the dual of its original
image. This is the linear algebra behind [TripathiGoswami, the definition of
the cohomological RM factor].
-/

@[expose] public noncomputable section

namespace AlgHom

variable {R A V : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid V] [Module R V]

/-- Transpose a commutative coefficient action on a module to its linear dual. -/
def dualEndomorphism (a : A →ₐ[R] Module.End R V) : A →ₐ[R] Module.End R (Module.Dual R V) where
  toFun x := (a x).dualMap
  map_zero' := by ext f v; simp
  map_one' := by ext f v; simp
  map_add' x y := by ext f v; simp
  map_mul' x y := by
    ext f v
    change f (a (x * y) v) = f (a y (a x v))
    rw [mul_comm x y, map_mul]
    rfl
  commutes' r := by
    ext f v
    change f (a (algebraMap R A r) v) = r • f v
    rw [a.commutes]
    simp

@[simp]
theorem dualEndomorphism_apply (a : A →ₐ[R] Module.End R V) (x : A)
    (f : Module.Dual R V) (v : V) : dualEndomorphism a x f v = f (a x v) := rfl

end AlgHom

namespace LinearMap

variable {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
  (e : Module.End R V) (he : IsIdempotentElem e)

include he in
/-- Transposing an idempotent gives an idempotent on the linear dual. -/
theorem dualMap_isIdempotentElem : IsIdempotentElem e.dualMap := by
  ext f v
  exact congrArg f (LinearMap.congr_fun he v)

/-- Restriction identifies the image of the transposed projector with the dual of its image. -/
def dualProjectorRangeEquiv : range e.dualMap ≃ₗ[R] Module.Dual R (range e) where
  toFun f := (f : Module.Dual R V).comp (range e).subtype
  invFun f := ⟨f.comp e.rangeRestrict, by
    apply (IsIdempotentElem.mem_range_iff (dualMap_isIdempotentElem e he)).mpr
    ext v
    change f ⟨e (e v), _⟩ = f ⟨e v, _⟩
    congr 1
    exact Subtype.ext (LinearMap.congr_fun he v)⟩
  left_inv f := by
    apply Subtype.ext
    ext v
    exact LinearMap.congr_fun
      ((IsIdempotentElem.mem_range_iff (dualMap_isIdempotentElem e he)).mp f.property) v
  right_inv f := by
    ext v
    change f ⟨e v, _⟩ = f v
    congr 1
    exact Subtype.ext ((IsIdempotentElem.mem_range_iff he).mp v.property)
  map_add' f g := rfl
  map_smul' r f := rfl

@[simp]
theorem dualProjectorRangeEquiv_apply (f : range e.dualMap) (v : range e) :
    dualProjectorRangeEquiv e he f v = (f : Module.Dual R V) v := rfl

@[simp]
theorem dualProjectorRangeEquiv_symm_apply (f : Module.Dual R (range e)) (v : V) :
    ((dualProjectorRangeEquiv e he).symm f : Module.Dual R V) v = f (e.rangeRestrict v) := rfl

end LinearMap
