/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # A common number field inside prescribed local coefficients

The compositum preserves both supplied embeddings. Its complex embedding can
be chosen to extend the eigenform's embedding, as needed for the finite twist
in [TripathiGoswami, §6].
-/

public noncomputable section

namespace HilbertModularity

variable {A B E : Type*} [Field A] [NumberField A] [Field B] [NumberField B]
  [Field E] [CharZero E]

/-- The compositum of two coefficient fields inside their given ambient field. -/
def coefficientCompositum (i : A →+* E) (j : B →+* E) : IntermediateField ℚ E :=
  i.toRatAlgHom.fieldRange ⊔ j.toRatAlgHom.fieldRange

instance coefficientCompositum_numberField (i : A →+* E) (j : B →+* E) :
    NumberField (coefficientCompositum i j) := by
  let : FiniteDimensional ℚ i.toRatAlgHom.fieldRange :=
    Module.Finite.of_surjective i.toRatAlgHom.equivFieldRange.toLinearMap
      i.toRatAlgHom.equivFieldRange.surjective
  let : FiniteDimensional ℚ j.toRatAlgHom.fieldRange :=
    Module.Finite.of_surjective j.toRatAlgHom.equivFieldRange.toLinearMap
      j.toRatAlgHom.equivFieldRange.surjective
  have : FiniteDimensional ℚ (coefficientCompositum i j) :=
    IntermediateField.finiteDimensional_sup _ _
  exact { }

namespace coefficientCompositum

/-- The first given field embedded into the compositum. -/
def left (i : A →+* E) (j : B →+* E) : A →+* coefficientCompositum i j where
  toFun a := ⟨i a, (show i.toRatAlgHom.fieldRange ≤ coefficientCompositum i j
    from le_sup_left) ⟨a, rfl⟩⟩
  map_one' := Subtype.ext (map_one i)
  map_mul' a b := Subtype.ext (map_mul i a b)
  map_zero' := Subtype.ext (map_zero i)
  map_add' a b := Subtype.ext (map_add i a b)

/-- The second given field embedded into the compositum. -/
def right (i : A →+* E) (j : B →+* E) : B →+* coefficientCompositum i j where
  toFun b := ⟨j b, (show j.toRatAlgHom.fieldRange ≤ coefficientCompositum i j
    from le_sup_right) ⟨b, rfl⟩⟩
  map_one' := Subtype.ext (map_one j)
  map_mul' a b := Subtype.ext (map_mul j a b)
  map_zero' := Subtype.ext (map_zero j)
  map_add' a b := Subtype.ext (map_add j a b)

@[simp]
theorem val_comp_left (i : A →+* E) (j : B →+* E) :
    (coefficientCompositum i j).val.toRingHom.comp (left i j) = i := (rfl)

@[simp]
theorem val_comp_right (i : A →+* E) (j : B →+* E) :
    (coefficientCompositum i j).val.toRingHom.comp (right i j) = j := (rfl)

/-- Extend a prescribed complex embedding of the first field to the compositum. -/
theorem exists_complexEmbedding (i : A →+* E) (j : B →+* E) (c : A →+* ℂ) :
    ∃ d : coefficientCompositum i j →+* ℂ, d.comp (left i j) = c := by
  let : Algebra A (coefficientCompositum i j) := (left i j).toAlgebra
  let : Algebra A ℂ := c.toAlgebra
  let : Algebra.IsAlgebraic A (coefficientCompositum i j) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) (L := A) (A := coefficientCompositum i j)
  let d : coefficientCompositum i j →ₐ[A] ℂ := IsAlgClosed.lift
  refine ⟨d.toRingHom, ?_⟩
  ext a
  exact d.commutes a

end coefficientCompositum
end HilbertModularity
