/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! # Complex conjugation on an algebraic closure

Restrict complex conjugation along a complex embedding over a real place.
This supplies the involution used in the rank-two irreducibility argument of
[TripathiGoswamiRevised, Lemma `prime-absolute-irred`].
-/

public section

namespace NumberField

/-- A real embedding of the base makes complex conjugation preserve every
normal extension embedded in `ℂ`. Its restriction is an involution. -/
theorem exists_complexConjugation_of_embedding
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Normal F E]
    (ι : E →+* ℂ) (hreal : ComplexEmbedding.IsReal (ι.comp (algebraMap F E))) :
    ∃ c : E ≃ₐ[F] E, c ^ 2 = 1 ∧ ∀ x, ι (c x) = star (ι x) := by
  let : Algebra E ℂ := ι.toAlgebra
  let : Algebra F ℂ := (ι.comp (algebraMap F E)).toAlgebra
  let : IsScalarTower F E ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let s : ℂ ≃ₐ[F] ℂ :=
    { Complex.conjAe.toRingEquiv with
      commutes' := fun x => RingHom.congr_fun hreal x }
  let c := s.restrictNormal E
  have hconj (x : E) : ι (c x) = star (ι x) :=
    s.restrictNormal_commutes E x
  refine ⟨c, ?_, hconj⟩
  ext x
  apply ι.injective
  change ι (c (c x)) = ι x
  rw [hconj, hconj, star_star]

/-- The algebraic closure of a totally real number field has an actual
complex-conjugation involution and an embedding which realizes it. -/
theorem exists_complexConjugation
    (F : Type*) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (ι : AlgebraicClosure F →+* ℂ)
      (c : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F),
      c ^ 2 = 1 ∧ ∀ x, ι (c x) = star (ι x) := by
  classical
  let ι := ComplexEmbedding.lift (AlgebraicClosure F)
    (Classical.choice inferInstance : F →+* ℂ)
  obtain ⟨c, hc, hconj⟩ := exists_complexConjugation_of_embedding (F := F) ι
    (IsTotallyReal.complexEmbedding_isReal _)
  exact ⟨ι, c, hc, hconj⟩

end NumberField
