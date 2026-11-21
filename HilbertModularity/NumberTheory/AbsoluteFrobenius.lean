/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.GaloisPrimes
public import HilbertModularity.NumberTheory.CyclotomicCharacter
public import HilbertModularity.RepresentationTheory.Unramified

/-! # Frobenius in an infinite Galois extension

The decomposition group surjects onto the residue Galois group. We choose an
arithmetic lift and define geometric Frobenius as its inverse, following
[TripathiGoswami, Frobenius conventions]. The construction applies to an
algebraic closure, so these are elements of the actual absolute Galois group.
-/

@[expose] public noncomputable section

open scoped NumberField Pointwise

namespace NumberField

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [IsGalois K E]
  (P : Ideal (𝓞 K)) (Q : Ideal (𝓞 E)) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
  [Finite (𝓞 K ⧸ P)]

attribute [local instance] Ideal.Quotient.field

omit [P.IsMaximal] [Q.IsMaximal] [Finite (𝓞 K ⧸ P)] in
/-- The residue action of the decomposition subgroup is surjective in any
algebraic Galois extension, including an algebraic closure. -/
theorem stabilizerHom_surjective [Q.IsPrime] :
    Function.Surjective (Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E)) := by
  let : TopologicalSpace (𝓞 E) := ⊥
  let : DiscreteTopology (𝓞 E) := ⟨rfl⟩
  exact Ideal.Quotient.stabilizerHom_surjective_of_profinite P Q

/-- A chosen arithmetic Frobenius lift in the actual decomposition subgroup. -/
def arithmeticFrobenius : MulAction.stabilizer (E ≃ₐ[K] E) Q :=
  (stabilizerHom_surjective K E P Q (Ideal.Quotient.arithmeticFrobenius P Q)).choose

/-- The chosen lift induces the canonical residue-field Frobenius. -/
theorem arithmeticFrobenius_residue :
    Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E) (arithmeticFrobenius K E P Q) =
      Ideal.Quotient.arithmeticFrobenius P Q :=
  (stabilizerHom_surjective K E P Q (Ideal.Quotient.arithmeticFrobenius P Q)).choose_spec

/-- Arithmetic Frobenius raises residues to the cardinality of the base residue field. -/
theorem arithmeticFrobenius_apply (x : 𝓞 E) :
    Ideal.Quotient.mk Q (arithmeticFrobenius K E P Q • x) =
      (Ideal.Quotient.mk Q x) ^ Nat.card (𝓞 K ⧸ P) := by
  have h := congrArg (fun f : (𝓞 E ⧸ Q) ≃ₐ[𝓞 K ⧸ P] (𝓞 E ⧸ Q) =>
    f (Ideal.Quotient.mk Q x)) (arithmeticFrobenius_residue K E P Q)
  simpa only [Ideal.Quotient.stabilizerHom_apply,
    Ideal.Quotient.arithmeticFrobenius_apply] using h

/-- Geometric Frobenius is the inverse of the chosen arithmetic Frobenius lift. -/
def geometricFrobenius : MulAction.stabilizer (E ≃ₐ[K] E) Q :=
  (arithmeticFrobenius K E P Q)⁻¹

/-- The inverse of geometric Frobenius induces the canonical arithmetic residue action. -/
theorem geometricFrobenius_inv_residue :
    Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E) (geometricFrobenius K E P Q)⁻¹ =
      Ideal.Quotient.arithmeticFrobenius P Q := by
  rw [geometricFrobenius, inv_inv, arithmeticFrobenius_residue]

/-- Geometric Frobenius acts on the residue field by the inverse Frobenius automorphism. -/
theorem geometricFrobenius_residue :
    Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E) (geometricFrobenius K E P Q) =
      (Ideal.Quotient.arithmeticFrobenius P Q)⁻¹ := by
  rw [geometricFrobenius, map_inv, arithmeticFrobenius_residue]

/-- In an unramified representation, every geometric Frobenius lift at the
same prime has the image of the chosen lift. -/
theorem geometricFrobenius_apply_eq_of_inertia_trivial
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    (ρ : Representation R (E ≃ₐ[K] E) V)
    (hρ : ∀ g ∈ Q.inertia (E ≃ₐ[K] E), ρ g = 1)
    (g : MulAction.stabilizer (E ≃ₐ[K] E) Q)
    (hg : Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E) g⁻¹ =
      Ideal.Quotient.arithmeticFrobenius P Q) :
    ρ g = ρ (geometricFrobenius K E P Q) := by
  apply Representation.apply_eq_of_inertia_trivial ρ Q hρ (g : E ≃ₐ[K] E)
    (geometricFrobenius K E P Q : E ≃ₐ[K] E)
  intro b
  have he : Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E) g =
      Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E) (geometricFrobenius K E P Q) := by
    rw [geometricFrobenius_residue]
    have h := congrArg (fun f : (𝓞 E ⧸ Q) ≃ₐ[𝓞 K ⧸ P] (𝓞 E ⧸ Q) => f⁻¹) hg
    simpa only [map_inv, inv_inv] using h
  exact congrArg (fun f : (𝓞 E ⧸ Q) ≃ₐ[𝓞 K ⧸ P] (𝓞 E ⧸ Q) =>
    f (Ideal.Quotient.mk Q b)) he

end NumberField

namespace Field

/-- The cyclotomic character at the constructed geometric Frobenius is the
inverse norm, with existence of the actual absolute Galois lift already proved. -/
theorem cyclotomicCharacterWithCoefficients_geometricFrobenius_apply
    (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P]
    (hp : (p : 𝓞 K) ∉ P) :
    (cyclotomicCharacterWithCoefficients K p L
      (NumberField.geometricFrobenius K (AlgebraicClosure K) P Q) : L) =
        (Nat.card (𝓞 K ⧸ P) : L)⁻¹ :=
  cyclotomicCharacterWithCoefficients_geometricFrobenius K p L P Q hp _
    (NumberField.geometricFrobenius_inv_residue K (AlgebraicClosure K) P Q)

end Field
