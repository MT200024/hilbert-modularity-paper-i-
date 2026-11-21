/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.Endomorphism
public import HilbertModularity.NumberTheory.RingOfIntegers.ScalarExtension
public import HilbertModularity.RepresentationTheory.ScalarExtension

/-! # Coefficient actions on geometric Tate modules

An action of the ring of integers on geometric points induces an action of its
number field on the rational Tate module. After extending the Tate coefficients,
it induces an action of the tensor product of the two coefficient fields.
If the integer endomorphisms are induced by morphisms over the ground field,
this action commutes with Galois. This is the coefficient-action construction
used in [TripathiGoswami, coefficient-label lemma]; existence of a particular
real multiplication action is an additional geometric assertion.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]

/-- An integer coefficient action on geometric points acts on the rational Tate module. -/
def integerTateAction (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A)) :
    𝓞 F →+* Module.End ℚ_[p] (rationalTate K A p) :=
  (TateModule.rationalEndomorphismMap p (Points K (AlgebraicClosure K) A)).comp φ

/-- Rationalizing an integer coefficient action gives an action of the number field. -/
def numberFieldTateAction (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A)) :
    F →ₐ[ℚ] Module.End ℚ_[p] (rationalTate K A p) :=
  NumberField.RingOfIntegers.rationalExtension F (integerTateAction K A p F φ)

@[simp]
theorem numberFieldTateAction_integer
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A)) (a : 𝓞 F) :
    numberFieldTateAction K A p F φ (a : F) = TateModule.rationalMap p (φ a) := by
  simp [numberFieldTateAction, integerTateAction]

omit [NumberField F] in
/-- Integer endomorphisms defined over the ground field commute with Galois on Tate modules. -/
theorem integerTateAction_commute
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
    (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : 𝓞 F) :
    Commute (integerTateAction K A p F φ a) (tateRepresentation K A p g) := by
  obtain ⟨f, hf, ha⟩ := hφ a
  change TateModule.rationalMap p (φ a) * tateRepresentation K A p g =
    tateRepresentation K A p g * TateModule.rationalMap p (φ a)
  rw [ha]
  apply LinearMap.ext
  intro x
  exact rationalTateMap_galois K p f g x

/-- The rational number-field action commutes with the Galois representation. -/
theorem numberFieldTateAction_commute
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
    (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F) :
    Commute (numberFieldTateAction K A p F φ a) (tateRepresentation K A p g) :=
  NumberField.RingOfIntegers.rationalExtension_commute F _ _
    (integerTateAction_commute K A p F φ hφ g) a

section ScalarExtension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]

/-- Integer coefficients act after extending the scalar field of the Tate module. -/
def extendedIntegerTateAction
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A)) :
    𝓞 F →+* Module.End L (L ⊗[ℚ_[p]] rationalTate K A p) :=
  (Module.End.baseChangeHom ℚ_[p] L (rationalTate K A p)).toRingHom.comp
    (integerTateAction K A p F φ)

/-- The tensor product of coefficient fields acts on the extended geometric Tate module. -/
def tensorTateAction
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A)) :
    L ⊗[ℚ] F →ₐ[L] Module.End L (L ⊗[ℚ_[p]] rationalTate K A p) :=
  NumberField.RingOfIntegers.tensorExtension F
    (A := Module.End L (L ⊗[ℚ_[p]] rationalTate K A p)) L
    (extendedIntegerTateAction K A p F L φ)

@[simp]
theorem tensorTateAction_integer
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A)) (a : 𝓞 F) :
    tensorTateAction K A p F L φ ((1 : L) ⊗ₜ[ℚ] (a : F)) =
      (TateModule.rationalMap p (φ a)).baseChange L := by
  simp only [tensorTateAction, NumberField.RingOfIntegers.tensorExtension_integer]
  rfl

/-- The full coefficient algebra commutes with Galois after extending Tate scalars. -/
theorem tensorTateAction_commute
    (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
    (hφ : ∀ a, ∃ (f : A ⟶ A) (_ : IsMonHom f),
      φ a = pointsMap K (AlgebraicClosure K) f)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : L ⊗[ℚ] F) :
    Commute (tensorTateAction K A p F L φ a)
      ((tateRepresentation K A p).baseChange L g) := by
  apply NumberField.RingOfIntegers.tensorExtension_commute
  intro b
  exact (integerTateAction_commute K A p F φ hφ g b).map
    (Module.End.baseChangeHom ℚ_[p] L (rationalTate K A p))

end ScalarExtension

section Naturality

variable {B : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsCommMonObj B]
  (φ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) A))
  (ψ : 𝓞 F →+* AddMonoid.End (Points K (AlgebraicClosure K) B))
  (f : A ⟶ B) [IsMonHom f]
  (h : ∀ (a : 𝓞 F) (x : Points K (AlgebraicClosure K) A),
    pointsMap K (AlgebraicClosure K) f (φ a x) = ψ a (pointsMap K (AlgebraicClosure K) f x))

include h in
omit [NumberField F] in
/-- A group-scheme map respecting integer coefficients intertwines their Tate actions. -/
theorem integerTateAction_intertwines (a : 𝓞 F) (v : rationalTate K A p) :
    rationalTateMap K p f (integerTateAction K A p F φ a v) =
      integerTateAction K B p F ψ a (rationalTateMap K p f v) := by
  induction v using TensorProduct.inductionOn with
  | tmul c v =>
    change c ⊗ₜ[ℤ_[p]] TateModule.map p (pointsMap K (AlgebraicClosure K) f)
      (TateModule.map p (φ a) v) =
        c ⊗ₜ[ℤ_[p]] TateModule.map p (ψ a)
          (TateModule.map p (pointsMap K (AlgebraicClosure K) f) v)
    congr 1
    apply Subtype.ext
    funext n
    apply Subtype.ext
    exact h a (v.val n)
  | add x y hx hy => simp only [map_add, hx, hy]

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]

include h in
/-- A geometric coefficient-linear map respects the full scalar-extended coefficient action. -/
theorem tensorTateAction_intertwines (a : L ⊗[ℚ] F)
    (v : L ⊗[ℚ_[p]] rationalTate K A p) :
    (rationalTateMap K p f).baseChange L (tensorTateAction K A p F L φ a v) =
      tensorTateAction K B p F L ψ a ((rationalTateMap K p f).baseChange L v) := by
  apply NumberField.RingOfIntegers.tensorExtension_intertwines
  intro b w
  induction w using TensorProduct.inductionOn with
  | tmul l w =>
    change l ⊗ₜ[ℚ_[p]] rationalTateMap K p f (integerTateAction K A p F φ b w) =
      l ⊗ₜ[ℚ_[p]] integerTateAction K B p F ψ b (rationalTateMap K p f w)
    rw [integerTateAction_intertwines K A p F φ ψ f h]
  | add x y hx hy => simp only [map_add, hx, hy]

end Naturality

end AlgebraicGeometry.GroupScheme
