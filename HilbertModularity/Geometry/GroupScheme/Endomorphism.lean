/- Assembled by AxiomProver. -/

module

public import HilbertModularity.CategoryTheory.GroupObjectPoints
public import HilbertModularity.Geometry.GroupScheme.Fiber
public import HilbertModularity.Geometry.TateModule.CoefficientAction

/-! # Specializing endomorphisms of a commutative group scheme

An actual ring action on one family specializes to ring actions on all its
fibres and their geometric points. This supplies the geometric realization
hypothesis of the Tate coefficient action, without a separate choice for
each fibre. See [TripathiGoswami, RM coefficient-label lemma].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj NumberField

namespace AlgebraicGeometry.GroupScheme

universe u
variable (K E : Type u) [Field K] [Field E] [Algebra K E]
  (A : CommGrp (Over (Spec (CommRingCat.of K))))

/-- Actual scheme endomorphisms act as a ring on geometric points. -/
def pointsEndomorphismMap :
    CategoryTheory.End A →+* AddMonoid.End (Points K E A.X) :=
  CommGrp.pointsEndomorphismMap (fieldPoint K E) A

variable {S : Scheme.{u}} (B : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- Pullback to a fibre is a homomorphism of actual endomorphism rings. -/
def fiberEndomorphismMap : CategoryTheory.End B →+* CategoryTheory.End (fiber K B x) where
  toFun f := (Over.pullback x).mapCommGrp.map f
  map_one' := (Over.pullback x).mapCommGrp.map_id B
  map_mul' f g := (Over.pullback x).mapCommGrp.map_comp g f
  map_zero' := (Over.pullback x).mapCommGrp.map_zero B B
  map_add' _ _ := (Over.pullback x).mapCommGrp.map_add

variable (R : Type*) [CommRing R] (φ : R →+* CategoryTheory.End B)

/-- A ring action on a single family acts on the geometric points of each fibre. -/
def fiberPointsAction : R →+* AddMonoid.End (Points K E (fiber K B x).X) :=
  (pointsEndomorphismMap K E (fiber K B x)).comp ((fiberEndomorphismMap K B x).comp φ)

/-- The fibre action is the composite of pullback and the action on points. -/
theorem fiberPointsAction_apply (a : R) :
    fiberPointsAction K E B x R φ a =
      pointsEndomorphismMap K E (fiber K B x) (fiberEndomorphismMap K B x (φ a)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every specialized coefficient endomorphism comes from a morphism of the same family. -/
theorem fiberPointsAction_realized (a : R) :
    ∃ (f : (fiber K B x).X ⟶ (fiber K B x).X) (_ : IsMonHom f),
      fiberPointsAction K E B x R φ a = pointsMap K E f := by
  exact ⟨((Over.pullback x).mapCommGrp.map (φ a)).hom.hom.hom, inferInstance, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- A coefficient-compatible family morphism remains compatible on every geometric fibre. -/
theorem fiberPointsAction_naturality {D : CommGrp (Over S)}
    (ψ : R →+* CategoryTheory.End D) (f : B ⟶ D)
    (h : ∀ a, φ a ≫ f = f ≫ ψ a) (a : R)
    (y : Points K E (fiber K B x).X) :
    pointsMap K E ((Over.pullback x).mapCommGrp.map f).hom.hom.hom
      (fiberPointsAction K E B x R φ a y) =
      fiberPointsAction K E D x R ψ a
        (pointsMap K E ((Over.pullback x).mapCommGrp.map f).hom.hom.hom y) := by
  have hc := congrArg
    (fun z : B ⟶ D => ((Over.pullback x).mapCommGrp.map z).hom.hom.hom) (h a)
  simp only [Functor.map_comp, CommGrp.comp_hom, Grp.comp_hom_hom] at hc
  change (y.toMul ≫ ((Over.pullback x).mapCommGrp.map (φ a)).hom.hom.hom) ≫
      ((Over.pullback x).mapCommGrp.map f).hom.hom.hom =
    (y.toMul ≫ ((Over.pullback x).mapCommGrp.map f).hom.hom.hom) ≫
      ((Over.pullback x).mapCommGrp.map (ψ a)).hom.hom.hom
  rw [Category.assoc, hc, Category.assoc]

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [NumberField F]

/-- Real multiplication on one family gives the rational coefficient action on each Tate fibre. -/
def fiberNumberFieldTateAction (ψ : 𝓞 F →+* CategoryTheory.End B) :
    F →ₐ[ℚ] Module.End ℚ_[p] (rationalTate K (fiber K B x).X p) :=
  numberFieldTateAction K (fiber K B x).X p F
    (fiberPointsAction K (AlgebraicClosure K) B x (𝓞 F) ψ)

/-- The specialized number-field action commutes with the actual covariant Galois action. -/
theorem fiberNumberFieldTateAction_commute (ψ : 𝓞 F →+* CategoryTheory.End B)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F) :
    Commute (fiberNumberFieldTateAction K B x p F ψ a)
      (tateRepresentation K (fiber K B x).X p g) :=
  numberFieldTateAction_commute K (fiber K B x).X p F _
    (fiberPointsAction_realized K (AlgebraicClosure K) B x (𝓞 F) ψ) g a

/-- On integral coefficients the rational action is precisely the Tate map of
that family endomorphism specialized to this fibre. -/
@[simp]
theorem fiberNumberFieldTateAction_integer (ψ : 𝓞 F →+* CategoryTheory.End B)
    (a : 𝓞 F) :
    fiberNumberFieldTateAction K B x p F ψ (a : F) =
      rationalTateMap K p ((fiberEndomorphismMap K B x) (ψ a)).hom.hom.hom :=
  numberFieldTateAction_integer K (fiber K B x).X p F _ a

end AlgebraicGeometry.GroupScheme

open scoped TensorProduct

namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (p : ℕ) [Fact p.Prime]
  (F : Type*) [Field F] [NumberField F] (φ : 𝓞 F →+* End A)

/-- The Tate scalar field and the original multiplication field act through their tensor algebra. -/
def fiberTensorTateAction : ℚ_[p] ⊗[ℚ] F →ₐ[ℚ_[p]]
    Module.End ℚ_[p] (rationalTate K (fiber K A x).X p) :=
  NumberField.RingOfIntegers.tensorExtension F ℚ_[p]
    (integerTateAction K (fiber K A x).X p F
      (fiberPointsAction K (AlgebraicClosure K) A x (𝓞 F) φ))

/-- An algebraic integer acts by the original family endomorphism on the actual fibre. -/
@[simp]
theorem fiberTensorTateAction_integer (a : 𝓞 F) :
    fiberTensorTateAction K A x p F φ ((1 : ℚ_[p]) ⊗ₜ[ℚ] (a : F)) =
      rationalTateMap K p ((fiberEndomorphismMap K A x) (φ a)).hom.hom.hom := by
  simp only [fiberTensorTateAction, NumberField.RingOfIntegers.tensorExtension_integer]
  rfl

/-- Pure tensor coefficients combine the native Tate scalar with the number-field action. -/
@[simp]
theorem fiberTensorTateAction_tmul (c : ℚ_[p]) (a : F) :
    fiberTensorTateAction K A x p F φ (c ⊗ₜ[ℚ] a) =
      c • fiberNumberFieldTateAction K A x p F φ a := by
  change algebraMap ℚ_[p] (Module.End ℚ_[p] (rationalTate K (fiber K A x).X p)) c *
      fiberNumberFieldTateAction K A x p F φ a = _
  exact (Algebra.smul_def _ _).symm

end AlgebraicGeometry.GroupScheme
