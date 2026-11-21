/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.Endomorphism
public import HilbertModularity.RepresentationTheory.CyclotomicCoefficients
public import HilbertModularity.RepresentationTheory.ScalarAction
public import HilbertModularity.RepresentationTheory.ScalarRestriction

/-! # Local coefficients on native rational Tate fibres

For prime-power real multiplication, the native coefficient tensor algebra is
canonically the completion at the unique prime above the conductor. Transporting
the actual scheme-induced action through this isomorphism makes the same Tate
representation linear over that completion. Its coefficient conjugates retain
the original Galois group, as in [TripathiGoswami, local coefficient conjugate].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj NumberField TensorProduct
open HilbertModularity.Cyclotomic
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] {S : Scheme.{u}} (A : CommGrp (Over S))
  (x : Spec (CommRingCat.of K) ⟶ S) (p k : ℕ) [Fact p.Prime]
  (φ : 𝓞 (realCyclotomicField (p ^ (k + 1))) →+* End A)

/-- The actual completed coefficient field acts on the original rational Tate fibre. -/
def localCoefficientTateAction : RealPrimePowerCompletion p k →ₐ[ℚ_[p]]
    Module.End ℚ_[p] (rationalTate K (fiber K A x).X p) :=
  (fiberTensorTateAction K A x p (realCyclotomicField (p ^ (k + 1))) φ).comp
    (realPrimePowerCompletionTensorEquiv p k).symm.toAlgHom

/-- An integral coefficient still acts by its original specialized scheme endomorphism. -/
@[simp] theorem localCoefficientTateAction_integer
    (a : 𝓞 (realCyclotomicField (p ^ (k + 1)))) :
    localCoefficientTateAction K A x p k φ
      (algebraMap (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k) a) =
      rationalTateMap K p ((fiberEndomorphismMap K A x) (φ a)).hom.hom.hom := by
  have h : (realPrimePowerCompletionTensorEquiv p k).symm
      (algebraMap (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k) a) =
        (1 : ℚ_[p]) ⊗ₜ[ℚ] (a : realCyclotomicField (p ^ (k + 1))) := by
    apply (realPrimePowerCompletionTensorEquiv p k).injective
    simp
  change fiberTensorTateAction K A x p _ φ
    ((realPrimePowerCompletionTensorEquiv p k).symm
      (algebraMap (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k) a)) = _
  rw [h]
  exact fiberTensorTateAction_integer K A x p (realCyclotomicField (p ^ (k + 1))) φ a

/-- The actual local coefficient action commutes with the original Galois action. -/
theorem localCoefficientTateAction_commute
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : RealPrimePowerCompletion p k) :
    Commute (localCoefficientTateAction K A x p k φ a)
      (tateRepresentation K (fiber K A x).X p g) := by
  apply NumberField.RingOfIntegers.tensorExtension_commute
  intro b
  exact integerTateAction_commute K (fiber K A x).X p
    (realCyclotomicField (p ^ (k + 1)))
    (fiberPointsAction K (AlgebraicClosure K) A x _ φ)
    (fiberPointsAction_realized K (AlgebraicClosure K) A x _ φ) g b

/-- The original rational Tate representation, now linear over its completed RM coefficient field. -/
def localCoefficientTateRepresentation :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    Representation (RealPrimePowerCompletion p k)
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (rationalTate K (fiber K A x).X p) :=
  Representation.withScalarAction (tateRepresentation K (fiber K A x).X p)
    (localCoefficientTateAction K A x p k φ).toRingHom
    (fun g a => (localCoefficientTateAction_commute K A x p k φ g a).symm)

/-- The coefficient-field reinterpretation leaves the actual Galois action unchanged. -/
@[simp] theorem localCoefficientTateRepresentation_apply
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (v : rationalTate K (fiber K A x).X p) :
    localCoefficientTateRepresentation K A x p k φ g v =
      tateRepresentation K (fiber K A x).X p g v := rfl

/-- The native Tate representation bundled over its completed multiplication field. -/
def localCoefficientTateRep :
    Rep (RealPrimePowerCompletion p k) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := by
  letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  exact Rep.of (localCoefficientTateRepresentation K A x p k φ)

/-- The bundled completed-coefficient Tate object retains its native rational p-adic module. -/
@[instance_reducible] def localCoefficientTateRepRationalModule :
    Module ℚ_[p] (localCoefficientTateRep K A x p k φ) :=
  inferInstanceAs (Module ℚ_[p] (rationalTate K (fiber K A x).X p))

attribute [local instance] localCoefficientTateRepRationalModule

/-- The actual scheme-induced completion action extends the native rational p-adic scalars. -/
theorem localCoefficientTateRepScalarTower :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) (localCoefficientTateRep K A x p k φ) where
  smul_assoc r a v := by
    change localCoefficientTateAction K A x p k φ (r • a) v =
      r • localCoefficientTateAction K A x p k φ a v
    rw [map_smul]
    rfl

attribute [local instance] localCoefficientTateRepScalarTower

/-- Rational scalar restriction is exactly the original native Tate representation. -/
theorem localCoefficientTateRep_restrictScalars :
    (localCoefficientTateRep K A x p k φ).ρ.restrictScalars ℚ_[p] =
      tateRepresentation K (fiber K A x).X p := rfl

/-- Bundling the local Tate representation preserves its native action on every vector. -/
@[simp] theorem localCoefficientTateRep_apply
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (v : rationalTate K (fiber K A x).X p) :
    (localCoefficientTateRep K A x p k φ).ρ g v =
      tateRepresentation K (fiber K A x).X p g v := rfl

/-- The local coefficient conjugate of an actual native rational Tate fibre. -/
def localConjugateTateRepresentation (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Rep (RealPrimePowerCompletion p k) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := by
  letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  exact Rep.localCoefficientConjugate p k m hm
    (Rep.of (localCoefficientTateRepresentation K A x p k φ))

/-- The native local conjugate is the ordinary coefficient conjugate of the bundled Tate object. -/
theorem localConjugateTateRepresentation_eq (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    localConjugateTateRepresentation K A x p k φ m hm =
      Rep.localCoefficientConjugate p k m hm (localCoefficientTateRep K A x p k φ) := rfl

/-- Galois acts on the native Tate tensorand alone after local coefficient conjugation. -/
theorem localConjugateTateRepresentation_tmul (m : ℕ) (hm : m.Coprime (p ^ (k + 1)))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (a : RealPrimePowerCompletion p k) (v : rationalTate K (fiber K A x).X p) :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
      (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
    letI : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
    (localConjugateTateRepresentation K A x p k φ m hm).ρ g
        (a ⊗ₜ[RealPrimePowerCompletion p k] v) =
      a ⊗ₜ[RealPrimePowerCompletion p k] tateRepresentation K (fiber K A x).X p g v := rfl

set_option maxHeartbeats 1000000 in
/-- In the genuine conjugate tensor, an original integral endomorphism has its conjugated coefficient. -/
theorem localConjugateTateRepresentation_integer (m : ℕ) (hm : m.Coprime (p ^ (k + 1)))
    (a : 𝓞 (realCyclotomicField (p ^ (k + 1)))) (v : rationalTate K (fiber K A x).X p) :
    letI : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
      Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
    letI : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
      (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
    letI : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
    (1 : RealPrimePowerCompletion p k) ⊗ₜ[RealPrimePowerCompletion p k]
        rationalTateMap K p ((fiberEndomorphismMap K A x) (φ a)).hom.hom.hom v =
      realPrimePowerCompletionAutomorphism p k m hm
          (algebraMap (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k) a)
        ⊗ₜ[RealPrimePowerCompletion p k] v := by
  let : Module (RealPrimePowerCompletion p k) (rationalTate K (fiber K A x).X p) :=
    Module.compHom _ (localCoefficientTateAction K A x p k φ).toRingHom
  let : Algebra (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) :=
    (realPrimePowerCompletionAutomorphism p k m hm).toRingHom.toAlgebra
  let : Module (RealPrimePowerCompletion p k) (RealPrimePowerCompletion p k) := Algebra.toModule
  have h := LinearMap.congr_fun (localCoefficientTateAction_integer K A x p k φ a) v
  refine (congrArg (fun z : rationalTate K (fiber K A x).X p =>
    (1 : RealPrimePowerCompletion p k) ⊗ₜ[RealPrimePowerCompletion p k] z) h.symm).trans ?_
  exact (Rep.scalarConjugate_balance
    (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (Rep.of (localCoefficientTateRepresentation K A x p k φ))
    (algebraMap (realCyclotomicField (p ^ (k + 1))) (RealPrimePowerCompletion p k) a) 1 v).trans
      (by rw [mul_one]; rfl)

end AlgebraicGeometry.GroupScheme
