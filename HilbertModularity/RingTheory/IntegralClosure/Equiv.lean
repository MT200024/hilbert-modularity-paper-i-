/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Integral closures under compatible ring isomorphisms

Both the coefficient ring and its ambient ring may change. Compatibility of
the two maps transports integral equations and gives an isomorphism of the
actual integral closures.
-/

@[expose] public section
namespace RingEquiv
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra T U]

/-- Compatible isomorphisms of coefficients and ambient rings identify their integral closures. -/
def mapIntegralClosure (e : R ≃+* T) (f : S ≃+* U)
    (h : ∀ x, f (algebraMap R S x) = algebraMap T U (e x)) :
    integralClosure R S ≃+* integralClosure T U where
  toFun x := ⟨f x, x.property.map_of_comp_eq e.toRingHom f.toRingHom
    (RingHom.ext fun x => (h x).symm)⟩
  invFun y := ⟨f.symm y, y.property.map_of_comp_eq e.symm.toRingHom f.symm.toRingHom
    (RingHom.ext fun y => by
      apply f.injective
      change f (algebraMap R S (e.symm y)) = f (f.symm (algebraMap T U y))
      rw [h, e.apply_symm_apply, f.apply_symm_apply])⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv y := Subtype.ext (f.apply_symm_apply y)
  map_mul' x y := Subtype.ext (f.map_mul x y)
  map_add' x y := Subtype.ext (f.map_add x y)

/-- The induced integral-closure isomorphism is the original ambient map on elements. -/
@[simp] theorem mapIntegralClosure_apply (e : R ≃+* T) (f : S ≃+* U)
    (h : ∀ x, f (algebraMap R S x) = algebraMap T U (e x)) (x : integralClosure R S) :
    (mapIntegralClosure e f h x : U) = f x := rfl

/-- The induced integral-closure isomorphism respects the changed coefficient ring. -/
theorem mapIntegralClosure_algebraMap (e : R ≃+* T) (f : S ≃+* U)
    (h : ∀ x, f (algebraMap R S x) = algebraMap T U (e x)) (x : R) :
    mapIntegralClosure e f h (algebraMap R (integralClosure R S) x) =
      algebraMap T (integralClosure T U) (e x) := Subtype.ext (h x)

end RingEquiv
