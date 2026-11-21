/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.ArithmeticProjection

/-! # Kernel of the arithmetic projection

Changing the target base point and identifying the field fundamental group with
its Galois group do not change the kernel of the structure map.
-/

public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable (K : Type u) [Field K] [CharZero K]
  {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of K))
  (x : Spec (CommRingCat.of K) ⟶ S) (hx : x ≫ f = 𝟙 _)

/-- The arithmetic quotient and the structure-map action have exactly the same kernel. -/
theorem etaleArithmeticProjection_ker :
    (etaleArithmeticProjection K f x hx).toMonoidHom.ker =
      (etaleFundamentalGroupMap f K x).ker := by
  ext g
  change etaleArithmeticProjection K f x hx g = 1 ↔ _
  change (galoisEtaleFundamentalGroupEquiv K).symm _ = 1 ↔ _
  rw [map_eq_one_iff _ (galoisEtaleFundamentalGroupEquiv K).symm.injective]
  have transport (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
      (hy : y = 𝟙 _) (m : etaleFundamentalGroup K x →ₜ* etaleFundamentalGroup K y) :
      (show etaleFundamentalGroup K x →ₜ* etaleFundamentalGroup K (𝟙 _) from by
        rw [hy] at m
        exact m) g = 1 ↔ m g = 1 := by
    subst y
    rfl
  exact transport (x ≫ f) hx (etaleFundamentalGroupContinuousMap f K x)

end AlgebraicGeometry.Scheme
