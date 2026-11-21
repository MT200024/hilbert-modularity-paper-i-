/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Field

/-! # The arithmetic projection of the étale fundamental group

The structure map and the actual field fundamental-group equivalence give the
arithmetic quotient. A rational point splits it.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K] [CharZero K]
  {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of K))
  (x : Spec (CommRingCat.of K) ⟶ S) (hx : x ≫ f = 𝟙 _)

/-- The actual structure morphism induces the arithmetic projection. -/
def etaleArithmeticProjection :
    etaleFundamentalGroup K x →ₜ* (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := by
  let m := etaleFundamentalGroupContinuousMap f K x
  rw [hx] at m
  exact ((galoisEtaleFundamentalGroupEquiv K).symm :
      etaleFundamentalGroup K (𝟙 (Spec (CommRingCat.of K))) →ₜ*
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).comp m

/-- The rational point is a section of the arithmetic projection. -/
theorem etaleArithmeticProjection_galois
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    etaleArithmeticProjection K f x hx (galoisToEtaleFundamentalGroup K x g) = g := by
  apply (galoisEtaleFundamentalGroupEquiv K).injective
  change (galoisEtaleFundamentalGroupEquiv K)
    ((galoisEtaleFundamentalGroupEquiv K).symm _) = _
  rw [ContinuousMulEquiv.apply_symm_apply, galoisEtaleFundamentalGroupEquiv_apply]
  have transport (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
      (hy : y = 𝟙 _) (m : etaleFundamentalGroup K x →ₜ* etaleFundamentalGroup K y)
      (hm : m (galoisToEtaleFundamentalGroup K x g) = galoisToEtaleFundamentalGroup K y g) :
      (show etaleFundamentalGroup K x →ₜ* etaleFundamentalGroup K (𝟙 _) from by
        rw [hy] at m
        exact m) (galoisToEtaleFundamentalGroup K x g) =
          galoisToEtaleFundamentalGroup K (𝟙 _) g := by
    subst y
    exact hm
  exact transport (x ≫ f) hx (etaleFundamentalGroupContinuousMap f K x)
    (etaleFundamentalGroupMap_galois f K x g)

end AlgebraicGeometry.Scheme
