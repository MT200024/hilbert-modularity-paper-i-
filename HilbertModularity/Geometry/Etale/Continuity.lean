/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteFiber
public import HilbertModularity.CategoryTheory.GaloisAction

/-! # Continuity of the arithmetic action on finite étale fibres

A point of a finite étale fibre is defined over a finite extension. Its open
stabilizer gives continuity of the arithmetic action, including the induced
homomorphism into the profinite étale fundamental group.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme

universe u
variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- Stabilizers of actual finite étale fibre points are open in the Krull topology. -/
theorem isOpen_arithmeticFiber_stabilizer (X : S.FiniteEtale)
    (y : (finiteArithmeticFiberFunctor K x).obj X) :
    IsOpen (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) y :
      Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
  let P := (Over.pullback x).obj ((Etale.forget S).obj X.obj)
  let e := (Over.mapPullbackAdj x).homEquiv
    (GroupScheme.fieldPoint K (AlgebraicClosure K)) ((Etale.forget S).obj X.obj)
  have : IsFinite P.hom := inferInstanceAs (IsFinite (Limits.pullback.snd X.obj.hom x))
  obtain ⟨L, hL, hfix⟩ := GroupScheme.exists_finite_fixing_field K (AlgebraicClosure K)
    P (Additive.ofMul (e y))
  let := hL
  apply Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) ?_ L.fixingSubgroup_isOpen
  intro g hg
  change g • y = y
  apply e.injective
  change e ((Over.map x).map (GroupScheme.fieldPointMap K (AlgebraicClosure K) g) ≫ y) = e y
  rw [Adjunction.homEquiv_naturality_left]
  exact hfix g hg

/-- Each finite arithmetic fibre is a continuous discrete Galois set. -/
instance finiteArithmeticFiberContinuousSMul (X : S.FiniteEtale) :
    ContinuousSMul (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((finiteArithmeticFiberFunctor K x).obj X) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (isOpen_arithmeticFiber_stabilizer K x X)

/-- The rational point induces a continuous homomorphism into the actual
profinite automorphism group of the finite étale fibre functor. -/
theorem continuous_galoisToEtaleFundamentalGroup :
    Continuous (galoisToEtaleFundamentalGroup K x) :=
  PreGaloisCategory.continuous_toAut_of_continuous_fibers
    (finiteArithmeticFiberFunctor K x) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)

/-- The bundled continuous arithmetic homomorphism supplied by the rational point. -/
def continuousGaloisToEtaleFundamentalGroup :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* etaleFundamentalGroup K x where
  __ := galoisToEtaleFundamentalGroup K x
  continuous_toFun := continuous_galoisToEtaleFundamentalGroup K x

end AlgebraicGeometry.Scheme
