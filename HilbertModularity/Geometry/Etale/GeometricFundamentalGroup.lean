/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricBaseChangePoint
public import HilbertModularity.Geometry.Etale.GeometricPathGroup

/-! # The actual geometric fundamental group and its arithmetic monodromy map

The group is the finite étale fundamental group of the scheme after extending
its ground field to the algebraic closure. Its map to the original fundamental
group is induced by the scheme projection and the specified geometric fibre
comparison. No injectivity or exactness statement is included.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
universe u
variable (K F : Type u) [Field K] [Field F] [Algebra K F]
  {S : Scheme.{u}} (f : S ⟶ Spec (CommRingCat.of K))
  (x : Spec (CommRingCat.of F) ⟶ S) (hx : x ≫ f = Spec.algebraMap K F)
  (j : AlgebraicClosure K →ₐ[K] AlgebraicClosure F)

/-- The fundamental group of the actual geometric base change, at the lifted geometric point. -/
abbrev geometricFundamentalGroup : ProfiniteGrp :=
  etaleFundamentalGroup (AlgebraicClosure F) (geometricBaseChangePoint K F f x hx j)

/-- The projected geometric fibre is the original generic fibre, after the canonical extension
of its already algebraically closed residue field. -/
def geometricBaseChangeFiberIso :
    finiteArithmeticFiberFunctor (AlgebraicClosure F)
        (geometricBaseChangePoint K F f x hx j ≫
          pullback.fst f (Spec.algebraMap K (AlgebraicClosure K))) ≅
      finiteArithmeticFiberFunctor F x := by
  have hp : geometricBaseChangePoint K F f x hx j ≫
      pullback.fst f (Spec.algebraMap K (AlgebraicClosure K)) =
        Spec.algebraMap F (AlgebraicClosure F) ≫ x :=
    geometricBaseChangePoint_fst K F f x hx j
  exact (eqToIso (congrArg (finiteArithmeticFiberFunctor (AlgebraicClosure F)) hp)).trans
    (arithmeticFiberFieldIso F (AlgebraicClosure F) x
      (IsScalarTower.toAlgHom F (AlgebraicClosure F)
        (AlgebraicClosure (AlgebraicClosure F)))).symm

/-- The actual geometric base-change projection induces the continuous geometric monodromy map. -/
def geometricFundamentalGroupMap :
    geometricFundamentalGroup K F f x hx j →ₜ* etaleFundamentalGroup F x :=
  (geometricFiberPathGroupEquiv (AlgebraicClosure F) F
    (geometricBaseChangeFiberIso K F f x hx j) :
      etaleFundamentalGroup (AlgebraicClosure F)
        (geometricBaseChangePoint K F f x hx j ≫
          pullback.fst f (Spec.algebraMap K (AlgebraicClosure K))) →ₜ*
            etaleFundamentalGroup F x).comp
    (etaleFundamentalGroupContinuousMap (pullback.fst f (Spec.algebraMap K (AlgebraicClosure K)))
      (AlgebraicClosure F) (geometricBaseChangePoint K F f x hx j))

end AlgebraicGeometry.Scheme
