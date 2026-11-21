/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiberComparison
public import HilbertModularity.Geometry.Etale.FiberComparisonInjective
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Paths between geometric fibre functors

Over a preconnected affine locally Noetherian scheme, the actual finite étale
fibre functors at any two field-valued points are naturally isomorphic.
The path is obtained from finite limits and connected subcovers, not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable {S : Scheme.{u}} [PreconnectedSpace S] [IsAffine S] [IsLocallyNoetherian S]
  (K L : Type u) [Field K] [Field L]
  (x : Spec (CommRingCat.of K) ⟶ S) (y : Spec (CommRingCat.of L) ⟶ S)

/-- Every natural comparison between the actual geometric fibres is bijective. -/
theorem finiteArithmeticFiber_natTrans_bijective
    (η : finiteArithmeticFiberFunctor K x ⟶ finiteArithmeticFiberFunctor L y)
    (X : S.FiniteEtale) : Function.Bijective (η.app X) := by
  obtain ⟨θ⟩ := nonempty_finiteArithmeticFiber_natTrans L K y x
  have hη := finiteArithmeticFiber_natTrans_injective K L x y η X
  have hθ := finiteArithmeticFiber_natTrans_injective L K y x θ X
  exact ⟨hη, (Finite.surjective_of_injective (hη.comp hθ)).of_comp⟩

/-- A natural comparison of actual geometric fibres is a natural isomorphism. -/
instance finiteArithmeticFiber_natTrans_isIso
    (η : finiteArithmeticFiberFunctor K x ⟶ finiteArithmeticFiberFunctor L y) :
    IsIso η := by
  have : ∀ X, IsIso (η.app X) := fun X =>
    (ConcreteCategory.isIso_iff_bijective (η.app X)).mpr
      (finiteArithmeticFiber_natTrans_bijective K L x y η X)
  exact NatIso.isIso_of_isIso_app η

/-- There exists a path between any two actual geometric fibre functors. -/
theorem nonempty_finiteArithmeticFiber_iso :
    Nonempty (finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor L y) := by
  obtain ⟨η⟩ := nonempty_finiteArithmeticFiber_natTrans K L x y
  exact ⟨asIso η⟩

/-- A choice of path between actual finite étale geometric fibre functors. -/
def finiteArithmeticFiberIso :
    finiteArithmeticFiberFunctor K x ≅ finiteArithmeticFiberFunctor L y :=
  Classical.choice (nonempty_finiteArithmeticFiber_iso K L x y)

end AlgebraicGeometry.Scheme
