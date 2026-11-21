/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteLimits
public import HilbertModularity.Geometry.Etale.Connected
public import HilbertModularity.CategoryTheory.FiniteFunctorComparison
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Whiskering

/-! # Comparing geometric fibres of finite étale covers

Finite limits make the category of pointed covers cofiltered. Over a
preconnected base every nonempty cover meets every geometric fibre. Compactness
of finite sets therefore constructs a natural map between any two actual fibres.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
universe u
variable {S : Scheme.{u}} [PreconnectedSpace S]
  (K L : Type u) [Field K] [Field L]
  (x : Spec (CommRingCat.of K) ⟶ S) (y : Spec (CommRingCat.of L) ⟶ S)

/-- Actual geometric fibres over a preconnected scheme admit a natural comparison. -/
theorem nonempty_finiteArithmeticFiber_natTrans :
    Nonempty (finiteArithmeticFiberFunctor K x ⟶ finiteArithmeticFiberFunctor L y) := by
  let F := finiteArithmeticFiberFunctor K x
  let G := finiteArithmeticFiberFunctor L y
  let U := CategoryTheory.forget FintypeCat.{u}
  have : IsCofiltered (F ⋙ U).Elements := Functor.isCofiltered_elements (F ⋙ U)
  have : ∀ X, Finite ((G ⋙ U).obj X) := fun X =>
    inferInstanceAs (Finite ((finiteArithmeticFiberFunctor L y).obj X))
  obtain ⟨η⟩ := Functor.nonempty_natTrans_of_finite (F ⋙ U) (G ⋙ U) (fun X h => by
    apply (finiteArithmeticFiber_nonempty_iff L y X).mpr
    exact (finiteArithmeticFiber_nonempty_iff K x X).mp h)
  exact ⟨((Functor.whiskeringRight S.FiniteEtale FintypeCat (Type u)).obj U).preimage η⟩

end AlgebraicGeometry.Scheme
