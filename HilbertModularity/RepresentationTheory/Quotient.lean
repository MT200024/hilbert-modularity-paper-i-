/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarConjugation
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Prod

/-! # Complementary rank-one quotients

Two different rank-one quotients of a two-dimensional representation identify
the representation with their product. The map is the pair of quotient maps.
-/

@[expose] public noncomputable section

namespace Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Distinct one-dimensional subspaces intersect trivially. -/
theorem disjoint_of_finrank_one_of_ne (P Q : Submodule K V)
    (hP : Module.finrank K P = 1) (hQ : Module.finrank K Q = 1) (hne : P ≠ Q) :
    Disjoint P Q := by
  let : FiniteDimensional K P := FiniteDimensional.of_finrank_eq_succ hP
  let : FiniteDimensional K Q := FiniteDimensional.of_finrank_eq_succ hQ
  apply disjoint_iff_inf_le.mpr
  intro v hv
  change v = 0
  by_contra hv0
  have heP : K ∙ v = P := eq_of_le_of_finrank_eq
    ((span_singleton_le_iff_mem v P).mpr hv.1) (by rw [finrank_span_singleton hv0, hP])
  have heQ : K ∙ v = Q := eq_of_le_of_finrank_eq
    ((span_singleton_le_iff_mem v Q).mpr hv.2) (by rw [finrank_span_singleton hv0, hQ])
  exact hne (heP.symm.trans heQ)

/-- Two distinct rank-one quotients of a plane give an isomorphism with their product. -/
def quotientPairEquiv [FiniteDimensional K V] (P Q : Submodule K V)
    (hV : Module.finrank K V = 2)
    (hP : Module.finrank K (V ⧸ P) = 1) (hQ : Module.finrank K (V ⧸ Q) = 1)
    (hne : P ≠ Q) : V ≃ₗ[K] (V ⧸ P) × (V ⧸ Q) := by
  have hdimP : Module.finrank K P = 1 := by
    have h := P.finrank_quotient_add_finrank
    rw [hV, hP] at h
    omega
  have hdimQ : Module.finrank K Q = 1 := by
    have h := Q.finrank_quotient_add_finrank
    rw [hV, hQ] at h
    omega
  apply (P.mkQ.prod Q.mkQ).linearEquivOfInjective
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_prod, ker_mkQ, ker_mkQ]
    exact (disjoint_of_finrank_one_of_ne P Q hdimP hdimQ hne).eq_bot
  · rw [Module.finrank_prod, hV, hP, hQ]

end Submodule

namespace Representation

variable {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (ρ : Representation K G V)

/-- The quotient-pair isomorphism intertwines the original action and the product action. -/
def quotientPairEquiv (P Q : Subrepresentation ρ) (hV : Module.finrank K V = 2)
    (hP : Module.finrank K (V ⧸ P.toSubmodule) = 1)
    (hQ : Module.finrank K (V ⧸ Q.toSubmodule) = 1) (hne : P ≠ Q) :
    ρ.Equiv ((ρ.quotient P.toSubmodule P.apply_mem_toSubmodule).prod
      (ρ.quotient Q.toSubmodule Q.apply_mem_toSubmodule)) :=
  .mk (Submodule.quotientPairEquiv P.toSubmodule Q.toSubmodule hV hP hQ
    (fun h => hne (Subrepresentation.toSubmodule_injective h))) (by intro g; ext v <;> rfl)

end Representation

namespace Representation.Equiv

variable {K G V W : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K G V} {τ : Representation K G W}

/-- An equivalence of representations identifies their lattices of stable subspaces. -/
def subrepresentationOrderIso (e : ρ.Equiv τ) : Subrepresentation ρ ≃o Subrepresentation τ :=
  Subrepresentation.semilinearOrderIso (RingEquiv.refl K) e.toLinearEquiv (fun g v =>
    congrArg (fun f : V →ₗ[K] W => f v) (e.isIntertwining' g))

/-- Corresponding quotients under an equivalence are equivalent representations. -/
def quotientCongr (e : ρ.Equiv τ) (S : Subrepresentation ρ) :
    (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).Equiv
      (τ.quotient (e.subrepresentationOrderIso S).toSubmodule
        (e.subrepresentationOrderIso S).apply_mem_toSubmodule) :=
  .mk (Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl) (by
    intro g
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro v
    change Submodule.Quotient.mk (e (ρ g v)) = Submodule.Quotient.mk (τ g (e v))
    exact congrArg Submodule.Quotient.mk
      (congrArg (fun f : V →ₗ[K] W => f v) (e.isIntertwining' g)))

end Representation.Equiv
