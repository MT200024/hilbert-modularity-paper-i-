/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Monodromy.Rigidity
public import HilbertModularity.LinearAlgebra.RankTwoTrace
public import HilbertModularity.RepresentationTheory.Generators
public import Mathlib.Topology.Algebra.Module.Basic

/-! # Rigidity of continuous rank-two representations

The two finite-cusp unipotents determine an irreducible rank-two
representation from its trace at infinity. The argument applies to
algebraic generators and to dense generators of a profinite group.
We follow [TripathiGoswami, rigid triple lemma].
-/

@[expose] public section

namespace Representation

variable {K G : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [Group G] [TopologicalSpace G]

/-- Continuous irreducible rank-two representations with two unipotent
topological generators and the same product trace are isomorphic. -/
theorem equiv_of_unipotent_generators
    (ρ σ : Representation K G (Fin 2 → K)) [ρ.IsIrreducible] [σ.IsIrreducible]
    (g₀ g₁ : G) (hg : Dense (Subgroup.closure {g₀, g₁} : Set G))
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (hρ₀ : (ρ g₀ - 1) ^ 2 = 0) (hρ₁ : (ρ g₁ - 1) ^ 2 = 0) (hρne : ρ g₁ ≠ 1)
    (hσ₀ : (σ g₀ - 1) ^ 2 = 0) (hσ₁ : (σ g₁ - 1) ^ 2 = 0) (hσne : σ g₁ ≠ 1)
    (ht : LinearMap.trace K (Fin 2 → K) (ρ (g₀ * g₁)) =
      LinearMap.trace K (Fin 2 → K) (σ (g₀ * g₁))) : Nonempty (ρ.Equiv σ) := by
  have hr : ∀ v, ρ g₀ v = v → ρ g₁ v = v → v = 0 := by
    intro v hv₀ hv₁
    apply ρ.eq_zero_of_forall_apply_eq hρne v
    apply ρ.apply_eq_of_dense_generators hg v (hρ v)
    rintro g (rfl | rfl)
    · exact hv₀
    · exact hv₁
  have hs : ∀ v, σ g₀ v = v → σ g₁ v = v → v = 0 := by
    intro v hv₀ hv₁
    apply σ.eq_zero_of_forall_apply_eq hσne v
    apply σ.apply_eq_of_dense_generators hg v (hσ v)
    rintro g (rfl | rfl)
    · exact hv₀
    · exact hv₁
  obtain ⟨e, he₀, he₁⟩ := HilbertModularity.Monodromy.exists_equiv_unipotent_pair
    (ρ g₀) (ρ g₁) (σ g₀) (σ g₁) hρ₀ hρ₁ hρne hr hσ₀ hσ₁ hσne hs
    (by simpa only [map_mul] using ht)
  apply equiv_of_intertwines_dense_generators ρ σ e e.toLinearMap.continuous_on_pi hg hρ hσ
  rintro g (rfl | rfl)
  · exact he₀
  · exact he₁

/-- For a product-one triple, the trace of the third generator determines
an irreducible rank-two representation with nonidentity unipotent finite-cusp
monodromy. The isomorphism already exists over the coefficient field. -/
theorem equiv_of_unipotent_triple
    (ρ σ : Representation K G (Fin 2 → K)) [ρ.IsIrreducible] [σ.IsIrreducible]
    (g₀ g₁ gInf : G) (hprod : g₀ * g₁ * gInf = 1)
    (hg : Dense (Subgroup.closure {g₀, g₁} : Set G))
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (hρ₀ : (ρ g₀ - 1) ^ 2 = 0) (hρ₁ : (ρ g₁ - 1) ^ 2 = 0) (hρne : ρ g₁ ≠ 1)
    (hσ₀ : (σ g₀ - 1) ^ 2 = 0) (hσ₁ : (σ g₁ - 1) ^ 2 = 0) (hσne : σ g₁ ≠ 1)
    (ht : LinearMap.trace K (Fin 2 → K) (ρ gInf) =
      LinearMap.trace K (Fin 2 → K) (σ gInf)) : Nonempty (ρ.Equiv σ) := by
  have trace_eq (π : Representation K G (Fin 2 → K)) [π.IsIrreducible]
      (hπ : ∀ v, Continuous (fun g => π g v)) (h₀ : (π g₀ - 1) ^ 2 = 0)
      (h₁ : (π g₁ - 1) ^ 2 = 0) (hne : π g₁ ≠ 1) :
      LinearMap.trace K (Fin 2 → K) (π gInf) =
        LinearMap.trace K (Fin 2 → K) (π (g₀ * g₁)) := by
    rw [map_mul]
    apply HilbertModularity.Monodromy.trace_third_eq_trace_product
      (π g₀) (π g₁) (π gInf) h₀ h₁ hne
    · intro v hv₀ hv₁
      apply π.eq_zero_of_forall_apply_eq hne v
      apply π.apply_eq_of_dense_generators hg v (hπ v)
      rintro g (rfl | rfl)
      · exact hv₀
      · exact hv₁
    · rw [← map_mul, ← map_mul, hprod, map_one]
  apply equiv_of_unipotent_generators ρ σ g₀ g₁ hg hρ hσ hρ₀ hρ₁ hρne hσ₀ hσ₁ hσne
  rw [← trace_eq ρ hρ hρ₀ hρ₁ hρne, ← trace_eq σ hσ hσ₀ hσ₁ hσne, ht]

/-- Two irreducible continuous rank-two representations with product-one
unipotent triples and the same distinct eigenvalues at infinity are isomorphic.
No extension of the coefficient field is required once the eigenvalues lie in it. -/
theorem equiv_of_unipotent_triple_eigenvalues
    (ρ σ : Representation K G (Fin 2 → K)) [ρ.IsIrreducible] [σ.IsIrreducible]
    (g₀ g₁ gInf : G) (hprod : g₀ * g₁ * gInf = 1)
    (hg : Dense (Subgroup.closure {g₀, g₁} : Set G))
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (hρ₀ : (ρ g₀ - 1) ^ 2 = 0) (hρ₁ : (ρ g₁ - 1) ^ 2 = 0) (hρne : ρ g₁ ≠ 1)
    (hσ₀ : (σ g₀ - 1) ^ 2 = 0) (hσ₁ : (σ g₁ - 1) ^ 2 = 0) (hσne : σ g₁ ≠ 1)
    {α β : K} (hαβ : α ≠ β)
    (hρα : Module.End.HasEigenvalue (ρ gInf) α) (hρβ : Module.End.HasEigenvalue (ρ gInf) β)
    (hσα : Module.End.HasEigenvalue (σ gInf) α) (hσβ : Module.End.HasEigenvalue (σ gInf) β) :
    Nonempty (ρ.Equiv σ) := by
  apply equiv_of_unipotent_triple ρ σ g₀ g₁ gInf hprod hg hρ hσ
    hρ₀ hρ₁ hρne hσ₀ hσ₁ hσne
  rw [Module.End.trace_eq_add_of_hasEigenvalue (Pi.basisFun K (Fin 2)) _ hαβ hρα hρβ,
    Module.End.trace_eq_add_of_hasEigenvalue (Pi.basisFun K (Fin 2)) _ hαβ hσα hσβ]

/-- The common eigenvalues may lie in any extension of the coefficient field.
The resulting rigidity isomorphism still descends to the original field. -/
theorem equiv_of_unipotent_triple_eigenvalues_baseChange
    (ρ σ : Representation K G (Fin 2 → K)) [ρ.IsIrreducible] [σ.IsIrreducible]
    (g₀ g₁ gInf : G) (hprod : g₀ * g₁ * gInf = 1)
    (hg : Dense (Subgroup.closure {g₀, g₁} : Set G))
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (hσ : ∀ v, Continuous (fun g => σ g v))
    (hρ₀ : (ρ g₀ - 1) ^ 2 = 0) (hρ₁ : (ρ g₁ - 1) ^ 2 = 0) (hρne : ρ g₁ ≠ 1)
    (hσ₀ : (σ g₀ - 1) ^ 2 = 0) (hσ₁ : (σ g₁ - 1) ^ 2 = 0) (hσne : σ g₁ ≠ 1)
    (E : Type*) [Field E] [Algebra K E] {α β : E} (hαβ : α ≠ β)
    (hρα : Module.End.HasEigenvalue ((ρ gInf).baseChange E) α)
    (hρβ : Module.End.HasEigenvalue ((ρ gInf).baseChange E) β)
    (hσα : Module.End.HasEigenvalue ((σ gInf).baseChange E) α)
    (hσβ : Module.End.HasEigenvalue ((σ gInf).baseChange E) β) :
    Nonempty (ρ.Equiv σ) := by
  apply equiv_of_unipotent_triple ρ σ g₀ g₁ gInf hprod hg hρ hσ
    hρ₀ hρ₁ hρne hσ₀ hσ₁ hσne
  apply (algebraMap K E).injective
  rw [← LinearMap.trace_baseChange, ← LinearMap.trace_baseChange]
  rw [Module.End.trace_eq_add_of_hasEigenvalue ((Pi.basisFun K (Fin 2)).baseChange E)
    _ hαβ hρα hρβ,
    Module.End.trace_eq_add_of_hasEigenvalue ((Pi.basisFun K (Fin 2)).baseChange E)
    _ hαβ hσα hσβ]

end Representation
