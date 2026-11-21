/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.Basic

/-! # Schur's lemma and descent of scalar endomorphisms

Absolute irreducibility forces intertwining endomorphisms to be scalars over
the original coefficient field. This is the descent step used in
[TripathiGoswami, constant character comparison lemma].
-/

@[expose] public section

open scoped TensorProduct

namespace Representation.IntertwiningMap

variable {K G V : Type*} [Field K] [CharZero K] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

/-- If a representation becomes irreducible over an algebraically closed
extension, every intertwining endomorphism is already a scalar over the base field. -/
theorem exists_eq_smul_id_of_baseChange_irreducible
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    (ρ : Representation K G V) [(ρ.baseChange E).IsIrreducible]
    (f : IntertwiningMap ρ ρ) :
    ∃ a : K, f.toLinearMap = a • (1 : Module.End K V) := by
  obtain ⟨a, ha⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ.baseChange E)).surjective (f.baseChange E)
  have hf : f.toLinearMap.baseChange E = a • (1 : Module.End E (E ⊗[K] V)) := by
    exact (congrArg (fun f : IntertwiningMap (ρ.baseChange E) (ρ.baseChange E) => f.toLinearMap) ha).symm
  let n := Module.finrank K V
  have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  have hnE : (n : E) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap K E)).mpr hn
  have ht : algebraMap K E (LinearMap.trace K V f.toLinearMap) = a * (n : E) := by
    have h := congrArg (LinearMap.trace E (E ⊗[K] V)) hf
    simpa only [LinearMap.trace_baseChange, map_smul, LinearMap.trace_one,
      Module.finrank_baseChange, smul_eq_mul] using h
  have ha' : a = algebraMap K E (LinearMap.trace K V f.toLinearMap / (n : K)) := by
    rw [map_div₀, map_natCast]
    exact (eq_div_iff hnE).mpr ht.symm
  refine ⟨LinearMap.trace K V f.toLinearMap / (n : K), ?_⟩
  apply LinearMap.baseChangeHom_injective K V E
  change f.toLinearMap.baseChange E = (_ • (1 : Module.End K V)).baseChange E
  rw [hf, ha', LinearMap.baseChange_smul, LinearMap.baseChange_one]
  exact IsScalarTower.algebraMap_smul E _ _

end Representation.IntertwiningMap
