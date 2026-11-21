/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.SemisimpleBaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RepresentationTheory.Irreducible

/-! # Reflection of irreducibility across scalar extension -/

public noncomputable section

open scoped TensorProduct

namespace Submodule

/-- A subspace keeps its dimension under extension of coefficient fields. -/
theorem finrank_baseChange_field
    {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] (P : Submodule K V) :
    Module.finrank L (P.baseChange L) = Module.finrank K P := by
  calc
    Module.finrank L (P.baseChange L) = Module.finrank L (L ⊗[K] P) :=
      (Submodule.toBaseChange.toLinearEquiv L P).finrank_eq.symm
    _ = Module.finrank K P := Module.finrank_baseChange

end Submodule

namespace Representation

/-- Irreducibility over a coefficient-field extension reflects to a
finite-dimensional representation over the original field. -/
theorem isIrreducible_of_baseChange
    {K L G V : Type*} [Field K] [Field L] [Algebra K L]
    [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K G V)
    (h : (ρ.baseChange L).IsIrreducible) : ρ.IsIrreducible := by
  apply (isSimpleOrder_iff (Subrepresentation ρ)).2
  constructor
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨⊥, ⊤, ?_⟩
    intro heq
    have hvtop : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := by
      change v ∈ (⊤ : Submodule K V)
      trivial
    rw [← heq] at hvtop
    have hvzero : v = 0 := by
      change v ∈ (⊥ : Submodule K V) at hvtop
      simpa using hvtop
    exact hv hvzero
  · intro S
    have hS : S.baseChange L = ⊥ ∨ S.baseChange L = ⊤ :=
      ((isSimpleOrder_iff (Subrepresentation (ρ.baseChange L))).1 h).2
        (S.baseChange L)
    rcases hS with hbot | htop
    · left
      apply Subrepresentation.ext
      change S.toSubmodule = (⊥ : Submodule K V)
      apply Submodule.finrank_eq_zero.mp
      calc
        Module.finrank K S.toSubmodule =
            Module.finrank L ((S.baseChange L).toSubmodule) := by
              rw [Subrepresentation.baseChange_toSubmodule]
              exact (Submodule.finrank_baseChange_field S.toSubmodule).symm
        _ = 0 := by
          rw [hbot]
          change Module.finrank L (⊥ : Submodule L (L ⊗[K] V)) = 0
          simp
    · right
      apply Subrepresentation.ext
      change S.toSubmodule = (⊤ : Submodule K V)
      apply Submodule.eq_top_of_finrank_eq
      calc
        Module.finrank K S.toSubmodule =
            Module.finrank L ((S.baseChange L).toSubmodule) := by
              rw [Subrepresentation.baseChange_toSubmodule]
              exact (Submodule.finrank_baseChange_field S.toSubmodule).symm
        _ = Module.finrank L (L ⊗[K] V) := by
          rw [htop]
          change Module.finrank L (⊤ : Submodule L (L ⊗[K] V)) = _
          simp
        _ = Module.finrank K V := Module.finrank_baseChange

/-- Tensor extension of a rank-two function-space action is the usual
entrywise coefficient extension in its standard basis. -/
def baseChangePiEquiv
    {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G]
    (ρ : Representation K G (Fin 2 → K)) :
    (ρ.baseChange L).Equiv (ρ.mapCoefficients (algebraMap K L)) := by
  simpa only [inBasis_pi ρ] using
    (ρ.baseChangeInBasisEquiv L (Pi.basisFun K (Fin 2)))

/-- Irreducibility after an entrywise field embedding reflects to the
original rank-two coefficient action. -/
theorem isIrreducible_of_mapCoefficients
    {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G]
    (ρ : Representation K G (Fin 2 → K))
    (h : (ρ.mapCoefficients (algebraMap K L)).IsIrreducible) :
    ρ.IsIrreducible := by
  have hbase : (ρ.baseChange L).IsIrreducible :=
    (OrderIso.isSimpleOrder_iff
      (baseChangePiEquiv (L := L) ρ).subrepresentationOrderIso).mpr h
  exact isIrreducible_of_baseChange ρ hbase

end Representation
