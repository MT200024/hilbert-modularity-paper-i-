/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.Multiplication
public import HilbertModularity.Topology.TateModule.FiniteGeneration

/-! # Finite generation from geometric multiplication

Finiteness of the actual multiplication morphism makes actual geometric
`p`-torsion finite. Surjectivity makes the geometric point group `p`-divisible.
The concrete inverse-limit generation theorem then proves finite generation
of the actual integral Tate module, as used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K] (A : Over (Spec (CommRingCat.of K)))
  [GrpObj A] [IsCommMonObj A] (p : ℕ)
  [IsFinite (multiplicationMap K A p).left]

/-- Finite geometric multiplication has finitely many actual p-torsion points. -/
instance finite_pTorsion_of_multiplication : Finite (pTorsion K A p) := by
  let f := pointsMap K (AlgebraicClosure K) (multiplicationMap K A p)
  let i : pTorsion K A p → f.ker := fun x => ⟨x.val, by
    change pointsMap K (AlgebraicClosure K) (multiplicationMap K A p) x.val = 0
    rw [pointsMap_multiplication]
    simpa only [pow_one] using AddSubgroup.torsionBy.nsmul_iff.mp x.property⟩
  apply Finite.of_injective i
  intro x y h
  exact Subtype.ext (congrArg (fun z : f.ker => z.val) h)

variable [Fact p.Prime] [Surjective (multiplicationMap K A p).left]

/-- Finite surjective multiplication proves finite generation of the actual integral Tate module. -/
instance integralTate_finite_of_multiplication : Module.Finite ℤ_[p] (integralTate K A p) :=
  TateModule.integral_finite_of_finite_torsion p (Points K (AlgebraicClosure K) A)
    (points_nsmul_surjective K A p)

end AlgebraicGeometry.GroupScheme
