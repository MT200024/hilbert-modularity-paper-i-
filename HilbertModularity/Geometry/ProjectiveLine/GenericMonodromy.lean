/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.GenericFundamentalGroup
public import HilbertModularity.Geometry.Etale.FiberNaturality
public import HilbertModularity.RepresentationTheory.SurjectiveRestriction
public import Mathlib.RepresentationTheory.Rep.Res

/-! # Generic arithmetic detection of monodromy on the punctured line

The actual generic arithmetic action detects intertwiners and invariant
submodules of monodromy. No geometric generating tuple is assumed here.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine
universe u v w
variable (K : Type u) [Field K] [CharZero K] (L : Type v) [Field L]

/-- Restricting actual monodromy representations to the generic arithmetic group
retains all intertwiners. -/
theorem genericArithmeticRestriction_full :
    (Rep.resFunctor.{w} (k := L)
      (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K))).Full :=
  Rep.full_res _ (puncturedRationalPoint_galoisToEtaleFundamentalGroup_surjective K)

/-- A family is irreducible at the generic arithmetic point exactly when its
actual monodromy representation at that point is irreducible. -/
theorem genericArithmeticFiber_isIrreducible_iff
    (M : Scheme.EtaleFiberGroupoid (RatFunc K) (punctured K) ⥤ ModuleCat.{w} L) :
    (Scheme.arithmeticFiberRepresentation (RatFunc K) (punctured K) M
      (puncturedRationalPoint K)).IsIrreducible ↔
    (Scheme.fiberMonodromy (RatFunc K) (punctured K) M
      (puncturedRationalPoint K)).IsIrreducible :=
  Representation.isIrreducible_comp_iff_of_surjective _ _
    (puncturedRationalPoint_galoisToEtaleFundamentalGroup_surjective K)

end AlgebraicGeometry.ProjectiveLine
