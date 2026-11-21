/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberFlatness
public import HilbertModularity.Hyperelliptic.SpecialFiberStructure

/-! # Properness of the scaled projective model

The actual glued double cover is finite over the projective line. Its
structure morphism to the coefficient spectrum is therefore proper, and the
flatness of that same morphism was established on its two affine charts.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace HilbertModularity.Hyperelliptic

variable {R : Type*} [CommRing R]

/-- The actual scaled cover is proper over its coefficient ring. -/
instance scaledDoubleCover_toSpec_isProper (P : R[X]) (t : R) :
    IsProper (scaledDoubleCoverToSpec P t) := by
  change IsProper (DoubleCover.toProjectiveLine
    (finiteBranchPolynomial P t) (infinityBranchPolynomial P t)
    (P.natDegree + 1) (branch_transition P t) ≫ ProjectiveLine.toSpec R)
  infer_instance

end HilbertModularity.Hyperelliptic
