/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GenericFundamentalGroup
public import HilbertModularity.Geometry.ProjectiveLine.GenericEtale

/-! # Generic arithmetic monodromy on the punctured parameter line

The absolute Galois group of `K(X)` surjects onto the actual finite étale
fundamental group based at the existing rational coordinate point.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K] [CharZero K]

/-- Generic arithmetic Galois action realizes every finite étale monodromy automorphism
of the punctured parameter scheme. -/
theorem puncturedRationalPoint_galoisToEtaleFundamentalGroup_surjective :
    Function.Surjective
      (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K)) := by
  let x := Spec.map (CommRingCat.ofHom (algebraMap (puncturedCoordinateRing K) (RatFunc K)))
  let E := Scheme.etaleFundamentalGroupIsoEquiv (puncturedAffineIso K).symm (RatFunc K) x
  intro α
  obtain ⟨β, hβ⟩ := E.surjective α
  obtain ⟨g, hg⟩ := Scheme.galoisToEtaleFundamentalGroup_surjective_of_fractionField
    (puncturedCoordinateRing K) (RatFunc K) β
  refine ⟨g, ?_⟩
  exact (Scheme.etaleFundamentalGroupIsoEquiv_galois
    (puncturedAffineIso K).symm (RatFunc K) x g).symm.trans
      ((congrArg E hg).trans hβ)

end AlgebraicGeometry.ProjectiveLine
