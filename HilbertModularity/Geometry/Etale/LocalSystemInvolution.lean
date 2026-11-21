/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystemPullback
public import HilbertModularity.Geometry.ProjectiveInvolution

/-! # Specialization of a family under the parameter involution

Pullback along the actual complement automorphism sends specialization at
`ξ` to specialization at `1 - ξ`. A single comparison of continuous families
therefore specializes at every parameter. The existence of that comparison,
and any character twist, remain separate geometric assertions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleLocalSystem

universe u v
variable (K : Type u) [Field K] (R : Type v) [Field R] [TopologicalSpace R]

/-- The actual complement pullback of one continuous family on the punctured line. -/
def complementPullback (L : EtaleLocalSystem K (ProjectiveLine.punctured K) R) :
    EtaleLocalSystem K (ProjectiveLine.punctured K) R :=
  L.pullback (ProjectiveLine.puncturedComplementIso K).hom K

/-- Specialization of complement pullback is the original arithmetic representation
at the complemented parameter. -/
def complementPullbackArithmeticEquiv
    (L : EtaleLocalSystem K (ProjectiveLine.punctured K) R)
    (ξ : ProjectiveLine.Parameter K) :
    ((L.complementPullback K R).arithmeticRepresentation (ProjectiveLine.puncturedPoint K ξ)).Equiv
      (L.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint K (ProjectiveLine.complementParameter K ξ))) :=
  L.pullbackArithmeticEquiv (ProjectiveLine.puncturedComplementIso K).hom K
    (ProjectiveLine.puncturedPoint K ξ)
    (ProjectiveLine.puncturedPoint K (ProjectiveLine.complementParameter K ξ))
    (ProjectiveLine.puncturedPoint_complement K ξ)

/-- One natural comparison with the complement pullback induces comparisons at every parameter. -/
def arithmeticEquivOfComplementIso
    (L M : EtaleLocalSystem K (ProjectiveLine.punctured K) R)
    (e : L.toFunctor ≅ (M.complementPullback K R).toFunctor)
    (ξ : ProjectiveLine.Parameter K) :
    (L.arithmeticRepresentation (ProjectiveLine.puncturedPoint K ξ)).Equiv
      (M.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint K (ProjectiveLine.complementParameter K ξ))) :=
  (arithmeticFiberEquiv K (ProjectiveLine.punctured K)
    (isoWhiskerRight e (forget₂ (TopModuleCat R) (ModuleCat R)))
    (ProjectiveLine.puncturedPoint K ξ)).trans
      (M.complementPullbackArithmeticEquiv K R ξ)

end AlgebraicGeometry.Scheme.EtaleLocalSystem
