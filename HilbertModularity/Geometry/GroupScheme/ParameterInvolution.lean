/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.BaseChange
public import HilbertModularity.Geometry.ProjectiveInvolution

/-! # Fibres under the parameter involution

The fibre at `ξ` of the family pulled back along `t ↦ 1 - t` is the original
family at `1 - ξ`. This is actual scheme base change and induces Tate
representation equivalences. An identification of the original family with its
pullback remains additional geometric data; it is not inferred from this identity.
See [TripathiGoswami, cusp involution].
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.GroupScheme

universe u
variable (K : Type u) [Field K]
  (A : CommGrp (Over (ProjectiveLine.punctured K)))
  (ξ : ProjectiveLine.Parameter K)

/-- The fibre of the complement pullback is the original family at the complemented parameter. -/
def complementPullbackFiberIso :
    parameterFiber K
      ((Over.pullback (ProjectiveLine.puncturedComplementIso K).hom).mapCommGrp.obj A) ξ ≅
      parameterFiber K A (ProjectiveLine.complementParameter K ξ) := by
  simpa only [parameterFiber, ProjectiveLine.puncturedPoint_complement] using
    fiberBaseChangeIso K A (ProjectiveLine.puncturedComplementIso K).hom
      (ProjectiveLine.puncturedPoint K ξ)

variable (p : ℕ) [Fact p.Prime]

/-- Complement base change identifies the actual integral Galois representations of the two fibres. -/
def complementPullbackIntegralTateEquiv :
    (integralTateRepresentation K (parameterFiber K
      ((Over.pullback (ProjectiveLine.puncturedComplementIso K).hom).mapCommGrp.obj A) ξ).X p).Equiv
      (integralTateRepresentation K
        (parameterFiber K A (ProjectiveLine.complementParameter K ξ)).X p) :=
  integralTateEquiv K p (complementPullbackFiberIso K A ξ)

/-- Complement base change identifies the actual covariant rational Tate representations of the two fibres. -/
def complementPullbackTateEquiv :
    (tateRepresentation K (parameterFiber K
      ((Over.pullback (ProjectiveLine.puncturedComplementIso K).hom).mapCommGrp.obj A) ξ).X p).Equiv
      (tateRepresentation K
        (parameterFiber K A (ProjectiveLine.complementParameter K ξ)).X p) :=
  tateEquiv K p (complementPullbackFiberIso K A ξ)

end AlgebraicGeometry.GroupScheme
