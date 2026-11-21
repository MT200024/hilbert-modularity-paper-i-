/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparison
public import HilbertModularity.Geometry.Etale.GeometricFiberPath
public import HilbertModularity.Geometry.ProjectiveLine.CoordinateRing

/-! # Specialization of the arithmetic RM comparison

The arithmetic comparison character is constructed on the generic punctured
line. Transport of both local systems along the same étale path gives its
specialization at another rational parameter. -/

public noncomputable section

open AlgebraicGeometry

namespace HilbertModularity.Hypergeometric

variable (K : Type*) [Field K] [CharZero K]

/-- A path between the actual geometric fibre functors at two nonsingular
rational parameters of the connected punctured line. -/
def puncturedArithmeticFiberPath (ξ₀ ξ : ProjectiveLine.Parameter K) :
    Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ₀) ≅
      Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ) :=
  Scheme.finiteArithmeticFiberIso K K
    (ProjectiveLine.puncturedPoint K ξ₀) (ProjectiveLine.puncturedPoint K ξ)

/-- A generic arithmetic comparison of two actual étale families specializes
with the same comparison character at each rational fibre. The two path maps
transport the same generic comparison; the character is independent of the
parameter. -/
def puncturedComparisonFiberEquiv
    (ξ₀ ξ : ProjectiveLine.Parameter K)
    (e : Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ₀) ≅
      Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ))
    {L : Type*} [Field L] [TopologicalSpace L]
    (F_RM F_HGM : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ)
    (h : ((Representation.ofCharacter (ν.comp (puncturedArithmeticProjectionHom K ξ₀))).tprod
      (puncturedFiberMonodromy K ξ₀ F_RM)).Equiv
        (puncturedFiberMonodromy K ξ₀ F_HGM)) :
    ((Representation.ofCharacter ν).tprod
      (puncturedFiberArithmeticRepresentation K ξ F_RM)).Equiv
        (puncturedFiberArithmeticRepresentation K ξ F_HGM) := by
  have hν : ∀ g, ν ((puncturedArithmeticProjectionHom K ξ₀)
      ((puncturedArithmeticLoopsAlongPath K ξ₀ ξ e) g)) = ν g := by
    intro g
    exact puncturedArithmeticCharacter_alongPath K ξ₀ ξ e ν g
  exact
  Representation.characterTensorEquivTransport
    (puncturedArithmeticProjectionHom K ξ₀)
    (puncturedFiberMonodromy K ξ₀ F_RM)
    (puncturedFiberMonodromy K ξ₀ F_HGM)
    (puncturedFiberArithmeticRepresentation K ξ F_RM)
    (puncturedFiberArithmeticRepresentation K ξ F_HGM)
    ν h (puncturedArithmeticLoopsAlongPath K ξ₀ ξ e) hν
    (puncturedArithmeticFiberPathEquiv K ξ₀ ξ e F_RM)
    (puncturedArithmeticFiberPathEquiv K ξ₀ ξ e F_HGM)

/-- One generic comparison and one Galois character give the comparison at
every rational nonsingular fibre of the same two local systems. -/
def puncturedComparisonAllFibers
    (ξ₀ : ProjectiveLine.Parameter K)
    {L : Type*} [Field L] [TopologicalSpace L]
    (F_RM F_HGM : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ)
    (h : ((Representation.ofCharacter (ν.comp (puncturedArithmeticProjectionHom K ξ₀))).tprod
      (puncturedFiberMonodromy K ξ₀ F_RM)).Equiv
        (puncturedFiberMonodromy K ξ₀ F_HGM)) :
    ∀ ξ : ProjectiveLine.Parameter K,
      ((Representation.ofCharacter ν).tprod
        (puncturedFiberArithmeticRepresentation K ξ F_RM)).Equiv
          (puncturedFiberArithmeticRepresentation K ξ F_HGM) :=
  fun ξ => puncturedComparisonFiberEquiv K ξ₀ ξ
    (puncturedArithmeticFiberPath K ξ₀ ξ) F_RM F_HGM ν h


end HilbertModularity.Hypergeometric
