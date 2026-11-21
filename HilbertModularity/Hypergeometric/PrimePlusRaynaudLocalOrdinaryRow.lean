/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudLocalOrdinary

/-! # The selected label-one local operator row

The generic conjugated-coordinate certificate is applied to the actual plus
Jacobian and the fixed Raynaud ordinary basis. -/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms ValuativeRel

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

/-- The selected global action at any prime above `p` agrees with the
label-one Raynaud ordinary coordinates after the standard conjugate
decomposition comparison. -/
theorem primePlusRaynaudLabelOneLocalEquiv_intertwines
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (hmap : C.localMap = AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ 1
      (Nat.coprime_one_left _))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) (v : Fin 2 → RealPrimePowerCompletion p 0) :
    let e := primePlusRaynaudLabelOneLocalEquiv p hp ξ β C hmap d σ
    e (primePlusTateFieldCoordinateAction p hp ξ β
      (g : AbsoluteGalois (realCyclotomicField p)) v) =
      d.coordinateRepresentation p hp ξ (φ g) (e v) := by
  rw [primePlusRaynaudLabelOneLocalEquiv_eq_generic p hp ξ β C hmap d σ]
  exact conjugatedRepresentationCoordinateEquiv_intertwines
    (primePlusTateFieldCoordinateAction p hp ξ β)
    (primePlusLocalTateRepresentation p hp ξ).ρ
    (primePlusLocalGaloisRestriction p)
    (d.coordinateRepresentation p hp ξ)
    (primePlusNativeComparisonLocalEquiv p hp ξ β C hmap)
    (primePlusLabelOneRaynaudCoordinateEquiv p hp ξ d)
    (primeDecompositionGroup Q).subtype φ σ hφ g v

end HilbertModularity.Hypergeometric
