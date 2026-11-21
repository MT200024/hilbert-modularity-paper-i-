/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist

/-! # Native local action on selected Tate coordinates

At the canonical completed coefficient field, an operator-level comparison
with the integral Tate lattice identifies the selected field coordinates with
the native completed Tate representation. This supplies the global action
part of the local ordinary comparison after the decomposition map is fixed.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme
open scoped NumberField TensorProduct ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms ValuativeRel

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower

/-- Extending a representation from a field to itself leaves its action
unchanged. The equivalence is the left tensor unit. -/
private def representationBaseChangeSelfEquiv
    {F G V : Type*} [Field F] [Monoid G]
    [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : (ρ.baseChange F).Equiv ρ := by
  refine .mk (TensorProduct.lid F V) ?_
  intro g
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
      change (TensorProduct.lid F V) (a ⊗ₜ[F] ρ g v) =
        ρ g ((TensorProduct.lid F V) (a ⊗ₜ[F] v))
      simp only [TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The selected global field coordinates are the native completed RM Tate
action once the actual integral lattice action is compared over the canonical
local field. No determinant equality is assumed here. -/
def primePlusTateFieldCoordinateNativeEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [ValuativeRel (RealPrimePowerCompletion p 0)]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (hβ : (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p)))
      (RealPrimePowerCompletion p 0)) =
      ((𝒪[RealPrimePowerCompletion p 0]).subtype.comp β).toAlgebra)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0)
        (RealPrimePowerCompletion p 0) :=
          (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
        (RealPrimePowerCompletion p 0)).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (RealPrimePowerCompletion p 0))) :
    (primePlusTateFieldCoordinateAction p hp ξ β).Equiv
      (primePlusLocalTateRepresentation p hp ξ).ρ := by
  letI := primePlusIntegralTateModule p hp ξ
  letI : Algebra (RealPrimePowerCompletion p 0)
      (RealPrimePowerCompletion p 0) :=
    (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
  exact (primePlusTateFieldCoordinateEquiv p hp ξ β hβ).trans
    (e.symm.trans (representationBaseChangeSelfEquiv
      (primePlusLocalTateRepresentation p hp ξ).ρ))

/-- The decomposition action is the native action along the fixed local
Galois restriction. -/
theorem primePlusDecompositionRepresentation_apply
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (v : primePlusDecompositionRepresentation p hp ξ) :
    (primePlusDecompositionRepresentation p hp ξ).ρ g v =
      (primePlusLocalTateRepresentation p hp ξ).ρ
        (primePlusLocalGaloisRestriction p g) v := by
  unfold primePlusDecompositionRepresentation Rep.of MonoidHom.comp
  rfl

/-- Once a decomposition homomorphism is compatible with the chosen local
Galois restriction, the same-Jacobian global field action intertwines the
native local Tate action. This proves the operator part of the local
Skinner--Wiles comparison; constructing the decomposition homomorphism and
matching the ordinary basis and residual inertia remain separate. -/
theorem primePlusTateFieldCoordinate_decompositionIntertwines
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [ValuativeRel (RealPrimePowerCompletion p 0)]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (hβ : (inferInstance : Algebra (AdicCompletion
      (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p)))
      (RealPrimePowerCompletion p 0)) =
      ((𝒪[RealPrimePowerCompletion p 0]).subtype.comp β).toAlgebra)
    (e : letI := primePlusIntegralTateModule p hp ξ
      letI : Algebra (RealPrimePowerCompletion p 0)
        (RealPrimePowerCompletion p 0) :=
          (AlgHom.id ℚ_[p] (RealPrimePowerCompletion p 0)).toAlgebra
      ((primePlusLocalTateRepresentation p hp ξ).ρ.baseChange
        (RealPrimePowerCompletion p 0)).Equiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (RealPrimePowerCompletion p 0)))
    (H : Type*) [Monoid H]
    (ι : H →* AbsoluteGalois (realCyclotomicField p))
    (δ : H →* Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hδ : ∀ g, primePlusLocalGaloisRestriction p (δ g) = ι g)
    (g : H) (v : Fin 2 → RealPrimePowerCompletion p 0) :
    let E := primePlusTateFieldCoordinateNativeEquiv p hp ξ β hβ e
    E (primePlusTateFieldCoordinateAction p hp ξ β (ι g) v) =
      (primePlusLocalTateRepresentation p hp ξ).ρ
        (primePlusLocalGaloisRestriction p (δ g)) (E v) := by
  let E := primePlusTateFieldCoordinateNativeEquiv p hp ξ β hβ e
  have h := LinearMap.congr_fun
    (E.toIntertwiningMap.isIntertwining' (ι g)) v
  change E (primePlusTateFieldCoordinateAction p hp ξ β (ι g) v) =
    (primePlusLocalTateRepresentation p hp ξ).ρ (ι g) (E v) at h
  rw [hδ g]
  exact h

end HilbertModularity.Hypergeometric
