/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimeHypergeometricChecklist

/-! # Residual data from the selected plus Jacobian's integral Tate action -/

public section
noncomputable section

open scoped NumberField Pointwise ValuativeRel TensorProduct
open scoped IsMulCommutative
open ValuativeRel NumberField AlgebraicGeometry AlgebraicGeometry.GroupScheme
open IsDedekindDomain

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms

/-- The determinant of the canonical-prime kernel of the selected plus
Jacobian is the reduced cyclotomic character, once its exact integral Tate
determinant is known. See [TripathiGoswamiRevised, Lemma `RMtorsion`]. -/
theorem primePlusKernel_det_of_exactTate
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p])))) :
    letI := primePlusKernelModule p hp ξ
    ∀ g : AbsoluteGalois (realCyclotomicField p),
      LinearMap.det (primePlusKernelRepresentation p hp ξ g) =
        (realPrimeResidualCyclotomicCharacter (realCyclotomicField p) p
          (by omega) g :
          𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
  let := coefficientKernelModule (realCyclotomicField p)
    (primePlusFiber p hp ξ) (𝓞 (realCyclotomicField p))
      (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
  intro g
  have h := congrArg (fun f => f g)
    (primePlusResidualDeterminantCharacter_of_integralTate p hp ξ E hTateDet)
  exact (det_primePlusKernelRepresentation p hp ξ g).trans (congrArg Units.val h)

/-- Residual determinant on the selected integral Tate coordinates, transported
through the same Jacobian's canonical-prime kernel. See
[TripathiGoswamiRevised, Lemma `RMtorsion`]. -/
theorem primePlusIntegralAction_residualDet_of_exactTate
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p])))) :
    letI := primePlusIntegralTateModule p hp ξ
    letI : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (𝒪[E]) := β.toAlgebra
    ∀ g : AbsoluteGalois (realCyclotomicField p),
      Ideal.Quotient.mk (𝓂[E])
        (LinearMap.det
          (((primePlusIntegralTateBasis p hp ξ).baseChange (𝒪[E])).equivFun.conjRingEquiv
            ((primePlusIntegralTateRepresentation p hp ξ).baseChange (𝒪[E]) g))) =
      ((Units.map κ.toMonoidHom).comp
        (realPrimeResidualCyclotomicCharacter (realCyclotomicField p) p
          (by omega)) g : 𝒪[E] ⧸ 𝓂[E]) := by
  let := primePlusIntegralTateModule p hp ξ
  let := primePlusKernelModule p hp ξ
  let : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
    (𝓞 (realCyclotomicField p))) (𝒪[E]) := β.toAlgebra
  let := (AdicCompletion.evalOneₐ
    (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
  let b := primePlusKernelBasisOfResidualTate p hp ξ
    (primePlusResidualTateBasis p hp ξ)
  let integralAction :=
    ((primePlusIntegralTateBasis p hp ξ).baseChange (𝒪[E])).equivFun.conjRingEquiv.toMonoidHom.comp
      ((primePlusIntegralTateRepresentation p hp ξ).baseChange (𝒪[E]))
  have hkernelDet := primePlusKernel_det_of_exactTate p hp ξ hTateDet
  intro g
  have hmat := primePlusIntegralCoordinateAction_kernelMatrix p hp ξ β κ g
  change Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g)) = _
  calc
    _ = ((LinearMap.toMatrix'
        (integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).det := by
      rw [← LinearMap.det_toMatrix'
        (integralAction g)]
      exact (Ideal.Quotient.mk (𝓂[E])).map_det _
    _ = ((LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map κ.toRingHom).det :=
      congrArg Matrix.det hmat.symm
    _ = κ (LinearMap.det (primePlusKernelRepresentation p hp ξ g)) := by
      rw [← LinearMap.det_toMatrix b]
      exact (κ.toRingHom.map_det _).symm
    _ = _ := by rw [hkernelDet g]; rfl

/-- A matrix comparison with the selected plus Jacobian's canonical-prime
kernel transports its rational torsion point into a fixed residual vector on
the *same* integral action. The determinant is recorded separately, so this
construction also applies to other integral coordinates. See
[TripathiGoswamiRevised, Lemma `RMtorsion`]. -/
noncomputable def skinnerWilesResidualData_of_primePlusKernelComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (integralAction : Representation (𝒪[E])
      (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → 𝒪[E]))
    (hintegral : ∀ g i j,
      ((integralAction g (Pi.single j 1) i : 𝒪[E]) : E) =
        ρ g (Pi.single j 1) i)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b (primePlusKernelRepresentation p hp ξ g)).map
        κ.toRingHom =
      (LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E])))
    (ε : AbsoluteGalois (realCyclotomicField p) →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (hdet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E])) :
    HilbertModularForms.SkinnerWilesResidualData ρ := by
  let fixed := exists_primePlusKernel_fixed_in_residualCoordinates p hp ξ
    integralAction κ b hmat
  let w := Classical.choose fixed
  have hw := (Classical.choose_spec fixed).1
  have hwfixed := (Classical.choose_spec fixed).2
  exact skinnerWilesResidualData_of_fixedVector ρ
    integralAction hintegral ε w hw hwfixed hdet

/-- The actual canonical-prime fixed torsion line keeps the trivial residual
character in the second position after comparison with integral coordinates. -/
theorem skinnerWilesResidualData_of_primePlusKernelComparison_chi₂_eq_one
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (integralAction : Representation (𝒪[E])
      (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → 𝒪[E]))
    (hintegral : ∀ g i j,
      ((integralAction g (Pi.single j 1) i : 𝒪[E]) : E) =
        ρ g (Pi.single j 1) i)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b (primePlusKernelRepresentation p hp ξ g)).map
        κ.toRingHom =
      (LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E])))
    (ε : AbsoluteGalois (realCyclotomicField p) →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (hdet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E])) :
    (skinnerWilesResidualData_of_primePlusKernelComparison p hp ξ ρ
      integralAction hintegral κ b hmat ε hdet).chi₂ = 1 := by
  unfold skinnerWilesResidualData_of_primePlusKernelComparison
  exact skinnerWilesResidualData_of_fixedVector_chi₂_eq_one
    ρ integralAction hintegral ε _ _ _ hdet

/-- The selected plus Jacobian itself supplies the fixed residual line and
cyclotomic residual determinant on its chosen Tate coordinates. The exact
characteristic-zero completed-Tate determinant is retained as an arithmetic
premise. See [TripathiGoswamiRevised, Lemma `RMtorsion` and Proposition
`primeresidual`]. -/
noncomputable def primePlusSelectedTateResidualData
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p])))) :
    HilbertModularForms.SkinnerWilesResidualData
      (primePlusTateFieldCoordinateAction p hp ξ β) := by
  letI := primePlusIntegralTateModule p hp ξ
  letI := primePlusKernelModule p hp ξ
  letI : Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
    (𝓞 (realCyclotomicField p))) (𝒪[E]) := β.toAlgebra
  letI := (AdicCompletion.evalOneₐ
    (Ideal.span {realPrimeGenerator p}) : _).toRingHom.toAlgebra
  let b := primePlusKernelBasisOfResidualTate p hp ξ
    (primePlusResidualTateBasis p hp ξ)
  exact skinnerWilesResidualData_of_primePlusKernelComparison
    p hp ξ (primePlusTateFieldCoordinateAction p hp ξ β)
    (primePlusIntegralTateCoordinateAction p hp ξ β)
    (primePlusTateFieldCoordinateAction_integral_coeff p hp ξ β)
    κ b
    (fun g => by
      simpa only [b, primePlusIntegralTateCoordinateAction_apply]
        using (primePlusIntegralCoordinateAction_kernelMatrix p hp ξ β κ g))
    ((Units.map κ.toMonoidHom).comp
      (realPrimeResidualCyclotomicCharacter (realCyclotomicField p) p (by omega)))
    (fun g => by
      rw [primePlusIntegralTateCoordinateAction_apply]
      exact primePlusIntegralAction_residualDet_of_exactTate p hp ξ β κ hTateDet g)

/-- The selected plus Jacobian's canonical-prime torsion point fixes the
second residual character to one on the same integral Tate coordinates. -/
theorem primePlusSelectedTateResidualData_chi₂_eq_one
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [FaithfulSMul (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[E])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p])))) :
    (primePlusSelectedTateResidualData p hp ξ β κ hTateDet).chi₂ = 1 := by
  unfold primePlusSelectedTateResidualData
  exact skinnerWilesResidualData_of_primePlusKernelComparison_chi₂_eq_one
    p hp ξ _ _ _ κ _ _ _ _


end HilbertModularity.Hypergeometric
