/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusRaynaudComplementDeepCuspOrdinary
public import HilbertModularity.Hypergeometric.PrimePlusRaynaudComplementOrdering

/-! # The selected complementary-cusp residual lower character -/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

local instance complementUpperResidualGalCompact (p : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) := by
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  infer_instance

/-- At the original selected fibre of the rational complementary deep cusp,
the Raynaud quotient's quadratic residual character is exactly the second
character of the swapped native residual datum. -/
theorem primePlusRaynaudCubicDifference_lowerResidual_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) :
    let d := primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀
      hξ hB hAB hdeep
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸
            𝓂[RealPrimePowerCompletion p 0])).comp
      (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
    (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ).swap.chi₂
      (g : AbsoluteGalois (realCyclotomicField p)) := by
  exact C.complementLowerResidual_eq_of_quadraticLower p hp
    (darmonRationalParameter p ξ₀) β κ 1 (Nat.coprime_one_left _)
    (primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀ hξ hB hAB hdeep)
    (primePlusRaynaudCubicDifferenceOrdinaryData_lowerCharacter p hp ξ₀
      hξ hB hAB hdeep) Q σ φ hφ g

/-- In a chosen triangular Tate basis, matching the determinant and the
lower residual character on the same two integral lattices forces the upper
residual character to match as well. -/
theorem upperResidual_eq_of_det_and_lower
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hfield : ∀ g : primeDecompositionGroup Q,
      LinearMap.det ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ (φ g)) =
        LinearMap.det (ρ (g : AbsoluteGalois (realCyclotomicField p))))
    (hlower : ∀ g : primeDecompositionGroup Q,
      ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
          𝒪[RealPrimePowerCompletion p 0] →*
            𝒪[RealPrimePowerCompletion p 0] ⧸
              𝓂[RealPrimePowerCompletion p 0])).comp
        (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
          D.chi₂ (g : AbsoluteGalois (realCyclotomicField p)))
    (g : primeDecompositionGroup Q) :
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸
            𝓂[RealPrimePowerCompletion p 0])).comp
      (IsNonarchimedeanLocalField.integerCharacter
        (RealPrimePowerCompletion p 0)
        d.upperCharacter d.upper_continuous)) (φ g) =
      D.chi₁ (g : AbsoluteGalois (realCyclotomicField p)) := by
  let F := RealPrimePowerCompletion p 0
  let q : 𝒪[F] →+* 𝒪[F] ⧸ 𝓂[F] := Ideal.Quotient.mk (𝓂[F])
  let u₁ := IsNonarchimedeanLocalField.integerCharacter F
    d.upperCharacter d.upper_continuous
  let u₂ := Representation.determinantCharacter d.lattice.toRepresentation
  let : Submodule.IsLattice F d.lattice.toSubmodule := d.lattice_isLattice
  have h₁F : (algebraMap 𝒪[F] F) (u₁ (φ g) : 𝒪[F]) =
      (d.upperCharacter (φ g) : F) := by
    have h := congrArg
      (fun f : Gal(PadicAlgCl p/F) →* Fˣ => f (φ g))
      (IsNonarchimedeanLocalField.map_integerCharacter F
        d.upperCharacter d.upper_continuous)
    have hval := congrArg (fun z : Fˣ => (z : F)) h
    simp only [MonoidHom.comp_apply, Units.coe_map] at hval
    change (algebraMap 𝒪[F] F) (u₁ (φ g) : 𝒪[F]) =
      (d.upperCharacter (φ g) : F) at hval
    exact hval
  have h₂F : (algebraMap 𝒪[F] F) (u₂ (φ g) : 𝒪[F]) =
      (d.lowerCharacter (φ g) : F) := by
    have h := congrArg
      (fun f : Gal(PadicAlgCl p/F) →* Fˣ => f (φ g))
      (Representation.map_determinantCharacter_characterLattice
        d.lowerCharacter d.lattice)
    have hval := congrArg (fun z : Fˣ => (z : F)) h
    simp only [MonoidHom.comp_apply, Units.coe_map] at hval
    change (algebraMap 𝒪[F] F) (u₂ (φ g) : 𝒪[F]) =
      (d.lowerCharacter (φ g) : F) at hval
    exact hval
  have hint : (u₁ (φ g) : 𝒪[F]) * (u₂ (φ g) : 𝒪[F]) =
      LinearMap.det (D.integralAction
        (g : AbsoluteGalois (realCyclotomicField p))) := by
    apply IsFractionRing.injective 𝒪[F] F
    calc
      (((u₁ (φ g) : 𝒪[F]) * (u₂ (φ g) : 𝒪[F]) : 𝒪[F]) : F) =
          (d.upperCharacter (φ g) : F) *
            (d.lowerCharacter (φ g) : F) := by
        change (algebraMap 𝒪[F] F)
          ((u₁ (φ g) : 𝒪[F]) * (u₂ (φ g) : 𝒪[F])) = _
        rw [map_mul, h₁F, h₂F]
      _ = LinearMap.det
          ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ (φ g)) :=
        d.upper_mul_lower_eq_det p hp ξ (φ g)
      _ = LinearMap.det (ρ (g : AbsoluteGalois (realCyclotomicField p))) :=
        hfield g
      _ = ((LinearMap.det (D.integralAction
          (g : AbsoluteGalois (realCyclotomicField p))) : 𝒪[F]) : F) :=
        (primePlusResidualData_det_integral_spec p ρ D _).symm
  have hprod : Units.map q.toMonoidHom (u₁ (φ g)) *
      Units.map q.toMonoidHom (u₂ (φ g)) =
      D.chi₁ (g : AbsoluteGalois (realCyclotomicField p)) *
        D.chi₂ (g : AbsoluteGalois (realCyclotomicField p)) := by
    apply Units.ext
    change q ((u₁ (φ g) : 𝒪[F]) * (u₂ (φ g) : 𝒪[F])) =
      (D.chi₁ (g : AbsoluteGalois (realCyclotomicField p)) : 𝒪[F] ⧸ 𝓂[F]) *
        (D.chi₂ (g : AbsoluteGalois (realCyclotomicField p)) : 𝒪[F] ⧸ 𝓂[F])
    rw [hint]
    exact D.residual_det (g : AbsoluteGalois (realCyclotomicField p))
  have hlow : Units.map q.toMonoidHom (u₂ (φ g)) =
      D.chi₂ (g : AbsoluteGalois (realCyclotomicField p)) := hlower g
  rw [hlow] at hprod
  exact mul_right_cancel hprod

/-- The actual complementary-cusp ordinary basis also has the upper
residual character of the swapped selected native datum. The calculation
uses its exact lower character and the determinant of the same selected
Tate action; no separate residual ordering is assumed. -/
theorem primePlusRaynaudCubicDifference_upperResidual_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1)
    (hdeep : (p : ℤ) ^ 3 ∣ ((B : ℤ) - A))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[RealPrimePowerCompletion p 0] ⧸
        𝓂[RealPrimePowerCompletion p 0]))
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) :
    let d := primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀
      hξ hB hAB hdeep
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸
            𝓂[RealPrimePowerCompletion p 0])).comp
      (IsNonarchimedeanLocalField.integerCharacter
        (RealPrimePowerCompletion p 0)
        d.upperCharacter d.upper_continuous)) (φ g) =
      (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ).swap.chi₁
        (g : AbsoluteGalois (realCyclotomicField p)) := by
  let ξ := darmonRationalParameter p ξ₀
  let d := primePlusRaynaudCubicDifferenceOrdinaryData p hp ξ₀ hξ hB hAB hdeep
  let ρ := primePlusTateFieldCoordinateAction p hp ξ β
  let D := (C.selectedResidualData p hp ξ β κ).swap
  exact upperResidual_eq_of_det_and_lower p hp ξ 1 (Nat.coprime_one_left _) d
    ρ D Q φ
    (fun t => primePlusLabelledLocalDet_eq_nativeGlobal_of_conjugacy
      p hp ξ β C 1 (Nat.coprime_one_left _) Q σ φ hφ t)
    (fun t => primePlusRaynaudCubicDifference_lowerResidual_eq p hp ξ₀
      hξ hB hAB hdeep β κ C Q σ φ hφ t) g

end HilbertModularity.Hypergeometric
