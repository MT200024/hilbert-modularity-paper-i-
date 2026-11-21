/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimePlusRaynaudStableApplication
public import HilbertModularity.Hypergeometric.PrimePlusNativeChecklist

/-! # Residual ordering for the selected Raynaud ordinary quotient

The split period quotient fixes the lower character of one chosen ordinary
basis. The canonical-prime torsion point fixes the second character of the
same selected Jacobian's native residual datum. These two facts give the
lower residual equality in the local Skinner–Wiles checklist.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.GroupScheme ValuativeRel
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower primePlusConjugateRationalModule
  primePlusConjugateScalarTower

local instance primePlusRaynaudResidualGalCompact (p : ℕ) [Fact p.Prime] :
    CompactSpace (Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) := by
  let : IsGalois (RealPrimePowerCompletion p 0) (PadicAlgCl p) :=
    IsGalois.tower_top_of_isGalois ℚ_[p]
      (RealPrimePowerCompletion p 0) (PadicAlgCl p)
  infer_instance

/-- Coefficient conjugation fixes the rational `p`-adic cyclotomic
determinant of the selected native local Tate action. -/
theorem primePlusDecompositionScalarConjugate_det_eq_cyclotomic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) :
    LinearMap.det ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p
          (primePlusLocalGaloisRestriction p g) : ℤ_[p]) : ℚ_[p]) := by
  let : Module.Finite (RealPrimePowerCompletion p 0)
      (primePlusDecompositionRepresentation p hp ξ) :=
    Module.finite_of_finrank_eq_succ (by
      simpa using finrank_primePlusDecompositionRepresentation p hp ξ)
  let σ := realPrimePowerCompletionAutomorphism p 0 m hm
  have hconj := Rep.det_scalarConjugate σ.toRingEquiv
    (primePlusDecompositionRepresentation p hp ξ) g
  change LinearMap.det ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ g) =
    σ (LinearMap.det ((primePlusDecompositionRepresentation p hp ξ).ρ g)) at hconj
  rw [hconj]
  have hbase : LinearMap.det ((primePlusDecompositionRepresentation p hp ξ).ρ g) =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p
          (primePlusLocalGaloisRestriction p g) : ℤ_[p]) : ℚ_[p]) := by
    change LinearMap.det ((primePlusLocalTateRepresentation p hp ξ).ρ
      (primePlusLocalGaloisRestriction p g)) = _
    exact primePlusLocalTateRepresentation_det p hp ξ
      (primePlusLocalGaloisRestriction p g)
  rw [hbase]
  exact σ.commutes _

/-- In the actual selected zero-cusp basis, the upper field character is
the cyclotomic determinant evaluated through the chosen local restriction. -/
theorem primePlusRaynaudCubicNumerator_upperCharacter_eq_cyclotomic
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) :
    ((primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
      hξ hA hB hAB hdeep m hm).upperCharacter g : RealPrimePowerCompletion p 0) =
    algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
      ((Field.cyclotomicCharacter (realCyclotomicField p) p
        (primePlusLocalGaloisRestriction p g) : ℤ_[p]) : ℚ_[p]) := by
  let d := primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
    hξ hA hB hAB hdeep m hm
  exact (d.upperCharacter_eq_det_of_lowerOne p hp
    (darmonRationalParameter p ξ₀)
    (primePlusRaynaudCubicNumeratorOrdinaryData_lowerCharacter_eq_one
      p hp ξ₀ hξ hA hB hAB hdeep m hm) g).trans
    (primePlusDecompositionScalarConjugate_det_eq_cyclotomic p hp
      (darmonRationalParameter p ξ₀) m hm g)

/-- The integral action stored in a selected residual datum has the same
determinant over the coefficient field as its chosen global representation. -/
theorem primePlusResidualData_det_integral_spec
    (p : ℕ) [Fact p.Prime]
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ)
    (g : AbsoluteGalois (realCyclotomicField p)) :
    ((LinearMap.det (D.integralAction g) :
      𝒪[RealPrimePowerCompletion p 0]) : RealPrimePowerCompletion p 0) =
      LinearMap.det (ρ g) := by
  let q : 𝒪[RealPrimePowerCompletion p 0] →+*
      RealPrimePowerCompletion p 0 := algebraMap _ _
  let M := LinearMap.toMatrix' (D.integralAction g)
  have hq (x : 𝒪[RealPrimePowerCompletion p 0]) :
      q x = (x : RealPrimePowerCompletion p 0) := rfl
  have hmat : M.map q = LinearMap.toMatrix' (ρ g) := by
    apply Matrix.ext
    intro i j
    simpa [M, hq, LinearMap.toMatrix'_apply] using
      D.integral_spec g i j
  calc
    ((LinearMap.det (D.integralAction g) :
        𝒪[RealPrimePowerCompletion p 0]) : RealPrimePowerCompletion p 0) =
        q M.det := by rw [← LinearMap.det_toMatrix']; rfl
    _ = (M.map q).det := q.map_det M
    _ = LinearMap.det (ρ g) := by
      rw [hmat]
      exact LinearMap.det_toMatrix' _

/-- Field equality of an upper ordinary character with the determinant of
the same global integral representation implies its required residual
equality when the selected second residual character is trivial. -/
theorem upperResidual_eq_of_upperFieldDet
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (d : PrimePlusNormalizedOrdinaryData p hp ξ m hm)
    (ρ : Representation (RealPrimePowerCompletion p 0)
      (AbsoluteGalois (realCyclotomicField p))
      (Fin 2 → RealPrimePowerCompletion p 0))
    (D : SkinnerWilesResidualData ρ) (hchi₂ : D.chi₂ = 1)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hfield : ∀ g : primeDecompositionGroup Q,
      (d.upperCharacter (φ g) : RealPrimePowerCompletion p 0) =
        LinearMap.det (ρ (g : AbsoluteGalois (realCyclotomicField p))))
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
  let χ := IsNonarchimedeanLocalField.integerCharacter F
    d.upperCharacter d.upper_continuous
  have hint : (χ (φ g) : 𝒪[F]) =
      LinearMap.det (D.integralAction
        (g : AbsoluteGalois (realCyclotomicField p))) := by
    apply IsFractionRing.injective 𝒪[F] F
    calc
      (((χ (φ g) : 𝒪[F]) : F)) = (d.upperCharacter (φ g) : F) := rfl
      _ = LinearMap.det (ρ (g : AbsoluteGalois (realCyclotomicField p))) :=
        hfield g
      _ = ((LinearMap.det (D.integralAction
          (g : AbsoluteGalois (realCyclotomicField p))) : 𝒪[F]) : F) :=
        (primePlusResidualData_det_integral_spec p ρ D _).symm
  have hchi₂g : D.chi₂ (g : AbsoluteGalois (realCyclotomicField p)) = 1 :=
    congrArg (fun f : AbsoluteGalois (realCyclotomicField p) →*
      (𝒪[F] ⧸ 𝓂[F])ˣ => f (g : AbsoluteGalois (realCyclotomicField p))) hchi₂
  have hdetRed : Ideal.Quotient.mk (𝓂[F])
      (LinearMap.det (D.integralAction
        (g : AbsoluteGalois (realCyclotomicField p)))) =
      (D.chi₁ (g : AbsoluteGalois (realCyclotomicField p)) : 𝒪[F] ⧸ 𝓂[F]) := by
    simpa only [hchi₂g, Units.val_one, mul_one] using
      D.residual_det (g : AbsoluteGalois (realCyclotomicField p))
  apply Units.ext
  change Ideal.Quotient.mk (𝓂[F]) (χ (φ g) : 𝒪[F]) =
    (D.chi₁ (g : AbsoluteGalois (realCyclotomicField p)) : 𝒪[F] ⧸ 𝓂[F])
  exact congrArg (Ideal.Quotient.mk (𝓂[F])) hint |>.trans hdetRed

/-- After the necessary conjugation of a prime above `p`, the upper Raynaud
character equals the determinant of the same selected global Tate action.
Cyclotomic character values are invariant under that conjugation. -/
theorem primePlusRaynaudCubicNumerator_upperFieldDet_eq_nativeGlobal
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (C : PrimePlusNativeTateComparison p hp (darmonRationalParameter p ξ₀)
      (RealPrimePowerCompletion p 0) β)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) :
    ((primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
      hξ hA hB hAB hdeep m hm).upperCharacter (φ g) :
        RealPrimePowerCompletion p 0) =
      LinearMap.det (primePlusTateFieldCoordinateAction p hp
        (darmonRationalParameter p ξ₀) β
        (g : AbsoluteGalois (realCyclotomicField p))) := by
  have hχ : (Field.cyclotomicCharacter (realCyclotomicField p) p
      (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹) : ℤ_[p]) =
      (Field.cyclotomicCharacter (realCyclotomicField p) p
        (g : AbsoluteGalois (realCyclotomicField p)) : ℤ_[p]) := by
    simp [map_mul, mul_assoc]
  calc
    _ = algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p
          (primePlusLocalGaloisRestriction p (φ g)) : ℤ_[p]) : ℚ_[p]) :=
      primePlusRaynaudCubicNumerator_upperCharacter_eq_cyclotomic p hp ξ₀
        hξ hA hB hAB hdeep m hm (φ g)
    _ = algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p
          (g : AbsoluteGalois (realCyclotomicField p)) : ℤ_[p]) : ℚ_[p]) := by
      rw [hφ g, hχ]
    _ = _ := (C.selectedFieldCoordinate_det p hp
      (darmonRationalParameter p ξ₀) β
      (g : AbsoluteGalois (realCyclotomicField p))).symm

/-- At any selected fibre and RM label, the local Tate determinant agrees
with the same native global field-coordinate determinant after conjugating
the decomposition prime. -/
theorem primePlusLabelledLocalDet_eq_nativeGlobal_of_conjugacy
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) (RealPrimePowerCompletion p 0)]
    (β : AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p)) →+* 𝒪[RealPrimePowerCompletion p 0])
    (C : PrimePlusNativeTateComparison p hp ξ (RealPrimePowerCompletion p 0) β)
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) :
    LinearMap.det ((primePlusDecompositionScalarConjugate p hp ξ m hm).ρ (φ g)) =
      LinearMap.det (primePlusTateFieldCoordinateAction p hp ξ β
        (g : AbsoluteGalois (realCyclotomicField p))) := by
  have hχ : (Field.cyclotomicCharacter (realCyclotomicField p) p
      (σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹) : ℤ_[p]) =
      (Field.cyclotomicCharacter (realCyclotomicField p) p
        (g : AbsoluteGalois (realCyclotomicField p)) : ℤ_[p]) := by
    simp [map_mul, mul_assoc]
  calc
    _ = algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p
          (primePlusLocalGaloisRestriction p (φ g)) : ℤ_[p]) : ℚ_[p]) :=
      primePlusDecompositionScalarConjugate_det_eq_cyclotomic
        p hp ξ m hm (φ g)
    _ = algebraMap ℚ_[p] (RealPrimePowerCompletion p 0)
        ((Field.cyclotomicCharacter (realCyclotomicField p) p
          (g : AbsoluteGalois (realCyclotomicField p)) : ℤ_[p]) : ℚ_[p]) := by
      rw [hφ g, hχ]
    _ = _ := (C.selectedFieldCoordinate_det p hp ξ β
      (g : AbsoluteGalois (realCyclotomicField p))).symm

/-- The actual zero-cusp Raynaud basis has the selected native upper residual
character after the prime's necessary conjugation. The equality follows from
the exact determinant on the same integral Tate lattice, with `chi₂ = 1`
already proved from the canonical-prime fixed torsion line. -/
theorem primePlusRaynaudCubicNumerator_upperResidual_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
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
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (σ : AbsoluteGalois (realCyclotomicField p))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (hφ : ∀ g : primeDecompositionGroup Q,
      primePlusLocalGaloisRestriction p (φ g) =
        σ * (g : AbsoluteGalois (realCyclotomicField p)) * σ⁻¹)
    (g : primeDecompositionGroup Q) :
    let d := primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
      hξ hA hB hAB hdeep m hm
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸
            𝓂[RealPrimePowerCompletion p 0])).comp
      (IsNonarchimedeanLocalField.integerCharacter
        (RealPrimePowerCompletion p 0)
        d.upperCharacter d.upper_continuous)) (φ g) =
    (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ).chi₁
      (g : AbsoluteGalois (realCyclotomicField p)) := by
  let d := primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
    hξ hA hB hAB hdeep m hm
  exact upperResidual_eq_of_upperFieldDet p hp
    (darmonRationalParameter p ξ₀) m hm d
    (primePlusTateFieldCoordinateAction p hp (darmonRationalParameter p ξ₀) β)
    (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ)
    (C.selectedResidualData_chi₂_eq_one p hp
      (darmonRationalParameter p ξ₀) β κ) Q φ
    (fun g => primePlusRaynaudCubicNumerator_upperFieldDet_eq_nativeGlobal
      p hp ξ₀ hξ hA hB hAB hdeep β C m hm Q σ φ hφ g) g

/-- The actual zero-cusp Raynaud basis and selected native residual datum have
the same lower residual character on every supplied decomposition map. The
map itself is constructed by the separate local/global Galois comparison. -/
theorem primePlusRaynaudCubicNumerator_lowerResidual_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ₀ : ProjectiveLine.Parameter ℚ) {A : ℤ} {B : ℕ}
    (hξ : ξ₀.val = (A : ℚ) / B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Int.gcd A B = 1) (hdeep : (p : ℤ) ^ 3 ∣ A)
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
    (m : ℕ) (hm : m.Coprime (p ^ (0 + 1)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    (φ : primeDecompositionGroup Q →*
      Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (g : primeDecompositionGroup Q) :
    let d := primePlusRaynaudCubicNumeratorOrdinaryData p hp ξ₀
      hξ hA hB hAB hdeep m hm
    ((Units.map (Ideal.Quotient.mk 𝓂[RealPrimePowerCompletion p 0] :
        𝒪[RealPrimePowerCompletion p 0] →*
          𝒪[RealPrimePowerCompletion p 0] ⧸
            𝓂[RealPrimePowerCompletion p 0])).comp
      (Representation.determinantCharacter d.lattice.toRepresentation)) (φ g) =
    (C.selectedResidualData p hp (darmonRationalParameter p ξ₀) β κ).chi₂
      (g : AbsoluteGalois (realCyclotomicField p)) := by
  exact C.lowerResidual_eq_of_lowerOne p hp (darmonRationalParameter p ξ₀)
    β κ m hm _
    (primePlusRaynaudCubicNumeratorOrdinaryData_lowerCharacter_eq_one
      p hp ξ₀ hξ hA hB hAB hdeep m hm) Q φ g

end HilbertModularity.Hypergeometric
