/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricFamily
public import HilbertModularity.Geometry.GroupScheme.FiberCoefficients
public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicDual
public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicResidual

/-! # The actual canonical-prime torsion of the chosen Darmon family

All objects use the same chosen family and its actual integral endomorphism
action. Multiplication geometry is inherited from that family. Canonical-prime
Tate reduction is identified with its actual scheme-kernel points, and integral
dual reduction with the actual kernel dual. The named Darmon existence input
remains a later-batch dependency; arithmetic determinant and fixed-point
existence are not proved here. See [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The actual nonsingular parameter fibre of the one chosen prime-conductor family. -/
def darmonPrimeFiber : CommGrp (Over (Spec (CommRingCat.of (realCyclotomicField p)))) :=
  parameterFiber (realCyclotomicField p) (darmonFamily p hp) ξ

/-- Integral real multiplication on this fibre is pulled back from the same chosen family. -/
def darmonPrimeFiberRealMultiplication :
    𝓞 (realCyclotomicField p) →+* End (darmonPrimeFiber p hp ξ) :=
  (fiberEndomorphismMap (realCyclotomicField p) (darmonFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).comp
      (darmonRealMultiplication p hp)

/-- The actual canonical-prime torsion group scheme of the chosen fibre. -/
def darmonPrimeKernel : CommGrp (Over (Spec (CommRingCat.of (realCyclotomicField p)))) :=
  CommGrp.pullbackKernel (darmonPrimeFiberRealMultiplication p hp ξ (realPrimeGenerator p))

instance darmonPrimeFiber_isProper : IsProper (darmonPrimeFiber p hp ξ).X.hom :=
  fiber_isProper (realCyclotomicField p) (darmonFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)

instance darmonPrimeFiber_multiplication_isFinite (n : ℕ) [NeZero n] :
    IsFinite (multiplicationMap (realCyclotomicField p) (darmonPrimeFiber p hp ξ).X n).left :=
  fiber_multiplication_isFinite (realCyclotomicField p) (darmonFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) n

instance darmonPrimeFiber_multiplication_etale (n : ℕ) [NeZero n] :
    Etale (multiplicationMap (realCyclotomicField p) (darmonPrimeFiber p hp ξ).X n).left :=
  fiber_multiplication_etale (realCyclotomicField p) (darmonFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) n

instance darmonPrimeFiber_multiplication_surjective (n : ℕ) [NeZero n] :
    Surjective (multiplicationMap (realCyclotomicField p) (darmonPrimeFiber p hp ξ).X n).left :=
  fiber_multiplication_surjective (realCyclotomicField p) (darmonFamily p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) n

local notation "Fₚ" => realCyclotomicField p
local notation "Rₚ" => 𝓞 Fₚ
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "Sₚ" => AdicCompletion Pₚ Rₚ
local notation "kₚ" => Rₚ ⧸ Pₚ

/-- The actual chosen canonical-prime kernel is finite. -/
instance darmonPrimeKernel_isFinite : IsFinite (darmonPrimeKernel p hp ξ).X.hom := by
  have : IsFinite (p • 𝟙 (darmonPrimeFiber p hp ξ)).hom.hom.hom.left := by
    rw [← multiplicationMap_eq_nsmul]
    infer_instance
  exact coefficientKernel_isFinite (darmonPrimeFiber p hp ξ) Rₚ
    (darmonPrimeFiberRealMultiplication p hp ξ) p (realPrimeGenerator p)
    (realPrimeCofactor p (by omega)) (realPrimeGenerator_mul_cofactor p (by omega))

/-- The actual chosen canonical-prime kernel is étale. -/
instance darmonPrimeKernel_etale : Etale (darmonPrimeKernel p hp ξ).X.hom := by
  have : IsFinite (p • 𝟙 (darmonPrimeFiber p hp ξ)).hom.hom.hom.left := by
    rw [← multiplicationMap_eq_nsmul]
    infer_instance
  have : Etale (p • 𝟙 (darmonPrimeFiber p hp ξ)).hom.hom.hom.left := by
    rw [← multiplicationMap_eq_nsmul]
    infer_instance
  exact coefficientKernel_etale (darmonPrimeFiber p hp ξ) Rₚ
    (darmonPrimeFiberRealMultiplication p hp ξ) p (realPrimeGenerator p)
    (realPrimeCofactor p (by omega)) (realPrimeGenerator_mul_cofactor p (by omega))

/-- The actual chosen kernel points carry the canonical residue coefficient action. -/
@[instance_reducible]
def darmonPrimeKernelModule :
    Module kₚ (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X) :=
  coefficientKernelModule Fₚ (darmonPrimeFiber p hp ξ) Rₚ
    (darmonPrimeFiberRealMultiplication p hp ξ) (realPrimeGenerator p)

/-- The residual action is the actual Galois action on the chosen scheme-kernel points. -/
def darmonPrimeKernelRepresentation :
    letI := darmonPrimeKernelModule p hp ξ
    Representation kₚ (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
      (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X) :=
  coefficientKernelRepresentation Fₚ (darmonPrimeFiber p hp ξ) Rₚ
    (darmonPrimeFiberRealMultiplication p hp ξ) (realPrimeGenerator p)

/-- The canonical completed coefficient ring acts on the actual chosen fibre's integral Tate module. -/
@[instance_reducible]
def darmonPrimeIntegralTateModule : Module Sₚ (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p) :=
  realPrimeIntegralTateModule Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ)

/-- The actual completed canonical-prime Tate representation of the chosen fibre. -/
def darmonPrimeIntegralTateRepresentation :
    letI := darmonPrimeIntegralTateModule p hp ξ
    Representation Sₚ (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
      (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p) :=
  realPrimeIntegralTateRepresentation Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ)

/-- This actual chosen-fibre lattice is finite over the canonical completed coefficient ring. -/
theorem darmonPrimeIntegralTate_finite :
    letI := darmonPrimeIntegralTateModule p hp ξ
    Module.Finite Sₚ (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p) :=
  realPrimeIntegralTate_finite Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ)

/-- This actual chosen-fibre lattice is free over the canonical completed coefficient ring. -/
theorem darmonPrimeIntegralTate_free :
    letI := darmonPrimeIntegralTateModule p hp ξ
    Module.Free Sₚ (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p) :=
  realPrimeIntegralTate_free Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ)

/-- Actual canonical-prime Tate reduction is the actual chosen scheme-kernel point representation. -/
def darmonPrimeResidualKernelEquiv :
    letI := darmonPrimeIntegralTateModule p hp ξ
    letI := darmonPrimeKernelModule p hp ξ
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange kₚ).Equiv
      (darmonPrimeKernelRepresentation p hp ξ) :=
  realPrimeResidualKernelEquiv Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ)

/-- The actual chosen-fibre integral dual reduces to the actual canonical-prime kernel dual. -/
def darmonPrimeResidualDualKernelEquiv :
    letI := darmonPrimeIntegralTateModule p hp ξ
    letI := darmonPrimeKernelModule p hp ξ
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    ((darmonPrimeIntegralTateRepresentation p hp ξ).dual.baseChange kₚ).Equiv
      (darmonPrimeKernelRepresentation p hp ξ).dual :=
  realPrimeResidualDualKernelEquiv Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ)

/-- The actual chosen residual determinant is reduction of the determinant on its actual lattice. -/
theorem det_darmonPrimeKernel (g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) :
    letI := darmonPrimeIntegralTateModule p hp ξ
    letI := darmonPrimeKernelModule p hp ξ
    LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g) =
      AdicCompletion.evalOneₐ Pₚ
        (LinearMap.det (darmonPrimeIntegralTateRepresentation p hp ξ g)) :=
  det_realPrimeKernel Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ) g

/-- An exact arithmetic determinant on this chosen fraction-field factor gives the native residual cyclotomic determinant on this chosen kernel. -/
theorem det_darmonPrimeKernel_eq_cyclotomic
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
    (hd : letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := darmonPrimeKernelModule p hp ξ
    realPrimeResidueEquiv p (by omega)
      (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g)) =
        (Field.cyclotomicCharacter Fₚ p g : ℤ_[p]).toZMod :=
  det_realPrimeKernel_eq_cyclotomic Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ) L g hd

/-- The actual chosen kernel has trivial and native cyclotomic factors once its fixed-point, rank and determinant inputs hold. -/
theorem exists_darmonPrimeKernel_factors
    (v : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X) (hv : v ≠ 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • v = v)
    (hrank : letI := realPrimeGenerator_isMaximal p (by omega)
      letI := Ideal.Quotient.field Pₚ
      letI := darmonPrimeKernelModule p hp ξ
      Module.finrank kₚ (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X) = 2)
    (hdet : letI := darmonPrimeKernelModule p hp ξ
      ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
        realPrimeResidueEquiv p (by omega)
          (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g)) =
            (Field.cyclotomicCharacter Fₚ p g : ℤ_[p]).toZMod) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    let ρ := darmonPrimeKernelRepresentation p hp ξ
    ∃ T : Subrepresentation ρ,
      Module.finrank kₚ T.toSubmodule = 1 ∧
      Module.finrank kₚ (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X
        ⧸ T.toSubmodule) = 1 ∧
      T.toRepresentation.IsIrreducible ∧
      (ρ.quotient T.toSubmodule T.apply_mem_toSubmodule).IsIrreducible ∧
      Nonempty ((T.toRepresentation.prod
        (ρ.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)).prod
              (Representation.ofCharacter (K := kₚ)
                (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))))) :=
  exists_realPrimeKernel_factors Fₚ p (by omega) (darmonPrimeFiber p hp ξ)
    (darmonPrimeFiberRealMultiplication p hp ξ) v hv hfix hrank hdet

end HilbertModularity.Hypergeometric
