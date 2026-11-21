/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicTorsion
public import HilbertModularity.RepresentationTheory.DualLattice

/-! # Duality at the actual canonical real-cyclotomic prime

The integral dual of the actual completed Tate lattice reduces to the dual
of the actual canonical-prime scheme kernel. Its evaluation pairing is the
residue of the integral pairing. This is the lattice comparison required by
[TripathiGoswami]; no etale-cohomology identification is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : CommGrp (Over (Spec (CommRingCat.of K))))
  (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
  (φ : 𝓞 (realCyclotomicField p) →+* End A)
  [IsFinite (multiplicationMap K A.X p).left]
  [Surjective (multiplicationMap K A.X p).left]

local notation "Rₚ" => 𝓞 (realCyclotomicField p)
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "Sₚ" => AdicCompletion Pₚ Rₚ
local notation "kₚ" => Rₚ ⧸ Pₚ

/-- The actual integral Tate dual reduces equivariantly to the actual canonical-prime kernel dual. -/
def realPrimeResidualDualKernelEquiv :
    letI := realPrimeIntegralTateModule K A p hp φ
    letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    ((realPrimeIntegralTateRepresentation K A p hp φ).dual.baseChange kₚ).Equiv
      (coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p)).dual := by
  letI := realPrimeIntegralTateModule K A p hp φ
  letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
  letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  haveI := realPrimeIntegralTate_finite K A p hp φ
  haveI := realPrimeIntegralTate_free K A p hp φ
  let E := realPrimeResidualKernelEquiv K A p hp φ
  let D : ((realPrimeIntegralTateRepresentation K A p hp φ).baseChange kₚ).dual.Equiv
      (coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p)).dual :=
    .mk E.toLinearEquiv.symm.dualMap (by
      intro g
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro x
      exact congrArg f (E.symm.toIntertwiningMap.isIntertwining _ _ g⁻¹ x).symm)
  exact (Representation.dualBaseChangeEquiv kₚ
    (realPrimeIntegralTateRepresentation K A p hp φ)).trans D

/-- Evaluation on actual reduced kernel points is reduction of the integral Tate pairing. -/
theorem realPrimeResidualDualKernelEquiv_tmul (c : kₚ)
    (f : letI := realPrimeIntegralTateModule K A p hp φ
      Module.Dual Sₚ (integralTate K A.X p)) (x : integralTate K A.X p) :
    let := realPrimeIntegralTateModule K A p hp φ
    let := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
    let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    realPrimeResidualDualKernelEquiv K A p hp φ (c ⊗ₜ[Sₚ] f)
      (realPrimeResidualKernelEquiv K A p hp φ ((1 : kₚ) ⊗ₜ[Sₚ] x)) =
        c * AdicCompletion.evalOneₐ Pₚ (f x) := by
  let := realPrimeIntegralTateModule K A p hp φ
  let := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
  let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  have := realPrimeIntegralTate_finite K A p hp φ
  have := realPrimeIntegralTate_free K A p hp φ
  change Representation.dualBaseChangeEquiv kₚ
    (realPrimeIntegralTateRepresentation K A p hp φ) (c ⊗ₜ[Sₚ] f)
    ((realPrimeResidualKernelEquiv K A p hp φ).symm
      (realPrimeResidualKernelEquiv K A p hp φ ((1 : kₚ) ⊗ₜ[Sₚ] x))) = _
  rw [Representation.Equiv.symm_apply_apply, Representation.dualBaseChangeEquiv_tmul]
  rfl

end AlgebraicGeometry.GroupScheme
