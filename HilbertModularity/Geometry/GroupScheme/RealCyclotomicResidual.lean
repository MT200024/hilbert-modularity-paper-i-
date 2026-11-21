/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicTorsion
public import HilbertModularity.RepresentationTheory.FixedLine
public import HilbertModularity.RepresentationTheory.DualSubquotient

/-! # Character factors of actual canonical-prime kernel points

A nonzero fixed point on the actual coefficient kernel gives the trivial
constituent. In rank two the other constituent is the actual residual
cyclotomic character when the determinant has that value. The fixed point,
rank and arithmetic determinant are explicit inputs, not existence claims.
See [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)

local notation "Rₚ" => 𝓞 (realCyclotomicField p)
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "kₚ" => Rₚ ⧸ Pₚ


/-- The native mod-p cyclotomic character in the actual canonical coefficient residue field. -/
def realPrimeResidualCyclotomicCharacter :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kₚˣ :=
  (Units.map (((realPrimeResidueEquiv p hp).symm.toRingHom.comp
    (PadicInt.toZMod (p := p))).toMonoidHom)).comp (Field.cyclotomicCharacter K p).toMonoidHom

/-- The canonical residue identification sends this character to the native mod-p value. -/
@[simp]
theorem realPrimeResidualCyclotomicCharacter_residue
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    realPrimeResidueEquiv p hp (realPrimeResidualCyclotomicCharacter K p hp g : kₚ) =
      (Field.cyclotomicCharacter K p g : ℤ_[p]).toZMod :=
  (realPrimeResidueEquiv p hp).apply_symm_apply _

variable (A : CommGrp (Over (Spec (CommRingCat.of K))))
  (φ : 𝓞 (realCyclotomicField p) →+* End A)

/-- Actual rank-two canonical-prime kernel points have trivial and cyclotomic irreducible factors when their fixed point and determinant inputs hold. -/
theorem exists_realPrimeKernel_factors
    (v : (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X)) (hv : v ≠ 0)
    (hfix : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • v = v)
    (hrank : letI := realPrimeGenerator_isMaximal p hp
      letI := Ideal.Quotient.field Pₚ
      letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
      Module.finrank kₚ (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X) = 2)
    (hdet : letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        realPrimeResidueEquiv p hp
          (LinearMap.det (coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p) g)) =
            (Field.cyclotomicCharacter K p g : ℤ_[p]).toZMod) :
    letI := realPrimeGenerator_isMaximal p hp
    letI := Ideal.Quotient.field Pₚ
    letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
    let ρ := coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p)
    ∃ S : Subrepresentation ρ,
      Module.finrank kₚ S.toSubmodule = 1 ∧
      Module.finrank kₚ ((Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X) ⧸ S.toSubmodule) = 1 ∧
      S.toRepresentation.IsIrreducible ∧
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).IsIrreducible ∧
      Nonempty ((S.toRepresentation.prod
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kₚˣ)).prod
              (Representation.ofCharacter (K := kₚ) (realPrimeResidualCyclotomicCharacter K p hp)))) := by
  let := realPrimeGenerator_isMaximal p hp
  let := Ideal.Quotient.field Pₚ
  let := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
  let ρ := coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p)
  have := Module.finite_of_finrank_eq_succ hrank
  have hχ : ρ.determinantCharacter = realPrimeResidualCyclotomicCharacter K p hp := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply (realPrimeResidueEquiv p hp).injective
    exact (hdet g).trans (realPrimeResidualCyclotomicCharacter_residue K p hp g).symm
  simpa only [hχ] using ρ.exists_fixedLine_factors hrank v hv hfix

/-- The dual of the actual canonical-prime kernel has trivial and inverse-cyclotomic factors. -/
theorem exists_realPrimeKernel_dual_factors
    (v : (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X)) (hv : v ≠ 0)
    (hfix : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • v = v)
    (hrank : letI := realPrimeGenerator_isMaximal p hp
      letI := Ideal.Quotient.field Pₚ
      letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
      Module.finrank kₚ (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X) = 2)
    (hdet : letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        realPrimeResidueEquiv p hp
          (LinearMap.det (coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p) g)) =
            (Field.cyclotomicCharacter K p g : ℤ_[p]).toZMod) :
    letI := realPrimeGenerator_isMaximal p hp
    letI := Ideal.Quotient.field Pₚ
    letI := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
    let ρ := coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p)
    ∃ S : Subrepresentation ρ.dual,
      Module.finrank kₚ S.toSubmodule = 1 ∧
      Module.finrank kₚ (Module.Dual kₚ (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X) ⧸ S.toSubmodule) = 1 ∧
      Representation.IsIrreducible
        (k := kₚ)
        (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (V := S.toSubmodule)
        S.toRepresentation ∧
      Representation.IsIrreducible
        (k := kₚ)
        (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (V := (Module.Dual kₚ
          (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X))
            ⧸ S.toSubmodule)
        (ρ.dual.quotient S.toSubmodule S.apply_mem_toSubmodule) ∧
      Representation.IsSemisimpleRepresentation
        (k := kₚ)
        (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (V := S.toSubmodule × (Module.Dual
          kₚ
          (Points K (AlgebraicClosure K) (CommGrp.pullbackKernel (φ (realPrimeGenerator p))).X)
            ⧸ S.toSubmodule))
        (S.toRepresentation.prod
          (ρ.dual.quotient S.toSubmodule S.apply_mem_toSubmodule)) ∧
      Nonempty ((S.toRepresentation.prod
        (ρ.dual.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kₚˣ)).prod
              (Representation.ofCharacter (K := kₚ) (realPrimeResidualCyclotomicCharacter K p hp)⁻¹))) := by
  let := realPrimeGenerator_isMaximal p hp
  let := Ideal.Quotient.field Pₚ
  let := coefficientKernelModule K A Rₚ φ (realPrimeGenerator p)
  let ρ := coefficientKernelRepresentation K A Rₚ φ (realPrimeGenerator p)
  have := Module.finite_of_finrank_eq_succ hrank
  have hχ : ρ.determinantCharacter = realPrimeResidualCyclotomicCharacter K p hp := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply (realPrimeResidueEquiv p hp).injective
    exact (hdet g).trans (realPrimeResidualCyclotomicCharacter_residue K p hp g).symm
  simpa only [hχ] using ρ.exists_dual_fixedLine_factors hrank v hv hfix

end AlgebraicGeometry.GroupScheme
