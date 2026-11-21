/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricPrimeKernelFamily
public import HilbertModularity.Geometry.GroupScheme.HypergeometricRanks
public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicRank

/-! # Rank two for canonical-prime torsion of the chosen Darmon family

The actual native rational Tate rank determines the integral coefficient rank
by comparing finite torsion cardinalities. Thus the chosen canonical-prime
kernel and its arithmetic local-system fibres have dimension two over their
actual residue field. We follow [TripathiGoswami, RM torsion lemma].
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

/-- The actual rational Tate dimension at every arithmetic fibre is twice the real coefficient degree. -/
theorem finrank_darmonRationalTate_at (p k : ℕ) [Fact p.Prime] (hN : 3 ≤ p ^ (k + 1))
    (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField (p ^ (k + 1)))) :
    Module.finrank ℚ_[p] (rationalTate K (fiber K (darmonFamily (p ^ (k + 1)) hN) x).X p) =
      Module.finrank ℚ (realCyclotomicField (p ^ (k + 1))) * 2 := by
  let V := localCoefficientTateRep K (darmonFamily (p ^ (k + 1)) hN) x p k
    (darmonRealMultiplication (p ^ (k + 1)) hN)
  let : Module ℚ_[p] V := localCoefficientTateRepRationalModule K _ x p k _
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k) V :=
    localCoefficientTateRepScalarTower K _ x p k _
  have hV : Module.finrank (RealPrimePowerCompletion p k) V = 2 :=
    finrank_darmonLocalTateRep_at p k hN K x
  have : Module.Finite (RealPrimePowerCompletion p k) V := Module.finite_of_finrank_eq_succ hV
  have hL : Module.finrank ℚ_[p] (RealPrimePowerCompletion p k) =
      Module.finrank ℚ (realCyclotomicField (p ^ (k + 1))) := by
    rw [← (realPrimePowerCompletionTensorEquiv p k).toLinearEquiv.finrank_eq,
      Module.finrank_baseChange]
  have h := Module.finrank_mul_finrank ℚ_[p] (RealPrimePowerCompletion p k) V
  rw [hL, hV] at h
  exact h.symm

variable (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

local notation "Fₚ" => realCyclotomicField p
local notation "Rₚ" => 𝓞 Fₚ
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "Sₚ" => AdicCompletion Pₚ Rₚ
local notation "kₚ" => Rₚ ⧸ Pₚ

/-- The actual canonical-prime kernel of every nonsingular chosen fibre is two-dimensional. -/
theorem finrank_darmonPrimeKernel :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    Module.finrank kₚ (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X) = 2 := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := darmonPrimeKernelModule p hp ξ
  have h (N : ℕ) [NeZero N] (hN : N = p ^ (0 + 1)) (hbound : 3 ≤ N)
      (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField N)) :
      Module.finrank ℚ_[p] (rationalTate K (fiber K (darmonFamily N hbound) x).X p) =
        Module.finrank ℚ (realCyclotomicField N) * 2 := by
    subst N
    with_reducible exact finrank_darmonRationalTate_at p 0 hbound K x
  have hT : Module.finrank ℚ_[p] (rationalTate Fₚ (darmonPrimeFiber p hp ξ).X p) =
      ((p - 1) / 2) * 2 := by
    unfold darmonPrimeFiber parameterFiber
    rw [← finrank_realCyclotomicField p (by omega)]
    with_reducible exact h p (by simp) hp Fₚ (ProjectiveLine.puncturedPoint Fₚ ξ)
  exact finrank_realPrimeKernel_of_rational_rank Fₚ (darmonPrimeFiber p hp ξ) p (by omega)
    (darmonPrimeFiberRealMultiplication p hp ξ) 2 hT

/-- The actual completed canonical-prime integral Tate lattice is free of rank two. -/
theorem finrank_darmonPrimeIntegralTate :
    letI := darmonPrimeIntegralTateModule p hp ξ
    Module.finrank Sₚ (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p) = 2 := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := darmonPrimeKernelModule p hp ξ
  let := darmonPrimeIntegralTateModule p hp ξ
  let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  have := darmonPrimeIntegralTate_free p hp ξ
  have := darmonPrimeIntegralTate_finite p hp ξ
  have := AdicCompletion.isDomain_of_isMaximal_span (realPrimeGenerator p)
    (realPrimeGenerator_ne_zero p (by omega))
  have h := (darmonPrimeResidualKernelEquiv p hp ξ).toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h
  exact h.trans (finrank_darmonPrimeKernel p hp ξ)

/-- Every arithmetic fibre of the actual canonical-prime kernel local system has rank two. -/
theorem finrank_darmonPrimeKernelLocalSystem :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    Module.finrank kₚ ((darmonPrimeKernelLocalSystem p hp).obj
      (ProjectiveLine.puncturedPoint Fₚ ξ)) = 2 := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := darmonPrimeKernelModule p hp ξ
  exact (darmonPrimeKernelLocalSystemRepresentationEquiv p hp ξ).toLinearEquiv.finrank_eq.trans
    (finrank_darmonPrimeKernel p hp ξ)

end HilbertModularity.Hypergeometric
