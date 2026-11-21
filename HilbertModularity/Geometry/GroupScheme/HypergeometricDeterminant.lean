/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricPrimeTorsion
public import HilbertModularity.LinearAlgebra.RankTwoTrace
public import HilbertModularity.RepresentationTheory.DeterminantRigidity

/-! # Determinant reduction on a chosen prime-conductor fibre

The canonical-prime kernel is the reduction of the integral Tate lattice of the
same chosen fibre.  This module records the determinant consequence of an exact
characteristic-zero identity on that lattice.  The identity itself still
requires the labelled auxiliary-system comparison in
[TripathiGoswamiRevised, Lemma `det-rigidity` and Lemma `RMtorsion`].
-/

public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField TensorProduct

namespace HilbertModularity

/-- The first two algebraic power traces determine the determinant of a labelled
rank-two Frobenius factor after any coefficient embedding. This is the linear
algebra step in [TripathiGoswamiRevised, Lemma `labelled-RM-compat`];
compatibility of the actual abelian-variety traces is a separate geometric
input. -/
theorem rankTwoDeterminant_of_compatiblePowerTraces
    {E L : Type*} [Field E] [Field L] [CharZero L]
    (ι : E →+* L) (M : Matrix (Fin 2) (Fin 2) L)
    (a b d : E) (htrace : M.trace = ι a)
    (htraceSq : (M ^ 2).trace = ι b)
    (hd : 2 * d = a ^ 2 - b) : M.det = ι d := by
  have hm := two_mul_det_eq_sq_trace_sub_trace_sq M
  rw [htrace, htraceSq] at hm
  have he : (2 : L) * ι d = (ι a) ^ 2 - ι b := by
    calc
      (2 : L) * ι d = ι (2 * d) := by simp only [map_mul, map_ofNat]
      _ = ι (a ^ 2 - b) := congrArg ι hd
      _ = (ι a) ^ 2 - ι b := by simp
  exact mul_left_cancel₀ (by norm_num : (2 : L) ≠ 0) (hm.trans he.symm)

end HilbertModularity

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

local notation "Fₚ" => realCyclotomicField p
local notation "Rₚ" => 𝓞 Fₚ
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "Sₚ" => AdicCompletion Pₚ Rₚ
local notation "kₚ" => Rₚ ⧸ Pₚ

local instance : Module Sₚ (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p) :=
  darmonPrimeIntegralTateModule p hp ξ

/-- Infinitely many auxiliary residual determinants determine the exact
determinant of the *chosen fibre's* completed Tate factor. The algebraic
Frobenius values, their compatibility with the same labelled auxiliary
factors, and the residual congruences are kept as explicit inputs. These are
the separate geometric and arithmetic assertions used in
[TripathiGoswamiRevised, Lemmas `labelled-RM-compat` and `det-rigidity`];
the auxiliary residual determinant is recorded in [DarmonMestre, Section 4,
printed p. 309]. -/
theorem darmonPrimeIntegralTate_determinant_of_auxiliaryCongruences
    (L : Type*) [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    [T2Space L] [Algebra Sₚ L] [IsFractionRing Sₚ L] [Algebra Fₚ L]
    {κ I J : Type*} [Fintype κ] [DecidableEq κ]
    [TopologicalSpace
      (L ⊗[Sₚ] (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p))]
    (b : letI := darmonPrimeIntegralTateModule p hp ξ
      Module.Basis κ L (L ⊗[Sₚ] (integralTate Fₚ (darmonPrimeFiber p hp ξ).X p)))
    (hb : ∀ k, Continuous (b.coord k))
    (hτ : letI := darmonPrimeIntegralTateModule p hp ξ
      ∀ w, Continuous (fun g =>
        (darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g w))
    (μ : (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →ₜ* Lˣ)
    (hμ : ∀ g,
      (μ g : L) = algebraMap Sₚ L
        (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p]))))
    (P : J → IsDedekindDomain.HeightOneSpectrum Rₚ) (V : J → Type*)
    [∀ j, AddCommGroup (V j)]
    [∀ j, Module ((P j).adicCompletion Fₚ) (V j)]
    [∀ j, Module ((P j).adicCompletionIntegers Fₚ) (V j)]
    [∀ j, IsScalarTower ((P j).adicCompletionIntegers Fₚ)
      ((P j).adicCompletion Fₚ) (V j)]
    (ρ : ∀ j, Representation ((P j).adicCompletion Fₚ)
      (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) (V j))
    (M : ∀ j, Subrepresentation
      ((ρ j).restrictScalars ((P j).adicCompletionIntegers Fₚ)))
    [∀ j, Submodule.IsLattice ((P j).adicCompletion Fₚ) (M j).toSubmodule]
    {ι : J → Type*}
    (a : ∀ j, Module.Basis (ι j) ((P j).adicCompletionIntegers Fₚ)
      (M j).toSubmodule)
    (t : I → AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
    (ht : DenseRange t) (x y : I → Fₚ)
    (hx : ∀ i,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L (t i)) =
        algebraMap Fₚ L (x i))
    (hy : ∀ i, (μ (t i) : L) = algebraMap Fₚ L (y i))
    (S : I → Set J)
    (hS : ∀ i, ((fun j => ringChar (Rₚ ⧸ (P j).asIdeal)) '' S i).Infinite)
    (haux : ∀ i j, j ∈ S i →
      LinearMap.det (ρ j (t i)) =
        algebraMap Fₚ ((P j).adicCompletion Fₚ) (x i))
    (hres : ∀ i j, j ∈ S i →
      ∀ hu : (P j).valuation Fₚ (y i) = 1,
      LinearMap.det (((M j).toRepresentation.baseChange
        (IsLocalRing.ResidueField ((P j).adicCompletionIntegers Fₚ))) (t i)) =
        (P j).completionResidueMap ((P j).specialization (y i) hu.le)) :
    letI := darmonPrimeIntegralTateModule p hp ξ
    ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p]))) := by
  have hdet := Representation.continuousDeterminantCharacter_eq_of_infinite_residual_congruences
    b hb ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L) hτ μ
    P V ρ M a t ht x y hx hy S hS haux hres
  intro g
  calc
    LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        (Representation.continuousDeterminantCharacter b hb
          ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L) hτ g : L) := by
            exact (Representation.continuousDeterminantCharacter_coe b hb
              ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L) hτ g).symm
    _ = (μ g : L) := congrArg Units.val (congrArg (fun f => f g) hdet)
    _ = _ := hμ g

/-- Exact determinant equality on the actual chosen integral Tate factor
reduces to the cyclotomic determinant on its actual canonical-prime kernel. -/
theorem darmonPrimeResidualDeterminant_of_integralTate
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := darmonPrimeKernelModule p hp ξ
    ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      realPrimeResidueEquiv p (by omega)
        (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g)) =
          (Field.cyclotomicCharacter Fₚ p g : ℤ_[p]).toZMod := by
  have := darmonPrimeKernelModule p hp ξ
  intro g
  exact det_darmonPrimeKernel_eq_cyclotomic p hp ξ L g (hdet g)

/-- The determinant character of the actual residual Galois representation,
under the exact Tate determinant input, is the native cyclotomic character. -/
theorem darmonPrimeResidualDeterminantCharacter_of_integralTate
    (L : Type*) [Field L] [Algebra Sₚ L] [IsFractionRing Sₚ L]
    (hdet : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Fₚ p g : ℤ_[p])))) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := darmonPrimeKernelModule p hp ξ
    (darmonPrimeKernelRepresentation p hp ξ).determinantCharacter =
      realPrimeResidualCyclotomicCharacter Fₚ p (by omega) := by
  have := realPrimeGenerator_isMaximal p (by omega)
  have := Ideal.Quotient.field Pₚ
  have := darmonPrimeKernelModule p hp ξ
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply (realPrimeResidueEquiv p (by omega)).injective
  exact (darmonPrimeResidualDeterminant_of_integralTate p hp ξ L hdet g).trans
    (realPrimeResidualCyclotomicCharacter_residue Fₚ p (by omega) g).symm

end HilbertModularity.Hypergeometric
