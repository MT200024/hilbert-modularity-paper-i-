/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.Inertia
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Galois conjugacy of inertia over finite rational-function primes

The integral closure of the polynomial ring has the original polynomial ring
as its Galois invariants. Profinite transitivity then identifies all primes
over the same finite coordinate, and their inertia groups are conjugate.
-/

@[expose] public noncomputable section
open scoped Pointwise
namespace RatFunc
universe u
variable (K : Type u) [Field K] [CharZero K]

/-- Galois invariants in the affine normalization are precisely the original polynomial coordinates. -/
instance affineIntegralClosure_isInvariant : Algebra.IsInvariant (Polynomial K)
    (affineIntegralClosure K)
      (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) where
  isInvariant b hb := by
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (K := AlgebraicClosure (RatFunc K)) (k := RatFunc K) (b : AlgebraicClosure (RatFunc K))).mpr
        (fun g => congrArg (fun z : affineIntegralClosure K =>
          (z : AlgebraicClosure (RatFunc K))) (hb g))
    have hi : IsIntegral (Polynomial K) a := by
      rw [← isIntegral_algebraMap_iff (B := AlgebraicClosure (RatFunc K)), ha]
      exact b.property
    obtain ⟨f, hf⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    refine ⟨f, Subtype.ext ?_⟩
    change algebraMap (Polynomial K) (AlgebraicClosure (RatFunc K)) f = b
    rw [IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K)
      (AlgebraicClosure (RatFunc K)), hf, ha]

/-- The absolute Galois action on the discrete affine normalization is continuous. -/
instance affineIntegralClosure_continuousSMul
    [TopologicalSpace (affineIntegralClosure K)] [DiscreteTopology (affineIntegralClosure K)] :
    ContinuousSMul (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
      (affineIntegralClosure K) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro z
  convert! stabilizer_isOpen_of_isIntegral (K := RatFunc K)
    (z : AlgebraicClosure (RatFunc K)) using 1
  ext g
  exact Subtype.ext_iff

/-- Any two primes of the algebraic normalization above the same coordinate prime are conjugate. -/
theorem exists_smul_affinePrime_of_under_eq
    (P Q : Ideal (affineIntegralClosure K)) [P.IsPrime] [Q.IsPrime]
    (h : P.under (Polynomial K) = Q.under (Polynomial K)) :
    ∃ g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K), Q = g • P := by
  let : TopologicalSpace (affineIntegralClosure K) := ⊥
  have : DiscreteTopology (affineIntegralClosure K) := ⟨rfl⟩
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := Polynomial K)
    (G := AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) P Q h

/-- The inertia group above a finite coordinate is independent of its chosen prime up to conjugacy. -/
theorem affineInertia_conjugate (a : K) (P : Ideal (affineIntegralClosure K))
    [P.IsPrime] [P.LiesOver (affinePrime K a)] :
    ∃ g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K),
      Ideal.inertia _ P = (affineInertia K a).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_smul_affinePrime_of_under_eq K (affinePrimeAbove K a) P
    (((affinePrimeAbove K a).over_def (affinePrime K a)).symm.trans
      (P.over_def (affinePrime K a)))
  refine ⟨g, ?_⟩
  rw [hg, Ideal.inertia_smul]
  rfl

end RatFunc
