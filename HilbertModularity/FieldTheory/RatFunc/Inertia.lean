/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Inertia above finite points of the rational function field

The prime at a finite coordinate is the kernel of polynomial evaluation.
A prime above it is chosen in the actual integral closure of the polynomial
ring in a fixed algebraic closure of its fraction field. Its inertia group is
the native group of automorphisms trivial on that residue field.
-/

@[expose] public noncomputable section
namespace RatFunc
universe u
variable (K : Type u) [Field K]

/-- The finite affine prime defined by evaluation at the specified coordinate. -/
def affinePrime (a : K) : Ideal (Polynomial K) := RingHom.ker (Polynomial.evalRingHom a)

/-- The finite-coordinate prime is maximal because polynomial evaluation reaches the field. -/
instance affinePrime_isMaximal (a : K) : (affinePrime K a).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom a)
    (fun c => ⟨Polynomial.C c, Polynomial.eval_C⟩)

/-- The actual normalization of the affine coordinate ring in the chosen algebraic closure. -/
abbrev affineIntegralClosure := integralClosure (Polynomial K) (AlgebraicClosure (RatFunc K))

/-- Polynomial coordinates embed faithfully into their actual algebraic normalization. -/
instance affineIntegralClosure_faithfulSMul : FaithfulSMul (Polynomial K) (affineIntegralClosure K) := by
  apply (faithfulSMul_iff_algebraMap_injective (Polynomial K) (affineIntegralClosure K)).mpr
  intro f g h
  have hv := congrArg (fun z : affineIntegralClosure K => (z : AlgebraicClosure (RatFunc K))) h
  change algebraMap (Polynomial K) (AlgebraicClosure (RatFunc K)) f =
    algebraMap (Polynomial K) (AlgebraicClosure (RatFunc K)) g at hv
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  apply (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K))).injective
  simpa only [IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K)
    (AlgebraicClosure (RatFunc K))] using hv

/-- Every finite coordinate has a prime in the actual algebraic normalization above it. -/
theorem exists_affinePrimeAbove (a : K) :
    ∃ P : Ideal (affineIntegralClosure K), P.IsMaximal ∧ P.LiesOver (affinePrime K a) :=
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral (affinePrime K a)

/-- A choice of a prime above the finite coordinate in the fixed algebraic closure. -/
def affinePrimeAbove (a : K) : Ideal (affineIntegralClosure K) :=
  Classical.choose (exists_affinePrimeAbove K a)

instance affinePrimeAbove_isMaximal (a : K) : (affinePrimeAbove K a).IsMaximal :=
  (Classical.choose_spec (exists_affinePrimeAbove K a)).1

instance affinePrimeAbove_liesOver (a : K) :
    (affinePrimeAbove K a).LiesOver (affinePrime K a) :=
  (Classical.choose_spec (exists_affinePrimeAbove K a)).2

/-- Absolute rational-function automorphisms commute with the polynomial scalar action. -/
instance affineClosure_smulCommClass :
    SMulCommClass (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
      (Polynomial K) (AlgebraicClosure (RatFunc K)) where
  smul_comm g f z := by
    simpa only [AlgEquiv.smul_def, AlgEquiv.coe_toLinearEquiv,
      AlgEquiv.restrictScalars_apply] using
      map_smul (g.restrictScalars (Polynomial K)).toLinearEquiv f z

/-- Actual inertia at the chosen prime above a finite coordinate of the rational function field. -/
def affineInertia (a : K) :
    Subgroup (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) :=
  Ideal.inertia _ (affinePrimeAbove K a)

/-- Inertia consists precisely of automorphisms acting trivially modulo the chosen prime. -/
theorem mem_affineInertia (a : K)
    (g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) :
    g ∈ affineInertia K a ↔ ∀ z : affineIntegralClosure K, g • z - z ∈ affinePrimeAbove K a :=
  Ideal.mem_inertia

end RatFunc
