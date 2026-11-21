/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CoefficientFree
public import HilbertModularity.RepresentationTheory.PrimeTorsion
public import HilbertModularity.RepresentationTheory.DualLattice

/-! # Reduction of the actual integral RM-prime Tate dual

The proved finite free actual RM-prime lattice and its actual torsion
comparison identify the reduction of its integral dual with the dual of
actual coefficient torsion. The pairing has the canonical residue formula.
This supplies the covariant/dual convention in [TripathiGoswami], without
asserting an etale-cohomology comparison.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (R G A : Type*) [CommRing R] [IsDomain R] [Group G]
  [AddCommGroup A] [Module R A] [DistribMulAction G A] [SMulCommClass G R A]
  [Module.Finite ℤ_[p] (integral p A)]

/-- Reduction of the actual RM-prime integral dual is equivariantly the actual torsion contragredient. -/
def coefficientPrimeResidualDualEquiv (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] (hpdiv : Function.Surjective (fun x : A => p • x)) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    ((coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ).dual.baseChange
      (R ⧸ Ideal.span {a})).Equiv (principalTorsionRepresentation R G A a).dual := by
  letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
  haveI := coefficientPrime_finite p R A (Ideal.span {a}) e he hJ
  haveI := coefficientPrime_free_of_domain p R A a b ha hab e he hJ
  let E := coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv
  let D : (((coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ).baseChange
      (R ⧸ Ideal.span {a})).dual).Equiv (principalTorsionRepresentation R G A a).dual :=
    .mk E.toLinearEquiv.symm.dualMap (by
      intro g
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro x
      exact congrArg φ (E.symm.toIntertwiningMap.isIntertwining
        (principalTorsionRepresentation R G A a)
        ((coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ).baseChange
          (R ⧸ Ideal.span {a})) g⁻¹ x).symm)
  exact (Representation.dualBaseChangeEquiv (R ⧸ Ideal.span {a})
    (coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ)).trans D

/-- The actual RM-prime residual duality pairing is reduction of the integral lattice pairing. -/
theorem coefficientPrimeResidualDualEquiv_tmul
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] (hpdiv : Function.Surjective (fun x : A => p • x))
    (c : R ⧸ Ideal.span {a})
    (φ : letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
      Module.Dual (AdicCompletion (Ideal.span {a}) R) (integral p A))
    (x : integral p A) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    coefficientPrimeResidualDualEquiv p R G A a b ha hab e he hJ hpdiv
      (c ⊗ₜ[AdicCompletion (Ideal.span {a}) R] φ) (principalProjection p R A a b hab x) =
        c * AdicCompletion.evalOneₐ (Ideal.span {a}) (φ x) := by
  let := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  let := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
  have := coefficientPrime_finite p R A (Ideal.span {a}) e he hJ
  have := coefficientPrime_free_of_domain p R A a b ha hab e he hJ
  change Representation.dualBaseChangeEquiv (R ⧸ Ideal.span {a})
    (coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ)
    (c ⊗ₜ[AdicCompletion (Ideal.span {a}) R] φ)
    ((coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv).symm
      (principalProjection p R A a b hab x)) = _
  have hx : (coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv).symm
      (principalProjection p R A a b hab x) =
        (1 : R ⧸ Ideal.span {a}) ⊗ₜ[AdicCompletion (Ideal.span {a}) R] x := by
    apply (coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv).injective
    change coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv
      ((coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv).symm
        (principalProjection p R A a b hab x)) =
      coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv
        ((1 : R ⧸ Ideal.span {a}) ⊗ₜ[AdicCompletion (Ideal.span {a}) R] x)
    rw [Representation.Equiv.apply_symm_apply]
    change principalProjection p R A a b hab x =
      coefficientPrimeResidualEquiv p R A a b hab e he hJ hpdiv
        ((1 : R ⧸ Ideal.span {a}) ⊗ₜ[AdicCompletion (Ideal.span {a}) R] x)
    rw [coefficientPrimeResidualEquiv_tmul, one_smul]
  rw [hx, Representation.dualBaseChangeEquiv_tmul]
  rfl

end TateModule
