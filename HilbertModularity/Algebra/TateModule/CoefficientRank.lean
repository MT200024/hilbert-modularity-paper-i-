/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CoefficientFree
public import HilbertModularity.Algebra.TateModule.FiniteLevelBasis

/-! # Ranks of Tate lattices over ramified coefficients

The same finite torsion group is obtained by reducing the integral Tate module
over the rational p-adic integers or over its completed coefficient ring.
Comparing these cardinalities determines the coefficient rank from the rational
Tate rank. This is the integral rank comparison used for canonical-prime torsion
in [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

attribute [local instance] coefficientModule completedCoefficientModule
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- The cofinal coefficient-ring isomorphism identifies the two actions on the same Tate lattice. -/
def coefficientPrimeEquiv (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) :
    letI := coefficientPrimeModule p R A J e he hJ
    LinearEquiv ((coefficientPrimeRingEquiv p R J e he hJ).toRingEquiv :
      AdicCompletion (Ideal.span {(p : R)}) R →+* AdicCompletion J R)
      (σ' := ((coefficientPrimeRingEquiv p R J e he hJ).toRingEquiv.symm :
        AdicCompletion J R →+* AdicCompletion (Ideal.span {(p : R)}) R))
      (integral p A) (integral p A) := by
  letI := coefficientPrimeModule p R A J e he hJ
  refine { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := ?_ }
  intro c x
  change c • x = (coefficientPrimeRingEquiv p R J e he hJ).symm
    (coefficientPrimeRingEquiv p R J e he hJ c) • x
  rw [AlgEquiv.symm_apply_apply]

/-- Freeness at a principal ramified coefficient prime also gives freeness over the p-adic coefficient completion. -/
theorem completedCoefficient_free_of_prime [IsDomain R]
    [Module.Finite ℤ_[p] (integral p A)]
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] :
    Module.Free (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) := by
  let := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  have := coefficientPrime_free_of_domain p R A a b ha hab e he hJ
  exact Module.Free.of_equiv (coefficientPrimeEquiv p R A (Ideal.span {a}) e he hJ).symm

section FiniteFree

variable [Nontrivial (AdicCompletion (Ideal.span {(p : R)}) R)]
  [Module.Finite (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A)]
  [Module.Free (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A)]

/-- The size of actual principal coefficient torsion is determined by the completed coefficient rank. -/
theorem card_principalTorsion (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    Nat.card (Submodule.torsionBy R A a) =
      Nat.card (R ⧸ Ideal.span {a}) ^
        Module.finrank (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) := by
  let := (completedPrincipalResidue p R a b hab).toAlgebra
  let basis := ((Module.finBasis (AdicCompletion (Ideal.span {(p : R)}) R)
    (integral p A)).baseChange (R ⧸ Ideal.span {a})).map
      (completedPrincipalResidualEquiv p R A a b hab hpdiv)
  rw [Nat.card_congr basis.equivFun.toEquiv, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Reduction of one Tate lattice over the two coefficient rings gives the ramification-degree rank formula. -/
theorem finrank_integral_eq_residue_degree_mul
    [Module.Finite ℤ_[p] (integral p A)]
    (hpdiv : Function.Surjective (fun x : A => p • x))
    (d : ℕ) (hcard : Nat.card (R ⧸ Ideal.span {(p : R)}) = p ^ d) :
    Module.finrank ℤ_[p] (integral p A) =
      d * Module.finrank (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) := by
  have eqv : Submodule.torsionBy R A (p : R) ≃ Torsion p A 1 :=
    Equiv.subtypeEquivRight fun x => by
      simp only [Submodule.mem_torsionBy_iff, AddSubgroup.torsionBy.nsmul_iff,
        pow_one, Nat.cast_smul_eq_nsmul]
  have h := card_principalTorsion p R A (p : R) 1 (mul_one _) hpdiv
  rw [Nat.card_congr eqv, card_torsion p A hpdiv 1, one_mul, hcard, ← pow_mul] at h
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h

end FiniteFree

/-- Total ramification and the actual rational-prime Tate rank determine the actual coefficient-prime torsion dimension. -/
theorem principalTorsion_finrank_of_integral_rank [IsDomain R]
    [Module.Finite ℤ_[p] (integral p A)]
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    (hpdiv : Function.Surjective (fun x : A => p • x))
    (d n : ℕ) (hd : 0 < d) (hcard : Nat.card (R ⧸ Ideal.span {(p : R)}) = p ^ d)
    (hrank : Module.finrank ℤ_[p] (integral p A) = d * n) :
    Module.finrank (R ⧸ Ideal.span {a}) (Submodule.torsionBy R A a) = n := by
  let : Nontrivial (AdicCompletion (Ideal.span {(p : R)}) R) :=
    ⟨⟨0, 1, fun h => (zero_ne_one : (0 : R ⧸ Ideal.span {a}) ≠ 1) (by
      simpa using congrArg (completedPrincipalResidue p R a b hab) h)⟩⟩
  have := completedCoefficient_finite p R A
  have := completedCoefficient_free_of_prime p R A a b ha hab e he hJ
  have h := finrank_integral_eq_residue_degree_mul p R A hpdiv d hcard
  have hcoeff : Module.finrank (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) = n :=
    Nat.eq_of_mul_eq_mul_left hd (h.symm.trans hrank)
  exact (principalTorsion_finrank p R A a b hab hpdiv).trans hcoeff

end TateModule
