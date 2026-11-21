/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.InertiaConjugacy
public import HilbertModularity.FieldTheory.RatFunc.Involution
public import HilbertModularity.FieldTheory.Galois.FieldEquiv
public import HilbertModularity.RingTheory.IntegralClosure.Equiv
public import HilbertModularity.RingTheory.Ideal.InertiaEquiv
public import HilbertModularity.RingTheory.Ideal.UnderEquiv

/-! # The complement coordinate on affine normalization and inertia

The actual extension of `X ↦ 1-X` to the algebraic closure acts on the
normalization of the polynomial coordinate ring. Its action on coordinate
primes agrees with the substitution on finite points.
-/

@[expose] public noncomputable section
namespace RatFunc
variable (K : Type*) [Field K]

/-- The chosen closure extension of the rational complement respects polynomial coordinates. -/
theorem complementClosure_algebraMap (f : Polynomial K) :
    IsAlgClosure.equivOfEquiv (AlgebraicClosure (RatFunc K)) (AlgebraicClosure (RatFunc K))
        (complementAlgEquiv K).toRingEquiv
        (algebraMap (Polynomial K) (AlgebraicClosure (RatFunc K)) f) =
      algebraMap (Polynomial K) (AlgebraicClosure (RatFunc K))
        (Polynomial.complementAlgEquiv K f) := by
  rw [IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K)
    (AlgebraicClosure (RatFunc K)), IsAlgClosure.equivOfEquiv_algebraMap]
  change algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K))
    (complementAlgEquiv K (algebraMap (Polynomial K) (RatFunc K) f)) = _
  rw [complementAlgEquiv_algebraMap, IsScalarTower.algebraMap_apply (Polynomial K)
    (RatFunc K) (AlgebraicClosure (RatFunc K)), Polynomial.complementAlgEquiv_apply]

/-- The complement coordinate induces an isomorphism of the actual affine normalization. -/
def affineComplementRingEquiv : affineIntegralClosure K ≃+* affineIntegralClosure K :=
  RingEquiv.mapIntegralClosure (Polynomial.complementAlgEquiv K).toRingEquiv
    (IsAlgClosure.equivOfEquiv (AlgebraicClosure (RatFunc K)) (AlgebraicClosure (RatFunc K))
      (complementAlgEquiv K).toRingEquiv) (complementClosure_algebraMap K)

/-- The normalized complement intertwines the actual absolute Galois actions. -/
theorem affineComplementRingEquiv_smul
    (g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
    (z : affineIntegralClosure K) :
    affineComplementRingEquiv K (g • z) =
      AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
        (complementAlgEquiv K).toRingEquiv g • affineComplementRingEquiv K z := by
  apply Subtype.ext
  exact (AlgebraicClosure.galoisFieldEquiv_intertwines (RatFunc K) (RatFunc K)
    (complementAlgEquiv K).toRingEquiv g z).symm

/-- Polynomial complement sends the prime at `a` to the prime at `1-a`. -/
theorem affinePrime_map_complement (a : K) :
    (affinePrime K a).map (Polynomial.complementAlgEquiv K).toRingEquiv =
      affinePrime K (1 - a) := by
  change (affinePrime K a).map
    ((Polynomial.complementAlgEquiv K).toRingEquiv : Polynomial K →+* Polynomial K) = _
  rw [Ideal.map_comap_of_equiv (Polynomial.complementAlgEquiv K).toRingEquiv]
  ext f
  change Polynomial.eval a ((Polynomial.complementAlgEquiv K).symm f) = 0 ↔
    Polynomial.eval (1 - a) f = 0
  simp only [Polynomial.complementAlgEquiv_symm, Polynomial.complementAlgEquiv_apply,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]

/-- The inertia group of a transported prime is the transported inertia subgroup. -/
theorem inertia_map_affineComplement (P : Ideal (affineIntegralClosure K)) :
    (P.map (affineComplementRingEquiv K)).inertia
        (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K)) =
      (P.inertia (AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))).map
        (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
          (complementAlgEquiv K).toRingEquiv).toMonoidHom :=
  Ideal.inertia_map_ringEquiv P (affineComplementRingEquiv K)
    (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
      (complementAlgEquiv K).toRingEquiv) (affineComplementRingEquiv_smul K)

/-- Complement sends a prime above `a` to a prime above `1-a`. -/
theorem affineComplementPrime_liesOver (a : K) (P : Ideal (affineIntegralClosure K))
    [P.LiesOver (affinePrime K a)] :
    (P.map (affineComplementRingEquiv K)).LiesOver (affinePrime K (1 - a)) := by
  constructor
  rw [Ideal.under_map_ringEquiv P (Polynomial.complementAlgEquiv K).toRingEquiv
    (affineComplementRingEquiv K)
    (RingEquiv.mapIntegralClosure_algebraMap _ _ (complementClosure_algebraMap K)),
    ← P.over_def (affinePrime K a), affinePrime_map_complement]

variable [CharZero K]

/-- The actual complement Galois isomorphism exchanges finite-coordinate inertia
with inertia at the complemented coordinate, up to a change of prime. -/
theorem affineInertia_complement_conjugate (a : K) :
    ∃ g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K),
      (affineInertia K a).map
        (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
          (complementAlgEquiv K).toRingEquiv).toMonoidHom =
        (affineInertia K (1 - a)).map (MulAut.conj g).toMonoidHom := by
  let P := (affinePrimeAbove K a).map (affineComplementRingEquiv K)
  have : P.LiesOver (affinePrime K (1 - a)) :=
    affineComplementPrime_liesOver K a (affinePrimeAbove K a)
  obtain ⟨g, hg⟩ := affineInertia_conjugate K (1 - a) P
  exact ⟨g, (inertia_map_affineComplement K (affinePrimeAbove K a)).symm.trans hg⟩

end RatFunc
