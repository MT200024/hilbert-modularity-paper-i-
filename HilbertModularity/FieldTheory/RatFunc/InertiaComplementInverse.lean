/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.RatFunc.InertiaComplement

/-! # Inverse complement transport of actual inertia

The selected algebraic-closure lift need not be involutive. The inverse lift
nevertheless covers the same polynomial complement, and exchanges the same
finite-coordinate inertia groups up to conjugacy.
-/

@[expose] public noncomputable section
namespace RatFunc
variable (K : Type*) [Field K]

/-- The inverse normalized complement also covers polynomial complement. -/
theorem affineComplementRingEquiv_symm_algebraMap (f : Polynomial K) :
    (affineComplementRingEquiv K).symm
        (algebraMap (Polynomial K) (affineIntegralClosure K) f) =
      algebraMap (Polynomial K) (affineIntegralClosure K)
        (Polynomial.complementAlgEquiv K f) := by
  apply (affineComplementRingEquiv K).injective
  rw [RingEquiv.apply_symm_apply]
  change _ = RingEquiv.mapIntegralClosure _ _ (complementClosure_algebraMap K) _
  rw [RingEquiv.mapIntegralClosure_algebraMap]
  have h := (Polynomial.complementAlgEquiv K).symm_apply_apply f
  rw [Polynomial.complementAlgEquiv_symm] at h
  change algebraMap (Polynomial K) (affineIntegralClosure K) f =
    algebraMap (Polynomial K) (affineIntegralClosure K)
      (Polynomial.complementAlgEquiv K (Polynomial.complementAlgEquiv K f))
  rw [h]

/-- The inverse normalized complement intertwines the inverse Galois-coordinate map. -/
theorem affineComplementRingEquiv_symm_smul
    (g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
    (z : affineIntegralClosure K) :
    (affineComplementRingEquiv K).symm (g • z) =
      (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
        (complementAlgEquiv K).toRingEquiv).symm g • (affineComplementRingEquiv K).symm z := by
  apply (affineComplementRingEquiv K).injective
  rw [RingEquiv.apply_symm_apply, affineComplementRingEquiv_smul,
    MulEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- Inverse normalized complement sends a prime above `a` to one above `1-a`. -/
theorem affineComplementPrime_symm_liesOver (a : K) (P : Ideal (affineIntegralClosure K))
    [P.LiesOver (affinePrime K a)] :
    (P.map (affineComplementRingEquiv K).symm).LiesOver (affinePrime K (1 - a)) := by
  constructor
  rw [Ideal.under_map_ringEquiv P (Polynomial.complementAlgEquiv K).toRingEquiv
    (affineComplementRingEquiv K).symm (affineComplementRingEquiv_symm_algebraMap K),
    ← P.over_def (affinePrime K a), affinePrime_map_complement]

variable [CharZero K]

/-- Inverse closure transport exchanges complementary finite-coordinate inertia groups. -/
theorem affineInertia_complement_symm_conjugate (a : K) :
    ∃ g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K),
      (affineInertia K a).map
        (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
          (complementAlgEquiv K).toRingEquiv).symm.toMonoidHom =
        (affineInertia K (1 - a)).map (MulAut.conj g).toMonoidHom := by
  let P := (affinePrimeAbove K a).map (affineComplementRingEquiv K).symm
  have : P.LiesOver (affinePrime K (1 - a)) :=
    affineComplementPrime_symm_liesOver K a (affinePrimeAbove K a)
  obtain ⟨g, hg⟩ := affineInertia_conjugate K (1 - a) P
  have h := Ideal.inertia_map_ringEquiv (affinePrimeAbove K a) (affineComplementRingEquiv K).symm
    (AlgebraicClosure.galoisFieldEquiv (RatFunc K) (RatFunc K)
      (complementAlgEquiv K).toRingEquiv).symm (affineComplementRingEquiv_symm_smul K)
  exact ⟨g, h.symm.trans hg⟩

end RatFunc
