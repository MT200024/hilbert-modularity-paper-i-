/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparisonSpecialization

/-! # Finite comparison character at all punctured fibres

The arithmetic comparison character is chosen on the generic fundamental
group. Once its finite image is known, the same character compares the two
local systems at every rational nonsingular fibre. The generic geometric
comparison and determinant calculations are handled separately in
`RMComparisonFinitePaths`. -/

public noncomputable section

open AlgebraicGeometry

namespace HilbertModularity.Hypergeometric

/-- Transport a finite generic comparison character to every rational fibre
of the actual punctured line. The character itself and its finite image are
generic data, so neither depends on the fibre or the chosen path. This is the
specialization step of [TripathiGoswamiRevised, Theorem RMgeneral]. -/
theorem finite_comparison_character_at_all_punctured_fibers
    (K : Type*) [Field K] [CharZero K]
    (ξ₀ : ProjectiveLine.Parameter K)
    {L : Type*} [Field L] [TopologicalSpace L]
    (F_RM F_eff : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ)
    (hν : Continuous ν) (hfinite : (Set.range ν).Finite)
    (hgeneric : ((Representation.ofCharacter
      (ν.comp (puncturedArithmeticProjectionHom K ξ₀))).tprod
        (puncturedFiberMonodromy K ξ₀ F_RM)).Equiv
          (puncturedFiberMonodromy K ξ₀ F_eff)) :
    Continuous ν ∧ (Set.range ν).Finite ∧
      ∀ ξ : ProjectiveLine.Parameter K,
        Nonempty (((Representation.ofCharacter ν).tprod
          (puncturedFiberArithmeticRepresentation K ξ F_RM)).Equiv
            (puncturedFiberArithmeticRepresentation K ξ F_eff)) := by
  refine ⟨hν, hfinite, ?_⟩
  intro ξ
  exact ⟨puncturedComparisonAllFibers K ξ₀ F_RM F_eff ν hgeneric ξ⟩

end HilbertModularity.Hypergeometric
