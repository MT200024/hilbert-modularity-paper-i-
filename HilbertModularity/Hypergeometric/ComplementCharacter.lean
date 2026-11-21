/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparisonSpecialization
public import HilbertModularity.Hypergeometric.FamilyComparison
public import HilbertModularity.RepresentationTheory.SurjectiveRestriction
public import HilbertModularity.Geometry.Etale.LocalSystemInvolution
public import HilbertModularity.Geometry.Etale.ParameterInvolution
public import HilbertModularity.Geometry.Etale.LocalSystem.Coordinates

/-! # The fixed midpoint makes a complement comparison quadratic

For [TripathiGoswamiRevised, Lemma `lem:involution`], a geometric
comparison with the actual complement pullback gives a single arithmetic
character by Schur descent. The fibre at `1/2` is fixed, so its determinant
forces this character to have square one. No Hodge or purity premise is
needed for this finiteness deduction.
-/

public noncomputable section

open AlgebraicGeometry

namespace HilbertModularity.Hypergeometric

/-- A geometrically absolutely irreducible rank-two family equivalent to
its complement pullback geometrically differs from it arithmetically by
one quadratic character, before all fibres are chosen. The supplied
geometric equivalence is an explicit remaining application input. -/
theorem exists_quadratic_character_of_geometric_complement
    (K L : Type*) [Field K] [CharZero K]
    [NontriviallyNormedField L] [CharZero L] [CompleteSpace L]
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (hd : Module.finrank L (F.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K)
        (ProjectiveLine.puncturedPoint K (ProjectiveLine.midpointParameter K)))) = 2)
    (eGeom : Representation.Equiv
      ((puncturedFiberMonodromy K (ProjectiveLine.midpointParameter K) F).comp
        (puncturedArithmeticProjectionHom K (ProjectiveLine.midpointParameter K)).ker.subtype)
      ((puncturedFiberMonodromy K (ProjectiveLine.midpointParameter K)
        (F.complementPullback K L)).comp
        (puncturedArithmeticProjectionHom K (ProjectiveLine.midpointParameter K)).ker.subtype))
    [Representation.IsIrreducible (Representation.baseChange (AlgebraicClosure L)
      ((puncturedFiberMonodromy K (ProjectiveLine.midpointParameter K) F).comp
        (puncturedArithmeticProjectionHom K (ProjectiveLine.midpointParameter K)).ker.subtype))] :
    ∃ ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ,
      Continuous ν ∧ ν ^ 2 = 1 ∧ (Set.range ν).Finite ∧
        ∀ ξ : ProjectiveLine.Parameter K,
          Nonempty (((Representation.ofCharacter ν).tprod
            (puncturedFiberArithmeticRepresentation K ξ F)).Equiv
              (puncturedFiberArithmeticRepresentation K
                (ProjectiveLine.complementParameter K ξ) F)) := by
  let ξ₀ := ProjectiveLine.midpointParameter K
  let x := ProjectiveLine.puncturedPoint K ξ₀
  let F' := F.complementPullback K L
  let ρ := F.coordinateMonodromy x
  let σ := F'.coordinateMonodromy x
  let e₀ := (F.coordinateMonodromyEquiv x).symm
  let e₁ := (F'.coordinateMonodromyEquiv x).symm
  let π := puncturedArithmeticProjectionHom K ξ₀
  let k := π.ker.subtype
  let : Nonempty (Fin (Module.finrank L (F.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)))) :=
    ⟨⟨0, by rw [hd]; decide⟩⟩
  have eGeom' := (e₀.compHom k).trans (eGeom.trans (e₁.symm.compHom k))
  let : (Representation.baseChange (AlgebraicClosure L) (ρ.comp k)).IsIrreducible := by
    apply (OrderIso.isSimpleOrder_iff
      ((e₀.compHom k).baseChange (AlgebraicClosure L)).subrepresentationOrderIso).mpr
    change (Representation.baseChange (AlgebraicClosure L)
      ((puncturedFiberMonodromy K (ProjectiveLine.midpointParameter K) F).comp
        (puncturedArithmeticProjectionHom K (ProjectiveLine.midpointParameter K)).ker.subtype)
      ).IsIrreducible
    infer_instance
  obtain ⟨ν, hνc, ⟨e⟩⟩ := exists_punctured_comparison_character K ξ₀ ρ σ
    (F.continuous_coordinateMonodromy x) (F'.continuous_coordinateMonodromy x)
    eGeom' (AlgebraicClosure L)
  have hgeneric :=
    (Representation.characterTensorEquivCongr (ν.comp π) e₀.symm).trans (e.trans e₁)
  have hall := puncturedComparisonAllFibers K ξ₀ F F' ν hgeneric
  have emid : (puncturedFiberArithmeticRepresentation K ξ₀ F').Equiv
      (puncturedFiberArithmeticRepresentation K ξ₀ F) := by
    exact F.pullbackArithmeticEquiv (ProjectiveLine.puncturedComplementIso K).hom K
      x x (ProjectiveLine.puncturedPoint_midpoint_complement K)
  have hsq := Representation.character_sq_of_tensor_equiv
    (puncturedFiberArithmeticRepresentation K ξ₀ F)
    (puncturedFiberArithmeticRepresentation K ξ₀ F) ν
    ((hall ξ₀).trans emid) hd (fun _ => rfl)
  refine ⟨ν, hνc, hsq, Representation.finite_range_of_character_sq ν hsq, ?_⟩
  intro ξ
  exact ⟨(hall ξ).trans (F.complementPullbackArithmeticEquiv K L ξ)⟩

end HilbertModularity.Hypergeometric
