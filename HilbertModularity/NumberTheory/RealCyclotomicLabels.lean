/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.RealCyclotomicNormal
public import HilbertModularity.NumberTheory.CyclotomicEmbeddings

/-! # Exhaustion of the real cyclotomic coefficient labels

Every embedding of the real multiplication field into a containing field is a
coprime power label. In particular the actual local scalar conjugates exhaust
the embedding labels, as used in [TripathiGoswami, ramified scalar label].
-/

@[expose] public noncomputable section
namespace HilbertModularity.Cyclotomic

/-- Every automorphism of the cyclotomic field is the specified coprime power automorphism. -/
theorem exists_powerAutomorphism (N : ℕ) [NeZero N]
    (g : cyclotomicField N ≃ₐ[ℚ] cyclotomicField N) :
    ∃ m < N, ∃ hm : m.Coprime N, g = powerAutomorphism N m hm := by
  obtain ⟨m, hmN, hm, hroot⟩ := (root_isPrimitiveRoot N).isPrimitiveRoot_iff.mp
    ((root_isPrimitiveRoot N).map_of_injective g.injective)
  refine ⟨m, hmN, hm, ?_⟩
  have he : g.toAlgHom = (powerAutomorphism N m hm).toAlgHom := by
    apply ((root_isPrimitiveRoot N).powerBasis ℚ).algHom_ext
    exact hroot.symm.trans (powerAutomorphism_root N m hm).symm
  exact AlgEquiv.ext (fun x => AlgHom.congr_fun he x)

/-- Restricting cyclotomic power automorphisms exhausts the real-field automorphisms. -/
theorem exists_realPowerAutomorphism (N : ℕ) [NeZero N]
    (g : realCyclotomicField N ≃ₐ[ℚ] realCyclotomicField N) :
    ∃ m < N, ∃ hm : m.Coprime N, g = realPowerAutomorphism N m hm := by
  let : Algebra (realCyclotomicField N) (cyclotomicField N) :=
    (IntermediateField.inclusion (realCyclotomicField_le N)).toAlgebra
  let : IsScalarTower ℚ (realCyclotomicField N) (cyclotomicField N) :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion (realCyclotomicField_le N)).comp_algebraMap
  obtain ⟨m, hmN, hm, he⟩ := exists_powerAutomorphism N (g.liftNormal (cyclotomicField N))
  refine ⟨m, hmN, hm, ?_⟩
  apply AlgEquiv.ext
  intro x
  apply (IntermediateField.inclusion (realCyclotomicField_le N)).injective
  have h := g.liftNormal_commutes (cyclotomicField N) x
  rw [he] at h
  exact h.symm

/-- Every coefficient embedding into a containing field has a coprime power label. -/
theorem exists_powerEmbedding (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L] [Algebra (realCyclotomicField N) L]
    [IsScalarTower ℚ (realCyclotomicField N) L]
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    ∃ m < N, ∃ hm : m.Coprime N,
      σ = (IsScalarTower.toAlgHom ℚ (realCyclotomicField N) L).comp
        (powerEmbedding N m hm) := by
  obtain ⟨m, hmN, hm, he⟩ := exists_realPowerAutomorphism N (Normal.algHomEquivAut ℚ L (realCyclotomicField N) σ)
  refine ⟨m, hmN, hm, ?_⟩
  have h := (Normal.algHomEquivAut ℚ L (realCyclotomicField N)).symm_apply_apply σ
  rw [he] at h
  exact h.symm

end HilbertModularity.Cyclotomic
