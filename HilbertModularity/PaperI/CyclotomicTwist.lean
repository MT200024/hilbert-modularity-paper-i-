module
public import HilbertModularity.Hypergeometric.CyclotomicComparison
public import HilbertModularity.Hypergeometric.ModularityHypotheses
public import HilbertModularity.RepresentationTheory.FiniteCharacterRamification

/-! # The character of the full cyclotomic field over its maximal real subfield -/
public noncomputable section
namespace HilbertModularity.PaperI
open HilbertModularity.Cyclotomic HilbertModularity.Hypergeometric HilbertModularity.HilbertModularForms
open IsDedekindDomain
open scoped Classical
variable (p : ℕ) [NeZero p] [Fact (1 < p)]

def cyclotomicSign (L : Type*) [Field L] : AbsoluteGalois (realCyclotomicField p) →* Lˣ :=
  (residualSignCharacter p L).comp (realCyclotomicGaloisEquiv p).symm.toMonoidHom

def primitiveRootInClosure := (realCyclotomicClosureEquiv p).symm (zeta p)

omit [Fact (1 < p)] in
theorem primitiveRootInClosure_isPrimitiveRoot : IsPrimitiveRoot (primitiveRootInClosure p) p :=
  (zeta_isPrimitiveRoot p).map_of_injective (realCyclotomicClosureEquiv p).symm.injective

theorem cyclotomicSign_apply (L : Type*) [Field L] (g : AbsoluteGalois (realCyclotomicField p)) :
    cyclotomicSign p L g = if g (primitiveRootInClosure p) = primitiveRootInClosure p then 1 else -1 := by
  obtain ⟨u, rfl⟩ := (realCyclotomicGaloisEquiv p).surjective g
  rw [cyclotomicSign, MonoidHom.comp_apply]
  change residualSignCharacter p L ((realCyclotomicGaloisEquiv p).symm ((realCyclotomicGaloisEquiv p) u)) = _
  rw [MulEquiv.symm_apply_apply, residualSignCharacter_apply, realCyclotomicGaloisEquiv_apply]
  simp [residualCharacter, (zeta_isPrimitiveRoot p).autToPow_eq_one_iff, primitiveRootInClosure]

theorem cyclotomicSign_locallyConstant (L : Type*) [Field L] : IsLocallyConstant (cyclotomicSign p L) := by
  classical
  let z := primitiveRootInClosure p
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  have ho := (stabilizer_isOpen_of_isIntegral (K := realCyclotomicField p) z).preimage
    (continuous_const.mul continuous_id : Continuous fun h => g⁻¹ * h)
  have hn := ho.mem_nhds (show g⁻¹*g ∈ MulAction.stabilizer (AbsoluteGalois (realCyclotomicField p)) z by simp)
  filter_upwards [hn] with h hh
  change (g⁻¹*h) z = z at hh
  have he : h z = g z := by simpa using congrArg g hh
  simp only [cyclotomicSign_apply, ← show z = primitiveRootInClosure p from rfl, he]

theorem cyclotomicSign_finite (L : Type*) [Field L] : (Set.range (cyclotomicSign p L)).Finite := by
  classical
  apply (Set.toFinite ({1, -1} : Set Lˣ)).subset
  rintro _ ⟨g, rfl⟩
  rw [cyclotomicSign_apply]
  split <;> simp

def algebraicCyclotomicSign (B : Type*) [Field B] [NumberField B] :
    FiniteAlgebraicGaloisCharacter (realCyclotomicField p) B := by
  classical
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  let χ := cyclotomicSign p B
  let h := finiteCharacter_unramifiedOutsideFinite χ
    (cyclotomicSign_locallyConstant p B).continuous (cyclotomicSign_finite p B)
  exact { toMonoidHom := χ, finite_range := cyclotomicSign_finite p B,
          local_continuous := fun w => ((cyclotomicSign_locallyConstant p B).comp
            (fun u : Bˣ => algebraMap B (w.adicCompletion B) (u : B))).continuous,
          bad := h.choose, bad_finite := h.choose_spec.1, unramified := h.choose_spec.2 }

theorem algebraicCyclotomicSign_map (B L : Type*) [Field B] [NumberField B] [Field L] (i : B →+* L) :
    (Units.map i.toMonoidHom).comp (algebraicCyclotomicSign p B).toMonoidHom = cyclotomicSign p L := by
  classical
  ext g
  change i (cyclotomicSign p B g : B) = (cyclotomicSign p L g : L)
  rw [cyclotomicSign_apply, cyclotomicSign_apply]
  split <;> simp

theorem cyclotomicSign_fixedField (L : Type*) [Field L] [CharZero L] :
    IntermediateField.fixedField (cyclotomicSign p L).ker =
      IntermediateField.adjoin (realCyclotomicField p) {primitiveRootInClosure p} := by
  classical
  have hz := primitiveRootInClosure_isPrimitiveRoot p
  rw [← hz.fixedField_ker_autToPow]
  congr 1
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, cyclotomicSign_apply, hz.autToPow_eq_one_iff]
  split <;> simp_all

end HilbertModularity.PaperI
