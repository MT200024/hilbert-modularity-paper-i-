/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.Quotient
public import HilbertModularity.RepresentationTheory.CharacterComparison
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Bases adapted to an ordinary quotient

A stable line in a two-dimensional representation yields an upper-triangular
basis. Its lower diagonal character is the actual action on the quotient,
as used in the nearly ordinary formulation of [TripathiGoswami].
-/

@[expose] public noncomputable section

open Classical

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- The character of a one-dimensional representation, expressed in a one-vector basis. -/
def characterOfBasis (ρ : Representation K G V) (b : Module.Basis (Fin 1) K V) : G →* Kˣ :=
  (((Matrix.uniqueAlgEquiv (R := K) (m := Fin 1) (A := K)).toMonoidHom.comp
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ).toHomUnits

@[simp]
theorem characterOfBasis_apply (ρ : Representation K G V) (b : Module.Basis (Fin 1) K V)
    (g : G) : (characterOfBasis ρ b g : K) = b.repr (ρ g (b 0)) 0 := by
  change (LinearMap.toMatrixAlgEquiv b (ρ g)) default default = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

/-- A one-dimensional action is scalar multiplication by its actual character. -/
theorem apply_eq_characterOfBasis_smul (ρ : Representation K G V)
    (b : Module.Basis (Fin 1) K V) (g : G) (v : V) :
    ρ g v = (characterOfBasis ρ b g : K) • v := by
  have hv : b.repr v 0 • b 0 = v := by simpa using b.sum_repr v
  have hg : b.repr (ρ g (b 0)) 0 • b 0 = ρ g (b 0) := by
    simpa using b.sum_repr (ρ g (b 0))
  rw [← hv, map_smul, ← hg, characterOfBasis_apply, smul_smul, smul_smul, mul_comm]

/-- A one-vector basis identifies the representation with its scalar character. -/
def characterOfBasisEquiv (ρ : Representation K G V) (b : Module.Basis (Fin 1) K V) :
    ρ.Equiv (ofCharacter (characterOfBasis ρ b)) :=
  .mk (b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)) (by
    intro g
    ext v
    change b.repr (ρ g v) 0 = (characterOfBasis ρ b g : K) * b.repr v 0
    rw [apply_eq_characterOfBasis_smul, map_smul]
    rfl)

end Representation

namespace Subrepresentation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {ρ : Representation K G V} (S : Subrepresentation ρ)
  (bS : Module.Basis (Fin 1) K S.toSubmodule) (bQ : Module.Basis (Fin 1) K (V ⧸ S.toSubmodule))

/-- The two-vector basis obtained from a basis of a stable line and of its quotient. -/
def ordinaryBasis : Module.Basis (Fin 2) K V :=
  (bS.sumQuot bQ).reindex finSumFinEquiv

@[simp]
theorem ordinaryBasis_zero : ordinaryBasis S bS bQ 0 = (bS 0 : V) := by
  rw [ordinaryBasis, Module.Basis.reindex_apply]
  change (bS.sumQuot bQ) (Sum.inl 0) = _
  exact bS.sumQuot_inl bQ 0

@[simp]
theorem ordinaryBasis_one_quotient :
    (Submodule.Quotient.mk (ordinaryBasis S bS bQ 1) : V ⧸ S.toSubmodule) = bQ 0 := by
  rw [ordinaryBasis, Module.Basis.reindex_apply]
  change S.toSubmodule.mkQ ((bS.sumQuot bQ) (Sum.inr 0)) = _
  exact bS.sumQuot_inr bQ 0

/-- The second coordinate in the adapted basis is exactly the quotient coordinate. -/
theorem ordinaryBasis_repr_one (v : V) :
    (ordinaryBasis S bS bQ).repr v 1 = bQ.repr (S.toSubmodule.mkQ v) 0 := by
  rw [ordinaryBasis, Module.Basis.repr_reindex_apply]
  change (bS.sumQuot bQ).repr v (Sum.inr 0) = _
  exact bS.sumQuot_repr_inr bQ v 0

/-- Stability forces the lower-left entry of every action matrix to vanish. -/
theorem toMatrix_ordinaryBasis_lower_left (g : G) :
    LinearMap.toMatrix (ordinaryBasis S bS bQ) (ordinaryBasis S bS bQ) (ρ g) 1 0 = 0 := by
  rw [LinearMap.toMatrix_apply, ordinaryBasis_zero, ordinaryBasis_repr_one]
  have h : S.toSubmodule.mkQ (ρ g (bS 0 : V)) = 0 :=
    (Submodule.Quotient.mk_eq_zero S.toSubmodule).mpr (S.apply_mem_toSubmodule g (bS 0).property)
  simp [h]

/-- The lower-right matrix entry is the scalar character of the actual quotient representation. -/
theorem toMatrix_ordinaryBasis_lower_right (g : G) :
    LinearMap.toMatrix (ordinaryBasis S bS bQ) (ordinaryBasis S bS bQ) (ρ g) 1 1 =
      (Representation.characterOfBasis
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) bQ g : K) := by
  rw [LinearMap.toMatrix_apply, ordinaryBasis_repr_one, Representation.characterOfBasis_apply]
  change bQ.repr ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) g
    (S.toSubmodule.mkQ (ordinaryBasis S bS bQ 1))) 0 = _
  rw [Submodule.mkQ_apply, ordinaryBasis_one_quotient]


/-- The upper-left matrix entry is the scalar character of the invariant line. -/
theorem toMatrix_ordinaryBasis_upper_left (g : G) :
    LinearMap.toMatrix (ordinaryBasis S bS bQ) (ordinaryBasis S bS bQ) (ρ g) 0 0 =
      (Representation.characterOfBasis S.toRepresentation bS g : K) := by
  rw [LinearMap.toMatrix_apply, ordinaryBasis_zero, ordinaryBasis,
    Module.Basis.repr_reindex_apply, Representation.characterOfBasis_apply]
  change (bS.sumQuot bQ).repr (ρ g (bS 0 : V)) (Sum.inl 0) = _
  rw [Module.Basis.sumQuot_repr_inl_of_mem _ _ _
    (S.apply_mem_toSubmodule g (bS 0).property)]
  rfl

omit bS bQ in
/-- A rank-one quotient of a two-dimensional representation gives an actual upper-triangular
basis; the lower diagonal character is equivariantly the given quotient representation. -/
theorem exists_basis_upperTriangular [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (hQ : Module.finrank K (V ⧸ S.toSubmodule) = 1) :
    ∃ (b : Module.Basis (Fin 2) K V) (χ₁ χ₂ : G →* Kˣ) (a : G → K),
      b 0 ∈ S ∧
      Nonempty ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).Equiv
        (Representation.ofCharacter χ₂)) ∧
      ∀ g, LinearMap.toMatrix b b (ρ g) = !![(χ₁ g : K), a g; 0, (χ₂ g : K)] := by
  have hS : Module.finrank K S.toSubmodule = 1 := by
    have h := S.toSubmodule.finrank_quotient_add_finrank
    rw [hV, hQ] at h
    omega
  let bS := Module.finBasisOfFinrankEq K S.toSubmodule hS
  let bQ := Module.finBasisOfFinrankEq K (V ⧸ S.toSubmodule) hQ
  let b := ordinaryBasis S bS bQ
  refine ⟨b, Representation.characterOfBasis S.toRepresentation bS,
    Representation.characterOfBasis (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) bQ,
    fun g => LinearMap.toMatrix b b (ρ g) 0 1, ?_, ?_, ?_⟩
  · change ordinaryBasis S bS bQ 0 ∈ S
    rw [ordinaryBasis_zero]
    exact (bS 0).property
  · exact ⟨Representation.characterOfBasisEquiv
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) bQ⟩
  · intro g
    ext i j
    fin_cases i <;> fin_cases j
    · exact toMatrix_ordinaryBasis_upper_left S bS bQ g
    · rfl
    · exact toMatrix_ordinaryBasis_lower_left S bS bQ g
    · exact toMatrix_ordinaryBasis_lower_right S bS bQ g

end Subrepresentation



namespace Representation

variable {K G V : Type*} [NontriviallyNormedField K] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]

/-- The scalar character of a continuous one-dimensional action is continuous. -/
theorem continuous_characterOfBasis (ρ : Representation K G V)
    (b : Module.Basis (Fin 1) K V) (hρ : ∀ v, Continuous (fun g => ρ g v)) :
    Continuous (characterOfBasis ρ b) := by
  have hv : Continuous (fun g => (characterOfBasis ρ b g : K)) := by
    simp only [characterOfBasis_apply]
    exact (IsModuleTopology.continuous_of_linearMap (b.coord 0)).comp (hρ (b 0))
  exact hv.of_coeHom_comp

end Representation

namespace Subrepresentation

variable {K G V : Type*} [NontriviallyNormedField K] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]
  [FiniteDimensional K V]
  {ρ : Representation K G V}

/-- For a continuous rank-two action, the two adapted diagonal characters are continuous;
the lower one is still equivariantly the original stable rank-one quotient. -/
theorem exists_continuous_characters_upperTriangular (S : Subrepresentation ρ)
    (hV : Module.finrank K V = 2) (hQ : Module.finrank K (V ⧸ S.toSubmodule) = 1)
    (hρ : ∀ v, Continuous (fun g => ρ g v)) :
    ∃ (b : Module.Basis (Fin 2) K V) (χ₁ χ₂ : G →* Kˣ) (a : G → K),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ S ∧
      Nonempty ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).Equiv
        (Representation.ofCharacter χ₂)) ∧
      ∀ g, LinearMap.toMatrix b b (ρ g) = !![(χ₁ g : K), a g; 0, (χ₂ g : K)] := by
  obtain ⟨b, χ₁, χ₂, a, hb, he, hm⟩ := S.exists_basis_upperTriangular hV hQ
  have hc (i j : Fin 2) : Continuous (fun g => LinearMap.toMatrix b b (ρ g) i j) := by
    simp only [LinearMap.toMatrix_apply]
    exact (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (hρ (b j))
  have hχ₁ : Continuous (fun g => (χ₁ g : K)) := by
    convert hc 0 0 using 1
    funext g
    rw [hm]
    rfl
  have hχ₂ : Continuous (fun g => (χ₂ g : K)) := by
    convert hc 1 1 using 1
    funext g
    rw [hm]
    rfl
  exact ⟨b, χ₁, χ₂, a, hχ₁.of_coeHom_comp, hχ₂.of_coeHom_comp, hb, he, hm⟩

end Subrepresentation
