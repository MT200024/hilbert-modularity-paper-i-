/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FamilyComparison
public import HilbertModularity.RepresentationTheory.DeterminantCharacter
public import Mathlib.Topology.Algebra.Group.Subgroup

/-! # A finite uniform twist from a cusp-swapping family involution

Dense unipotent cusp generators make the geometric determinant trivial.
An automorphism over the arithmetic quotient therefore preserves the family
determinant. The rank-two comparison of [TripathiGoswami, lem:involution]
then gives one finite quadratic character for every section.
-/

@[expose] public noncomputable section

namespace HilbertModularity.Hypergeometric

variable {K G : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [Group G] [TopologicalSpace G] [ContinuousInv G]

/-- Dense irreducible unipotent cusp monodromies force the determinant character
of the whole continuous representation to be trivial. -/
theorem determinantCharacter_eq_one_of_unipotent_cusps
    (ρ : Representation K G (Fin 2 → K))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (a b : G) (hdense : Dense (Subgroup.closure ({a, b} : Set G) : Set G))
    (hA : (ρ a - 1) ^ 2 = 0) (hB : (ρ b - 1) ^ 2 = 0) (hBne : ρ b ≠ 1)
    (hirr : ∀ v, ρ a v = v → ρ b v = v → v = 0) :
    Representation.determinantCharacter ρ = 1 := by
  obtain ⟨c, τ, _, hc0, hc1⟩ := Monodromy.exists_basis_unipotent_pair
    (ρ a) (ρ b) hA hB hBne hirr
  have ha : Representation.determinantCharacter ρ a = 1 := by
    apply Units.ext
    change LinearMap.det (ρ a) = 1
    simpa only [LinearMap.det_toMatrix, Monodromy.det_U0] using congrArg Matrix.det hc0
  have hb : Representation.determinantCharacter ρ b = 1 := by
    apply Units.ext
    change LinearMap.det (ρ b) = 1
    simpa only [LinearMap.det_toMatrix, Monodromy.det_U1] using congrArg Matrix.det hc1
  have hc : Continuous (Representation.determinantCharacter ρ) :=
    Representation.continuous_determinantCharacter_of_basis (Pi.basisFun K (Fin 2))
      (fun i => ((Pi.basisFun K (Fin 2)).coord i).continuous_of_finiteDimensional)
      ρ hρ
  have he : Set.EqOn (Representation.determinantCharacter ρ) (1 : G →* Kˣ) {a, b} := by
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact ha
    · exact Set.mem_singleton_iff.mp hg ▸ hb
  have hall : (Representation.determinantCharacter ρ : G → Kˣ) = fun _ => 1 :=
    Continuous.ext_on hdense hc continuous_const (MonoidHom.eqOn_closure he)
  apply MonoidHom.ext
  exact congrFun hall

omit [CompleteSpace K] [TopologicalSpace G] [ContinuousInv G] in
/-- An arithmetic-quotient-preserving automorphism preserves determinants when
the determinant is trivial on the quotient kernel. -/
theorem determinant_eq_comp_of_kernel_trivial {Γ : Type*} [Group Γ]
    (π : G →* Γ) (ρ : Representation K G (Fin 2 → K)) (α : G ≃* G)
    (hπα : π.comp α.toMonoidHom = π)
    (hker : ∀ h : π.ker, Representation.determinantCharacter ρ h = 1) :
    ∀ g, LinearMap.det (ρ g) = LinearMap.det ((ρ.comp α.toMonoidHom) g) := by
  intro g
  have hg : π (α g) = π g := congrArg (fun f : G →* Γ => f g) hπα
  have hk : α g * g⁻¹ ∈ π.ker := by
    change π (α g * g⁻¹) = 1
    simp [hg]
  have he := hker ⟨α g * g⁻¹, hk⟩
  change Representation.determinantCharacter ρ (α g * g⁻¹) = 1 at he
  rw [map_mul, map_inv, mul_inv_eq_one] at he
  exact congrArg Units.val he.symm

omit [ContinuousInv G] in
/-- A continuous rank-two family with an arithmetic cusp-swapping automorphism
has one finite quadratic twist for all its sections. The determinant and
absolute irreducibility conclusions are derived from the actual cusp data. -/
theorem exists_uniform_quadratic_character_of_cusp_involution
    [CharZero K] [CompactSpace G] [IsTopologicalGroup G]
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [T2Space Γ]
    (π : G →* Γ) (hπ : Function.Surjective π) (hπc : Continuous π)
    (ρ : Representation K G (Fin 2 → K))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (α : G ≃* G) (hα : Continuous α) (hπα : π.comp α.toMonoidHom = π)
    (a b : π.ker) (hdense : Dense (Subgroup.closure ({a, b} : Set π.ker) : Set π.ker))
    (ha : α (a : G) = b) (hb : α (b : G) = a)
    (hA : (ρ a - 1) ^ 2 = 0) (hB : (ρ b - 1) ^ 2 = 0)
    (hAne : ρ a ≠ 1) (hBne : ρ b ≠ 1)
    (hirr : ∀ v, ρ a v = v → ρ b v = v → v = 0)
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E] :
    ∃ ν : Γ →* Kˣ, Continuous ν ∧ ν ^ 2 = 1 ∧ (Set.range ν).Finite ∧
      Nonempty (((Representation.ofCharacter (ν.comp π)).tprod ρ).Equiv
        (ρ.comp α.toMonoidHom)) ∧
      ∀ (s : Γ →* G), π.comp s = MonoidHom.id Γ →
        Nonempty (((Representation.ofCharacter ν).tprod (ρ.comp s)).Equiv
          ((ρ.comp α.toMonoidHom).comp s)) := by
  have hδ := determinantCharacter_eq_one_of_unipotent_cusps (ρ.comp π.ker.subtype)
    (fun v => (hρ v).comp continuous_subtype_val) a b hdense hA hB hBne hirr
  have hker : ∀ h : π.ker, Representation.determinantCharacter ρ h = 1 := by
    intro h
    exact congrArg (fun χ : π.ker →* Kˣ => χ h) hδ
  refine exists_uniform_quadratic_character_of_cusps π hπ hπc ρ
    (ρ.comp α.toMonoidHom) hρ (fun v => (hρ v).comp hα) a b hdense
    hA hB hBne hirr ?_ ?_ ?_ ?_ ?_ ?_ E
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ha] using hB
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hb] using hA
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hb] using hAne
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ha, hb] using
      (fun v hvb hva => hirr v hva hvb)
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_mul, map_mul, ha, hb] using
      (LinearMap.trace_mul_comm K (ρ (a : G)) (ρ (b : G)))
  · exact determinant_eq_comp_of_kernel_trivial π ρ α hπα hker

end HilbertModularity.Hypergeometric
