/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterComparison
public import HilbertModularity.RepresentationTheory.CharacterTwist
public import HilbertModularity.Monodromy.CuspInvolution
public import HilbertModularity.Monodromy.AbsoluteIrreducibility
public import Mathlib.LinearAlgebra.Determinant

/-! # A uniform finite comparison character for specializations

The parameter-independent character in [TripathiGoswami, lem:involution]
comes from a comparison of the whole family. Equal rank-two determinants
force that character to be quadratic. Specialization along any section of
the same arithmetic quotient preserves this one character.
-/

@[expose] public noncomputable section

namespace Representation

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Equivalent representations have the same determinant at each group element. -/
theorem Equiv.determinant_eq {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) (g : G) : LinearMap.det (ρ g) = LinearMap.det (σ g) := by
  rw [← e.conj_apply_self g]
  exact (LinearMap.det_conj (ρ g) e.toLinearEquiv).symm

/-- Equal determinants force a rank-two tensor-comparison character to be quadratic. -/
theorem character_sq_of_tensor_equiv
    (ρ : Representation K G V) (σ : Representation K G W) (χ : G →* Kˣ)
    (e : ((ofCharacter χ).tprod ρ).Equiv σ)
    (hdim : Module.finrank K V = 2)
    (hdet : ∀ g, LinearMap.det (ρ g) = LinearMap.det (σ g)) : χ ^ 2 = 1 := by
  let e' := (characterTwistTensorEquiv ρ χ).symm.trans e
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change (χ g : K) ^ 2 = 1
  have h := e'.determinant_eq g
  change LinearMap.det ((χ g : K) • ρ g) = LinearMap.det (σ g) at h
  rw [LinearMap.det_smul, hdim, ← hdet g] at h
  have hd : LinearMap.det (ρ g) ≠ 0 :=
    (MonoidHom.toHomUnits (LinearMap.det.comp ρ) g).ne_zero
  exact (mul_right_cancel₀ hd (h.trans (one_mul _).symm))

/-- A quadratic character over a field has finite image, contained in the two signs. -/
theorem finite_range_of_character_sq (χ : G →* Kˣ) (hχ : χ ^ 2 = 1) :
    (Set.range χ).Finite := by
  apply ((Set.finite_singleton (-1 : Kˣ)).insert 1).subset
  rintro y ⟨g, rfl⟩
  have hg : (χ g : K) ^ 2 = 1 :=
    congrArg (fun ψ : G →* Kˣ => (ψ g : K)) hχ
  rcases sq_eq_one_iff.mp hg with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl (Units.ext h))
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (Units.ext h)))

/-- A family-level tensor comparison specializes along a section of the
arithmetic quotient with exactly the same quotient character. -/
def characterTensorEquivSpecialization {Γ : Type*} [Group Γ]
    (π : G →* Γ) (ρ : Representation K G V) (σ : Representation K G W)
    (ν : Γ →* Kˣ) (e : ((ofCharacter (ν.comp π)).tprod ρ).Equiv σ)
    (s : Γ →* G) (hs : π.comp s = MonoidHom.id Γ) :
    ((ofCharacter ν).tprod (ρ.comp s)).Equiv (σ.comp s) :=
  Equiv.mk e.toLinearEquiv fun g => by
    have hg : π (s g) = g := congrArg (fun f : Γ →* Γ => f g) hs
    have he := e.isIntertwining' (s g)
    simpa only [tprod_apply, ofCharacter, MonoidHom.comp_apply, hg] using he

/-- A rank-two family comparison with equal determinants supplies one continuous
finite quadratic character for every specialization along the arithmetic quotient.
The actual family, quotient, geometric restriction equivalence and determinants
are hypotheses; no geometric or trace comparison is hidden in this conclusion. -/
theorem exists_uniform_quadratic_character
    {K G Γ V W : Type*} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K]
    [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ]
    [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W]
    (π : G →* Γ) (hπ : Function.Surjective π) (hπc : Continuous π)
    (ρ : Representation K G V) (σ : Representation K G W)
    (e : Representation.Equiv (ρ.comp π.ker.subtype) (σ.comp π.ker.subtype))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ v, Continuous (fun g => σ g v))
    (hdim : Module.finrank K V = 2)
    (hdet : ∀ g, LinearMap.det (ρ g) = LinearMap.det (σ g))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible (Representation.baseChange E (ρ.comp π.ker.subtype))] :
    ∃ ν : Γ →* Kˣ, Continuous ν ∧ ν ^ 2 = 1 ∧ (Set.range ν).Finite ∧
      Nonempty (((ofCharacter (ν.comp π)).tprod ρ).Equiv σ) ∧
      ∀ (s : Γ →* G), π.comp s = MonoidHom.id Γ →
        Nonempty (((ofCharacter ν).tprod (ρ.comp s)).Equiv (σ.comp s)) := by
  obtain ⟨ν, hν, ⟨he⟩⟩ :=
    exists_character_of_equiv_kernel_restriction π hπ hπc ρ σ e hρ hσ E
  have hsq := character_sq_of_tensor_equiv ρ σ (ν.comp π) he hdim hdet
  have hνsq : ν ^ 2 = 1 := by
    apply MonoidHom.ext
    intro γ
    obtain ⟨g, rfl⟩ := hπ γ
    exact congrArg (fun χ : G →* Kˣ => χ g) hsq
  refine ⟨ν, hν, hνsq, finite_range_of_character_sq ν hνsq, ⟨he⟩, ?_⟩
  intro s hs
  exact ⟨characterTensorEquivSpecialization π ρ σ ν he s hs⟩

end Representation

namespace HilbertModularity.Hypergeometric

/-- Two rank-two families with the same irreducible unipotent cusp data and
determinant have one finite quadratic comparison character at every section.
The geometric restriction equivalence and absolute irreducibility are both
derived from the cusp data. -/
theorem exists_uniform_quadratic_character_of_cusps
    {K G Γ : Type*} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K]
    [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ]
    (π : G →* Γ) (hπ : Function.Surjective π) (hπc : Continuous π)
    (ρ σ : Representation K G (Fin 2 → K))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ v, Continuous (fun g => σ g v))
    (a b : π.ker) (hdense : Dense (Subgroup.closure ({a, b} : Set π.ker) : Set π.ker))
    (hA : (ρ a - 1) ^ 2 = 0) (hB : (ρ b - 1) ^ 2 = 0) (hBne : ρ b ≠ 1)
    (hirr : ∀ v, ρ a v = v → ρ b v = v → v = 0)
    (hA' : (σ a - 1) ^ 2 = 0) (hB' : (σ b - 1) ^ 2 = 0) (hBne' : σ b ≠ 1)
    (hirr' : ∀ v, σ a v = v → σ b v = v → v = 0)
    (ht : LinearMap.trace K (Fin 2 → K) (ρ ((a * b : π.ker) : G)) =
      LinearMap.trace K (Fin 2 → K) (σ ((a * b : π.ker) : G)))
    (hdet : ∀ g, LinearMap.det (ρ g) = LinearMap.det (σ g))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E] :
    ∃ ν : Γ →* Kˣ, Continuous ν ∧ ν ^ 2 = 1 ∧ (Set.range ν).Finite ∧
      Nonempty (((Representation.ofCharacter (ν.comp π)).tprod ρ).Equiv σ) ∧
      ∀ (s : Γ →* G), π.comp s = MonoidHom.id Γ →
        Nonempty (((Representation.ofCharacter ν).tprod (ρ.comp s)).Equiv (σ.comp s)) := by
  have : Representation.IsIrreducible
      (Representation.baseChange E (ρ.comp π.ker.subtype)) :=
    Monodromy.isIrreducible_baseChange_of_unipotent_cusps E
      (ρ.comp π.ker.subtype) a b hA hB hBne hirr
  obtain ⟨e⟩ := Monodromy.nonempty_equiv_of_unipotent_cusps
    (ρ.comp π.ker.subtype) (σ.comp π.ker.subtype)
    (fun v => (hρ v).comp continuous_subtype_val)
    (fun v => (hσ v).comp continuous_subtype_val)
    a b hdense hA hB hBne hirr hA' hB' hBne' hirr' ht
  exact Representation.exists_uniform_quadratic_character π hπ hπc ρ σ e hρ hσ
    (by simp) hdet E

end HilbertModularity.Hypergeometric
