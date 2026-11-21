/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FamilyInvolution
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Rational and algebraic coefficients for quadratic comparison characters

A square-one character takes only the two rational signs. Its coefficient
realizations therefore come from one rational, hence algebraic, character.
This supplies the coefficient compatibility in
[TripathiGoswami, lem:involution].
-/

@[expose] public noncomputable section

open scoped Classical

namespace MonoidHom

variable {G K : Type*} [Group G] [Field K]

/-- Every value of a square-one field-valued character is a sign. -/
theorem apply_eq_one_or_neg_one_of_sq (χ : G →* Kˣ) (hχ : χ ^ 2 = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have hg : (χ g : K) ^ 2 = 1 := congrArg (fun ψ : G →* Kˣ => (ψ g : K)) hχ
  rcases sq_eq_one_iff.mp hg with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

/-- Realize the two signs of a quadratic character over any coefficient field. -/
def quadraticRealization (χ : G →* Kˣ) (hχ : χ ^ 2 = 1)
    (L : Type*) [Field L] : G →* Lˣ := by
  classical
  refine
    { toFun := fun g => if χ g = 1 then 1 else -1
      map_one' := by simp
      map_mul' := ?_ }
  intro g h
  by_cases hg : χ g = 1
  · simp [map_mul, hg]
  by_cases hh : χ h = 1
  · simp [map_mul, hh, hg]
  have hg' := (apply_eq_one_or_neg_one_of_sq χ hχ g).resolve_left hg
  have hh' := (apply_eq_one_or_neg_one_of_sq χ hχ h).resolve_left hh
  simp only [ite_eq_right hg, ite_eq_right hh]
  simp [map_mul, hg', hh']

/-- The realization has the same explicit sign rule. -/
theorem quadraticRealization_apply (χ : G →* Kˣ) (hχ : χ ^ 2 = 1)
    (L : Type*) [Field L] (g : G) :
    quadraticRealization χ hχ L g = if χ g = 1 then 1 else -1 := by
  classical
  rfl

/-- Every coefficient realization remains quadratic. -/
theorem quadraticRealization_sq (χ : G →* Kˣ) (hχ : χ ^ 2 = 1)
    (L : Type*) [Field L] : quadraticRealization χ hχ L ^ 2 = 1 := by
  classical
  apply MonoidHom.ext
  intro g
  change quadraticRealization χ hχ L g ^ 2 = 1
  rw [quadraticRealization_apply]
  split_ifs <;> simp

/-- Every coefficient realization has finite image. -/
theorem quadraticRealization_finite_range (χ : G →* Kˣ) (hχ : χ ^ 2 = 1)
    (L : Type*) [Field L] : (Set.range (quadraticRealization χ hχ L)).Finite :=
  Representation.finite_range_of_character_sq _ (quadraticRealization_sq χ hχ L)

/-- Mapping an original quadratic character along a coefficient embedding is
exactly its sign realization over the new field. -/
theorem map_eq_quadraticRealization (χ : G →* Kˣ) (hχ : χ ^ 2 = 1)
    {L : Type*} [Field L] (ι : K →+* L) :
    (Units.map ι.toMonoidHom).comp χ = quadraticRealization χ hχ L := by
  classical
  apply MonoidHom.ext
  intro g
  rw [quadraticRealization_apply]
  by_cases hg : χ g = 1
  · simp [hg]
  · have hn := (apply_eq_one_or_neg_one_of_sq χ hχ g).resolve_left hg
    simp only [ite_eq_right hg, MonoidHom.comp_apply]
    apply Units.ext
    simp [hn]

/-- Realizations commute with every subsequent coefficient embedding. -/
theorem map_quadraticRealization (χ : G →* Kˣ) (hχ : χ ^ 2 = 1)
    {L M : Type*} [Field L] [Field M] (ι : L →+* M) :
    (Units.map ι.toMonoidHom).comp (quadraticRealization χ hχ L) =
      quadraticRealization χ hχ M := by
  classical
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.comp_apply, quadraticRealization_apply]
  split_ifs <;> apply Units.ext <;> simp

/-- The realization over the original coefficient field is the original character. -/
theorem quadraticRealization_self (χ : G →* Kˣ) (hχ : χ ^ 2 = 1) :
    quadraticRealization χ hχ K = χ := by
  simpa using (map_eq_quadraticRealization χ hχ (RingHom.id K)).symm

/-- A quadratic character descends to rational coefficients, whose canonical
realization recovers the given characteristic-zero coefficient character. -/
theorem rational_quadraticRealization_recovers [CharZero K]
    (χ : G →* Kˣ) (hχ : χ ^ 2 = 1) :
    (Units.map (algebraMap ℚ K).toMonoidHom).comp (quadraticRealization χ hχ ℚ) = χ := by
  rw [map_quadraticRealization, quadraticRealization_self]

/-- The actual algebraic character in the fixed algebraic closure has compatible
realizations under all pairs of coefficient embeddings. -/
theorem algebraic_quadraticRealization_compatible
    (χ : G →* Kˣ) (hχ : χ ^ 2 = 1)
    {L : Type*} [Field L] (ι : AlgebraicClosure ℚ →+* L) (j : K →+* L) :
    (Units.map ι.toMonoidHom).comp (quadraticRealization χ hχ (AlgebraicClosure ℚ)) =
      (Units.map j.toMonoidHom).comp χ := by
  rw [map_quadraticRealization, map_eq_quadraticRealization]

/-- A continuous quadratic character has locally constant realizations in every
coefficient field, including the rational field and its algebraic closure. -/
theorem quadraticRealization_isLocallyConstant
    [TopologicalSpace G] [TopologicalSpace K] [T2Space K]
    (χ : G →* Kˣ) (hχ : χ ^ 2 = 1) (hc : Continuous χ)
    (L : Type*) [Field L] : IsLocallyConstant (quadraticRealization χ hχ L) := by
  let := (Representation.finite_range_of_character_sq χ hχ).fintype
  have hc' : Continuous (fun g => (⟨χ g, Set.mem_range_self g⟩ : Set.range χ)) :=
    hc.subtype_mk _
  have hlc := (IsLocallyConstant.iff_continuous _).mpr hc'
  exact hlc.comp (fun y : Set.range χ => if y.val = 1 then (1 : Lˣ) else -1)

end MonoidHom

namespace Representation

/-- One rational quadratic character realizes a family comparison and all its
specializations over the original characteristic-zero coefficient field. -/
theorem exists_uniform_rational_quadratic_character
    {K G Γ V W : Type*} [Field K] [CharZero K] [Group G] [Group Γ]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (π : G →* Γ) (ρ : Representation K G V) (σ : Representation K G W)
    (ν : Γ →* Kˣ) (hν : ν ^ 2 = 1)
    (e : ((ofCharacter (ν.comp π)).tprod ρ).Equiv σ) :
    ∃ η : Γ →* ℚˣ, η ^ 2 = 1 ∧ (Set.range η).Finite ∧
      (Units.map (algebraMap ℚ K).toMonoidHom).comp η = ν ∧
      ∀ (s : Γ →* G), π.comp s = MonoidHom.id Γ →
        Nonempty (((ofCharacter ((Units.map (algebraMap ℚ K).toMonoidHom).comp η)).tprod
          (ρ.comp s)).Equiv (σ.comp s)) := by
  refine ⟨ν.quadraticRealization hν ℚ, ν.quadraticRealization_sq hν ℚ,
    ν.quadraticRealization_finite_range hν ℚ,
    ν.rational_quadraticRealization_recovers hν, ?_⟩
  intro s hs
  rw [ν.rational_quadraticRealization_recovers hν]
  exact ⟨characterTensorEquivSpecialization π ρ σ ν e s hs⟩

end Representation

namespace HilbertModularity.Hypergeometric

/-- An arithmetic cusp-swapping involution yields one rational finite-order
character, hence one algebraic character, for the entire family and all sections.
Its realization in the original coefficient field is continuous. -/
theorem exists_uniform_rational_character_of_cusp_involution
    {K G : Type*} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
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
    ∃ η : Γ →* ℚˣ, η ^ 2 = 1 ∧ (Set.range η).Finite ∧ IsLocallyConstant η ∧
      Continuous ((Units.map (algebraMap ℚ K).toMonoidHom).comp η) ∧
      Nonempty (((Representation.ofCharacter
        (((Units.map (algebraMap ℚ K).toMonoidHom).comp η).comp π)).tprod ρ).Equiv
        (ρ.comp α.toMonoidHom)) ∧
      ∀ (s : Γ →* G), π.comp s = MonoidHom.id Γ →
        Nonempty (((Representation.ofCharacter
          ((Units.map (algebraMap ℚ K).toMonoidHom).comp η)).tprod (ρ.comp s)).Equiv
          ((ρ.comp α.toMonoidHom).comp s)) := by
  obtain ⟨ν, hνc, hνsq, _, he, hs⟩ :=
    exists_uniform_quadratic_character_of_cusp_involution π hπ hπc ρ hρ α hα hπα
      a b hdense ha hb hA hB hAne hBne hirr E
  refine ⟨ν.quadraticRealization hνsq ℚ, ν.quadraticRealization_sq hνsq ℚ,
    ν.quadraticRealization_finite_range hνsq ℚ,
    ν.quadraticRealization_isLocallyConstant hνsq hνc ℚ, ?_, ?_, ?_⟩
  · simpa only [ν.rational_quadraticRealization_recovers hνsq] using hνc
  · simpa only [ν.rational_quadraticRealization_recovers hνsq] using he
  · simpa only [ν.rational_quadraticRealization_recovers hνsq] using hs

end HilbertModularity.Hypergeometric
