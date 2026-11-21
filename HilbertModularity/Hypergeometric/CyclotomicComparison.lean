/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicGalois
public import HilbertModularity.Hypergeometric.ReflectionFrobeniusLift
public import HilbertModularity.RepresentationTheory.CharacterComparison

/-! # Quadratic descent from the full cyclotomic field

The arithmetic involution argument in [TripathiGoswami, lem:involution]
first compares restrictions over the full cyclotomic field. Absolute
irreducibility then leaves a finite quadratic character over its real subfield.
The restriction equivalence is an explicit hypothesis here.
-/

@[expose] public noncomputable section

namespace HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] [Fact (1 < N)]

/-- Restriction of an automorphism over the full cyclotomic field lies in the
actual residual cyclotomic kernel. -/
theorem restrictCyclotomicGalois_mem_ker (g : Gal(Qbar/cyclotomicField N)) :
    restrictCyclotomicGalois N g ∈ (residualCharacter N).ker := by
  change (zeta_isPrimitiveRoot N).autToPow (realCyclotomicField N)
    (restrictCyclotomicGalois N g) = 1
  rw [(zeta_isPrimitiveRoot N).autToPow_eq_one_iff]
  exact g.commutes ⟨zeta N, zeta_mem N⟩

/-- A member of the residual kernel is an automorphism over the full cyclotomic
field, with the same action on the fixed algebraic closure. -/
def cyclotomicGaloisOfKernel (g : (residualCharacter N).ker) :
    Gal(Qbar/cyclotomicField N) :=
  { g.val.toRingEquiv with
    commutes' a := by
      have ha : (a : Qbar) ∈
          (IntermediateField.fixedField (residualCharacter N).ker).restrictScalars ℚ := by
        rw [fixedField_ker_residualCharacter N]
        exact a.property
      exact (IntermediateField.mem_fixedField_iff _ _).mp ha g.val g.property }

/-- The absolute Galois group over the full cyclotomic field is the actual
kernel subgroup inside the Galois group over the real subfield. -/
def cyclotomicGaloisEquivKernel :
    Gal(Qbar/cyclotomicField N) ≃* (residualCharacter N).ker where
  toFun g := ⟨restrictCyclotomicGalois N g, restrictCyclotomicGalois_mem_ker N g⟩
  invFun := cyclotomicGaloisOfKernel N
  left_inv g := by ext x; rfl
  right_inv g := by apply Subtype.ext; ext x; rfl
  map_mul' g h := by apply Subtype.ext; exact map_mul (restrictCyclotomicGalois N) g h

/-- The kernel identification preserves the action on the algebraic closure. -/
@[simp] theorem cyclotomicGaloisEquivKernel_apply
    (g : Gal(Qbar/cyclotomicField N)) (x : Qbar) :
    (cyclotomicGaloisEquivKernel N g).val x = g x := rfl

/-- An actual equivalence on the absolute Galois group of the full cyclotomic
field gives an equivalence on its kernel realization in the real Galois group. -/
def kernelRestrictionEquiv {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K (Gal(Qbar/realCyclotomicField N)) W)
    (σ : Representation K (Gal(Qbar/realCyclotomicField N)) V)
    (e : Representation.Equiv (ρ.comp (restrictCyclotomicGalois N))
      (σ.comp (restrictCyclotomicGalois N))) :
    Representation.Equiv (ρ.comp (residualCharacter N).ker.subtype)
      (σ.comp (residualCharacter N).ker.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => by
    have hg : restrictCyclotomicGalois N (cyclotomicGaloisOfKernel N g) = g.val := by
      ext x
      rfl
    have he := e.isIntertwining' (cyclotomicGaloisOfKernel N g)
    change e.toLinearEquiv.toLinearMap.comp (ρ (restrictCyclotomicGalois N
      (cyclotomicGaloisOfKernel N g))) = (σ (restrictCyclotomicGalois N
      (cyclotomicGaloisOfKernel N g))).comp e.toLinearEquiv.toLinearMap at he
    rw [hg] at he
    exact he

/-- Restriction to the kernel and restriction to the full cyclotomic Galois
group have identical invariant subspaces. -/
def cyclotomicRestrictionSubrepresentationEquiv {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    (ρ : Representation K (Gal(Qbar/realCyclotomicField N)) V) :
    Subrepresentation (ρ.comp (residualCharacter N).ker.subtype) ≃o
      Subrepresentation (ρ.comp (restrictCyclotomicGalois N)) where
  toFun W :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule g _ hv :=
        W.apply_mem_toSubmodule (cyclotomicGaloisEquivKernel N g) hv }
  invFun W :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule g _ hv := by
        have hg : restrictCyclotomicGalois N (cyclotomicGaloisOfKernel N g) = g.val := by
          ext x
          rfl
        have h := W.apply_mem_toSubmodule (cyclotomicGaloisOfKernel N g) hv
        change ρ (restrictCyclotomicGalois N (cyclotomicGaloisOfKernel N g)) _ ∈
          W.toSubmodule at h
        rw [hg] at h
        exact h }
  left_inv W := by ext; rfl
  right_inv W := by ext; rfl
  map_rel_iff' := Iff.rfl

/-- Absolute irreducibility is unchanged by realizing the full cyclotomic
Galois group as its actual kernel subgroup. -/
theorem cyclotomicRestriction_baseChange_irreducible_iff
    {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Field E] [Algebra K E]
    (ρ : Representation K (Gal(Qbar/realCyclotomicField N)) V) :
    Representation.IsIrreducible
      (Representation.baseChange E (ρ.comp (residualCharacter N).ker.subtype)) ↔
    Representation.IsIrreducible
      (Representation.baseChange E (ρ.comp (restrictCyclotomicGalois N))) :=
  (cyclotomicRestrictionSubrepresentationEquiv N (ρ.baseChange E)).isSimpleOrder_iff

/-- The quotient cutting out the full cyclotomic field has exponent two. -/
theorem residualQuotient_sq
    (q : Gal(Qbar/realCyclotomicField N) ⧸ (residualCharacter N).ker) : q ^ 2 = 1 := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    change (QuotientGroup.mk' (residualCharacter N).ker) g ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    change residualCharacter N (g ^ 2) = 1
    rw [map_pow]
    exact congrArg (fun χ => χ g) (residualCharacter_sq N)

/-- The quotient by the residual cyclotomic kernel is finite. -/
instance finite_residualQuotient :
    Finite (Gal(Qbar/realCyclotomicField N) ⧸ (residualCharacter N).ker) :=
  Finite.of_injective (QuotientGroup.quotientKerEquivRange (residualCharacter N))
    (QuotientGroup.quotientKerEquivRange (residualCharacter N)).injective

/-- Every character of the cyclotomic quotient is quadratic. -/
theorem residualQuotient_character_sq {A : Type*} [CommGroup A]
    (ν : (Gal(Qbar/realCyclotomicField N) ⧸ (residualCharacter N).ker) →* A) :
    ν ^ 2 = 1 := by
  ext q
  change ν q ^ 2 = 1
  rw [← map_pow, residualQuotient_sq, map_one]

/-- Pullback of a character of the cyclotomic quotient is quadratic. -/
theorem residualQuotient_character_pullback_sq {A : Type*} [CommGroup A]
    (ν : (Gal(Qbar/realCyclotomicField N) ⧸ (residualCharacter N).ker) →* A) :
    (ν.comp (QuotientGroup.mk' (residualCharacter N).ker)) ^ 2 = 1 := by
  ext g
  exact congrArg (fun χ => χ (QuotientGroup.mk g))
    (residualQuotient_character_sq N ν)

omit [Fact (1 < N)] in
/-- Pullback of a character of the cyclotomic quotient has finite image. -/
theorem residualQuotient_character_pullback_finite_range {A : Type*} [Group A]
    (ν : (Gal(Qbar/realCyclotomicField N) ⧸ (residualCharacter N).ker) →* A) :
    (Set.range (ν.comp (QuotientGroup.mk' (residualCharacter N).ker))).Finite := by
  apply (Set.finite_range ν).subset
  rintro y ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- The sign of the actual cyclotomic extension over its real subfield,
with values in an arbitrary coefficient field. -/
def residualSignCharacter (K : Type*) [Field K] :
    Gal(Qbar/realCyclotomicField N) →* Kˣ := by
  classical
  refine
    { toFun := fun g => if residualCharacter N g = 1 then 1 else -1
      map_one' := by simp
      map_mul' := ?_ }
  intro g h
  by_cases hg : residualCharacter N g = 1
  · simp [map_mul, hg]
  by_cases hh : residualCharacter N h = 1
  · simp [map_mul, hh, hg]
  have hg' := (residualCharacter_eq_one_or_neg_one N g).resolve_left hg
  have hh' := (residualCharacter_eq_one_or_neg_one N h).resolve_left hh
  simp only [ite_eq_right hg, ite_eq_right hh]
  simp [map_mul, hg', hh']

/-- The sign is computed by whether the primitive root is fixed. -/
theorem residualSignCharacter_apply (K : Type*) [Field K]
    (g : Gal(Qbar/realCyclotomicField N)) :
    residualSignCharacter N K g =
      if residualCharacter N g = 1 then 1 else -1 := by
  classical
  rfl

/-- The cyclotomic sign character is quadratic. -/
theorem residualSignCharacter_sq (K : Type*) [Field K] :
    residualSignCharacter N K ^ 2 = 1 := by
  classical
  apply MonoidHom.ext
  intro g
  change residualSignCharacter N K g ^ 2 = 1
  rw [residualSignCharacter_apply]
  split_ifs <;> simp

/-- The actual Krull topology makes the cyclotomic sign locally constant. -/
theorem residualSignCharacter_isLocallyConstant (K : Type*) [Field K] :
    IsLocallyConstant (residualSignCharacter N K) := by
  have : Algebra.IsIntegral (realCyclotomicField N) Qbar := Algebra.IsIntegral.tower_top ℚ
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro σ
  have ho := (stabilizer_isOpen_of_isIntegral (K := realCyclotomicField N) (zeta N)).preimage
    (continuous_const.mul continuous_id : Continuous fun τ => σ⁻¹ * τ)
  have hn := ho.mem_nhds (show σ⁻¹ * σ ∈
    MulAction.stabilizer (Gal(Qbar/realCyclotomicField N)) (zeta N) by simp)
  filter_upwards [hn] with τ hτ
  change (σ⁻¹ * τ) (zeta N) = zeta N at hτ
  have heq : τ (zeta N) = σ (zeta N) := by simpa using congrArg σ hτ
  have hiff : residualCharacter N τ = 1 ↔ residualCharacter N σ = 1 := by
    change (zeta_isPrimitiveRoot N).autToPow (realCyclotomicField N) τ = 1 ↔
      (zeta_isPrimitiveRoot N).autToPow (realCyclotomicField N) σ = 1
    rw [(zeta_isPrimitiveRoot N).autToPow_eq_one_iff,
      (zeta_isPrimitiveRoot N).autToPow_eq_one_iff, heq]
  simp only [residualSignCharacter_apply, hiff]

/-- The cyclotomic sign is continuous for every topology on its coefficient field. -/
theorem residualSignCharacter_continuous (K : Type*) [Field K] [TopologicalSpace K] :
    Continuous (residualSignCharacter N K) :=
  (residualSignCharacter_isLocallyConstant N K).continuous

/-- In characteristic zero the sign kernel is exactly the residual cyclotomic
kernel, rather than a larger subgroup. -/
theorem residualSignCharacter_ker (K : Type*) [Field K] [CharZero K] :
    (residualSignCharacter N K).ker = (residualCharacter N).ker := by
  classical
  ext g
  change residualSignCharacter N K g = 1 ↔ residualCharacter N g = 1
  rw [residualSignCharacter_apply]
  by_cases h : residualCharacter N g = 1
  · simp [h]
  · have hn : (-1 : Kˣ) ≠ 1 := by
      intro he
      have hv := congrArg Units.val he
      norm_num at hv
    simp [h, hn]

/-- The explicit sign character cuts out precisely the full cyclotomic field. -/
theorem fixedField_ker_residualSignCharacter (K : Type*) [Field K] [CharZero K] :
    (IntermediateField.fixedField (residualSignCharacter N K).ker).restrictScalars ℚ =
      cyclotomicField N := by
  rw [residualSignCharacter_ker, fixedField_ker_residualCharacter]

/-- Every actual complex conjugation has sign minus one at levels at least three. -/
theorem residualSignCharacter_complexConjugation (K : Type*) [Field K]
    (hN : 3 ≤ N) (ι : Qbar →+* ℂ) (c : Gal(Qbar/realCyclotomicField N))
    (hc : ∀ x, ι (c x) = star (ι x)) : residualSignCharacter N K c = -1 := by
  have : Fact (2 < N) := ⟨by omega⟩
  have hn : (-1 : (ZMod N)ˣ) ≠ 1 := by
    intro h
    exact ZMod.neg_one_ne_one (congrArg Units.val h)
  rw [residualSignCharacter_apply, residualCharacter_complexConjugation N ι c hc,
    ite_eq_right hn]

/-- Every coefficient-field character trivial on the full cyclotomic Galois
group is either trivial or the explicit cyclotomic sign character. -/
theorem character_eq_one_or_residualSign {K : Type*} [Field K]
    (χ : Gal(Qbar/realCyclotomicField N) →* Kˣ)
    (hH : ∀ h : (residualCharacter N).ker, χ h = 1) :
    χ = 1 ∨ χ = residualSignCharacter N K := by
  classical
  by_cases hχ : χ = 1
  · exact Or.inl hχ
  right
  obtain ⟨g, hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra h
    apply hχ
    apply MonoidHom.ext
    intro g
    exact not_not.mp (not_exists.mp h g)
  have hgk : residualCharacter N g ≠ 1 := by
    intro h
    exact hg (hH ⟨g, h⟩)
  have hgsq : χ g ^ 2 = 1 := by
    rw [← map_pow]
    apply hH ⟨g ^ 2, ?_⟩
    change residualCharacter N (g ^ 2) = 1
    rw [map_pow]
    exact congrArg (fun ψ => ψ g) (residualCharacter_sq N)
  have hgneg : χ g = -1 := by
    have hs : (χ g : K) ^ 2 = 1 := congrArg Units.val hgsq
    rcases sq_eq_one_iff.mp hs with h | h
    · exact False.elim (hg (Units.ext h))
    · exact Units.ext h
  apply MonoidHom.ext
  intro h
  rw [residualSignCharacter_apply]
  by_cases hh : residualCharacter N h = 1
  · rw [ite_eq_left hh]
    exact hH ⟨h, hh⟩
  rw [ite_eq_right hh]
  have he : residualCharacter N (h * g⁻¹) = 1 := by
    rw [map_mul, map_inv,
      (residualCharacter_eq_one_or_neg_one N h).resolve_left hh,
      (residualCharacter_eq_one_or_neg_one N g).resolve_left hgk]
    simp
  have hc := hH ⟨h * g⁻¹, he⟩
  change χ (h * g⁻¹) = 1 at hc
  rw [map_mul, map_inv, mul_inv_eq_one] at hc
  exact hc.trans hgneg

/-- Isomorphic absolutely irreducible restrictions over the full cyclotomic
field give an actual tensor-twist equivalence over the real subfield, with a
continuous finite quadratic character over the original coefficient field. -/
theorem exists_quadratic_character_of_cyclotomic_restriction
    {K V W : Type*} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K]
    [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
    [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W] [Nontrivial W]
    (ρ : Representation K (Gal(Qbar/realCyclotomicField N)) W)
    (σ : Representation K (Gal(Qbar/realCyclotomicField N)) V)
    (e : Representation.Equiv (ρ.comp (residualCharacter N).ker.subtype)
      (σ.comp (residualCharacter N).ker.subtype))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ v, Continuous (fun g => σ g v))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible
      (Representation.baseChange E (ρ.comp (residualCharacter N).ker.subtype))] :
    ∃ χ : Gal(Qbar/realCyclotomicField N) →* Kˣ,
      Continuous χ ∧ χ ^ 2 = 1 ∧ (Set.range χ).Finite ∧
      (∀ h : (residualCharacter N).ker, χ h = 1) ∧
      Nonempty (((Representation.ofCharacter χ).tprod ρ).Equiv σ) := by
  obtain ⟨ν, hν, he⟩ := Representation.exists_quotient_character_of_equiv_restriction
    ρ σ (residualCharacter N).ker e hρ hσ E
  refine ⟨ν.comp (QuotientGroup.mk' (residualCharacter N).ker),
    hν.comp continuous_quotient_mk', residualQuotient_character_pullback_sq N ν,
    residualQuotient_character_pullback_finite_range N ν, ?_, he⟩
  intro h
  change ν (QuotientGroup.mk (h : Gal(Qbar/realCyclotomicField N))) = 1
  rw [(QuotientGroup.eq_one_iff _).mpr h.property, map_one]

/-- An actual equivalence after restriction to the absolute Galois group of
the full cyclotomic field descends up to a continuous finite quadratic twist.
Absolute irreducibility is assumed on that same actual restriction. -/
theorem exists_quadratic_character_of_fullCyclotomic_restriction
    {K V W : Type*} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K]
    [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
    [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W] [Nontrivial W]
    (ρ : Representation K (Gal(Qbar/realCyclotomicField N)) W)
    (σ : Representation K (Gal(Qbar/realCyclotomicField N)) V)
    (e : Representation.Equiv (ρ.comp (restrictCyclotomicGalois N))
      (σ.comp (restrictCyclotomicGalois N)))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ v, Continuous (fun g => σ g v))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible
      (Representation.baseChange E (ρ.comp (restrictCyclotomicGalois N)))] :
    ∃ χ : Gal(Qbar/realCyclotomicField N) →* Kˣ,
      Continuous χ ∧ χ ^ 2 = 1 ∧ (Set.range χ).Finite ∧
      (∀ h : (residualCharacter N).ker, χ h = 1) ∧
      Nonempty (((Representation.ofCharacter χ).tprod ρ).Equiv σ) := by
  have : Representation.IsIrreducible
      (Representation.baseChange E (ρ.comp (residualCharacter N).ker.subtype)) :=
    (cyclotomicRestriction_baseChange_irreducible_iff N ρ).mpr inferInstance
  exact exists_quadratic_character_of_cyclotomic_restriction N ρ σ
    (kernelRestrictionEquiv N ρ σ e) hρ hσ E

/-- The only ambiguity in descent from an absolutely irreducible actual
full-cyclotomic restriction is twisting by the explicit cyclotomic sign. -/
theorem equiv_or_residualSign_twist_of_fullCyclotomic_restriction
    {K V W : Type*} [NontriviallyNormedField K] [CharZero K] [CompleteSpace K]
    [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
    [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W] [Nontrivial W]
    (ρ : Representation K (Gal(Qbar/realCyclotomicField N)) W)
    (σ : Representation K (Gal(Qbar/realCyclotomicField N)) V)
    (e : Representation.Equiv (ρ.comp (restrictCyclotomicGalois N))
      (σ.comp (restrictCyclotomicGalois N)))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ v, Continuous (fun g => σ g v))
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    [Representation.IsIrreducible
      (Representation.baseChange E (ρ.comp (restrictCyclotomicGalois N)))] :
    Nonempty (ρ.Equiv σ) ∨
      Nonempty (((Representation.ofCharacter (residualSignCharacter N K)).tprod ρ).Equiv σ) := by
  obtain ⟨χ, _, _, _, hH, ⟨he⟩⟩ :=
    exists_quadratic_character_of_fullCyclotomic_restriction N ρ σ e hρ hσ E
  rcases character_eq_one_or_residualSign N χ hH with h | h
  · subst χ
    left
    let eone := Representation.characterTensorEquiv ρ ρ 1 (LinearEquiv.refl K W)
      (by intro g v; simp)
    exact ⟨eone.symm.trans he⟩
  · rw [h] at he
    exact Or.inr ⟨he⟩

end HilbertModularity.Cyclotomic
