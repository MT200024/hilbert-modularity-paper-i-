/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Algebraic periods of finite characters

Hilbert 90 supplies nonzero algebraic periods of characters factoring through a
finite Galois extension. These are the finite-character periods used in the
weight-zero quotient argument of [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace FiniteCharacter

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A base-field-valued character of a finite extension has a nonzero inverse period. -/
theorem exists_period (χ : Gal(L/K) →* Kˣ) :
    ∃ c : Lˣ, ∀ g : Gal(L/K), g (c : L) * algebraMap K L (χ g : Kˣ) = c := by
  let f : Gal(L/K) → Lˣ := fun g => Units.map (algebraMap K L) (χ g)⁻¹
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    apply Units.ext
    simp [f, AlgEquiv.smul_units_def, mul_comm]
  obtain ⟨c, hc⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨c, fun g => ?_⟩
  have h := congrArg Units.val (hc g)
  have h' : g (c : L) / (c : L) = (algebraMap K L (χ g : Kˣ))⁻¹ := by
    simpa [AlgEquiv.smul_units_def, f] using h
  have hc0 : (c : L) ≠ 0 := c.ne_zero
  have hχ : algebraMap K L (χ g : Kˣ) ≠ 0 :=
    by simp
  field_simp at h'
  simpa [mul_comm, mul_left_comm, mul_assoc] using h'

end FiniteCharacter

namespace MonoidHom

variable {G A : Type*} [Group G] [Group A] [TopologicalSpace G]
  [TopologicalSpace A] [T1Space A]

/-- A continuous character with finite image has open kernel. -/
theorem isOpen_ker_of_finite_range (χ : G →* A) (hχ : Continuous χ)
    (hfin : (Set.range χ).Finite) : IsOpen (χ.ker : Set G) := by
  have hclosed : IsClosed ((Set.range χ) \ {1}) := hfin.sdiff.isClosed
  have heq : (χ.ker : Set G) = χ ⁻¹' (((Set.range χ) \ {1})ᶜ) := by
    ext g
    simp
  rw [heq]
  exact hclosed.isOpen_compl.preimage hχ

end MonoidHom

namespace FiniteCharacter

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]

/-- An open-kernel homomorphism factors through a finite Galois intermediate field. -/
theorem exists_finite_galois_factor {A : Type*} [Group A] (χ : Gal(E/K) →* A)
    (hopen : IsOpen (χ.ker : Set Gal(E/K))) :
    ∃ F : FiniteGaloisIntermediateField K E, ∃ ψ : Gal(F/K) →* A,
      ∀ g, ψ (AlgEquiv.restrictNormalHom F g) = χ g := by
  let H : ClosedSubgroup Gal(E/K) := ⟨χ.ker, χ.ker.isClosed_of_isOpen hopen⟩
  let F : IntermediateField K E := IntermediateField.fixedField H.toSubgroup
  have hfix : F.fixingSubgroup = χ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have : FiniteDimensional K F := (InfiniteGalois.isOpen_iff_finite F).mp (hfix ▸ hopen)
  have : H.toSubgroup.Normal := inferInstanceAs χ.ker.Normal
  have : F.fixingSubgroup.Normal := hfix ▸ (inferInstanceAs χ.ker.Normal)
  have : IsGalois K F := (InfiniteGalois.normal_iff_isGalois F).mp inferInstance
  let e := InfiniteGalois.normalAutEquivQuotient H
  let ψ : Gal(F/K) →* A := (QuotientGroup.lift χ.ker χ le_rfl).comp e.symm.toMonoidHom
  refine ⟨{ F with finiteDimensional := inferInstance, isGalois := inferInstance }, ψ, fun g => ?_⟩
  change (QuotientGroup.lift χ.ker χ le_rfl) (e.symm (e (QuotientGroup.mk g))) = χ g
  rw [e.symm_apply_apply]
  rfl

/-- An open-kernel character of a possibly infinite Galois extension has an algebraic period. -/
theorem exists_period_of_isOpen_ker (χ : Gal(E/K) →* Kˣ)
    (hopen : IsOpen (χ.ker : Set Gal(E/K))) :
    ∃ c : Eˣ, ∀ g : Gal(E/K), g (c : E) * algebraMap K E (χ g : Kˣ) = c := by
  obtain ⟨F, ψ, hψ⟩ := exists_finite_galois_factor χ hopen
  obtain ⟨c, hc⟩ := exists_period ψ
  refine ⟨Units.map F.toIntermediateField.subtype.toMonoidHom c, fun g => ?_⟩
  have h := congrArg (fun x : F => (x : E)) (hc (AlgEquiv.restrictNormalHom F g))
  simpa [hψ, AlgEquiv.restrictNormalHom_apply] using! h

/-- Continuity and finite image supply the algebraic period without a chosen finite factor. -/
theorem exists_period_of_continuous_finite_range [TopologicalSpace Kˣ] [T1Space Kˣ]
    (χ : Gal(E/K) →* Kˣ) (hχ : Continuous χ) (hfin : (Set.range χ).Finite) :
    ∃ c : Eˣ, ∀ g : Gal(E/K), g (c : E) * algebraMap K E (χ g : Kˣ) = c :=
  exists_period_of_isOpen_ker χ (χ.isOpen_ker_of_finite_range hχ hfin)

end FiniteCharacter

namespace MonoidHom

/-- A character killed by a positive power has finite image in a field's units. -/
theorem finite_range_of_pow_eq_one {G K : Type*} [Group G] [Field K]
    (χ : G →* Kˣ) {n : ℕ} (hn : n ≠ 0) (hχ : ∀ g, χ g ^ n = 1) :
    (Set.range χ).Finite := by
  let : NeZero n := ⟨hn⟩
  have hfinite : Finite (rootsOfUnity n K) := inferInstance
  apply (Set.finite_range (fun x : rootsOfUnity n K => (x : Kˣ))).subset
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨χ g, (mem_rootsOfUnity n (χ g)).mpr (hχ g)⟩, rfl⟩

end MonoidHom

namespace FiniteCharacter

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [IsGalois K E]

/-- A continuous finite-order character has a nonzero algebraic inverse period. -/
theorem exists_period_of_continuous_pow_eq_one [TopologicalSpace Kˣ] [T1Space Kˣ]
    (χ : Gal(E/K) →* Kˣ) (hχ : Continuous χ) {n : ℕ} (hn : n ≠ 0)
    (hpow : ∀ g, χ g ^ n = 1) :
    ∃ c : Eˣ, ∀ g : Gal(E/K), g (c : E) * algebraMap K E (χ g : Kˣ) = c :=
  exists_period_of_continuous_finite_range χ hχ (χ.finite_range_of_pow_eq_one hn hpow)

/-- Algebraic periods map to periods in any equivariant overfield, including a completion. -/
theorem exists_period_in_overfield {C : Type*} [Field C] (j : E →+* C)
    (ρ : Gal(E/K) →* (C ≃+* C)) (hρ : ∀ g x, ρ g (j x) = j (g x))
    (χ : Gal(E/K) →* Kˣ) (hopen : IsOpen (χ.ker : Set Gal(E/K))) :
    ∃ c : Cˣ, ∀ g : Gal(E/K), ρ g (c : C) * j (algebraMap K E (χ g : Kˣ)) = c := by
  obtain ⟨c, hc⟩ := exists_period_of_isOpen_ker χ hopen
  refine ⟨Units.map j.toMonoidHom c, fun g => ?_⟩
  simpa [hρ] using congrArg j (hc g)

end FiniteCharacter

namespace MonoidHom

/-- Finite order of a field-valued character as a homomorphism implies finite image. -/
theorem finite_range_of_isOfFinOrder {G K : Type*} [Group G] [Field K]
    (χ : G →* Kˣ) (hχ : IsOfFinOrder χ) : (Set.range χ).Finite := by
  obtain ⟨n, hn, hpow⟩ := hχ.exists_pow_eq_one
  apply χ.finite_range_of_pow_eq_one hn.ne'
  intro g
  simpa using DFunLike.congr_fun hpow g

end MonoidHom
