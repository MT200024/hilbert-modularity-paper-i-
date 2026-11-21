/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.OrdinaryFlag
public import HilbertModularity.RepresentationTheory.DeterminantCharacter
public import HilbertModularity.RepresentationTheory.Products
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Fixed lines in two-dimensional representations

A nonzero fixed vector gives a trivial constituent. The determinant then
identifies the character of the one-dimensional quotient. These are the
representation-theoretic steps in [TripathiGoswami, residual representation].
-/

@[expose] public noncomputable section

namespace Subrepresentation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {ρ : Representation K G V} (S : Subrepresentation ρ)
  (bS : Module.Basis (Fin 1) K S.toSubmodule)
  (bQ : Module.Basis (Fin 1) K (V ⧸ S.toSubmodule))

/-- In an adapted two-vector basis, the determinant is the product of the
characters on the invariant line and its quotient. -/
theorem determinantCharacter_eq_mul :
    ρ.determinantCharacter = Representation.characterOfBasis S.toRepresentation bS *
      Representation.characterOfBasis
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) bQ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change LinearMap.det (ρ g) = _
  rw [← LinearMap.det_toMatrix (ordinaryBasis S bS bQ), Matrix.det_fin_two,
    toMatrix_ordinaryBasis_upper_left, toMatrix_ordinaryBasis_lower_right,
    toMatrix_ordinaryBasis_lower_left]
  simp

end Subrepresentation

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V) (v : V) (hfix : ∀ g, ρ g v = v)

/-- The actual invariant line spanned by a fixed vector. -/
def fixedLine : Subrepresentation ρ where
  toSubmodule := K ∙ v
  apply_mem_toSubmodule g w hw := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hfix]
    exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩

/-- The action on the entire fixed line is trivial. -/
theorem fixedLine_apply (g : G) (w : fixedLine ρ v hfix) :
    (fixedLine ρ v hfix).toRepresentation g w = w := by
  apply Subtype.ext
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp w.property
  change ρ g (w : V) = w
  rw [← ha, map_smul, hfix]

/-- A nonzero fixed vector spans a one-dimensional invariant subspace. -/
theorem finrank_fixedLine (hv : v ≠ 0) :
    Module.finrank K (fixedLine ρ v hfix).toSubmodule = 1 :=
  finrank_span_singleton hv

/-- Its quotient in a two-dimensional representation is one-dimensional. -/
theorem finrank_quotient_fixedLine [FiniteDimensional K V]
    (hv : v ≠ 0) (hV : Module.finrank K V = 2) :
    Module.finrank K (V ⧸ (fixedLine ρ v hfix).toSubmodule) = 1 := by
  have h := (fixedLine ρ v hfix).toSubmodule.finrank_quotient_add_finrank
  rw [finrank_fixedLine ρ v hfix hv, hV] at h
  omega

/-- Every one-vector basis of the fixed line gives the trivial character. -/
theorem characterOfBasis_fixedLine
    (b : Module.Basis (Fin 1) K (fixedLine ρ v hfix).toSubmodule) :
    characterOfBasis (fixedLine ρ v hfix).toRepresentation b = 1 := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  rw [characterOfBasis_apply, fixedLine_apply]
  simp

/-- The quotient character is the determinant of the original rank-two action. -/
theorem characterOfBasis_quotient_fixedLine
    (b : Module.Basis (Fin 1) K (fixedLine ρ v hfix).toSubmodule)
    (c : Module.Basis (Fin 1) K (V ⧸ (fixedLine ρ v hfix).toSubmodule)) :
    characterOfBasis
      (ρ.quotient (fixedLine ρ v hfix).toSubmodule
        (fixedLine ρ v hfix).apply_mem_toSubmodule) c = ρ.determinantCharacter := by
  have h := (fixedLine ρ v hfix).determinantCharacter_eq_mul b c
  apply MonoidHom.ext
  intro g
  have hh := congrArg (fun f : G →* Kˣ => f g) h.symm
  simpa only [MonoidHom.mul_apply, characterOfBasis_fixedLine, MonoidHom.one_apply,
    _root_.one_mul] using hh

/-- The fixed line is equivariantly the trivial character line. -/
def fixedLineEquiv (b : Module.Basis (Fin 1) K (fixedLine ρ v hfix).toSubmodule) :
    (fixedLine ρ v hfix).toRepresentation.Equiv (ofCharacter (1 : G →* Kˣ)) := by
  have e := characterOfBasisEquiv (fixedLine ρ v hfix).toRepresentation b
  rw [characterOfBasis_fixedLine] at e
  exact e

/-- The actual quotient by a fixed line is equivariantly the determinant character line. -/
def quotientFixedLineEquiv
    (b : Module.Basis (Fin 1) K (fixedLine ρ v hfix).toSubmodule)
    (c : Module.Basis (Fin 1) K (V ⧸ (fixedLine ρ v hfix).toSubmodule)) :
    (ρ.quotient (fixedLine ρ v hfix).toSubmodule
      (fixedLine ρ v hfix).apply_mem_toSubmodule).Equiv (ofCharacter ρ.determinantCharacter) := by
  have e := characterOfBasisEquiv
    (ρ.quotient (fixedLine ρ v hfix).toSubmodule
      (fixedLine ρ v hfix).apply_mem_toSubmodule) c
  rw [characterOfBasis_quotient_fixedLine ρ v hfix b c] at e
  exact e

omit v hfix in
/-- Every one-dimensional representation is irreducible, over any coefficient field. -/
theorem isIrreducible_of_finrank_eq_one (h : Module.finrank K V = 1) : ρ.IsIrreducible := by
  apply (ρ.irreducible_iff_isSimpleModule_asModule).mpr
  apply (isSimpleModule_iff _ _).mpr
  exact is_simple_module_of_finrank_eq_one (K := K) (ρ.asModuleEquiv.finrank_eq.trans h)

end Representation



namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (ρ : Representation K G V)

/-- A nonzero fixed vector in rank two gives the actual two irreducible factors:
the trivial line and the determinant character. Their direct sum is the
associated graded of this invariant flag. -/
theorem exists_fixedLine_factors (hV : Module.finrank K V = 2)
    (v : V) (hv : v ≠ 0) (hfix : ∀ g, ρ g v = v) :
    ∃ S : Subrepresentation ρ,
      Module.finrank K S.toSubmodule = 1 ∧
      Module.finrank K (V ⧸ S.toSubmodule) = 1 ∧
      S.toRepresentation.IsIrreducible ∧
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).IsIrreducible ∧
      Nonempty ((S.toRepresentation.prod
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((ofCharacter (1 : G →* Kˣ)).prod (ofCharacter ρ.determinantCharacter))) := by
  let S := fixedLine ρ v hfix
  have hS : Module.finrank K S.toSubmodule = 1 := finrank_fixedLine ρ v hfix hv
  have hQ : Module.finrank K (V ⧸ S.toSubmodule) = 1 :=
    finrank_quotient_fixedLine ρ v hfix hv hV
  let b := Module.finBasisOfFinrankEq K S.toSubmodule hS
  let c := Module.finBasisOfFinrankEq K (V ⧸ S.toSubmodule) hQ
  exact ⟨S, hS, hQ, S.toRepresentation.isIrreducible_of_finrank_eq_one hS,
    (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).isIrreducible_of_finrank_eq_one hQ,
    ⟨(fixedLineEquiv ρ v hfix b).prod (quotientFixedLineEquiv ρ v hfix b c)⟩⟩

end Representation

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V)

/-- The associated graded of a fixed-line flag in rank two is semisimple. -/
theorem isSemisimple_fixedLine_factors [FiniteDimensional K V]
    (hV : Module.finrank K V = 2) (v : V) (hv : v ≠ 0) (hfix : ∀ g, ρ g v = v) :
    ((fixedLine ρ v hfix).toRepresentation.prod
      (ρ.quotient (fixedLine ρ v hfix).toSubmodule
        (fixedLine ρ v hfix).apply_mem_toSubmodule)).IsSemisimpleRepresentation := by
  let := (fixedLine ρ v hfix).toRepresentation.isIrreducible_of_finrank_eq_one
    (finrank_fixedLine ρ v hfix hv)
  let := (ρ.quotient (fixedLine ρ v hfix).toSubmodule
    (fixedLine ρ v hfix).apply_mem_toSubmodule).isIrreducible_of_finrank_eq_one
      (finrank_quotient_fixedLine ρ v hfix hv hV)
  exact isSemisimple_prod _ _

end Representation
