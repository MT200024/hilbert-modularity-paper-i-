/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterComparison
public import HilbertModularity.RepresentationTheory.Quotient
public import Mathlib.RepresentationTheory.Semisimple

/-! # Character twists and stable quotients

Multiplication of the action by a character preserves the lattice of stable
subspaces. The resulting quotient is the character twist of the original
quotient. These are the algebraic steps in the finite-twist argument of
[TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- Multiply a representation's action by a scalar character. -/
def characterTwist (ρ : Representation K G V) (χ : G →* Kˣ) :
    Representation K G V where
  toFun g := (χ g : K) • ρ g
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

@[simp]
theorem characterTwist_apply (ρ : Representation K G V) (χ : G →* Kˣ)
    (g : G) (v : V) : characterTwist ρ χ g v = (χ g : K) • ρ g v := rfl

/-- The scalar-action model is canonically the tensor product with the
one-dimensional character representation. -/
def characterTwistTensorEquiv (ρ : Representation K G V) (χ : G →* Kˣ) :
    ((ofCharacter χ).tprod ρ).Equiv (characterTwist ρ χ) :=
  characterTensorEquiv ρ (characterTwist ρ χ) χ (LinearEquiv.refl K V)
    (fun _ _ => rfl)

/-- Twisting changes the action, but leaves precisely the same subspaces stable. -/
def characterTwistSubrepresentationEquiv (ρ : Representation K G V) (χ : G →* Kˣ) :
    Subrepresentation ρ ≃o Subrepresentation (characterTwist ρ χ) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g v hv =>
        S.toSubmodule.smul_mem (χ g : K) (S.apply_mem_toSubmodule g hv) }
  invFun T :=
    { toSubmodule := T.toSubmodule
      apply_mem_toSubmodule := fun g v hv => by
        have h := T.toSubmodule.smul_mem ((χ g)⁻¹ : Kˣ).val
          (T.apply_mem_toSubmodule g hv)
        simpa only [characterTwist_apply, smul_smul, Units.inv_mul, one_smul] using h }
  left_inv S := by apply Subrepresentation.toSubmodule_injective; rfl
  right_inv T := by apply Subrepresentation.toSubmodule_injective; rfl
  map_rel_iff' := Iff.rfl

/-- The quotient vector space is unchanged by a character twist. -/
@[simp]
theorem characterTwistSubrepresentationEquiv_toSubmodule
    (ρ : Representation K G V) (χ : G →* Kˣ) (S : Subrepresentation ρ) :
    (characterTwistSubrepresentationEquiv ρ χ S).toSubmodule = S.toSubmodule := rfl

/-- Passing to a stable quotient commutes with the actual scalar character action. -/
def characterTwistQuotientEquiv (ρ : Representation K G V) (χ : G →* Kˣ)
    (S : Subrepresentation ρ) :
    ((characterTwist ρ χ).quotient
      (characterTwistSubrepresentationEquiv ρ χ S).toSubmodule
      (characterTwistSubrepresentationEquiv ρ χ S).apply_mem_toSubmodule).Equiv
      (characterTwist (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ) :=
  .mk (LinearEquiv.refl K (V ⧸ S.toSubmodule)) (by
    intro g
    ext x
    rfl)

/-- Tensoring with a character gives an order isomorphism on stable subspaces. -/
def characterTensorSubrepresentationEquiv (ρ : Representation K G V) (χ : G →* Kˣ) :
    Subrepresentation ρ ≃o Subrepresentation ((ofCharacter χ).tprod ρ) :=
  (characterTwistSubrepresentationEquiv ρ χ).trans
    (characterTwistTensorEquiv ρ χ).symm.subrepresentationOrderIso

/-- Every corresponding tensor quotient is the tensor twist of the original quotient. -/
def characterTensorQuotientEquiv (ρ : Representation K G V) (χ : G →* Kˣ)
    (S : Subrepresentation ρ) :
    (((ofCharacter χ).tprod ρ).quotient
      (characterTensorSubrepresentationEquiv ρ χ S).toSubmodule
      (characterTensorSubrepresentationEquiv ρ χ S).apply_mem_toSubmodule).Equiv
      ((ofCharacter χ).tprod (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)) :=
  ((characterTwistTensorEquiv ρ χ).symm.quotientCongr
    (characterTwistSubrepresentationEquiv ρ χ S)).symm.trans
    ((characterTwistQuotientEquiv ρ χ S).trans
      (characterTwistTensorEquiv (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) χ).symm)

/-- Tensoring with a character preserves the dimension of each corresponding quotient. -/
theorem finrank_characterTensor_quotient (ρ : Representation K G V) (χ : G →* Kˣ)
    (S : Subrepresentation ρ) :
    Module.finrank K ((K ⊗[K] V) ⧸
      (characterTensorSubrepresentationEquiv ρ χ S).toSubmodule) =
      Module.finrank K (V ⧸ S.toSubmodule) :=
  ((characterTensorQuotientEquiv ρ χ S).toLinearEquiv.trans
    (_root_.TensorProduct.lid K (V ⧸ S.toSubmodule))).finrank_eq

/-- Tensoring by a character preserves existence of stable quotients of any rank. -/
theorem exists_quotient_finrank_characterTensor_iff
    (ρ : Representation K G V) (χ : G →* Kˣ) (n : ℕ) :
    (∃ T : Subrepresentation ((ofCharacter χ).tprod ρ),
      Module.finrank K ((K ⊗[K] V) ⧸ T.toSubmodule) = n) ↔
      ∃ S : Subrepresentation ρ, Module.finrank K (V ⧸ S.toSubmodule) = n := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨S, rfl⟩ := (characterTensorSubrepresentationEquiv ρ χ).surjective T
    exact ⟨S, (finrank_characterTensor_quotient ρ χ S).symm.trans hT⟩
  · rintro ⟨S, hS⟩
    exact ⟨characterTensorSubrepresentationEquiv ρ χ S,
      (finrank_characterTensor_quotient ρ χ S).trans hS⟩

/-- Character twists preserve semisimplicity because they preserve the lattice
of invariant subspaces and its complements. -/
theorem isSemisimple_characterTwist_iff (ρ : Representation K G V) (χ : G →* Kˣ) :
    (characterTwist ρ χ).IsSemisimpleRepresentation ↔ ρ.IsSemisimpleRepresentation :=
  (OrderIso.complementedLattice_iff (characterTwistSubrepresentationEquiv ρ χ)).symm

/-- Tensoring with a character line preserves semisimplicity. -/
theorem isSemisimple_characterTensor_iff (ρ : Representation K G V) (χ : G →* Kˣ) :
    ((ofCharacter χ).tprod ρ).IsSemisimpleRepresentation ↔ ρ.IsSemisimpleRepresentation :=
  (OrderIso.complementedLattice_iff (characterTensorSubrepresentationEquiv ρ χ)).symm

end Representation
