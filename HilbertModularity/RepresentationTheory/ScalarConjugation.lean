/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Stable subquotients under conjugation of coefficients

Conjugation by a coefficient-field automorphism transports stable subspaces and
quotients through the actual scalar-extension tensor. This is the algebraic part
of coefficient independence in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace Subrepresentation

variable {K G V W : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K G V} {τ : Representation K G W}
  (σ : K ≃+* K)

/-- A semilinear equivalence commuting with the group action transports the
entire lattice of stable subspaces. -/
def semilinearOrderIso
    (e : LinearEquiv (σ : K →+* K) (σ' := (σ.symm : K →+* K)) V W)
    (he : ∀ (g : G) (v : V), e (ρ g v) = τ g (e v)) :
    Subrepresentation ρ ≃o Subrepresentation τ where
  toFun S :=
    { toSubmodule := S.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := fun g w hw => by
        obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
        exact Submodule.mem_map.mpr ⟨ρ g v, S.apply_mem_toSubmodule g hv, he g v⟩ }
  invFun T :=
    { toSubmodule := T.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule := fun g v hv => by
        change e (ρ g v) ∈ T.toSubmodule
        rw [he]
        exact T.apply_mem_toSubmodule g hv }
  left_inv S := toSubmodule_injective (Submodule.comap_map_eq_of_injective e.injective _)
  right_inv T := toSubmodule_injective (Submodule.map_comap_eq_of_surjective e.surjective _)
  map_rel_iff' := Submodule.map_le_map_iff_of_injective e.injective _ _

end Subrepresentation

namespace Rep

variable {K G : Type*} [Field K] [Monoid G]
variable (σ : K ≃+* K) (V : Rep K G)

/-- The canonical semilinear map into the scalar-conjugate representation. -/
def toScalarConjugate : V →ₛₗ[(σ : K →+* K)] scalarConjugate σ V := by
  letI : Algebra K K := σ.toRingHom.toAlgebra
  letI : Module K K := Algebra.toModule
  refine { toFun := fun v => 1 ⊗ₜ[K] v, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    exact TensorProduct.tmul_add _ _ _
  · intro r v
    exact (scalarConjugate_balance σ V r 1 v).trans
      (baseChange_smul_tmul K V (σ r) 1 v).symm

/-- Conjugating coefficients loses no vectors. -/
theorem toScalarConjugate_bijective : Function.Bijective (toScalarConjugate σ V) := by
  let : Algebra K K := σ.toRingHom.toAlgebra
  let : Module K K := Algebra.toModule
  constructor
  · exact Module.Flat.tensorProduct_mk_injective K V K
  · intro z
    change ∃ v, (1 : K) ⊗ₜ[K] v = z
    induction z using TensorProduct.inductionOn with
    | tmul a v =>
        refine ⟨σ.symm a • v, ?_⟩
        rw [Representation.baseChange_balance K]
        change (σ (σ.symm a) * 1) ⊗ₜ[K] v = a ⊗ₜ[K] v
        simp
    | add z w hz hw =>
        obtain ⟨v, rfl⟩ := hz
        obtain ⟨w, rfl⟩ := hw
        exact ⟨v + w, TensorProduct.tmul_add _ _ _⟩

/-- The actual scalar tensor is semilinearly equivalent to the original representation. -/
def scalarConjugateEquiv :
    LinearEquiv (σ : K →+* K) (σ' := (σ.symm : K →+* K)) V (scalarConjugate σ V) :=
  LinearEquiv.ofBijective (toScalarConjugate σ V) (toScalarConjugate_bijective σ V)

/-- The semilinear equivalence commutes with the unchanged group action. -/
theorem scalarConjugateEquiv_apply_action (g : G) (v : V) :
    scalarConjugateEquiv σ V (V.ρ g v) =
      (scalarConjugate σ V).ρ g (scalarConjugateEquiv σ V v) := rfl

/-- Stable subspaces correspond bijectively under the actual coefficient twist. -/
def scalarConjugateSubrepresentationEquiv :
    Subrepresentation V.ρ ≃o Subrepresentation (scalarConjugate σ V).ρ :=
  Subrepresentation.semilinearOrderIso σ (scalarConjugateEquiv σ V)
    (scalarConjugateEquiv_apply_action σ V)

/-- The induced map identifies the corresponding quotient spaces semilinearly. -/
def scalarConjugateQuotientEquiv (S : Subrepresentation V.ρ) :
    LinearEquiv (σ : K →+* K) (σ' := (σ.symm : K →+* K))
      (V ⧸ S.toSubmodule)
      (scalarConjugate σ V ⧸ (scalarConjugateSubrepresentationEquiv σ V S).toSubmodule) :=
  Submodule.Quotient.equiv _ _ (scalarConjugateEquiv σ V) rfl

/-- Conjugating coefficients preserves the rank of every stable quotient. -/
theorem finrank_scalarConjugate_quotient (S : Subrepresentation V.ρ) :
    Module.finrank K (scalarConjugate σ V ⧸
      (scalarConjugateSubrepresentationEquiv σ V S).toSubmodule) =
      Module.finrank K (V ⧸ S.toSubmodule) := by
  let e := scalarConjugateQuotientEquiv σ V S
  have h := lift_rank_eq_of_equiv_equiv σ e.toAddEquiv σ.bijective
    (fun r v => e.map_smulₛₗ r v)
  simpa only [Cardinal.toNat_lift, Module.finrank] using (congrArg Cardinal.toNat h).symm

/-- The quotient correspondence intertwines the induced group actions. -/
theorem scalarConjugateQuotientEquiv_apply_action (S : Subrepresentation V.ρ)
    (g : G) (x : V ⧸ S.toSubmodule) :
    scalarConjugateQuotientEquiv σ V S
      (V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule g x) =
    (scalarConjugate σ V).ρ.quotient
      (scalarConjugateSubrepresentationEquiv σ V S).toSubmodule
      (scalarConjugateSubrepresentationEquiv σ V S).apply_mem_toSubmodule g
      (scalarConjugateQuotientEquiv σ V S x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  change Submodule.Quotient.mk (scalarConjugateEquiv σ V (V.ρ g v)) =
    Submodule.Quotient.mk ((scalarConjugate σ V).ρ g (scalarConjugateEquiv σ V v))
  rw [scalarConjugateEquiv_apply_action]

/-- The existence of a stable quotient of prescribed rank is unchanged by coefficient conjugation. -/
theorem exists_quotient_finrank_scalarConjugate_iff (n : ℕ) :
    (∃ T : Subrepresentation (scalarConjugate σ V).ρ,
      Module.finrank K (scalarConjugate σ V ⧸ T.toSubmodule) = n) ↔
    ∃ S : Subrepresentation V.ρ, Module.finrank K (V ⧸ S.toSubmodule) = n := by
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨S, rfl⟩ := (scalarConjugateSubrepresentationEquiv σ V).surjective T
    exact ⟨S, (finrank_scalarConjugate_quotient σ V S).symm.trans hT⟩
  · rintro ⟨S, hS⟩
    exact ⟨scalarConjugateSubrepresentationEquiv σ V S,
      (finrank_scalarConjugate_quotient σ V S).trans hS⟩

end Rep
