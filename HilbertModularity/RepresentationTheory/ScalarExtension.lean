/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Extension and conjugation of representation coefficients

Scalar extension leaves the acting group unchanged. We place the coefficient
factor first, as in mathlib's `LinearMap.baseChange`; tensor commutation gives
the convention with the representation factor first used in
[TripathiGoswami, coefficient-label lemma].
-/

@[expose] public section

open scoped TensorProduct

namespace Representation

variable {R G V : Type*} [CommSemiring R] [Monoid G] [AddCommMonoid V] [Module R V]

/-- Extend the coefficients of a representation, with the group acting only
on the original representation factor. -/
noncomputable def baseChange (A : Type*) [CommSemiring A] [Algebra R A]
    (ρ : Representation R G V) : Representation A G (A ⊗[R] V) where
  toFun g := (ρ g).baseChange A
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' g h := by rw [map_mul, LinearMap.baseChange_mul]

/-- The extended action fixes the coefficient tensorand. -/
@[simp] theorem baseChange_tmul (A : Type*) [CommSemiring A] [Algebra R A]
    (ρ : Representation R G V) (g : G) (a : A) (v : V) :
    baseChange A ρ g (a ⊗ₜ[R] v) = a ⊗ₜ[R] ρ g v := rfl

/-- The balancing relation for extension of scalars uses the algebra map. -/
theorem baseChange_balance (A : Type*) [CommSemiring A] [Algebra R A]
    (r : R) (a : A) (v : V) :
    a ⊗ₜ[R] (r • v) = (algebraMap R A r * a) ⊗ₜ[R] v := by
  rw [← TensorProduct.smul_tmul, Algebra.smul_def]

namespace IntertwiningMap

variable {W : Type*} [AddCommMonoid W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Extend an intertwining map along with the representation coefficients. -/
noncomputable def baseChange (A : Type*) [CommSemiring A] [Algebra R A]
    (f : IntertwiningMap ρ σ) :
    IntertwiningMap (ρ.baseChange A) (σ.baseChange A) where
  toLinearMap := f.toLinearMap.baseChange A
  isIntertwining' g := by
    change f.toLinearMap.baseChange A ∘ₗ (ρ g).baseChange A =
      (σ g).baseChange A ∘ₗ f.toLinearMap.baseChange A
    have h := congrArg (fun f : V →ₗ[R] W => f.baseChange A) (f.isIntertwining' g)
    simpa only [LinearMap.baseChange_comp] using h

/-- Scalar extension of an intertwiner acts on the representation tensorand. -/
@[simp] theorem baseChange_tmul (A : Type*) [CommSemiring A] [Algebra R A]
    (f : IntertwiningMap ρ σ) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ[R] v) = a ⊗ₜ[R] f v := rfl

end IntertwiningMap

end Representation

namespace Rep

variable {R G : Type*} [CommRing R] [Monoid G]

/-- The bundled scalar extension carries its target-field module structure
explicitly, including when source and target fields have the same underlying type. -/
noncomputable def baseChange (A : Type*) [CommRing A] [Algebra R A]
    (V : Rep R G) : Rep A G :=
  Rep.of (Representation.baseChange A V.ρ)

/-- Target coefficients act by multiplication on the coefficient tensorand. -/
@[simp] theorem baseChange_smul_tmul (A : Type*) [CommRing A] [Algebra R A]
    (V : Rep R G) (a b : A) (v : V) :
    a • (b ⊗ₜ[R] v : baseChange A V) = (a * b) ⊗ₜ[R] v :=
  TensorProduct.smul_tmul' _ _ _

/-- Scalar extension preserves finite generation. -/
instance baseChange_finite (A : Type*) [CommRing A] [Algebra R A]
    (V : Rep R G) [Module.Finite R V] : Module.Finite A (baseChange A V) :=
  inferInstanceAs (Module.Finite A (A ⊗[R] V))

/-- Scalar extension preserves the dimension of a free representation. -/
theorem finrank_baseChange (A : Type*) [CommRing A] [Algebra R A]
    [StrongRankCondition R] [StrongRankCondition A]
    (V : Rep R G) [Module.Free R V] :
    Module.finrank A (baseChange A V) = Module.finrank R V :=
  Module.finrank_baseChange

/-- Conjugation of coefficients by a ring automorphism is extension along
that automorphism. The acting group remains `G`. -/
noncomputable def scalarConjugate (σ : R ≃+* R) (V : Rep R G) : Rep R G :=
  letI : Algebra R R := σ.toRingHom.toAlgebra
  baseChange R V

/-- Scalar conjugation acts on pure tensors through the original representation. -/
@[simp] theorem scalarConjugate_tmul (σ : R ≃+* R) (V : Rep R G)
    (g : G) (a : R) (v : V) :
    letI : Algebra R R := σ.toRingHom.toAlgebra
    letI : Module R R := Algebra.toModule
    (scalarConjugate σ V).ρ g (a ⊗ₜ[R] v) = a ⊗ₜ[R] V.ρ g v := rfl

/-- The tensor relation uses the specified automorphism on coefficients. -/
theorem scalarConjugate_balance (σ : R ≃+* R) (V : Rep R G) (r a : R) (v : V) :
    letI : Algebra R R := σ.toRingHom.toAlgebra
    letI : Module R R := Algebra.toModule
    a ⊗ₜ[R] (r • v) = (σ r * a) ⊗ₜ[R] v := by
  let : Algebra R R := σ.toRingHom.toAlgebra
  let : Module R R := Algebra.toModule
  exact Representation.baseChange_balance R r a v

/-- After commuting the tensor factors, the action is on the first factor,
as in `V ⊗_{R,σ} R`. -/
theorem scalarConjugate_comm_tmul (σ : R ≃+* R) (V : Rep R G)
    (g : G) (a : R) (v : V) :
    letI : Algebra R R := σ.toRingHom.toAlgebra
    letI : Module R R := Algebra.toModule
    TensorProduct.comm R R V ((scalarConjugate σ V).ρ g (a ⊗ₜ[R] v)) =
      V.ρ g v ⊗ₜ[R] a := by
  let : Algebra R R := σ.toRingHom.toAlgebra
  let : Module R R := Algebra.toModule
  rw [scalarConjugate_tmul, TensorProduct.comm_tmul]

/-- Conjugation of coefficients preserves finite generation. -/
instance scalarConjugate_finite (σ : R ≃+* R) (V : Rep R G) [Module.Finite R V] :
    Module.Finite R (scalarConjugate σ V) := by
  let : Algebra R R := σ.toRingHom.toAlgebra
  exact baseChange_finite R V

/-- Conjugation of a field representation preserves its dimension; the
statement also applies to free modules over suitable commutative rings. -/
theorem finrank_scalarConjugate [StrongRankCondition R]
    (σ : R ≃+* R) (V : Rep R G) [Module.Free R V] :
    Module.finrank R (scalarConjugate σ V) = Module.finrank R V := by
  let : Algebra R R := σ.toRingHom.toAlgebra
  exact finrank_baseChange R V

end Rep

namespace Subrepresentation

variable {R G V : Type*} [CommSemiring R] [Monoid G] [AddCommMonoid V] [Module R V]
  {ρ : Representation R G V}

/-- Extend a stable subspace along with its ambient representation. -/
noncomputable def baseChange (A : Type*) [CommSemiring A] [Algebra R A]
    (S : Subrepresentation ρ) : Subrepresentation (ρ.baseChange A) :=
  (Representation.IntertwiningMap.baseChange A
    ({ toLinearMap := S.toSubmodule.subtype
       isIntertwining' _ := rfl } : S.toRepresentation.IntertwiningMap ρ)).range

/-- The underlying subspace is the usual scalar extension of a submodule. -/
@[simp]
theorem baseChange_toSubmodule (A : Type*) [CommSemiring A] [Algebra R A]
    (S : Subrepresentation ρ) : (S.baseChange A).toSubmodule = S.toSubmodule.baseChange A := rfl

end Subrepresentation

namespace Representation

variable {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
  (A : Type*) [CommRing A] [Algebra R A] {ρ : Representation R G V}

/-- Taking a stable quotient commutes with extension of coefficients, equivariantly. -/
noncomputable def quotientBaseChangeEquiv (S : Subrepresentation ρ) :
    ((ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).baseChange A).Equiv
      ((ρ.baseChange A).quotient (S.baseChange A).toSubmodule
        (S.baseChange A).apply_mem_toSubmodule) :=
  Representation.Equiv.mk
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv A R A S.toSubmodule) (by
      intro g
      ext v
      rfl)

end Representation

namespace Representation

variable {K L M G V : Type*} [CommSemiring K] [CommSemiring L] [CommSemiring M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [Monoid G] [AddCommMonoid V] [Module K V]

/-- Iterated extension of representation coefficients agrees with direct extension. -/
noncomputable def baseChangeTowerEquiv (ρ : Representation K G V) :
    ((ρ.baseChange L).baseChange M).Equiv (ρ.baseChange M) :=
  .mk (TensorProduct.AlgebraTensorModule.cancelBaseChange K L M M V) (by
    intro g
    ext a
    rfl)

end Representation

namespace Representation.Equiv
variable {R G V W : Type*} [CommSemiring R] [Monoid G]
  [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Extend a representation equivalence along with its coefficients. -/
noncomputable def baseChange (A : Type*) [CommSemiring A] [Algebra R A]
    (e : Representation.Equiv ρ σ) :
    Representation.Equiv (ρ.baseChange A) (σ.baseChange A) :=
  .mk (LinearEquiv.baseChange R A V W e.toLinearEquiv)
    (e.toIntertwiningMap.baseChange A).isIntertwining'

/-- The extended equivalence fixes the coefficient tensorand. -/
@[simp]
theorem baseChange_tmul (A : Type*) [CommSemiring A] [Algebra R A]
    (e : Representation.Equiv ρ σ) (a : A) (v : V) :
    e.baseChange A (a ⊗ₜ[R] v) = a ⊗ₜ[R] e v := rfl

end Representation.Equiv
