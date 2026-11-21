/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ScalarConjugation
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Restriction of scalars and coefficient conjugation

A coefficient automorphism fixing the ground field becomes a linear equivalence
after restriction to that field. The acting group and its elements are unchanged.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable (R : Type*) {E G V : Type*} [CommSemiring R] [Semiring E] [Monoid G]
  [AddCommMonoid V] [Module E V] [Module R V] [LinearMap.CompatibleSMul V V R E]

/-- Regard a representation as linear over a compatible smaller scalar ring. -/
def restrictScalars (ρ : Representation E G V) : Representation R G V where
  toFun g := (ρ g).restrictScalars R
  map_one' := by ext v; exact congrArg (fun f : V →ₗ[E] V => f v) ρ.map_one
  map_mul' g h := by ext v; exact congrArg (fun f : V →ₗ[E] V => f v) (ρ.map_mul g h)

/-- Restriction of scalars preserves an actual intertwining equivalence. -/
def Equiv.restrictScalars {W : Type*} [AddCommMonoid W] [Module E W] [Module R W]
    [LinearMap.CompatibleSMul W W R E] [LinearMap.CompatibleSMul V W R E]
    {ρ : Representation E G V} {τ : Representation E G W} (e : ρ.Equiv τ) :
    (ρ.restrictScalars R).Equiv (τ.restrictScalars R) :=
  .mk (e.toLinearEquiv.restrictScalars R) (by
    intro g
    ext v
    exact congrArg (fun f : V →ₗ[E] W => f v) (e.isIntertwining' g))

/-- Restrict an intertwining map to a compatible smaller ring of scalars. -/
def IntertwiningMap.restrictScalars {W : Type*} [AddCommMonoid W] [Module E W] [Module R W]
    [LinearMap.CompatibleSMul W W R E] [LinearMap.CompatibleSMul V W R E]
    {ρ : Representation E G V} {τ : Representation E G W} (f : ρ.IntertwiningMap τ) :
    (ρ.restrictScalars R).IntertwiningMap (τ.restrictScalars R) where
  toLinearMap := f.toLinearMap.restrictScalars R
  isIntertwining' g := by
    ext v
    exact congrArg (fun l : V →ₗ[E] W => l v) (f.isIntertwining' g)

end Representation

namespace LinearEquiv

variable (R : Type*) {E V W : Type*} [CommSemiring R] [CommSemiring E] [Algebra R E]
  [AddCommMonoid V] [Module E V] [Module R V] [IsScalarTower R E V]
  [AddCommMonoid W] [Module E W] [Module R W] [IsScalarTower R E W]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A semilinear equivalence whose coefficient automorphism fixes `R` is `R`-linear. -/
def restrictScalarsOfAlgEquiv (σ : E ≃ₐ[R] E)
    (e : LinearEquiv (σ.toRingEquiv : E →+* E)
      (σ' := (σ.toRingEquiv.symm : E →+* E)) V W) : V ≃ₗ[R] W :=
  e.toAddEquiv.toLinearEquiv fun r v => by
    change e (r • v) = r • e v
    rw [← algebraMap_smul E r v, e.map_smulₛₗ]
    change σ (algebraMap R E r) • e v = r • e v
    rw [σ.commutes, algebraMap_smul]

end LinearEquiv

namespace Rep

variable (R : Type*) {E G : Type*} [Field R] [Field E] [Algebra R E] [Monoid G]
  (σ : E ≃ₐ[R] E) (V : Rep E G)
  [Module R V] [IsScalarTower R E V]
  [Module R (scalarConjugate σ.toRingEquiv V)]
  [IsScalarTower R E (scalarConjugate σ.toRingEquiv V)]

/-- Coefficient conjugation is an equivalence over every ground field fixed by the automorphism. -/
def scalarConjugateRestrictScalarsEquiv :
    (Representation.restrictScalars R V.ρ).Equiv
      (Representation.restrictScalars R (scalarConjugate σ.toRingEquiv V).ρ) :=
  Representation.Equiv.mk
    (LinearEquiv.restrictScalarsOfAlgEquiv R σ (scalarConjugateEquiv σ.toRingEquiv V)) (by
      intro g
      ext v
      exact scalarConjugateEquiv_apply_action σ.toRingEquiv V g v)

set_option maxHeartbeats 800000 in
/-- Corresponding stable quotients under coefficient conjugation are isomorphic over the
ground field fixed by the coefficient automorphism. -/
def scalarConjugateQuotientRestrictScalarsEquiv (S : Subrepresentation V.ρ) :
    (Representation.restrictScalars R
      (V.ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
    (Representation.restrictScalars R
      ((scalarConjugate σ.toRingEquiv V).ρ.quotient
        (scalarConjugateSubrepresentationEquiv σ.toRingEquiv V S).toSubmodule
        (scalarConjugateSubrepresentationEquiv σ.toRingEquiv V S).apply_mem_toSubmodule)) :=
  Representation.Equiv.mk
    (LinearEquiv.restrictScalarsOfAlgEquiv R σ
      (scalarConjugateQuotientEquiv σ.toRingEquiv V S)) (by
      intro g
      apply LinearMap.ext
      intro v
      exact scalarConjugateQuotientEquiv_apply_action σ.toRingEquiv V S g v)

end Rep

namespace Representation

variable {K L G V : Type*} [Field K] [Field L] [Algebra K L] [Monoid G]
  [AddCommGroup V] [Module K V]

/-- A linear functional on the coefficient field acts on the coefficient tensorand. -/
def baseChangeCoefficientMap (ρ : Representation K G V) (φ : L →ₗ[K] K) :
    ((ρ.baseChange L).restrictScalars K).IntertwiningMap ρ where
  toLinearMap := (_root_.TensorProduct.lid K V).toLinearMap ∘ₗ
    TensorProduct.map φ (LinearMap.id : V →ₗ[K] V)
  isIntertwining' g := by
    ext a v
    change φ a • ρ g v = ρ g (φ a • v)
    exact (map_smul (ρ g) (φ a) v).symm

/-- The coefficient functional evaluates the first tensorand. -/
@[simp]
theorem baseChangeCoefficientMap_tmul (ρ : Representation K G V) (φ : L →ₗ[K] K)
    (a : L) (v : V) : baseChangeCoefficientMap ρ φ (a ⊗ₜ[K] v) = φ a • v := rfl

/-- Scalar extension admits an equivariant surjection back to the original representation,
viewed over the ground field. -/
theorem exists_surjective_baseChange_coefficientMap (ρ : Representation K G V) :
    ∃ f : ((ρ.baseChange L).restrictScalars K).IntertwiningMap ρ, Function.Surjective f := by
  let φ := (Algebra.linearMap K L).leftInverse
  have hker : LinearMap.ker (Algebra.linearMap K L) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap K L).injective
  have hφ : φ 1 = 1 := by
    simpa [φ] using LinearMap.leftInverse_apply_of_inj hker (1 : K)
  refine ⟨baseChangeCoefficientMap ρ φ, ?_⟩
  intro v
  exact ⟨(1 : L) ⊗ₜ[K] v, by simp [hφ]⟩

/-- Fixing a coefficient defines a ground-linear equivariant map into the scalar extension. -/
def baseChangeTensorMap (ρ : Representation K G V) (a : L) :
    ρ.IntertwiningMap ((ρ.baseChange L).restrictScalars K) where
  toLinearMap := TensorProduct.mk K L V a
  isIntertwining' g := by ext v; rfl

/-- The coefficient tensor map sends a vector to its pure tensor with the chosen coefficient. -/
@[simp]
theorem baseChangeTensorMap_apply (ρ : Representation K G V) (a : L) (v : V) :
    baseChangeTensorMap ρ a v = a ⊗ₜ[K] v := rfl

end Representation
