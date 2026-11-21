/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.TensorRelabelling
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import HilbertModularity.RepresentationTheory.ScalarConjugationInvariants

/-! # Equivariant coefficient relabelling

An equivariant semilinear identification induces an equivalence over a common
coefficient field with compatible labels. In particular, it preserves the
determinant used in [TripathiGoswami, prime determinant].
-/

public section

open scoped TensorProduct

namespace Representation

variable {R S F G M N : Type*} [CommRing R] [CommRing S] [CommRing F]
  [Algebra R F] [Algebra S F] [Monoid G]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (σ : R ≃+* S) (hσ : ∀ r, algebraMap S F (σ r) = algebraMap R F r)

local instance : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

local instance : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- Compatible coefficient labels turn an equivariant semilinear map into an
equivalence of representations over the target coefficient ring. -/
noncomputable def baseChangeRelabellingEquiv
    (ρ : Representation R G M) (τ : Representation S G N)
    (e : M ≃ₛₗ[σ.toRingHom] N) (he : ∀ g m, e (ρ g m) = τ g (e m)) :
    (ρ.baseChange F).Equiv (τ.baseChange F) :=
  .mk (LinearEquiv.baseChangeRelabelling σ hσ e) (by
    intro g
    apply LinearMap.ext
    intro x
    change LinearEquiv.baseChangeRelabelling σ hσ e (ρ.baseChange F g x) =
      τ.baseChange F g (LinearEquiv.baseChangeRelabelling σ hσ e x)
    induction x using TensorProduct.inductionOn with
    | tmul a m => simp only [baseChange_tmul, LinearEquiv.baseChangeRelabelling_tmul, he]
    | add x y hx hy => simp only [map_add, hx, hy])

/-- The equivariant relabelling fixes the coefficient tensorand. -/
@[simp] theorem baseChangeRelabellingEquiv_tmul
    (ρ : Representation R G M) (τ : Representation S G N)
    (e : M ≃ₛₗ[σ.toRingHom] N) (he : ∀ g m, e (ρ g m) = τ g (e m))
    (a : F) (m : M) :
    baseChangeRelabellingEquiv σ hσ ρ τ e he (a ⊗ₜ[R] m) = a ⊗ₜ[S] e m := by
  change LinearEquiv.baseChangeRelabelling σ hσ e (a ⊗ₜ[R] m) = _
  exact LinearEquiv.baseChangeRelabelling_tmul σ hσ e a m

end Representation

namespace Representation

variable {R S F G M N : Type*} [CommRing R] [CommRing S] [Field F]
  [Algebra R F] [Algebra S F] [Monoid G]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (σ : R ≃+* S) (hσ : ∀ r, algebraMap S F (σ r) = algebraMap R F r)

local instance : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

local instance : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

include hσ in
/-- Relabelling a coefficient-ring action preserves every determinant after
extension along compatible labels. -/
theorem det_baseChangeRelabelling
    (ρ : Representation R G M) (τ : Representation S G N)
    (e : M ≃ₛₗ[σ.toRingHom] N) (he : ∀ g m, e (ρ g m) = τ g (e m)) (g : G) :
    LinearMap.det (τ.baseChange F g) = LinearMap.det (ρ.baseChange F g) :=
  (baseChangeRelabellingEquiv σ hσ ρ τ e he).det_eq g

end Representation
