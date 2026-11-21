/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.Isogeny
public import HilbertModularity.RepresentationTheory.TateModule
public import Mathlib.RepresentationTheory.Intertwining

/-! # Equivariant isogeny invariance of actual Tate modules

A surjective equivariant point homomorphism with bounded kernel gives an
isomorphism of the actual rational Tate representations. This is the
conditional isogeny-invariance step in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Monoid G]
  {A B : Type*} [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B]

/-- The actual rational Tate isogeny is equivariant whenever its point map is equivariant. -/
def rationalIsogenyRepresentationEquiv (f : A →+ B)
    (heq : ∀ (g : G) (x : A), f (g • x) = g • f x)
    (hf : Function.Surjective f) (m : ℕ) (hm : m ≠ 0)
    (hk : ∀ x, f x = 0 → m • x = 0) :
    (rationalRepresentation p G A).Equiv (rationalRepresentation p G B) :=
  .mk (rationalIsogenyEquiv p f hf m hm hk) (by
    intro g
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    | tmul a x =>
      change a ⊗ₜ[ℤ_[p]] map p f (representation p G A g x) =
        a ⊗ₜ[ℤ_[p]] representation p G B g (map p f x)
      congr 1
      apply Subtype.ext
      funext n
      apply Subtype.ext
      exact heq g (projection p A n x))

/-- The equivariant isogeny comparison is the original covariant map on pure tensors. -/
@[simp]
theorem rationalIsogenyRepresentationEquiv_tmul (f : A →+ B)
    (heq : ∀ (g : G) (x : A), f (g • x) = g • f x)
    (hf : Function.Surjective f) (m : ℕ) (hm : m ≠ 0)
    (hk : ∀ x, f x = 0 → m • x = 0) (a : ℚ_[p]) (x : integral p A) :
    rationalIsogenyRepresentationEquiv p G f heq hf m hm hk (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] map p f x := rfl

/-- A finite-kernel surjective equivariant point map preserves the rational Tate representation. -/
def rationalFiniteKernelRepresentationEquiv (f : A →+ B) [Finite f.ker]
    (heq : ∀ (g : G) (x : A), f (g • x) = g • f x) (hf : Function.Surjective f) :
    (rationalRepresentation p G A).Equiv (rationalRepresentation p G B) :=
  rationalIsogenyRepresentationEquiv p G f heq hf (Nat.card f.ker)
    (Nat.ne_of_gt Nat.card_pos) (by
      intro x hx
      exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ : f.ker))))

end TateModule
