/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.Cohomology.Automorphisms
public import HilbertModularity.Geometry.TateModule
public import Mathlib.Algebra.Group.Equiv.Opposite

/-! # Galois action on actual geometric pro-étale cohomology

Field automorphisms act contravariantly on spectra and hence on the actual
base-changed scheme. Composing this with contravariant cohomological pullback
gives the algebraic Galois action. The construction retains the specified
field embedding and the actual pullback; no dimension or continuity assertion
is part of this construction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

open GroupScheme

universe u
variable (K E : Type u) [Field K] [Field E] [Algebra K E]

/-- The actual spectrum maps give an opposite-automorphism action on the extension-field point. -/
def fieldPointGaloisAut : (E ≃ₐ[K] E) →* (Aut (fieldPoint K E))ᵐᵒᵖ where
  toFun σ := MulOpposite.op
    { hom := fieldPointMap K E σ
      inv := fieldPointMap K E σ⁻¹
      hom_inv_id := by rw [← fieldPointMap_mul]; simp
      inv_hom_id := by rw [← fieldPointMap_mul]; simp }
  map_one' := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    exact fieldPointMap_one K E
  map_mul' σ τ := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    exact fieldPointMap_mul K E σ τ

/-- The field-point action uses the original spectrum map, with its proved variance. -/
theorem fieldPointGaloisAut_hom (σ : E ≃ₐ[K] E) :
    (fieldPointGaloisAut K E σ).unop.hom = fieldPointMap K E σ := rfl

variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

/-- Pullback transports the spectrum action to the actual extension-field base change. -/
def fieldBaseChangeGaloisAut :
    (E ≃ₐ[K] E) →* (Aut (pullback (fieldPoint K E).hom p))ᵐᵒᵖ :=
  (MonoidHom.op ((Over.pullback p ⋙ Over.forget X).mapAut (fieldPoint K E))).comp
    (fieldPointGaloisAut K E)

/-- On the field projection, the base-change action is the original spectrum automorphism. -/
@[simp] theorem fieldBaseChangeGaloisAut_fst (σ : E ≃ₐ[K] E) :
    (fieldBaseChangeGaloisAut K E p σ).unop.hom ≫ pullback.fst (fieldPoint K E).hom p =
      pullback.fst (fieldPoint K E).hom p ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  change ((Over.pullback p).map (fieldPointMap K E σ)).left ≫
    pullback.fst (fieldPoint K E).hom p = _
  simp only [Over.pullback_map_left, pullback.lift_fst]
  rfl

/-- The base-change action fixes the projection to the original scheme. -/
@[simp] theorem fieldBaseChangeGaloisAut_snd (σ : E ≃ₐ[K] E) :
    (fieldBaseChangeGaloisAut K E p σ).unop.hom ≫ pullback.snd (fieldPoint K E).hom p =
      pullback.snd (fieldPoint K E).hom p := by
  change ((Over.pullback p).map (fieldPointMap K E σ)).left ≫
    pullback.snd (fieldPoint K E).hom p = _
  simp only [Over.pullback_map_left, pullback.lift_snd]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual integral cohomology of the geometric base change carries its algebraic Galois action. -/
def ellAdicCohomologyGaloisRepresentation (n : ℕ) :
    Representation ℤ_[ℓ] (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((pullback (fieldPoint K (AlgebraicClosure K)).hom p).EllAdicCohomology ℓ n) :=
  (ellAdicCohomologyAutRepresentation _ ℓ n).comp
    (fieldBaseChangeGaloisAut K (AlgebraicClosure K) p)

/-- The Galois representation is pullback by the actual base-changed spectrum automorphism. -/
theorem ellAdicCohomologyGaloisRepresentation_apply (n : ℕ)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : (pullback (fieldPoint K (AlgebraicClosure K)).hom p).EllAdicCohomology ℓ n) :
    ellAdicCohomologyGaloisRepresentation K p ℓ n σ x =
      ellAdicCohomologyEquiv (fieldBaseChangeGaloisAut K (AlgebraicClosure K) p σ).unop ℓ n x := rfl

/-- Rational geometric cohomology with the scalar extension of its actual integral Galois action. -/
def rationalEllAdicCohomologyGaloisRepresentation (n : ℕ) :
    Representation ℚ_[ℓ] (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ((pullback (fieldPoint K (AlgebraicClosure K)).hom p).RationalEllAdicCohomology ℓ n) :=
  Representation.baseChange ℚ_[ℓ] (ellAdicCohomologyGaloisRepresentation K p ℓ n)

/-- The rational Galois action fixes the coefficient tensorand and acts on actual integral cohomology. -/
@[simp] theorem rationalEllAdicCohomologyGaloisRepresentation_tmul (n : ℕ)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : ℚ_[ℓ])
    (x : (pullback (fieldPoint K (AlgebraicClosure K)).hom p).EllAdicCohomology ℓ n) :
    rationalEllAdicCohomologyGaloisRepresentation K p ℓ n σ (a ⊗ₜ[ℤ_[ℓ]] x) =
      a ⊗ₜ[ℤ_[ℓ]] ellAdicCohomologyGaloisRepresentation K p ℓ n σ x := rfl

end AlgebraicGeometry.Scheme
