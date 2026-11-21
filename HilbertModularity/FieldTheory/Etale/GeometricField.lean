/- Assembled by AxiomProver. -/

module

public import HilbertModularity.FieldTheory.IsAlgClosed.IntegralPoints
public import HilbertModularity.CategoryTheory.GaloisAction
public import Mathlib.RingTheory.Etale.Finite

/-! # Extending the geometric field of a finite étale fibre functor

Postcomposition with an extension of an algebraically closed field is a
natural isomorphism of the existing finite étale fibre functors.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
open scoped CategoryTheory.PreGaloisCategory

namespace CommAlgCat.FiniteEtale
universe u v w
variable (k : Type u) [Field k] (Ω Ω' : Type w)
  [Field Ω] [IsAlgClosed Ω] [Field Ω']
  [Algebra k Ω] [Algebra k Ω'] [Algebra Ω Ω'] [IsScalarTower k Ω Ω']

/-- Enlarging an algebraically closed geometric field identifies finite étale fibres naturally. -/
def fiberIsoOfFieldExtension : fiber.{v} k Ω ≅ fiber.{v} k Ω' :=
  NatIso.ofComponents (fun A => FintypeCat.equivEquivIso
    (Equiv.ofBijective (fun φ : A.unop.obj →ₐ[k] Ω =>
      (IsScalarTower.toAlgHom k Ω Ω').comp φ)
      (AlgHom.bijective_comp_of_isAlgClosed k A.unop.obj Ω Ω'))) (by
        intro A B f
        apply FintypeCat.hom_ext
        intro φ
        apply AlgHom.ext
        intro a
        rfl)

/-- The geometric fibre comparison sends a point to its actual field extension. -/
@[simp]
theorem fiberIsoOfFieldExtension_hom_apply (A : (FiniteEtale.{v} k)ᵒᵖ)
    (φ : A.unop.obj →ₐ[k] Ω) :
    (fiberIsoOfFieldExtension k Ω Ω').hom.app A φ =
      (IsScalarTower.toAlgHom k Ω Ω').comp φ := rfl

/-- The geometric field extension identifies the profinite fibre automorphism groups. -/
def fiberAutFieldExtensionEquiv : Aut (fiber.{v} k Ω) ≃ₜ* Aut (fiber.{v} k Ω') :=
  let e := fiberIsoOfFieldExtension.{u, v, w} k Ω Ω'
  { e.conjAut with
    continuous_toFun := PreGaloisCategory.continuous_conjAut e
    continuous_invFun := PreGaloisCategory.continuous_conjAut e.symm }

end CommAlgCat.FiniteEtale
