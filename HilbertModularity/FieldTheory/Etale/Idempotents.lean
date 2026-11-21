/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RingTheory.Idempotents
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Algebra.Ring.Fin

/-! # Natural fibre maps preserve constant sections and idempotents

A natural endomorphism of the finite étale algebra fibre functor fixes every
point induced by a section over the base. Applying this to the two constant
components shows that it preserves the value of every idempotent.
-/

@[expose] public section
open CategoryTheory Opposite
namespace CommAlgCat.FiniteEtale
universe u v
variable (R : Type u) [CommRing R] (Ω : Type v) [Field Ω] [Algebra R Ω]
  (α : End (fiber.{u} R Ω))

/-- Naturality fixes every geometric point induced by a section over the base ring. -/
theorem fiberEnd_fixes_section (A : FiniteEtale.{u} R) (φ : A.obj →ₐ[R] R) :
    α.app (op A) ((Algebra.ofId R Ω).comp φ) = (Algebra.ofId R Ω).comp φ := by
  let T := FiniteEtale.of R R
  let f : A ⟶ T := FiniteEtale.ofHom φ
  have hbase : α.app (op T) (Algebra.ofId R Ω) = Algebra.ofId R Ω := by
    apply AlgHom.ext
    intro r
    exact (α.app (op T) (Algebra.ofId R Ω) : R →ₐ[R] Ω).commutes r
  have h := ConcreteCategory.congr_hom (α.naturality f.op) (Algebra.ofId R Ω)
  change α.app (op A) ((Algebra.ofId R Ω).comp φ) =
    (α.app (op T) (Algebra.ofId R Ω)).comp φ at h
  exact h.trans (congrArg (fun ψ : R →ₐ[R] Ω => ψ.comp φ) hbase)

/-- Every natural fibre endomorphism preserves evaluation of the algebra's idempotents. -/
theorem fiberEnd_preserves_idempotent (A : FiniteEtale.{u} R)
    (e : A.obj) (he : IsIdempotentElem e) (φ : A.obj →ₐ[R] Ω) :
    DFunLike.coe (F := A.obj →ₐ[R] Ω) (α.app (op A) φ) e = φ e := by
  let eProd : (Fin 2 → R) ≃ₐ[R] R × R :=
    { RingEquiv.piFinTwo (fun _ => R) with commutes' _ := rfl }
  have : Algebra.Etale R (R × R) := Algebra.Etale.of_equiv eProd
  let C := FiniteEtale.of R (R × R)
  let f : C ⟶ A := FiniteEtale.ofHom (he.prodAlgHom (R := R))
  have h := ConcreteCategory.congr_hom (α.naturality f.op) φ
  change α.app (op C) (φ.comp he.prodAlgHom) = AlgHom.comp (α.app (op A) φ) he.prodAlgHom at h
  have hc : α.app (op C) (φ.comp he.prodAlgHom) = φ.comp he.prodAlgHom := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map φ) with hz | ho
    · rw [he.comp_prodAlgHom_of_eq_zero φ hz]
      exact fiberEnd_fixes_section R Ω α C (AlgHom.snd R R R)
    · rw [he.comp_prodAlgHom_of_eq_one φ ho]
      exact fiberEnd_fixes_section R Ω α C (AlgHom.fst R R R)
  have hv := AlgHom.congr_fun (h.symm.trans hc) (1, 0)
  have he10 : he.prodAlgHom (R := R) (1, 0) = e := by
    simp [IsIdempotentElem.prodAlgHom]
  change DFunLike.coe (F := A.obj →ₐ[R] Ω) (α.app (op A) φ)
    (he.prodAlgHom (R := R) (1, 0)) = φ (he.prodAlgHom (R := R) (1, 0)) at hv
  simpa only [he10] using hv

end CommAlgCat.FiniteEtale
