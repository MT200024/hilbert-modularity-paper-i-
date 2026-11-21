/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic

/-! # Absolute Galois groups under field isomorphisms -/

@[expose] public noncomputable section
namespace AlgebraicClosure
variable (E K : Type*) [Field E] [Field K] (σ : E ≃+* K)

/-- Conjugation by a chosen extension of a field isomorphism identifies absolute Galois groups. -/
def galoisFieldEquiv :
    (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) ≃*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := by
  let j := IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ
  let forward (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) :
      AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := (j.symm.trans g.toRingEquiv).trans j) (by
      intro a
      simp [j])
  let backward (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E :=
    AlgEquiv.ofRingEquiv (f := (j.trans g.toRingEquiv).trans j.symm) (by
      intro a
      simp [j])
  refine { toFun := forward, invFun := backward, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }
  · intro g
    apply AlgEquiv.ext
    intro a
    change j.symm (j (g (j.symm (j a)))) = g a
    simp only [RingEquiv.symm_apply_apply]
  · intro g
    apply AlgEquiv.ext
    intro a
    change j (j.symm (g (j (j.symm a)))) = g a
    simp only [RingEquiv.apply_symm_apply]
  · intro g h
    apply AlgEquiv.ext
    intro a
    change j (g (h (j.symm a))) = j (g (j.symm (j (h (j.symm a)))))
    rw [j.symm_apply_apply]

/-- The transported automorphism is literal conjugation on the algebraic closure. -/
@[simp]
theorem galoisFieldEquiv_apply
    (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (a : AlgebraicClosure K) :
    galoisFieldEquiv E K σ g a =
      IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ
        (g ((IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ).symm a)) := rfl

/-- Conjugation intertwines the two actions on the algebraic closures. -/
theorem galoisFieldEquiv_intertwines
    (g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (a : AlgebraicClosure E) :
    galoisFieldEquiv E K σ g
        (IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ a) =
      IsAlgClosure.equivOfEquiv (AlgebraicClosure E) (AlgebraicClosure K) σ (g a) := by
  simp only [galoisFieldEquiv_apply, RingEquiv.symm_apply_apply]

end AlgebraicClosure
