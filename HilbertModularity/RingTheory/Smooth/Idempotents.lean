/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RingTheory.Smooth.GenericFiber
public import HilbertModularity.RingTheory.Idempotents

/-! # Idempotents of smooth generic fibres over a normal base

A generic-fibre idempotent extends uniquely to the original smooth algebra.
This preserves the decomposition into connected components at the generic point.
-/

@[expose] public section
open scoped TensorProduct
namespace Algebra.TensorProduct
variable (R S F : Type*) [CommRing R] [IsIntegrallyClosed R]
  [CommRing S] [Algebra R S] [Algebra.Smooth R S]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- Generic-fibre idempotents descend uniquely over an integrally closed base. -/
theorem existsUnique_includeRight_idempotent (z : F ⊗[R] S) (hz : IsIdempotentElem z) :
    ∃! s : S, IsIdempotentElem s ∧ (includeRight : S →ₐ[R] F ⊗[R] S) s = z := by
  let c := Algebra.TensorProduct.comm R F S
  obtain ⟨s, hs⟩ := (isIntegral_iff_exists_includeLeft R S F (c z)).mp
    ((hz.map c).isIntegral (R := S))
  have he : (includeRight : S →ₐ[R] F ⊗[R] S) s = z := by
    apply c.injective
    simpa only [c, Algebra.TensorProduct.comm_tmul, includeRight_apply, includeLeft_apply] using hs
  have hi : Function.Injective (includeRight : S →ₐ[R] F ⊗[R] S) :=
    includeRight_injective (IsFractionRing.injective R F)
  have hid : IsIdempotentElem s := by
    apply isIdempotentElem_iff.mpr
    apply hi
    simpa only [map_mul, he] using hz.eq
  exact ⟨s, ⟨hid, he⟩, fun t ht => hi (ht.2.trans he.symm)⟩

end Algebra.TensorProduct
