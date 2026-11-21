/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Ideal.Over

/-! # Contraction of ideals under compatible ring isomorphisms -/

@[expose] public section
namespace Ideal
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra T U]

/-- Contracting a transported ideal agrees with transporting its contraction. -/
theorem under_map_ringEquiv (P : Ideal S) (e : R ≃+* T) (f : S ≃+* U)
    (h : ∀ x, f (algebraMap R S x) = algebraMap T U (e x)) :
    (P.map f).under T = (P.under R).map e := by
  change (P.map (f : S →+* U)).under T = (P.under R).map (e : R →+* T)
  rw [Ideal.map_comap_of_equiv f, Ideal.map_comap_of_equiv e]
  ext t
  change f.symm (algebraMap T U t) ∈ P ↔ algebraMap R S (e.symm t) ∈ P
  have ht : f.symm (algebraMap T U t) = algebraMap R S (e.symm t) := by
    apply f.injective
    rw [f.apply_symm_apply, h, e.apply_symm_apply]
  rw [ht]

end Ideal
