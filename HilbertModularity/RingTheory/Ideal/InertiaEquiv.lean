/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Ideal.Pointwise

/-! # Inertia under equivariant ring isomorphisms -/

@[expose] public section
namespace Ideal
variable {G H R S : Type*} [Group G] [Group H] [Ring R] [Ring S]
  [MulSemiringAction G R] [MulSemiringAction H S]

/-- An equivariant ring isomorphism transports the actual inertia subgroup. -/
theorem inertia_map_ringEquiv (I : Ideal R) (e : R ≃+* S) (q : G ≃* H)
    (he : ∀ g x, e (g • x) = q g • e x) :
    (I.map e).inertia H = (I.inertia G).map q.toMonoidHom := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_inertia, mem_inertia]
  constructor
  · intro hh x
    apply (apply_mem_of_equiv_iff (f := e)).mp
    rw [map_sub, he, q.apply_symm_apply]
    exact hh (e x)
  · intro hh y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx := (apply_mem_of_equiv_iff (f := e)).mpr (hh x)
    simpa only [map_sub, he, q.apply_symm_apply] using hx

end Ideal
