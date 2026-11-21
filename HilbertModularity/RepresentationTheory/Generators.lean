/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Separation.Hausdorff

/-! # Representations determined by generators

Fixed vectors and intertwiners can be tested on a generating set. These
lemmas support the rigidity argument of [TripathiGoswami].
-/

@[expose] public section

namespace Representation

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A vector fixed by a set of group elements is fixed by the subgroup they generate. -/
theorem apply_eq_of_mem_closure (ρ : Representation K G V) {s : Set G} {v : V}
    (hv : ∀ g ∈ s, ρ g v = v) {g : G} (hg : g ∈ Subgroup.closure s) : ρ g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hv g hg
  | one => simp
  | mul g h _ _ hg hh => simp only [map_mul, Module.End.mul_apply, hh, hg]
  | inv g _ hg =>
    calc
      ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := by rw [hg]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

/-- A nontrivial irreducible representation has no nonzero globally fixed vector. -/
theorem eq_zero_of_forall_apply_eq (ρ : Representation K G V) [ρ.IsIrreducible]
    {g : G} (hg : ρ g ≠ 1) (v : V) (hv : ∀ g, ρ g v = v) : v = 0 := by
  let S : Subrepresentation ρ :=
    ⟨Submodule.span K {v}, by
      intro h w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hv]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))⟩
  rcases eq_bot_or_eq_top S with hS | hS
  · have h : v ∈ S := Submodule.subset_span (Set.mem_singleton v)
    rw [hS] at h
    exact h
  · apply False.elim
    apply hg
    apply LinearMap.ext
    intro w
    have hw : w ∈ S := by rw [hS]; trivial
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp only [map_smul, hv, Module.End.one_apply]

/-- Intertwining on generators extends to their generated subgroup. -/
theorem intertwines_of_mem_closure
    (ρ : Representation K G V) (σ : Representation K G W)
    (e : V ≃ₗ[K] W) {s : Set G}
    (he : ∀ g ∈ s, e.toLinearMap.comp (ρ g) = (σ g).comp e.toLinearMap)
    {g : G} (hg : g ∈ Subgroup.closure s) :
    e.toLinearMap.comp (ρ g) = (σ g).comp e.toLinearMap := by
  have h : Set.EqOn (e.conjRingEquiv.toMonoidHom.comp ρ) σ s := by
    intro g hg
    apply LinearMap.ext
    intro w
    have h := congrArg (fun f : V →ₗ[K] W => f (e.symm w)) (he g hg)
    simpa using h
  apply LinearMap.ext
  intro v
  have h' := congrArg (fun f : Module.End K W => f (e v)) (MonoidHom.eqOn_closure h hg)
  simpa using h'

/-- An invertible linear map intertwining a generating set intertwines the
whole group representation. -/
theorem equiv_of_intertwines_generators
    (ρ : Representation K G V) (σ : Representation K G W)
    (e : V ≃ₗ[K] W) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (he : ∀ g ∈ s, e.toLinearMap.comp (ρ g) = (σ g).comp e.toLinearMap) :
    Nonempty (ρ.Equiv σ) := by
  refine ⟨Representation.Equiv.mk e fun g => ?_⟩
  exact intertwines_of_mem_closure ρ σ e he (by rw [hs]; trivial)

section Topology

variable [TopologicalSpace G] [TopologicalSpace V] [TopologicalSpace W]

/-- A vector fixed by topological generators of a continuous representation
is globally fixed. -/
theorem apply_eq_of_dense_generators [T2Space V]
    (ρ : Representation K G V) {s : Set G}
    (hs : Dense (Subgroup.closure s : Set G)) (v : V)
    (hρ : Continuous (fun g => ρ g v)) (hv : ∀ g ∈ s, ρ g v = v) (g : G) :
    ρ g v = v := by
  have h : Set.EqOn (fun g => ρ g v) (fun _ => v) (Subgroup.closure s : Set G) :=
    fun _ hg => apply_eq_of_mem_closure ρ hv hg
  exact h.closure hρ continuous_const (hs g)

/-- A continuous linear equivalence intertwining topological generators
intertwines the continuous representations on the whole group. -/
theorem equiv_of_intertwines_dense_generators [T2Space W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (e : V ≃ₗ[K] W) (hec : Continuous e) {s : Set G}
    (hs : Dense (Subgroup.closure s : Set G))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ w, Continuous (fun g => σ g w))
    (he : ∀ g ∈ s, e.toLinearMap.comp (ρ g) = (σ g).comp e.toLinearMap) :
    Nonempty (ρ.Equiv σ) := by
  refine ⟨Representation.Equiv.mk e fun g => ?_⟩
  apply LinearMap.ext
  intro v
  have h : Set.EqOn (fun g => e (ρ g v)) (fun g => σ g (e v))
      (Subgroup.closure s : Set G) := by
    intro g hg
    exact congrArg (fun f : V →ₗ[K] W => f v) (intertwines_of_mem_closure ρ σ e he hg)
  exact h.closure (hec.comp (hρ v)) (hσ (e v)) (hs g)

end Topology

end Representation
