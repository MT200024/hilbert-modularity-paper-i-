/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Monodromy.Rigidity
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Representation comparison under a cusp involution

The rank-two rigidity argument of [TripathiGoswami, involution lemma]
extends from two local monodromies to continuous representations when their
algebraically generated subgroup is topologically dense.
-/

@[expose] public section

namespace Representation

variable {K G V W : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]
  [NormedAddCommGroup W] [NormedSpace K W] [FiniteDimensional K W]

/-- An intertwiner on a set of topological generators extends to the continuous
representations, over the original coefficient field. -/
def equivOfDenseGenerators (ρ : Representation K G V) (σ : Representation K G W)
    (s : Set G) (hs : Dense (Subgroup.closure s : Set G))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ w, Continuous (fun g => σ g w))
    (e : V ≃ₗ[K] W)
    (he : ∀ g ∈ s, e.toLinearMap.comp (ρ g) = (σ g).comp e.toLinearMap) :
    ρ.Equiv σ := by
  let τ : Representation K G V := e.symm.conjRingEquiv.toMonoidHom.comp σ
  have hagree : Set.EqOn τ ρ s := by
    intro g hg
    apply LinearMap.ext
    intro v
    change e.symm (σ g (e v)) = ρ g v
    have h := congrArg (fun f : V →ₗ[K] W => f v) (he g hg)
    change e (ρ g v) = σ g (e v) at h
    rw [← h, e.symm_apply_apply]
  have hall : ∀ g, τ g = ρ g := by
    intro g
    apply LinearMap.ext
    intro v
    have hc := MonoidHom.eqOn_closure hagree
    have hv : (fun g => τ g v) = (fun g => ρ g v) :=
      Continuous.ext_on hs
        (e.symm.toLinearMap.continuous_of_finiteDimensional.comp (hσ (e v)))
        (hρ v) (fun g hg => congrArg (fun f : Module.End K V => f v) (hc hg))
    exact congrFun hv g
  refine Representation.Equiv.mk e fun g => ?_
  apply LinearMap.ext
  intro v
  have h := congrArg (fun f : Module.End K V => e (f v)) (hall g)
  change e (e.symm (σ g (e v))) = e (ρ g v) at h
  simpa only [e.apply_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] using h.symm

end Representation

namespace HilbertModularity.Monodromy

variable {K G : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [Group G] [TopologicalSpace G]

/-- Continuous rank-two representations are determined by two irreducible
unipotent cusp monodromies and the trace of their product, provided those
cusps topologically generate the group. -/
theorem nonempty_equiv_of_unipotent_cusps
    (ρ σ : Representation K G (Fin 2 → K))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (hσ : ∀ v, Continuous (fun g => σ g v))
    (a b : G) (hdense : Dense (Subgroup.closure ({a, b} : Set G) : Set G))
    (hA : (ρ a - 1) ^ 2 = 0) (hB : (ρ b - 1) ^ 2 = 0) (hBne : ρ b ≠ 1)
    (hirr : ∀ v, ρ a v = v → ρ b v = v → v = 0)
    (hA' : (σ a - 1) ^ 2 = 0) (hB' : (σ b - 1) ^ 2 = 0) (hBne' : σ b ≠ 1)
    (hirr' : ∀ v, σ a v = v → σ b v = v → v = 0)
    (ht : LinearMap.trace K (Fin 2 → K) (ρ (a * b)) =
      LinearMap.trace K (Fin 2 → K) (σ (a * b))) :
    Nonempty (ρ.Equiv σ) := by
  obtain ⟨e, hea, heb⟩ := exists_equiv_unipotent_pair (ρ a) (ρ b) (σ a) (σ b)
    hA hB hBne hirr hA' hB' hBne' hirr' (by simpa only [map_mul] using ht)
  refine ⟨Representation.equivOfDenseGenerators ρ σ {a, b} hdense hρ hσ e ?_⟩
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact hea
  · exact Set.mem_singleton_iff.mp hg ▸ heb

/-- Swapping two nontrivial unipotent cusp monodromies preserves the continuous
rank-two representation. The actual group automorphism and dense generators
are inputs; this theorem does not construct an etale fundamental group. -/
theorem nonempty_equiv_comp_cusp_swap
    (ρ : Representation K G (Fin 2 → K))
    (hρ : ∀ v, Continuous (fun g => ρ g v))
    (a b : G) (hdense : Dense (Subgroup.closure ({a, b} : Set G) : Set G))
    (α : G ≃* G) (hα : Continuous α) (ha : α a = b) (hb : α b = a)
    (hA : (ρ a - 1) ^ 2 = 0) (hB : (ρ b - 1) ^ 2 = 0)
    (hAne : ρ a ≠ 1) (hBne : ρ b ≠ 1)
    (hirr : ∀ v, ρ a v = v → ρ b v = v → v = 0) :
    Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom)) := by
  obtain ⟨e, hea, heb⟩ := exists_equiv_unipotent_pair (ρ a) (ρ b) (ρ b) (ρ a)
    hA hB hBne hirr hB hA hAne (fun v hvb hva => hirr v hva hvb)
    (LinearMap.trace_mul_comm K (ρ a) (ρ b))
  refine ⟨Representation.equivOfDenseGenerators ρ (ρ.comp α.toMonoidHom)
    {a, b} hdense hρ (fun v => (hρ v).comp hα) e ?_⟩
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ha] using hea
  · have hgb : g = b := Set.mem_singleton_iff.mp hg
    subst g
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hb] using heb

end HilbertModularity.Monodromy
