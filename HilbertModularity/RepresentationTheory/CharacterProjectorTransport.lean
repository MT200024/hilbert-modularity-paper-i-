/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CharacterProjector

/-! # Transport of finite character projectors

An equivariant linear equivalence transports a normalized character average
when the group parameters are relabelled by an automorphism. The equality of
averages uses a reindexing of the entire finite group.
-/

@[expose] public noncomputable section

namespace Representation

variable {L G V W : Type*} [Field L] [CommGroup G] [Fintype G]
  [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]

/-- Reindex a character projector along a group automorphism and an
intertwining linear equivalence. -/
theorem characterProjector_comp_equiv (χ : G →* Lˣ)
    (ρV : Representation L G V) (ρW : Representation L G W)
    (e : G ≃* G) (T : V ≃ₗ[L] W)
    (hT : ∀ g : G, (ρW g).comp T.toLinearMap =
      T.toLinearMap.comp (ρV (e g))) :
    (characterProjector (χ.comp e.toMonoidHom) ρW).comp T.toLinearMap =
      T.toLinearMap.comp (characterProjector χ ρV) := by
  classical
  ext v
  simp only [characterProjector, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv e.toEquiv
  intro g
  change ((χ (e g) : L)⁻¹) • ρW g (T v) =
    ((χ (e g) : L)⁻¹) • T (ρV (e g) v)
  congr 1
  exact congrArg (fun f : V →ₗ[L] W => f v) (hT g)

/-- The same intertwiner identifies the two actual projector images. -/
def characterProjectorRangeEquiv (χ : G →* Lˣ)
    (ρV : Representation L G V) (ρW : Representation L G W)
    (e : G ≃* G) (T : V ≃ₗ[L] W)
    (hT : ∀ g : G, (ρW g).comp T.toLinearMap =
      T.toLinearMap.comp (ρV (e g))) :
    (characterProjector χ ρV).range ≃ₗ[L]
      (characterProjector (χ.comp e.toMonoidHom) ρW).range := by
  let pV := characterProjector χ ρV
  let pW := characterProjector (χ.comp e.toMonoidHom) ρW
  have hp : pW.comp T.toLinearMap = T.toLinearMap.comp pV :=
    characterProjector_comp_equiv χ ρV ρW e T hT
  have hf (v : pV.range) : T v.1 ∈ pW.range := by
    obtain ⟨x, hx⟩ := v.2
    refine ⟨T x, ?_⟩
    rw [← hx]
    exact congrArg (fun f : V →ₗ[L] W => f x) hp
  have hi (w : pW.range) : T.symm w.1 ∈ pV.range := by
    obtain ⟨y, hy⟩ := w.2
    refine ⟨T.symm y, ?_⟩
    apply T.injective
    change T (pV (T.symm y)) = T (T.symm w.1)
    calc
      T (pV (T.symm y)) = pW (T (T.symm y)) :=
        (congrArg (fun f : V →ₗ[L] W => f (T.symm y)) hp).symm
      _ = pW y := by rw [T.apply_symm_apply]
      _ = w.1 := hy
      _ = T (T.symm w.1) := (T.apply_symm_apply w.1).symm
  exact
    { toFun := fun v => ⟨T v.1, hf v⟩
      invFun := fun w => ⟨T.symm w.1, hi w⟩
      left_inv := by intro v; apply Subtype.ext; exact T.symm_apply_apply v.1
      right_inv := by intro w; apply Subtype.ext; exact T.apply_symm_apply w.1
      map_add' := by intro v w; apply Subtype.ext; exact T.map_add v.1 w.1
      map_smul' := by intro c v; apply Subtype.ext; exact T.map_smul c v.1 }

end Representation
