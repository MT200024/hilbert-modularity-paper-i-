/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.IntegralNaturality
public import HilbertModularity.RepresentationTheory.IntegralBaseChange
public import HilbertModularity.RepresentationTheory.DualLattice

/-! # Naturality of integral and dual representation lattices

Equivariant maps preserve the canonical integral image lattices through the
scalar-extension tower. Their transposes preserve the actual dual lattices.
These are the integral naturality statements used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable (R₀ R L : Type*) {G M : Type*} [CommRing R₀] [CommRing R] [CommRing L]
  [Algebra R₀ R] [Algebra R₀ L] [Algebra R L] [IsScalarTower R₀ R L]
  [Monoid G] [AddCommMonoid M] [Module R₀ M] (ρ : Representation R₀ G M)
  (S : Type*) [CommRing S] [Algebra R₀ S] [Algebra S L] [IsScalarTower R₀ S L]

variable {N : Type*} [AddCommMonoid N] [Module R₀ N]
  {τ : Representation R₀ G N} (f : ρ.IntertwiningMap τ)

/-- The canonical tensor tower equivalence is natural in equivariant maps. -/
theorem baseChangeTowerEquiv_natural (x : L ⊗[S] (S ⊗[R₀] M)) :
    baseChangeTowerEquiv (K := R₀) (L := S) (M := L) τ
        ((f.baseChange S).baseChange L x) =
      f.baseChange L (baseChangeTowerEquiv (K := R₀) (L := S) (M := L) ρ x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    induction x using _root_.TensorProduct.inductionOn with
    | add x y hx hy => simp only [_root_.TensorProduct.tmul_add, map_add, hx, hy]
    | tmul b m => rfl

/-- An integral equivariant map preserves the canonical lattice in iterated scalar extension. -/
theorem map_mem_iteratedIntegralBaseChangeLattice
    {x : L ⊗[S] (S ⊗[R₀] M)}
    (hx : x ∈ (iteratedIntegralBaseChangeLattice R₀ R L ρ S).toSubmodule) :
    (f.baseChange S).baseChange L x ∈
      (iteratedIntegralBaseChangeLattice R₀ R L τ S).toSubmodule := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨f.baseChange L v,
    Algebra.TensorProduct.map_mem_integralBaseChangeLattice R₀ R L M f.toLinearMap hv, ?_⟩
  apply (baseChangeTowerEquiv (K := R₀) (L := S) (M := L) τ).toLinearEquiv.injective
  change baseChangeTowerEquiv (K := R₀) (L := S) (M := L) τ
      ((baseChangeTowerEquiv (K := R₀) (L := S) (M := L) τ).symm (f.baseChange L v)) =
      baseChangeTowerEquiv (K := R₀) (L := S) (M := L) τ
        ((f.baseChange S).baseChange L
          ((baseChangeTowerEquiv (K := R₀) (L := S) (M := L) ρ).symm v))
  rw [Representation.Equiv.apply_symm_apply, baseChangeTowerEquiv_natural]
  rw [Representation.Equiv.apply_symm_apply]


end Representation

namespace Submodule

variable {R K V W : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommMonoid W] [Module R W] [Module K W] [IsScalarTower R K W]
  (M : Submodule R V) (N : Submodule R W)
  [IsLattice K M] [Module.Free R M] [IsLattice K N] [Module.Free R N]
  (f : V →ₗ[K] W) (hf : ∀ v ∈ M, f v ∈ N)

include hf in
/-- The transpose of a coefficient-linear lattice map preserves the actual integral dual lattices. -/
theorem dualMap_mem_dualLattice {ell : Module.Dual K W} (hell : ell ∈ dualLattice N) :
    f.dualMap ell ∈ dualLattice M := by
  rw [mem_dualLattice_iff] at hell ⊢
  intro v
  exact hell ⟨f v, hf v v.property⟩

end Submodule
