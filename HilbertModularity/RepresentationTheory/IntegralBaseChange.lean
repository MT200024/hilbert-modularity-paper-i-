/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.IntegralBaseChange
public import HilbertModularity.RepresentationTheory.CoefficientLattice
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Integral scalar extension of representations

The actual tensor map from integral to coefficient scalar extension intertwines
the group action. Its image is a full stable lattice when the original integral
module is finite. Iterated scalar extension is identified equivariantly with
direct scalar extension, as needed for geometric Tate modules in
[TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable (R₀ R L : Type*) {G M : Type*} [CommRing R₀] [CommRing R] [CommRing L]
  [Algebra R₀ R] [Algebra R₀ L] [Algebra R L] [IsScalarTower R₀ R L]
  [Monoid G] [AddCommMonoid M] [Module R₀ M] (ρ : Representation R₀ G M)

/-- Integral scalar extension maps equivariantly into coefficient scalar extension. -/
def integralBaseChangeIntertwiner :
    (ρ.baseChange R).IntertwiningMap ((ρ.baseChange L).restrictScalars R) where
  toLinearMap := Algebra.TensorProduct.integralBaseChangeMap R₀ R L M
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    induction x using _root_.TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    | tmul r m =>
      change Algebra.TensorProduct.integralBaseChangeMap R₀ R L M (r ⊗ₜ[R₀] ρ g m) =
        (ρ g).baseChange L (Algebra.TensorProduct.integralBaseChangeMap R₀ R L M (r ⊗ₜ[R₀] m))
      rw [Algebra.TensorProduct.integralBaseChangeMap_tmul,
        Algebra.TensorProduct.integralBaseChangeMap_tmul]
      rfl

/-- The actual stable image lattice of an integral representation. -/
def integralBaseChangeLattice : Subrepresentation ((ρ.baseChange L).restrictScalars R) :=
  (integralBaseChangeIntertwiner R₀ R L ρ).range

/-- Finite generation of the original integral representation supplies a full stable lattice. -/
instance integralBaseChangeLattice_isLattice [Module.Finite R₀ M] :
    Submodule.IsLattice L (integralBaseChangeLattice R₀ R L ρ).toSubmodule :=
  Algebra.TensorProduct.integralBaseChangeLattice_isLattice R₀ R L M

variable (S : Type*) [CommRing S] [Algebra R₀ S] [Algebra S L] [IsScalarTower R₀ S L]

/-- The ambient integral lattice inside an iterated scalar extension, transported through the canonical equivalence. -/
def iteratedIntegralBaseChangeLattice :
    Subrepresentation (((ρ.baseChange S).baseChange L).restrictScalars R) :=
  (((baseChangeTowerEquiv (K := R₀) (L := S) (M := L) ρ).symm.toIntertwiningMap).restrictScalars R).mapSubrepresentation
    (integralBaseChangeLattice R₀ R L ρ)

/-- Iterated rational scalar extension retains the full stable lattice coming from the integral module. -/
instance iteratedIntegralBaseChangeLattice_isLattice [Module.Finite R₀ M] :
    Submodule.IsLattice L (iteratedIntegralBaseChangeLattice R₀ R L ρ S).toSubmodule :=
  IntertwiningMap.mapSubrepresentation_isLattice
    (baseChangeTowerEquiv (K := R₀) (L := S) (M := L) ρ).symm.toIntertwiningMap
    (baseChangeTowerEquiv (K := R₀) (L := S) (M := L) ρ).toLinearEquiv.symm.surjective
    (integralBaseChangeLattice R₀ R L ρ)

end Representation
