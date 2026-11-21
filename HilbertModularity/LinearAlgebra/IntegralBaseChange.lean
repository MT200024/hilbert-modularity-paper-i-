/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.LatticeImage
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # Integral lattices after scalar extension

For a finite module over an integral coefficient ring, the image of its scalar
extension to a larger integral ring is a full lattice in the scalar extension
to the coefficient field. This is the ambient integral construction used for
Tate factors in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (R₀ R L M : Type*) [CommRing R₀] [CommRing R] [CommRing L]
  [Algebra R₀ R] [Algebra R₀ L] [Algebra R L] [IsScalarTower R₀ R L]
  [AddCommMonoid M] [Module R₀ M]

/-- The canonical map from integral scalar extension to coefficient scalar extension. -/
def integralBaseChangeMap : R ⊗[R₀] M →ₗ[R] L ⊗[R₀] M :=
  (_root_.TensorProduct.mk R₀ L M 1).liftBaseChange R

@[simp]
theorem integralBaseChangeMap_tmul (r : R) (m : M) :
    integralBaseChangeMap R₀ R L M (r ⊗ₜ[R₀] m) = algebraMap R L r ⊗ₜ[R₀] m := by
  simp [integralBaseChangeMap, _root_.TensorProduct.smul_tmul', Algebra.smul_def]

/-- The actual image of integral scalar extension inside the coefficient module. -/
def integralBaseChangeLattice : Submodule R (L ⊗[R₀] M) :=
  LinearMap.range (integralBaseChangeMap R₀ R L M)

/-- A finite integral module produces a full lattice after scalar extension. -/
instance integralBaseChangeLattice_isLattice [Module.Finite R₀ M] :
    Submodule.IsLattice L (integralBaseChangeLattice R₀ R L M) where
  fg := Submodule.fg_range _
  span_eq_top := by
    apply top_unique
    intro t ht
    clear ht
    induction t using _root_.TensorProduct.inductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul a m =>
      have hm : (1 : L) ⊗ₜ[R₀] m ∈ integralBaseChangeLattice R₀ R L M :=
        ⟨(1 : R) ⊗ₜ[R₀] m, by simp⟩
      have hm' : (1 : L) ⊗ₜ[R₀] m ∈
          Submodule.span L (integralBaseChangeLattice R₀ R L M : Set (L ⊗[R₀] M)) :=
        Submodule.subset_span hm
      have hsm := Submodule.smul_mem
        (Submodule.span L (integralBaseChangeLattice R₀ R L M : Set (L ⊗[R₀] M))) a hm'
      simpa only [_root_.TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hsm

end Algebra.TensorProduct
