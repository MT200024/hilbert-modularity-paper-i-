/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.RationalCoordinate
public import HilbertModularity.FieldTheory.RatFunc.InertiaConstants
public import HilbertModularity.Geometry.Etale.ArithmeticFieldFixed
public import HilbertModularity.Geometry.Etale.Pullback

/-! # Cusp inertia acts trivially on the arithmetic base

The conjugacy choices of the finite cusp generators preserve the fact that
inertia fixes algebraic constants. Consequently their actual generic loops
lie in the kernel of the map induced by the structure morphism.
-/

public noncomputable section

namespace RatFunc

variable (K : Type*) [Field K]

/-- A conjugate of finite-coordinate inertia still fixes every algebraic constant. -/
theorem conjugate_affineInertia_fixes_algebraic_constants (a : K)
    (c g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
    (hg : g ∈ (affineInertia K a).map (MulAut.conj c).toMonoidHom)
    (z : AlgebraicClosure (RatFunc K)) (hz : IsIntegral K z) : g z = z := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hg
  change c (d (c.symm z)) = z
  rw [affineInertia_fixes_algebraic_constants K a d hd (c.symm z)
    (hz.map (c.symm.restrictScalars K))]
  exact c.apply_symm_apply z

end RatFunc

namespace AlgebraicGeometry.ProjectiveLine

open CategoryTheory

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
/-- Finite cusp inertia, including arbitrary conjugacy choices, is killed by
the structure-map action on finite étale covers of the constant field. -/
theorem conjugate_affineInertia_mem_arithmetic_kernel (a : K)
    (c g : AlgebraicClosure (RatFunc K) ≃ₐ[RatFunc K] AlgebraicClosure (RatFunc K))
    (hg : g ∈ (RatFunc.affineInertia K a).map (MulAut.conj c).toMonoidHom) :
    Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) g ∈
      (Scheme.etaleFundamentalGroupMap (puncturedToSpec K) (RatFunc K)
        (puncturedRationalPoint K)).ker := by
  change Scheme.etaleFundamentalGroupMap (puncturedToSpec K) (RatFunc K)
    (puncturedRationalPoint K)
    (Scheme.galoisToEtaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) g) = 1
  rw [Scheme.etaleFundamentalGroupMap_galois, puncturedRationalPoint_toSpec]
  let j : AlgebraicClosure K →ₐ[K] AlgebraicClosure (RatFunc K) := IsAlgClosed.lift
  have hfix (z : AlgebraicClosure K) : g (j z) = j z :=
    RatFunc.conjugate_affineInertia_fixes_algebraic_constants K a c g hg (j z)
      ((Algebra.IsIntegral.isIntegral z).map j)
  have h := Scheme.galoisToEtaleFundamentalGroup_eq_one_of_fixes_constants K (RatFunc K)
    (𝟙 (Spec (CommRingCat.of K))) j g hfix
  rw [Category.comp_id] at h
  exact h

end AlgebraicGeometry.ProjectiveLine
