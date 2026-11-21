/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GenericFundamentalGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # The generic Galois quotient defining finite étale monodromy

For a normal affine base with perfect fraction field, the actual finite étale
fundamental group is the topological quotient of the native arithmetic Galois
group by the kernel of its action on finite étale covers.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme
universe u
variable (R F : Type u) [CommRing R] [IsIntegrallyClosed R]
  [Field F] [PerfectField F] [Algebra R F] [IsFractionRing R F]

/-- The actual generic arithmetic kernel gives the finite étale fundamental group
as a topological group quotient. -/
def genericGaloisQuotientEquiv :
    ((AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ⧸
      (galoisToEtaleFundamentalGroup F
        (Spec.map (CommRingCat.ofHom (algebraMap R F)))).ker) ≃ₜ*
      etaleFundamentalGroup F (Spec.map (CommRingCat.ofHom (algebraMap R F))) := by
  let φ := galoisToEtaleFundamentalGroup F (Spec.map (CommRingCat.ofHom (algebraMap R F)))
  let e := QuotientGroup.quotientKerEquivOfSurjective φ
    (galoisToEtaleFundamentalGroup_surjective_of_fractionField R F)
  have hc : Continuous e := (QuotientGroup.isQuotientMap_mk φ.ker).continuous_iff.mpr
    (continuous_galoisToEtaleFundamentalGroup F _)
  exact { e with
    continuous_toFun := hc
    continuous_invFun := hc.continuous_symm_of_equiv_compact_to_t2 }

/-- The quotient identification retains the original arithmetic action on every class. -/
@[simp]
theorem genericGaloisQuotientEquiv_mk
    (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    genericGaloisQuotientEquiv R F (QuotientGroup.mk g) =
      galoisToEtaleFundamentalGroup F (Spec.map (CommRingCat.ofHom (algebraMap R F))) g := rfl

end AlgebraicGeometry.Scheme
