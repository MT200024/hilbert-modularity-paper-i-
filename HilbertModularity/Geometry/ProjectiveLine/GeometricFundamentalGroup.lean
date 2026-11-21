/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.GeometricFundamentalGroup
public import HilbertModularity.Geometry.ProjectiveLine.CuspInertia

/-! # Geometric monodromy of the actual punctured parameter line

The geometric group is defined on the scheme after the genuine extension to
the algebraic closure of its ground field. Inertia is pulled back through the
actual scheme-induced map to the original generic fundamental group.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.ProjectiveLine
universe u
variable (K : Type u) [Field K] [CharZero K]

/-- The actual geometric fundamental group of the three-punctured projective line. -/
abbrev puncturedGeometricFundamentalGroup : ProfiniteGrp :=
  Scheme.geometricFundamentalGroup K (RatFunc K) (puncturedToSpec K)
    (puncturedRationalPoint K) (puncturedRationalPoint_toSpec K) IsAlgClosed.lift

/-- The actual geometric base-change projection induces the arithmetic monodromy map. -/
def puncturedGeometricFundamentalGroupMap :
    puncturedGeometricFundamentalGroup K →ₜ*
      Scheme.etaleFundamentalGroup (RatFunc K) (puncturedRationalPoint K) :=
  Scheme.geometricFundamentalGroupMap K (RatFunc K) (puncturedToSpec K)
    (puncturedRationalPoint K) (puncturedRationalPoint_toSpec K) IsAlgClosed.lift

/-- The inverse image of actual finite-coordinate inertia in the geometric base-change group. -/
def puncturedGeometricAffineInertia (a : K) : Subgroup (puncturedGeometricFundamentalGroup K) :=
  (puncturedAffineInertia K a).comap (puncturedGeometricFundamentalGroupMap K).toMonoidHom

/-- The inverse image of actual infinite inertia in the geometric base-change group. -/
def puncturedGeometricInfinityInertia : Subgroup (puncturedGeometricFundamentalGroup K) :=
  (puncturedInfinityInertia K).comap (puncturedGeometricFundamentalGroupMap K).toMonoidHom

end AlgebraicGeometry.ProjectiveLine
