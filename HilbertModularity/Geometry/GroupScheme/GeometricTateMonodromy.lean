/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.ProjectiveLine.GeometricFundamentalGroup
public import HilbertModularity.Geometry.GroupScheme.TateMonodromy

/-! # Tate monodromy on the genuine geometric parameter scheme

The actual Tate representation is restricted along the scheme projection from
the geometric base change. This is the representation needed to state the
associated monodromy conclusion of [DarmonFibres, Proposition 3.2].
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry.GroupScheme
universe u
variable (K : Type u) [Field K] [CharZero K]
  (A : CommGrp (Over (ProjectiveLine.punctured K))) (p : ℕ) [Fact p.Prime]
  [∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left]
  [∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left]

/-- The integral Tate action of the actual geometric fundamental group. -/
def integralGeometricTateMonodromy : Representation ℤ_[p]
    (ProjectiveLine.puncturedGeometricFundamentalGroup K)
    (TateModule.integral p
      (Additive (Scheme.geometricPointOver (RatFunc K) (ProjectiveLine.puncturedRationalPoint K) ⟶ A.X))) :=
  (integralTateMonodromy (RatFunc K) (ProjectiveLine.puncturedRationalPoint K) A p).comp
    (ProjectiveLine.puncturedGeometricFundamentalGroupMap K).toMonoidHom

/-- The covariant rational Tate action of the actual geometric fundamental group. -/
def rationalGeometricTateMonodromy : Representation ℚ_[p]
    (ProjectiveLine.puncturedGeometricFundamentalGroup K)
    (TateModule.rational p
      (Additive (Scheme.geometricPointOver (RatFunc K) (ProjectiveLine.puncturedRationalPoint K) ⟶ A.X))) :=
  (rationalTateMonodromy (RatFunc K) (ProjectiveLine.puncturedRationalPoint K) A p).comp
    (ProjectiveLine.puncturedGeometricFundamentalGroupMap K).toMonoidHom

end AlgebraicGeometry.GroupScheme
