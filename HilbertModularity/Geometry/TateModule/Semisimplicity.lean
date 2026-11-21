/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RepresentationTheory.Semisimple

/-! # Semisimplicity of the rational Tate representation

Faltings's theorem is used once, for the actual rational Tate module of an
abelian variety over a number field.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupScheme

/-- Faltings semisimplicity, as stated in [MilneAV, Chapter IV, Appendix,
Theorem 3, p. 159]. The appendix specifies a number field `K`, its absolute
Galois group, an abelian variety `A/K`, and `V_ℓ A = ℚ_ℓ ⊗ T_ℓ A`.
Properness, smoothness and geometric connectedness below make the actual
commutative group scheme an abelian variety. The representation is covariant;
there is no dual, coefficient extension, RM projector or Tate twist in this
named literature input. The cited appendix attributes the theorem to
Faltings, Invent. Math. 73 (1983), 349–366, with erratum 75 (1984), 381. -/
theorem tateRepresentation_isSemisimple
    (K : Type*) [Field K] [NumberField K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (tateRepresentation K A ℓ).IsSemisimpleRepresentation := by
  sorry

end AlgebraicGeometry.GroupScheme
