/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedFullPolynomial
public import HilbertModularity.Examples.PrimeFivePolynomialBaseChange
public import HilbertModularity.LinearAlgebra.ReverseCharacteristicPolynomial

/-! # Basis-independent scalar extension of the full dual polynomial

The scalar-extension basis is chosen independently of the original basis.
Both describe the same full Tate operator, so their reverse characteristic
polynomials agree before any selected plus Jacobian is inserted.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open scoped NumberField TensorProduct

namespace HilbertModularity.Examples

open GroupScheme

local instance dualBaseChangeFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Reverse characteristic polynomials of one endomorphism do not depend
on the finite basis used to write its matrix. -/
theorem toMatrix_charpolyRev_eq_of_basis
    {L V ι : Type*} [Field L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Fintype ι] [DecidableEq ι]
    (f : Module.End L V) (b c : Module.Basis ι L V) :
    (LinearMap.toMatrix b b f).charpolyRev =
      (LinearMap.toMatrix c c f).charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

/-- Dual Tate reverse polynomials commute with scalar extension in any
chosen basis of the extended dual, independent of how that basis arose. -/
theorem dualTate_charpolyRev_baseChange_anyBasis
    {K L G V ι : Type*} [Field K] [Field L] [Algebra K L]
    [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (ρ : Representation K G V) (g : G)
    (bK : Module.Basis ι K (Module.Dual K V))
    (bL : Module.Basis ι L (Module.Dual L (L ⊗[K] V))) :
    (LinearMap.toMatrix bL bL ((ρ.baseChange L).dual g)).charpolyRev =
      ((LinearMap.toMatrix bK bK (ρ.dual g)).charpolyRev).map
        (algebraMap K L) := by
  let e := Representation.dualBaseChangeEquiv L ρ
  let c := (Algebra.TensorProduct.basis L bK).map e.toLinearEquiv
  calc
    (LinearMap.toMatrix bL bL ((ρ.baseChange L).dual g)).charpolyRev =
        (LinearMap.toMatrix c c ((ρ.baseChange L).dual g)).charpolyRev :=
      toMatrix_charpolyRev_eq_of_basis ((ρ.baseChange L).dual g) bL c
    _ = ((LinearMap.toMatrix bK bK (ρ.dual g)).charpolyRev).map
          (algebraMap K L) :=
      dualTate_charpolyRev_baseChange (L := L) ρ g bK

/-- The same coefficient-extension identity intrinsically, with no basis
to transport through a concrete group scheme. -/
theorem dualTate_charpolyRev_baseChange_intrinsic
    {K L G V : Type*} [Field K] [Field L] [Algebra K L]
    [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) :
    ((ρ.baseChange L).dual g).charpolyRev =
      ((ρ.dual g).charpolyRev).map (algebraMap K L) := by
  let bK := Module.finBasis K (Module.Dual K V)
  let e := Representation.dualBaseChangeEquiv L ρ
  let bL := (Algebra.TensorProduct.basis L bK).map e.toLinearEquiv
  have h := dualTate_charpolyRev_baseChange_anyBasis ρ g bK bL
  simpa only [LinearMap.charpolyRev_toMatrix] using h

/-- Transport an already established intrinsic polynomial before the
actual abelian variety and coefficient field are inserted. -/
theorem dualTate_charpolyRev_baseChange_of_polynomial
    {K L G V : Type*} [Field K] [Field L] [Algebra K L]
    [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) (R : Polynomial K)
    (hR : (ρ.dual g).charpolyRev = R) :
    ((ρ.baseChange L).dual g).charpolyRev = R.map (algebraMap K L) := by
  exact (dualTate_charpolyRev_baseChange_intrinsic (L := L) ρ g).trans
    (congrArg (fun P : Polynomial K => P.map (algebraMap K L)) hR)

/-- A specified full polynomial certificate controls the same operator
in every basis after any coefficient extension. -/
theorem SelectedDualPolynomialData.charpolyRev_overField_in_basis
    (K : Type*) [Field K]
    (A : CommGrp (Over (Spec (CommRingCat.of K))))
    [FiniteDimensional ℚ_[5] (rationalTate K A.X 5)]
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (R : Polynomial ℚ_[5])
    (D : SelectedDualPolynomialData K A g R)
    (L : Type*) [Field L] [Algebra ℚ_[5] L]
    (bL : Module.Basis (Fin 4) L
      (Module.Dual L (L ⊗[ℚ_[5]] rationalTate K A.X 5))) :
    (LinearMap.toMatrix bL bL
      (((tateRepresentation K A.X 5).baseChange L).dual g)).charpolyRev =
        R.map (algebraMap ℚ_[5] L) := by
  calc
    (LinearMap.toMatrix bL bL
        (((tateRepresentation K A.X 5).baseChange L).dual g)).charpolyRev =
        ((LinearMap.toMatrix D.basis D.basis
          ((tateRepresentation K A.X 5).dual g)).charpolyRev).map
            (algebraMap ℚ_[5] L) :=
      dualTate_charpolyRev_baseChange_anyBasis
        (tateRepresentation K A.X 5) g D.basis bL
    _ = R.map (algebraMap ℚ_[5] L) :=
      congrArg (fun P : Polynomial ℚ_[5] => P.map (algebraMap ℚ_[5] L))
        D.charpolyRev_eq

end HilbertModularity.Examples
