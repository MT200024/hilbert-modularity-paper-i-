/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Examples.PrimeFiveSelectedPolynomialFortyOne

/-! # The pointed level-five count on its original dual Tate carrier -/

public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace HilbertModularity.Examples

open Hyperelliptic GroupScheme

local instance pointedRawFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The checked eleven-prime point counts give a basis-level polynomial on
any pointed Jacobian of the displayed reduced curve, before choosing a
residue quotient or a good model. -/
theorem exists_primeFive_pointedJacobianPolynomial11_basis
    (k : Type*) [Field k] [Fintype k] (hk : Fintype.card k = 11)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (point : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)))
    (pointed : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)))
      point J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation k J.X 5).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        primeFiveNumericalPolynomial11 ℚ_[5] := by
  let D : PrimeFivePointedData k := ⟨J, point, pointed⟩
  have h := PointedPolynomial11.toRaw k D (countedPolynomial11OfData k hk D)
  exact RawSpecialPolynomial11.exists_basis k J h

/-- The analogous forty-one-prime point counts give the full polynomial
on the original pointed Jacobian dual Tate carrier. -/
theorem exists_primeFive_pointedJacobianPolynomial41_basis
    (k : Type*) [Field k] [Fintype k] (hk : Fintype.card k = 41)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (point : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)))
    (pointed : PointedCurveJacobian k
      (Over.mk (AlgebraicGeometry.Hyperelliptic.toSpec
        (primeFivePolynomial k) 3 (primeFivePolynomial_degree k)))
      point J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[5]
      (Module.Dual ℚ_[5] (rationalTate k J.X 5)),
      (LinearMap.toMatrix b b
        ((tateRepresentation k J.X 5).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius k))).charpolyRev =
        primeFiveNumericalPolynomial41 ℚ_[5] := by
  let D : PrimeFivePointedData k := ⟨J, point, pointed⟩
  have h := PointedPolynomial41.toRaw k D (countedPolynomial41OfData k hk D)
  exact RawSpecialPolynomial41.exists_basis k J h

end HilbertModularity.Examples
