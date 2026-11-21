/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricDeterminant
public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesInput

/-! # Residual matrix comparison for the selected plus Jacobian

An identification of the actual canonical-prime kernel with the reduction of
the chosen Skinner–Wiles lattice should compare their full Galois actions.
The determinant comparison used in the residual checklist follows from that
matrix comparison. See [TripathiGoswamiRevised, Proposition `SW-checklist`].
-/

public section
noncomputable section

open scoped NumberField Pointwise ValuativeRel
open ValuativeRel NumberField AlgebraicGeometry AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms

/-- A full comparison of two integral residual matrices, over an identified
residue field, gives the determinant comparison. The basis on the left is a
basis of the actual scheme kernel, not an abstract rank-two replacement. -/
theorem residualDeterminant_eq_of_kernelMatrixComparison
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : SkinnerWilesResidualData ρ)
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map
          κ.toRingHom =
        (LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))) :
    letI := primePlusKernelModule p hp ξ
    ∀ g : AbsoluteGalois (realCyclotomicField p),
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        κ (LinearMap.det (primePlusKernelRepresentation p hp ξ g)) := by
  let := primePlusKernelModule p hp ξ
  intro g
  calc
    Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        ((LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).det := by
      rw [← LinearMap.det_toMatrix' (D.integralAction g)]
      exact (Ideal.Quotient.mk (𝓂[E])).map_det _
    _ = ((LinearMap.toMatrix b b
          (primePlusKernelRepresentation p hp ξ g)).map
              κ.toRingHom).det := congrArg Matrix.det (hmat g).symm
    _ = κ (LinearMap.det (primePlusKernelRepresentation p hp ξ g)) := by
      rw [← LinearMap.det_toMatrix b]
      exact (κ.toRingHom.map_det _).symm

/-- A coefficient-compatible identification of the actual canonical-prime
kernel with the chosen residual lattice identifies their Galois matrices.
The coordinate condition is about one map and one basis; no separate matrix
comparison is required. -/
theorem kernelMatrixComparison_of_coordinateIdentification
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (j : Points (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p))
        (primePlusKernel p hp ξ).X ≃+ (Fin 2 → 𝒪[E] ⧸ 𝓂[E]))
    (hequiv : ∀ (g : AbsoluteGalois (realCyclotomicField p)) v,
      j (g • v) =
        ((LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hcoord : letI := primePlusKernelModule p hp ξ
      ∀ v, j v = fun i => κ (b.repr v i)) :
    ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map κ.toRingHom =
      (LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E])) := by
  let := primePlusKernelModule p hp ξ
  intro g
  apply Matrix.ext
  intro i k
  have hcol : j (b k) = Pi.single k 1 := by
    rw [hcoord]
    ext l
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hpoint : primePlusKernelRepresentation p hp ξ g (b k) = g • b k :=
    primePlusKernelRepresentation_apply p hp ξ g (b k)
  calc
    ((LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map κ.toRingHom) i k =
        j (g • b k) i := by
      rw [hcoord, ← hpoint]
      simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
      rfl
    _ = (((LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec (Pi.single k 1)) i := by
      rw [hequiv g (b k), hcol]
    _ = ((LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))) i k := by simp [Matrix.mulVec_single]

/-- Coordinates on the actual selected Jacobian's canonical-prime kernel,
followed by the identified coefficient residue field. This identification is
determined by one kernel basis; it is not an additional arithmetic input. -/
def primePlusKernelCoordinateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X)) :
    Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p))
        (primePlusKernel p hp ξ).X ≃+ (Fin 2 → 𝒪[E] ⧸ 𝓂[E]) := by
  letI := primePlusKernelModule p hp ξ
  exact b.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight (fun _ : Fin 2 => κ.toAddEquiv))

/-- Coordinates through the selected kernel basis and the residue-field map. -/
theorem primePlusKernelCoordinateEquiv_apply
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (x : Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X)
    (i : Fin 2) :
    letI := primePlusKernelModule p hp ξ
    primePlusKernelCoordinateEquiv p hp ξ κ b x i = κ (b.repr x i) := by
  let := primePlusKernelModule p hp ξ
  rfl

/-- If the chosen Skinner–Wiles integral lattice has the same residual matrix
as the selected Jacobian's canonical-prime kernel, its coordinate
identification is automatically Galois equivariant. This uses all matrix
entries, not just the determinant. -/
theorem primePlusKernelCoordinateEquiv_galois_for_action
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (integralAction : Representation (𝒪[E])
      (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → 𝒪[E]))
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map κ.toRingHom =
      (LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E])))
    (g : AbsoluteGalois (realCyclotomicField p))
    (v : Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X) :
    primePlusKernelCoordinateEquiv p hp ξ κ b (g • v) =
      ((LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec
          (primePlusKernelCoordinateEquiv p hp ξ κ b v) := by
  let := primePlusKernelModule p hp ξ
  let j := primePlusKernelCoordinateEquiv p hp ξ κ b
  have hj (w) (i : Fin 2) : j w i = κ (b.repr w i) := rfl
  have haction := primePlusKernelRepresentation_apply p hp ξ g v
  rw [← haction, ← hmat g]
  ext i
  rw [hj, ← LinearMap.toMatrix_mulVec_repr b b
    (primePlusKernelRepresentation p hp ξ g) v]
  simp only [Matrix.mulVec, Matrix.map_apply]
  simp [primePlusKernelCoordinateEquiv]

/-- The residual-data version of the selected kernel coordinate action. -/
theorem primePlusKernelCoordinateEquiv_galois
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (b : letI := primePlusKernelModule p hp ξ
      Module.Basis (Fin 2)
        (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        (Points (realCyclotomicField p)
          (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X))
    (hmat : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := primePlusKernelModule p hp ξ
      (LinearMap.toMatrix b b
        (primePlusKernelRepresentation p hp ξ g)).map κ.toRingHom =
      (LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E])))
    (g : AbsoluteGalois (realCyclotomicField p))
    (v : Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p)) (primePlusKernel p hp ξ).X) :
    primePlusKernelCoordinateEquiv p hp ξ κ b (g • v) =
      ((LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec
          (primePlusKernelCoordinateEquiv p hp ξ κ b v) :=
  primePlusKernelCoordinateEquiv_galois_for_action p hp ξ D.integralAction
    κ b hmat g v

end HilbertModularity.Hypergeometric
