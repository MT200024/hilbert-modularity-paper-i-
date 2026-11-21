/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricResidual
public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicTorsion
public import HilbertModularity.RepresentationTheory.DeterminantRigidity
import Mathlib.NumberTheory.LocalField.Basic

/-! # Determinant reduction for the prime plus family

The exact completed-Tate determinant is an arithmetic premise. Its reduction
on the same plus-family fibre is a formal consequence of the canonical-prime
Tate comparison. See [TripathiGoswamiRevised, Lemma `det-rigidity`].
-/

public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NumberField TensorProduct ValuativeRel

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme ValuativeRel

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

local notation "Kₚ" => realCyclotomicField p
local notation "Rₚ" => 𝓞 Kₚ
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "Sₚ" => AdicCompletion Pₚ Rₚ

private theorem basis_map_repr_apply
    {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    {ι : Type*} (b : Module.Basis ι R M) (e : M ≃ₗ[R] N) (v : M) :
    (b.map e).repr (e v) = b.repr v := by
  rw [Module.Basis.map_repr]
  simp

private theorem toMatrix_map_eq_of_intertwining
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (e : M ≃ₗ[R] N)
    (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (h : ∀ v, e (f v) = g (e v)) :
    LinearMap.toMatrix (b.map e) (b.map e) g =
      LinearMap.toMatrix b b f := by
  ext i j
  simp only [LinearMap.toMatrix_apply,
    Module.Basis.map_apply]
  rw [← h (b j), basis_map_repr_apply]

private theorem toMatrix_baseChange_eq_map
    {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) :
    LinearMap.toMatrix (b.baseChange A) (b.baseChange A) (f.baseChange A) =
      (LinearMap.toMatrix b b f).map (algebraMap R A) := by
  ext i j
  simp only [Matrix.map_apply,
    LinearMap.toMatrix_apply,
    Module.Basis.baseChange_apply,
    LinearMap.baseChange_tmul]
  rw [Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem toMatrix_coordinateAction
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) :
    LinearMap.toMatrix' (b.equivFun.conjRingEquiv f) =
      LinearMap.toMatrix b b f := by
  ext i j
  change b.equivFun (f (b.equivFun.symm (Pi.single j 1))) i = _
  simp only [LinearMap.toMatrix_apply]
  simp

/-- A coordinate entry after base change is the image of the original
coordinate entry. -/
theorem coordinateAction_baseChange_entry
    {R A M : Type*} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M)
    (α : R →+* A) (i j : ι) :
    letI : Algebra R A := α.toAlgebra
    ((b.baseChange A).equivFun.conjRingEquiv (f.baseChange A))
        (Pi.single j 1) i = α ((b.repr (f (b j))) i) := by
  let : Algebra R A := α.toAlgebra
  have hmatrix :
      LinearMap.toMatrix'
          ((b.baseChange A).equivFun.conjRingEquiv (f.baseChange A)) =
        (LinearMap.toMatrix b b f).map α := by
    rw [toMatrix_coordinateAction]
    exact toMatrix_baseChange_eq_map b f
  have h := congrArg (fun N : Matrix ι ι A => N i j) hmatrix
  simpa only [LinearMap.toMatrix'_apply, Matrix.map_apply,
    LinearMap.toMatrix_apply, Module.Basis.coord_apply] using h

private theorem ringEquiv_toMonoidHom_apply
    {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (x : R) : e.toMonoidHom x = e x := by
  rfl

private theorem representation_baseChange_apply
    {R A M G : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Monoid G]
    (ρ : Representation R G M) (g : G) :
    (ρ.baseChange A) g = (ρ g).baseChange A := by
  rfl

/-- Coordinate matrices commute with compatible coefficient extensions. -/
theorem toMatrix_coordinateAction_extension
    {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M)
    (α : A →+* B) (hα : ∀ r : R,
      α (algebraMap R A r) = algebraMap R B r) :
    (LinearMap.toMatrix' ((b.baseChange A).equivFun.conjRingEquiv
      (f.baseChange A))).map α =
    LinearMap.toMatrix' ((b.baseChange B).equivFun.conjRingEquiv
      (f.baseChange B)) := by
  rw [toMatrix_coordinateAction, toMatrix_coordinateAction,
    toMatrix_baseChange_eq_map, toMatrix_baseChange_eq_map]
  ext i j
  exact hα _

/-- Conjugating an endomorphism through a chosen basis does not change its
determinant. The coordinate matrix is the endomorphism matrix in that basis. -/
theorem det_coordinateAction
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) :
    LinearMap.det (b.equivFun.conjRingEquiv f) = LinearMap.det f := by
  rw [← LinearMap.det_toMatrix' (b.equivFun.conjRingEquiv f),
    toMatrix_coordinateAction, LinearMap.det_toMatrix]

/-- Taking coordinates after a coefficient extension specializes the
determinant of the original endomorphism. -/
theorem det_coordinateAction_baseChange
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) :
    LinearMap.det ((b.baseChange A).equivFun.conjRingEquiv (f.baseChange A)) =
      algebraMap R A (LinearMap.det f) := by
  rw [det_coordinateAction, LinearMap.det_baseChange]

/-- Two coefficient specializations of one integral action have the same
residual matrix when their coefficient maps agree after reduction. -/
theorem toMatrix_baseChange_residue_compatibility
    {R A B C M : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [Algebra R A] [Algebra R B]
    [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M)
    (α : A →+* C) (β : B →+* C)
    (h : ∀ r : R, α (algebraMap R A r) = β (algebraMap R B r)) :
    (LinearMap.toMatrix' ((b.baseChange A).equivFun.conjRingEquiv
      (f.baseChange A))).map α =
      (LinearMap.toMatrix (b.baseChange B) (b.baseChange B)
        (f.baseChange B)).map β := by
  rw [toMatrix_coordinateAction, toMatrix_baseChange_eq_map,
    toMatrix_baseChange_eq_map]
  ext i j
  simp only [Matrix.map_apply]
  exact h _

/-- The completed integral Tate lattice belongs to the selected plus-family fibre. -/
@[expose, instance_reducible] def primePlusIntegralTateModule :
    Module Sₚ (integralTate Kₚ (primePlusFiber p hp ξ).X p) :=
  realPrimeIntegralTateModule Kₚ (primePlusFiber p hp ξ) p (by omega)
    (primePlusFiberRealMultiplication p hp ξ)

local instance : Module Sₚ (integralTate Kₚ (primePlusFiber p hp ξ).X p) :=
  primePlusIntegralTateModule p hp ξ

/-- The integral Galois action on that same completed Tate lattice. -/
@[expose] def primePlusIntegralTateRepresentation :
    letI := primePlusIntegralTateModule p hp ξ
    Representation Sₚ (AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ)
      (integralTate Kₚ (primePlusFiber p hp ξ).X p) :=
  realPrimeIntegralTateRepresentation Kₚ (primePlusFiber p hp ξ) p (by omega)
    (primePlusFiberRealMultiplication p hp ξ)

/-- The completed coefficient action has the same underlying Galois action
on each actual compatible torsion point. -/
theorem primePlusIntegralTateRepresentation_apply_native
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ)
    (v : integralTate Kₚ (primePlusFiber p hp ξ).X p) :
    letI := primePlusIntegralTateModule p hp ξ
    primePlusIntegralTateRepresentation p hp ξ g v =
      integralTateRepresentation Kₚ (primePlusFiber p hp ξ).X p g v := by
  simp only [primePlusIntegralTateRepresentation,
    realPrimeIntegralTateRepresentation, primeIntegralTateRepresentation,
    integralTateRepresentation, TateModule.coefficientPrimeRepresentation_apply]

/-- Reduction of the completed Tate lattice of the selected plus Jacobian is
the canonical-prime kernel of that same Jacobian, equivariantly for Galois.
This is the selected-fibre form of the principal-torsion comparison. -/
def primePlusResidualKernelEquiv :
    letI := primePlusIntegralTateModule p hp ξ
    letI := primePlusKernelModule p hp ξ
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    ((primePlusIntegralTateRepresentation p hp ξ).baseChange (Rₚ ⧸ Pₚ)).Equiv
      (primePlusKernelRepresentation p hp ξ) := by
  letI := primePlusIntegralTateModule p hp ξ
  letI := primePlusKernelModule p hp ξ
  letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  exact realPrimeResidualKernelEquiv Kₚ (primePlusFiber p hp ξ) p (by omega)
    (primePlusFiberRealMultiplication p hp ξ)

/-- The completed Tate lattice of the selected plus Jacobian has integral
rank two. Its rank is detected on the actual canonical-prime kernel. -/
theorem finrank_primePlusIntegralTate :
    letI := primePlusIntegralTateModule p hp ξ
    Module.finrank Sₚ (integralTate Kₚ (primePlusFiber p hp ξ).X p) = 2 := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := primePlusKernelModule p hp ξ
  let := primePlusIntegralTateModule p hp ξ
  let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  have := realPrimeIntegralTate_free Kₚ (primePlusFiber p hp ξ) p (by omega)
    (primePlusFiberRealMultiplication p hp ξ)
  have := realPrimeIntegralTate_finite Kₚ (primePlusFiber p hp ξ) p (by omega)
    (primePlusFiberRealMultiplication p hp ξ)
  have := AdicCompletion.isDomain_of_isMaximal_span (realPrimeGenerator p)
    (realPrimeGenerator_ne_zero p (by omega))
  have h := (primePlusResidualKernelEquiv p hp ξ).toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h
  exact h.trans (finrank_primePlusKernel p hp ξ)

/-- A rank-two integral coordinate basis on the Tate lattice of the selected
plus Jacobian. Choices of coordinates do not alter the underlying action. -/
def primePlusIntegralTateBasis :
    letI := primePlusIntegralTateModule p hp ξ
    Module.Basis (Fin 2) Sₚ
      (integralTate Kₚ (primePlusFiber p hp ξ).X p) := by
  letI := realPrimeGenerator_isMaximal p (by omega)
  letI := primePlusIntegralTateModule p hp ξ
  have := realPrimeIntegralTate_free Kₚ (primePlusFiber p hp ξ) p (by omega)
    (primePlusFiberRealMultiplication p hp ξ)
  have := realPrimeIntegralTate_finite Kₚ (primePlusFiber p hp ξ) p (by omega)
    (primePlusFiberRealMultiplication p hp ξ)
  have := AdicCompletion.isDomain_of_isMaximal_span (realPrimeGenerator p)
    (realPrimeGenerator_ne_zero p (by omega))
  exact Module.finBasisOfFinrankEq Sₚ _ (finrank_primePlusIntegralTate p hp ξ)

/-- Residual coordinates obtained by reducing the integral coordinates of
the same selected plus Jacobian. -/
def primePlusResidualTateBasis :
    letI := primePlusIntegralTateModule p hp ξ
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    Module.Basis (Fin 2) (Rₚ ⧸ Pₚ)
      ((Rₚ ⧸ Pₚ) ⊗[Sₚ] (integralTate Kₚ (primePlusFiber p hp ξ).X p)) := by
  letI := primePlusIntegralTateModule p hp ξ
  letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  exact (primePlusIntegralTateBasis p hp ξ).baseChange (Rₚ ⧸ Pₚ)

/-- The residual basis is the reduction of the chosen integral Tate basis. -/
theorem primePlusResidualTateBasis_eq_baseChange :
    letI := primePlusIntegralTateModule p hp ξ
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    primePlusResidualTateBasis p hp ξ =
      (primePlusIntegralTateBasis p hp ξ).baseChange (Rₚ ⧸ Pₚ) := by
  rfl

/-- The action matrix on a coefficient extension of the selected Jacobian's
integral Tate lattice is obtained by applying the coefficient map entrywise
to its integral action matrix. -/
theorem primePlusIntegralTateMatrix_baseChange
    {A : Type*} [CommSemiring A] (β : Sₚ →+* A)
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    letI := primePlusIntegralTateModule p hp ξ
    letI : Algebra Sₚ A := β.toAlgebra
    LinearMap.toMatrix ((primePlusIntegralTateBasis p hp ξ).baseChange A)
        ((primePlusIntegralTateBasis p hp ξ).baseChange A)
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange A g) =
      (LinearMap.toMatrix (primePlusIntegralTateBasis p hp ξ)
        (primePlusIntegralTateBasis p hp ξ)
        (primePlusIntegralTateRepresentation p hp ξ g)).map β := by
  let := primePlusIntegralTateModule p hp ξ
  let : Algebra Sₚ A := β.toAlgebra
  exact toMatrix_baseChange_eq_map
    (primePlusIntegralTateBasis p hp ξ)
    (primePlusIntegralTateRepresentation p hp ξ g)

/-- Coordinates for the Galois action of the selected plus Jacobian after an
integral coefficient extension. The action is conjugated through the basis of
the same completed Tate lattice. -/
def primePlusIntegralTateCoordinateAction
    {A : Type*} [CommRing A] (β : Sₚ →+* A) :
    Representation A (AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ)
      (Fin 2 → A) := by
  letI := primePlusIntegralTateModule p hp ξ
  letI : Algebra Sₚ A := β.toAlgebra
  exact ((primePlusIntegralTateBasis p hp ξ).baseChange A).equivFun.conjRingEquiv.toMonoidHom.comp
    ((primePlusIntegralTateRepresentation p hp ξ).baseChange A)

/-- The selected integral coordinate action is the conjugated action on the
base-changed Tate lattice. This equation exposes the chosen action across
module boundaries without exposing its implementation. -/
theorem primePlusIntegralTateCoordinateAction_apply
    {A : Type*} [CommRing A] (β : Sₚ →+* A)
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    letI := primePlusIntegralTateModule p hp ξ
    letI : Algebra Sₚ A := β.toAlgebra
    primePlusIntegralTateCoordinateAction p hp ξ β g =
      ((primePlusIntegralTateBasis p hp ξ).baseChange A).equivFun.conjRingEquiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange A g) := by
  simp only [primePlusIntegralTateCoordinateAction, MonoidHom.comp_apply,
    ringEquiv_toMonoidHom_apply]

/-- The field-valued coordinates are obtained from the *same* selected
Jacobian lattice and basis as the integral coordinates. An integral
coefficient map supplies the field map by inclusion. -/
def primePlusTateFieldCoordinateAction
    {E : Type*} [Field E] [ValuativeRel E] (β : Sₚ →+* 𝒪[E]) :
    Representation E (AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ)
      (Fin 2 → E) :=
  primePlusIntegralTateCoordinateAction p hp ξ ((𝒪[E]).subtype.comp β)

/-- The field coordinates of the selected Jacobian are conjugated from its
chosen integral Tate basis. -/
theorem primePlusTateFieldCoordinateAction_apply
    {E : Type*} [Field E] [ValuativeRel E] (β : Sₚ →+* 𝒪[E])
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    letI := primePlusIntegralTateModule p hp ξ
    letI : Algebra Sₚ E := ((𝒪[E]).subtype.comp β).toAlgebra
    primePlusTateFieldCoordinateAction p hp ξ β g =
      ((primePlusIntegralTateBasis p hp ξ).baseChange E).equivFun.conjRingEquiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange E g) := by
  simpa only [primePlusTateFieldCoordinateAction] using
    (primePlusIntegralTateCoordinateAction_apply p hp ξ
      ((𝒪[E]).subtype.comp β) g)

/-- Extending the selected Jacobian's integral Tate coordinates to the
coefficient field gives its field coordinate action entry by entry. Both
actions use the same basis before coefficient extension. -/
theorem primePlusTateFieldCoordinateAction_matrix
    {E : Type*} [Field E] [ValuativeRel E] (β : Sₚ →+* 𝒪[E])
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    (LinearMap.toMatrix' (primePlusIntegralTateCoordinateAction p hp ξ β g)).map
      (𝒪[E]).subtype =
    LinearMap.toMatrix' (primePlusTateFieldCoordinateAction p hp ξ β g) := by
  let := primePlusIntegralTateModule p hp ξ
  let : Algebra Sₚ (𝒪[E]) := β.toAlgebra
  let : Algebra Sₚ E := ((𝒪[E]).subtype.comp β).toAlgebra
  have h := toMatrix_coordinateAction_extension
    (R := Sₚ) (A := 𝒪[E]) (B := E)
    (M := integralTate Kₚ (primePlusFiber p hp ξ).X p) (ι := Fin 2)
    (primePlusIntegralTateBasis p hp ξ)
    (primePlusIntegralTateRepresentation p hp ξ g)
    (𝒪[E]).subtype (fun _ => rfl)
  simpa only [primePlusIntegralTateCoordinateAction_apply,
    primePlusTateFieldCoordinateAction,
    representation_baseChange_apply] using h

/-- The integral coordinate action used in the residual calculation is an
integral model of the selected Jacobian's field coordinate action. -/
theorem primePlusTateFieldCoordinateAction_integral_coeff
    {E : Type*} [Field E] [ValuativeRel E] (β : Sₚ →+* 𝒪[E]) :
    ∀ g i j,
      ((primePlusIntegralTateCoordinateAction p hp ξ β g (Pi.single j 1) i :
        𝒪[E]) : E) =
      primePlusTateFieldCoordinateAction p hp ξ β g (Pi.single j 1) i := by
  intro g i j
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) E => M i j)
    (primePlusTateFieldCoordinateAction_matrix p hp ξ β g)
  have hc (x : 𝒪[E]) : (𝒪[E]).subtype x = (x : E) := rfl
  simpa only [Matrix.map_apply, LinearMap.toMatrix'_apply, hc] using h

/-- Transport coordinates from the reduction of the selected integral Tate
lattice to the actual canonical-prime kernel, using the equivariant map above. -/
def primePlusKernelBasisOfResidualTate
    (b : letI := primePlusIntegralTateModule p hp ξ
      letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
      Module.Basis (Fin 2) (Rₚ ⧸ Pₚ)
        ((Rₚ ⧸ Pₚ) ⊗[Sₚ] (integralTate Kₚ (primePlusFiber p hp ξ).X p))) :
    letI := primePlusKernelModule p hp ξ
    Module.Basis (Fin 2) (Rₚ ⧸ Pₚ)
      (Points Kₚ (AlgebraicClosure Kₚ) (primePlusKernel p hp ξ).X) := by
  letI := primePlusIntegralTateModule p hp ξ
  letI := primePlusKernelModule p hp ξ
  letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  exact b.map (primePlusResidualKernelEquiv p hp ξ).toLinearEquiv

/-- In coordinates transported from the same integral Tate lattice, the
canonical-prime kernel action has exactly its residual Tate matrix. This
uses the Galois-equivariant principal-torsion comparison, with no separately
chosen two-dimensional representation. -/
theorem primePlusKernelMatrix_eq_residualTateMatrix
    (b : letI := primePlusIntegralTateModule p hp ξ
      letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
      Module.Basis (Fin 2) (Rₚ ⧸ Pₚ)
        ((Rₚ ⧸ Pₚ) ⊗[Sₚ] (integralTate Kₚ (primePlusFiber p hp ξ).X p)))
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    letI := primePlusIntegralTateModule p hp ξ
    letI := primePlusKernelModule p hp ξ
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    LinearMap.toMatrix (primePlusKernelBasisOfResidualTate p hp ξ b)
        (primePlusKernelBasisOfResidualTate p hp ξ b)
        (primePlusKernelRepresentation p hp ξ g) =
      LinearMap.toMatrix b b
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange (Rₚ ⧸ Pₚ) g) := by
  let := primePlusIntegralTateModule p hp ξ
  let := primePlusKernelModule p hp ξ
  let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  exact toMatrix_map_eq_of_intertwining b
    (primePlusResidualKernelEquiv p hp ξ).toLinearEquiv
    ((primePlusIntegralTateRepresentation p hp ξ).baseChange (Rₚ ⧸ Pₚ) g)
    (primePlusKernelRepresentation p hp ξ g)
    (fun v => (primePlusResidualKernelEquiv p hp ξ).toIntertwiningMap.isIntertwining
      _ _ g v)

/-- A coefficient specialization of the selected Jacobian's integral Tate
action has the canonical-prime kernel as its residual representation whenever
its coefficient map reduces to the canonical completion map. Both matrices
come from the same integral Tate basis. -/
theorem primePlusCoefficientSpecialization_kernelMatrix
    {A : Type*} [CommRing A] (β : Sₚ →+* A)
    (α : A →+* (Rₚ ⧸ Pₚ))
    (hαβ : ∀ r : Sₚ,
      α (β r) = (AdicCompletion.evalOneₐ Pₚ).toRingHom r)
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    letI := primePlusIntegralTateModule p hp ξ
    letI := primePlusKernelModule p hp ξ
    (LinearMap.toMatrix (primePlusIntegralTateBasis p hp ξ)
      (primePlusIntegralTateBasis p hp ξ)
      (primePlusIntegralTateRepresentation p hp ξ g)).map (α.comp β) =
      LinearMap.toMatrix
        (primePlusKernelBasisOfResidualTate p hp ξ
          (primePlusResidualTateBasis p hp ξ))
        (primePlusKernelBasisOfResidualTate p hp ξ
          (primePlusResidualTateBasis p hp ξ))
        (primePlusKernelRepresentation p hp ξ g) := by
  let := primePlusIntegralTateModule p hp ξ
  let := primePlusKernelModule p hp ξ
  let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  calc
    _ = (LinearMap.toMatrix (primePlusIntegralTateBasis p hp ξ)
          (primePlusIntegralTateBasis p hp ξ)
          (primePlusIntegralTateRepresentation p hp ξ g)).map
          (AdicCompletion.evalOneₐ Pₚ).toRingHom := by
            ext i j
            exact hαβ _
    _ = LinearMap.toMatrix (primePlusResidualTateBasis p hp ξ)
          (primePlusResidualTateBasis p hp ξ)
          ((primePlusIntegralTateRepresentation p hp ξ).baseChange (Rₚ ⧸ Pₚ) g) := by
            simpa only [primePlusResidualTateBasis] using
              (primePlusIntegralTateMatrix_baseChange p hp ξ
                (AdicCompletion.evalOneₐ Pₚ).toRingHom g).symm
    _ = _ := (primePlusKernelMatrix_eq_residualTateMatrix p hp ξ
      (primePlusResidualTateBasis p hp ξ) g).symm

/-- The residue of any supplied integral coefficient map out of the completed
real cyclotomic prime is the canonical residue map. Total ramification makes
the image of the prime generator nilpotent in characteristic `p`; its field
image is therefore zero. The completion map consequently factors through the
prime field, where a ring endomorphism must be the identity. -/
theorem primePlusIntegralCoefficient_residue
    (hp : 5 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (β : Sₚ →+* 𝒪[E])
    (κ : (Rₚ ⧸ Pₚ) ≃+* (𝒪[E] ⧸ 𝓂[E]))
    (r : Sₚ) :
    Ideal.Quotient.mk (𝓂[E]) (β r) =
      κ ((AdicCompletion.evalOneₐ Pₚ).toRingHom r) := by
  let k := 𝒪[E] ⧸ 𝓂[E]
  let α : Sₚ →+* k := (Ideal.Quotient.mk (𝓂[E])).comp β
  let γ : Sₚ →+* k := κ.toRingHom.comp (AdicCompletion.evalOneₐ Pₚ).toRingHom
  have hp2 : p ≠ 2 := by omega
  have hpP : (p : Rₚ) ∈ Pₚ :=
    Ideal.mem_span_singleton.mpr (realPrimeGenerator_dvd_conductor p hp2)
  have hpquot : ((p : Rₚ) : Rₚ ⧸ Pₚ) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hpzero : (p : k) = 0 := by
    simpa using congrArg κ hpquot
  have hpowmem : (realPrimeGenerator p) ^ ((p - 1) / 2) ∈
      (Ideal.span {(p : Rₚ)} : Ideal Rₚ) := by
    rw [← span_realPrimeGenerator_pow p hp2, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hpowmem
  have hπpow : α (algebraMap Rₚ Sₚ (realPrimeGenerator p)) ^ ((p - 1) / 2) = 0 := by
    calc
      _ = α (algebraMap Rₚ Sₚ ((realPrimeGenerator p) ^ ((p - 1) / 2))) := by simp
      _ = α (algebraMap Rₚ Sₚ ((p : Rₚ) * c)) := by rw [hc]
      _ = 0 := by simp [hpzero]
  have hπ : α (algebraMap Rₚ Sₚ (realPrimeGenerator p)) = 0 := by
    by_contra hn
    exact (pow_ne_zero _ hn) hπpow
  have hker : RingHom.ker (AdicCompletion.evalOneₐ Pₚ).toRingHom ≤ RingHom.ker α := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map Pₚ (Submodule.fg_span_singleton _)]
    rw [Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro x ⟨y, hy, rfl⟩
    have : y = realPrimeGenerator p := Set.mem_singleton_iff.mp hy
    subst y
    exact hπ
  have hkerγ : RingHom.ker γ ≤ RingHom.ker α := by
    intro x hx
    apply hker
    change γ x = 0 at hx
    change (AdicCompletion.evalOneₐ Pₚ).toRingHom x = 0
    exact κ.injective (by simpa [γ] using hx)
  have hγ : Function.Surjective γ := by
    intro x
    obtain ⟨y, rfl⟩ := κ.surjective x
    have hsurj : Function.Surjective (AdicCompletion.evalOneₐ Pₚ) := by
      exact AdicCompletion.evalOneₐ_surjective Pₚ
    obtain ⟨z, hz⟩ := hsurj y
    exact ⟨z, by simpa [γ] using congrArg κ hz⟩
  let δ : k →+* k := (γ.liftOfSurjective hγ) ⟨α, hkerγ⟩
  have hδγ : δ.comp γ = α := γ.liftOfSurjective_comp hγ ⟨α, hkerγ⟩
  let e : k ≃+* ZMod p := κ.symm.trans (realPrimeResidueEquiv p hp2)
  have hδ : δ = RingHom.id k := by
    have h := RingHom.ext_zmod
      (e.toRingHom.comp (δ.comp e.symm.toRingHom)) (RingHom.id (ZMod p))
    ext x
    have hx := congrArg (fun f : ZMod p →+* ZMod p => f (e x)) h
    simpa [e] using e.injective hx
  have hαγ : α = γ := by
    rw [← hδγ, hδ]
    rfl
  exact congrArg (fun f : Sₚ →+* k => f r) hαγ

/-- A coefficient map into an integral valuation ring carries the chosen
selected-Jacobian Tate action to the same residual action as the canonical
prime kernel. Residue compatibility follows from total ramification and the
prime-field quotient; the matrix comparison is then formal. -/
theorem primePlusIntegralCoordinateAction_residualMatrix
    {E : Type*} [Field E] [ValuativeRel E]
    (β : Sₚ →+* 𝒪[E])
    (κ : (Rₚ ⧸ Pₚ) ≃+* (𝒪[E] ⧸ 𝓂[E]))
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    letI := primePlusIntegralTateModule p hp ξ
    letI : Algebra Sₚ (𝒪[E]) := β.toAlgebra
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    (LinearMap.toMatrix'
      (((primePlusIntegralTateBasis p hp ξ).baseChange (𝒪[E])).equivFun.conjRingEquiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange (𝒪[E]) g))).map
          (Ideal.Quotient.mk (𝓂[E])) =
      (LinearMap.toMatrix
        ((primePlusIntegralTateBasis p hp ξ).baseChange (Rₚ ⧸ Pₚ))
        ((primePlusIntegralTateBasis p hp ξ).baseChange (Rₚ ⧸ Pₚ))
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange
          (Rₚ ⧸ Pₚ) g)).map κ.toRingHom := by
  let := primePlusIntegralTateModule p hp ξ
  let : Algebra Sₚ (𝒪[E]) := β.toAlgebra
  let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  exact toMatrix_baseChange_residue_compatibility
      (primePlusIntegralTateBasis p hp ξ)
      (primePlusIntegralTateRepresentation p hp ξ g)
      (Ideal.Quotient.mk (𝓂[E])) κ.toRingHom
      (primePlusIntegralCoefficient_residue p hp β κ)

/-- The residual matrix of the selected integral Tate action is the matrix on
the canonical-prime kernel, in bases transported from the same Tate lattice. -/
theorem primePlusIntegralCoordinateAction_kernelMatrix
    {E : Type*} [Field E] [ValuativeRel E]
    (β : Sₚ →+* 𝒪[E])
    (κ : (Rₚ ⧸ Pₚ) ≃+* (𝒪[E] ⧸ 𝓂[E]))
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    letI := primePlusIntegralTateModule p hp ξ
    letI := primePlusKernelModule p hp ξ
    letI : Algebra Sₚ (𝒪[E]) := β.toAlgebra
    letI := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
    (LinearMap.toMatrix
      (primePlusKernelBasisOfResidualTate p hp ξ
        (primePlusResidualTateBasis p hp ξ))
      (primePlusKernelBasisOfResidualTate p hp ξ
        (primePlusResidualTateBasis p hp ξ))
      (primePlusKernelRepresentation p hp ξ g)).map κ.toRingHom =
    (LinearMap.toMatrix'
      (((primePlusIntegralTateBasis p hp ξ).baseChange (𝒪[E])).equivFun.conjRingEquiv
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange (𝒪[E]) g))).map
      (Ideal.Quotient.mk (𝓂[E])) := by
  let := primePlusIntegralTateModule p hp ξ
  let := primePlusKernelModule p hp ξ
  let : Algebra Sₚ (𝒪[E]) := β.toAlgebra
  let := (AdicCompletion.evalOneₐ Pₚ).toRingHom.toAlgebra
  calc
    _ = (LinearMap.toMatrix (primePlusResidualTateBasis p hp ξ)
        (primePlusResidualTateBasis p hp ξ)
        ((primePlusIntegralTateRepresentation p hp ξ).baseChange (Rₚ ⧸ Pₚ) g)).map
          κ.toRingHom :=
      congrArg (fun M => M.map κ.toRingHom)
        (primePlusKernelMatrix_eq_residualTateMatrix p hp ξ
          (primePlusResidualTateBasis p hp ξ) g)
    _ = _ := by
      simpa only [primePlusResidualTateBasis] using
          (primePlusIntegralCoordinateAction_residualMatrix p hp ξ β κ g).symm

/-- Infinitely many auxiliary residual determinants determine the exact
determinant of the *chosen fibre's* completed Tate factor. The algebraic
Frobenius values, their compatibility with the same labelled auxiliary
factors, and their integral-lattice residual congruences are explicit
inputs. The conclusion concerns the selected plus Jacobian, not a separately
chosen Darmon witness. The residual identity is [DarmonMestre, Section 4,
printed p. 309, display after (6)], with `s = 2t - 1`; its specialization
and same-lattice comparison are not asserted by that display. See
[TripathiGoswamiRevised, Lemmas `labelled-RM-compat` and `det-rigidity`]. -/
theorem primePlusIntegralTate_determinant_of_auxiliaryCongruences
    (L : Type*) [Field L] [TopologicalSpace L] [IsTopologicalRing L]
    [T2Space L] [Algebra Sₚ L] [IsFractionRing Sₚ L] [Algebra Kₚ L]
    {κ I J : Type*} [Fintype κ] [DecidableEq κ]
    [TopologicalSpace
      (L ⊗[Sₚ] (integralTate Kₚ (primePlusFiber p hp ξ).X p))]
    (b : letI := primePlusIntegralTateModule p hp ξ
      Module.Basis κ L (L ⊗[Sₚ] (integralTate Kₚ (primePlusFiber p hp ξ).X p)))
    (hb : ∀ k, Continuous (b.coord k))
    (hτ : letI := primePlusIntegralTateModule p hp ξ
      ∀ w, Continuous (fun g =>
        (primePlusIntegralTateRepresentation p hp ξ).baseChange L g w))
    (μ : (AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) →ₜ* Lˣ)
    (hμ : ∀ g,
      (μ g : L) = algebraMap Sₚ L
        (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Kₚ p g : ℤ_[p]))))
    (P : J → IsDedekindDomain.HeightOneSpectrum Rₚ) (V : J → Type*)
    [∀ j, AddCommGroup (V j)]
    [∀ j, Module ((P j).adicCompletion Kₚ) (V j)]
    [∀ j, Module ((P j).adicCompletionIntegers Kₚ) (V j)]
    [∀ j, IsScalarTower ((P j).adicCompletionIntegers Kₚ)
      ((P j).adicCompletion Kₚ) (V j)]
    (ρ : ∀ j, Representation ((P j).adicCompletion Kₚ)
      (AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) (V j))
    (M : ∀ j, Subrepresentation
      ((ρ j).restrictScalars ((P j).adicCompletionIntegers Kₚ)))
    [∀ j, Submodule.IsLattice ((P j).adicCompletion Kₚ) (M j).toSubmodule]
    {ι : J → Type*}
    (a : ∀ j, Module.Basis (ι j) ((P j).adicCompletionIntegers Kₚ)
      (M j).toSubmodule)
    (t : I → AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ)
    (ht : DenseRange t) (x y : I → Kₚ)
    (hx : ∀ i,
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L (t i)) =
        algebraMap Kₚ L (x i))
    (hy : ∀ i, (μ (t i) : L) = algebraMap Kₚ L (y i))
    (S : I → Set J)
    (hS : ∀ i, ((fun j => ringChar (Rₚ ⧸ (P j).asIdeal)) '' S i).Infinite)
    (haux : ∀ i j, j ∈ S i →
      LinearMap.det (ρ j (t i)) =
        algebraMap Kₚ ((P j).adicCompletion Kₚ) (x i))
    (hres : ∀ i j, j ∈ S i →
      ∀ hu : (P j).valuation Kₚ (y i) = 1,
      LinearMap.det (((M j).toRepresentation.baseChange
        (IsLocalRing.ResidueField ((P j).adicCompletionIntegers Kₚ))) (t i)) =
        (P j).completionResidueMap ((P j).specialization (y i) hu.le)) :
    letI := primePlusIntegralTateModule p hp ξ
    ∀ g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ,
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Kₚ p g : ℤ_[p]))) := by
  have hdet := Representation.continuousDeterminantCharacter_eq_of_infinite_residual_congruences
    b hb ((primePlusIntegralTateRepresentation p hp ξ).baseChange L) hτ μ
    P V ρ M a t ht x y hx hy S hS haux hres
  intro g
  calc
    LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L g) =
        (Representation.continuousDeterminantCharacter b hb
          ((primePlusIntegralTateRepresentation p hp ξ).baseChange L) hτ g : L) := by
            exact (Representation.continuousDeterminantCharacter_coe b hb
              ((primePlusIntegralTateRepresentation p hp ξ).baseChange L) hτ g).symm
    _ = (μ g : L) := congrArg Units.val (congrArg (fun f => f g) hdet)
    _ = _ := hμ g

/-- Exact determinant on the selected family's completed Tate factor reduces
to the native cyclotomic determinant on its canonical-prime kernel. -/
theorem primePlusResidualDeterminant_of_integralTate
    (L : Type*) [Field L] [Algebra Sₚ L] [FaithfulSMul Sₚ L]
    (hdet : ∀ g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ,
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Kₚ p g : ℤ_[p])))) :
    letI := coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
      (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
    ∀ g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ,
      realPrimeResidueEquiv p (by omega)
        (LinearMap.det (coefficientKernelRepresentation Kₚ (primePlusFiber p hp ξ)
          Rₚ (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p) g)) =
          (Field.cyclotomicCharacter Kₚ p g : ℤ_[p]).toZMod := by
  let := coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
    (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
  intro g
  with_reducible
    exact det_realPrimeKernel_eq_cyclotomic Kₚ (primePlusFiber p hp ξ) p (by omega)
      (primePlusFiberRealMultiplication p hp ξ) L g (by
        simpa only [primePlusIntegralTateRepresentation, primePlusIntegralTateModule]
          using hdet g)

/-- The residual determinant character of the actual selected plus-family
kernel, conditional on the exact completed-Tate determinant. -/
theorem primePlusResidualDeterminantCharacter_of_integralTate
    (L : Type*) [Field L] [Algebra Sₚ L] [FaithfulSMul Sₚ L]
    (hdet : ∀ g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ,
      letI := primePlusIntegralTateModule p hp ξ
      LinearMap.det ((primePlusIntegralTateRepresentation p hp ξ).baseChange L g) =
        algebraMap Sₚ L
          (TateModule.coefficientPrimeRingEquiv p Rₚ Pₚ ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega)) (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p Rₚ (Field.cyclotomicCharacter Kₚ p g : ℤ_[p])))) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
      (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
    (coefficientKernelRepresentation Kₚ (primePlusFiber p hp ξ) Rₚ
      (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)).determinantCharacter =
      realPrimeResidualCyclotomicCharacter Kₚ p (by omega) := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
    (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply (realPrimeResidueEquiv p (by omega)).injective
  exact (primePlusResidualDeterminant_of_integralTate p hp ξ L hdet g).trans
    (realPrimeResidualCyclotomicCharacter_residue Kₚ p (by omega) g).symm

end HilbertModularity.Hypergeometric
