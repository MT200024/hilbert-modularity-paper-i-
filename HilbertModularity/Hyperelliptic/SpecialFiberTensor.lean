/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberBaseChange
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # Scalar extension of quadratic charts -/

public noncomputable section

open Polynomial
open scoped TensorProduct QuadraticAlgebra

namespace HilbertModularity.Hyperelliptic

section QuadraticTensor

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

private def quadraticBaseMap (a b : A) :
    QuadraticAlgebra A a b →ₐ[A]
      QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b) where
  toRingHom := QuadraticAlgebra.mapCoeffs (algebraMap A B) a b
  commutes' r := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.mapCoeffs]

/-- The scalar-extended quadratic chart maps to the quadratic chart of the extended equation. -/
def quadraticTensorMap (a b : A) :
    (B ⊗[A] QuadraticAlgebra A a b) →ₐ[B]
      QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId B (QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b)))
    (quadraticBaseMap a b) (fun _ _ => Commute.all _ _)

/-- The quadratic generator of the old chart, included in its scalar extension. -/
def quadraticTensorRoot (a b : A) : B ⊗[A] QuadraticAlgebra A a b :=
  (Algebra.TensorProduct.includeRight :
    QuadraticAlgebra A a b →ₐ[A] B ⊗[A] QuadraticAlgebra A a b)
      QuadraticAlgebra.omega

private theorem quadraticTensorRoot_relation (a b : A) :
    quadraticTensorRoot a b * quadraticTensorRoot a b =
      (algebraMap A B a) • (1 : B ⊗[A] QuadraticAlgebra A a b) +
        (algebraMap A B b) • quadraticTensorRoot a b := by
  let j : QuadraticAlgebra A a b →ₐ[A] B ⊗[A] QuadraticAlgebra A a b :=
    Algebra.TensorProduct.includeRight
  change j QuadraticAlgebra.omega * j QuadraticAlgebra.omega = _
  rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  rw [map_add, map_mul, j.commutes, j.commutes]
  have ha : (algebraMap A (B ⊗[A] QuadraticAlgebra A a b)) a =
      (algebraMap B (B ⊗[A] QuadraticAlgebra A a b)) ((algebraMap A B) a) :=
    IsScalarTower.algebraMap_apply A B _ a
  have hb : (algebraMap A (B ⊗[A] QuadraticAlgebra A a b)) b =
      (algebraMap B (B ⊗[A] QuadraticAlgebra A a b)) ((algebraMap A B) b) :=
    IsScalarTower.algebraMap_apply A B _ b
  rw [ha, hb]
  rw [Algebra.smul_def (algebraMap A B a) (1 : B ⊗[A] QuadraticAlgebra A a b)]
  rw [Algebra.smul_def (algebraMap A B b) (quadraticTensorRoot a b)]
  simp only [mul_one, quadraticTensorRoot]
  rfl

/-- Evaluation of the new quadratic generator in the scalar extension. -/
def quadraticTensorInverse (a b : A) :
    QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b) →ₐ[B]
      B ⊗[A] QuadraticAlgebra A a b :=
  QuadraticAlgebra.lift ⟨quadraticTensorRoot a b, quadraticTensorRoot_relation a b⟩

@[simp] theorem quadraticTensorMap_root (a b : A) :
    quadraticTensorMap a b (quadraticTensorRoot a b) =
      (QuadraticAlgebra.omega : QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b)) := by
  simp [quadraticTensorMap, quadraticTensorRoot, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul, quadraticBaseMap]
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.mapCoeffs]

@[simp] theorem quadraticTensorInverse_omega (a b : A) :
    quadraticTensorInverse a b
      (QuadraticAlgebra.omega : QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b)) =
      quadraticTensorRoot a b := by
  simp [quadraticTensorInverse]

theorem quadraticTensorMap_comp_inverse (a b : A) :
    (quadraticTensorMap a b).comp (quadraticTensorInverse a b) =
      AlgHom.id B (QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b)) := by
  apply AlgHom.ext
  intro z
  rw [← QuadraticAlgebra.re_smul_add_im_smul z]
  simp

private theorem quadraticTensorInverse_baseMap (a b : A)
    (z : QuadraticAlgebra A a b) :
    quadraticTensorInverse a b (quadraticBaseMap a b z) =
      (Algebra.TensorProduct.includeRight :
        QuadraticAlgebra A a b →ₐ[A] B ⊗[A] QuadraticAlgebra A a b) z := by
  have hω : quadraticBaseMap a b
      (QuadraticAlgebra.omega : QuadraticAlgebra A a b) =
      (QuadraticAlgebra.omega : QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b)) := by
    apply QuadraticAlgebra.ext <;>
      simp [quadraticBaseMap, QuadraticAlgebra.mapCoeffs]
  conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul z]
  conv_rhs => rw [← QuadraticAlgebra.re_smul_add_im_smul z]
  simp only [map_add, map_smul, map_one, hω]
  simp [Algebra.smul_def, quadraticTensorRoot]

theorem quadraticTensorInverse_comp_map (a b : A) :
    (quadraticTensorInverse a b).comp (quadraticTensorMap a b) =
      AlgHom.id B (B ⊗[A] QuadraticAlgebra A a b) := by
  apply Algebra.TensorProduct.ext'
  intro x z
  simp [quadraticTensorMap, Algebra.TensorProduct.lift_tmul,
    quadraticTensorInverse_baseMap, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- A quadratic chart commutes with arbitrary extension of its coefficient ring. -/
def quadraticTensorEquiv (a b : A) :
    (B ⊗[A] QuadraticAlgebra A a b) ≃ₐ[B]
      QuadraticAlgebra B (algebraMap A B a) (algebraMap A B b) :=
  AlgEquiv.ofAlgHom (quadraticTensorMap a b) (quadraticTensorInverse a b)
    (quadraticTensorMap_comp_inverse a b) (quadraticTensorInverse_comp_map a b)

@[simp] theorem quadraticTensorEquiv_includeRight (a b : A)
    (z : QuadraticAlgebra A a b) :
    quadraticTensorEquiv (B := B) a b
      ((Algebra.TensorProduct.includeRight :
        QuadraticAlgebra A a b →ₐ[A] B ⊗[A] QuadraticAlgebra A a b) z) =
      QuadraticAlgebra.mapCoeffs (algebraMap A B) a b z := by
  simp [quadraticTensorEquiv, quadraticTensorMap, quadraticBaseMap]

/-- Transport the scalar-extension equivalence across equal branch coefficients. -/
def quadraticTensorEquivOfEq (a b : A) (c d : B)
    (ha : algebraMap A B a = c) (hb : algebraMap A B b = d) :
    (B ⊗[A] QuadraticAlgebra A a b) ≃ₐ[B] QuadraticAlgebra B c d := by
  cases ha
  cases hb
  exact quadraticTensorEquiv a b

@[simp] theorem quadraticTensorEquivOfEq_includeRight_re (a b : A) (c d : B)
    (ha : algebraMap A B a = c) (hb : algebraMap A B b = d)
    (z : QuadraticAlgebra A a b) :
    ((quadraticTensorEquivOfEq a b c d ha hb)
      ((Algebra.TensorProduct.includeRight :
        QuadraticAlgebra A a b →ₐ[A] B ⊗[A] QuadraticAlgebra A a b) z)).re =
      algebraMap A B z.re := by
  cases ha
  cases hb
  simpa [quadraticTensorEquivOfEq] using congrArg QuadraticAlgebra.re
    (quadraticTensorEquiv_includeRight (B := B) a b z)

@[simp] theorem quadraticTensorEquivOfEq_includeRight_im (a b : A) (c d : B)
    (ha : algebraMap A B a = c) (hb : algebraMap A B b = d)
    (z : QuadraticAlgebra A a b) :
    ((quadraticTensorEquivOfEq a b c d ha hb)
      ((Algebra.TensorProduct.includeRight :
        QuadraticAlgebra A a b →ₐ[A] B ⊗[A] QuadraticAlgebra A a b) z)).im =
      algebraMap A B z.im := by
  cases ha
  cases hb
  simpa [quadraticTensorEquivOfEq] using congrArg QuadraticAlgebra.im
    (quadraticTensorEquiv_includeRight (B := B) a b z)

end QuadraticTensor

section ChartTensor

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

local instance : Algebra R[X] S[X] :=
  (Polynomial.mapRingHom (algebraMap R S)).toAlgebra

/-- Scalar extension of the finite quadratic chart of the scaled cover. -/
def finiteChartTensorEquiv (P : R[X]) (t : R) :
    (S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) ≃ₐ[S[X]]
      AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t)) := by
  have hmap : (algebraMap R[X] S[X]) =
      Polynomial.mapRingHom (algebraMap R S) := rfl
  have ha : (algebraMap R[X] S[X]) (finiteBranchPolynomial P t) =
      finiteBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t) := by
    rw [hmap]
    exact finiteBranchPolynomial_map (algebraMap R S) P t
  have hb : (algebraMap R[X] S[X]) 0 = 0 := map_zero _
  change (S[X] ⊗[R[X]] QuadraticAlgebra R[X] (finiteBranchPolynomial P t) 0) ≃ₐ[S[X]]
    QuadraticAlgebra S[X]
      (finiteBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t)) 0
  exact quadraticTensorEquivOfEq (A := R[X]) (B := S[X])
    (finiteBranchPolynomial P t) 0 _ _ ha hb

/-- Scalar extension of the reciprocal quadratic chart, with its degree retained. -/
def infinityChartTensorEquiv (P : R[X]) (t : R)
    (hdeg : (P.map (algebraMap R S)).natDegree = P.natDegree) :
    (S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) ≃ₐ[S[X]]
      AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t)) := by
  have hmap : (algebraMap R[X] S[X]) =
      Polynomial.mapRingHom (algebraMap R S) := rfl
  have ha : (algebraMap R[X] S[X]) (infinityBranchPolynomial P t) =
      infinityBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t) := by
    rw [hmap]
    exact infinityBranchPolynomial_map (algebraMap R S) P t hdeg
  have hb : (algebraMap R[X] S[X]) 0 = 0 := map_zero _
  change (S[X] ⊗[R[X]] QuadraticAlgebra R[X] (infinityBranchPolynomial P t) 0) ≃ₐ[S[X]]
    QuadraticAlgebra S[X]
      (infinityBranchPolynomial (P.map (algebraMap R S)) (algebraMap R S t)) 0
  exact quadraticTensorEquivOfEq (A := R[X]) (B := S[X])
    (infinityBranchPolynomial P t) 0 _ _ ha hb

/-- Restricting the finite tensor equivalence to the old chart is coefficient change. -/
theorem finiteChartTensorEquiv_includeRight (P : R[X]) (t : R)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    finiteChartTensorEquiv (S := S) P t
      ((Algebra.TensorProduct.includeRight :
        AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t) →ₐ[R[X]]
          S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) z) =
      finiteChartMap (algebraMap R S) P t z := by
  apply QuadraticAlgebra.ext
  · have h := quadraticTensorEquivOfEq_includeRight_re (A := R[X]) (B := S[X])
      (finiteBranchPolynomial P t) 0 _ _
      (finiteBranchPolynomial_map (algebraMap R S) P t) (map_zero _) z
    simpa [finiteChartTensorEquiv, finiteChartMap_re, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h
  · have h := quadraticTensorEquivOfEq_includeRight_im (A := R[X]) (B := S[X])
      (finiteBranchPolynomial P t) 0 _ _
      (finiteBranchPolynomial_map (algebraMap R S) P t) (map_zero _) z
    simpa [finiteChartTensorEquiv, finiteChartMap_im, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h

/-- Restricting the reciprocal tensor equivalence to the old chart is coefficient change. -/
theorem infinityChartTensorEquiv_includeRight (P : R[X]) (t : R)
    (hdeg : (P.map (algebraMap R S)).natDegree = P.natDegree)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    infinityChartTensorEquiv (S := S) P t hdeg
      ((Algebra.TensorProduct.includeRight :
        AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t) →ₐ[R[X]]
          S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) z) =
      infinityChartMap (algebraMap R S) P t hdeg z := by
  apply QuadraticAlgebra.ext
  · have h := quadraticTensorEquivOfEq_includeRight_re (A := R[X]) (B := S[X])
      (infinityBranchPolynomial P t) 0 _ _
      (infinityBranchPolynomial_map (algebraMap R S) P t hdeg) (map_zero _) z
    simpa [infinityChartTensorEquiv, infinityChartMap_re, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h
  · have h := quadraticTensorEquivOfEq_includeRight_im (A := R[X]) (B := S[X])
      (infinityBranchPolynomial P t) 0 _ _
      (infinityBranchPolynomial_map (algebraMap R S) P t hdeg) (map_zero _) z
    simpa [infinityChartTensorEquiv, infinityChartMap_im, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h

/-- The finite residue chart is the scalar extension of the actual family chart. -/
def finiteSpecializationTensorEquiv (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) :
    (S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) ≃ₐ[S[X]]
      AlgebraicGeometry.DoubleCover.ChartRing
        (finiteBranchPolynomial (P.map (algebraMap R S)) 0) := by
  change (S[X] ⊗[R[X]] QuadraticAlgebra R[X] (finiteBranchPolynomial P t) 0) ≃ₐ[S[X]]
    QuadraticAlgebra S[X] (finiteBranchPolynomial (P.map (algebraMap R S)) 0) 0
  refine quadraticTensorEquivOfEq (A := R[X]) (B := S[X])
    (finiteBranchPolynomial P t) 0 _ _ ?_ (map_zero _)
  change (finiteBranchPolynomial P t).map (algebraMap R S) = _
  simpa only [ht] using finiteBranchPolynomial_map (algebraMap R S) P t

/-- The reciprocal residue chart is the scalar extension of the actual family chart. -/
def infinitySpecializationTensorEquiv [Nontrivial S] (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0) (hP : P.Monic) :
    (S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) ≃ₐ[S[X]]
      AlgebraicGeometry.DoubleCover.ChartRing
        (infinityBranchPolynomial (P.map (algebraMap R S)) 0) := by
  change (S[X] ⊗[R[X]] QuadraticAlgebra R[X] (infinityBranchPolynomial P t) 0) ≃ₐ[S[X]]
    QuadraticAlgebra S[X] (infinityBranchPolynomial (P.map (algebraMap R S)) 0) 0
  refine quadraticTensorEquivOfEq (A := R[X]) (B := S[X])
    (infinityBranchPolynomial P t) 0 _ _ ?_ (map_zero _)
  change (infinityBranchPolynomial P t).map (algebraMap R S) = _
  simpa only [ht] using infinityBranchPolynomial_map (algebraMap R S) P t
    (monic_natDegree_map (algebraMap R S) P hP)

/-- The finite tensor identification restricts to the actual residue specialization map. -/
theorem finiteSpecializationTensorEquiv_includeRight (P : R[X]) (t : R)
    (ht : algebraMap R S t = 0)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) :
    finiteSpecializationTensorEquiv (S := S) P t ht
      ((Algebra.TensorProduct.includeRight :
        AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t) →ₐ[R[X]]
          S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P t)) z) =
      finiteSpecializationMap (algebraMap R S) P t ht z := by
  apply QuadraticAlgebra.ext
  · have h := quadraticTensorEquivOfEq_includeRight_re (A := R[X]) (B := S[X])
      (finiteBranchPolynomial P t) 0 _ _
      (by
        change (finiteBranchPolynomial P t).map (algebraMap R S) = _
        simpa only [ht] using finiteBranchPolynomial_map (algebraMap R S) P t)
      (map_zero _) z
    simpa [finiteSpecializationTensorEquiv, finiteSpecializationMap_re, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h
  · have h := quadraticTensorEquivOfEq_includeRight_im (A := R[X]) (B := S[X])
      (finiteBranchPolynomial P t) 0 _ _
      (by
        change (finiteBranchPolynomial P t).map (algebraMap R S) = _
        simpa only [ht] using finiteBranchPolynomial_map (algebraMap R S) P t)
      (map_zero _) z
    simpa [finiteSpecializationTensorEquiv, finiteSpecializationMap_im, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h

/-- The reciprocal tensor identification restricts to the actual residue specialization map. -/
theorem infinitySpecializationTensorEquiv_includeRight [Nontrivial S]
    (P : R[X]) (t : R) (ht : algebraMap R S t = 0) (hP : P.Monic)
    (z : AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) :
    infinitySpecializationTensorEquiv (S := S) P t ht hP
      ((Algebra.TensorProduct.includeRight :
        AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t) →ₐ[R[X]]
          S[X] ⊗[R[X]] AlgebraicGeometry.DoubleCover.ChartRing (infinityBranchPolynomial P t)) z) =
      infinitySpecializationMap (algebraMap R S) P t ht hP z := by
  apply QuadraticAlgebra.ext
  · have h := quadraticTensorEquivOfEq_includeRight_re (A := R[X]) (B := S[X])
      (infinityBranchPolynomial P t) 0 _ _
      (by
        change (infinityBranchPolynomial P t).map (algebraMap R S) = _
        simpa only [ht] using infinityBranchPolynomial_map (algebraMap R S) P t
          (monic_natDegree_map (algebraMap R S) P hP))
      (map_zero _) z
    simpa [infinitySpecializationTensorEquiv, infinitySpecializationMap_re, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h
  · have h := quadraticTensorEquivOfEq_includeRight_im (A := R[X]) (B := S[X])
      (infinityBranchPolynomial P t) 0 _ _
      (by
        change (infinityBranchPolynomial P t).map (algebraMap R S) = _
        simpa only [ht] using infinityBranchPolynomial_map (algebraMap R S) P t
          (monic_natDegree_map (algebraMap R S) P hP))
      (map_zero _) z
    simpa [infinitySpecializationTensorEquiv, infinitySpecializationMap_im, id_eq,
      show (algebraMap R[X] S[X]) = Polynomial.mapRingHom (algebraMap R S) from rfl] using h

end ChartTensor

end HilbertModularity.Hyperelliptic
