/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberAwaySplit
public import Mathlib.RingTheory.Smooth.Pi

/-! # Smoothness away from the special-fibre crossings

The two sheets separate after inverting the branch polynomial. The resulting
algebra is smooth over the residue field, so all remaining singularities must
lie over its zero locus.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

/-- A punctured affine line is smooth over its ground field. -/
theorem smooth_polynomialAway {k : Type*} [Field k] (H : k[X]) :
    Algebra.Smooth k (Localization.Away H) := by
  let : Algebra.Smooth k k[X] := ⟨Algebra.FormallySmooth.polynomial k, by infer_instance⟩
  let : Algebra.Smooth k[X] (Localization.Away H) :=
    Algebra.Smooth.of_isLocalization_Away H
  exact Algebra.Smooth.comp k k[X] (Localization.Away H)

/-- Both copies of a punctured affine line are smooth. -/
theorem smooth_piPolynomialAway {k : Type*} [Field k] (H : k[X]) :
    Algebra.Smooth k (Fin 2 → Localization.Away H) := by
  let A := Localization.Away H
  let : Algebra.Smooth k A := smooth_polynomialAway H
  exact ⟨by infer_instance, by infer_instance⟩

/-- A pair of algebra elements as a two-element indexed family. -/
def productFinTwoAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    (A × A) ≃ₐ[R] (Fin 2 → A) where
  toFun p i := if i = 0 then p.1 else p.2
  invFun f := (f 0, f 1)
  left_inv p := by
    apply Prod.ext <;> simp
  right_inv f := by
    funext i
    fin_cases i <;> simp
  map_mul' p q := by
    funext i
    fin_cases i <;> simp
  map_add' p q := by
    funext i
    fin_cases i <;> simp
  commutes' r := by
    funext i
    fin_cases i <;> simp

/-- The square-branch chart is smooth after inverting its branch polynomial. -/
theorem smooth_squareBranchAway {k : Type*} [Field k] (H : k[X])
    (h2 : (2 : k) ≠ 0) :
    let A := Localization.Away H
    Algebra.Smooth k (QuadraticAlgebra A ((algebraMap k[X] A H) ^ 2) 0) := by
  let A := Localization.Away H
  let : Algebra.Smooth k (Fin 2 → A) := smooth_piPolynomialAway H
  let e : QuadraticAlgebra A ((algebraMap k[X] A H) ^ 2) 0 ≃ₐ[k] (Fin 2 → A) :=
    ((squareBranchAwaySplitEquiv H h2).restrictScalars k).trans
      (productFinTwoAlgEquiv k A)
  exact Algebra.Smooth.of_equiv e.symm

/-- The actual finite special-fibre chart is smooth off `X * P`. -/
theorem smooth_finiteSpecialFiberAway {k : Type*} [Field k] (P : k[X])
    (h2 : (2 : k) ≠ 0) :
    let A := Localization.Away (finiteComponentPolynomial P)
    Algebra.Smooth k
      (QuadraticAlgebra A (algebraMap k[X] A (finiteBranchPolynomial P 0)) 0) := by
  dsimp
  rw [finiteBranchPolynomial_zero, map_pow]
  exact smooth_squareBranchAway (finiteComponentPolynomial P) h2

/-- The actual reciprocal special-fibre chart is smooth off `P.reverse`. -/
theorem smooth_infinitySpecialFiberAway {k : Type*} [Field k] (P : k[X])
    (h2 : (2 : k) ≠ 0) :
    let A := Localization.Away (infinityComponentPolynomial P)
    Algebra.Smooth k
      (QuadraticAlgebra A (algebraMap k[X] A (infinityBranchPolynomial P 0)) 0) := by
  dsimp
  rw [infinityBranchPolynomial_zero, map_pow]
  exact smooth_squareBranchAway (infinityComponentPolynomial P) h2

end HilbertModularity.Hyperelliptic
