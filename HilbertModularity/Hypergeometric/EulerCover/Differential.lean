/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.EulerCover.Smoothness
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Relative differentials of the affine Euler cover

On the finite branch complement, the Euler algebra is étale over a localization
of the polynomial line. Its actual Kähler differential module is therefore free
on the differential of the `x` coordinate. This calculation concerns the affine
part of [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

namespace HilbertModularity.Hypergeometric.EulerCover

universe u
variable {R : Type u} [CommRing R]

/-- The polynomial `x` coordinate in the actual Euler root algebra. -/
def coverX (N m : ℕ) (t : R) : CoverRing N m t :=
  algebraMap R[X] (CoverRing N m t) X

/-- In the relative differential module, `dx` is a free generator on the
branch complement. -/
def coverDifferentialEquiv (N m : ℕ) (t : R) (hN : N ≠ 0)
    (hn : IsUnit (N : R)) :
    CoverRing N m t ≃ₗ[CoverRing N m t]
      KaehlerDifferential R (CoverRing N m t) := by
  letI : Algebra.FormallyEtale R[X] (BaseRing t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (branchProduct t))
  letI : Algebra.FormallyEtale (BaseRing t) (CoverRing N m t) :=
    (coverRing_etale N m t hN hn).formallyEtale
  letI : Algebra.FormallyEtale R[X] (CoverRing N m t) :=
    Algebra.FormallyEtale.comp R[X] (BaseRing t) (CoverRing N m t)
  let e₁ : CoverRing N m t ≃ₗ[CoverRing N m t]
      CoverRing N m t ⊗[R[X]] R[X] :=
    (TensorProduct.AlgebraTensorModule.rid R[X] (CoverRing N m t) (CoverRing N m t)).symm
  let e₂ : CoverRing N m t ⊗[R[X]] R[X] ≃ₗ[CoverRing N m t]
      CoverRing N m t ⊗[R[X]] KaehlerDifferential R R[X] :=
    TensorProduct.AlgebraTensorModule.congr (.refl _ _)
      (KaehlerDifferential.polynomialEquiv R).symm
  exact (e₁.trans e₂).trans
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R R[X] (CoverRing N m t))

/-- The free generator above is the actual differential of `x`. -/
theorem coverDifferentialEquiv_one (N m : ℕ) (t : R) (hN : N ≠ 0)
    (hn : IsUnit (N : R)) :
    coverDifferentialEquiv N m t hN hn 1 =
      KaehlerDifferential.D R (CoverRing N m t) (coverX N m t) := by
  simp [coverDifferentialEquiv, coverX,
    TensorProduct.AlgebraTensorModule.rid_symm_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul]

/-- A one-element basis of relative differentials, given by the actual `dx`. -/
def coverDifferentialBasis (N m : ℕ) (t : R) (hN : N ≠ 0)
    (hn : IsUnit (N : R)) :
    Module.Basis (Fin 1) (CoverRing N m t)
      (KaehlerDifferential R (CoverRing N m t)) :=
  (Module.Basis.singleton (Fin 1) (CoverRing N m t)).map
    (coverDifferentialEquiv N m t hN hn)

@[simp]
theorem coverDifferentialBasis_zero (N m : ℕ) (t : R) (hN : N ≠ 0)
    (hn : IsUnit (N : R)) :
    coverDifferentialBasis N m t hN hn 0 =
      KaehlerDifferential.D R (CoverRing N m t) (coverX N m t) := by
  simpa [coverDifferentialBasis] using coverDifferentialEquiv_one N m t hN hn

end HilbertModularity.Hypergeometric.EulerCover
