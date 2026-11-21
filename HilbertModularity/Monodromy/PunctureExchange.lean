/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Monodromy.Cyclotomic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RepresentationTheory.Intertwining

/-! # Exchanging the two unipotent monodromies

An explicit invertible matrix exchanges the two standard finite-puncture
monodromies. The free-group representation therefore intertwines with its
pullback by the generator exchange. The identification with the geometric
local system is a separate realization theorem; see [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace HilbertModularity.Monodromy

open Matrix

variable {K : Type*} [Field K] (τ : K)

/-- The matrix exchanging the standard upper and lower unipotent monodromies. -/
def punctureExchangeMatrix : Matrix (Fin 2) (Fin 2) K := !![0, 1; τ - 2, 0]

/-- The determinant of the exchange matrix. -/
theorem det_punctureExchangeMatrix : (punctureExchangeMatrix τ).det = -(τ - 2) := by
  simp [punctureExchangeMatrix, Matrix.det_fin_two_of]

/-- The exchange matrix intertwines the first monodromy with the second. -/
theorem punctureExchangeMatrix_mul_U0 :
    punctureExchangeMatrix τ * U0 = U1 τ * punctureExchangeMatrix τ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [punctureExchangeMatrix, U0, U1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The exchange matrix intertwines the second monodromy with the first. -/
theorem punctureExchangeMatrix_mul_U1 :
    punctureExchangeMatrix τ * U1 τ = U0 * punctureExchangeMatrix τ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [punctureExchangeMatrix, U0, U1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The associated invertible linear map when the trace parameter is nontrivial. -/
def punctureExchangeEquiv (hτ : τ ≠ 2) : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) :=
  (punctureExchangeMatrix τ).toLinearEquiv' (Matrix.invertibleOfIsUnitDet _ (by
    rw [det_punctureExchangeMatrix]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (sub_ne_zero.mpr hτ))))

/-- The standard pair of monodromies defines an actual free-group action by linear automorphisms. -/
def standardMonodromyAut : FreeGroup (Fin 2) →* ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
  FreeGroup.lift fun i => Matrix.SpecialLinearGroup.toLin' (standardTriple τ i.castSucc)

/-- The two-generator standard monodromy representation. -/
def standardMonodromy : Representation K (FreeGroup (Fin 2)) (Fin 2 → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (standardMonodromyAut τ)

/-- The automorphism of the free group exchanging the two finite puncture generators. -/
def punctureExchange : FreeGroup (Fin 2) ≃* FreeGroup (Fin 2) :=
  FreeGroup.freeGroupCongr (Equiv.swap 0 1)

/-- The concrete generator intertwining equations. -/
theorem punctureExchangeEquiv_generator (hτ : τ ≠ 2) (i : Fin 2) :
    punctureExchangeEquiv τ hτ * standardMonodromyAut τ (FreeGroup.of i) =
      standardMonodromyAut τ (punctureExchange (FreeGroup.of i)) * punctureExchangeEquiv τ hτ := by
  apply LinearEquiv.toLinearMap_injective
  fin_cases i
  · change Matrix.toLin' (punctureExchangeMatrix τ) ∘ₗ Matrix.toLin' U0 =
      Matrix.toLin' (U1 τ) ∘ₗ Matrix.toLin' (punctureExchangeMatrix τ)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, punctureExchangeMatrix_mul_U0]
  · change Matrix.toLin' (punctureExchangeMatrix τ) ∘ₗ Matrix.toLin' (U1 τ) =
      Matrix.toLin' U0 ∘ₗ Matrix.toLin' (punctureExchangeMatrix τ)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, punctureExchangeMatrix_mul_U1]

/-- The generator intertwiner extends to every word of the actual free-group representation. -/
theorem punctureExchangeEquiv_intertwines (hτ : τ ≠ 2) (g : FreeGroup (Fin 2)) :
    punctureExchangeEquiv τ hτ * standardMonodromyAut τ g =
      standardMonodromyAut τ (punctureExchange g) * punctureExchangeEquiv τ hτ := by
  have he : (MulAut.conj (punctureExchangeEquiv τ hτ)).toMonoidHom.comp
      (standardMonodromyAut τ) =
        (standardMonodromyAut τ).comp punctureExchange.toMonoidHom := by
    apply FreeGroup.ext_hom
    intro i
    change punctureExchangeEquiv τ hτ * standardMonodromyAut τ (FreeGroup.of i) *
        (punctureExchangeEquiv τ hτ)⁻¹ =
      standardMonodromyAut τ (punctureExchange (FreeGroup.of i))
    rw [punctureExchangeEquiv_generator]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have h := DFunLike.congr_fun he g
  change punctureExchangeEquiv τ hτ * standardMonodromyAut τ g *
    (punctureExchangeEquiv τ hτ)⁻¹ = standardMonodromyAut τ (punctureExchange g) at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- The standard monodromy representation is isomorphic to its pullback by exchanging generators. -/
def standardMonodromyPunctureExchangeEquiv (hτ : τ ≠ 2) :
    (standardMonodromy τ).Equiv ((standardMonodromy τ).comp punctureExchange.toMonoidHom) :=
  .mk (punctureExchangeEquiv τ hτ) (by
    intro g
    exact congrArg LinearEquiv.toLinearMap (punctureExchangeEquiv_intertwines τ hτ g))

/-- Exchanging the two finite punctures preserves the infinity word up to conjugacy. -/
theorem punctureExchange_infinity :
    punctureExchange ((FreeGroup.of (0 : Fin 2) * FreeGroup.of 1)⁻¹) =
      (FreeGroup.of (0 : Fin 2))⁻¹ *
        (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1)⁻¹ * FreeGroup.of 0 := by
  simp [punctureExchange, FreeGroup.freeGroupCongr, _root_.mul_inv_rev, mul_assoc]

end HilbertModularity.Monodromy

namespace HilbertModularity.Cyclotomic

open Monodromy

/-- The actual cyclotomic-labelled monodromy action is invariant under exchanging finite punctures. -/
theorem standardMonodromy_tau_punctureExchange (N m : ℕ) [NeZero N]
    (hN : 3 ≤ N) (hm : m.Coprime N) :
    Nonempty ((standardMonodromy (tau N m)).Equiv
      ((standardMonodromy (tau N m)).comp punctureExchange.toMonoidHom)) :=
  ⟨standardMonodromyPunctureExchangeEquiv (tau N m) (tau_ne_two N m hN hm)⟩

end HilbertModularity.Cyclotomic
