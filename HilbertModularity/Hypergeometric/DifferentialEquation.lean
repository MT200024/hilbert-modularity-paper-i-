/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
import Mathlib.Tactic.Ring

/-! # Reflection of the hypergeometric differential equation

The actual differential operator of [TripathiGoswami, equation (hgde)]
commutes with pullback by `t ↦ 1 - t`. This gives a bijection on analytic
solutions on reflected domains. Identification with an etale local system
is a separate comparison theorem.
-/

@[expose] public noncomputable section

namespace HilbertModularity.Hypergeometric

variable {K : Type*} [NontriviallyNormedField K]

/-- The Gauss operator for the parameters `(a, 1-a; 1)`, using actual derivatives. -/
def differentialOperator (a : K) (y : K → K) (t : K) : K :=
  t * (1 - t) * deriv (deriv y) t + (1 - 2 * t) * deriv y t - a * (1 - a) * y t

/-- Pullback of functions by the complement involution is a linear equivalence. -/
def complementPullback : (K → K) ≃ₗ[K] (K → K) where
  toFun y t := y (1 - t)
  invFun y t := y (1 - t)
  left_inv y := by ext t; simp
  right_inv y := by ext t; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem complementPullback_apply (y : K → K) (t : K) :
    complementPullback y t = y (1 - t) := rfl

@[simp]
theorem complementPullback_twice (y : K → K) :
    complementPullback (complementPullback y) = y := by
  ext t
  simp

/-- The differential equation is preserved by reflection, without imposing
extra differentiability assumptions on the total derivative operator. -/
theorem differentialOperator_complement (a : K) (y : K → K) (t : K) :
    differentialOperator a (complementPullback y) t = differentialOperator a y (1 - t) := by
  have hderiv : deriv (complementPullback y) = fun t => -deriv y (1 - t) := by
    funext t
    exact deriv_comp_const_sub y 1 t
  simp only [differentialOperator, hderiv, deriv.fun_neg, deriv_comp_const_sub, neg_neg,
    complementPullback_apply]
  ring

/-- Reflection transports solutions on a domain to its inverse image. -/
theorem differentialOperator_complement_zero_iff (a : K) (y : K → K) (U : Set K) :
    (∀ t ∈ (fun t : K => 1 - t) ⁻¹' U,
      differentialOperator a (complementPullback y) t = 0) ↔
    ∀ t ∈ U, differentialOperator a y t = 0 := by
  constructor
  · intro h t ht
    have hx : 1 - t ∈ (fun t : K => 1 - t) ⁻¹' U := by simpa using ht
    simpa only [differentialOperator_complement, sub_sub_cancel] using h (1 - t) hx
  · intro h t ht
    rw [differentialOperator_complement]
    exact h (1 - t) ht

/-- Analyticity is preserved and reflected on the reflected domain. -/
theorem analyticOnNhd_complement_iff (y : K → K) (U : Set K) :
    AnalyticOnNhd K (complementPullback y) ((fun t : K => 1 - t) ⁻¹' U) ↔
    AnalyticOnNhd K y U := by
  have hcomp (f : K → K) (S : Set K) (hf : AnalyticOnNhd K f S) :
      AnalyticOnNhd K (complementPullback f) ((fun t : K => 1 - t) ⁻¹' S) := by
    intro t ht
    exact (hf (1 - t) ht).comp (analyticAt_const.sub analyticAt_id)
  constructor
  · intro h t ht
    have h' := hcomp (complementPullback y) _ h
    have hx : t ∈ (fun t : K => 1 - t) ⁻¹' ((fun t : K => 1 - t) ⁻¹' U) := by
      simpa using ht
    simpa only [complementPullback_twice] using h' t hx
  · exact hcomp y U

/-- Actual analytic solutions correspond bijectively under reflection. -/
def analyticSolutionReflection (a : K) (U : Set K) :
    {y : K → K // AnalyticOnNhd K y U ∧ ∀ t ∈ U, differentialOperator a y t = 0} ≃
    {y : K → K // AnalyticOnNhd K y ((fun t : K => 1 - t) ⁻¹' U) ∧
      ∀ t ∈ (fun t : K => 1 - t) ⁻¹' U, differentialOperator a y t = 0} where
  toFun y := ⟨complementPullback y.val,
    (analyticOnNhd_complement_iff y.val U).mpr y.property.1,
    (differentialOperator_complement_zero_iff a y.val U).mpr y.property.2⟩
  invFun y := ⟨complementPullback y.val, by
    constructor
    · apply (analyticOnNhd_complement_iff (complementPullback y.val) U).mp
      simpa only [complementPullback_twice] using y.property.1
    · apply (differentialOperator_complement_zero_iff a (complementPullback y.val) U).mp
      simpa only [complementPullback_twice] using y.property.2⟩
  left_inv y := by apply Subtype.ext; ext t; simp
  right_inv y := by apply Subtype.ext; ext t; simp

end HilbertModularity.Hypergeometric
