/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CoefficientFinite
public import HilbertModularity.Algebra.AdicCompletion.PrincipalDVR
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Freeness of the actual RM-prime Tate lattice

For a discrete valuation coefficient completion, the actual Tate module is
torsion-free: its uniformizer divides `p`, whose action on compatible Tate
families is injective. Together with proved finite generation, this gives
freeness of the actual lattice. See [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

attribute [local instance] coefficientModule

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- Actual Tate torsion-freeness extends to the RM-prime DVR coefficients. -/
theorem coefficientPrime_isTorsionFree (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    [IsDomain (AdicCompletion (Ideal.span {a}) R)]
    [IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R)] :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    Module.IsTorsionFree (AdicCompletion (Ideal.span {a}) R) (integral p A) := by
  let := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  let S := AdicCompletion (Ideal.span {a}) R
  let ϖ : S := algebraMap R S a
  have hirr : Irreducible ϖ := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr
    have hm := AdicCompletion.isMaximal_map_of_le (Ideal.span {a}) (Ideal.span {a})
      le_rfl (Submodule.fg_span_singleton _)
    simpa only [Ideal.map_span, Set.image_singleton] using (IsLocalRing.eq_maximalIdeal hm).symm
  have ha : Function.Injective (fun x : integral p A => ϖ • x) := by
    intro x y h
    change algebraMap R (AdicCompletion (Ideal.span {a}) R) a • x =
      algebraMap R (AdicCompletion (Ideal.span {a}) R) a • y at h
    rw [coefficientPrime_smul_algebraMap p R A (Ideal.span {a}) e he hJ,
      coefficientPrime_smul_algebraMap p R A (Ideal.span {a}) e he hJ] at h
    have h' : a • x = a • y := h
    apply nsmul_injective p A
    simpa only [← mul_smul, mul_comm b a, hab, Nat.cast_smul_eq_nsmul] using
      congrArg (fun z : integral p A => b • z) h'
  have hpowers (n : ℕ) : Function.Injective (fun x : integral p A => (ϖ ^ n) • x) := by
    induction n with
    | zero =>
      intro x y h
      simpa only [pow_zero, one_smul] using h
    | succ n ih =>
      intro x y h
      apply ha
      apply ih
      simpa only [pow_succ, mul_smul] using h
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro c x hcx
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hirr
    have hx : (ϖ ^ n) • x = 0 := by
      simpa [← mul_smul] using congrArg (fun y : integral p A => (↑(u⁻¹) : S) • y) hcx
    exact hpowers n (by simpa only [smul_zero] using hx)

/-- The actual finite RM-prime Tate lattice is free over a DVR completion. -/
theorem coefficientPrime_free [Module.Finite ℤ_[p] (integral p A)]
    (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal]
    [IsDomain (AdicCompletion (Ideal.span {a}) R)]
    [IsDiscreteValuationRing (AdicCompletion (Ideal.span {a}) R)] :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    Module.Free (AdicCompletion (Ideal.span {a}) R) (integral p A) := by
  let := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  have := coefficientPrime_finite p R A (Ideal.span {a}) e he hJ
  have := coefficientPrime_isTorsionFree p R A a b hab e he hJ
  infer_instance

/-- A nonzero principal RM prime in a domain gives a free actual completed Tate lattice. -/
theorem coefficientPrime_free_of_domain [IsDomain R] [Module.Finite ℤ_[p] (integral p A)]
    (a b : R) (ha : a ≠ 0) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    Module.Free (AdicCompletion (Ideal.span {a}) R) (integral p A) := by
  have := AdicCompletion.isDomain_of_isMaximal_span a ha
  have := AdicCompletion.isDiscreteValuationRing_of_isMaximal_span a ha
  exact coefficientPrime_free p R A a b hab e he hJ

end TateModule
