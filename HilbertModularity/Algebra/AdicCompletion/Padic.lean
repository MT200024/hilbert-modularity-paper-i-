/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.NumberTheory.Padics.RingHoms

/-! # Canonical p-adic scalars in completed coefficient rings

The compatible finite scalar maps from integers modulo powers of `p` give
a canonical map from `ℤ_p` to the `p`-adic completion of any commutative
coefficient ring. This identifies the scalar action used by actual Tate
modules with that of their completed RM coefficients; see [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace AdicCompletion

variable (p : ℕ) (R : Type*) [CommRing R]

/-- Finite rational-prime scalars map canonically to finite coefficient quotients. -/
def zmodToQuotient (n : ℕ) : ZMod (p ^ n) →+* R ⧸ (Ideal.span {(p : R)}) ^ n :=
  ZMod.castHom (m := ringChar (R ⧸ (Ideal.span {(p : R)}) ^ n)) (by
    apply (CharP.cast_eq_zero_iff (R ⧸ (Ideal.span {(p : R)}) ^ n) _ _).mp
    change Ideal.Quotient.mk _ ((p ^ n : ℕ) : R) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : R))) n) _

/-- These finite scalar maps respect the coefficient quotient transition. -/
theorem zmodToQuotient_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : R)}) hmn).comp (zmodToQuotient p R n) =
      (zmodToQuotient p R m).comp (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))) :=
  Subsingleton.elim _ _

end AdicCompletion

namespace PadicInt

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R]

/-- The canonical p-adic scalar map into the completed integral coefficient ring. -/
def toAdicCompletion : ℤ_[p] →+* AdicCompletion (Ideal.span {(p : R)}) R :=
  AdicCompletion.liftRingHom (Ideal.span {(p : R)})
    (fun n => (AdicCompletion.zmodToQuotient p R n).comp (toZModPow n))
    (fun {m n} hmn => by
      rw [← RingHom.comp_assoc, AdicCompletion.zmodToQuotient_compatible,
        RingHom.comp_assoc, zmod_cast_comp_toZModPow m n hmn])

@[simp]
theorem evalₐ_toAdicCompletion (n : ℕ) (z : ℤ_[p]) :
    AdicCompletion.evalₐ (Ideal.span {(p : R)}) n (toAdicCompletion p R z) =
      AdicCompletion.zmodToQuotient p R n (toZModPow n z) :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ _ _

end PadicInt
