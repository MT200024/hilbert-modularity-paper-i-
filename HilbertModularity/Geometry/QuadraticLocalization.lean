/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-! # Localization of quadratic algebras

Quadratic algebras commute with localization of their coefficient ring. This
provides the affine overlap maps used to construct double covers.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Apply a coefficient-ring homomorphism to a quadratic algebra. -/
@[simps]
def mapCoeffs (f : R →+* S) (a b : R) :
    QuadraticAlgebra R a b →+* QuadraticAlgebra S (f a) (f b) where
  toFun z := ⟨f z.re, f z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp

/-- Transport a quadratic algebra across an isomorphism of coefficient rings. -/
@[simps!]
def mapCoeffsEquiv (f : R ≃+* S) (a b : R) :
    QuadraticAlgebra R a b ≃+* QuadraticAlgebra S (f a) (f b) where
  __ := mapCoeffs f.toRingHom a b
  invFun z := ⟨f.symm z.re, f.symm z.im⟩
  left_inv z := by ext <;> simp [mapCoeffs]
  right_inv z := by ext <;> simp [mapCoeffs]

/-- The scalar part of a constant from a coefficient subring. -/
@[simp]
theorem algebraMap_re_of_algebra [Algebra S R] (a b : R) (s : S) :
    (algebraMap S (QuadraticAlgebra R a b) s).re = algebraMap S R s := rfl

/-- The quadratic part of a constant from a coefficient subring is zero. -/
@[simp]
theorem algebraMap_im_of_algebra [Algebra S R] (a b : R) (s : S) :
    (algebraMap S (QuadraticAlgebra R a b) s).im = 0 := rfl

variable [Algebra R S] (a b : R)

/-- The coefficient extension homomorphism of quadratic algebras. -/
abbrev baseChange : QuadraticAlgebra R a b →+*
    QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) :=
  mapCoeffs (algebraMap R S) a b

/-- The algebra structure induced by extension of coefficients. -/
instance baseChangeAlgebra : Algebra (QuadraticAlgebra R a b)
    (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  (baseChange a b).toAlgebra

/-- The scalar extension algebra structure uses coefficientwise extension. -/
@[simp]
theorem algebraMap_baseChange (z : QuadraticAlgebra R a b) :
    algebraMap (QuadraticAlgebra R a b)
      (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) z =
        baseChange (S := S) a b z := rfl

/-- Extension of coefficients commutes with the inclusion of constants. -/
@[simp]
theorem baseChange_algebraMap (x : R) :
    baseChange (S := S) a b (algebraMap R (QuadraticAlgebra R a b) x) =
      algebraMap S _ (algebraMap R S x) := by
  ext <;> simp [baseChange, mapCoeffs]

/-- Localizing the coefficients localizes the quadratic algebra at the same scalars. -/
theorem isLocalization (M : Submonoid R) [IsLocalization M S] :
    IsLocalization (M.map (algebraMap R (QuadraticAlgebra R a b)).toMonoidHom)
      (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
  rw [isLocalization_iff]
  constructor
  · rintro ⟨y, x, hx, rfl⟩
    change IsUnit (baseChange a b (algebraMap R (QuadraticAlgebra R a b) x))
    rw [baseChange_algebraMap]
    exact (IsLocalization.map_units S (⟨x, hx⟩ : M)).map (algebraMap S _)
  constructor
  · intro z
    obtain ⟨r, s, m, hr, hs⟩ := IsLocalization.surj₂ M S z.re z.im
    refine ⟨(⟨r, s⟩, ⟨algebraMap R _ m, Submonoid.mem_map.mpr ⟨m, m.property, rfl⟩⟩), ?_⟩
    change z * baseChange a b (algebraMap R _ m) = baseChange a b ⟨r, s⟩
    ext <;> simpa [baseChange, mapCoeffs] using (by assumption)
  · intro x y h
    have hr := congrArg QuadraticAlgebra.re h
    have hi := congrArg QuadraticAlgebra.im h
    change algebraMap R S x.re = algebraMap R S y.re at hr
    change algebraMap R S x.im = algebraMap R S y.im at hi
    obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M) hr
    obtain ⟨n, hn⟩ := IsLocalization.exists_of_eq (M := M) hi
    refine ⟨⟨algebraMap R _ (m * n), Submonoid.mem_map.mpr
      ⟨m * n, (m * n).property, rfl⟩⟩, ?_⟩
    ext
    · simp only [algebraMap_re, algebraMap_im, re_mul]
      linear_combination (n : R) * hm
    · simp only [algebraMap_re, algebraMap_im, im_mul, zero_mul, add_zero]
      linear_combination (m : R) * hn

/-- The affine overlap obtained by inverting a scalar in a quadratic algebra. -/
theorem isLocalizationAway (x : R) [IsLocalization.Away x S] :
    IsLocalization.Away (algebraMap R (QuadraticAlgebra R a b) x)
      (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
  have h := isLocalization (S := S) a b (Submonoid.powers x)
  rw [Submonoid.map_powers] at h
  exact h

end QuadraticAlgebra
