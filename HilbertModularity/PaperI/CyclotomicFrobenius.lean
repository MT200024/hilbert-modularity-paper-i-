module

public import HilbertModularity.PaperI.CyclotomicTwist
public import HilbertModularity.NumberTheory.AbsoluteFrobenius

/-! # The quadratic character at primes of norm minus one modulo the conductor -/
public noncomputable section

namespace HilbertModularity.PaperI
open HilbertModularity.Cyclotomic HilbertModularity.HilbertModularForms
open scoped NumberField

/-- At a prime whose norm is minus one modulo p, geometric Frobenius
acts by the nontrivial element of the full/real cyclotomic extension. -/
theorem cyclotomicSign_geometricFrobenius_neg_one
    (p : ℕ) [NeZero p] [Fact (1 < p)] (hp : 2 < p) (L : Type*) [Field L]
    (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal]
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p)))) [Q.IsMaximal] [Q.LiesOver P]
    (hpP : (p : 𝓞 (realCyclotomicField p)) ∉ P)
    (hmod : p ∣ Nat.card (𝓞 (realCyclotomicField p) ⧸ P) + 1) :
    cyclotomicSign p L
      (NumberField.geometricFrobenius (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p)) P Q) = -1 := by
  classical
  let K := realCyclotomicField p
  let E := AlgebraicClosure K
  let z := primitiveRootInClosure p
  let n := Nat.card (𝓞 K ⧸ P)
  let g := NumberField.arithmeticFrobenius K E P Q
  have hz : IsPrimitiveRoot z p := primitiveRootInClosure_isPrimitiveRoot p
  let zI : 𝓞 E := ⟨z, hz.isIntegral (NeZero.pos p)⟩
  have hzI : IsPrimitiveRoot zI p :=
    hz.of_map_of_injective (f := algebraMap (𝓞 E) E) NumberField.RingOfIntegers.coe_injective
  have hpQ : (p : 𝓞 E) ∉ Q := by
    intro h
    apply hpP
    apply (Ideal.mem_of_liesOver Q P (p : 𝓞 K)).mpr
    simpa only [map_natCast] using h
  have hI : g • zI = zI ^ n := Ideal.smul_root_eq_pow_of_quotient_action Q g n
    (NumberField.arithmeticFrobenius_apply K E P Q) hpQ hzI hzI.pow_eq_one
  have harith : (g : AbsoluteGalois K) z = z ^ n := by
    exact congrArg (fun a : 𝓞 E => (a : E)) hI
  have hfix : (g : AbsoluteGalois K) z ≠ z := by
    intro he
    have hpow : z ^ 2 = 1 := calc
      z ^ 2 = z ^ n * z := by rw [harith.symm.trans he, pow_two]
      _ = z ^ (n + 1) := (pow_succ z n).symm
      _ = 1 := (hz.pow_eq_one_iff_dvd _).mpr hmod
    exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide : 0 < 2) ((hz.pow_eq_one_iff_dvd _).mp hpow))
  change cyclotomicSign p L (g : AbsoluteGalois K)⁻¹ = -1
  rw [map_inv, cyclotomicSign_apply]
  split
  · rename_i hg
    exact (hfix hg).elim
  · simp

end HilbertModularity.PaperI
