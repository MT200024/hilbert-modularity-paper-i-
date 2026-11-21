/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Monodromy.Admissible
public import HilbertModularity.NumberTheory.CyclotomicEmbeddings

@[expose] public section

/-! # The cyclotomic integral monodromy triple -/

namespace HilbertModularity.Cyclotomic

open Monodromy
open scoped NumberField

noncomputable section

/-- The ordered monodromy triple over the integer ring of the real cyclotomic field. -/
def integralTriple (N m : ℕ) [NeZero N] :
    Fin 3 → Matrix (Fin 2) (Fin 2) (𝓞 (realCyclotomicField N)) :=
  ![U0, U1 (tauInteger N m), Uinf (tauInteger N m)]

/-- The coefficient embedding on the integer ring. -/
def integralCoefficientEmbedding (N m : ℕ) [NeZero N] (hm : m.Coprime N)
    (E : IntermediateField ℚ Qbar) (hE : realCyclotomicField N ≤ E) :
    𝓞 (realCyclotomicField N) →+* E :=
  (coefficientEmbedding N m hm E hE).toRingHom.comp
    (algebraMap (𝓞 (realCyclotomicField N)) (realCyclotomicField N))

/-- Applying the labelled embedding to the base integral triple gives the power-labelled
triple in the fixed coefficient field. -/
theorem coefficientEmbedding_integralTriple (N m : ℕ) [NeZero N] (hm : m.Coprime N)
    (E : IntermediateField ℚ Qbar) (hE : realCyclotomicField N ≤ E) (j : Fin 3) :
    (integralTriple N 1 j).map (integralCoefficientEmbedding N m hm E hE) =
      (integralTriple N m j).map
        ((IntermediateField.inclusion hE).toRingHom.comp
          (algebraMap (𝓞 (realCyclotomicField N)) (realCyclotomicField N))) := by
  let f := integralCoefficientEmbedding N m hm E hE
  let g := (IntermediateField.inclusion hE).toRingHom.comp
    (algebraMap (𝓞 (realCyclotomicField N)) (realCyclotomicField N))
  have ht : f (tauInteger N 1) = g (tauInteger N m) := coefficientEmbedding_tau_one N m hm E hE
  obtain ⟨h₀, h₁, hInf⟩ := map_triple f (tauInteger N 1)
  obtain ⟨h₀', h₁', hInf'⟩ := map_triple g (tauInteger N m)
  rw [ht] at h₁ hInf
  fin_cases j
  · exact h₀.trans h₀'.symm
  · exact h₁.trans h₁'.symm
  · exact hInf.trans hInf'.symm

/-- The integral triple as an actual special-linear triple. -/
def integralTripleSL (N m : ℕ) [NeZero N] :
    Fin 3 → Matrix.SpecialLinearGroup (Fin 2) (𝓞 (realCyclotomicField N)) :=
  standardTriple (tauInteger N m)

/-- The integer-ring triple has precisely the previously defined matrix entries. -/
@[simp] theorem coe_integralTripleSL (N m : ℕ) [NeZero N] (j : Fin 3) :
    (integralTripleSL N m j : Matrix (Fin 2) (Fin 2) (𝓞 (realCyclotomicField N))) =
      integralTriple N m j := by
  fin_cases j <;> rfl

/-- The cyclotomic trace parameter differs from `2` in its actual real field. -/
theorem tau_ne_two (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : m.Coprime N) :
    tau N m ≠ 2 := by
  intro h
  have hc := congrArg (realCyclotomicField N).val h
  change (zeta N) ^ m + (zeta N)⁻¹ ^ m = (realCyclotomicField N).val 2 at hc
  exact HilbertModularity.Monodromy.tau_ne_two hN (zeta_isPrimitiveRoot N) hm
    (by simpa only [map_ofNat] using hc)

/-- The infinity monodromy has finite order already over the real cyclotomic field. -/
theorem Uinf_tau_pow (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : m.Coprime N) :
    Uinf (tau N m) ^ N = 1 := by
  let f := (realCyclotomicField N).val.toRingHom
  apply Matrix.map_injective f.injective
  change (Uinf (tau N m) ^ N).map f = (1 : Matrix (Fin 2) (Fin 2) (realCyclotomicField N)).map f
  simp only [Matrix.map_pow, Matrix.map_one, map_zero, map_one,
    (map_triple f (tau N m)).2.2]
  change Uinf ((zeta N) ^ m + (zeta N)⁻¹ ^ m) ^ N = 1
  have h := pow_orderOf_eq_one (Uinf ((zeta N) ^ m + (zeta N)⁻¹ ^ m))
  rwa [orderOf_Uinf hN (zeta_isPrimitiveRoot N) hm] at h

/-- Darmon admissibility of the integral triple after its natural inclusion into the real field. -/
theorem integralTriple_admissible (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : m.Coprime N) :
    AdmissibleTriple (fun j => Matrix.SpecialLinearGroup.map
      (algebraMap (𝓞 (realCyclotomicField N)) (realCyclotomicField N)) (integralTripleSL N m j)) := by
  have ht : (fun j => Matrix.SpecialLinearGroup.map
      (algebraMap (𝓞 (realCyclotomicField N)) (realCyclotomicField N)) (integralTripleSL N m j)) =
      standardTriple (tau N m) := by
    funext j
    apply Subtype.ext
    obtain ⟨h₀, h₁, hInf⟩ := map_triple
      (algebraMap (𝓞 (realCyclotomicField N)) (realCyclotomicField N)) (tauInteger N m)
    fin_cases j
    · exact h₀
    · exact h₁
    · exact hInf
  rw [ht]
  exact standardTriple_admissible_of_pow _ (tau_ne_two N m hN hm) N (by omega)
    (Uinf_tau_pow N m hN hm)

end

end HilbertModularity.Cyclotomic
