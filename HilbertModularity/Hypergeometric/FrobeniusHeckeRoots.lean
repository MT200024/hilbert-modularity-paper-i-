/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.FrobeniusComparison
public import HilbertModularity.NumberTheory.AbsoluteFrobenius
public import HilbertModularity.LinearAlgebra.RankTwoTrace

/-! # From the geometric trace comparison to finite hypergeometric values

The final deduction of [TripathiGoswamiRevised, proof of `thm:intro-main`]
uses restriction of geometric Frobenius, the rank-two power-trace identity, and
the fixed algebraic coefficient embedding. The actual normalized Euler trace
comparison and the local Hecke polynomial remain explicit hypotheses here.
No modularity or geometric comparison is assumed through the conclusion.
-/

public noncomputable section

open scoped NumberField Pointwise
open IsDedekindDomain Polynomial

namespace HilbertModularity.Cyclotomic

attribute [local instance] Ideal.Quotient.field

variable (N : ℕ) [NeZero N]
  {K E L V : Type*} [Field K] [NumberField K] [Field E] [Field L]
  [Algebra K (cyclotomicField N)] [Algebra K E]
  [Algebra (cyclotomicField N) E] [IsScalarTower K (cyclotomicField N) E]
  [AddCommGroup V] [Module L V] [Module.Free L V] [Module.Finite L V]

/-- The actual McCarthy value is the residue-degree power sum of the local
Hecke roots. The coefficient embedding is fixed across the Euler comparison
and the Hecke polynomial, and no additional geometric prime is excluded.
The statement works for every residue degree and for repeated roots. -/
theorem mccarthyValue_eq_frobenius_root_powers
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ)
    (q : Ideal (𝓞 K)) [q.IsMaximal] [P.asIdeal.LiesOver q]
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver q] [Q.LiesOver P.asIdeal]
    (ρ : Representation L (E ≃ₐ[K] E) V) (b : Module.Basis (Fin 2) L V)
    (hρ : ∀ g ∈ Q.inertia (E ≃ₐ[K] E), ρ g = 1)
    (g : MulAction.stabilizer (E ≃ₐ[K] E) Q)
    (g' : MulAction.stabilizer (E ≃ₐ[cyclotomicField N] E) Q)
    (hg : Ideal.Quotient.stabilizerHom Q q (E ≃ₐ[K] E) g⁻¹ =
      Ideal.Quotient.arithmeticFrobenius q Q)
    (hg' : Ideal.Quotient.stabilizerHom Q P.asIdeal
      (E ≃ₐ[cyclotomicField N] E) g'⁻¹ =
      Ideal.Quotient.arithmeticFrobenius P.asIdeal Q)
    (ι : Qbar →+* L) (a δ α β : Qbar)
    (hHecke : (ρ (g : E ≃ₐ[K] E)).charpoly =
      (X ^ 2 - C a * X + C δ).map ι)
    (hroots : (X - C α) * (X - C β) = X ^ 2 - C a * X + C δ)
    (hcomparison :
      ι ((cyclotomicField N).val
        (normalizedCyclotomicEulerTrace N P.asIdeal hP m
          (P.specialization ξ hξ.valuation_eq_one.le))) =
        LinearMap.trace L V
          (ρ (AlgEquiv.restrictScalarsHom K
            (g' : E ≃ₐ[cyclotomicField N] E)))) :
    mccarthyValue N P hP m θ ξ hξ =
      α ^ P.asIdeal.inertiaDeg (𝓞 K) + β ^ P.asIdeal.inertiaDeg (𝓞 K) := by
  apply ι.injective
  rw [map_add, map_pow, map_pow,
    ← normalizedCyclotomicEulerTrace_val_mccarthyValue N P hP m hm hmN θ hθ ξ hξ,
    hcomparison,
    ρ.geometricFrobenius_restrictScalars q P.asIdeal Q hρ g g' hg hg']
  have hpoly : (ρ (g : E ≃ₐ[K] E)).charpoly.map (RingHom.id L) =
      (X - C (ι α)) * (X - C (ι β)) := by
    rw [Polynomial.map_id, hHecke, ← hroots]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
  exact linearMap_trace_pow_eq_sum_roots (RingHom.id L) b
    (ρ (g : E ≃ₐ[K] E)) (ι α) (ι β) hpoly _

section CanonicalFrobenius

variable [IsGalois K E] [IsGalois (cyclotomicField N) E]

/-- The roots needed by the final trace formula exist in the fixed algebraic
closure. Both geometric Frobenius lifts are constructed, and their required
residue actions follow from the construction. Only the actual unramified
Euler comparison and the rank-two Hecke polynomial remain inputs. -/
theorem exists_mccarthyValue_eq_hecke_root_powers
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ)
    (q : Ideal (𝓞 K)) [q.IsMaximal] [P.asIdeal.LiesOver q]
    [Finite (𝓞 K ⧸ q)]
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver q] [Q.LiesOver P.asIdeal]
    (ρ : Representation L (E ≃ₐ[K] E) V) (b : Module.Basis (Fin 2) L V)
    (hρ : ∀ g ∈ Q.inertia (E ≃ₐ[K] E), ρ g = 1)
    (ι : Qbar →+* L) (a δ : Qbar)
    (hHecke : (ρ (NumberField.geometricFrobenius K E q Q : E ≃ₐ[K] E)).charpoly =
      (X ^ 2 - C a * X + C δ).map ι)
    (hcomparison :
      ι ((cyclotomicField N).val
        (normalizedCyclotomicEulerTrace N P.asIdeal hP m
          (P.specialization ξ hξ.valuation_eq_one.le))) =
        LinearMap.trace L V
          (ρ (AlgEquiv.restrictScalarsHom K
            (NumberField.geometricFrobenius (cyclotomicField N) E P.asIdeal Q :
              E ≃ₐ[cyclotomicField N] E)))) :
    ∃ α β : Qbar,
      (X - C α) * (X - C β) = X ^ 2 - C a * X + C δ ∧
      mccarthyValue N P hP m θ ξ hξ =
        α ^ P.asIdeal.inertiaDeg (𝓞 K) + β ^ P.asIdeal.inertiaDeg (𝓞 K) := by
  have hdeg : (X ^ 2 - C a * X + C δ).degree ≠ 0 := by
    intro h
    have hc := Polynomial.coeff_eq_zero_of_degree_lt
      (p := X ^ 2 - C a * X + C δ) (n := 2) (by rw [h]; norm_num)
    norm_num at hc
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (X ^ 2 - C a * X + C δ) hdeg
  simp only [Polynomial.IsRoot, eval_add, eval_sub, eval_pow, eval_X,
    eval_mul, eval_C] at hα
  have hδ : δ = α * (a - α) := by linear_combination hα
  have hroots : (X - C α) * (X - C (a - α)) = X ^ 2 - C a * X + C δ := by
    rw [hδ]
    simp only [map_sub, map_mul]
    ring
  refine ⟨α, a - α, hroots, ?_⟩
  exact mccarthyValue_eq_frobenius_root_powers N P hP m hm hmN θ hθ ξ hξ
    q Q ρ b hρ (NumberField.geometricFrobenius K E q Q)
    (NumberField.geometricFrobenius (cyclotomicField N) E P.asIdeal Q)
    (NumberField.geometricFrobenius_inv_residue K E q Q)
    (NumberField.geometricFrobenius_inv_residue (cyclotomicField N) E P.asIdeal Q)
    ι a δ α (a - α) hHecke hroots hcomparison

/-- The degree-one and degree-two clauses of the finite hypergeometric trace
formula, with no root choices or factorization hypotheses. In degree two the
answer is the Frobenius-square trace `a² - 2δ`. -/
theorem mccarthyValue_eq_hecke_of_residue_degree
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (m : ℕ) (hm : 0 < m) (hmN : m < N)
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (ξ : cyclotomicField N) (hξ : P.GoodUnit ξ)
    (q : Ideal (𝓞 K)) [q.IsMaximal] [P.asIdeal.LiesOver q]
    [Finite (𝓞 K ⧸ q)]
    (Q : Ideal (𝓞 E)) [Q.IsMaximal] [Q.LiesOver q] [Q.LiesOver P.asIdeal]
    (ρ : Representation L (E ≃ₐ[K] E) V) (b : Module.Basis (Fin 2) L V)
    (hρ : ∀ g ∈ Q.inertia (E ≃ₐ[K] E), ρ g = 1)
    (ι : Qbar →+* L) (a δ : Qbar)
    (hHecke : (ρ (NumberField.geometricFrobenius K E q Q : E ≃ₐ[K] E)).charpoly =
      (X ^ 2 - C a * X + C δ).map ι)
    (hcomparison :
      ι ((cyclotomicField N).val
        (normalizedCyclotomicEulerTrace N P.asIdeal hP m
          (P.specialization ξ hξ.valuation_eq_one.le))) =
        LinearMap.trace L V
          (ρ (AlgEquiv.restrictScalarsHom K
            (NumberField.geometricFrobenius (cyclotomicField N) E P.asIdeal Q :
              E ≃ₐ[cyclotomicField N] E)))) :
    (P.asIdeal.inertiaDeg (𝓞 K) = 1 → mccarthyValue N P hP m θ ξ hξ = a) ∧
    (P.asIdeal.inertiaDeg (𝓞 K) = 2 →
      mccarthyValue N P hP m θ ξ hξ = a ^ 2 - 2 * δ) := by
  obtain ⟨α, β, hroots, hvalue⟩ := exists_mccarthyValue_eq_hecke_root_powers
    N P hP m hm hmN θ hθ ξ hξ q Q ρ b hρ ι a δ hHecke hcomparison
  constructor
  · intro hf
    rw [hvalue, hf]
    exact root_sum_of_quadratic_factorization α β a δ hroots
  · intro hf
    rw [hvalue, hf]
    exact root_sq_sum_of_quadratic_factorization α β a δ hroots

end CanonicalFrobenius

end HilbertModularity.Cyclotomic
