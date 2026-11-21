/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! # Rank-two characteristic polynomials and traces of powers -/

@[expose] public section

namespace HilbertModularity

open Matrix Polynomial

section Newton

variable {R : Type*} [CommRing R]

/-- Vieta's formulas for a monic quadratic with roots `α`, `β`. -/
private lemma sum_prod_of_quadratic_factorization (α β a δ : R) (h : (X - C α) * (X - C β) = X ^ 2 - C a * X + C δ) :
    α + β = a ∧ α * β = δ := by
  have h1 := congrArg (fun p => p.coeff 1) h
  have h0 := congrArg (fun p => p.coeff 0) h
  simp [mul_sub, sub_mul, coeff_X, coeff_C, coeff_X_pow] at h1 h0
  constructor
  · linear_combination -h1
  · linear_combination h0

/-- Residue degree one: `α + β = a_𝔮` for the roots of `X² - a X + δ`. -/
theorem root_sum_of_quadratic_factorization (α β a δ : R) (h : (X - C α) * (X - C β) = X ^ 2 - C a * X + C δ) :
    α ^ 1 + β ^ 1 = a := by
  simpa using (sum_prod_of_quadratic_factorization α β a δ h).1

/-- Residue degree two, (6.3): `α² + β² = a² - 2δ`. -/
theorem root_sq_sum_of_quadratic_factorization (α β a δ : R) (h : (X - C α) * (X - C β) = X ^ 2 - C a * X + C δ) :
    α ^ 2 + β ^ 2 = a ^ 2 - 2 * δ := by
  obtain ⟨h1, h2⟩ := sum_prod_of_quadratic_factorization α β a δ h
  rw [← h1, ← h2]; ring

/-- [TripathiGoswami], §1.1: the symmetric-square trace `α² + αβ + β² = a² - δ` differs from the
Frobenius-power trace. -/
theorem symmetricSquare_root_sum (α β a δ : R) (h : (X - C α) * (X - C β) = X ^ 2 - C a * X + C δ) :
    α ^ 2 + α * β + β ^ 2 = a ^ 2 - δ := by
  obtain ⟨h1, h2⟩ := sum_prod_of_quadratic_factorization α β a δ h
  rw [← h1, ← h2]; ring

/-- [TripathiGoswami], Lemma 5.1: for a `2 × 2` matrix, `2 det F = (tr F)² - tr(F²)`. -/
theorem two_mul_det_eq_sq_trace_sub_trace_sq (F : Matrix (Fin 2) (Fin 2) R) :
    2 * F.det = F.trace ^ 2 - (F ^ 2).trace := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two, sq F]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

end Newton

variable {R : Type*} [CommRing R]

/-- The degree-two Cayley–Hamilton identity, including the zero ring. -/
lemma matrix_sq_eq_trace_smul_sub_det (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.trace_fin_two] <;> ring

/-- Power traces satisfy the characteristic-polynomial recurrence for every exponent. -/
theorem trace_pow_recurrence (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (M ^ (n + 2)).trace = M.trace * (M ^ (n + 1)).trace - M.det * (M ^ n).trace := by
  rw [pow_add, matrix_sq_eq_trace_smul_sub_det, mul_sub,
    mul_smul_comm, mul_smul_comm, mul_one, ← pow_succ,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul]
  rfl

/-- Roots counted with multiplicity give the trace and determinant by Vieta. -/
lemma charpoly_roots_sum_prod [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R)
    (α β : R) (h : M.charpoly = (X - C α) * (X - C β)) :
    α + β = M.trace ∧ α * β = M.det := by
  rw [Matrix.charpoly_fin_two] at h
  have h1 := congrArg (fun p : R[X] => p.coeff 1) h
  have h0 := congrArg (fun p : R[X] => p.coeff 0) h
  simp [mul_sub, sub_mul, coeff_X, coeff_C, coeff_X_pow] at h1 h0
  constructor
  · linear_combination h1
  · linear_combination -h0

/-- The trace of every matrix power is the power sum of the two roots of its
characteristic polynomial, including repeated roots. -/
theorem trace_pow_eq_sum_roots [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R)
    (α β : R) (h : M.charpoly = (X - C α) * (X - C β)) (n : ℕ) :
    (M ^ n).trace = α ^ n + β ^ n := by
  obtain ⟨hs, hp⟩ := charpoly_roots_sum_prod M α β h
  induction n using Nat.twoStepInduction with
  | zero => simp [← two_mul]
  | one => simpa using hs.symm
  | more n ih₀ ih₁ =>
    rw [trace_pow_recurrence, ih₀, ih₁, ← hs, ← hp]
    ring

/-- A coefficient embedding preserves the power-trace identity. The roots may
lie in an extension field; their factorization records algebraic multiplicity. -/
theorem map_trace_pow_eq_sum_roots {S : Type*} [CommRing S] [Nontrivial S]
    (σ : R →+* S) (M : Matrix (Fin 2) (Fin 2) R) (α β : S)
    (h : M.charpoly.map σ = (X - C α) * (X - C β)) (n : ℕ) :
    σ ((M ^ n).trace) = α ^ n + β ^ n := by
  rw [AddMonoidHom.map_trace, Matrix.map_pow]
  exact trace_pow_eq_sum_roots (M.map σ) α β (by rwa [Matrix.charpoly_map]) n

/-- The coordinate-independent power-trace identity, expressed in an arbitrary
two-element basis and with roots in a coefficient extension. -/
theorem linearMap_trace_pow_eq_sum_roots
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {S : Type*} [CommRing S] [Nontrivial S] (σ : R →+* S)
    (b : Module.Basis (Fin 2) R V) (f : V →ₗ[R] V) (α β : S)
    (h : f.charpoly.map σ = (X - C α) * (X - C β)) (n : ℕ) :
    σ (LinearMap.trace R V (f ^ n)) = α ^ n + β ^ n := by
  rw [LinearMap.trace_eq_matrix_trace R b, ← LinearMap.toMatrix_pow]
  exact map_trace_pow_eq_sum_roots σ (LinearMap.toMatrix b b f) α β
    (by rwa [LinearMap.charpoly_toMatrix]) n

end HilbertModularity

namespace Module.End

/-- Two distinct eigenvalues determine the trace of a rank-two endomorphism. -/
theorem trace_eq_add_of_hasEigenvalue {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (b : Module.Basis (Fin 2) K V)
    (f : Module.End K V) {α β : K} (hαβ : α ≠ β)
    (hα : f.HasEigenvalue α) (hβ : f.HasEigenvalue β) :
    LinearMap.trace K V f = α + β := by
  let := Module.Finite.of_basis b
  let M := LinearMap.toMatrix b b f
  have he (x : K) (hx : f.HasEigenvalue x) : x ^ 2 - M.trace * x + M.det = 0 := by
    have h := (Module.End.hasEigenvalue_iff_isRoot_charpoly f x).mp hx
    rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_fin_two] at h
    simpa [M, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow] using h
  have hp : (α - β) * (α + β - M.trace) = 0 := by
    linear_combination he α hα - he β hβ
  have ht := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hαβ)
  rw [LinearMap.trace_eq_matrix_trace K b]
  exact (sub_eq_zero.mp ht).symm

end Module.End
