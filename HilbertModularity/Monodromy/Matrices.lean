/- Assembled by AxiomProver. -/

module

/-
Assembled with the assistance of AxiomProver, an automated formalization tool from Axiom Math.

# Local monodromy of `HD_{N,m}` and the integral triple

The elementary algebra behind §1.3 (the field of definition `K_N = ℚ(ζ_N)⁺`) and
Lemma 3.1 (the admissible triple `U^{(m)}` of (3.1)).
-/
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace HilbertModularity.Monodromy

open Polynomial Matrix

/-- [TripathiGoswami], §1.3: for `m` a unit mod `N`, a unit `h` stabilizes the unordered pair `{m, -m}` if
and only if `h ≡ ±1 (mod N)`. -/
theorem stabilizer_pair_iff {N : ℕ} (m h : (ZMod N)ˣ) :
    ({(h : ZMod N) * m, -((h : ZMod N) * m)} : Set (ZMod N)) = {(m : ZMod N), -(m : ZMod N)} ↔
      h = 1 ∨ h = -1 := by
  constructor
  · intro hS
    have hmem : (h : ZMod N) * m ∈ ({(m : ZMod N), -(m : ZMod N)} : Set (ZMod N)) := by
      rw [← hS]; exact Set.mem_insert _ _
    rcases hmem with h1 | h1
    · left
      apply Units.ext
      rw [Units.val_one]
      exact (Units.mul_left_inj m).1 (by rw [h1, one_mul])
    · right
      apply Units.ext
      rw [Units.val_neg, Units.val_one]
      exact (Units.mul_left_inj m).1 (by rw [h1, neg_one_mul])
  · rintro (rfl | rfl)
    · simp
    · simp [Set.pair_comm]

/-- [TripathiGoswami], §1.3: `(X - ζ^m)(X - ζ^{-m}) = X² - (ζ^m + ζ^{-m}) X + 1`. -/
theorem numerator_quadratic {K : Type*} [Field K] (ζ : K) (hζ : ζ ≠ 0) (m : ℤ) :
    (X - C (ζ ^ m)) * (X - C (ζ ^ (-m))) = X ^ 2 - C (ζ ^ m + ζ ^ (-m)) * X + 1 := by
  have h1 : ζ ^ m * ζ ^ (-m) = 1 := by
    rw [← zpow_add₀ hζ, add_neg_cancel, zpow_zero]
  have h2 : C (ζ ^ m) * C (ζ ^ (-m)) = (1 : K[X]) := by rw [← C_mul, h1, C_1]
  rw [C_add]
  linear_combination h2

section Triple

variable {R : Type*} [CommRing R]

/-- `U₀ = [[1,1],[0,1]]` (paper, (3.1)). -/
def U0 : Matrix (Fin 2) (Fin 2) R := !![1, 1; 0, 1]

/-- `U₁ = [[1,0],[τ-2,1]]` (paper, (3.1)). -/
def U1 (τ : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; τ - 2, 1]

/-- `U_∞ = (U₀ U₁)⁻¹` (paper, (3.1)). -/
noncomputable def Uinf (τ : R) : Matrix (Fin 2) (Fin 2) R := (U0 * U1 τ)⁻¹

theorem det_U0 : (U0 : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [U0, Matrix.det_fin_two_of]

theorem det_U1 (τ : R) : (U1 τ).det = 1 := by
  simp [U1, Matrix.det_fin_two_of]

/-- The product `U₀ U₁` computed explicitly. -/
private lemma U0_mul_U1_eq (τ : R) : U0 * U1 τ = !![τ - 1, 1; τ - 2, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [U0, U1, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- `U_∞` computed explicitly. -/
private lemma Uinf_eq (τ : R) : Uinf τ = !![1, -1; 2 - τ, τ - 1] := by
  unfold Uinf
  apply Matrix.inv_eq_right_inv
  rw [U0_mul_U1_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- [TripathiGoswami], Lemma 3.1: `U₀ U₁ U_∞ = 1`. -/
theorem U0_mul_U1_mul_Uinf (τ : R) : U0 * U1 τ * Uinf τ = 1 := by
  rw [U0_mul_U1_eq, Uinf_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- [TripathiGoswami], Lemma 3.1: `tr(U₀U₁) = τ`. -/
theorem trace_U0_mul_U1 (τ : R) : (U0 * U1 τ).trace = τ := by
  rw [U0_mul_U1_eq, Matrix.trace_fin_two_of]; ring

/-- [TripathiGoswami], Lemma 3.1: `det(U₀U₁) = 1`. -/
theorem det_U0_mul_U1 (τ : R) : (U0 * U1 τ).det = 1 := by
  rw [U0_mul_U1_eq, Matrix.det_fin_two_of]; ring

/-- The monodromy at infinity has determinant one. -/
theorem det_Uinf (τ : R) : (Uinf τ).det = 1 := by
  rw [Uinf_eq, Matrix.det_fin_two_of]
  ring

/-- [TripathiGoswami], Lemma 3.1: `U_∞` has characteristic polynomial `X² - τX + 1`. -/
theorem charpoly_Uinf (τ : R) : (Uinf τ).charpoly = X ^ 2 - C τ * X + 1 := by
  nontriviality R
  rw [Matrix.charpoly_fin_two, Uinf_eq, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  have h1 : (1 : R) + (τ - 1) = τ := by ring
  have h2 : (1 : R) * (τ - 1) - -1 * (2 - τ) = 1 := by ring
  rw [h1, h2, C_1]

/-- [TripathiGoswami], Lemma 3.1: `U₀` is a nontrivial unipotent. -/
theorem U0_unipotent [Nontrivial R] :
    (U0 : Matrix (Fin 2) (Fin 2) R) ≠ 1 ∧ (U0 - 1 : Matrix (Fin 2) (Fin 2) R) ^ 2 = 0 := by
  constructor
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [U0] at this
  · rw [sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [U0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- [TripathiGoswami], Lemma 3.1: `U₁` is a nontrivial unipotent when `τ ≠ 2`. -/
theorem U1_unipotent (τ : R) (hτ : τ ≠ 2) : U1 τ ≠ 1 ∧ (U1 τ - 1) ^ 2 = 0 := by
  constructor
  · intro h
    have := congrFun (congrFun h 1) 0
    simp [U1] at this
    exact hτ (sub_eq_zero.1 this)
  · rw [sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [U1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- [TripathiGoswami], Lemma 3.1: the triple is compatible with coefficient embeddings:
if `σ(τ₁) = τ_m` then `σ(U_j^{(1)}) = U_j^{(m)}` entrywise. -/
theorem map_triple {S : Type*} [CommRing S] (σ : R →+* S) (τ : R) :
    (U0 : Matrix (Fin 2) (Fin 2) R).map σ = U0 ∧ (U1 τ).map σ = U1 (σ τ) ∧
      (Uinf τ).map σ = Uinf (σ τ) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [U0]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [U1, map_ofNat]
  · rw [Uinf_eq, Uinf_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [map_ofNat]

end Triple

section Field

variable {K : Type*} [Field K]

/-- [TripathiGoswami], Lemma 3.1: if `τ ≠ 2`, then `U₀` and `U₁` have no common eigenvector, so the group
they generate has no invariant line (absolute irreducibility, applied over an algebraic
closure). -/
theorem no_common_eigenvector (τ : K) (hτ : τ ≠ 2) (v : Fin 2 → K) (hv : v ≠ 0)
    (a b : K) (ha : U0 *ᵥ v = a • v) (hb : U1 τ *ᵥ v = b • v) : False := by
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  simp [U0, U1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at ha0 ha1 hb0 hb1
  have hv1 : v 1 = 0 := by
    by_contra hne
    have : a = 1 := by
      have : (a - 1) * v 1 = 0 := by linear_combination -ha1
      rcases mul_eq_zero.1 this with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hne
    subst this
    exact hne (by linear_combination ha0)
  have hv0 : v 0 ≠ 0 := by
    intro h0; apply hv; ext i; fin_cases i <;> simp [h0, hv1]
  rw [hv1] at hb1
  have : (τ - 2) * v 0 = 0 := by linear_combination hb1
  rcases mul_eq_zero.1 this with h | h
  · exact hτ (sub_eq_zero.1 h)
  · exact hv0 h

/-- The two unipotent generators have no proper nonzero invariant subspace,
over any field in which the trace parameter is not `2`. -/
theorem invariant_submodule_eq_bot_or_top (τ : K) (hτ : τ ≠ 2)
    (W : Submodule K (Fin 2 → K))
    (h₀ : ∀ v ∈ W, U0 *ᵥ v ∈ W) (h₁ : ∀ v ∈ W, U1 τ *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hex : ∃ v ∈ W, v ≠ 0 := by
    by_contra h
    push Not at h
    apply hW
    apply le_antisymm ?_ bot_le
    intro v hv
    rw [h v hv]
    exact Submodule.zero_mem _
  obtain ⟨v, hv, hv0⟩ := hex
  let e₀ : Fin 2 → K := ![1, 0]
  let e₁ : Fin 2 → K := ![0, 1]
  have he₀ : e₀ ∈ W := by
    by_cases hv1 : v 1 = 0
    · have hv00 : v 0 ≠ 0 := by
        intro h
        apply hv0
        ext i
        fin_cases i <;> simp [h, hv1]
      have h := W.smul_mem (v 0)⁻¹ hv
      convert h using 1
      ext i
      fin_cases i <;> simp [e₀, hv00, hv1]
    · have h := W.smul_mem (v 1)⁻¹ (W.sub_mem (h₀ v hv) hv)
      convert h using 1
      ext i
      fin_cases i <;> simp [e₀, U0, dotProduct, Fin.sum_univ_two, vecHead, vecTail, hv1]
  have he₁ : e₁ ∈ W := by
    have h := W.smul_mem (τ - 2)⁻¹ (W.sub_mem (h₁ e₀ he₀) he₀)
    convert h using 1
    ext i
    fin_cases i <;> simp [e₀, e₁, U1, vecHead, vecTail, sub_ne_zero.mpr hτ]
  apply le_antisymm le_top
  intro w _
  have h := W.add_mem (W.smul_mem (w 0) he₀) (W.smul_mem (w 1) he₁)
  convert h using 1
  ext i
  fin_cases i <;> simp [e₀, e₁]

/-- [TripathiGoswami], Lemma 3.1: for `ζ` a primitive `N`-th root of unity with `N ≥ 3` and `m` prime to `N`,
`τ_{N,m} = ζ^m + ζ^{-m} ≠ 2`. -/
theorem tau_ne_two {N : ℕ} (hN : 3 ≤ N) {ζ : K} (hζ : IsPrimitiveRoot ζ N) {m : ℕ}
    (hm : m.Coprime N) : ζ ^ m + ζ⁻¹ ^ m ≠ 2 := by
  have hp := hζ.pow_of_coprime m hm
  have hne : ζ ^ m ≠ 0 := hp.ne_zero (by omega)
  intro h
  rw [inv_pow] at h
  have h1 : ζ ^ m = 1 := by
    have : (ζ ^ m - 1) ^ 2 = 0 := by
      field_simp at h
      linear_combination h
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
  have := hp.eq_orderOf
  rw [h1, orderOf_one] at this
  omega

/-- [TripathiGoswami], Lemma 3.1: the eigenvalues of `U_∞` are `ζ^m` and `ζ^{-m}`. -/
theorem charpoly_Uinf_eq_prod (ζ : K) (hζ : ζ ≠ 0) (m : ℕ) :
    (Uinf (ζ ^ m + ζ⁻¹ ^ m)).charpoly = (X - C (ζ ^ m)) * (X - C (ζ⁻¹ ^ m)) := by
  rw [charpoly_Uinf]
  have h := numerator_quadratic ζ hζ (m : ℤ)
  simp only [_root_.zpow_neg, zpow_natCast, inv_pow] at h ⊢
  exact h.symm

/-- An explicit eigenbasis for the monodromy at infinity. The two primitive-root
eigenvalues are distinct because their common order is at least three. -/
theorem diagonalize_Uinf {N : ℕ} (hN : 3 ≤ N) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) {m : ℕ} (hm : m.Coprime N) :
    ∃ P : Matrix (Fin 2) (Fin 2) K, IsUnit P.det ∧
      Uinf (ζ ^ m + ζ⁻¹ ^ m) * P = P * diagonal ![ζ ^ m, ζ⁻¹ ^ m] := by
  set l := ζ ^ m with hl
  have hp : IsPrimitiveRoot l N := hζ.pow_of_coprime m hm
  have hl0 : l ≠ 0 := hp.ne_zero (by omega)
  have hτ : ζ ^ m + ζ⁻¹ ^ m = l + l⁻¹ := by rw [inv_pow]
  have hll : l - l⁻¹ ≠ 0 := by
    intro h
    have h2 : l ^ 2 = 1 := by
      field_simp at h
      linear_combination h
    have := Nat.le_of_dvd two_pos (hp.dvd_of_pow_eq_one 2 h2)
    omega
  refine ⟨!![1, 1; 1 - l, 1 - l⁻¹], ?_, ?_⟩
  · rw [det_fin_two_of]
    refine isUnit_iff_ne_zero.2 ?_
    intro h
    apply hll
    linear_combination h
  · rw [hτ, Uinf_eq]
    simp only [inv_pow, ← hl]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- [TripathiGoswami], Lemma 3.1: the local monodromy at infinity has exact order N. -/
theorem orderOf_Uinf {N : ℕ} (hN : 3 ≤ N) {ζ : K} (hζ : IsPrimitiveRoot ζ N) {m : ℕ}
    (hm : m.Coprime N) : orderOf (Uinf (ζ ^ m + ζ⁻¹ ^ m)) = N := by
  set l := ζ ^ m with hl
  have hp : IsPrimitiveRoot l N := hζ.pow_of_coprime m hm
  have hτ : ζ ^ m + ζ⁻¹ ^ m = l + l⁻¹ := by rw [inv_pow]
  obtain ⟨P, hP, hMP⟩ := diagonalize_Uinf hN hζ hm
  rw [hτ] at hMP ⊢
  simp only [inv_pow, ← hl] at hMP
  set M := Uinf (l + l⁻¹)
  set D : Matrix (Fin 2) (Fin 2) K := diagonal ![l, l⁻¹] with hD
  have hpow : ∀ k : ℕ, M ^ k * P = P * D ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, hMP, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  rw [hp.eq_orderOf]
  refine orderOf_eq_orderOf_iff.2 fun k => ?_
  have hDk : D ^ k = diagonal ![l ^ k, l⁻¹ ^ k] := by
    rw [hD, diagonal_pow]; congr 1; ext i; fin_cases i <;> simp
  constructor
  · intro h
    have h2 := hpow k
    rw [h, one_mul] at h2
    have h3 : D ^ k = 1 := by
      have := congrArg (P⁻¹ * ·) h2
      rw [← mul_assoc, Matrix.nonsing_inv_mul _ hP, one_mul] at this
      exact this.symm
    have := congrFun (congrFun h3 0) 0
    rw [hDk] at this
    simpa using this
  · intro h
    have hD1 : D ^ k = 1 := by
      rw [hDk, inv_pow, h, inv_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have h2 := hpow k
    rw [hD1, mul_one] at h2
    have := congrArg (· * P⁻¹) h2
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ hP, mul_one] at this

end Field

end HilbertModularity.Monodromy
