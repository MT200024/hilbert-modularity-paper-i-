/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Adic completeness and positive ideal powers

Positive powers define cofinal ideal filtrations. This permits the integral
RM-prime completion to be compared with the rational-prime completion used
by the actual Tate inverse limit; see [TripathiGoswami].
-/

@[expose] public noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace IsAdicComplete

/-- Positive powers of an ideal have exactly the same complete modules. -/
theorem pow_iff (I : Ideal R) (e : ℕ) (he : 0 < e) :
    IsAdicComplete (I ^ e) M ↔ IsAdicComplete I M := by
  have hle (n : ℕ) : n ≤ e * n := Nat.le_mul_of_pos_left n he
  have hsub (n : ℕ) : (I ^ e) ^ n • (⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
    rw [← pow_mul]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (hle n))
  constructor
  · intro h
    refine { haus' := ?_, prec' := ?_ }
    · intro x hx
      apply h.haus x
      intro n
      simpa only [← pow_mul] using hx (e * n)
    · intro f hf
      obtain ⟨L, hL⟩ := h.prec (f := fun n => f (e * n)) (fun {m n} hmn => by
        simpa only [← pow_mul] using hf (Nat.mul_le_mul_left e hmn))
      refine ⟨L, fun n => ?_⟩
      exact (hf (hle n)).trans (SModEq.mono (hsub n) (hL n))
  · intro h
    refine { haus' := ?_, prec' := ?_ }
    · exact fun x hx => h.haus x (fun n => SModEq.mono (hsub n) (hx n))
    · intro f hf
      obtain ⟨L, hL⟩ := h.prec (f := f) (fun {m n} hmn => SModEq.mono (hsub m) (hf hmn))
      refine ⟨L, fun n => (hf (hle n)).trans ?_⟩
      simpa only [← pow_mul] using hL (e * n)

end IsAdicComplete

namespace AdicCompletion

/-- Finite projections of the completed ring respect the ideal quotient transition maps. -/
theorem factor_evalₐ (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn) (evalₐ I n x) = evalₐ I m x := by
  obtain ⟨f, rfl⟩ := mk_surjective I R x
  simp only [evalₐ_mk, Ideal.Quotient.factorₐ_apply_mk]
  simpa [SModEq.def] using (f.property hmn).symm

/-- Forgetting the cofinal indexing by a positive ideal power. -/
def ofPow (I : Ideal R) (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R →ₐ[R] AdicCompletion I R :=
  liftAlgHom I (fun n =>
    (Ideal.Quotient.factorₐ R (show (I ^ e) ^ n ≤ I ^ n by
      rw [← pow_mul]
      exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he))).comp (evalₐ (I ^ e) n))
    (fun {m n} hmn => by
      ext x
      simp only [AlgHom.comp_apply]
      rw [← factor_evalₐ (I ^ e) hmn x]
      simp only [← AlgHom.comp_apply, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp])

/-- Restricting the finite projections to multiples of the ideal-power exponent. -/
def toPow (I : Ideal R) (e : ℕ) :
    AdicCompletion I R →ₐ[R] AdicCompletion (I ^ e) R :=
  liftAlgHom (I ^ e) (fun n =>
    (Ideal.Quotient.factorₐ R (show I ^ (e * n) ≤ (I ^ e) ^ n by rw [pow_mul])).comp
      (evalₐ I (e * n)))
    (fun {m n} hmn => by
      ext x
      simp only [AlgHom.comp_apply]
      rw [← factor_evalₐ I (Nat.mul_le_mul_left e hmn) x]
      simp only [← AlgHom.comp_apply, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp])

@[simp]
theorem evalₐ_ofPow (I : Ideal R) (e : ℕ) (he : 0 < e) (n : ℕ)
    (x : AdicCompletion (I ^ e) R) :
    evalₐ I n (ofPow I e he x) =
      Ideal.Quotient.factorₐ R (show (I ^ e) ^ n ≤ I ^ n by
        rw [← pow_mul]
        exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he)) (evalₐ (I ^ e) n x) :=
  evalₐ_liftAlgHom _ _ _ _ _

@[simp]
theorem evalₐ_toPow (I : Ideal R) (e n : ℕ) (x : AdicCompletion I R) :
    evalₐ (I ^ e) n (toPow I e x) =
      Ideal.Quotient.factorₐ R (show I ^ (e * n) ≤ (I ^ e) ^ n by rw [pow_mul])
        (evalₐ I (e * n) x) :=
  evalₐ_liftAlgHom _ _ _ _ _

@[simp]
theorem ofPow_toPow (I : Ideal R) (e : ℕ) (he : 0 < e) (x : AdicCompletion I R) :
    ofPow I e he (toPow I e x) = x := by
  apply ext_evalₐ
  intro n
  simp only [evalₐ_ofPow, evalₐ_toPow]
  rw [← factor_evalₐ I (Nat.le_mul_of_pos_left n he) x]
  simp only [← AlgHom.comp_apply, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]

@[simp]
theorem toPow_ofPow (I : Ideal R) (e : ℕ) (he : 0 < e) (x : AdicCompletion (I ^ e) R) :
    toPow I e (ofPow I e he x) = x := by
  apply ext_evalₐ
  intro n
  simp only [evalₐ_toPow, evalₐ_ofPow]
  rw [← factor_evalₐ (I ^ e) (Nat.le_mul_of_pos_left n he) x]
  simp only [← AlgHom.comp_apply, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]

/-- Positive powers of an ideal give canonically isomorphic completed coefficient rings. -/
def powAlgEquiv (I : Ideal R) (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R ≃ₐ[R] AdicCompletion I R where
  __ := ofPow I e he
  invFun := toPow I e
  left_inv := toPow_ofPow I e he
  right_inv := ofPow_toPow I e he

/-- The cofinal completion equivalence preserves the canonical residue map. -/
theorem evalOneₐ_powAlgEquiv (I : Ideal R) (e : ℕ) (he : 0 < e)
    (x : AdicCompletion (I ^ e) R) :
    evalOneₐ I (powAlgEquiv I e he x) =
      Ideal.Quotient.factorₐ R (Ideal.pow_le_self (Nat.ne_zero_of_lt he))
        (evalOneₐ (I ^ e) x) := by
  change Ideal.Quotient.factorₐ R (show I ^ 1 ≤ I by simp)
      (evalₐ I 1 (ofPow I e he x)) =
    Ideal.Quotient.factorₐ R _
      (Ideal.Quotient.factorₐ R (show (I ^ e) ^ 1 ≤ I ^ e by simp) (evalₐ (I ^ e) 1 x))
  rw [evalₐ_ofPow]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ (I ^ e) 1 x)
  rw [← hr]
  rfl

/-- Residue compatibility survives identifying the power ideal with another ideal. -/
theorem evalOneₐ_powAlgEquiv_cast {I J : Ideal R} (e : ℕ) (he : 0 < e)
    (h : J ^ e = I) (hIJ : I ≤ J) (x : AdicCompletion I R) :
    evalOneₐ J ((h ▸ powAlgEquiv J e he) x) =
      Ideal.Quotient.factorₐ R hIJ (evalOneₐ I x) := by
  subst I
  exact evalOneₐ_powAlgEquiv J e he x

end AdicCompletion
