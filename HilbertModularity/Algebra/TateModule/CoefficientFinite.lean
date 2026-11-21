/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.PrimeCompletion
public import HilbertModularity.Algebra.AdicCompletion.Padic
public import HilbertModularity.Topology.TateModule.FiniteGeneration

/-! # Finite generation over actual completed coefficients

Canonical p-adic scalars in the completed coefficient ring act as the native
p-adic scalars on the actual Tate inverse limit. Thus its existing finite
generation over `ℤ_p` supplies finite generation over the completed RM
coefficients. See [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

attribute [local instance] coefficientModule completedCoefficientModule

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- Finite completed coefficient congruence acts by the same congruence on actual Tate vectors. -/
theorem completedCoefficient_smodEq_smul (n : ℕ)
    (c : AdicCompletion (Ideal.span {(p : R)}) R) (r : R)
    (hc : AdicCompletion.evalₐ (Ideal.span {(p : R)}) n c =
      Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n) r) (x : integral p A) :
    c • x ≡ r • x [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R (integral p A)))] := by
  let I := Ideal.span {(p : R)}
  have hc' : c.val n = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) r := by
    change AdicCompletion.eval I R n c = _
    rw [← AdicCompletion.factor_evalₐ_eq_eval I c (by simp), hc]
    rfl
  have h := congrArg (fun y : AdicCompletion I (integral p A) => y.val n)
    ((coefficientCompletionEquiv p R A).map_smul c x)
  change Submodule.Quotient.mk (p := I ^ n • ⊤) (c • x) =
    c.val n • Submodule.Quotient.mk (p := I ^ n • ⊤) x at h
  rw [hc'] at h
  exact h

/-- Canonical p-adic scalars in completed coefficients act as the actual native Tate scalars. -/
theorem completedCoefficient_smul_padic (z : ℤ_[p]) (x : integral p A) :
    PadicInt.toAdicCompletion p R z • x = z • x := by
  apply Subtype.ext
  funext n
  let k := (PadicInt.toZModPow n z).val
  have hk : (k : ZMod (p ^ n)) = PadicInt.toZModPow n z := ZMod.natCast_zmod_val _
  have hc : AdicCompletion.evalₐ (Ideal.span {(p : R)}) n (PadicInt.toAdicCompletion p R z) =
      Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n) (k : R) := by
    rw [PadicInt.evalₐ_toAdicCompletion, ← hk, map_natCast]
    rfl
  have h := (coefficient_smodEq_iff_projection_eq p R A n _ _).mp
    (completedCoefficient_smodEq_smul p R A n _ (k : R) hc x)
  change projection p A n (PadicInt.toAdicCompletion p R z • x) = projection p A n (z • x)
  rw [h, Nat.cast_smul_eq_nsmul, map_nsmul, map_smul]
  change k • projection p A n x = PadicInt.toZModPow n z • projection p A n x
  rw [← hk, Nat.cast_smul_eq_nsmul]

/-- Finite generation of the actual native Tate module persists over its completed coefficients. -/
theorem completedCoefficient_finite [Module.Finite ℤ_[p] (integral p A)] :
    Module.Finite (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) := by
  let := (PadicInt.toAdicCompletion p R).toAlgebra
  have : IsScalarTower ℤ_[p] (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) :=
    ⟨fun z c x => by
      change (PadicInt.toAdicCompletion p R z * c) • x = z • (c • x)
      rw [mul_smul, completedCoefficient_smul_padic]⟩
  exact Module.Finite.of_restrictScalars_finite ℤ_[p]
    (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A)

/-- The actual RM-prime lattice is finite whenever the actual native Tate module is finite. -/
theorem coefficientPrime_finite [Module.Finite ℤ_[p] (integral p A)]
    (J : Ideal R) (e : ℕ) (he : 0 < e) (hJ : J ^ e = Ideal.span {(p : R)}) :
    letI := coefficientPrimeModule p R A J e he hJ
    Module.Finite (AdicCompletion J R) (integral p A) := by
  let := coefficientPrimeModule p R A J e he hJ
  have := completedCoefficient_finite p R A
  let E := coefficientPrimeRingEquiv p R J e he hJ
  let f : integral p A →ₛₗ[E.toRingHom] integral p A :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change c • x = E.symm (E c) • x
        rw [AlgEquiv.symm_apply_apply] }
  exact Module.Finite.of_surjective f Function.surjective_id

/-- Finite actual level-one torsion and p-divisibility imply a finite actual RM-prime lattice. -/
theorem coefficientPrime_finite_of_finite_torsion [Finite (Torsion p A 1)]
    (hpdiv : Function.Surjective (fun x : A => p • x))
    (J : Ideal R) (e : ℕ) (he : 0 < e) (hJ : J ^ e = Ideal.span {(p : R)}) :
    letI := coefficientPrimeModule p R A J e he hJ
    Module.Finite (AdicCompletion J R) (integral p A) := by
  have := integral_finite_of_finite_torsion p A hpdiv
  exact coefficientPrime_finite p R A J e he hJ

end TateModule
