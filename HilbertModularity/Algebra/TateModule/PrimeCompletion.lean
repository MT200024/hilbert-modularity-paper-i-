/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CompletedReduction
public import HilbertModularity.Algebra.AdicCompletion.IdealPower

/-! # Completeness of the actual Tate module at a coefficient prime

When the rational-prime ideal is a positive power of the RM-prime ideal,
the actual Tate inverse limit is already complete at that RM prime.
The ramification relation is explicit; see [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

attribute [local instance] coefficientModule

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- Total ramification transfers actual Tate completeness to the coefficient-prime ideal. -/
theorem isAdicComplete_coefficientPrime (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) : IsAdicComplete J (integral p A) := by
  apply (IsAdicComplete.pow_iff J e he).mp
  rw [hJ]
  infer_instance

/-- Completion at the actual coefficient-prime ideal recovers the original Tate module. -/
def coefficientPrimeCompletionEquiv (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) :
    integral p A ≃ₗ[R] AdicCompletion J (integral p A) := by
  haveI := isAdicComplete_coefficientPrime p R A J e he hJ
  exact AdicCompletion.ofLinearEquiv J (integral p A)

@[simp]
theorem coefficientPrimeCompletionEquiv_apply (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) (x : integral p A) :
    coefficientPrimeCompletionEquiv p R A J e he hJ x =
      AdicCompletion.of J (integral p A) x := rfl

/-- The coefficient completion at the rational prime is canonically the RM-prime completion. -/
def coefficientPrimeRingEquiv (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) :
    AdicCompletion (Ideal.span {(p : R)}) R ≃ₐ[R] AdicCompletion J R :=
  hJ ▸ AdicCompletion.powAlgEquiv J e he

omit [Fact p.Prime] in
/-- The actual RM-prime residue agrees with the previously constructed canonical principal residue. -/
theorem coefficientPrimeRingEquiv_residue (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (c : AdicCompletion (Ideal.span {(p : R)}) R) :
    AdicCompletion.evalOneₐ (Ideal.span {a})
      (coefficientPrimeRingEquiv p R (Ideal.span {a}) e he hJ c) =
        completedPrincipalResidue p R a b hab c := by
  exact AdicCompletion.evalOneₐ_powAlgEquiv_cast e he hJ (by
    rw [← hJ]
    exact Ideal.pow_le_self (Nat.ne_zero_of_lt he)) c

attribute [local instance] completedCoefficientModule

/-- The actual RM-prime completion acts on the original Tate module through the canonical cofinal equivalence. -/
@[instance_reducible]
def coefficientPrimeModule (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) :
    Module (AdicCompletion J R) (integral p A) :=
  Module.compHom (integral p A) (coefficientPrimeRingEquiv p R J e he hJ).symm.toRingHom

/-- The RM-prime action extends the actual integral coefficient action. -/
theorem coefficientPrime_smul_algebraMap (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) (r : R) (x : integral p A) :
    letI := coefficientPrimeModule p R A J e he hJ
    algebraMap R (AdicCompletion J R) r • x = r • x := by
  change (coefficientPrimeRingEquiv p R J e he hJ).symm
    (algebraMap R (AdicCompletion J R) r) • x = r • x
  rw [AlgEquiv.commutes, completedCoefficient_smul_algebraMap]

/-- The actual torsion projection is semilinear for the actual RM-prime residue map. -/
theorem principalProjection_prime_smul (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (c : AdicCompletion (Ideal.span {a}) R) (x : integral p A) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    principalProjection p R A a b hab (c • x) =
      AdicCompletion.evalOneₐ (Ideal.span {a}) c • principalProjection p R A a b hab x := by
  change principalProjection p R A a b hab
    ((coefficientPrimeRingEquiv p R (Ideal.span {a}) e he hJ).symm c • x) = _
  rw [principalProjection_completed_smul]
  have h := coefficientPrimeRingEquiv_residue p R a b hab e he hJ
    ((coefficientPrimeRingEquiv p R (Ideal.span {a}) e he hJ).symm c)
  rw [AlgEquiv.apply_symm_apply] at h
  rw [← h]

/-- Reduction over the actual RM-prime completion gives the actual principal torsion subgroup. -/
def coefficientPrimeResidualEquiv (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    ((R ⧸ Ideal.span {a}) ⊗[AdicCompletion (Ideal.span {a}) R] integral p A) ≃ₗ[R ⧸ Ideal.span {a}]
      Submodule.torsionBy R A a := by
  let S := AdicCompletion (Ideal.span {a}) R
  let k := R ⧸ Ideal.span {a}
  letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  let q : S →+* k := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom
  letI : Algebra S k := q.toAlgebra
  letI : Module S (Submodule.torsionBy R A a) := Module.compHom _ q
  letI : IsScalarTower S k (Submodule.torsionBy R A a) :=
    ⟨fun c d x => mul_smul (q c) d x⟩
  let f : integral p A →ₗ[S] Submodule.torsionBy R A a :=
    { __ := (principalProjection p R A a b hab).toAddMonoidHom
      map_smul' := principalProjection_prime_smul p R A a b hab e he hJ }
  have hf : Function.Surjective f := principalProjection_surjective p R A a b hab hpdiv
  have hker : f.ker = RingHom.ker (algebraMap S k) • (⊤ : Submodule S (integral p A)) := by
    ext x
    rw [LinearMap.mem_ker]
    change principalProjection p R A a b hab x = 0 ↔
      x ∈ RingHom.ker q • (⊤ : Submodule S (integral p A))
    rw [principalProjection_eq_zero_iff p R A a b hab hpdiv]
    change _ ↔ x ∈ RingHom.ker (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom • _
    rw [AdicCompletion.ker_evalOneₐ_eq_map _ (Submodule.fg_span_singleton _),
      Ideal.map_span, Set.image_singleton, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and, coefficientPrime_smul_algebraMap]
  exact LinearEquiv.ofBijective (f.liftBaseChange k)
    (f.bijective_liftBaseChange_of_ker (AdicCompletion.evalOneₐ_surjective _) hf hker)

@[simp]
theorem coefficientPrimeResidualEquiv_tmul (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (hpdiv : Function.Surjective (fun x : A => p • x))
    (c : R ⧸ Ideal.span {a}) (x : integral p A) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    coefficientPrimeResidualEquiv p R A a b hab e he hJ hpdiv
      (c ⊗ₜ[AdicCompletion (Ideal.span {a}) R] x) =
        c • principalProjection p R A a b hab x := rfl

/-- Actual torsion dimension is the rank over the actual RM-prime completion. -/
theorem coefficientPrimeTorsion_finrank (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    [(Ideal.span {a}).IsMaximal] (hpdiv : Function.Surjective (fun x : A => p • x)) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    ∀ [Module.Free (AdicCompletion (Ideal.span {a}) R) (integral p A)],
    Module.finrank (R ⧸ Ideal.span {a}) (Submodule.torsionBy R A a) =
      Module.finrank (AdicCompletion (Ideal.span {a}) R) (integral p A) := by
  let := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  intro _
  let := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
  have : Nontrivial (AdicCompletion (Ideal.span {a}) R) :=
    ⟨⟨0, 1, fun h => (zero_ne_one : (0 : R ⧸ Ideal.span {a}) ≠ 1) (by
      simpa using congrArg (AdicCompletion.evalOneₐ (Ideal.span {a})) h)⟩⟩
  rw [← (coefficientPrimeResidualEquiv p R A a b hab e he hJ hpdiv).finrank_eq,
    Module.finrank_baseChange]

end TateModule
