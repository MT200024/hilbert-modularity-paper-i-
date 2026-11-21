/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CoefficientCompletion

/-! # Reduction over completed integral coefficients

The canonical residue map from the completed coefficient ring acts on the
actual principal torsion subgroup. Reducing the actual Tate module over this
completed ring gives that torsion subgroup, as required for the integral
RM-prime lattice comparison in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace LinearMap

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- A surjective map with the scalar-reduction kernel becomes an isomorphism after base change. -/
theorem bijective_liftBaseChange_of_ker (f : M →ₗ[R] N)
    (hS : Function.Surjective (algebraMap R S)) (hf : Function.Surjective f)
    (hker : f.ker = RingHom.ker (algebraMap R S) • (⊤ : Submodule R M)) :
    Function.Bijective (f.liftBaseChange S) := by
  let I := RingHom.ker (algebraMap R S)
  let eS : (R ⧸ I) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hS
  let e : (S ⊗[R] M) ≃ₗ[R] N :=
    (eS.symm.toLinearEquiv.rTensor M).trans
      ((TensorProduct.quotTensorEquivQuotSMul M I).trans
        ((Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)))
  have he (x : S ⊗[R] M) : f.liftBaseChange S x = e x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      obtain ⟨r, rfl⟩ := hS a
      have hr : eS.symm (algebraMap R S r) = Ideal.Quotient.mk I r := by
        apply eS.injective
        rw [AlgEquiv.apply_symm_apply]
        exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := Algebra.ofId R S) hS r).symm
      change f.liftBaseChange S (algebraMap R S r ⊗ₜ[R] x) =
        f.quotKerEquivOfSurjective hf
          (Submodule.quotEquivOfEq _ _ hker.symm
            (TensorProduct.quotTensorEquivQuotSMul M I
              (eS.symm (algebraMap R S r) ⊗ₜ[R] x)))
      rw [hr, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
        liftBaseChange_tmul, map_smul, algebraMap_smul]
  have hfun : (f.liftBaseChange S : _ → _) = (e : _ → _) := funext he
  change Function.Bijective (f.liftBaseChange S : _ → _)
  rw [hfun]
  exact e.bijective

end LinearMap

namespace TateModule

attribute [local instance] coefficientModule completedCoefficientModule
  completedCoefficientScalarTower

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- The actual principal Tate projection is semilinear for the canonical completed residue map. -/
def completedPrincipalProjection (a b : R) (hab : a * b = (p : R)) :
    integral p A →ₛₗ[completedPrincipalResidue p R a b hab] Submodule.torsionBy R A a where
  __ := (principalProjection p R A a b hab).toAddMonoidHom
  map_smul' := principalProjection_completed_smul p R A a b hab

/-- Reducing the actual integral Tate module over completed coefficients gives actual principal torsion. -/
def completedPrincipalResidualEquiv (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    letI := (completedPrincipalResidue p R a b hab).toAlgebra
    ((R ⧸ Ideal.span {a}) ⊗[AdicCompletion (Ideal.span {(p : R)}) R] integral p A) ≃ₗ[R ⧸ Ideal.span {a}]
      Submodule.torsionBy R A a := by
  let S := AdicCompletion (Ideal.span {(p : R)}) R
  let k := R ⧸ Ideal.span {a}
  letI : Algebra S k := (completedPrincipalResidue p R a b hab).toAlgebra
  letI : Module S (Submodule.torsionBy R A a) :=
    Module.compHom _ (completedPrincipalResidue p R a b hab)
  letI : IsScalarTower S k (Submodule.torsionBy R A a) :=
    ⟨fun c d x => mul_smul (completedPrincipalResidue p R a b hab c) d x⟩
  let f : integral p A →ₗ[S] Submodule.torsionBy R A a :=
    { __ := (principalProjection p R A a b hab).toAddMonoidHom
      map_smul' := principalProjection_completed_smul p R A a b hab }
  have hf : Function.Surjective f := principalProjection_surjective p R A a b hab hpdiv
  have hker : f.ker = RingHom.ker (algebraMap S k) • (⊤ : Submodule S (integral p A)) := by
    ext x
    rw [LinearMap.mem_ker]
    change principalProjection p R A a b hab x = 0 ↔
      x ∈ RingHom.ker (completedPrincipalResidue p R a b hab) • (⊤ : Submodule S (integral p A))
    rw [principalProjection_eq_zero_iff p R A a b hab hpdiv, ker_completedPrincipalResidue,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and, completedCoefficient_smul_algebraMap]
  exact LinearEquiv.ofBijective (f.liftBaseChange k)
    (f.bijective_liftBaseChange_of_ker (completedPrincipalResidue_surjective p R a b hab) hf hker)

@[simp]
theorem completedPrincipalResidualEquiv_tmul (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x))
    (c : R ⧸ Ideal.span {a}) (x : integral p A) :
    letI := (completedPrincipalResidue p R a b hab).toAlgebra
    completedPrincipalResidualEquiv p R A a b hab hpdiv
      (c ⊗ₜ[AdicCompletion (Ideal.span {(p : R)}) R] x) =
        c • principalProjection p R A a b hab x := rfl

/-- At a principal maximal ideal, actual torsion dimension equals the completed Tate rank. -/
theorem principalTorsion_finrank
    [Module.Free (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A)]
    (a b : R) (hab : a * b = (p : R)) [(Ideal.span {a}).IsMaximal]
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    Module.finrank (R ⧸ Ideal.span {a}) (Submodule.torsionBy R A a) =
      Module.finrank (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A) := by
  let := (completedPrincipalResidue p R a b hab).toAlgebra
  have : Nontrivial (AdicCompletion (Ideal.span {(p : R)}) R) :=
    ⟨⟨0, 1, fun h => (zero_ne_one : (0 : R ⧸ Ideal.span {a}) ≠ 1) (by
      simpa using congrArg (completedPrincipalResidue p R a b hab) h)⟩⟩
  rw [← (completedPrincipalResidualEquiv p R A a b hab hpdiv).finrank_eq,
    Module.finrank_baseChange]

end TateModule
