/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CompletedReduction
public import HilbertModularity.RepresentationTheory.TateModule
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Equivariant principal coefficient reduction

A group action commuting with a coefficient ring acts on its actual torsion
subgroups over the quotient coefficient ring. Principal reduction identifies
this action with scalar reduction of the integral Tate action, as required
for the RM-prime torsion comparison in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

attribute [local instance] coefficientModule completedCoefficientModule
  completedCoefficientScalarTower

variable (p : ℕ) [Fact p.Prime] (R G A : Type*) [CommRing R] [Monoid G]
  [AddCommGroup A] [Module R A] [DistribMulAction G A] [SMulCommClass G R A]

/-- The actual integral Tate action is linear for every commuting coefficient action. -/
def coefficientRepresentation : Representation R G (integral p A) where
  toFun g :=
    { __ := (representation p G A g).toAddMonoidHom
      map_smul' r x := by
        apply Subtype.ext
        funext n
        apply Subtype.ext
        exact smul_comm g r (x.val n : A) }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (map_one (representation p G A)) x
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (map_mul (representation p G A) g h) x

@[simp]
theorem coefficientRepresentation_apply (g : G) (x : integral p A) :
    coefficientRepresentation p R G A g x = representation p G A g x := rfl

omit [Fact p.Prime] in
/-- The action on the actual subgroup killed by `a`, over its quotient coefficient ring. -/
def principalTorsionRepresentation (a : R) :
    Representation (R ⧸ Ideal.span {a}) G (Submodule.torsionBy R A a) where
  toFun g :=
    { toFun x := ⟨g • (x : A), by
        change a • (g • (x : A)) = 0
        rw [← smul_comm g a, show a • (x : A) = 0 from x.property, smul_zero]⟩
      map_add' x y := Subtype.ext (smul_add g _ _)
      map_smul' c x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        apply Subtype.ext
        exact smul_comm g r (x : A) }
  map_one' := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (one_smul G (x : A))
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (mul_smul g h (x : A))

omit [Fact p.Prime] in
@[simp]
theorem principalTorsionRepresentation_apply (a : R) (g : G)
    (x : Submodule.torsionBy R A a) :
    (principalTorsionRepresentation R G A a g x : A) = g • (x : A) := rfl

/-- Principal scalar reduction of the actual Tate action is the actual coefficient-torsion action. -/
def principalResidualRepresentationEquiv (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    ((coefficientRepresentation p R G A).baseChange (R ⧸ Ideal.span {a})).Equiv
      (principalTorsionRepresentation R G A a) :=
  .mk (principalResidualEquiv p R A a b hab hpdiv) (by
    intro g
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    | tmul c x =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      change principalResidualEquiv p R A a b hab hpdiv
        (Ideal.Quotient.mk (Ideal.span {a}) r ⊗ₜ[R] coefficientRepresentation p R G A g x) =
          principalTorsionRepresentation R G A a g
            (principalResidualEquiv p R A a b hab hpdiv
              (Ideal.Quotient.mk (Ideal.span {a}) r ⊗ₜ[R] x))
      rw [principalResidualEquiv_mk_tmul, principalResidualEquiv_mk_tmul]
      apply Subtype.ext
      change r • (b • (g • (projection p A 1 x : A))) =
        g • (r • (b • (projection p A 1 x : A)))
      rw [smul_comm g r, smul_comm g b])

@[simp]
theorem principalResidualRepresentationEquiv_mk_tmul (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) (r : R) (x : integral p A) :
    principalResidualRepresentationEquiv p R G A a b hab hpdiv
      (Ideal.Quotient.mk (Ideal.span {a}) r ⊗ₜ[R] x) =
        r • principalProjection p R A a b hab x :=
  principalResidualEquiv_mk_tmul p R A a b hab hpdiv r x

/-- The same actual Tate action is linear over the constructed completed coefficient ring. -/
def completedCoefficientRepresentation :
    Representation (AdicCompletion (Ideal.span {(p : R)}) R) G (integral p A) where
  toFun g := completedCoefficientLinearMap p R A (coefficientRepresentation p R G A g)
  map_one' := by
    apply LinearMap.ext
    intro x
    simp only [completedCoefficientLinearMap_apply, map_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp only [completedCoefficientLinearMap_apply, map_mul, Module.End.mul_apply]

@[simp]
theorem completedCoefficientRepresentation_apply (g : G) (x : integral p A) :
    completedCoefficientRepresentation p R G A g x = representation p G A g x :=
  completedCoefficientLinearMap_apply p R A (coefficientRepresentation p R G A g) x

/-- Completed integral scalar reduction intertwines with the actual principal coefficient-torsion action. -/
def completedPrincipalResidualRepresentationEquiv (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    letI := (completedPrincipalResidue p R a b hab).toAlgebra
    ((completedCoefficientRepresentation p R G A).baseChange (R ⧸ Ideal.span {a})).Equiv
      (principalTorsionRepresentation R G A a) := by
  letI := (completedPrincipalResidue p R a b hab).toAlgebra
  refine .mk (completedPrincipalResidualEquiv p R A a b hab hpdiv) ?_
  intro g
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
  | tmul c x =>
    change completedPrincipalResidualEquiv p R A a b hab hpdiv
      (c ⊗ₜ[AdicCompletion (Ideal.span {(p : R)}) R] completedCoefficientRepresentation p R G A g x) =
        principalTorsionRepresentation R G A a g
          (completedPrincipalResidualEquiv p R A a b hab hpdiv
            (c ⊗ₜ[AdicCompletion (Ideal.span {(p : R)}) R] x))
    rw [completedPrincipalResidualEquiv_tmul, completedPrincipalResidualEquiv_tmul, map_smul]
    congr 1
    apply Subtype.ext
    change b • (projection p A 1 (completedCoefficientRepresentation p R G A g x) : A) =
      g • (b • (projection p A 1 x : A))
    rw [completedCoefficientRepresentation_apply, representation_projection]
    exact (smul_comm g b _).symm

section Determinant

variable [Module.Free (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A)]
  [Module.Finite (AdicCompletion (Ideal.span {(p : R)}) R) (integral p A)]

/-- The actual coefficient-torsion determinant is the residue of the completed integral determinant. -/
theorem det_principalTorsionRepresentation (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) (g : G) :
    LinearMap.det (principalTorsionRepresentation R G A a g) =
      completedPrincipalResidue p R a b hab
        (LinearMap.det (completedCoefficientRepresentation p R G A g)) := by
  let := (completedPrincipalResidue p R a b hab).toAlgebra
  let e := completedPrincipalResidualRepresentationEquiv p R G A a b hab hpdiv
  have he : e.toLinearEquiv.toLinearMap ∘ₗ
      ((completedCoefficientRepresentation p R G A).baseChange (R ⧸ Ideal.span {a})) g ∘ₗ
        e.toLinearEquiv.symm.toLinearMap = principalTorsionRepresentation R G A a g := by
    apply LinearMap.ext
    intro x
    change e (((completedCoefficientRepresentation p R G A).baseChange
      (R ⧸ Ideal.span {a})) g (e.symm x)) = principalTorsionRepresentation R G A a g x
    simpa using e.toIntertwiningMap.isIntertwining _ _ g (e.symm x)
  rw [← he, LinearMap.det_conj]
  exact LinearMap.det_baseChange (completedCoefficientRepresentation p R G A g)

/-- An exact determinant after faithful coefficient extension specializes to actual coefficient torsion. -/
theorem det_principalTorsionRepresentation_eq_of_baseChange
    (L : Type*) [CommRing L] [Algebra (AdicCompletion (Ideal.span {(p : R)}) R) L]
    (hL : Function.Injective (algebraMap (AdicCompletion (Ideal.span {(p : R)}) R) L))
    (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) (g : G)
    (d : AdicCompletion (Ideal.span {(p : R)}) R)
    (hd : LinearMap.det ((completedCoefficientRepresentation p R G A).baseChange L g) =
      algebraMap (AdicCompletion (Ideal.span {(p : R)}) R) L d) :
    LinearMap.det (principalTorsionRepresentation R G A a g) =
      completedPrincipalResidue p R a b hab d := by
  rw [det_principalTorsionRepresentation p R G A a b hab hpdiv]
  congr 1
  apply hL
  exact (LinearMap.det_baseChange (completedCoefficientRepresentation p R G A g)).symm.trans hd

end Determinant

end TateModule
