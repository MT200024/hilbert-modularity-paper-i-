/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.PrimeCompletion
public import HilbertModularity.RepresentationTheory.CoefficientTorsion

/-! # Actual torsion and the RM-prime Tate representation

The canonical cofinal coefficient-completion equivalence extends the actual
Galois action to the RM-prime completion. Its reduction acts on the actual
principal torsion subgroup; see [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

attribute [local instance] coefficientModule completedCoefficientModule

variable (p : ℕ) [Fact p.Prime] (R G A : Type*) [CommRing R] [Monoid G]
  [AddCommGroup A] [Module R A] [DistribMulAction G A] [SMulCommClass G R A]

/-- The actual Tate action over the actual RM-prime coefficient completion. -/
def coefficientPrimeRepresentation (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) :
    letI := coefficientPrimeModule p R A J e he hJ
    Representation (AdicCompletion J R) G (integral p A) := by
  letI := coefficientPrimeModule p R A J e he hJ
  refine
    { toFun := fun g =>
        { toFun := completedCoefficientRepresentation p R G A g
          map_add' := map_add _
          map_smul' := fun c x =>
            (completedCoefficientRepresentation p R G A g).map_smul
              ((coefficientPrimeRingEquiv p R J e he hJ).symm c) x }
      map_one' := ?_
      map_mul' := ?_ }
  · apply LinearMap.ext
    intro x
    exact congrArg (fun f => f x) (map_one (completedCoefficientRepresentation p R G A))
  · intro g h
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f x) (map_mul (completedCoefficientRepresentation p R G A) g h)

@[simp]
theorem coefficientPrimeRepresentation_apply (J : Ideal R) (e : ℕ) (he : 0 < e)
    (hJ : J ^ e = Ideal.span {(p : R)}) (g : G) (x : integral p A) :
    letI := coefficientPrimeModule p R A J e he hJ
    coefficientPrimeRepresentation p R G A J e he hJ g x = representation p G A g x :=
  completedCoefficientRepresentation_apply p R G A g x

/-- Reduction of the actual RM-prime Tate action is the actual principal torsion action. -/
def coefficientPrimeResidualRepresentationEquiv (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
    ((coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ).baseChange
      (R ⧸ Ideal.span {a})).Equiv (principalTorsionRepresentation R G A a) := by
  letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  letI := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
  refine .mk (coefficientPrimeResidualEquiv p R A a b hab e he hJ hpdiv) ?_
  intro g
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
  | tmul c x =>
    change coefficientPrimeResidualEquiv p R A a b hab e he hJ hpdiv
      (c ⊗ₜ[AdicCompletion (Ideal.span {a}) R]
        coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ g x) =
      principalTorsionRepresentation R G A a g
        (coefficientPrimeResidualEquiv p R A a b hab e he hJ hpdiv
          (c ⊗ₜ[AdicCompletion (Ideal.span {a}) R] x))
    rw [coefficientPrimeResidualEquiv_tmul, coefficientPrimeResidualEquiv_tmul, map_smul]
    congr 1
    apply Subtype.ext
    change b • (projection p A 1
        (coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ g x) : A) =
      g • (b • (projection p A 1 x : A))
    rw [coefficientPrimeRepresentation_apply, representation_projection]
    exact (smul_comm g b _).symm

/-- The determinant on actual principal torsion is the residue of the actual RM-prime lattice determinant. -/
theorem det_coefficientPrimeResidualRepresentation (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (hpdiv : Function.Surjective (fun x : A => p • x)) (g : G) :
    letI := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
    ∀ [Module.Free (AdicCompletion (Ideal.span {a}) R) (integral p A)]
      [Module.Finite (AdicCompletion (Ideal.span {a}) R) (integral p A)],
    LinearMap.det (principalTorsionRepresentation R G A a g) =
      AdicCompletion.evalOneₐ (Ideal.span {a})
        (LinearMap.det (coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ g)) := by
  let := coefficientPrimeModule p R A (Ideal.span {a}) e he hJ
  intro _ _
  let := (AdicCompletion.evalOneₐ (Ideal.span {a})).toRingHom.toAlgebra
  let E := coefficientPrimeResidualRepresentationEquiv p R G A a b hab e he hJ hpdiv
  have hE : E.toLinearEquiv.toLinearMap ∘ₗ
      ((coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ).baseChange
        (R ⧸ Ideal.span {a})) g ∘ₗ E.toLinearEquiv.symm.toLinearMap =
      principalTorsionRepresentation R G A a g := by
    apply LinearMap.ext
    intro x
    change E (((coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ).baseChange
      (R ⧸ Ideal.span {a})) g (E.symm x)) = principalTorsionRepresentation R G A a g x
    simpa using E.toIntertwiningMap.isIntertwining _ _ g (E.symm x)
  rw [← hE, LinearMap.det_conj]
  exact LinearMap.det_baseChange
    (coefficientPrimeRepresentation p R G A (Ideal.span {a}) e he hJ g)

end TateModule
