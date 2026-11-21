/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.FiniteGeneration
public import HilbertModularity.RepresentationTheory.CoefficientTorsion

/-! # Actual coefficient torsion of commutative group schemes

An integral coefficient action by endomorphisms over the ground field acts on
geometric points and commutes with Galois. If `a * b = p`, reduction of its
actual integral Tate module modulo `a` identifies equivariantly with the
geometric points killed by `a`. This uses finite-surjective multiplication
by `p`, rather than an assumed identification with a residual representation.
See [TripathiGoswami, RM torsion determinant].
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupScheme

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  (R : Type*) [CommRing R]
  [Module R (Points K (AlgebraicClosure K) A)]

/-- The actual geometric points killed by a principal coefficient. -/
abbrev coefficientTorsion (a : R) :=
  Submodule.torsionBy R (Points K (AlgebraicClosure K) A) a

variable
  (hφ : ∀ r, ∃ (f : A ⟶ A) (_ : IsMonHom f),
    Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r =
      pointsMap K (AlgebraicClosure K) f)

include hφ in
/-- Coefficients defined by ground-field endomorphisms commute with the actual Galois action. -/
theorem points_coefficient_galois_comm :
    SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) R
      (Points K (AlgebraicClosure K) A) where
  smul_comm g r x := by
    obtain ⟨f, hf, hr⟩ := hφ r
    change g • Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r x =
      Module.toAddMonoidEnd R (Points K (AlgebraicClosure K) A) r (g • x)
    rw [hr]
    exact (pointsMap_galois K (AlgebraicClosure K) f g x).symm

attribute [local instance] TateModule.coefficientModule
  TateModule.completedCoefficientModule TateModule.completedCoefficientScalarTower

/-- The integral geometric Tate action with its actual integral coefficient action. -/
def coefficientIntegralTateRepresentation (p : ℕ) [Fact p.Prime] :
    Representation R (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (integralTate K A p) := by
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.coefficientRepresentation p R _ (Points K (AlgebraicClosure K) A)

/-- The same geometric Tate action over the actual completed integral coefficient ring. -/
def completedCoefficientIntegralTateRepresentation (p : ℕ) [Fact p.Prime] :
    Representation (AdicCompletion (Ideal.span {(p : R)}) R)
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (integralTate K A p) := by
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.completedCoefficientRepresentation p R _ (Points K (AlgebraicClosure K) A)

/-- Galois acts on actual principal coefficient torsion over the quotient coefficient ring. -/
def coefficientTorsionRepresentation (a : R) :
    Representation (R ⧸ Ideal.span {a}) (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (coefficientTorsion K A R a) := by
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.principalTorsionRepresentation R _ (Points K (AlgebraicClosure K) A) a

@[simp]
theorem coefficientTorsionRepresentation_apply (a : R)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : coefficientTorsion K A R a) :
    (coefficientTorsionRepresentation K A R hφ a g x : Points K (AlgebraicClosure K) A) =
      g • (x : Points K (AlgebraicClosure K) A) := rfl

variable (p : ℕ) [Fact p.Prime]
  [IsFinite (multiplicationMap K A p).left] [Surjective (multiplicationMap K A p).left]

/-- Actual finite-surjective multiplication supplies the principal RM torsion comparison. -/
def coefficientResidualIntegralTateEquiv (a b : R) (hab : a * b = (p : R)) :
    ((coefficientIntegralTateRepresentation K A R hφ p).baseChange
      (R ⧸ Ideal.span {a})).Equiv (coefficientTorsionRepresentation K A R hφ a) := by
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.principalResidualRepresentationEquiv p R _ (Points K (AlgebraicClosure K) A)
    a b hab (points_nsmul_surjective K A p)

@[simp]
theorem coefficientResidualIntegralTateEquiv_mk_tmul (a b : R) (hab : a * b = (p : R))
    (r : R) (x : integralTate K A p) :
    (coefficientResidualIntegralTateEquiv K A R hφ p a b hab
      (Ideal.Quotient.mk (Ideal.span {a}) r ⊗ₜ[R] x) : Points K (AlgebraicClosure K) A) =
        r • (b • (TateModule.projection p (Points K (AlgebraicClosure K) A) 1 x :
          Points K (AlgebraicClosure K) A)) := by
  have := points_coefficient_galois_comm K A R hφ
  exact congrArg Subtype.val (TateModule.principalResidualRepresentationEquiv_mk_tmul
    p R _ (Points K (AlgebraicClosure K) A) a b hab (points_nsmul_surjective K A p) r x)

omit [Fact p.Prime] [Surjective (multiplicationMap K A p).left] in
/-- Finite multiplication makes the actual principal coefficient-torsion group finite. -/
theorem finite_coefficientTorsion (a b : R) (hab : a * b = (p : R)) :
    Finite (coefficientTorsion K A R a) := by
  let i : coefficientTorsion K A R a → pTorsion K A p := fun x => ⟨x.val, by
    rw [AddSubgroup.torsionBy.nsmul_iff, pow_one, ← Nat.cast_smul_eq_nsmul R,
      ← hab, mul_comm a b, mul_smul, show a • x.val = 0 from x.property, smul_zero]⟩
  apply Finite.of_injective i
  intro x y h
  exact Subtype.ext (congrArg (fun z : pTorsion K A p => z.val) h)

omit [Fact p.Prime] [IsFinite (multiplicationMap K A p).left]
  [Surjective (multiplicationMap K A p).left] in
/-- The actual principal coefficient-torsion action has continuous orbit maps. -/
theorem continuous_coefficientTorsionRepresentation
    [IsSeparated A.hom] [LocallyOfFiniteType A.hom]
    (a : R) (x : coefficientTorsion K A R a) :
    Continuous (fun g => coefficientTorsionRepresentation K A R hφ a g x) :=
  Continuous.subtype_mk (continuous_id.smul continuous_const) _

/-- Reduction of the completed integral RM action gives the actual geometric RM torsion action. -/
def completedCoefficientResidualIntegralTateEquiv (a b : R) (hab : a * b = (p : R)) :
    letI := (TateModule.completedPrincipalResidue p R a b hab).toAlgebra
    ((completedCoefficientIntegralTateRepresentation K A R hφ p).baseChange
      (R ⧸ Ideal.span {a})).Equiv (coefficientTorsionRepresentation K A R hφ a) := by
  letI := (TateModule.completedPrincipalResidue p R a b hab).toAlgebra
  haveI := points_coefficient_galois_comm K A R hφ
  exact TateModule.completedPrincipalResidualRepresentationEquiv p R _
    (Points K (AlgebraicClosure K) A) a b hab (points_nsmul_surjective K A p)

variable [Module.Free (AdicCompletion (Ideal.span {(p : R)}) R) (integralTate K A p)]
  [Module.Finite (AdicCompletion (Ideal.span {(p : R)}) R) (integralTate K A p)]

/-- The determinant on actual geometric coefficient torsion is the residue of its completed Tate determinant. -/
theorem det_coefficientTorsionRepresentation (a b : R) (hab : a * b = (p : R))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    LinearMap.det (coefficientTorsionRepresentation K A R hφ a g) =
      TateModule.completedPrincipalResidue p R a b hab
        (LinearMap.det (completedCoefficientIntegralTateRepresentation K A R hφ p g)) := by
  have := points_coefficient_galois_comm K A R hφ
  exact TateModule.det_principalTorsionRepresentation p R _
    (Points K (AlgebraicClosure K) A) a b hab (points_nsmul_surjective K A p) g

omit [Module.Finite (AdicCompletion (Ideal.span {(p : R)}) R) (integralTate K A p)] in
/-- Actual residual RM dimension is the rank of the completed integral Tate module. -/
theorem coefficientTorsion_finrank (a b : R) (hab : a * b = (p : R))
    [(Ideal.span {a}).IsMaximal] :
    Module.finrank (R ⧸ Ideal.span {a}) (coefficientTorsion K A R a) =
      Module.finrank (AdicCompletion (Ideal.span {(p : R)}) R) (integralTate K A p) :=
  TateModule.principalTorsion_finrank p R (Points K (AlgebraicClosure K) A)
    a b hab (points_nsmul_surjective K A p)

end AlgebraicGeometry.GroupScheme
