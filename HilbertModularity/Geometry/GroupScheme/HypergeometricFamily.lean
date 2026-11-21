/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.StandardInertiaRank

/-! # One chosen Darmon family for each conductor

The family and its integral real multiplication are chosen once. At prime
conductors at least five we use the explicit plus Jacobian from
[DarmonFibres, Section 3 Example 3]; otherwise we use Proposition 3.2.
Neither a coefficient prime nor an embedding label enters this choice. The coefficient ranks use the actual all-prime Tate
realization of [DarmonFibres, Proposition 3.4].
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct MatrixGroups Matrix
namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic
attribute [local irreducible] GroupScheme.geometricTensorTateAction

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)

/-- The plus-family inertia data realizes the identical integral base triple
used in Darmon's general existence theorem, at every realization prime. -/
theorem primePlusData_hasStandardInertiaRealization (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) :
    HasStandardInertiaRealization p (primePlusData p hp).family
      (primePlusData p hp).realMultiplication
      (primePlusData p hp).multiplication_finite
      (primePlusData p hp).multiplication_etale := by
  let T := (primePlusData p hp).tensorTateTriple
  unfold HasStandardInertiaRealization
  refine ⟨T.γ, T.c, ⟨T.inertia, T.normalization⟩, ?_⟩
  have h := T.realization
  unfold PrimePlusTensorTateRealization at h
  with_reducible exact h

/-- The chosen family with its Darmon existence properties. At prime conductors
at least five the witness is the plus Jacobian, retaining its fixed RM action. -/
@[irreducible] def darmonExistenceWitness :
    {D : Σ A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))),
        𝓞 (realCyclotomicField N) →+* End A //
      Function.Injective D.2 ∧ IsProper D.1.X.hom ∧
      SmoothOfRelativeDimension (Module.finrank ℚ (realCyclotomicField N)) D.1.X.hom ∧
      GeometricallyConnected D.1.X.hom ∧
      ∃ (hfinite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 D.1).hom.hom.hom.left)
        (hetale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 D.1).hom.hom.hom.left)
        (_hsurjective : ∀ n : ℕ, 0 < n → Surjective (n • 𝟙 D.1).hom.hom.hom.left),
      HasStandardInertiaRealization N D.1 D.2 hfinite hetale} :=
  if hp : N.Prime ∧ 5 ≤ N then
    letI : Fact N.Prime := ⟨hp.1⟩
    let D := primePlusData N hp.2
    ⟨⟨D.family, D.realMultiplication⟩,
      D.realMultiplication_injective, D.proper, D.smooth, D.geometricallyConnected,
      D.multiplication_finite, D.multiplication_etale, D.multiplication_surjective,
      primePlusData_hasStandardInertiaRealization N hp.2⟩
  else
    Classical.indefiniteDescription _ (exists_darmon_abelianScheme N hN)

/-- The family and its actual integral multiplication, selected together as dependent data.
The pair contains no assumed properties; those are obtained from the named existence inputs. -/
@[expose] def darmonFamilyWithRealMultiplication :
    Σ A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))),
      𝓞 (realCyclotomicField N) →+* End A :=
  (darmonExistenceWitness N hN).val

/-- The single abelian scheme chosen for the integral base triple at conductor `N`. -/
@[expose] def darmonFamily : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))) :=
  (darmonFamilyWithRealMultiplication N hN).1

/-- The integral real multiplication on that same chosen family. -/
@[expose] def darmonRealMultiplication : 𝓞 (realCyclotomicField N) →+* End (darmonFamily N hN) :=
  (darmonFamilyWithRealMultiplication N hN).2

/-- The chosen integral real multiplication is faithful. -/
theorem darmonRealMultiplication_injective : Function.Injective (darmonRealMultiplication N hN) :=
  (darmonExistenceWitness N hN).property.1

/-- The chosen family is proper over its parameter scheme. -/
instance darmonFamily_isProper : IsProper (darmonFamily N hN).X.hom :=
  (darmonExistenceWitness N hN).property.2.1

/-- The chosen family has the required smooth relative dimension. -/
instance darmonFamily_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (Module.finrank ℚ (realCyclotomicField N)) (darmonFamily N hN).X.hom :=
  (darmonExistenceWitness N hN).property.2.2.1

/-- The chosen family has geometrically connected fibres. -/
instance darmonFamily_geometricallyConnected : GeometricallyConnected (darmonFamily N hN).X.hom :=
  (darmonExistenceWitness N hN).property.2.2.2.1

/-- Positive multiplication on the chosen family is finite. -/
instance darmonFamily_multiplication_isFinite (n : ℕ) [NeZero n] :
    IsFinite (n • 𝟙 (darmonFamily N hN)).hom.hom.hom.left :=
  (darmonExistenceWitness N hN).property.2.2.2.2.choose n (NeZero.pos n)

/-- Positive multiplication on the chosen family is étale. -/
instance darmonFamily_multiplication_etale (n : ℕ) [NeZero n] :
    Etale (n • 𝟙 (darmonFamily N hN)).hom.hom.hom.left :=
  (darmonExistenceWitness N hN).property.2.2.2.2.choose_spec.choose n (NeZero.pos n)

/-- Positive multiplication on the chosen family is surjective. -/
instance darmonFamily_multiplication_surjective (n : ℕ) [NeZero n] :
    Surjective (n • 𝟙 (darmonFamily N hN)).hom.hom.hom.left :=
  (darmonExistenceWitness N hN).property.2.2.2.2.choose_spec.choose_spec.choose n (NeZero.pos n)

/-- The actual inertia realization belongs to the same chosen family and RM action.
This exposes the simultaneous basis supplied by [DarmonFibres, Propositions 3.2
and 3.4], without making a new choice of family at a coefficient prime. -/
theorem darmonFamily_inertia_realization :
    HasStandardInertiaRealization N (darmonFamily N hN) (darmonRealMultiplication N hN)
      (fun n hn => @darmonFamily_multiplication_isFinite N _ hN n ⟨Nat.ne_of_gt hn⟩)
      (fun n hn => @darmonFamily_multiplication_etale N _ hN n ⟨Nat.ne_of_gt hn⟩) := by
  exact (darmonExistenceWitness N hN).property.2.2.2.2.choose_spec.choose_spec.choose_spec

/-- At a prime conductor at least five the Darmon witness is the selected plus
family with exactly the same integral coefficient action. -/
theorem darmonFamilyWithRealMultiplication_eq_primePlus [Fact N.Prime] (hp : 5 ≤ N) :
    darmonFamilyWithRealMultiplication N hN =
      ⟨primePlusFamily N hp, primePlusRealMultiplication N hp⟩ := by
  have hh : N.Prime ∧ 5 ≤ N := ⟨Fact.out, hp⟩
  simp only [darmonFamilyWithRealMultiplication, darmonExistenceWitness, dite_eq_left hh]
  rfl

/-- The prime Darmon and plus families are a single chosen arithmetic family. -/
theorem darmonFamily_eq_primePlusFamily [Fact N.Prime] (hp : 5 ≤ N) :
    darmonFamily N hN = primePlusFamily N hp := by
  exact congrArg Sigma.fst (darmonFamilyWithRealMultiplication_eq_primePlus N hN hp)

/-- Each nonsingular fibre of the chosen prime Darmon family is the pointed
Jacobian of the manuscript's plus curve. The preceding equality of dependent
family/RM pairs retains the coefficient action over the real cyclotomic field. -/
def darmonPrimeRationalFiberJacobian [Fact N.Prime] (hp : 5 ≤ N)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    GroupScheme.PlusCurveJacobian (realCyclotomicField N) N
      (primePlusData N hp).p_odd ξ.val
      (GroupScheme.fiber (realCyclotomicField N) (darmonFamily N hN)
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ)) := by
  rw [darmonFamily_eq_primePlusFamily N hN hp]
  exact primePlusRationalFiberJacobian N hp ξ

-- Keep the chosen data abstract when applying its public properties.
attribute [irreducible] darmonFamilyWithRealMultiplication darmonFamily darmonRealMultiplication

/-- Each embedding-labelled generic Tate fibre of the chosen family has dimension two. -/
theorem finrank_darmonLabelledTateLocalSystem
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    Module.finrank L ((GroupScheme.labelledTateLocalSystem (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p L (realCyclotomicField N) (darmonRealMultiplication N hN) hL σ).obj
      (Scheme.etaleFiberPoint (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))) = 2 := by
  exact HasStandardInertiaRealization.finrank_labelledTateLocalSystem N
    (darmonFamily N hN) (darmonRealMultiplication N hN)
    (fun n hn => @darmonFamily_multiplication_isFinite N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (fun n hn => @darmonFamily_multiplication_etale N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (darmonFamily_inertia_realization N hN) p L hL σ

end HilbertModularity.Hypergeometric
