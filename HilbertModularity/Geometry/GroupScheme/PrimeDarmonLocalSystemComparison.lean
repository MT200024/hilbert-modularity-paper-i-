/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricFactors
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricFactors

/-! # Equality of the chosen prime Tate local systems

The chosen Darmon family and its RM action agree with the selected plus
family as a dependent pair. Comparing the local systems first avoids
reconstructing their dependent arithmetic fibre carriers.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

/-- Equal group-scheme/RM pairs give equal coefficient-labelled local systems. -/
theorem labelledTateFamilyAtPrime_eq_of_familyEq
    (K : Type) [Field K] {S : Scheme}
    (N ℓ m : ℕ) [NeZero N] [Fact ℓ.Prime] (hm : m.Coprime N)
    (D D' : Σ A : CommGrp (Over S), 𝓞 (realCyclotomicField N) →+* End A)
    [∀ n : ℕ, IsFinite (ℓ ^ n • 𝟙 D.1).hom.hom.hom.left]
    [∀ n : ℕ, Etale (ℓ ^ n • 𝟙 D.1).hom.hom.hom.left]
    [Surjective (ℓ • 𝟙 D.1).hom.hom.hom.left]
    [∀ n : ℕ, IsFinite (ℓ ^ n • 𝟙 D'.1).hom.hom.hom.left]
    [∀ n : ℕ, Etale (ℓ ^ n • 𝟙 D'.1).hom.hom.hom.left]
    [Surjective (ℓ • 𝟙 D'.1).hom.hom.hom.left]
    (h : D = D')
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})]
    (L : Type) [NontriviallyNormedField L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[ℓ] L] [IsScalarTower ℚ_[ℓ] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L] :
    labelledTateFamilyAtPrime K D.1 ℓ N m hm E hE w L D.2 =
      labelledTateFamilyAtPrime K D'.1 ℓ N m hm E hE w L D'.2 := by
  subst D'
  rfl

/-- At prime conductor the chosen Darmon and selected plus Tate local
systems are identical, with the same exponent and coefficient completion. -/
theorem darmonLabelledTateFamily_eq_primePlus
    (p : ℕ) [Fact p.Prime] (h3 : 3 ≤ p) (hp : 5 ≤ p)
    (K : Type) [Field K] (m : ℕ) (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L] :
    darmonLabelledTateFamily K p h3 p m hm E hE w L =
      primePlusLabelledTateFamily p hp K m hm E hE w L := by
  rw [primePlusLabelledTateFamily_eq_labelled]
  have he : (⟨darmonFamily p h3, darmonRealMultiplication p h3⟩ :
      Σ A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p))),
        𝓞 (realCyclotomicField p) →+* End A) =
      darmonFamilyWithRealMultiplication p h3 := by
    unfold darmonFamily darmonRealMultiplication
    exact Sigma.eta _
  exact labelledTateFamilyAtPrime_eq_of_familyEq K p p m hm
    ⟨darmonFamily p h3, darmonRealMultiplication p h3⟩
    ⟨primePlusFamily p hp, primePlusRealMultiplication p hp⟩
    (he.trans (darmonFamilyWithRealMultiplication_eq_primePlus p h3 hp)) E hE w L

/-- Equal local systems have canonically equivalent arithmetic fibres. -/
def arithmeticLocalSystemEquivOfEq
    (K : Type) [Field K] {S : Scheme}
    (L : Type) [Field L] [TopologicalSpace L]
    (F F' : Scheme.EtaleLocalSystem K S L) (h : F = F')
    (x : Spec (CommRingCat.of K) ⟶ S) :
    (F.arithmeticRepresentation x).Equiv (F'.arithmeticRepresentation x) := by
  subst F'
  exact Representation.Equiv.refl _

/-- The actual chosen Darmon arithmetic fibre identifies with the native
Tate factor of the selected plus Jacobian, retaining its coefficient label. -/
def darmonPrimeArithmeticTateEquivPlus
    (p : ℕ) [Fact p.Prime] (h3 : 3 ≤ p) (hp : 5 ≤ p)
    (K : Type) [Field K] [CharZero K] (m : ℕ) (hm : m.Coprime p)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField p) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L]
    [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[p] L]
    (x : Spec (CommRingCat.of K) ⟶ ProjectiveLine.punctured (realCyclotomicField p)) :=
  (arithmeticLocalSystemEquivOfEq K L
    (darmonLabelledTateFamily K p h3 p m hm E hE w L)
    (primePlusLabelledTateFamily p hp K m hm E hE w L)
    (darmonLabelledTateFamily_eq_primePlus p h3 hp K m hm E hE w L) x).trans
      (primePlusLabelledTateFamily_arithmeticEquivEndomorphism p hp K m hm E hE w L x)

end HilbertModularity.Hypergeometric
