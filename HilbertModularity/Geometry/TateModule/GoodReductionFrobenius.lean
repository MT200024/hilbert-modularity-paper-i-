/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.TateModule.GoodReduction
public import HilbertModularity.Geometry.Etale.FiniteFieldGenusTwoFrobenius

/-! # Frobenius on the two fibres of a good abelian model

The standard prime-to-residue-characteristic specialization of the Tate module
identifies geometric Galois Frobenius on the generic cohomological dual with
geometric Galois Frobenius on the special dual. This comparison is deliberately
independent of the level-five equation, its point counts and its RM labels.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace AlgebraicGeometry.GroupScheme


attribute [local instance] Ideal.Quotient.field

/- Standard smooth-proper good-reduction comparison of full dual Tate
Frobenius polynomials. The basis is transported by the prime-to-characteristic
specialization equivalence, and both actions use geometric Galois Frobenius.
This is the Abelian-variety specialization of [MilneAV, Chapter IV, Theorem
3.5 and paragraph after Corollary 3.6, printed pp. 141–142]. The latter
paragraph identifies the reduction isomorphism with the decomposition-to-residue
Galois map and the canonical residue generator with the q-power endomorphism
of [MilneAV, Chapter II, §1, printed p. 75]. Inverting both Galois generators
and taking contragredient duals gives this comparison without a Tate twist.
Transporting the given special basis supplies the generic basis. No numerical
polynomial, coefficient label or comparison character is asserted. -/
/-- **Literature input.** The same good-reduction specialization gives both
transported-basis Frobenius polynomials and a linear equivalence intertwining
the full dual Tate Frobenius operators. These are two API consequences of the
single specialization isomorphism in [MilneAV, IV Theorem 3.5 and paragraph
after Corollary 3.6, pp.141–142; II §1, p.75]. They retain the same abelian
model, residue field, auxiliary prime and geometric Frobenius conventions.
The joint input keeps the existing basis interface available while exposing
the operator comparison needed by the selected-model application. No numeric
polynomial, coefficient label or manuscript comparison character is admitted. -/
theorem goodReduction_dualTateFrobenius_comparison
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : 𝓞 K) ∉ P.asIdeal)
    [Fintype (𝓞 K ⧸ P.asIdeal)]
    : (∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bₛ : Module.Basis ι ℚ_[ℓ]
      (Module.Dual ℚ_[ℓ]
        (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X ℓ))),
    ∃ bₙ : Module.Basis ι ℚ_[ℓ]
        (Module.Dual ℚ_[ℓ] (rationalTate K (localGenericFiber K P B).X ℓ)),
      (LinearMap.toMatrix bₙ bₙ
        ((tateRepresentation K (localGenericFiber K P B).X ℓ).dual
          (NumberField.geometricFrobenius K (AlgebraicClosure K) P.asIdeal Q))).charpolyRev =
        (LinearMap.toMatrix bₛ bₛ
          ((tateRepresentation (𝓞 K ⧸ P.asIdeal)
            (localSpecialFiber K P B).X ℓ).dual
            (Hyperelliptic.finiteFieldGeometricFrobenius (𝓞 K ⧸ P.asIdeal)))).charpolyRev) ∧
      ∃ e : Module.Dual ℚ_[ℓ]
        (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X ℓ) ≃ₗ[ℚ_[ℓ]]
        Module.Dual ℚ_[ℓ] (rationalTate K (localGenericFiber K P B).X ℓ),
      e.conj ((tateRepresentation (𝓞 K ⧸ P.asIdeal)
        (localSpecialFiber K P B).X ℓ).dual
        (Hyperelliptic.finiteFieldGeometricFrobenius (𝓞 K ⧸ P.asIdeal))) =
        (tateRepresentation K (localGenericFiber K P B).X ℓ).dual
          (NumberField.geometricFrobenius K (AlgebraicClosure K) P.asIdeal Q) := by
  sorry

/-- The full linear Frobenius specialization supplied by the single named
good-reduction comparison. -/
theorem exists_goodReduction_dualTateFrobenius_equiv
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : 𝓞 K) ∉ P.asIdeal)
    [Fintype (𝓞 K ⧸ P.asIdeal)]
    : ∃ e : Module.Dual ℚ_[ℓ]
        (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X ℓ) ≃ₗ[ℚ_[ℓ]]
        Module.Dual ℚ_[ℓ] (rationalTate K (localGenericFiber K P B).X ℓ),
      e.conj ((tateRepresentation (𝓞 K ⧸ P.asIdeal)
        (localSpecialFiber K P B).X ℓ).dual
        (Hyperelliptic.finiteFieldGeometricFrobenius (𝓞 K ⧸ P.asIdeal))) =
        (tateRepresentation K (localGenericFiber K P B).X ℓ).dual
          (NumberField.geometricFrobenius K (AlgebraicClosure K) P.asIdeal Q) :=
  (goodReduction_dualTateFrobenius_comparison.{_, 0} K P B Q ℓ hℓ).2

/-- The transported-basis consequence of the single cited good-reduction
comparison; the source remains a named admission. -/
theorem exists_goodReduction_dualTateFrobenius_basis
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : 𝓞 K) ∉ P.asIdeal)
    [Fintype (𝓞 K ⧸ P.asIdeal)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bₛ : Module.Basis ι ℚ_[ℓ]
      (Module.Dual ℚ_[ℓ]
        (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X ℓ))) :
    ∃ bₙ : Module.Basis ι ℚ_[ℓ]
        (Module.Dual ℚ_[ℓ] (rationalTate K (localGenericFiber K P B).X ℓ)),
      (LinearMap.toMatrix bₙ bₙ
        ((tateRepresentation K (localGenericFiber K P B).X ℓ).dual
          (NumberField.geometricFrobenius K (AlgebraicClosure K) P.asIdeal Q))).charpolyRev =
        (LinearMap.toMatrix bₛ bₛ
          ((tateRepresentation (𝓞 K ⧸ P.asIdeal)
            (localSpecialFiber K P B).X ℓ).dual
            (Hyperelliptic.finiteFieldGeometricFrobenius (𝓞 K ⧸ P.asIdeal)))).charpolyRev :=
  (goodReduction_dualTateFrobenius_comparison K P B Q ℓ hℓ).1 bₛ

/-- A polynomial established on the actual special fibre is the polynomial
of the same good model's generic cohomological dual at the corresponding
geometric Frobenius. This is the direct application of the standard
specialization comparison above; `R` can be computed independently. -/
theorem exists_goodReduction_genericFrobeniusPolynomial_of_special
    (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K))
    (B : CommGrp (Over (Spec (CommRingCat.of (P.valuationSubringAtPrime K)))))
    [IsProper B.X.hom] [Smooth B.X.hom] [GeometricallyConnected B.X.hom]
    (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P.asIdeal]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : 𝓞 K) ∉ P.asIdeal)
    [Fintype (𝓞 K ⧸ P.asIdeal)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Polynomial ℚ_[ℓ])
    (hpoly : ∃ bₛ : Module.Basis ι ℚ_[ℓ]
      (Module.Dual ℚ_[ℓ]
        (rationalTate (𝓞 K ⧸ P.asIdeal) (localSpecialFiber K P B).X ℓ)),
      (LinearMap.toMatrix bₛ bₛ
        ((tateRepresentation (𝓞 K ⧸ P.asIdeal)
          (localSpecialFiber K P B).X ℓ).dual
          (Hyperelliptic.finiteFieldGeometricFrobenius (𝓞 K ⧸ P.asIdeal)))).charpolyRev = R) :
    ∃ bₙ : Module.Basis ι ℚ_[ℓ]
        (Module.Dual ℚ_[ℓ] (rationalTate K (localGenericFiber K P B).X ℓ)),
      (LinearMap.toMatrix bₙ bₙ
        ((tateRepresentation K (localGenericFiber K P B).X ℓ).dual
          (NumberField.geometricFrobenius K (AlgebraicClosure K) P.asIdeal Q))).charpolyRev =
        R := by
  obtain ⟨bₛ, hbₛ⟩ := hpoly
  obtain ⟨bₙ, hbₙ⟩ :=
    exists_goodReduction_dualTateFrobenius_basis K P B Q ℓ hℓ bₛ
  exact ⟨bₙ, hbₙ.trans hbₛ⟩

end AlgebraicGeometry.GroupScheme
