/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalCompatibleSystem
public import HilbertModularity.RepresentationTheory.Duality

/-! # Cohomological normalization of Hilbert automorphy

For a chosen family of actions attached to an algebraic parallel-weight-two
Hilbert eigenform, this module fixes the cohomological representation and its
covariant Tate dual. It records the duality dictionary used in
[TripathiGoswami, Remark 2.4]. The actions remain independently supplied;
the definition does not assert their existence.
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- The chosen cohomological Galois representation of a Hilbert eigenform at
one coefficient place. Its geometric-Frobenius normalization is inherited
from the independently supplied trace and determinant identities. -/
def EigenformCohomologicalActions.cohomologicalRepresentation
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E)) :
    Representation (w.adicCompletion E) (AbsoluteGalois F)
      (Fin 2 → w.adicCompletion E) :=
  D.action w

/-- The covariant Tate convention for the same chosen eigenform action is
the ordinary representation dual, with no Tate twist. -/
def EigenformCohomologicalActions.covariantRepresentation
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E)) :
    Representation (w.adicCompletion E) (AbsoluteGalois F)
      (Module.Dual (w.adicCompletion E) (Fin 2 → w.adicCompletion E)) :=
  (D.cohomologicalRepresentation w).dual

/-- The chosen cohomological action has the eigenform's independently defined
Hecke polynomial at geometric Frobenius, away from its bad primes and the
coefficient characteristic. -/
theorem EigenformCohomologicalActions.cohomologicalRepresentation_charpoly
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (D.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (D.cohomologicalRepresentation w
      (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
        (φ.heckePolynomial q hq).map (algebraMap E (w.adicCompletion E)) :=
  D.frobenius_charpoly w q hq P hP hp Q

/-- A covariant representation is automorphic through the chosen eigenform
exactly when its cohomological dual is equivalent to the chosen cohomological
action. This is the duality convention of [TripathiGoswami, Remark 2.4]. -/
theorem EigenformCohomologicalActions.covariantEquiv_iff_dualEquiv
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (w : HeightOneSpectrum (𝓞 E))
    (ρ : Representation (w.adicCompletion E) (AbsoluteGalois F)
      (Fin 2 → w.adicCompletion E)) :
    Nonempty (ρ.Equiv (D.covariantRepresentation w)) ↔
      Nonempty (ρ.dual.Equiv (D.cohomologicalRepresentation w)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨HilbertModularity.dualEquivOfEquivDual e⟩
  · rintro ⟨e⟩
    exact ⟨(HilbertModularity.representationBidualEquiv ρ).trans
      (HilbertModularity.representationDualEquiv e)⟩

end HilbertModularity.HilbertModularForms
