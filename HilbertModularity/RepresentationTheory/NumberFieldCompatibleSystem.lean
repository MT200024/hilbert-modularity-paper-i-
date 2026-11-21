/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CompatiblePolynomials
public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisRealization

/-! # Compatible systems over the completions of one number field

The coefficient embedding at a finite place is the canonical map into that
place's completion. The common polynomial is algebraic before this embedding;
the exceptional geometric primes are independent of the coefficient place.
Geometric Frobenius is used throughout, as in [TripathiGoswami,
Lemma “Promotion from one realization”].
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

/-- A semisimple rank-two system on the actual coefficient-field completions.
The separate residue-characteristic data records which geometric primes must
be removed at each coefficient place. -/
structure NumberFieldCompatibleSystem (F E : Type*) [Field F] [NumberField F]
    [Field E] [NumberField E] where
  residueCharacteristic : HeightOneSpectrum (𝓞 E) → ℕ
  residueCharacteristic_prime : ∀ w, (residueCharacteristic w).Prime
  coefficientPrime : ∀ w : HeightOneSpectrum (𝓞 E),
    w.asIdeal.LiesOver (Ideal.span {(residueCharacteristic w : ℤ)})
  action : ∀ w : HeightOneSpectrum (𝓞 E),
    Representation (w.adicCompletion E) (HilbertModularForms.AbsoluteGalois F)
      (Fin 2 → w.adicCompletion E)
  continuous : ∀ w (i j : Fin 2),
    Continuous (fun g : HilbertModularForms.AbsoluteGalois F =>
      action w g (Pi.single j 1) i)
  semisimple : ∀ w, (action w).IsSemisimpleRepresentation
  bad : Set (HeightOneSpectrum (𝓞 F))
  bad_finite : bad.Finite
  polynomial : HeightOneSpectrum (𝓞 F) → Polynomial E
  unramified : ∀ w q, q ∉ bad →
    ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
    (residueCharacteristic w : 𝓞 F) ∉ P →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : HilbertModularForms.AbsoluteGalois F,
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → action w g = 1
  frobenius_charpoly : ∀ w q, q ∉ bad →
    ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
    (residueCharacteristic w : 𝓞 F) ∉ P →
    ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
      (action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
        (polynomial q).map (algebraMap E (w.adicCompletion E))

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- The chosen identification at one completion identifies the two algebraic
Frobenius polynomials at each prime good for that completion. -/
theorem NumberFieldCompatibleSystem.polynomial_eq_scaleRoots_of_onePlace
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : HilbertModularForms.AbsoluteGalois F →* Eˣ)
    (w₀ : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter
        ((Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (σ.action w₀)))
    (q : HeightOneSpectrum (𝓞 F)) (hρ : q ∉ ρ.bad) (hσ : q ∉ σ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hpρ : (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (hpσ : (σ.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    ρ.polynomial q = (σ.polynomial q).scaleRoots
      (χ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E) := by
  have : Infinite (w₀.adicCompletion E) :=
    Infinite.of_injective (algebraMap E (w₀.adicCompletion E))
      (algebraMap E (w₀.adicCompletion E)).injective
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  exact Representation.common_polynomial_eq_scaleRoots
    (algebraMap E (w₀.adicCompletion E)) (ρ.action w₀) (σ.action w₀)
    ((Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom).comp χ)
    e g (ρ.polynomial q) (σ.polynomial q) (χ g)
    (ρ.frobenius_charpoly w₀ q hρ P hP hpρ Q)
    (σ.frobenius_charpoly w₀ q hσ P hP hpσ Q) rfl

/-- The single algebraic character then gives equal actual Frobenius
polynomials at another completion. The residue characteristics at both the
original and new places are excluded explicitly. -/
theorem NumberFieldCompatibleSystem.charpoly_characterTensor_eq_of_onePlace
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : HilbertModularForms.AbsoluteGalois F →* Eˣ)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter
        ((Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (σ.action w₀)))
    (q : HeightOneSpectrum (𝓞 F)) (hρ : q ∉ ρ.bad) (hσ : q ∉ σ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hpρ₀ : (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (hpσ₀ : (σ.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (hpρ : (ρ.residueCharacteristic w : 𝓞 F) ∉ P)
    (hpσ : (σ.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      (((Representation.ofCharacter
        ((Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (σ.action w))
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
  have : Infinite (w.adicCompletion E) :=
    Infinite.of_injective (algebraMap E (w.adicCompletion E))
      (algebraMap E (w.adicCompletion E)).injective
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have hpoly : ρ.polynomial q = (σ.polynomial q).scaleRoots (χ g : E) :=
    ρ.polynomial_eq_scaleRoots_of_onePlace σ χ w₀ e q hρ hσ P hP hpρ₀ hpσ₀ Q
  rw [ρ.frobenius_charpoly w q hρ P hP hpρ Q, hpoly]
  exact (Representation.charpoly_characterTensor_eq_map_scaleRoots
    (algebraMap E (w.adicCompletion E)) (σ.action w)
    ((Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom).comp χ)
    g (σ.polynomial q) (χ g)
    (σ.frobenius_charpoly w q hσ P hP hpσ Q) rfl).symm

/-- Equality of geometric-Frobenius traces at every coefficient completion.
The character value is embedded through the fixed coefficient-field map. -/
theorem NumberFieldCompatibleSystem.frobenius_trace_characterTwist_eq_of_onePlace
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : HilbertModularForms.AbsoluteGalois F →* Eˣ)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter
        ((Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom).comp χ)).tprod
          (σ.action w₀)))
    (q : HeightOneSpectrum (𝓞 F)) (hρ : q ∉ ρ.bad) (hσ : q ∉ σ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hpρ₀ : (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (hpσ₀ : (σ.residueCharacteristic w₀ : 𝓞 F) ∉ P)
    (hpρ : (ρ.residueCharacteristic w : 𝓞 F) ∉ P)
    (hpσ : (σ.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) =
      (χ (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : w.adicCompletion E) *
        LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
          (σ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let χw := (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom).comp χ
  have hpoly := ρ.charpoly_characterTensor_eq_of_onePlace σ χ w₀ w e q hρ hσ
    P hP hpρ₀ hpσ₀ hpρ hpσ Q
  have hpoly' : (ρ.action w g).charpoly =
      ((σ.action w).characterTwist χw g).charpoly :=
    hpoly.trans ((Representation.characterTwistTensorEquiv (σ.action w) χw).charpoly_eq g)
  let b := Pi.basisFun (w.adicCompletion E) (Fin 2)
  have hM : (LinearMap.toMatrix b b (ρ.action w g)).charpoly =
      (LinearMap.toMatrix b b ((σ.action w).characterTwist χw g)).charpoly := by
    simpa only [LinearMap.charpoly_toMatrix] using hpoly'
  have htrace : LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
      (ρ.action w g) = LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
      ((σ.action w).characterTwist χw g) := by
    rw [LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
      LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
      Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hM]
  rw [htrace]
  change LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
      ((χw g : w.adicCompletion E) • (σ.action w g)) = _
  rw [LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
    LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
    map_smul, Matrix.trace_smul]
  change (χw g : w.adicCompletion E) *
      Matrix.trace (LinearMap.toMatrix b b (σ.action w g)) = _
  rfl


end HilbertModularity
