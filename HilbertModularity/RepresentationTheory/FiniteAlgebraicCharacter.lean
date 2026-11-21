/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteExceptionalPrimes
public import HilbertModularity.RepresentationTheory.PromotionFiniteSet
public import HilbertModularity.RepresentationTheory.CharacterTwist

/-! # Finite-order algebraic Galois characters

A finite-order character used to twist a compatible system has one algebraic
value at each Galois element, hence one fixed image in every coefficient
completion.  We record local continuity and finite ramification explicitly;
neither follows from the bare algebraic homomorphism in the present library.
The finite ramification set is independent of the coefficient place.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- A single finite-order algebraic character, with its continuous local
realizations and a common finite ramification set. -/
structure FiniteAlgebraicGaloisCharacter (F E : Type*) [Field F] [NumberField F]
    [Field E] [NumberField E] where
  toMonoidHom : HilbertModularForms.AbsoluteGalois F →* Eˣ
  finite_range : (Set.range toMonoidHom).Finite
  local_continuous : ∀ w : HeightOneSpectrum (𝓞 E),
    Continuous (fun g : HilbertModularForms.AbsoluteGalois F =>
      (((Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom).comp
        toMonoidHom) g : w.adicCompletion E))
  bad : Set (HeightOneSpectrum (𝓞 F))
  bad_finite : bad.Finite
  unramified : ∀ q, q ∉ bad →
    ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
        ∀ g : HilbertModularForms.AbsoluteGalois F,
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F) → toMonoidHom g = 1

/-- The local character uses the canonical embedding of the one algebraic
coefficient field into its completion. -/
def FiniteAlgebraicGaloisCharacter.local
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) :
    HilbertModularForms.AbsoluteGalois F →* (w.adicCompletion E)ˣ :=
  (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom).comp χ.toMonoidHom

/-- The local character is the fixed algebraic character followed by the
canonical coefficient embedding. -/
theorem FiniteAlgebraicGaloisCharacter.local_eq_composition
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) :
    χ.local w =
      (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom).comp χ.toMonoidHom :=
  (rfl)

/-- A finite-order character twist of a compatible-system member is
semisimple at every coefficient place. -/
theorem NumberFieldCompatibleSystem.characterTwist_semisimple
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) :
    ((σ.action w).characterTwist (χ.local w)).IsSemisimpleRepresentation :=
  (Representation.isSemisimple_characterTwist_iff (σ.action w) (χ.local w)).2
    (σ.semisimple w)

/-- The equivalent character-line tensor representation is semisimple too. -/
theorem NumberFieldCompatibleSystem.characterTensor_semisimple
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) :
    ((Representation.ofCharacter (χ.local w)).tprod
      (σ.action w)).IsSemisimpleRepresentation :=
  (Representation.isSemisimple_characterTensor_iff (σ.action w) (χ.local w)).2
    (σ.semisimple w)

/-- The matrix coefficients of the twisted local action are continuous. -/
theorem NumberFieldCompatibleSystem.characterTwist_continuous
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) (i j : Fin 2) :
    Continuous (fun g : HilbertModularForms.AbsoluteGalois F =>
      ((σ.action w).characterTwist (χ.local w) g (Pi.single j 1)) i) := by
  have h : Continuous (fun g : HilbertModularForms.AbsoluteGalois F =>
      (χ.local w g : w.adicCompletion E) *
        (σ.action w g (Pi.single j 1)) i) :=
    (χ.local_continuous w).mul (σ.continuous w i j)
  convert h using 1
  funext g
  simp [Representation.characterTwist_apply, Pi.smul_apply, smul_eq_mul]

/-- Outside the union of the system and character bad sets, the twisted
action is trivial on the inertia group of the chosen geometric prime. -/
theorem NumberFieldCompatibleSystem.characterTwist_unramified
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F))
    (hqσ : q ∉ σ.bad) (hqχ : q ∉ χ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (σ.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (g : HilbertModularForms.AbsoluteGalois F)
    (hg : g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F)) :
    (σ.action w).characterTwist (χ.local w) g = 1 := by
  have hσ := σ.unramified w q hqσ P hP hp Q g hg
  have hχ := χ.unramified q hqχ P hP Q g hg
  ext v
  simp [Representation.characterTwist_apply, hσ,
    FiniteAlgebraicGaloisCharacter.local, hχ]

/-- A fixed coefficient place has a finite exceptional set for the twisted
action. It includes the algebraic character's finite ramification set. -/
def NumberFieldCompatibleSystem.twistBadAt
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) : Set (HeightOneSpectrum (𝓞 F)) :=
  σ.badAt w ∪ χ.bad

theorem NumberFieldCompatibleSystem.twistBadAt_finite
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) :
    (σ.twistBadAt χ w).Finite :=
  (σ.badAt_finite w).union χ.bad_finite

/-- Good primes for the system and character avoid the twist's exceptional set. -/
theorem NumberFieldCompatibleSystem.not_mem_twistBadAt_of_good
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E)) (q : HeightOneSpectrum (𝓞 F))
    (hσ : q ∉ σ.bad) (hχ : q ∉ χ.bad)
    (hp : (σ.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal) :
    q ∉ σ.twistBadAt χ w := by
  simpa only [NumberFieldCompatibleSystem.twistBadAt, Set.mem_union, not_or]
    using And.intro (σ.not_mem_badAt_of_good w q hσ hp) hχ

/-- The actual character-twisted local representation is unramified away
from the finite set just defined. -/
theorem NumberFieldCompatibleSystem.characterTwist_unramified_of_good
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ σ.twistBadAt χ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (g : HilbertModularForms.AbsoluteGalois F)
    (hg : g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F)) :
    (σ.action w).characterTwist (χ.local w) g = 1 := by
  have h := hq
  simp only [NumberFieldCompatibleSystem.twistBadAt, Set.mem_union, not_or] at h
  rcases h with ⟨hσbad, hχ⟩
  obtain ⟨hσ, hp⟩ := σ.good_of_not_mem_badAt w q hσbad
  exact σ.characterTwist_unramified χ w q hσ hχ P hP (hP.symm ▸ hp) Q g hg

/-- At every allowed geometric Frobenius, the local twisted polynomial comes
from the original algebraic polynomial and the value of the *same* algebraic
character. No coefficient place occurs in that algebraic expression. -/
theorem NumberFieldCompatibleSystem.characterTwist_frobenius_charpoly
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ σ.twistBadAt χ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    ((σ.action w).characterTwist (χ.local w)
      (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      ((σ.polynomial q).scaleRoots
        (χ.toMonoidHom
          (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) : E)).map
            (algebraMap E (w.adicCompletion E)) := by
  have h := hq
  simp only [NumberFieldCompatibleSystem.twistBadAt, Set.mem_union, not_or] at h
  have hgood := (σ.good_of_not_mem_badAt w q h.1)
  have hσ := σ.frobenius_charpoly w q hgood.1 P hP (hP.symm ▸ hgood.2) Q
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  let χw := χ.local w
  have : Infinite (w.adicCompletion E) :=
    Infinite.of_injective (algebraMap E (w.adicCompletion E))
      (algebraMap E (w.adicCompletion E)).injective
  have htensor := Representation.charpoly_characterTensor_eq_map_scaleRoots
    (algebraMap E (w.adicCompletion E)) (σ.action w) χw g
    (σ.polynomial q) (χ.toMonoidHom g : E) hσ rfl
  exact ((Representation.characterTwistTensorEquiv (σ.action w) χw).charpoly_eq g).symm.trans
    htensor

/-- The comparison set also excludes ramification of the one algebraic
character. This is the finite set needed when Frobenius detection is applied
to the actual twisted representation. -/
def NumberFieldCompatibleSystem.characterComparisonBad
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E)) : Set (HeightOneSpectrum (𝓞 F)) :=
  ρ.comparisonBad σ w₀ w ∪ χ.bad

theorem NumberFieldCompatibleSystem.characterComparisonBad_finite
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E)) :
    (ρ.characterComparisonBad σ χ w₀ w).Finite :=
  (ρ.comparisonBad_finite σ w₀ w).union χ.bad_finite

/-- Avoiding the character comparison set also avoids the ordinary
two-system comparison set. -/
theorem NumberFieldCompatibleSystem.not_mem_comparisonBad_of_characterGood
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad σ χ w₀ w) :
    q ∉ ρ.comparisonBad σ w₀ w := by
  have h : q ∉ ρ.comparisonBad σ w₀ w ∧ q ∉ χ.bad := by
    simpa only [NumberFieldCompatibleSystem.characterComparisonBad,
      Set.mem_union, not_or] using hq
  exact h.1

/-- The joint complement supplies all four coefficient exclusions as well as
the independent character ramification exclusion. -/
theorem NumberFieldCompatibleSystem.good_of_not_mem_characterComparisonBad
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad σ χ w₀ w) :
    q ∉ ρ.bad ∧ q ∉ σ.bad ∧ q ∉ χ.bad ∧
      (ρ.residueCharacteristic w₀ : 𝓞 F) ∉ q.asIdeal ∧
      (σ.residueCharacteristic w₀ : 𝓞 F) ∉ q.asIdeal ∧
      (ρ.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal ∧
      (σ.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal := by
  have hpair : q ∉ ρ.comparisonBad σ w₀ w ∧ q ∉ χ.bad := by
    simpa only [NumberFieldCompatibleSystem.characterComparisonBad,
      Set.mem_union, not_or] using hq
  obtain ⟨hρ, hσ, hpρ₀, hpσ₀, hpρ, hpσ⟩ :=
    ρ.good_of_not_mem_comparisonBad σ w₀ w q hpair.1
  exact ⟨hρ, hσ, hpair.2, hpρ₀, hpσ₀, hpρ, hpσ⟩

/-- The twisted target is unramified away from the finite comparison set. -/
theorem NumberFieldCompatibleSystem.characterTwist_unramified_of_comparisonGood
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad σ χ w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (g : HilbertModularForms.AbsoluteGalois F)
    (hg : g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois F)) :
    (σ.action w).characterTwist (χ.local w) g = 1 := by
  obtain ⟨_, hσ, hχ, _, _, _, hpσ⟩ :=
    ρ.good_of_not_mem_characterComparisonBad σ χ w₀ w q hq
  exact σ.characterTwist_unramified χ w q hσ hχ P hP (hP.symm ▸ hpσ) Q g hg

/-- Outside the joint finite set, the two actual representations have the
same geometric-Frobenius polynomial. The character ramification exclusion is
retained for the subsequent Chebotarev step. -/
theorem NumberFieldCompatibleSystem.charpoly_characterTwist_eq_of_good
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (σ.action w₀)))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad σ χ w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    (ρ.action w (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
      ((σ.action w).characterTwist (χ.local w)
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly := by
  have hq' : q ∉ ρ.comparisonBad σ w₀ w := by
    have hqpair : q ∉ ρ.comparisonBad σ w₀ w ∧ q ∉ χ.bad := by
      simpa only [NumberFieldCompatibleSystem.characterComparisonBad,
        Set.mem_union, not_or] using hq
    exact hqpair.1
  have htensor := ρ.charpoly_characterTensor_eq_of_good σ χ.toMonoidHom w₀ w
    (by simpa only [FiniteAlgebraicGaloisCharacter.local] using e)
    q hq' P hP Q
  exact htensor.trans
    ((Representation.characterTwistTensorEquiv (σ.action w) (χ.local w)).charpoly_eq
      (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q))

end HilbertModularity
