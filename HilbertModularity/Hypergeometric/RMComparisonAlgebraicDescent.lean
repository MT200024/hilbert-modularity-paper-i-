/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparisonAlgebraization

/-! # Algebraic descent of the generic comparison

Geometric comparison and normalized determinant identities produce a finite
character on the arithmetic quotient. At one finitely ramified rational fibre
its values generate a number field over the specified coefficient field.
The resulting algebraic character compares every fibre of the same two local
systems. The geometric and determinant hypotheses remain explicit.
-/

public noncomputable section

open AlgebraicGeometry NumberField IsDedekindDomain

namespace HilbertModularity.Hypergeometric

/-- The arithmetic descent deduction of [TripathiGoswamiRevised,
Theorem RMgeneral, steps 3--5], using the determinant criterion for finiteness.
The supplied normed representations are identified with the actual monodromy
of the two local systems. No finite comparison character is assumed.
The same algebraic character works at every rational nonsingular fibre;
its coefficient field retains the specified embedding of `E₀`.

Applying this theorem to the manuscript still requires the geometric comparison,
absolute irreducibility and determinant formulas for the selected families. -/
theorem exists_algebraic_comparison_character_at_all_punctured_fibers
    (K E₀ L : Type*) [Field K] [NumberField K]
    [Field E₀] [NumberField E₀]
    [NontriviallyNormedField L] [CharZero L] [CompleteSpace L]
    (ι₀ : E₀ →+* L) (ξ₀ : ProjectiveLine.Parameter K)
    (F_RM F_eff : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]
    (ρRM : Representation L
      (Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀)) V)
    (ρEff : Representation L
      (Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀)) W)
    (eRM : ρRM.Equiv (puncturedFiberMonodromy K ξ₀ F_RM))
    (eEff : ρEff.Equiv (puncturedFiberMonodromy K ξ₀ F_eff))
    (hRMc : ∀ v, Continuous (fun g => ρRM g v))
    (hEffc : ∀ v, Continuous (fun g => ρEff g v))
    (eGeom : Representation.Equiv
      (ρRM.comp (puncturedArithmeticProjectionHom K ξ₀).ker.subtype)
      (ρEff.comp (puncturedArithmeticProjectionHom K ξ₀).ker.subtype))
    (Lbar : Type*) [Field Lbar] [Algebra L Lbar] [IsAlgClosed Lbar]
    [Representation.IsIrreducible (Representation.baseChange Lbar
      (ρRM.comp (puncturedArithmeticProjectionHom K ξ₀).ker.subtype))]
    (hdim : Module.finrank L V = 2)
    (ε : Scheme.etaleFundamentalGroup K
      (ProjectiveLine.puncturedPoint K ξ₀) →* Lˣ)
    (hRMdet : ∀ g, ρRM.determinantCharacter g * ε g = 1)
    (n : ℕ) (hn : 0 < n)
    (hEffdet : ∀ g, (ρEff.determinantCharacter g * ε g) ^ n = 1)
    (badRM badEff : Set (HeightOneSpectrum (𝓞 K)))
    (hbadRM : badRM.Finite) (hbadEff : badEff.Finite)
    (hRM : ∀ q, q ∉ badRM →
      ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois K,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois K) →
              puncturedFiberArithmeticRepresentation K ξ₀ F_RM g = 1)
    (hEff : ∀ q, q ∉ badEff →
      ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure K))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois K,
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois K) →
              puncturedFiberArithmeticRepresentation K ξ₀ F_eff g = 1) :
    ∃ ν : HilbertModularForms.AbsoluteGalois K →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        letI : Algebra E₀ L := ι₀.toAlgebra
        let E := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E₀) ν
        letI : NumberField E :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter K E,
          χ.bad = badRM ∪ badEff ∧
          (Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          E.subtype.comp (algebraMap E₀ E) = ι₀ ∧
          ∀ ξ : ProjectiveLine.Parameter K,
            Nonempty (((Representation.ofCharacter
              ((Units.map E.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                (puncturedFiberArithmeticRepresentation K ξ F_RM)).Equiv
                  (puncturedFiberArithmeticRepresentation K ξ F_eff)) := by
  obtain ⟨ν, hνc, hνfin, ⟨e⟩, _⟩ :=
    exists_finite_comparison_character_along_punctured_paths
      K ξ₀ ρRM ρEff hRMc hEffc eGeom Lbar hdim ε hRMdet n hn hEffdet
  let : Nontrivial (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K)
        (ProjectiveLine.puncturedPoint K ξ₀))) :=
    eRM.toLinearEquiv.injective.nontrivial
  have hgeneric :=
    (Representation.characterTensorEquivCongr
      (ν.comp (puncturedArithmeticProjectionHom K ξ₀)) eRM.symm).trans
        (e.trans eEff)
  exact ⟨ν, hνc, hνfin,
    algebraic_comparison_character_at_all_punctured_fibers
      K E₀ L ι₀ ξ₀ F_RM F_eff ν hνc hνfin hgeneric
      badRM badEff hbadRM hbadEff hRM hEff⟩

end HilbertModularity.Hypergeometric
