/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.LocalSystem.Coordinates
public import HilbertModularity.Hypergeometric.RMComparisonAlgebraicDescent
public import HilbertModularity.Hypergeometric.DarmonFiniteRamification
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomologyIrreducibility

/-! # Algebraic comparison for the chosen Darmon family

The arithmetic descent argument constructs one finite algebraic character for
all nonsingular fibres. The RM-side rank, absolute irreducibility and finite ramification are derived
from the actual chosen abelian scheme. The final determinant-based API needs
only geometric comparison and normalized determinants: finite ramification of
the constructed finite character follows from a named standard literature input.
The earlier API with prescribed effective-side ramification remains available.
-/

public noncomputable section

open AlgebraicGeometry NumberField IsDedekindDomain

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]

/-- The arithmetic deduction of [TripathiGoswamiRevised, Theorem RMgeneral,
steps 3--5] for the single chosen Darmon family. The constructed coefficient
field contains the specified coefficient field with its original embedding.
Every fibre uses the same character and the same labelled cohomological dual,
identified with the explicit Tate factor by
`darmonCohomologicalFamilyArithmeticEquiv`.
This does not establish the geometric or determinant prerequisites. -/
theorem exists_algebraic_character_comparing_darmon_fibers
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_eff : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]
    (ρRM : Representation L
      (Scheme.etaleFundamentalGroup (realCyclotomicField N)
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀)) V)
    (ρEff : Representation L
      (Scheme.etaleFundamentalGroup (realCyclotomicField N)
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀)) W)
    (eRM : ρRM.Equiv (puncturedFiberMonodromy (realCyclotomicField N) ξ₀
      (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)))
    (eEff : ρEff.Equiv (puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff))
    (hRMc : ∀ v, Continuous (fun g => ρRM g v))
    (hEffc : ∀ v, Continuous (fun g => ρEff g v))
    (eGeom : Representation.Equiv
      (ρRM.comp (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype)
      (ρEff.comp (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype))
    (ε : Scheme.etaleFundamentalGroup (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀) →* Lˣ)
    (hRMdet : ∀ g, ρRM.determinantCharacter g * ε g = 1)
    (n : ℕ) (hn : 0 < n)
    (hEffdet : ∀ g, (ρEff.determinantCharacter g * ε g) ^ n = 1)
    (badEff : Set (HeightOneSpectrum (𝓞 (realCyclotomicField N)))) (hbadEff : badEff.Finite)
    (hEff : ∀ q, q ∉ badEff →
      ∀ (P : Ideal (𝓞 (realCyclotomicField N))) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N)))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N),
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois (realCyclotomicField N)) →
              puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ₀ F_eff g = 1) :
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        letI : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
          (algebraMap E (w.adicCompletion E))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        letI : NumberField E' :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) E',
          (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          E'.subtype.comp (algebraMap E E') = (algebraMap (w.adicCompletion E) L).comp
            (algebraMap E (w.adicCompletion E)) ∧
          ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
            Nonempty (((Representation.ofCharacter
              ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
                  (darmonCohomologicalFamily (realCyclotomicField N)
                    N hN p m hm E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ F_eff)) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let Lbar := AlgebraicClosure L
  let : Algebra ℚ_[p] Lbar := inferInstance
  let : Algebra ℚ Lbar := inferInstance
  have : IsScalarTower ℚ_[p] L Lbar := inferInstance
  have : IsScalarTower ℚ L Lbar := inferInstance
  have : IsScalarTower ℚ ℚ_[p] L :=
    IsScalarTower.to₁₂₄ ℚ ℚ_[p] (w.adicCompletion E) L
  have : IsScalarTower ℚ ℚ_[p] Lbar :=
    IsScalarTower.to₁₂₄ ℚ ℚ_[p] L Lbar
  let k := (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype
  have hirr := darmonCohomologicalFamily_arithmeticKernel_baseChange_isIrreducible
    N hN p m hm E hE w L Lbar ξ₀
  have : (Representation.baseChange Lbar (ρRM.comp k)).IsIrreducible :=
    (OrderIso.isSimpleOrder_iff ((eRM.compHom k).baseChange Lbar).subrepresentationOrderIso).mpr hirr
  have hdim : Module.finrank L V = 2 :=
    eRM.toLinearEquiv.finrank_eq.trans
      (finrank_darmonCohomologicalFamily_at (realCyclotomicField N) N hN p m hm E hE w L
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀))
  have hramification :=
    darmonCohomologicalFamily_unramifiedOutsideFinite (realCyclotomicField N)
      N hN p m hm E hE w L (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀)
  rcases hramification with ⟨badRM, hbadRM, hRM⟩
  have hcomparison :=
    exists_algebraic_comparison_character_at_all_punctured_fibers
      (realCyclotomicField N) E L
      ((algebraMap (w.adicCompletion E) L).comp (algebraMap E (w.adicCompletion E)))
      ξ₀ (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)
      F_eff ρRM ρEff eRM eEff hRMc hEffc eGeom Lbar hdim ε hRMdet n hn hEffdet
      badRM badEff hbadRM hbadEff hRM hEff
  rcases hcomparison with ⟨ν, hνc, hνfin, χ, _, hχ, hEχ, hfib⟩
  exact ⟨ν, hνc, hνfin, χ, hχ, hEχ, hfib⟩

/-- The same arithmetic comparison stated directly for the two actual continuous
local systems. Finite normed coordinates and continuous orbit maps are constructed
from their existing fibre topologies; they are not additional hypotheses.
The geometric comparison, determinant normalizations and effective ramification
are exactly the remaining inputs to this deduction of
[TripathiGoswamiRevised, Theorem RMgeneral, steps 3--5]. -/
theorem exists_algebraic_character_comparing_darmon_localSystems
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_eff : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (eGeom : Representation.Equiv
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀
        (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)).comp
          (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype)
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff).comp
        (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype))
    (ε : Scheme.etaleFundamentalGroup (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀) →* Lˣ)
    (hRMdet : ∀ g, (puncturedFiberMonodromy (realCyclotomicField N) ξ₀
      (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)).determinantCharacter g * ε g = 1)
    (n : ℕ) (hn : 0 < n)
    (hEffdet : ∀ g, ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff).determinantCharacter g * ε g) ^ n = 1)
    (badEff : Set (HeightOneSpectrum (𝓞 (realCyclotomicField N)))) (hbadEff : badEff.Finite)
    (hEff : ∀ q, q ∉ badEff →
      ∀ (P : Ideal (𝓞 (realCyclotomicField N))) [P.IsMaximal], P = q.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N)))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N),
            g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois (realCyclotomicField N)) →
              puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ₀ F_eff g = 1) :
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        letI : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
          (algebraMap E (w.adicCompletion E))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        letI : NumberField E' :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) E',
          (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          E'.subtype.comp (algebraMap E E') = (algebraMap (w.adicCompletion E) L).comp
            (algebraMap E (w.adicCompletion E)) ∧
          ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
            Nonempty (((Representation.ofCharacter
              ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
                  (darmonCohomologicalFamily (realCyclotomicField N)
                    N hN p m hm E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ F_eff)) := by
  let K := realCyclotomicField N
  let x := ProjectiveLine.puncturedPoint K ξ₀
  let F_RM := darmonCohomologicalFamily K N hN p m hm E hE w L
  let eRM := (F_RM.coordinateMonodromyEquiv x).symm
  let eEff := (F_eff.coordinateMonodromyEquiv x).symm
  have hdim : Module.finrank L (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)) = 2 :=
    finrank_darmonCohomologicalFamily_at K N hN p m hm E hE w L x
  let : Nonempty (Fin (Module.finrank L (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)))) :=
    ⟨⟨0, by omega⟩⟩
  let k := (puncturedArithmeticProjectionHom K ξ₀).ker.subtype
  have eGeom' := (eRM.compHom k).trans (eGeom.trans (eEff.symm.compHom k))
  have detRM (g) : (F_RM.coordinateMonodromy x).determinantCharacter g =
      (puncturedFiberMonodromy K ξ₀ F_RM).determinantCharacter g := by
    apply Units.ext
    change LinearMap.det ((F_RM.coordinateMonodromy x) g) =
      LinearMap.det (Scheme.fiberMonodromy K (ProjectiveLine.punctured K) F_RM.algebraicFunctor x g)
    exact (LinearMap.det_conj _ eRM.toLinearEquiv).symm.trans
      (congrArg LinearMap.det (eRM.conj_apply_self g))
  have detEff (g) : (F_eff.coordinateMonodromy x).determinantCharacter g =
      (puncturedFiberMonodromy K ξ₀ F_eff).determinantCharacter g := by
    apply Units.ext
    change LinearMap.det ((F_eff.coordinateMonodromy x) g) =
      LinearMap.det (Scheme.fiberMonodromy K (ProjectiveLine.punctured K) F_eff.algebraicFunctor x g)
    exact (LinearMap.det_conj _ eEff.toLinearEquiv).symm.trans
      (congrArg LinearMap.det (eEff.conj_apply_self g))
  exact exists_algebraic_character_comparing_darmon_fibers N hN p m hm E hE w L
    ξ₀ F_eff (F_RM.coordinateMonodromy x) (F_eff.coordinateMonodromy x)
    eRM eEff (F_RM.continuous_coordinateMonodromy x)
    (F_eff.continuous_coordinateMonodromy x) eGeom' ε
    (fun g => by rw [detRM]; exact hRMdet g) n hn
    (fun g => by rw [detEff]; exact hEffdet g) badEff hbadEff hEff

/-- The all-fibre arithmetic deduction for the actual Darmon local system from
geometric comparison and normalized determinants alone. Rank, absolute
irreducibility and continuous coordinates are derived internally. Finite
ramification of the resulting finite character uses
[MilneFT, Theorem 7.13; MilneANT, Remark 3.39(b)].
This does not establish the geometric comparison or determinant identities. -/
theorem exists_algebraic_character_comparing_darmon_localSystems_of_determinants
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_eff : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (eGeom : Representation.Equiv
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀
        (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)).comp
          (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype)
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff).comp
        (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype))
    (ε : Scheme.etaleFundamentalGroup (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀) →* Lˣ)
    (hRMdet : ∀ g, (puncturedFiberMonodromy (realCyclotomicField N) ξ₀
      (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)).determinantCharacter g * ε g = 1)
    (n : ℕ) (hn : 0 < n)
    (hEffdet : ∀ g, ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff).determinantCharacter g * ε g) ^ n = 1)
    : ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
      Continuous ν ∧ ∃ hνfin : (Set.range ν).Finite,
        letI : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
          (algebraMap E (w.adicCompletion E))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        letI : NumberField E' :=
          RepresentationTheory.numberField_finiteCharacterCoefficientField ν hνfin
        ∃ χ : FiniteAlgebraicGaloisCharacter (realCyclotomicField N) E',
          (Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom = ν ∧
          E'.subtype.comp (algebraMap E E') = (algebraMap (w.adicCompletion E) L).comp
            (algebraMap E (w.adicCompletion E)) ∧
          ∀ ξ : ProjectiveLine.Parameter (realCyclotomicField N),
            Nonempty (((Representation.ofCharacter
              ((Units.map E'.subtype.toMonoidHom).comp χ.toMonoidHom)).tprod
                (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ
                  (darmonCohomologicalFamily (realCyclotomicField N)
                    N hN p m hm E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ F_eff)) := by
  let K := realCyclotomicField N
  let x := ProjectiveLine.puncturedPoint K ξ₀
  let F_RM := darmonCohomologicalFamily K N hN p m hm E hE w L
  let eRM := (F_RM.coordinateMonodromyEquiv x).symm
  let eEff := (F_eff.coordinateMonodromyEquiv x).symm
  have hdim : Module.finrank L (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)) = 2 :=
    finrank_darmonCohomologicalFamily_at K N hN p m hm E hE w L x
  let : Nonempty (Fin (Module.finrank L (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)))) :=
    ⟨⟨0, by omega⟩⟩
  let k := (puncturedArithmeticProjectionHom K ξ₀).ker.subtype
  have eGeom' := (eRM.compHom k).trans (eGeom.trans (eEff.symm.compHom k))
  have detRM (g) : (F_RM.coordinateMonodromy x).determinantCharacter g =
      (puncturedFiberMonodromy K ξ₀ F_RM).determinantCharacter g := by
    apply Units.ext
    change LinearMap.det ((F_RM.coordinateMonodromy x) g) =
      LinearMap.det (Scheme.fiberMonodromy K (ProjectiveLine.punctured K) F_RM.algebraicFunctor x g)
    exact (LinearMap.det_conj _ eRM.toLinearEquiv).symm.trans
      (congrArg LinearMap.det (eRM.conj_apply_self g))
  have detEff (g) : (F_eff.coordinateMonodromy x).determinantCharacter g =
      (puncturedFiberMonodromy K ξ₀ F_eff).determinantCharacter g := by
    apply Units.ext
    change LinearMap.det ((F_eff.coordinateMonodromy x) g) =
      LinearMap.det (Scheme.fiberMonodromy K (ProjectiveLine.punctured K) F_eff.algebraicFunctor x g)
    exact (LinearMap.det_conj _ eEff.toLinearEquiv).symm.trans
      (congrArg LinearMap.det (eEff.conj_apply_self g))
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let Lbar := AlgebraicClosure L
  have : IsScalarTower ℚ ℚ_[p] L :=
    IsScalarTower.to₁₂₄ ℚ ℚ_[p] (w.adicCompletion E) L
  have : IsScalarTower ℚ ℚ_[p] Lbar :=
    IsScalarTower.to₁₂₄ ℚ ℚ_[p] L Lbar
  have hirr := darmonCohomologicalFamily_arithmeticKernel_baseChange_isIrreducible
    N hN p m hm E hE w L Lbar ξ₀
  have : (Representation.baseChange Lbar
      ((F_RM.coordinateMonodromy x).comp k)).IsIrreducible :=
    (OrderIso.isSimpleOrder_iff
      ((eRM.compHom k).baseChange Lbar).subrepresentationOrderIso).mpr hirr
  have hdim' : Module.finrank L (Fin (Module.finrank L (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x))) → L) = 2 :=
    eRM.toLinearEquiv.finrank_eq.trans hdim
  obtain ⟨ν, hνc, hνfin, ⟨e⟩, _⟩ :=
    exists_finite_comparison_character_along_punctured_paths
      K ξ₀ (F_RM.coordinateMonodromy x) (F_eff.coordinateMonodromy x)
      (F_RM.continuous_coordinateMonodromy x)
      (F_eff.continuous_coordinateMonodromy x) eGeom' Lbar hdim' ε
      (fun g => by rw [detRM]; exact hRMdet g) n hn
      (fun g => by rw [detEff]; exact hEffdet g)
  have hgeneric :=
    (Representation.characterTensorEquivCongr
      (ν.comp (puncturedArithmeticProjectionHom K ξ₀)) eRM.symm).trans
        (e.trans eEff)
  exact ⟨ν, hνc, hνfin, algebraic_comparison_character_of_finite_image
    K E L ((algebraMap (w.adicCompletion E) L).comp
      (algebraMap E (w.adicCompletion E))) ξ₀ F_RM F_eff ν hνc hνfin hgeneric⟩

end HilbertModularity.Hypergeometric
