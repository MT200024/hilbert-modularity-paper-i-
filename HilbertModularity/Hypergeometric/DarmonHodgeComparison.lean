/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.DarmonGenericComparison
public import HilbertModularity.RepresentationTheory.LabelledCharacterAlgebraization

/-! # Hodge–Tate determinant route to the Darmon comparison

The normalized determinant at one actual arithmetic fibre has finite order
by its zero labelled weights. Generic geometric comparison then propagates
that bound and produces one algebraic character comparing every fibre.
This is the determinant argument in [TripathiGoswami, Proposition 2.5]
followed by [TripathiGoswamiRevised, Theorem RMgeneral, steps 3–5].
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField CategoryTheory.MonObj
open NumberField.LocalGalois

attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic

/-- The actual arithmetic determinant multiplied by the cyclotomic character,
whose vanishing Hodge–Tate weights force finite order. -/
def puncturedFiberNormalizedDeterminant
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L]
    (ξ : ProjectiveLine.Parameter K)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    HilbertModularForms.AbsoluteGalois K →* Lˣ :=
  (puncturedFiberArithmeticRepresentation K ξ F).determinantCharacter *
    (Field.cyclotomicCharacterWithCoefficients K p L).toMonoidHom

/-- The normalization uses the actual arithmetic determinant and cyclotomic action. -/
theorem puncturedFiberNormalizedDeterminant_eq
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L]
    (ξ : ProjectiveLine.Parameter K)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    puncturedFiberNormalizedDeterminant K p L ξ F =
      (puncturedFiberArithmeticRepresentation K ξ F).determinantCharacter *
        (Field.cyclotomicCharacterWithCoefficients K p L).toMonoidHom := (rfl)

/-- Evaluation of the normalized arithmetic determinant. -/
theorem puncturedFiberNormalizedDeterminant_apply
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L]
    (ξ : ProjectiveLine.Parameter K)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (g : HilbertModularForms.AbsoluteGalois K) :
    puncturedFiberNormalizedDeterminant K p L ξ F g =
      (puncturedFiberArithmeticRepresentation K ξ F).determinantCharacter g *
        Field.cyclotomicCharacterWithCoefficients K p L g := (rfl)

/-- Continuity follows from the given local system and the actual cyclotomic
character; it is not a new arithmetic-comparison hypothesis. -/
theorem continuous_puncturedFiberNormalizedDeterminant
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L]
    (ξ : ProjectiveLine.Parameter K)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    Continuous (puncturedFiberNormalizedDeterminant K p L ξ F) := by
  let x := ProjectiveLine.puncturedPoint K ξ
  let a := Scheme.galoisToEtaleFundamentalGroup K x
  let e := ((F.coordinateMonodromyEquiv x).compHom a).symm
  let ρ := (F.coordinateMonodromy x).comp a
  let b := Module.finBasis L (Fin (Module.finrank L
    (F.toFunctor.obj (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x))) → L)
  have hc : Continuous (Representation.determinantCharacter ρ) :=
    Representation.continuous_determinantCharacter_of_basis b
      (fun i => (b.coord i).continuous_of_finiteDimensional) ρ
      (fun v => (F.continuous_coordinateMonodromy x v).comp
        (Scheme.continuous_galoisToEtaleFundamentalGroup K x))
  have hd : Representation.determinantCharacter ρ =
      (puncturedFiberArithmeticRepresentation K ξ F).determinantCharacter := by
    ext g
    exact (LinearMap.det_conj _ e.toLinearEquiv).symm.trans
      (congrArg LinearMap.det (e.conj_apply_self g))
  rw [hd] at hc
  exact hc.mul (Field.cyclotomicCharacterWithCoefficients K p L).continuous

variable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime N)
  (E : IntermediateField ℚ Qbar) [NumberField E]
  (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
  (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion E) L] [ContinuousSMul (w.adicCompletion E) L]
  [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]

/-- Bijective local Hodge–Tate comparison and zero weights at every label
for the actual normalized determinant at one fibre suffice for the single
finite algebraic character comparison at all fibres. The geometric comparison,
path compatibility, finite ramification and local Hodge assertions still need
their applications to the selected effective family. -/
theorem exists_algebraic_character_comparing_darmon_localSystems_of_labelledHodgeTate
    [Fact N.Prime] (hp : 5 ≤ N) [IsScalarTower ℚ ℚ_[p] L]
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_eff : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (F_gen : Scheme.EtaleLocalSystem (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ePath : Representation.Equiv
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff).comp
        (Scheme.geometricFiberPathGroupEquiv _ _
          (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
            (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀))).toMonoidHom))
    (eGeom :
      let xgen := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
      let k := (Scheme.etaleFundamentalGroupMap
        (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
        (RatFunc (realCyclotomicField N)) xgen).ker.subtype
      Representation.Equiv
        ((Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
          (ProjectiveLine.punctured (realCyclotomicField N))
          (darmonCohomologicalFamily (RatFunc (realCyclotomicField N))
            N hN p m hm E hE w L).algebraicFunctor xgen).comp k)
        ((Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
          (ProjectiveLine.punctured (realCyclotomicField N))
          F_gen.algebraicFunctor xgen).comp k))
    (bad : Finset (HeightOneSpectrum (𝓞 (realCyclotomicField N))))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N)))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N),
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois (realCyclotomicField N)) → q ∉ bad → (puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L ξ₀ F_eff) g = 1)
    (hHT : ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      Function.Bijective (HodgeTate.comparison p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion (realCyclotomicField N)))
        ((Representation.ofCharacter ((puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L ξ₀ F_eff).comp (localGaloisRestriction p (realCyclotomicField N) q))).restrictScalars
          ℚ_[p])))
    (hweights : ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ τ : q.adicCompletion (realCyclotomicField N) →ₐ[ℚ_[p]] AlgebraicClosure L,
      ∀ n : ℤ, n ≠ 0 → HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion (realCyclotomicField N)))
        (Representation.ofCharacter ((puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L ξ₀ F_eff).comp (localGaloisRestriction p (realCyclotomicField N) q))) n τ = ⊥)
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
  obtain ⟨n, hn, hpow⟩ := finite_order_of_labelledHodgeTate p
    ((algebraMap (w.adicCompletion E) L).comp (algebraMap E (w.adicCompletion E)))
    (puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L ξ₀ F_eff)
    (continuous_puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L ξ₀ F_eff)
    bad hunram hHT hweights
  apply exists_algebraic_character_comparing_darmon_localSystems_of_one_fiber
    N hN p m hm E hE w L hp ξ₀ F_eff F_gen ePath eGeom n hn
  exact hpow

end HilbertModularity.Hypergeometric
