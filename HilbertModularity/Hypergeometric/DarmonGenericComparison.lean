/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.DarmonAlgebraicComparison
public import HilbertModularity.Hypergeometric.DarmonDeterminantNormalization
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomologyRigidity

/-! # Algebraic comparison from the generic geometric factor

Transport the chosen labelled comparison before arithmetic descent and
specialization, as in [TripathiGoswamiRevised, Theorem RMgeneral].
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry IsDedekindDomain
open scoped NumberField CategoryTheory.MonObj
namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic

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

omit [FiniteDimensional ℚ_[p] L] in
/-- The generic geometric comparison in [TripathiGoswamiRevised,
Theorem RMgeneral, steps 2–5] yields one algebraic comparison character at every
nonsingular fibre. Transport to the arithmetic kernel is proved internally.
The effective generic and rational systems must be linked by the actual path
comparison; normalized arithmetic determinants remain explicit hypotheses. -/
theorem exists_algebraic_character_comparing_darmon_localSystems_of_generic
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
  have hKernel := darmonCohomologicalFamily_arithmeticKernel_equiv_of_generic
    N hN p m hm E hE w L ξ₀ F_gen F_eff
  dsimp only at hKernel
  specialize hKernel ePath
  specialize hKernel eGeom
  obtain ⟨eKernel⟩ := hKernel
  exact exists_algebraic_character_comparing_darmon_localSystems_of_determinants
    N hN p m hm E hE w L ξ₀ F_eff eKernel ε hRMdet n hn hEffdet

omit [FiniteDimensional ℚ_[p] L] in
/-- The comparison normalized by the actual covariant Tate determinant. The
RM-side determinant premise is proved by duality. At prime conductors at least
five, `darmonTateDeterminantCharacter_along_arithmeticPath` identifies its
restriction at every nonsingular arithmetic fibre with the cyclotomic character.
The effective geometric comparison and finite-order determinant ratio remain
explicit application hypotheses. -/
theorem exists_algebraic_character_comparing_darmon_localSystems_of_tate_determinant
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
    (n : ℕ) (hn : 0 < n)
    (hEffdet : ∀ g, ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff).determinantCharacter g *
      darmonTateDeterminantCharacter N hN p m hm E hE w L ξ₀ g) ^ n = 1)
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
  exact exists_algebraic_character_comparing_darmon_localSystems_of_generic
    N hN p m hm E hE w L ξ₀ F_eff F_gen ePath eGeom
    (darmonTateDeterminantCharacter N hN p m hm E hE w L ξ₀)
    (darmonCohomologicalFamily_det_mul_tateDeterminant N hN p m hm E hE w L ξ₀)
    n hn hEffdet

omit [FiniteDimensional ℚ_[p] L] in
/-- At prime conductor at least five, the arithmetic comparison needs a
finite-exponent determinant bound at just one nonsingular fibre, normalized
by the actual cyclotomic character. Geometric equivalence propagates that bound
to the fundamental group; descent then constructs the same finite algebraic
character at every fibre. This implements the one-fibre reduction of
[TripathiGoswamiRevised, Theorem RMgeneral, steps 3–5] by the sufficient
determinant route. The effective generic comparison and path compatibility
remain application hypotheses. -/
theorem exists_algebraic_character_comparing_darmon_localSystems_of_one_fiber
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
    (n : ℕ) (hn : 0 < n)
    (hEffdet : ∀ g, ((puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ₀ F_eff).determinantCharacter g *
      Field.cyclotomicCharacterWithCoefficients (realCyclotomicField N) p L g) ^ n = 1)
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
  have hKernel := darmonCohomologicalFamily_arithmeticKernel_equiv_of_generic
    N hN p m hm E hE w L ξ₀ F_gen F_eff
  dsimp only at hKernel
  obtain ⟨eKernel⟩ := hKernel ePath eGeom
  apply exists_algebraic_character_comparing_darmon_localSystems_of_determinants
    N hN p m hm E hE w L ξ₀ F_eff eKernel
    (darmonTateDeterminantCharacter N hN p m hm E hE w L ξ₀)
    (darmonCohomologicalFamily_det_mul_tateDeterminant N hN p m hm E hE w L ξ₀)
    n hn
  apply determinant_power_eq_one_of_section
    (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀)
    (Scheme.galoisToEtaleFundamentalGroup (realCyclotomicField N)
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀))
    (puncturedArithmeticProjection_galois (realCyclotomicField N) ξ₀)
    _ _ eKernel _
    (darmonCohomologicalFamily_det_mul_tateDeterminant N hN p m hm E hE w L ξ₀)
  intro g
  rw [darmonTateDeterminantCharacter_arithmetic N hN p m hm E hE w L ξ₀ hp]
  exact hEffdet g

end HilbertModularity.Hypergeometric
