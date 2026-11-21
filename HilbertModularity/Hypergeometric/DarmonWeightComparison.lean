/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.DarmonGenericComparison
public import HilbertModularity.Hypergeometric.DarmonHodgeComparison
public import HilbertModularity.RepresentationTheory.HodgeTateDeterminantAlgebraization

/-! # Rank-two Hodge–Tate route to the Darmon comparison

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

/-- The actual arithmetic fibre action in its canonical finite normed coordinates. -/
@[expose] def puncturedFiberCoordinateRepresentation
    (K : Type) [Field K] (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    (ξ : ProjectiveLine.Parameter K)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    Representation L (HilbertModularForms.AbsoluteGalois K)
      (Fin (Module.finrank L (F.toFunctor.obj (Scheme.etaleFiberPoint K
        (ProjectiveLine.punctured K) (ProjectiveLine.puncturedPoint K ξ)))) → L) :=
  (F.coordinateMonodromy (ProjectiveLine.puncturedPoint K ξ)).comp
    (Scheme.galoisToEtaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ))

/-- Finite-dimensional coordinates turn continuous orbit maps into a jointly
continuous action, retaining the original local-system topology. -/
theorem continuous_puncturedFiberCoordinateRepresentation
    (K : Type) [Field K] (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    (ξ : ProjectiveLine.Parameter K)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    Continuous (fun gv : HilbertModularForms.AbsoluteGalois K ×
      (Fin (Module.finrank L (F.toFunctor.obj (Scheme.etaleFiberPoint K
        (ProjectiveLine.punctured K) (ProjectiveLine.puncturedPoint K ξ)))) → L) =>
      puncturedFiberCoordinateRepresentation K L ξ F gv.1 gv.2) := by
  let ρ := puncturedFiberCoordinateRepresentation K L ξ F
  have hc : Continuous (fun g => (ρ g).toContinuousLinearMap) :=
    continuous_clm_apply.mpr fun v =>
      (F.continuous_coordinateMonodromy (ProjectiveLine.puncturedPoint K ξ) v).comp
        (Scheme.continuous_galoisToEtaleFundamentalGroup K
          (ProjectiveLine.puncturedPoint K ξ))
  exact (hc.comp continuous_fst).clm_apply continuous_snd

/-- Coordinates preserve the actual normalized arithmetic determinant. -/
theorem puncturedFiberCoordinateRepresentation_normalizedDeterminant
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L] [NormedAlgebra ℚ_[p] L]
    (ξ : ProjectiveLine.Parameter K)
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L) :
    (puncturedFiberCoordinateRepresentation K L ξ F).determinantCharacter *
      (Field.cyclotomicCharacterWithCoefficients K p L).toMonoidHom =
      puncturedFiberNormalizedDeterminant K p L ξ F := by
  let x := ProjectiveLine.puncturedPoint K ξ
  let a := Scheme.galoisToEtaleFundamentalGroup K x
  let e := ((F.coordinateMonodromyEquiv x).compHom a).symm
  have hd : (puncturedFiberCoordinateRepresentation K L ξ F).determinantCharacter =
      (puncturedFiberArithmeticRepresentation K ξ F).determinantCharacter := by
    ext g
    exact (LinearMap.det_conj _ e.toLinearEquiv).symm.trans
      (congrArg LinearMap.det (e.conj_apply_self g))
  rw [hd]
  exact (puncturedFiberNormalizedDeterminant_eq K p L ξ F).symm

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

/-- Weights `{0,1}` of the original rank-two arithmetic fibre imply one
finite algebraic comparison character at every nonsingular fibre. The finite
rank, finite exponent and determinant weight hypotheses are derived. The actual effective
family still must satisfy the geometric/path, ramification and Hodge inputs. -/
theorem exists_algebraic_character_comparing_darmon_localSystems_of_weights_zero_one
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
        (Representation.restrictScalars ℚ_[p]
          ((puncturedFiberCoordinateRepresentation (realCyclotomicField N) L ξ₀ F_eff).comp
            (localGaloisRestriction p (realCyclotomicField N) q)))))
    (hmult : ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})],
      ∀ (τ : q.adicCompletion (realCyclotomicField N) →ₐ[ℚ_[p]] AlgebraicClosure L)
        (n : ℤ),
      Module.finrank (AlgebraicClosure L) (HodgeTate.labelledWeightSpace p
        (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := q.adicCompletion (realCyclotomicField N)))
        ((puncturedFiberCoordinateRepresentation (realCyclotomicField N) L ξ₀ F_eff).comp
          (localGaloisRestriction p (realCyclotomicField N) q)) n τ) =
            (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0))
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
  let : IsModuleTopology ℚ_[p] (Fin (Module.finrank L (F_eff.toFunctor.obj
    (Scheme.etaleFiberPoint (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N))
      (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀)))) → L) :=
    isModuleTopologyOfFiniteDimensional
  have hd : Module.finrank L (F_eff.toFunctor.obj
      (Scheme.etaleFiberPoint (realCyclotomicField N)
        (ProjectiveLine.punctured (realCyclotomicField N))
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ₀))) = 2 :=
    ePath.toLinearEquiv.finrank_eq.symm.trans
      (eGeom.toLinearEquiv.finrank_eq.symm.trans
        (finrank_darmonCohomologicalFamily_at (RatFunc (realCyclotomicField N))
          N hN p m hm E hE w L
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))))
  obtain ⟨n, hn, hpow⟩ := finite_order_normalizedDeterminant_of_weights_zero_one p
    ((algebraMap (w.adicCompletion E) L).comp (algebraMap E (w.adicCompletion E)))
    (puncturedFiberCoordinateRepresentation (realCyclotomicField N) L ξ₀ F_eff)
    (continuous_puncturedFiberCoordinateRepresentation (realCyclotomicField N) L ξ₀ F_eff)
    (by simpa using hd) bad
    (by simpa only [puncturedFiberCoordinateRepresentation_normalizedDeterminant] using hunram)
    hHT hmult
  rw [puncturedFiberCoordinateRepresentation_normalizedDeterminant] at hpow
  apply exists_algebraic_character_comparing_darmon_localSystems_of_one_fiber
    N hN p m hm E hE w L hp ξ₀ F_eff F_gen ePath eGeom n hn
  simpa only [puncturedFiberNormalizedDeterminant_apply] using hpow

end HilbertModularity.Hypergeometric
