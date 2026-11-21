/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.DarmonCohomologicalHodgeTate
public import HilbertModularity.Hypergeometric.ComparisonCharacterWeights

/-! # Arithmetic Darmon comparison from the original fibre's Hodge data

The general Darmon family's Hodge weights and finite ramification are already
proved applications of named literature inputs. Geometric comparison then
constructs one finite algebraic character using the weights of both families
at one actual arithmetic fibre. No prime-conductor determinant formula is
needed in this deduction of [TripathiGoswamiRevised, Theorem `thm:RMgeneral`].
-/

public noncomputable section

open AlgebraicGeometry NumberField IsDedekindDomain NumberField.LocalGalois
attribute [local instance] completionPadicAlgebra completionPadicTower
  completionComplexAlgebra completionComplexTower completionComplexRationalTower

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

private theorem puncturedFiberMonodromy_determinant_galois
    (K : Type*) [Field K] [CharZero K] (ξ : ProjectiveLine.Parameter K)
    {L : Type*} [Field L] [TopologicalSpace L]
    (F : Scheme.EtaleLocalSystem K (ProjectiveLine.punctured K) L)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (puncturedFiberMonodromy K ξ F).determinantCharacter
        (Scheme.galoisToEtaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ) g) =
      (puncturedFiberArithmeticRepresentation K ξ F).determinantCharacter g := by
  rfl

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
  [IsScalarTower ℚ ℚ_[p] L]

/-- The normalized determinant of the actual Darmon fibre has finite order
at every conductor. This uses its derived Hodge weights and finite ramification,
not an exact determinant formula. -/
theorem finite_order_darmonFiberNormalizedDeterminant
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    ∃ n : ℕ, 0 < n ∧ ∀ g,
      (puncturedFiberNormalizedDeterminant (realCyclotomicField N) p L ξ
        (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L) g) ^ n = 1 := by
  classical
  let K := realCyclotomicField N
  let F := darmonCohomologicalFamily K N hN p m hm E hE w L
  let x := ProjectiveLine.puncturedPoint K ξ
  let ρ := puncturedFiberCoordinateRepresentation K L ξ F
  let : IsModuleTopology ℚ_[p] (Fin (Module.finrank L (F.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x))) → L) :=
    isModuleTopologyOfFiniteDimensional
  have hd : Module.finrank L (F.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)) = 2 :=
    finrank_darmonCohomologicalFamily_at K N hN p m hm E hE w L x
  obtain ⟨bad, hbad, hu⟩ :=
    darmonCohomologicalFamily_unramifiedOutsideFinite K N hN p m hm E hE w L x
  let e := (F.coordinateMonodromyEquiv x).symm.compHom
    (Scheme.galoisToEtaleFundamentalGroup K x)
  obtain ⟨bad', hu'⟩ := normalizedDeterminant_unramifiedOutsideFinite p ρ hbad.toFinset
    (fun q Q hQ hQq g hg hq => by
      let : Q.IsMaximal := hQ
      let : Q.LiesOver q.asIdeal := hQq
      apply LinearMap.ext
      intro v
      apply e.toLinearEquiv.injective
      exact (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v).trans
        (congrArg (fun f => f (e v))
          (hu q (by simpa using hq) q.asIdeal rfl Q g hg)))
  have hw := darmonCohomologicalFamily_labelledHodgeTate N hN p m hm E hE w L ξ
  obtain ⟨n, hn, hpow⟩ := finite_order_normalizedDeterminant_of_weights_zero_one p
    ((algebraMap (w.adicCompletion E) L).comp (algebraMap E (w.adicCompletion E)))
    ρ (continuous_puncturedFiberCoordinateRepresentation K L ξ F)
    (by simpa using hd) bad' hu' hw.1 hw.2
  refine ⟨n, hn, ?_⟩
  intro g
  rw [puncturedFiberCoordinateRepresentation_normalizedDeterminant] at hpow
  exact hpow g

/-- The same algebraic character compares every fibre of the supplied
geometric counterpart of the actual chosen Darmon family. Only the other
family's finite ramification and original labelled Hodge data are hypotheses;
all Darmon-side arithmetic properties and character finiteness are derived.
Finite ramification of the other normalized determinant is sufficient. -/
theorem exists_algebraic_character_comparing_darmon_localSystems_of_hodgeTate
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_eff : Scheme.EtaleLocalSystem (realCyclotomicField N)
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (eGeom : Representation.Equiv
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀
        (darmonCohomologicalFamily (realCyclotomicField N) N hN p m hm E hE w L)).comp
          (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype)
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ₀ F_eff).comp
        (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ₀).ker.subtype))
    (bad : Finset (HeightOneSpectrum (𝓞 (realCyclotomicField N))))
    (hunram : ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N)))),
      Q.IsMaximal → Q.LiesOver q.asIdeal →
      ∀ g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N),
        g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois (realCyclotomicField N)) →
          q ∉ bad → puncturedFiberNormalizedDeterminant
            (realCyclotomicField N) p L ξ₀ F_eff g = 1)
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
        let : Algebra E L := ((algebraMap (w.adicCompletion E) L).comp
          (algebraMap E (w.adicCompletion E))).toAlgebra
        let E' := RepresentationTheory.finiteCharacterCoefficientField (E₀ := E) ν
        let : NumberField E' :=
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
  let F_RM := darmonCohomologicalFamily K N hN p m hm E hE w L
  let x := ProjectiveLine.puncturedPoint K ξ₀
  let eRM := (F_RM.coordinateMonodromyEquiv x).symm
  let eEff := (F_eff.coordinateMonodromyEquiv x).symm
  let k := (puncturedArithmeticProjectionHom K ξ₀).ker.subtype
  have eGeom' := (eRM.compHom k).trans (eGeom.trans (eEff.symm.compHom k))
  have hdim : Module.finrank L (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)) = 2 :=
    finrank_darmonCohomologicalFamily_at K N hN p m hm E hE w L x
  have hdimCoord : Module.finrank L (Fin (Module.finrank L (F_RM.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x))) → L) = 2 := by
    simpa using hdim
  have hdimEff : Module.finrank L (F_eff.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x)) = 2 := by
    simpa using eGeom'.toLinearEquiv.finrank_eq.symm.trans hdimCoord
  let : IsModuleTopology ℚ_[p] (Fin (Module.finrank L (F_eff.toFunctor.obj
      (Scheme.etaleFiberPoint K (ProjectiveLine.punctured K) x))) → L) :=
    isModuleTopologyOfFiniteDimensional
  obtain ⟨n0, hn0, hpow0⟩ := finite_order_darmonFiberNormalizedDeterminant
    N hN p m hm E hE w L ξ₀
  obtain ⟨n1, hn1, hpow1⟩ := finite_order_normalizedDeterminant_of_weights_zero_one p
    ((algebraMap (w.adicCompletion E) L).comp (algebraMap E (w.adicCompletion E)))
    (puncturedFiberCoordinateRepresentation K L ξ₀ F_eff)
    (continuous_puncturedFiberCoordinateRepresentation K L ξ₀ F_eff)
    (by simpa using hdimEff) bad
    (by simpa only [puncturedFiberCoordinateRepresentation_normalizedDeterminant] using hunram)
    hHT hmult
  rw [puncturedFiberCoordinateRepresentation_normalizedDeterminant] at hpow1
  let ρ0 := puncturedFiberMonodromy K ξ₀ F_RM
  let ρ1 := puncturedFiberMonodromy K ξ₀ F_eff
  let ε := ρ0.determinantCharacter⁻¹
  have hnorm : ∀ g, ρ0.determinantCharacter g * ε g = 1 := fun g => mul_inv_cancel _
  apply exists_algebraic_character_comparing_darmon_localSystems_of_determinants
    N hN p m hm E hE w L ξ₀ F_eff eGeom ε hnorm (n0 * n1) (Nat.mul_pos hn0 hn1)
  apply determinant_power_eq_one_of_section (puncturedArithmeticProjectionHom K ξ₀)
    (Scheme.galoisToEtaleFundamentalGroup K x) (puncturedArithmeticProjection_galois K ξ₀)
    ρ0 ρ1 eGeom ε hnorm (n0 * n1)
  intro g
  have heq : ρ1.determinantCharacter (Scheme.galoisToEtaleFundamentalGroup K x g) *
      ε (Scheme.galoisToEtaleFundamentalGroup K x g) =
      puncturedFiberNormalizedDeterminant K p L ξ₀ F_eff g /
        puncturedFiberNormalizedDeterminant K p L ξ₀ F_RM g := by
    rw [puncturedFiberNormalizedDeterminant_apply, puncturedFiberNormalizedDeterminant_apply]
    change ρ1.determinantCharacter (Scheme.galoisToEtaleFundamentalGroup K x g) *
        (ρ0.determinantCharacter (Scheme.galoisToEtaleFundamentalGroup K x g))⁻¹ = _
    simp [ρ0, ρ1, x,
      div_eq_mul_inv, mul_inv_rev, mul_assoc]
    exact congrArg₂ (· * ·) (puncturedFiberMonodromy_determinant_galois K ξ₀ F_eff g)
      (congrArg Inv.inv (puncturedFiberMonodromy_determinant_galois K ξ₀ F_RM g))
  have hleft : (puncturedFiberNormalizedDeterminant K p L ξ₀ F_eff g) ^ (n0 * n1) = 1 := by
    rw [Nat.mul_comm n0 n1, pow_mul, hpow1 g, one_pow]
  have hright : (puncturedFiberNormalizedDeterminant K p L ξ₀ F_RM g) ^ (n0 * n1) = 1 := by
    rw [pow_mul, hpow0 g, one_pow]
  rw [heq, div_pow, hleft, hright]
  simp

end HilbertModularity.Hypergeometric
