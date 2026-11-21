/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationHodgeTate
public import HilbertModularity.Hypergeometric.GaloisRealizationGenericFibre
public import HilbertModularity.Geometry.GroupScheme.HypergeometricCohomologyRigidity

/-! # Generic geometric monodromy of the selected Euler quotient

The generic local system is the generic restriction of the *same* chosen
quotient/descent, with an actual path comparison to the original rational
fibre. Its local classes are the external hypergeometric monodromy calculation
of [GPRV, Proposition 3.12 and Theorem 8.20]. The comparison with Darmon's
cohomological factor is deduced below using the checked rigidity theorem.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

/-- Generic restriction and geometric path compatibility for the local system
of one selected real Euler quotient. [GPRV, Theorem 9.2 and Proposition 9.5,
pp. 40–41] fix the quotient before choosing the coefficient place.
[src_milne_lec, Theorem 20.4, pp. 127–128] supplies smooth proper
specialization of its finite cohomology sheaves; [proetale2015, Lemma 4.2.12,
Corollary 5.1.6, Example 5.2.2, Definition 6.8.1 and Lemma 6.8.2(1)]
supplies the continuous rational-coefficient comparison. Finite norm/Leray
for the quotient and its fixed component is as in [src_milne_lec,
Proposition 8.3(c), Corollary 8.4, Exercise 12.3 and Theorem 12.7].

This literature interface is the existence of a generic restriction and its
path map. It does not assert a Darmon comparison or finite-order character.
The source passages do not state this project's `EtaleLocalSystem` API
verbatim; the interface records their application to the selected smooth
proper quotient and its fixed coefficient component. -/
theorem exists_genericLocalSystem_of_commonRealEulerQuotient
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let D := R.placeDescent N m 𝒞 p L ι
    ∃ F_gen : Scheme.EtaleLocalSystem.{0,0,0} (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) L,
      Nonempty (Representation.Equiv
        (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
          (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
        ((puncturedFiberMonodromy (realCyclotomicField N) ξ D.localSystem).comp
          (Scheme.geometricFiberPathGroupEquiv _ _
            (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
              (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ))).toMonoidHom)) := by
  sorry

/-- [GPRV, Proposition 3.12 and Theorem 8.20] identify the three oriented
local classes of the actual generic Euler realization and its geometric
irreducibility under condition `(Irr)`. For the symmetric coprime datum, `(Irr)` follows from the
scaled gcd-one certificate `symmetricParameters_irreducible` and [GPRV,
Lemma 8.5, p. 30]. The parameter `F_gen` is required to be the path-compatible
generic restriction of the *selected* quotient realization, and the displayed
coefficient equation prevents a second exponent relabelling.

These are local-class and irreducibility inputs only. In particular GPRV does
not assert the Darmon comparison which is deduced from them by the project's
rigidity theorem. -/
theorem commonRealEulerQuotient_generic_localMonodromy_of_coprime
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (hcop) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_gen : Scheme.EtaleLocalSystem.{0,0,0} (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ePath : Nonempty (Representation.Equiv
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ
        (R.placeDescent N m 𝒞 p L ι).localSystem).comp
        (Scheme.geometricFiberPathGroupEquiv _ _
          (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
            (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ))).toMonoidHom))) :
    (∀
      (γ c : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
        RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N)))
      (ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N))),
      (∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map
             (MulAut.conj (c i)).toMonoidHom) →
      ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ →
      ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1) →
      ProjectiveLine.HasStandardLocalMonodromy N L
        (coefficientEmbeddingAbovePrime N m
          (hcop) E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
          w L) F_gen γ) ∧
    (let xgen := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
     let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
       (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor xgen
     let k := (Scheme.etaleFundamentalGroupMap
       (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
       (RatFunc (realCyclotomicField N)) xgen).ker.subtype
     Representation.IsIrreducible (ρ.comp k)) := by
  sorry

/-- [GPRV, Proposition 3.12 and Theorem 8.20] identify the three oriented
local classes of the actual generic Euler realization and its geometric
irreducibility under condition `(Irr)`. For the symmetric odd coprime datum, `(Irr)` follows from the
scaled gcd-one certificate `symmetricParameters_irreducible` and [GPRV,
Lemma 8.5, p. 30]. The parameter `F_gen` is required to be the path-compatible
generic restriction of the *selected* quotient realization, and the displayed
coefficient equation prevents a second exponent relabelling.

These are local-class and irreducibility inputs only. In particular GPRV does
not assert the Darmon comparison which is deduced from them by the project's
rigidity theorem. -/
theorem commonRealEulerQuotient_generic_localMonodromy_of_odd_coprime
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (_hOdd : Odd N) (hmPos : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (hcop) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_gen : Scheme.EtaleLocalSystem.{0,0,0} (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ePath : Nonempty (Representation.Equiv
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ
        (R.placeDescent N m 𝒞 p L ι).localSystem).comp
        (Scheme.geometricFiberPathGroupEquiv _ _
          (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
            (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ))).toMonoidHom))) :
    (∀
      (γ c : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
        RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N)))
      (ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N))),
      (∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map
             (MulAut.conj (c i)).toMonoidHom) →
      ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ →
      ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1) →
      ProjectiveLine.HasStandardLocalMonodromy N L
        (coefficientEmbeddingAbovePrime N m
          (hcop) E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
          w L) F_gen γ) ∧
    (let xgen := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
     let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
       (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor xgen
     let k := (Scheme.etaleFundamentalGroupMap
       (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
       (RatFunc (realCyclotomicField N)) xgen).ker.subtype
     Representation.IsIrreducible (ρ.comp k)) := by
  exact commonRealEulerQuotient_generic_localMonodromy_of_coprime
    N m p h3 hmPos hmN hcop E hE w L 𝒞 R ι hι ξ F_gen ePath

/-- The prime conductor monodromy interface is a specialization of the
odd coprime GPRV local-class and irreducibility result. -/
theorem commonRealEulerQuotient_generic_localMonodromy
    (N m p : ℕ) [NeZero N] [Fact N.Prime] [Fact p.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N))
    (F_gen : Scheme.EtaleLocalSystem.{0,0,0} (RatFunc (realCyclotomicField N))
      (ProjectiveLine.punctured (realCyclotomicField N)) L)
    (ePath : Nonempty (Representation.Equiv
      (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
      ((puncturedFiberMonodromy (realCyclotomicField N) ξ
        (R.placeDescent N m 𝒞 p L ι).localSystem).comp
        (Scheme.geometricFiberPathGroupEquiv _ _
          (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
            (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ))).toMonoidHom))) :
    (∀
      (γ c : Fin 3 → AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[
        RatFunc (realCyclotomicField N)] AlgebraicClosure (RatFunc (realCyclotomicField N)))
      (ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N))),
      (∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map
             (MulAut.conj (c i)).toMonoidHom) →
      ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ →
      ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1) →
      ProjectiveLine.HasStandardLocalMonodromy N L
        (coefficientEmbeddingAbovePrime N m
          (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
          ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
          w L) F_gen γ) ∧
    (let xgen := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
     let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
       (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor xgen
     let k := (Scheme.etaleFundamentalGroupMap
       (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
       (RatFunc (realCyclotomicField N)) xgen).ker.subtype
     Representation.IsIrreducible (ρ.comp k)) := by
  have hOdd : Odd N := hN.odd_of_ne_two (by omega)
  let hcop := eulerExponent_coprime_of_prime N m hN hmPos hmN
  exact commonRealEulerQuotient_generic_localMonodromy_of_odd_coprime
    N m p (le_trans (by decide : 3 ≤ 5) h5) hOdd hmPos hmN hcop
    E hE w L 𝒞 R ι hι ξ F_gen ePath

/-- The manuscript's one-fibre determinant argument applied to the actual
selected effective Euler local system at the conductor prime. The generic
Euler input supplies only its own path and local monodromy; the comparison
with Darmon's fixed labelled cohomological factor is proved by rigidity.
The finite exceptional set is constructed from the actual parameter, and
the original-fibre Hodge comparison is the named external input above.

The resulting finite algebraic comparison character is one character for
every nonsingular fibre of this same selected descent. -/
theorem exists_algebraic_character_comparing_selectedEuler_realization
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[N] L]
    (𝒞 : SmoothProperEulerFamily N m)
    (R : CommonRealEulerQuotientRealization N m 𝒞)
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let D := R.placeDescent N m 𝒞 N L ι
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
                    N (le_trans (by decide : 3 ≤ 5) h5) N m
                    (eulerExponent_coprime_of_prime N m hN hmPos hmN)
                    E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation
                    (realCyclotomicField N) ξ D.localSystem)) := by
  let h3 : 3 ≤ N := le_trans (by decide : 3 ≤ 5) h5
  let hmcp : m.Coprime N :=
    eulerExponent_coprime_of_prime N m hN hmPos hmN
  let D := R.placeDescent N m 𝒞 N L ι
  obtain ⟨F_gen, ⟨ePath⟩⟩ :=
    exists_genericLocalSystem_of_commonRealEulerQuotient N m N 𝒞 R L ι ξ₀
  obtain ⟨hlocal, hirred⟩ :=
    commonRealEulerQuotient_generic_localMonodromy N m N hN h5 hmPos hmN
      E hE w L 𝒞 R ι hι ξ₀ F_gen ⟨ePath⟩
  obtain ⟨eGeom⟩ :=
    darmonCohomologicalFamily_geometricEquiv_of_localMonodromy
      N h3 N m hmcp E hE w L (by omega) F_gen hlocal hirred
  let : IsScalarTower ℚ ℚ_[N] L :=
    IsScalarTower.to₁₂₄ ℚ ℚ_[N] (w.adicCompletion E) L
  obtain ⟨hHT, hmult⟩ :=
    commonRealEulerQuotientRealization_labelledHodgeTate
      N m N hN h5 hmPos hmN 𝒞 R L ι ξ₀
  have hunram :
      ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
        (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N)))),
        Q.IsMaximal → Q.LiesOver q.asIdeal →
        ∀ g : HilbertModularForms.AbsoluteGalois (realCyclotomicField N),
          g ∈ Q.inertia (HilbertModularForms.AbsoluteGalois
            (realCyclotomicField N)) →
          q ∉ properEulerBadPrimes N N hN ξ₀ →
          puncturedFiberNormalizedDeterminant (realCyclotomicField N) N L
            ξ₀ D.localSystem g = 1 := by
    intro q Q hQ hOver g hg hq
    let : Q.IsMaximal := hQ
    let : Q.LiesOver q.asIdeal := hOver
    exact D.normalizedDeterminant_inertia_eq_one N m N L ι hN h5 hmPos
      hmN 𝒞 ξ₀ q Q g hg hq
  exact exists_algebraic_character_comparing_darmon_localSystems_of_weights_zero_one
    N h3 N m hmcp E hE w L h5 ξ₀ D.localSystem F_gen ePath eGeom
    (properEulerBadPrimes N N hN ξ₀) hunram hHT hmult

/-- Apply the preceding deduction to the project's single chosen exponent-`m`
Euler family and its single chosen quotient over the real parameter line.
The coefficient embedding is fixed before either generic comparison or
specialization. The only admissions in this theorem's cone are the named
geometric, cohomological and Hodge literature interfaces. -/
theorem exists_algebraic_character_comparing_chosenEuler_realization
    (N m : ℕ) [NeZero N] [Fact N.Prime]
    (hN : N.Prime) (h5 : 5 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (E : IntermediateField ℚ Qbar) [NumberField E]
    (hE : IntermediateField.normalClosure ℚ (realCyclotomicField N) Qbar ≤ E)
    (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver (Ideal.span {(N : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion E) L]
    [ContinuousSMul (w.adicCompletion E) L]
    [NormedAlgebra ℚ_[N] L] [FiniteDimensional ℚ_[N] L]
    [IsScalarTower ℚ_[N] (w.adicCompletion E) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion E) L]
    [IsScalarTower ℚ ℚ_[N] L]
    (ι : cyclotomicField N →+* L)
    (hι : coefficientEmbeddingAbovePrime N m
        (eulerExponent_coprime_of_prime N m hN hmPos hmN) E
        ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
        w L (tau N 1) =
      ι ((root N) ^ m + (root N)⁻¹ ^ m))
    (ξ₀ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenSmoothProperEulerFamily N m hN h5 hmPos hmN
    let R := chosenCommonRealEulerQuotientRealization N m 𝒞 hN h5 hmPos hmN
    let D := R.placeDescent N m 𝒞 N L ι
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
                    N (le_trans (by decide : 3 ≤ 5) h5) N m
                    (eulerExponent_coprime_of_prime N m hN hmPos hmN)
                    E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation
                    (realCyclotomicField N) ξ D.localSystem)) := by
  exact exists_algebraic_character_comparing_selectedEuler_realization
    N m hN h5 hmPos hmN E hE w L
      (chosenSmoothProperEulerFamily N m hN h5 hmPos hmN)
      (chosenCommonRealEulerQuotientRealization N m
        (chosenSmoothProperEulerFamily N m hN h5 hmPos hmN)
        hN h5 hmPos hmN)
      ι hι ξ₀

end HilbertModularity.Hypergeometric
