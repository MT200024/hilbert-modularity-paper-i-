/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.DarmonHodgeAlgebraicComparison
public import HilbertModularity.Hypergeometric.CoprimeEulerGenericMonodromy
import HilbertModularity.Geometry.Etale.ParameterInvolution

/-! # One arithmetic comparison character for every coprime raw Euler fibre

The actual chosen Euler quotient supplies its geometric local classes,
ramification and labelled Hodge weights. The general Darmon Hodge application
and two-sided character argument then give a single algebraic character,
chosen before all nonsingular fibres, at the fixed coefficient realization.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

/-- The fixed-label arithmetic comparison of [TripathiGoswamiRevised,
Theorem `thm:RMgeneral`] for all coprime conductors, before the finite κ normalization.
Every coefficient prime is permitted, including two, by the characteristic-zero
rigidity input [YunRigid2014, Proposition 3.2.7 and Theorem 3.2.8]. No comparison, determinant, ramification or Hodge premise is
supplied for either chosen family. The same character works at every fibre. -/
theorem exists_algebraic_character_comparing_chosenCoprimeRawEuler
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]
    [IsScalarTower ℚ ℚ_[p] L] :
    let E := cyclotomicField N
    let hE := realCyclotomicNormalClosure_le_full_of_neZero N
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
    let D := R.placeDescent N m 𝒞 p L (coprimeEulerCoefficientMap N w L)
    ∃ ν : HilbertModularForms.AbsoluteGalois (realCyclotomicField N) →* Lˣ,
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
                    N h3 p m hcop E hE w L))).Equiv
                  (puncturedFiberArithmeticRepresentation (realCyclotomicField N) ξ D.localSystem)) := by
  let K := realCyclotomicField N
  let E := cyclotomicField N
  let hE := realCyclotomicNormalClosure_le_full_of_neZero N
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
  let ι := coprimeEulerCoefficientMap N w L
  let D := R.placeDescent N m 𝒞 p L ι
  let ξ₀ := ProjectiveLine.midpointParameter K
  obtain ⟨F_gen, ⟨ePath⟩, hlocal, hirr⟩ :=
    exists_chosenCoprimeEulerGenericLocalMonodromy
      N m p h3 hmPos hmN hcop w L ξ₀
  obtain ⟨eGeom⟩ := darmonCohomologicalFamily_geometricEquiv_of_localMonodromy_charZero
    N h3 p m hcop E hE w L F_gen hlocal hirr
  obtain ⟨eKernel⟩ := darmonCohomologicalFamily_arithmeticKernel_equiv_of_generic
    N h3 p m hcop E hE w L ξ₀ F_gen D.localSystem ePath eGeom
  have hweights := commonRealEulerQuotientRealization_labelledHodgeTate_of_coprime
    N m p h3 hmPos hmN hcop 𝒞 R L ι ξ₀
  apply exists_algebraic_character_comparing_darmon_localSystems_of_hodgeTate
    N h3 p m hcop E hE w L ξ₀ D.localSystem eKernel
      (properEulerBadPrimesOfConductor N p ξ₀) ?_ hweights.1 hweights.2
  intro q Q hQ hQq g hg hq
  let : Q.IsMaximal := hQ
  let : Q.LiesOver q.asIdeal := hQq
  exact D.normalizedDeterminant_inertia_eq_one_of_coprime
    N m p L ι h3 hmPos hmN hcop 𝒞 ξ₀ q Q g hg hq

end HilbertModularity.Hypergeometric
