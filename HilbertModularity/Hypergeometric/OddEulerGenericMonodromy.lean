/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.OddEulerRealization
public import HilbertModularity.Hypergeometric.GaloisRealizationGenericMonodromy

/-! # Generic geometry of the one selected odd Euler quotient

The generic local system is obtained from the same chosen quotient used in
all fibres. Its oriented inertia classes and geometric irreducibility come
from the GPRV source interface at the fixed exponent label.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

/-- The actual chosen odd coprime quotient has a path-compatible generic
local system with the three common-oriented hypergeometric local classes
and an irreducible geometric restriction. This uses [GPRV, Proposition
3.12, Theorem 8.20] after the `(Irr)` check of Lemma 8.5, p. 30; the
source does not provide a Darmon comparison. -/
theorem exists_chosenOddEulerGenericLocalMonodromy
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hOdd : Odd N) (hmPos : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [Algebra (w.adicCompletion (cyclotomicField N)) L]
    [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField N)) L]
    [Algebra ℚ L]
    [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let E := cyclotomicField N
    let hE := realCyclotomicNormalClosure_le_full_of_neZero N
    let 𝒞 := chosenOddEulerFamily N m h3 hOdd hmPos hmN hcop
    let R := chosenOddEulerRealization N m h3 hOdd hmPos hmN hcop
    let ι := oddEulerCoefficientMap N w L
    ∃ F_gen : Scheme.EtaleLocalSystem.{0,0,0} (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N)) L,
      Nonempty (Representation.Equiv
        (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
          (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
        ((puncturedFiberMonodromy (realCyclotomicField N) ξ
          (R.placeDescent N m 𝒞 p L ι).localSystem).comp
          (Scheme.geometricFiberPathGroupEquiv _ _
            (ProjectiveLine.puncturedGenericFiberPath (realCyclotomicField N)
              (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ))).toMonoidHom)) ∧
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
          (coefficientEmbeddingAbovePrime N m hcop E
            ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE)
            w L) F_gen γ) ∧
      (let xgen := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
       let ρ := Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
         (ProjectiveLine.punctured (realCyclotomicField N)) F_gen.algebraicFunctor xgen
       let k := (Scheme.etaleFundamentalGroupMap
         (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
         (RatFunc (realCyclotomicField N)) xgen).ker.subtype
       Representation.IsIrreducible (ρ.comp k)) := by
  let 𝒞 := chosenOddEulerFamily N m h3 hOdd hmPos hmN hcop
  let R := chosenOddEulerRealization N m h3 hOdd hmPos hmN hcop
  let E := cyclotomicField N
  let hE := realCyclotomicNormalClosure_le_full_of_neZero N
  let ι := oddEulerCoefficientMap N w L
  obtain ⟨F_gen, ePath⟩ :=
    exists_genericLocalSystem_of_commonRealEulerQuotient N m p 𝒞 R L ι ξ
  have hlocal := commonRealEulerQuotient_generic_localMonodromy_of_odd_coprime
    N m p h3 hOdd hmPos hmN hcop E hE w L 𝒞 R ι
    (oddEulerCoefficientMap_tau_one N m hcop w L) ξ F_gen ePath
  exact ⟨F_gen, ePath, hlocal.1, hlocal.2⟩

end HilbertModularity.Hypergeometric
