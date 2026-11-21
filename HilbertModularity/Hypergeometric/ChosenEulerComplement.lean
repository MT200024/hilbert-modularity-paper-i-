/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GeometricComplement
public import HilbertModularity.Hypergeometric.CoprimeEulerGenericMonodromy
public import HilbertModularity.Hypergeometric.ComplementCharacter
public import HilbertModularity.Hypergeometric.EffectiveEulerRealization

/-! # Complement comparison of the actual chosen Euler family

The chosen quotient supplies its oriented GPRV local classes. Cusp-swap
rigidity proves the geometric comparison, and the fixed midpoint makes the
single arithmetic comparison character quadratic.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField

namespace HilbertModularity.Hypergeometric
open HilbertModularity.Cyclotomic

variable (N m p : ℕ) [NeZero N] [Fact p.Prime]
  (h3 : 3 ≤ N) (hmPos : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
  (w : HeightOneSpectrum (𝓞 (cyclotomicField N)))
  [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
  (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
  [Algebra (w.adicCompletion (cyclotomicField N)) L]
  [ContinuousSMul (w.adicCompletion (cyclotomicField N)) L]
  [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsScalarTower ℚ_[p] (w.adicCompletion (cyclotomicField N)) L]
  [Algebra ℚ L] [IsScalarTower ℚ (w.adicCompletion (cyclotomicField N)) L]

/-- The actual chosen raw Euler family is geometrically isomorphic to its
actual complement pullback, and its geometric action is absolutely irreducible.
This proves the geometric deduction of [TripathiGoswamiRevised,
Lemma `lem:involution`] for every coprime conductor and coefficient prime. -/
theorem chosenCoprimeRawEuler_geometricComplement :
    let K := realCyclotomicField N
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
    let F := (R.placeDescent N m 𝒞 p L (coprimeEulerCoefficientMap N w L)).localSystem
    let ξ₀ := ProjectiveLine.midpointParameter K
    let k := (puncturedArithmeticProjectionHom K ξ₀).ker.subtype
    Nonempty (Representation.Equiv ((puncturedFiberMonodromy K ξ₀ F).comp k)
      ((puncturedFiberMonodromy K ξ₀ (F.complementPullback K L)).comp k)) ∧
      (Representation.baseChange (AlgebraicClosure L)
        ((puncturedFiberMonodromy K ξ₀ F).comp k)).IsIrreducible := by
  let K := realCyclotomicField N
  let E := cyclotomicField N
  let hE := realCyclotomicNormalClosure_le_full_of_neZero N
  let σ := coefficientEmbeddingAbovePrime N m hcop E
    ((IntermediateField.le_normalClosure (realCyclotomicField N)).trans hE) w L
  let ι := coprimeEulerCoefficientMap N w L
  have hroot : IsPrimitiveRoot (ι (root N)) N :=
    (root_isPrimitiveRoot N).map_of_injective ι.injective
  have hτ : σ (tau N 1) ≠ 2 := by
    rw [coprimeEulerCoefficientMap_tau_one N m hcop w L]
    simpa only [map_add, map_pow, map_inv₀] using Monodromy.tau_ne_two h3 hroot hcop
  obtain ⟨Fgen, ⟨ePath⟩, hlocal, _⟩ :=
    exists_chosenCoprimeEulerGenericLocalMonodromy N m p h3 hmPos hmN hcop w L
      (ProjectiveLine.midpointParameter K)
  let C := Classical.choice (ProjectiveLine.exists_complementCuspGenerators N h3)
  exact geometricComplementEquiv_of_standardLocalMonodromy N C L σ hτ
    _ Fgen ePath (hlocal C.gamma C.conjugator C.roots C.inertia C.orientation C.label)

/-- One continuous quadratic character compares the actual raw Euler fibres
at `ξ` and `1-ξ`, before the parameter is chosen. No geometric intertwiner,
Hodge comparison, purity, or finite-order character is supplied as a premise. -/
theorem exists_quadratic_character_chosenCoprimeRawEuler_complement :
    let K := realCyclotomicField N
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
    let F := (R.placeDescent N m 𝒞 p L (coprimeEulerCoefficientMap N w L)).localSystem
    ∃ ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ,
      Continuous ν ∧ ν ^ 2 = 1 ∧ (Set.range ν).Finite ∧
      ∀ ξ : ProjectiveLine.Parameter K,
        Nonempty (((Representation.ofCharacter ν).tprod
          (puncturedFiberArithmeticRepresentation K ξ F)).Equiv
            (puncturedFiberArithmeticRepresentation K
              (ProjectiveLine.complementParameter K ξ) F)) := by
  let K := realCyclotomicField N
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
  let F := (R.placeDescent N m 𝒞 p L (coprimeEulerCoefficientMap N w L)).localSystem
  obtain ⟨⟨e⟩, hAbs⟩ := chosenCoprimeRawEuler_geometricComplement
    N m p h3 hmPos hmN hcop w L
  let _ := hAbs
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact exists_quadratic_character_of_geometric_complement K L F
    (chosenCoprimeRawEulerRealization_rank_two N m h3 hmPos hmN hcop p L
      (coprimeEulerCoefficientMap N w L) (ProjectiveLine.midpointParameter K)) e

private def tensorComparisonSameTwist
    {L G V W : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρ : Representation L G V) (σ : Representation L G W)
    (ν κ : G →* Lˣ) (e : ((Representation.ofCharacter ν).tprod ρ).Equiv σ) :
    ((Representation.ofCharacter ν).tprod (ρ.characterTwist κ)).Equiv
      (σ.characterTwist κ) := by
  let e₀ := (Representation.characterTwistTensorEquiv ρ ν).symm.trans e
  apply Representation.characterTensorEquiv (ρ.characterTwist κ) (σ.characterTwist κ)
    ν e₀.toLinearEquiv
  intro g v
  have he := congrArg (fun f : V →ₗ[L] W => f v) (e₀.isIntertwining' g)
  change e₀ ((ν g : L) • ρ g v) = σ g (e₀ v) at he
  change (κ g : L) • σ g (e₀ v) = (ν g : L) • e₀ ((κ g : L) • ρ g v)
  rw [← he, map_smul, map_smul, smul_comm]

/-- The same quadratic complement character compares the actual effective
Euler fibres, including the required κ normalization at even conductors.
The common κ character on both fibres cancels from the comparison. -/
theorem exists_quadratic_character_chosenEffectiveEuler_complement :
    let K := realCyclotomicField N
    ∃ ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ,
      Continuous ν ∧ ν ^ 2 = 1 ∧ (Set.range ν).Finite ∧
      ∀ ξ : ProjectiveLine.Parameter K,
        Nonempty (((Representation.ofCharacter ν).tprod
          (chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L
            (coprimeEulerCoefficientMap N w L) ξ)).Equiv
              (chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L
                (coprimeEulerCoefficientMap N w L)
                (ProjectiveLine.complementParameter K ξ))) := by
  let K := realCyclotomicField N
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hmPos hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hmPos hmN hcop
  let ι := coprimeEulerCoefficientMap N w L
  let F := (R.placeDescent N m 𝒞 p L ι).localSystem
  let κ := gprvKappaLocal N h3 m L
  have heff (ξ : ProjectiveLine.Parameter K) :
      chosenEffectiveEulerAction N m p h3 hmPos hmN hcop L ι ξ =
        (puncturedFiberArithmeticRepresentation K ξ F).characterTwist κ := by
    ext g v
    exact chosenEffectiveEulerAction_apply N m p h3 hmPos hmN hcop L ι ξ g v
  obtain ⟨ν, hνc, hνsq, hνfin, hall⟩ :=
    exists_quadratic_character_chosenCoprimeRawEuler_complement N m p h3 hmPos hmN hcop w L
  refine ⟨ν, hνc, hνsq, hνfin, ?_⟩
  intro ξ
  obtain ⟨e⟩ := hall ξ
  rw [heff, heff]
  exact ⟨tensorComparisonSameTwist _ _ ν κ e⟩

end HilbertModularity.Hypergeometric
