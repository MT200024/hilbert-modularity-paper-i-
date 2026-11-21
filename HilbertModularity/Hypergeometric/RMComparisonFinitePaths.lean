/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparisonFiniteCharacter

/-! # One finite comparison character along every rational fibre path

The arithmetic quotient and paths here are the actual étale fundamental group
and fibre functors of the punctured parameter line. The two representations are
generic arithmetic representations; identifying them with the chosen effective
GPRV and dual Darmon factors is a separate realization step. -/

public noncomputable section

open AlgebraicGeometry

namespace HilbertModularity.Hypergeometric

/-- Geometric comparison and the two determinant formulas give a single finite
coefficient-valued character. It compares the generic representations after
pullback along every rational fibre path, independently of the path choice.
This is the arithmetic descent and specialization portion of
[TripathiGoswamiRevised, Theorem RMgeneral]. -/
theorem exists_finite_comparison_character_along_punctured_paths
    (K : Type*) [Field K] [CharZero K] (ξ₀ : ProjectiveLine.Parameter K)
    {L V W : Type*} [NontriviallyNormedField L] [CharZero L] [CompleteSpace L]
    [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]
    (ρRM : Representation L
      (Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀)) V)
    (ρEff : Representation L
      (Scheme.etaleFundamentalGroup K (ProjectiveLine.puncturedPoint K ξ₀)) W)
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
    (hEffdet : ∀ g, (ρEff.determinantCharacter g * ε g) ^ n = 1) :
    ∃ ν : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Lˣ,
      Continuous ν ∧ (Set.range ν).Finite ∧
      Nonempty (((Representation.ofCharacter
        (ν.comp (puncturedArithmeticProjectionHom K ξ₀))).tprod ρRM).Equiv ρEff) ∧
      ∀ (ξ : ProjectiveLine.Parameter K)
        (e : Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ₀) ≅
          Scheme.finiteArithmeticFiberFunctor K (ProjectiveLine.puncturedPoint K ξ)),
        Nonempty (((Representation.ofCharacter ν).tprod
          (ρRM.comp (puncturedArithmeticLoopsAlongPath K ξ₀ ξ e))).Equiv
          (ρEff.comp (puncturedArithmeticLoopsAlongPath K ξ₀ ξ e))) := by
  obtain ⟨ν, hν, hfinite, he, hpaths⟩ :=
    exists_uniform_finite_comparison_character_of_determinants
      (puncturedArithmeticProjectionHom K ξ₀)
      (puncturedArithmeticProjection_surjective K ξ₀)
      (puncturedArithmeticProjection K ξ₀).continuous
      ρRM ρEff hRMc hEffc eGeom Lbar hdim ε hRMdet n hn hEffdet
  refine ⟨ν, hν, hfinite, he, ?_⟩
  intro ξ e
  obtain ⟨a, ha⟩ := puncturedArithmeticProjection_alongPath K ξ₀ ξ e
  exact hpaths (puncturedArithmeticLoopsAlongPath K ξ₀ ξ e) a (fun g => ha g)

end HilbertModularity.Hypergeometric
