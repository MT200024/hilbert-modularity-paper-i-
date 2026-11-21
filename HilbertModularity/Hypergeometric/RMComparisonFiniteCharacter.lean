/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.RMComparison
public import HilbertModularity.Hypergeometric.RMComparisonDeterminant

/-! # A finite character from geometric comparison and determinants

This combines geometric Schur descent with the determinant calculation. The
generic geometric equivalence and both determinant identities are explicit
inputs, to be supplied for the chosen Darmon and effective families. The
character is constructed once on the arithmetic quotient, before taking any
specialization. -/

public section

namespace HilbertModularity.Hypergeometric

/-- A geometric equivalence gives one arithmetic comparison character. If the
cohomological RM determinant is inverse cyclotomic and the normalized
effective determinant has a positive finite exponent, that character has
finite image. Its pullback is the same at every arithmetic section whose
projection is conjugate to the identity. This is the formal descent and
determinant portion of [TripathiGoswamiRevised, Theorem RMgeneral]. -/
theorem exists_uniform_finite_comparison_character_of_determinants
    {L G Γ V W : Type*} [NontriviallyNormedField L] [CharZero L] [CompleteSpace L]
    [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
    [Group Γ] [TopologicalSpace Γ] [T2Space Γ]
    [NormedAddCommGroup V] [NormedSpace L V] [FiniteDimensional L V] [Nontrivial V]
    [NormedAddCommGroup W] [NormedSpace L W] [FiniteDimensional L W]
    (π : G →* Γ) (hπ : Function.Surjective π) (hπc : Continuous π)
    (ρRM : Representation L G V) (ρEff : Representation L G W)
    (hRMc : ∀ v, Continuous (fun g => ρRM g v))
    (hEffc : ∀ v, Continuous (fun g => ρEff g v))
    (eGeom : Representation.Equiv (ρRM.comp π.ker.subtype)
      (ρEff.comp π.ker.subtype))
    (Lbar : Type*) [Field Lbar] [Algebra L Lbar] [IsAlgClosed Lbar]
    [Representation.IsIrreducible (Representation.baseChange Lbar
      (ρRM.comp π.ker.subtype))]
    (hdim : Module.finrank L V = 2)
    (ε : G →* Lˣ)
    (hRMdet : ∀ g, ρRM.determinantCharacter g * ε g = 1)
    (n : ℕ) (hn : 0 < n)
    (hEffdet : ∀ g, (ρEff.determinantCharacter g * ε g) ^ n = 1) :
    ∃ ν : Γ →* Lˣ, Continuous ν ∧ (Set.range ν).Finite ∧
      Nonempty (((Representation.ofCharacter (ν.comp π)).tprod ρRM).Equiv ρEff) ∧
      ∀ (s : Γ →* G) (a : Γ),
        (∀ g, π (s g) = a * g * a⁻¹) →
        Nonempty (((Representation.ofCharacter ν).tprod (ρRM.comp s)).Equiv
          (ρEff.comp s)) := by
  obtain ⟨ν, hν, ⟨e⟩, hsections⟩ :=
    Representation.exists_uniform_comparison_character π hπ hπc ρRM ρEff
      hRMc hEffc eGeom Lbar
  have hfinitePullback : (Set.range (ν.comp π)).Finite :=
    comparisonCharacter_finite_range_of_tensor_equiv_and_power
      ρRM ρEff (ν.comp π) ε e hdim hRMdet n hn hEffdet
  have hfinite : (Set.range ν).Finite := by
    apply hfinitePullback.subset
    rintro y ⟨γ, rfl⟩
    obtain ⟨g, rfl⟩ := hπ γ
    exact ⟨g, rfl⟩
  exact ⟨ν, hν, hfinite, ⟨e⟩, hsections⟩

end HilbertModularity.Hypergeometric
