/- Assembled by AxiomProver. -/

module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Connected.Clopen

/-! # Connected clopen neighbourhoods in Noetherian spaces -/

@[expose] public section
open TopologicalSpace Set

/-- A point in a clopen subset of a Noetherian space has a connected clopen
neighbourhood contained in that subset. -/
theorem exists_connected_clopen_subset_of_noetherian {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {s : Set X} (hs : IsClopen s) {x : X} (hx : x ∈ s) :
    ∃ t : Set X, x ∈ t ∧ t ⊆ s ∧ IsClopen t ∧ IsConnected t := by
  suffices H : ∀ s : Closeds X, IsOpen (s : Set X) → ∀ x ∈ s,
      ∃ t : Set X, x ∈ t ∧ t ⊆ s ∧ IsClopen t ∧ IsConnected t from
    H ⟨s, hs.isClosed⟩ hs.isOpen x hx
  intro s
  apply (wellFounded_lt : WellFounded ((· < ·) : Closeds X → Closeds X → Prop)).induction s
  intro s ih hs x hx
  by_cases hc : IsPreconnected (s : Set X)
  · exact ⟨s, hx, Subset.rfl, ⟨s.isClosed, hs⟩, ⟨⟨x, hx⟩, hc⟩⟩
  obtain ⟨a, b, ha, hb, ha0, hb0, hab, hsab⟩ :=
    (IsClopen.not_isPreconnected_iff ⟨s.isClosed, hs⟩).mp hc
  have descend (a b : Set X) (ha : IsClopen a) (hb0 : b.Nonempty)
      (hab : Disjoint a b) (hsab : (s : Set X) = a ∪ b) (hxa : x ∈ a) :
      ∃ t : Set X, x ∈ t ∧ t ⊆ s ∧ IsClopen t ∧ IsConnected t := by
    have has : a ⊆ s := by rw [hsab]; exact subset_union_left
    have hlt : (⟨a, ha.isClosed⟩ : Closeds X) < s := by
      apply lt_iff_le_and_ne.mpr
      refine ⟨has, ?_⟩
      intro he
      have he' : a = (s : Set X) := congrArg (fun U : Closeds X => (U : Set X)) he
      obtain ⟨z, hz⟩ := hb0
      have hza : z ∈ a := by rw [he', hsab]; exact Or.inr hz
      exact Set.disjoint_left.mp hab hza hz
    obtain ⟨t, htx, hta, ht, htc⟩ := ih ⟨a, ha.isClosed⟩ hlt ha.isOpen x hxa
    exact ⟨t, htx, hta.trans has, ht, htc⟩
  have hx' : x ∈ a ∪ b := hsab ▸ hx
  rcases hx' with hxa | hxb
  · exact descend a b ha hb0 hab hsab hxa
  · exact descend b a hb ha0 hab.symm (hsab.trans (Set.union_comm a b)) hxb
