/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalGlobalInertia

/-! # Identifying the residue prime from a specified contraction -/

public section

open IsDedekindDomain
open scoped NumberField

namespace NumberField

/-- The rational prime selected by contraction is the specified nonnegative
generator of the contracted ideal. This identifies coefficient-characteristic
labels without changing the prime or completion. -/
theorem primeBelow_eq_of_liesOver
    (F : Type) [Field F] [NumberField F]
    (q : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    [q.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    primeBelow F q = p := by
  have he : Ideal.span {(primeBelow F q : ℤ)} = Ideal.span {(p : ℤ)} :=
    (show q.asIdeal.LiesOver (Ideal.span {(primeBelow F q : ℤ)}) from
      inferInstance).over.trans
      (show q.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) from inferInstance).over.symm
  apply Nat.dvd_antisymm
  · have h : (p : ℤ) ∈ Ideal.span {(primeBelow F q : ℤ)} := by
      rw [he]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hd := Ideal.mem_span_singleton.mp h
    exact_mod_cast hd
  · have h : (primeBelow F q : ℤ) ∈ Ideal.span {(p : ℤ)} := by
      rw [← he]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hd := Ideal.mem_span_singleton.mp h
    exact_mod_cast hd

end NumberField
