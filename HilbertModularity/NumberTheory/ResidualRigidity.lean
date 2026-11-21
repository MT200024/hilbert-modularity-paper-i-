/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.DenseEmbedding

/-! # Rigidity from infinitely many residue characteristics

A nonzero element of a Dedekind domain vanishes at only finitely many primes.
Consequently congruences at infinitely many coefficient primes determine an
algebraic number. This is the arithmetic step in the determinant argument of
[TripathiGoswami].
-/

@[expose] public noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A nonzero element belongs to only finitely many nonzero prime ideals. -/
theorem finite_primes_containing {a : R} (ha : a ≠ 0) :
    {P : HeightOneSpectrum R | a ∈ P.asIdeal}.Finite := by
  simpa only [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using
    Ideal.finite_factors (I := Ideal.span {a}) (Ideal.span_singleton_eq_bot.not.mpr ha)

/-- Equality in infinitely many prime quotients forces equality in the domain. -/
theorem eq_of_infinite_residue_eq (a b : R) (S : Set (HeightOneSpectrum R))
    (hS : S.Infinite) (h : ∀ P ∈ S, Ideal.Quotient.mk P.asIdeal a =
      Ideal.Quotient.mk P.asIdeal b) : a = b := by
  by_contra hab
  apply hS.not_finite
  apply (finite_primes_containing (sub_ne_zero.mpr hab)).subset
  intro P hP
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, h P hP, sub_self]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A fraction integral at infinitely many primes and reducing to one there
is one. Multiplying by a global denominator reduces the assertion to the
Dedekind domain; no purity or finite-order assumption is required. -/
theorem eq_one_of_infinite_specialization_eq (x : K) (S : Set (HeightOneSpectrum R))
    (hS : S.Infinite) (hint : ∀ P ∈ S, P.valuation K x ≤ 1)
    (hred : ∀ P (hP : P ∈ S), P.specialization x (hint P hP) = 1) : x = 1 := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective R x
  have hb0 : algebraMap R K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hm : x * algebraMap R K b = algebraMap R K a := by
    rw [← hx, div_mul_cancel₀ _ hb0]
  have hab : a = b := eq_of_infinite_residue_eq a b S hS (fun P hP => by
    have hl : P.localElement x (hint P hP) *
        algebraMap R (P.valuationSubringAtPrime K) b =
          algebraMap R (P.valuationSubringAtPrime K) a := Subtype.ext hm
    have hr := congrArg P.localResidue hl
    rw [map_mul, ← specialization, hred P hP, one_mul,
      localResidue_algebraMap, localResidue_algebraMap] at hr
    exact hr.symm)
  rw [← hx, hab, div_self hb0]

/-- Infinitely many distinct residue characteristics suffice; the primes above
them need not be fixed in advance. -/
theorem eq_one_of_infinite_residue_characteristics (x : K) (S : Set ℕ)
    (hS : S.Infinite)
    (h : ∀ ℓ ∈ S, ∃ P : HeightOneSpectrum R,
      ringChar (R ⧸ P.asIdeal) = ℓ ∧
        ∃ hx : P.valuation K x ≤ 1, P.specialization x hx = 1) : x = 1 := by
  let T : Set (HeightOneSpectrum R) :=
    {P | ∃ hx : P.valuation K x ≤ 1, P.specialization x hx = 1}
  have hT : T.Infinite := by
    intro hf
    apply hS.not_finite
    apply (hf.image (fun P => ringChar (R ⧸ P.asIdeal))).subset
    intro ℓ hℓ
    obtain ⟨P, hp, hx, hr⟩ := h ℓ hℓ
    exact ⟨P, ⟨hx, hr⟩, hp⟩
  choose hint hred using (fun P (hP : P ∈ T) => hP)
  exact eq_one_of_infinite_specialization_eq x T hT hint hred

end IsDedekindDomain.HeightOneSpectrum

namespace ContinuousMonoidHom

open IsDedekindDomain

/-- A continuous character is trivial if its values on a dense family are
algebraic and reduce to one in infinitely many residue characteristics.
This separates the elementary arithmetic argument from the source of density. -/
theorem eq_one_of_infinite_residual_congruences
    {R K L G I : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [TopologicalSpace L] [T2Space L] [Algebra K L]
    [Monoid G] [TopologicalSpace G]
    (χ : G →ₜ* Lˣ) (t : I → G) (ht : DenseRange t)
    (a : I → K) (ha : ∀ i, (χ (t i) : L) = algebraMap K L (a i))
    (S : I → Set ℕ) (hS : ∀ i, (S i).Infinite)
    (hred : ∀ i ℓ, ℓ ∈ S i → ∃ P : HeightOneSpectrum R,
      ringChar (R ⧸ P.asIdeal) = ℓ ∧
        ∃ hx : P.valuation K (a i) ≤ 1, P.specialization (a i) hx = 1) : χ = 1 := by
  have he : (fun g => (χ g : L)) = fun _ => (1 : L) := by
    apply ht.equalizer (Units.continuous_val.comp χ.continuous) continuous_const
    funext i
    change (χ (t i) : L) = 1
    rw [ha,
      HeightOneSpectrum.eq_one_of_infinite_residue_characteristics
        (a i) (S i) (hS i) (hred i), map_one]
  ext g
  exact congrFun he g

end ContinuousMonoidHom
