/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Frobenius
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Invariant.Profinite

/-! # Galois actions on primes in algebraic extensions

The absolute Galois action on algebraic integers is continuous for the discrete
topology. Its invariant ring is the integer ring of the base field. These facts
allow the profinite transitivity theorem to apply to primes in an algebraic closure.
-/

@[expose] public noncomputable section

open scoped NumberField Pointwise

namespace NumberField.RingOfIntegers

/-- The integers fixed by a Galois group are exactly the integers of the base field,
including for infinite algebraic Galois extensions. -/
instance isInvariantAlgEquiv (K E : Type*) [Field K] [Field E] [Algebra K E]
    [IsGalois K E] : Algebra.IsInvariant (𝓞 K) (𝓞 E) (E ≃ₐ[K] E) where
  isInvariant b hb := by
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (K := E) (k := K)
      (b : E)).mpr (fun g => congrArg (fun x : 𝓞 E => (x : E)) (hb g))
    have hi : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (B := E), ha]
      exact b.property
    exact ⟨⟨a, hi⟩, Subtype.ext ha⟩

/-- Krull-continuous action on algebraic integers with their discrete topology. -/
instance continuousSMulAlgEquiv (K E : Type*) [Field K] [Field E] [Algebra K E]
    [Algebra.IsIntegral K E] [TopologicalSpace (𝓞 E)] [DiscreteTopology (𝓞 E)] :
    ContinuousSMul (E ≃ₐ[K] E) (𝓞 E) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  convert! stabilizer_isOpen_of_isIntegral (K := K) (x : E) using 1
  ext g
  exact Subtype.ext_iff

/-- Primes above the same base prime are conjugate even in an infinite Galois extension. -/
theorem exists_smul_of_under_eq (K E : Type*) [Field K] [Field E] [Algebra K E]
    [IsGalois K E] (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under (𝓞 K) = Q.under (𝓞 K)) :
    ∃ g : E ≃ₐ[K] E, Q = g • P := by
  let : TopologicalSpace (𝓞 E) := ⊥
  let : DiscreteTopology (𝓞 E) := ⟨rfl⟩
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := 𝓞 K) (G := E ≃ₐ[K] E) P Q hPQ

end NumberField.RingOfIntegers

namespace Ideal

/-- Contraction commutes with compatible automorphisms of the two rings. -/
theorem comap_smul_of_equivariant {R S G H : Type*} [CommRing R] [CommRing S]
    [Group G] [Group H] [MulSemiringAction G R] [MulSemiringAction H S]
    (f : R →+* S) (g : G) (h : H) (hf : ∀ x, f (g • x) = h • f x)
    (Q : Ideal S) : (h • Q).comap f = g • Q.comap f := by
  have hi (x : R) : f (g⁻¹ • x) = h⁻¹ • f x := by
    apply (MulAction.injective h)
    change h • f (g⁻¹ • x) = h • (h⁻¹ • f x)
    rw [← hf, smul_inv_smul, smul_inv_smul]
  ext x
  simp only [Ideal.mem_comap, mem_pointwise_smul_iff_inv_smul_mem]
  rw [hi]

end Ideal

namespace NumberField.RingOfIntegers

/-- An automorphism in a finite-level decomposition group lifts to the
corresponding decomposition group in a normal overfield. The overfield may be
infinite, and no ramification assumption is needed. -/
theorem exists_stabilizer_lift
    (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Normal K E] [IsGalois F E]
    (P : Ideal (𝓞 F)) (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver P]
    (σ : F ≃ₐ[K] F) (hσ : σ ∈ MulAction.stabilizer (F ≃ₐ[K] F) P) :
    ∃ g : MulAction.stabilizer (E ≃ₐ[K] E) Q,
      ∀ x : F, (g : E ≃ₐ[K] E) (algebraMap F E x) = algebraMap F E (σ x) := by
  let g₀ := σ.liftNormal E
  have hf (x : 𝓞 F) : algebraMap (𝓞 F) (𝓞 E) (σ • x) =
      g₀ • algebraMap (𝓞 F) (𝓞 E) x := by
    apply Subtype.ext
    exact (σ.liftNormal_commutes E (x : F)).symm
  have hu : (g₀ • Q).under (𝓞 F) = Q.under (𝓞 F) := by
    rw [Ideal.under_def, Ideal.comap_smul_of_equivariant _ σ g₀ hf,
      ← Ideal.under_def, ← Q.over_def P]
    exact hσ
  obtain ⟨τ, hτ⟩ := exists_smul_of_under_eq F E (g₀ • Q) Q hu
  refine ⟨⟨τ.restrictScalars K * g₀, ?_⟩, ?_⟩
  · change (τ.restrictScalars K * g₀) • Q = Q
    rw [mul_smul]
    exact hτ.symm
  · intro x
    change τ (g₀ (algebraMap F E x)) = algebraMap F E (σ x)
    rw [AlgEquiv.liftNormal_commutes, AlgEquiv.commutes]

end NumberField.RingOfIntegers
