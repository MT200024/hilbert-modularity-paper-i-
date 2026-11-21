/- Assembled by AxiomProver. -/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Algebra.GroupWithZero.Idempotent

/-! # Galois orbits of algebra maps into an algebraic closure

The kernel determines an algebra map up to postcomposition by an absolute
Galois automorphism. Its algebraic image is a field, and an isomorphism between
two such images extends by normality of the algebraic closure.
-/

@[expose] public noncomputable section
namespace AlgHom
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]

/-- Two algebra maps to the algebraic closure with equal kernels differ by an
absolute Galois automorphism. No reducedness or finiteness of the source is needed. -/
theorem exists_galois_comp_eq_of_ker_eq (φ ψ : A →ₐ[K] AlgebraicClosure K)
    (h : RingHom.ker φ = RingHom.ker ψ) :
    ∃ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g.toAlgHom.comp φ = ψ := by
  have hφ : φ.range.IsAlgebraic := fun a _ => Algebra.IsAlgebraic.isAlgebraic a
  have hψ : ψ.range.IsAlgebraic := fun a _ => Algebra.IsAlgebraic.isAlgebraic a
  let L := hφ.toIntermediateField
  let M := hψ.toIntermediateField
  let eφ := Ideal.quotientKerEquivRange φ
  let eψ := Ideal.quotientKerEquivRange ψ
  let e : L ≃ₐ[K] M := eφ.symm.trans ((Ideal.quotientEquivAlgOfEq K h).trans eψ)
  have he (a : A) : e (φ.rangeRestrict a) = ψ.rangeRestrict a := by
    change e (eφ (Ideal.Quotient.mk _ a)) = eψ (Ideal.Quotient.mk _ a)
    change eψ ((Ideal.quotientEquivAlgOfEq K h)
      (eφ.symm (eφ (Ideal.Quotient.mk _ a)))) = eψ (Ideal.Quotient.mk _ a)
    rw [AlgEquiv.symm_apply_apply, Ideal.quotientEquivAlgOfEq_mk]
  refine ⟨e.liftNormal (AlgebraicClosure K), ?_⟩
  apply AlgHom.ext
  intro a
  exact (e.liftNormal_commutes (AlgebraicClosure K) (φ.rangeRestrict a)).trans
    (congrArg Subtype.val (he a))

/-- Kernels classify the Galois orbits of algebra maps into the algebraic closure. -/
theorem ker_eq_iff_exists_galois_comp_eq (φ ψ : A →ₐ[K] AlgebraicClosure K) :
    RingHom.ker φ = RingHom.ker ψ ↔
      ∃ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g.toAlgHom.comp φ = ψ := by
  refine ⟨exists_galois_comp_eq_of_ker_eq K A φ ψ, ?_⟩
  rintro ⟨g, rfl⟩
  ext a
  change φ a = 0 ↔ g (φ a) = 0
  exact g.map_eq_zero_iff.symm

/-- For an Artinian algebra, a single idempotent detects exactly the Galois orbit
of a chosen algebra map into the algebraic closure. -/
theorem exists_idempotent_galoisOrbit_indicator [IsArtinianRing A]
    (φ : A →ₐ[K] AlgebraicClosure K) :
    ∃ e : A, IsIdempotentElem e ∧ ∀ ψ : A →ₐ[K] AlgebraicClosure K,
      ψ e = 1 ↔ ∃ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g.toAlgHom.comp φ = ψ := by
  classical
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ.toRingHom
  obtain ⟨e, heφ, he, hothers⟩ :=
    IsArtinianRing.exists_not_mem_forall_mem_of_ne (RingHom.ker φ)
  refine ⟨e, he, fun ψ => ?_⟩
  rw [← ker_eq_iff_exists_galois_comp_eq K A φ ψ]
  by_cases h : RingHom.ker φ = RingHom.ker ψ
  · have hn : ψ e ≠ 0 := by
      change e ∉ RingHom.ker ψ
      simpa only [← h] using heφ
    exact ⟨fun _ => h, fun _ =>
      (IsIdempotentElem.iff_eq_zero_or_one.mp (he.map ψ)).resolve_left hn⟩
  · have hz : ψ e = 0 := hothers (RingHom.ker ψ)
      (RingHom.ker_isPrime ψ.toRingHom) (Ne.symm h)
    simp only [hz, zero_ne_one, h]

end AlgHom
