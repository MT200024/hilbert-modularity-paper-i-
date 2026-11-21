/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicResidue
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-! # Frobenius lifts and their action on roots of unity

We construct an arithmetic Frobenius lift in the decomposition group by lifting
the canonical automorphism of the residue field. The inverse is the geometric
Frobenius convention used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped Pointwise NumberField

/-- Field automorphisms over `K` commute with scalars from its integer ring
on the integer ring of the extension. -/
instance NumberField.RingOfIntegers.smulCommClassAlgEquiv
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    SMulCommClass (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) where
  smul_comm g a b := by
    apply NumberField.RingOfIntegers.ext
    change g (algebraMap K E (a : K) * (b : E)) = algebraMap K E (a : K) * g (b : E)
    rw [map_mul, AlgEquiv.commutes]

namespace Ideal

/-- A residue power action lifts uniquely to roots of unity of order prime to
the residue characteristic. No finiteness of the acting group is required. -/
theorem smul_root_eq_pow_of_quotient_action
    {B G : Type*} [CommRing B] [IsDomain B] [CharZero B]
    [Group G] [MulSemiringAction G B] (Q : Ideal B) [Q.IsPrime]
    (g : G) (q : ℕ)
    (hg : ∀ b : B, Ideal.Quotient.mk Q (g • b) = (Ideal.Quotient.mk Q b) ^ q)
    {N : ℕ} [NeZero N] (hN : (N : B) ∉ Q)
    {ζ x : B} (hζ : IsPrimitiveRoot ζ N) (hx : x ^ N = 1) :
    g • x = x ^ q := by
  have : NeZero (N : B ⧸ Q) := ⟨by
    intro h
    apply hN
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_natCast] using h⟩
  apply hζ.eq_of_map_eq_on_roots (Ideal.Quotient.mk Q)
    (hζ.map_of_order_ne_zero (Ideal.Quotient.mk Q))
  · rw [← smul_pow', hx, smul_one]
  · rw [pow_right_comm, hx, one_pow]
  · rw [map_pow]
    exact hg x

/-- Inertia acts trivially on roots of unity of order invertible in the residue field. -/
theorem inertia_smul_root
    {B G : Type*} [CommRing B] [IsDomain B] [CharZero B]
    [Group G] [MulSemiringAction G B] (Q : Ideal B) [Q.IsPrime]
    (g : Q.inertia G) {N : ℕ} [NeZero N] (hN : (N : B) ∉ Q)
    {ζ x : B} (hζ : IsPrimitiveRoot ζ N) (hx : x ^ N = 1) :
    g • x = x := by
  have h := smul_root_eq_pow_of_quotient_action Q (g : G) 1 (fun b => by
    rw [pow_one, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_inertia.mp g.property) b) hN hζ hx
  change (g : G) • x = x
  simpa only [pow_one] using h

end Ideal

namespace Ideal.Quotient

section Residue

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
  [Finite (A ⧸ P)] [Algebra.IsAlgebraic (A ⧸ P) (B ⧸ Q)]

attribute [local instance] Ideal.Quotient.field

/-- Arithmetic Frobenius on an algebraic extension of a finite residue field. -/
def arithmeticFrobenius : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) :=
  let := Fintype.ofFinite (A ⧸ P)
  FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P) (B ⧸ Q)

/-- The residue Frobenius raises elements to the base residue-field cardinality. -/
@[simp] theorem arithmeticFrobenius_apply (x : B ⧸ Q) :
    arithmeticFrobenius P Q x = x ^ Nat.card (A ⧸ P) := by
  let := Fintype.ofFinite (A ⧸ P)
  simp only [arithmeticFrobenius, FiniteField.frobeniusAlgEquivOfAlgebraic_apply,
    Nat.card_eq_fintype_card]

/-- A geometric Frobenius lift has inverse acting by the arithmetic residue power. -/
theorem inv_smul_eq_of_geometricFrobenius
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (g : MulAction.stabilizer G Q)
    (hg : stabilizerHom Q P G g⁻¹ = arithmeticFrobenius P Q) (b : B) :
    Ideal.Quotient.mk Q ((g : G)⁻¹ • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (A ⧸ P) := by
  have h := congrArg (fun a : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) => a (Ideal.Quotient.mk Q b)) hg
  simpa only [stabilizerHom_apply, arithmeticFrobenius_apply,
    Subgroup.smul_def, Subgroup.coe_inv] using h

end Residue

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
  [Finite (A ⧸ P)] [Finite (B ⧸ Q)]

attribute [local instance] Ideal.Quotient.field

/-- An arithmetic Frobenius lift in the stabilizer of a prime. -/
def arithmeticFrobeniusLift : MulAction.stabilizer G Q :=
  (stabilizerHom_surjective G P Q (arithmeticFrobenius P Q)).choose

/-- A Frobenius lift acts on residues by the cardinality of the base residue field. -/
theorem arithmeticFrobeniusLift_spec (b : B) :
    Ideal.Quotient.mk Q (arithmeticFrobeniusLift G P Q • b) =
      (Ideal.Quotient.mk Q b) ^ Nat.card (A ⧸ P) := by
  have h := (stabilizerHom_surjective G P Q (arithmeticFrobenius P Q)).choose_spec
  have hv := congrArg (fun f : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) => f (Ideal.Quotient.mk Q b)) h
  simpa only [arithmeticFrobeniusLift, stabilizerHom_apply, arithmeticFrobenius_apply] using hv

/-- Away from the root order, a Frobenius lift acts on every root of unity
by raising it to the cardinality of the base residue field. -/
theorem arithmeticFrobeniusLift_smul_root [IsDomain B] [CharZero B]
    {N : ℕ} [NeZero N] (hN : (N : B) ∉ Q)
    {ζ x : B} (hζ : IsPrimitiveRoot ζ N) (hx : x ^ N = 1) :
    arithmeticFrobeniusLift G P Q • x = x ^ Nat.card (A ⧸ P) := by
  exact Ideal.smul_root_eq_pow_of_quotient_action Q
    (arithmeticFrobeniusLift G P Q) (Nat.card (A ⧸ P))
    (arithmeticFrobeniusLift_spec G P Q) hN hζ hx

end Ideal.Quotient
