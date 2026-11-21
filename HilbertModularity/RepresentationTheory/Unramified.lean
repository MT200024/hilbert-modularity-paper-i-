/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Frobenius
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia

/-! # Unramified representations and residue Frobenius

An action trivial on inertia depends only on the residue-field action. This
allows Frobenius comparison under extension of the base number field, as used in
[TripathiGoswami, residue-degree trace formulas].
-/

@[expose] public section

namespace Representation

variable {R B G V : Type*} [CommSemiring R] [CommRing B]
  [Group G] [MulSemiringAction G B] [AddCommMonoid V] [Module R V]

/-- Two automorphisms with the same residue action have the same image under
a representation trivial on inertia. -/
theorem apply_eq_of_inertia_trivial (ρ : Representation R G V) (Q : Ideal B)
    (hρ : ∀ g ∈ Q.inertia G, ρ g = 1) (g h : G)
    (he : ∀ b : B, Ideal.Quotient.mk Q (g • b) = Ideal.Quotient.mk Q (h • b)) :
    ρ g = ρ h := by
  have hi : g * h⁻¹ ∈ Q.inertia G := by
    rw [Ideal.mem_inertia]
    intro b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, mul_smul]
    simpa only [smul_inv_smul] using he (h⁻¹ • b)
  have hh := congrArg (fun f : Module.End R V => f * ρ h) (hρ _ hi)
  simpa only [← map_mul, inv_mul_cancel_right, one_mul] using hh

end Representation

namespace Ideal.Quotient

/-- Iterating a residue power action raises its exponent to the same power. -/
theorem pow_smul_eq_of_quotient_action
    {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]
    (Q : Ideal B) (g : G) (q : ℕ)
    (hg : ∀ b : B, Ideal.Quotient.mk Q (g • b) = (Ideal.Quotient.mk Q b) ^ q)
    (n : ℕ) (b : B) :
    Ideal.Quotient.mk Q (g ^ n • b) = (Ideal.Quotient.mk Q b) ^ q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, hg, ih, ← pow_mul, pow_succ]

end Ideal.Quotient

open scoped NumberField Pointwise

namespace Representation

variable {K F E R V : Type*} [Field K] [Field F] [Field E]
  [NumberField K] [NumberField F]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [CommSemiring R] [AddCommMonoid V] [Module R V]

attribute [local instance] Ideal.Quotient.field

/-- In a common algebraic overfield, restriction of an unramified representation
sends geometric Frobenius to the residue-degree power of geometric Frobenius.
The primes, their residue actions, and inertia are the standard ideal-theoretic
objects. The result also holds when the extension of base fields is ramified. -/
theorem geometricFrobenius_restrictScalars
    (ρ : Representation R (E ≃ₐ[K] E) V)
    (P : Ideal (𝓞 K)) [P.IsMaximal] (P' : Ideal (𝓞 F)) [P'.IsMaximal]
    [P'.LiesOver P] (Q : Ideal (𝓞 E)) [Q.IsMaximal]
    [Q.LiesOver P] [Q.LiesOver P']
    (hρ : ∀ g ∈ Q.inertia (E ≃ₐ[K] E), ρ g = 1)
    (g : MulAction.stabilizer (E ≃ₐ[K] E) Q)
    (g' : MulAction.stabilizer (E ≃ₐ[F] E) Q)
    (hg : Ideal.Quotient.stabilizerHom Q P (E ≃ₐ[K] E) g⁻¹ =
      Ideal.Quotient.arithmeticFrobenius P Q)
    (hg' : Ideal.Quotient.stabilizerHom Q P' (E ≃ₐ[F] E) g'⁻¹ =
      Ideal.Quotient.arithmeticFrobenius P' Q) :
    ρ (AlgEquiv.restrictScalarsHom K (g' : E ≃ₐ[F] E)) =
      ρ (g : E ≃ₐ[K] E) ^ P'.inertiaDeg (𝓞 K) := by
  let f := P'.inertiaDeg (𝓞 K)
  have hcard : Nat.card (𝓞 F ⧸ P') = Nat.card (𝓞 K ⧸ P) ^ f :=
    (Ideal.cardQuot_pow_inertiaDeg P P').symm
  have hact := Ideal.Quotient.inv_smul_eq_of_geometricFrobenius P Q g hg
  have hact' := Ideal.Quotient.inv_smul_eq_of_geometricFrobenius P' Q g' hg'
  have he : ρ (AlgEquiv.restrictScalarsHom K (g' : E ≃ₐ[F] E))⁻¹ =
      ρ ((g : E ≃ₐ[K] E)⁻¹ ^ f) := by
    apply apply_eq_of_inertia_trivial ρ Q hρ
    intro b
    rw [Ideal.Quotient.pow_smul_eq_of_quotient_action Q _ _ hact]
    change Ideal.Quotient.mk Q ((g' : E ≃ₐ[F] E)⁻¹ • b) = _
    rw [hact', hcard]
  have hu : ρ.asGroupHom (AlgEquiv.restrictScalarsHom K (g' : E ≃ₐ[F] E))⁻¹ =
      ρ.asGroupHom ((g : E ≃ₐ[K] E)⁻¹ ^ f) := Units.ext he
  have hi := congrArg (fun u : (Module.End R V)ˣ => ((u⁻¹ : (Module.End R V)ˣ) : Module.End R V)) hu
  simpa only [map_inv, map_pow, inv_pow, inv_inv, Units.val_pow_eq_pow_val,
    asGroupHom_apply] using hi

end Representation
