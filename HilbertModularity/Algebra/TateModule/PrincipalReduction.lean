/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.Reduction
public import HilbertModularity.Algebra.TateModule.Endomorphism

/-! # Principal coefficient reduction of Tate modules

For a coefficient factorization `a * b = p`, the map sending a compatible
Tate family to `b` times its first coordinate takes values in the actual
`a`-torsion subgroup. If the point group is `p`-divisible, its kernel is
`a` times the integral Tate module. This is the principal coefficient-prime
comparison used in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- Coefficients act coordinatewise on the existing compatible-family Tate module. -/
local instance coefficientModule : Module R (integral p A) :=
  Module.compHom (integral p A) ((endomorphismMap p A).comp (Module.toAddMonoidEnd R A))

@[simp]
theorem coefficient_smul_projection (r : R) (x : integral p A) (n : ℕ) :
    (projection p A n (r • x) : A) = r • (projection p A n x : A) := rfl

/-- Projection followed by the complementary coefficient lands in actual coefficient torsion. -/
def principalProjection (a b : R) (hab : a * b = (p : R)) :
    integral p A →ₗ[R] Submodule.torsionBy R A a where
  toFun x := ⟨b • (projection p A 1 x : A), by
    change a • (b • (projection p A 1 x : A)) = 0
    rw [← mul_smul, hab, Nat.cast_smul_eq_nsmul]
    simpa only [pow_one] using
      AddSubgroup.torsionBy.nsmul_iff.mp (projection p A 1 x).property⟩
  map_add' x y := by apply Subtype.ext; exact smul_add b _ _
  map_smul' r x := by apply Subtype.ext; exact smul_comm b r _

@[simp]
theorem principalProjection_apply (a b : R) (hab : a * b = (p : R)) (x : integral p A) :
    (principalProjection p R A a b hab x : A) = b • (projection p A 1 x : A) := rfl

omit [Fact p.Prime] in
/-- A factor of `p` acts surjectively on a `p`-divisible coefficient module. -/
theorem coefficient_smul_surjective (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    Function.Surjective (fun x : A => a • x) := by
  intro x
  obtain ⟨y, hy⟩ := hpdiv x
  refine ⟨b • y, ?_⟩
  change a • (b • y) = x
  rw [← mul_smul, hab, Nat.cast_smul_eq_nsmul]
  exact hy

/-- Every coefficient-torsion point is the principal reduction of an actual Tate family. -/
theorem principalProjection_surjective (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    Function.Surjective (principalProjection p R A a b hab) := by
  intro x
  obtain ⟨y, hy⟩ := coefficient_smul_surjective p R A b a (by rwa [mul_comm]) hpdiv (x : A)
  change b • y = (x : A) at hy
  have hy0 : p • y = 0 := by
    rw [← Nat.cast_smul_eq_nsmul R, ← hab, mul_smul, hy]
    exact x.property
  let z : Torsion p A 1 := ⟨y, by
    rw [AddSubgroup.torsionBy.nsmul_iff, pow_one]; exact hy0⟩
  obtain ⟨t, ht⟩ := projection_one_surjective p A hpdiv z
  refine ⟨t, Subtype.ext ?_⟩
  change b • (projection p A 1 t : A) = (x : A)
  rw [ht]
  exact hy

/-- The principal coefficient projection kills exactly coefficient multiples of Tate vectors. -/
theorem principalProjection_eq_zero_iff (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) (x : integral p A) :
    principalProjection p R A a b hab x = 0 ↔ ∃ y : integral p A, a • y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := coefficient_smul_surjective p R A a b hab hpdiv
      (projection p A 1 x : A)
    change a • y = (projection p A 1 x : A) at hy
    have hy0 : p • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul R, ← hab, mul_comm a b, mul_smul, hy]
      exact congrArg Subtype.val hx
    let z : Torsion p A 1 := ⟨y, by
      rw [AddSubgroup.torsionBy.nsmul_iff, pow_one]; exact hy0⟩
    obtain ⟨t, ht⟩ := projection_one_surjective p A hpdiv z
    have hzero : projection p A 1 (x - a • t) = 0 := by
      apply Subtype.ext
      change (projection p A 1 x : A) - a • (projection p A 1 t : A) = 0
      rw [ht]
      exact sub_eq_zero.mpr hy.symm
    obtain ⟨u, hu⟩ := (projection_eq_zero_iff p A 1 (x - a • t)).mp hzero
    refine ⟨t + b • u, ?_⟩
    have hpu : a • (b • u) = x - a • t := by
      rw [← mul_smul, hab, Nat.cast_smul_eq_nsmul]
      simpa only [pow_one, Nat.cast_smul_eq_nsmul] using hu
    rw [smul_add, hpu]
    rw [add_comm, sub_add_cancel]
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change b • (a • (projection p A 1 y : A)) = 0
    rw [← mul_smul, mul_comm b a, hab, Nat.cast_smul_eq_nsmul]
    simpa only [pow_one] using
      AddSubgroup.torsionBy.nsmul_iff.mp (projection p A 1 y).property

/-- The principal projection kernel is the ideal multiple of the actual integral Tate module. -/
theorem ker_principalProjection (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    LinearMap.ker (principalProjection p R A a b hab) =
      Ideal.span {a} • (⊤ : Submodule R (integral p A)) := by
  ext x
  rw [LinearMap.mem_ker, principalProjection_eq_zero_iff p R A a b hab hpdiv,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

/-- Quotienting the actual Tate module by a principal coefficient gives actual coefficient torsion. -/
def principalReductionEquiv (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    (integral p A ⧸ (Ideal.span {a} • (⊤ : Submodule R (integral p A)))) ≃ₗ[R]
      Submodule.torsionBy R A a :=
  (Submodule.quotEquivOfEq _ _ (ker_principalProjection p R A a b hab hpdiv).symm).trans
    ((principalProjection p R A a b hab).quotKerEquivOfSurjective
      (principalProjection_surjective p R A a b hab hpdiv))

@[simp]
theorem principalReductionEquiv_mk (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) (x : integral p A) :
    principalReductionEquiv p R A a b hab hpdiv (Submodule.Quotient.mk x) =
      principalProjection p R A a b hab x := rfl

/-- Scalar reduction at a principal coefficient ideal is the actual coefficient-torsion module. -/
def principalResidualEquiv (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) :
    ((R ⧸ Ideal.span {a}) ⊗[R] integral p A) ≃ₗ[R ⧸ Ideal.span {a}]
      Submodule.torsionBy R A a := by
  let e := (TensorProduct.quotTensorEquivQuotSMul (integral p A) (Ideal.span {a})).trans
    (principalReductionEquiv p R A a b hab hpdiv)
  exact
    { e.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        change e (algebraMap R (R ⧸ Ideal.span {a}) r • x) = r • e x
        rw [algebraMap_smul]
        exact e.map_smul r x }

@[simp]
theorem principalResidualEquiv_mk_tmul (a b : R) (hab : a * b = (p : R))
    (hpdiv : Function.Surjective (fun x : A => p • x)) (r : R) (x : integral p A) :
    principalResidualEquiv p R A a b hab hpdiv
      (Ideal.Quotient.mk (Ideal.span {a}) r ⊗ₜ[R] x) =
        r • principalProjection p R A a b hab x := by
  change principalReductionEquiv p R A a b hab hpdiv
    (TensorProduct.quotTensorEquivQuotSMul (integral p A) (Ideal.span {a})
      (Ideal.Quotient.mk (Ideal.span {a}) r ⊗ₜ[R] x)) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, principalReductionEquiv_mk, map_smul]

end TateModule
