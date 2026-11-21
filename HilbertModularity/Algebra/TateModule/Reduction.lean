/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Reduction of the actual covariant Tate module

Shifting compatible torsion families proves that the kernel of finite-level
projection is exactly the corresponding power of `p` times the Tate module.
If the point group is `p`-divisible, projection onto its `p`-torsion is onto.
This is the actual integral reduction step in [TripathiGoswami]; divisibility
of a particular geometric point group remains a separate geometric input.
-/

@[expose] public noncomputable section

open scoped Pointwise TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]

/-- The transition equation on underlying torsion points. -/
theorem nsmul_projection (n : ℕ) (x : integral p A) :
    p • (projection p A (n + 1) x : A) = (projection p A n x : A) :=
  congrArg Subtype.val (transition_projection p A n x)

/-- Multiplication by `p` on the actual Tate module is injective for every additive point group. -/
theorem nsmul_injective : Function.Injective (fun x : integral p A => p • x) := by
  intro x y h
  apply Subtype.ext
  funext n
  apply Subtype.ext
  have h' := congrArg (fun z : integral p A => (projection p A (n + 1) z : A)) h
  change p • (projection p A (n + 1) x : A) = p • (projection p A (n + 1) y : A) at h'
  exact (nsmul_projection p A n x).symm.trans (h'.trans (nsmul_projection p A n y))

/-- Every power of `p` acts injectively on the actual compatible-family Tate module. -/
theorem pow_nsmul_injective (n : ℕ) :
    Function.Injective (fun x : integral p A => p ^ n • x) := by
  induction n with
  | zero =>
    intro x y h
    simpa only [pow_zero, one_nsmul] using h
  | succ n hn =>
    intro x y h
    change p ^ (n + 1) • x = p ^ (n + 1) • y at h
    rw [pow_succ', mul_nsmul, mul_nsmul] at h
    exact nsmul_injective p A (hn h)

/-- The actual integral Tate module has no torsion over the `p`-adic integers. -/
instance integral_isTorsionFree : Module.IsTorsionFree ℤ_[p] (integral p A) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r x hx
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  rw [PadicInt.unitCoeff_spec hr, mul_smul] at hx
  change PadicInt.unitCoeff hr • ((p : ℤ_[p]) ^ r.valuation • x) = 0 at hx
  have hpow := congrArg (fun z : integral p A => (PadicInt.unitCoeff hr)⁻¹ • z) hx
  simp only [inv_smul_smul, smul_zero] at hpow
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hpow
  apply pow_nsmul_injective p A r.valuation
  simpa only [smul_zero] using hpow

/-- Iterating the transition multiplies a torsion coordinate by the corresponding power of `p`. -/
theorem pow_nsmul_projection (n k : ℕ) (x : integral p A) :
    p ^ k • (projection p A (n + k) x : A) = (projection p A n x : A) := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ', mul_nsmul]
    rw [show n + (k + 1) = (n + k) + 1 by omega]
    rw [nsmul_projection, hk]

/-- A compatible family vanishing at level `n` has a canonical `pⁿ`-division by shifting coordinates. -/
def divideOfProjectionEqZero (n : ℕ) (x : integral p A)
    (hx : projection p A n x = 0) : integral p A :=
  ⟨fun k => ⟨(projection p A (k + n) x : A), by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    have h := pow_nsmul_projection p A n k x
    rw [Nat.add_comm n k] at h
    exact h.trans (congrArg Subtype.val hx)⟩, by
    intro k
    apply Subtype.ext
    change p • (projection p A (k + 1 + n) x : A) = (projection p A (k + n) x : A)
    rw [show k + 1 + n = (k + n) + 1 by omega]
    exact nsmul_projection p A (k + n) x⟩

/-- Shifting a vanishing family really divides it by the required power of `p`. -/
theorem pow_smul_divideOfProjectionEqZero (n : ℕ) (x : integral p A)
    (hx : projection p A n x = 0) :
    (p : ℤ_[p]) ^ n • divideOfProjectionEqZero p A n x hx = x := by
  apply Subtype.ext
  funext k
  change (p : ℤ_[p]) ^ n • (divideOfProjectionEqZero p A n x hx).val k = x.val k
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  apply Subtype.ext
  exact pow_nsmul_projection p A k n x

/-- The finite-level kernel consists exactly of multiples by the corresponding power of `p`. -/
theorem projection_eq_zero_iff (n : ℕ) (x : integral p A) :
    projection p A n x = 0 ↔ ∃ y : integral p A, (p : ℤ_[p]) ^ n • y = x := by
  constructor
  · intro hx
    exact ⟨divideOfProjectionEqZero p A n x hx, pow_smul_divideOfProjectionEqZero p A n x hx⟩
  · rintro ⟨y, rfl⟩
    rw [map_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply Subtype.ext
    exact AddSubgroup.torsionBy.nsmul_iff.mp (projection p A n y).property

/-- Finite-level reduction kills exactly the ideal multiple of the actual integral Tate module. -/
theorem ker_projection (n : ℕ) :
    LinearMap.ker (projection p A n) =
      (Ideal.span {(p : ℤ_[p]) ^ n}) • (⊤ : Submodule ℤ_[p] (integral p A)) := by
  ext x
  rw [LinearMap.mem_ker, projection_eq_zero_iff, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

/-- For every point group, finite-level reduction is the image of its actual Tate projection. -/
def reductionRangeEquiv (n : ℕ) :
    ((integral p A) ⧸
      ((Ideal.span {(p : ℤ_[p]) ^ n}) • (⊤ : Submodule ℤ_[p] (integral p A)))) ≃ₗ[ℤ_[p]]
        LinearMap.range (projection p A n) :=
  (Submodule.quotEquivOfEq _ _ (ker_projection p A n).symm).trans
    (projection p A n).quotKerEquivRange

/-- Divisibility of the point group makes each actual torsion transition surjective. -/
theorem transition_surjective (hpdiv : Function.Surjective (fun a : A => p • a)) (n : ℕ) :
    Function.Surjective (transition p A n) := by
  intro x
  obtain ⟨y, hy⟩ := hpdiv (x : A)
  change p • y = (x : A) at hy
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  rw [AddSubgroup.torsionBy.nsmul_iff, pow_succ', mul_nsmul, hy]
  exact AddSubgroup.torsionBy.nsmul_iff.mp x.property

/-- Every `p`-torsion point lifts to an actual compatible Tate family when the group is `p`-divisible. -/
theorem projection_one_surjective (hpdiv : Function.Surjective (fun a : A => p • a)) :
    Function.Surjective (projection p A 1) := by
  classical
  intro a
  let next (n : ℕ) (x : Torsion p A n) : Torsion p A (n + 1) :=
    Classical.choose (transition_surjective p A hpdiv n x)
  have hnext (n : ℕ) (x : Torsion p A n) : transition p A n (next n x) = x :=
    Classical.choose_spec (transition_surjective p A hpdiv n x)
  let seq : (n : ℕ) → Torsion p A (n + 1) :=
    fun n => Nat.rec a (fun n x => next (n + 1) x) n
  let x : integral p A := ⟨fun n => Nat.casesOn n 0 seq, by
    intro n
    cases n with
    | zero =>
      apply Subtype.ext
      change p • (a : A) = 0
      simpa only [pow_one] using AddSubgroup.torsionBy.nsmul_iff.mp a.property
    | succ n => exact hnext (n + 1) (seq n)⟩
  exact ⟨x, rfl⟩

/-- For a `p`-divisible point group, quotienting the actual Tate module by `p` gives its `p`-torsion. -/
def reductionEquiv (hpdiv : Function.Surjective (fun a : A => p • a)) :
    ((integral p A) ⧸
      ((Ideal.span {(p : ℤ_[p]) ^ 1}) • (⊤ : Submodule ℤ_[p] (integral p A)))) ≃ₗ[ℤ_[p]]
        Torsion p A 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_projection p A 1).symm).trans
    ((projection p A 1).quotKerEquivOfSurjective (projection_one_surjective p A hpdiv))


/-- The canonical coefficient algebra at a finite torsion level. -/
local instance torsionCoefficientAlgebra (n : ℕ) : Algebra ℤ_[p] (ZMod (p ^ n)) :=
  (PadicInt.toZModPow n).toAlgebra

/-- The existing `p`-adic action on torsion is restriction of its finite coefficient action. -/
local instance torsionCoefficientScalarTower (n : ℕ) :
    IsScalarTower ℤ_[p] (ZMod (p ^ n)) (Torsion p A n) where
  smul_assoc r s x := by
    change (PadicInt.toZModPow n r * s) • x = PadicInt.toZModPow n r • (s • x)
    exact mul_smul _ _ _

/-- Extend finite-level projection to the actual residual coefficient ring. -/
def residualProjection (n : ℕ) :
    ZMod (p ^ n) ⊗[ℤ_[p]] integral p A →ₗ[ZMod (p ^ n)] Torsion p A n :=
  (projection p A n).liftBaseChange (ZMod (p ^ n))

@[simp]
theorem residualProjection_tmul (n : ℕ) (a : ZMod (p ^ n)) (x : integral p A) :
    residualProjection p A n (a ⊗ₜ[ℤ_[p]] x) = a • projection p A n x := rfl

/-- Surjective finite-level projection becomes an isomorphism after the actual scalar reduction. -/
theorem residualProjection_bijective (n : ℕ)
    (hproj : Function.Surjective (projection p A n)) :
    Function.Bijective (residualProjection p A n) := by
  let I : Ideal ℤ_[p] := RingHom.ker (PadicInt.toZModPow n)
  have hs : Function.Surjective (Algebra.ofId ℤ_[p] (ZMod (p ^ n))) :=
    ZMod.ringHom_surjective (PadicInt.toZModPow n)
  let eS : (ℤ_[p] ⧸ I) ≃ₐ[ℤ_[p]] ZMod (p ^ n) :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId ℤ_[p] (ZMod (p ^ n))) hs
  have hker : I • (⊤ : Submodule ℤ_[p] (integral p A)) =
      LinearMap.ker (projection p A n) := by
    rw [ker_projection]
    change RingHom.ker (PadicInt.toZModPow n) • _ = _
    rw [PadicInt.ker_toZModPow]
  let e : (ZMod (p ^ n) ⊗[ℤ_[p]] integral p A) ≃ₗ[ℤ_[p]] Torsion p A n :=
    (eS.symm.toLinearEquiv.rTensor (integral p A)).trans
      ((TensorProduct.quotTensorEquivQuotSMul (integral p A) I).trans
        ((Submodule.quotEquivOfEq _ _ hker).trans
          ((projection p A n).quotKerEquivOfSurjective hproj)))
  have he (x : ZMod (p ^ n) ⊗[ℤ_[p]] integral p A) : residualProjection p A n x = e x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      obtain ⟨r, rfl⟩ := hs a
      have hr : eS.symm (algebraMap ℤ_[p] (ZMod (p ^ n)) r) = Ideal.Quotient.mk I r := by
        apply eS.injective
        rw [AlgEquiv.apply_symm_apply]
        exact (Ideal.quotientKerAlgEquivOfSurjective_mk hs r).symm
      change residualProjection p A n (algebraMap ℤ_[p] (ZMod (p ^ n)) r ⊗ₜ[ℤ_[p]] x) =
        (projection p A n).quotKerEquivOfSurjective hproj
          (Submodule.quotEquivOfEq _ _ hker
            (TensorProduct.quotTensorEquivQuotSMul (integral p A) I
              (eS.symm (algebraMap ℤ_[p] (ZMod (p ^ n)) r) ⊗ₜ[ℤ_[p]] x)))
      rw [hr, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
        residualProjection_tmul, map_smul, algebraMap_smul]
  have hfun : (residualProjection p A n : _ → _) = (e : _ → _) := funext he
  change Function.Bijective (residualProjection p A n : _ → _)
  rw [hfun]
  exact e.bijective

/-- Actual scalar reduction of a `p`-divisible point group's Tate module is its `p`-torsion. -/
def residualEquiv (hpdiv : Function.Surjective (fun a : A => p • a)) :
    (ZMod (p ^ 1) ⊗[ℤ_[p]] integral p A) ≃ₗ[ZMod (p ^ 1)] Torsion p A 1 :=
  LinearEquiv.ofBijective (residualProjection p A 1)
    (residualProjection_bijective p A 1 (projection_one_surjective p A hpdiv))

@[simp]
theorem residualEquiv_tmul (hpdiv : Function.Surjective (fun a : A => p • a))
    (a : ZMod (p ^ 1)) (x : integral p A) :
    residualEquiv p A hpdiv (a ⊗ₜ[ℤ_[p]] x) = a • projection p A 1 x := rfl


/-- Finite generation of the actual integral Tate module makes geometric `p`-torsion finite-dimensional. -/
theorem torsion_finite [Module.Finite ℤ_[p] (integral p A)]
    (hpdiv : Function.Surjective (fun a : A => p • a)) :
    Module.Finite (ZMod (p ^ 1)) (Torsion p A 1) :=
  Module.Finite.of_surjective (residualProjection p A 1)
    (residualEquiv p A hpdiv).surjective

/-- The dimension of actual `p`-torsion is the rank of the actual integral Tate module. -/
theorem torsion_finrank [Module.Finite ℤ_[p] (integral p A)]
    (hpdiv : Function.Surjective (fun a : A => p • a)) :
    Module.finrank (ZMod (p ^ 1)) (Torsion p A 1) = Module.finrank ℤ_[p] (integral p A) := by
  let : Fact (p ^ 1).Prime := ⟨by simpa only [pow_one] using (Fact.out : p.Prime)⟩
  rw [← (residualEquiv p A hpdiv).finrank_eq, Module.finrank_baseChange]

end TateModule
