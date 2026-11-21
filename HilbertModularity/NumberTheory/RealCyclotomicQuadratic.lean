/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.Cyclotomic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.RingTheory.Norm.Basic

/-! # The quadratic full cyclotomic extension of its real subfield

For an odd prime conductor, one and the chosen root form a basis over the
actual real cyclotomic field. The relative norm of root minus one is the
real parameter used to generate the RM prime; see [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

/-- The canonical inclusion makes the full cyclotomic field an algebra over its real subfield. -/
@[instance_reducible]
def realFieldAlgebra : Algebra (realCyclotomicField p) (cyclotomicField p) :=
  (IntermediateField.inclusion (realCyclotomicField_le p)).toRingHom.toAlgebra

attribute [local instance] realFieldAlgebra

/-- Cyclotomic conjugation is an involution on the actual full field. -/
theorem conjugation_involutive (x : cyclotomicField p) :
    conjugation p (conjugation p x) = x := by
  have h : (conjugation p).toAlgHom.comp (conjugation p).toAlgHom =
      AlgHom.id ℚ (cyclotomicField p) := by
    apply ((root_isPrimitiveRoot p).powerBasis ℚ).algHom_ext
    change conjugation p (conjugation p (root p)) = root p
    rw [conjugation_root, map_inv₀, conjugation_root, inv_inv]
  exact AlgHom.congr_fun h x

/-- An odd-prime primitive root is not fixed by inversion. -/
theorem root_sub_inv_ne_zero (hp : p ≠ 2) : root p - (root p)⁻¹ ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  have hpow : root p ^ 2 = 1 := by
    rw [pow_two]
    calc
      root p * root p = (root p)⁻¹ * root p := congrArg (fun z => z * root p) he
      _ = 1 := inv_mul_cancel₀ ((root_isPrimitiveRoot p).ne_zero (NeZero.ne p))
  have hd := (root_isPrimitiveRoot p).dvd_of_pow_eq_one 2 hpow
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  have hprime := (Fact.out : p.Prime).two_le
  omega

/-- Linear combinations of one and the chosen root over the real field. -/
def realQuadraticLinearMap :
    (realCyclotomicField p × realCyclotomicField p) →ₗ[realCyclotomicField p] cyclotomicField p where
  toFun x := algebraMap _ _ x.1 + algebraMap _ _ x.2 * root p
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
  map_smul' c x := by
    change algebraMap _ _ (c * x.1) + algebraMap _ _ (c * x.2) * root p =
      algebraMap _ _ c * (algebraMap _ _ x.1 + algebraMap _ _ x.2 * root p)
    simp only [map_mul]
    ring

/-- One and the root are linearly independent over the actual real field. -/
theorem realQuadraticLinearMap_injective (hp : p ≠ 2) :
    Function.Injective (realQuadraticLinearMap p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change algebraMap _ _ x.1 + algebraMap _ _ x.2 * root p = 0 at hx
  have hc := congrArg (conjugation p) hx
  change conjugation p
    (IntermediateField.inclusion (realCyclotomicField_le p) x.1 +
      IntermediateField.inclusion (realCyclotomicField_le p) x.2 * root p) = _ at hc
  rw [map_add, map_mul, conjugation_inclusion, conjugation_inclusion,
    conjugation_root, map_zero] at hc
  have hz : algebraMap (realCyclotomicField p) (cyclotomicField p) x.2 = 0 := by
    apply (mul_eq_zero.mp (show algebraMap _ _ x.2 * (root p - (root p)⁻¹) = 0 by
      linear_combination hx - hc)).resolve_right (root_sub_inv_ne_zero p hp)
  have hx2 : x.2 = 0 := (algebraMap (realCyclotomicField p) (cyclotomicField p)).injective
    (hz.trans (map_zero _).symm)
  have hx1 : x.1 = 0 := (algebraMap (realCyclotomicField p) (cyclotomicField p)).injective (by
    simpa only [hx2, map_zero, zero_mul, add_zero] using hx)
  exact Prod.ext hx1 hx2

/-- Every cyclotomic element is a real linear combination of one and the root. -/
theorem realQuadraticLinearMap_surjective (hp : p ≠ 2) :
    Function.Surjective (realQuadraticLinearMap p) := by
  intro x
  let c : cyclotomicField p := (x - conjugation p x) / (root p - (root p)⁻¹)
  have hc : conjugation p c = c := by
    dsimp [c]
    rw [map_div₀, map_sub, conjugation_involutive, map_sub,
      conjugation_root, map_inv₀, conjugation_root, inv_inv]
    rw [show conjugation p x - x = -(x - conjugation p x) by ring,
      show (root p)⁻¹ - root p = -(root p - (root p)⁻¹) by ring, neg_div_neg_eq]
  have hd : conjugation p (x - c * root p) = x - c * root p := by
    rw [map_sub, map_mul, hc, conjugation_root]
    have hmul : c * (root p - (root p)⁻¹) = x - conjugation p x :=
      div_mul_cancel₀ _ (root_sub_inv_ne_zero p hp)
    linear_combination hmul
  let a : realCyclotomicField p :=
    ⟨(x - c * root p : cyclotomicField p), (conjugation_eq_self_iff p _).mp hd⟩
  let b : realCyclotomicField p := ⟨(c : Qbar), (conjugation_eq_self_iff p c).mp hc⟩
  refine ⟨(a, b), ?_⟩
  change (x - c * root p) + c * root p = x
  ring

/-- Coordinates in the actual quadratic extension of the real cyclotomic field. -/
def realQuadraticEquiv (hp : p ≠ 2) :
    (realCyclotomicField p × realCyclotomicField p) ≃ₗ[realCyclotomicField p] cyclotomicField p :=
  LinearEquiv.ofBijective (realQuadraticLinearMap p)
    ⟨realQuadraticLinearMap_injective p hp, realQuadraticLinearMap_surjective p hp⟩

/-- The actual full cyclotomic field has real basis one and the chosen root. -/
def realQuadraticBasis (hp : p ≠ 2) :
    Module.Basis (Fin 2) (realCyclotomicField p) (cyclotomicField p) :=
  (Module.Basis.finTwoProd (realCyclotomicField p)).map (realQuadraticEquiv p hp)

@[simp]
theorem realQuadraticBasis_zero (hp : p ≠ 2) : realQuadraticBasis p hp 0 = 1 := by
  simp only [realQuadraticBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_zero]
  change algebraMap _ _ 1 + algebraMap _ _ 0 * root p = 1
  simp only [map_one, map_zero, zero_mul, add_zero]

@[simp]
theorem realQuadraticBasis_one (hp : p ≠ 2) : realQuadraticBasis p hp 1 = root p := by
  simp only [realQuadraticBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_one]
  change algebraMap _ _ 0 + algebraMap _ _ 1 * root p = root p
  simp only [map_one, map_zero, one_mul, zero_add]

/-- The full cyclotomic field has degree two over its actual real subfield. -/
theorem finrank_real_cyclotomic (hp : p ≠ 2) :
    Module.finrank (realCyclotomicField p) (cyclotomicField p) = 2 := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (realQuadraticBasis p hp)

/-- Multiplication by root minus one has the expected quadratic matrix over the real field. -/
theorem realQuadratic_leftMul_root_sub_one (hp : p ≠ 2) :
    Algebra.leftMulMatrix (realQuadraticBasis p hp) (root p - 1) =
      !![-1, -1; 1, tau p 1 - 1] := by
  have ht : algebraMap (realCyclotomicField p) (cyclotomicField p) (tau p 1) =
      root p + (root p)⁻¹ := by
    change IntermediateField.inclusion (realCyclotomicField_le p) (tau p 1) = _
    apply Subtype.ext
    simp [tau, root]
  have h0 : (root p - 1) * realQuadraticBasis p hp 0 =
      (-1 : realCyclotomicField p) • realQuadraticBasis p hp 0 + realQuadraticBasis p hp 1 := by
    simp only [realQuadraticBasis_zero, realQuadraticBasis_one, mul_one, neg_smul, one_smul]
    ring
  have h1 : (root p - 1) * realQuadraticBasis p hp 1 =
      (-1 : realCyclotomicField p) • realQuadraticBasis p hp 0 +
        (tau p 1 - 1) • realQuadraticBasis p hp 1 := by
    rw [realQuadraticBasis_zero, realQuadraticBasis_one]
    simp only [Algebra.smul_def, map_neg, map_one, map_sub, ht]
    field_simp [(root_isPrimitiveRoot p).ne_zero (NeZero.ne p)]
    ring
  apply Matrix.ext
  intro i j
  fin_cases j <;> rw [Algebra.leftMulMatrix_eq_repr_mul]
  · change (realQuadraticBasis p hp).repr ((root p - 1) * realQuadraticBasis p hp 0) i = _
    rw [h0]
    simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply]
    fin_cases i <;> norm_num
  · change (realQuadraticBasis p hp).repr ((root p - 1) * realQuadraticBasis p hp 1) i = _
    rw [h1]
    simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply]
    fin_cases i <;> norm_num

/-- The relative norm of the cyclotomic uniformizer is the actual real scaling parameter. -/
theorem norm_root_sub_one_real (hp : p ≠ 2) :
    Algebra.norm (realCyclotomicField p) (root p - 1) = 2 - tau p 1 := by
  rw [Algebra.norm_eq_matrix_det (realQuadraticBasis p hp),
    realQuadratic_leftMul_root_sub_one p hp, Matrix.det_fin_two]
  simp
  ring

end HilbertModularity.Cyclotomic
