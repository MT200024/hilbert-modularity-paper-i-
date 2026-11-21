/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Rational extension of actions of the ring of integers

The integral basis identifies the rational scalar extension of a number field's
ring of integers with the field itself. Consequently an action of the ring of
integers on a rational vector space extends canonically to the number field.
-/

@[expose] public noncomputable section

open scoped NumberField TensorProduct

namespace NumberField.RingOfIntegers

variable (K : Type*) [Field K] [NumberField K]

/-- The canonical map from the rationalized ring of integers to its number field. -/
def rationalizationMap : ℚ ⊗[ℤ] (𝓞 K) →ₐ[ℚ] K :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ K) (algebraMap (𝓞 K) K).toIntAlgHom
    (fun _ _ => Commute.all _ _)

@[simp]
theorem rationalizationMap_tmul (q : ℚ) (x : 𝓞 K) :
    rationalizationMap K (q ⊗ₜ[ℤ] x) = q • (x : K) := by
  simp [rationalizationMap, Algebra.smul_def]

/-- The canonical rationalization map is bijective, as witnessed by an integral basis. -/
theorem rationalizationMap_bijective : Function.Bijective (rationalizationMap K) := by
  let b := (basis K).baseChange ℚ
  let e := b.equiv (NumberField.integralBasis K) (Equiv.refl _)
  have h : (rationalizationMap K).toLinearMap = e.toLinearMap := by
    apply b.ext
    intro i
    change rationalizationMap K (b i) = e (b i)
    simp only [e, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [b, Module.Basis.baseChange_apply, NumberField.integralBasis_apply]
  change Function.Bijective (rationalizationMap K).toLinearMap
  rw [h]
  exact e.bijective

/-- Rationalizing the ring of integers recovers the number field. -/
def rationalizationEquiv : ℚ ⊗[ℤ] (𝓞 K) ≃ₐ[ℚ] K :=
  AlgEquiv.ofBijective (rationalizationMap K) (rationalizationMap_bijective K)

@[simp]
theorem rationalizationEquiv_tmul (q : ℚ) (x : 𝓞 K) :
    rationalizationEquiv K (q ⊗ₜ[ℤ] x) = q • (x : K) :=
  rationalizationMap_tmul K q x

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- An action of the ring of integers on a rational algebra extends to the number field. -/
def rationalExtension (f : 𝓞 K →+* A) : K →ₐ[ℚ] A :=
  (Algebra.TensorProduct.lift (Algebra.ofId ℚ A) f.toIntAlgHom
    (fun q x => show Commute ((Algebra.ofId ℚ A) q) (f.toIntAlgHom x) from
      Algebra.commutes q (f x))).comp (rationalizationEquiv K).symm.toAlgHom

/-- The rational extension agrees with the original map on algebraic integers. -/
@[simp]
theorem rationalExtension_apply (f : 𝓞 K →+* A) (x : 𝓞 K) :
    rationalExtension K f (x : K) = f x := by
  have hx : (rationalizationEquiv K).symm (x : K) = (1 : ℚ) ⊗ₜ[ℤ] x := by
    apply (rationalizationEquiv K).injective
    simp
  change (Algebra.TensorProduct.lift (Algebra.ofId ℚ A) f.toIntAlgHom
    (fun q x => show Commute ((Algebra.ofId ℚ A) q) (f.toIntAlgHom x) from
      Algebra.commutes q (f x))) ((rationalizationEquiv K).symm (x : K)) = f x
  rw [hx]
  simp

/-- An extension from the ring of integers is unique among rational algebra maps. -/
theorem rationalExtension_unique (f : 𝓞 K →+* A) (g : K →ₐ[ℚ] A)
    (h : ∀ x : 𝓞 K, g (x : K) = f x) : g = rationalExtension K f := by
  have hg : g.comp (rationalizationEquiv K).toAlgHom =
      (rationalExtension K f).comp (rationalizationEquiv K).toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    ext x
    simp [h]
  ext x
  obtain ⟨t, rfl⟩ := (rationalizationEquiv K).surjective x
  exact AlgHom.congr_fun hg t

/-- Extending coefficients preserves commutation with a fixed endomorphism. -/
theorem rationalExtension_commute (f : 𝓞 K →+* A) (b : A)
    (h : ∀ a : 𝓞 K, Commute (f a) b) (x : K) : Commute (rationalExtension K f x) b := by
  obtain ⟨t, rfl⟩ := (rationalizationEquiv K).surjective x
  induction t using TensorProduct.inductionOn with
  | tmul q a =>
    change Commute ((Algebra.TensorProduct.lift (Algebra.ofId ℚ A) f.toIntAlgHom
      (fun q x => show Commute ((Algebra.ofId ℚ A) q) (f.toIntAlgHom x) from
      Algebra.commutes q (f x)))
        ((rationalizationEquiv K).symm (rationalizationEquiv K (q ⊗ₜ[ℤ] a)))) b
    rw [AlgEquiv.symm_apply_apply]
    exact Commute.mul_left (show Commute (algebraMap ℚ A q) b from Algebra.commutes q b) (h a)
  | add x y hx hy => simpa only [map_add] using hx.add_left hy

section TensorExtension

variable (L : Type*) [CommRing L] [Algebra ℚ L] [Algebra L A]
  [IsScalarTower ℚ L A]

/-- Extending an integer coefficient action to a scalar extension of its number field. -/
def tensorExtension (f : 𝓞 K →+* A) : L ⊗[ℚ] K →ₐ[L] A :=
  Algebra.TensorProduct.lift (Algebra.ofId L A) (rationalExtension K f)
    (fun l x => show Commute ((Algebra.ofId L A) l) (rationalExtension K f x) from
      Algebra.commutes l (rationalExtension K f x))

@[simp]
theorem tensorExtension_tmul (f : 𝓞 K →+* A) (l : L) (x : K) :
    tensorExtension K L f (l ⊗ₜ[ℚ] x) = algebraMap L A l * rationalExtension K f x := rfl

/-- Integer coefficients act through the original ring homomorphism. -/
theorem tensorExtension_integer (f : 𝓞 K →+* A) (x : 𝓞 K) :
    tensorExtension K L f ((1 : L) ⊗ₜ[ℚ] (x : K)) = f x := by
  simp

/-- Scalar extension preserves commutation with the original integer coefficient action. -/
theorem tensorExtension_commute (f : 𝓞 K →+* A) (b : A)
    (h : ∀ a : 𝓞 K, Commute (f a) b) (x : L ⊗[ℚ] K) :
    Commute (tensorExtension K L f x) b := by
  induction x using TensorProduct.inductionOn with
  | tmul l x =>
    exact Commute.mul_left
      (show Commute (algebraMap L A l) b from Algebra.commutes l b)
      (rationalExtension_commute K f b h x)
  | add x y hx hy => simpa only [map_add] using hx.add_left hy

end TensorExtension

section Intertwining

variable {R V W : Type*} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]
  [AddCommGroup W] [Module R W] [Module ℚ W] [IsScalarTower ℚ R W]

/-- A linear map intertwining integer coefficient actions intertwines their rational extensions. -/
theorem rationalExtension_intertwines
    (a : 𝓞 K →+* Module.End R V) (b : 𝓞 K →+* Module.End R W)
    (f : V →ₗ[R] W) (h : ∀ (x : 𝓞 K) (v : V), f (a x v) = b x (f v))
    (x : K) (v : V) : f (rationalExtension K a x v) = rationalExtension K b x (f v) := by
  obtain ⟨t, rfl⟩ := (rationalizationEquiv K).surjective x
  induction t using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalizationEquiv_tmul, map_smul, rationalExtension_apply]
    change f (q • a x v) = q • b x (f v)
    rw [f.map_smul_of_tower, h]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Intertwining integer actions suffices to intertwine their full tensor coefficient actions. -/
theorem tensorExtension_intertwines
    (a : 𝓞 K →+* Module.End R V) (b : 𝓞 K →+* Module.End R W)
    (f : V →ₗ[R] W) (h : ∀ (x : 𝓞 K) (v : V), f (a x v) = b x (f v))
    (x : R ⊗[ℚ] K) (v : V) :
    f (tensorExtension K R a x v) = tensorExtension K R b x (f v) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change f (r • rationalExtension K a x v) = r • rationalExtension K b x (f v)
    rw [f.map_smul, rationalExtension_intertwines K a b f h]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end Intertwining

end NumberField.RingOfIntegers

namespace NumberField.RingOfIntegers
variable (K : Type*) [Field K] [NumberField K]
  {A : Type*} [Ring A] [Algebra ℚ A]
  (L : Type*) [CommRing L] [Algebra ℚ L] [Algebra L A] [IsScalarTower ℚ L A]

/-- The tensor extension of an integral coefficient action is uniquely determined on integers. -/
theorem tensorExtension_unique (f : 𝓞 K →+* A) (g : L ⊗[ℚ] K →ₐ[L] A)
    (h : ∀ a : 𝓞 K, g ((1 : L) ⊗ₜ[ℚ] (a : K)) = f a) :
    g = tensorExtension K L f := by
  have hg : (g.restrictScalars ℚ).comp
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] L ⊗[ℚ] K) = rationalExtension K f :=
    rationalExtension_unique K f _ h
  apply Algebra.TensorProduct.ext'
  intro l x
  have hx := AlgHom.congr_fun hg x
  change g ((1 : L) ⊗ₜ[ℚ] x) = rationalExtension K f x at hx
  rw [tensorExtension_tmul, ← Algebra.smul_def]
  rw [show l ⊗ₜ[ℚ] x = l • ((1 : L) ⊗ₜ[ℚ] x) by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hx]

variable {B : Type*} [Ring B] [Algebra ℚ B] [Algebra L B] [IsScalarTower ℚ L B]

/-- Tensor extension commutes with every homomorphism of the target coefficient algebras. -/
theorem tensorExtension_comp (f : 𝓞 K →+* A) (g : A →ₐ[L] B) :
    g.comp (tensorExtension K L f) = tensorExtension K L (g.toRingHom.comp f) := by
  apply tensorExtension_unique
  intro a
  simp only [AlgHom.comp_apply, tensorExtension_integer, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

end NumberField.RingOfIntegers
