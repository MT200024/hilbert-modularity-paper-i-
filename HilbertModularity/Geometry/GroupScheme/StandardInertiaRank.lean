/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientRank

/-! # Rank from the standard inertia realization

The simultaneous coefficient basis in [DarmonFibres, Proposition 3.4]
computes every labelled factor of the same family.
-/

public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct
namespace HilbertModularity.Hypergeometric

attribute [local irreducible] GroupScheme.geometricTensorTateAction
open HilbertModularity.Cyclotomic

/-- Each embedding-labelled generic Tate fibre of a standard-inertia family has dimension two. -/
theorem HasStandardInertiaRealization.finrank_labelledTateLocalSystem
    (N : ℕ) [NeZero N]
    (A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))))
    (φ : 𝓞 (realCyclotomicField N) →+* End A)
    (hfinite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 A).hom.hom.hom.left)
    (hetale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 A).hom.hom.hom.left)
    (hreal : HasStandardInertiaRealization N A φ hfinite hetale)
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    letI : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left :=
      fun n => hfinite (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    letI : ∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left :=
      fun n => hetale (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    Module.finrank L ((GroupScheme.labelledTateLocalSystem (RatFunc (realCyclotomicField N))
      A p L (realCyclotomicField N) φ hL σ).obj
      (Scheme.etaleFiberPoint (RatFunc (realCyclotomicField N))
        (ProjectiveLine.punctured (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))) = 2 := by
  let : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left :=
    fun n => hfinite (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
  let : ∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left :=
    fun n => hetale (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
  let V := TateModule.rational p
    (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ A.X))
  let : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
    Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
      A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
  have hr := hreal
  unfold HasStandardInertiaRealization at hr
  have hb : Nonempty (Module.Basis (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V) := by
    with_reducible exact ⟨(hr.choose_spec.choose_spec.2 p (Fact.out : p.Prime)).choose⟩
  obtain ⟨b⟩ := hb
  exact (GroupScheme.finrank_labelledTateLocalSystem_obj (I := Fin 2)
    (RatFunc (realCyclotomicField N)) A p L
    (realCyclotomicField N) φ
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) hL b σ).trans
      (Fintype.card_fin 2)

end HilbertModularity.Hypergeometric
