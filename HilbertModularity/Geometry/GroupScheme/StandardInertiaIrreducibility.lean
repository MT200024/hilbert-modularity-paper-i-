/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientArithmeticMonodromy
public import HilbertModularity.Geometry.ProjectiveLine.GenericFundamentalGroup
public import HilbertModularity.RepresentationTheory.Quotient
public import HilbertModularity.LinearAlgebra.CoefficientTensorFactor
public import HilbertModularity.Monodromy.AbsoluteIrreducibility
public import HilbertModularity.Monodromy.Cyclotomic
public import HilbertModularity.Geometry.ProjectiveLine.CuspArithmetic

/-! # Irreducibility of the chosen Darmon monodromy

The simultaneous inertia basis from [DarmonFibres, Propositions 3.2 and 3.4]
contains two transverse transvections. Evaluating the coefficient tensor algebra
at any field-valued embedding preserves their distinct fixed lines, as in
[TripathiGoswami, admissible triple lemma].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj NumberField

namespace HilbertModularity.Hypergeometric

attribute [local irreducible] GroupScheme.geometricTensorTateAction
  GroupScheme.coefficientTateMonodromy GroupScheme.rationalTateMonodromy

open _root_.HilbertModularity.Cyclotomic Algebra.TensorProduct

/-- Every field-valued coefficient specialization of the actual native generic
Tate monodromy of the single chosen Darmon family is irreducible. -/
theorem HasStandardInertiaRealization.specialization_isIrreducible
    (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))))
    (φ : 𝓞 (realCyclotomicField N) →+* End A)
    (hfinite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 A).hom.hom.hom.left)
    (hetale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 A).hom.hom.hom.left)
    (hreal : HasStandardInertiaRealization N A φ hfinite hetale)
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    letI : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left :=
      fun n => hfinite (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    letI : ∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left :=
      fun n => hetale (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    let V := TateModule.rational p
      (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
      Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
        A p (realCyclotomicField N) φ
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
      (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
    ((GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
      A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).baseChange L).IsIrreducible := by
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
  let : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
  have hr := hreal
  unfold HasStandardInertiaRealization at hr
  let γ := hr.choose
  let c := hr.choose_spec.choose
  have hclosure := hr.choose_spec.choose_spec.1.1
  have hbasis := hr.choose_spec.choose_spec.2 p (Fact.out : p.Prime)
  let b : Module.Basis (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V := by
    with_reducible exact hbasis.choose
  have hb : ∀ (i : Fin 3) (v : V),
      (b.repr (GroupScheme.rationalTateMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) A p
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ i)) v) :
          Fin 2 → ℚ_[p] ⊗[ℚ] realCyclotomicField N) =
      ((Monodromy.standardTriple ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) i :
        Matrix (Fin 2) (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N)) *ᵥ b.repr v) := by
    with_reducible exact hbasis.choose_spec
  apply Monodromy.isIrreducible_specialization_of_standard_cusps L _ b
      (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ 0))
      (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ 1))
      ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1)
  · change coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ
      ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) ≠ 2
    rw [coefficientTensorEmbedding_tmul, map_one, one_mul]
    intro h
    exact tau_ne_two N 1 hN (Nat.coprime_one_left N)
      (σ.injective (h.trans (map_ofNat σ 2).symm))
  · intro v
    change (b.repr (GroupScheme.coefficientTateMonodromy
      (RatFunc (realCyclotomicField N)) A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) _ v) :
        Fin 2 → ℚ_[p] ⊗[ℚ] realCyclotomicField N) = _
    rw [GroupScheme.coefficientTateMonodromy_apply]
    with_reducible simpa [Monodromy.standardTriple] using hb 0 v
  · intro v
    change (b.repr (GroupScheme.coefficientTateMonodromy
      (RatFunc (realCyclotomicField N)) A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) _ v) :
        Fin 2 → ℚ_[p] ⊗[ℚ] realCyclotomicField N) = _
    rw [GroupScheme.coefficientTateMonodromy_apply]
    with_reducible simpa [Monodromy.standardTriple] using hb 1 v

/-- The same field-valued specialization is irreducible on the kernel of the
actual structure-map action on finite étale covers of the constant field. -/
theorem HasStandardInertiaRealization.arithmeticKernel_specialization_isIrreducible
    (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))))
    (φ : 𝓞 (realCyclotomicField N) →+* End A)
    (hfinite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 A).hom.hom.hom.left)
    (hetale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 A).hom.hom.hom.left)
    (hreal : HasStandardInertiaRealization N A φ hfinite hetale)
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    letI : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left :=
      fun n => hfinite (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    letI : ∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left :=
      fun n => hetale (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
    let V := TateModule.rational p
      (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ A.X))
    letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
      Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
        A p (realCyclotomicField N) φ
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
    letI : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
      (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
    (Representation.baseChange L ((GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
      A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).comp
        (Scheme.etaleFundamentalGroupMap
          (ProjectiveLine.puncturedToSpec (realCyclotomicField N))
          (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).ker.subtype)).IsIrreducible := by
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
  let : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
  have hr := hreal
  unfold HasStandardInertiaRealization at hr
  let γ := hr.choose
  let c := hr.choose_spec.choose
  have hclosure := hr.choose_spec.choose_spec.1.1
  have hbasis := hr.choose_spec.choose_spec.2 p (Fact.out : p.Prime)
  let b : Module.Basis (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V := by
    with_reducible exact hbasis.choose
  have hb : ∀ (i : Fin 3) (v : V),
      (b.repr (GroupScheme.rationalTateMonodromy (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) A p
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ i)) v) :
          Fin 2 → ℚ_[p] ⊗[ℚ] realCyclotomicField N) =
      ((Monodromy.standardTriple ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) i :
        Matrix (Fin 2) (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N)) *ᵥ b.repr v) := by
    with_reducible exact hbasis.choose_spec
  have hmem (i : Fin 3) : γ i ∈
      (![RatFunc.affineInertia (realCyclotomicField N) 0,
         RatFunc.affineInertia (realCyclotomicField N) 1,
         RatFunc.infinityInertia (realCyclotomicField N)] i).map
           (MulAut.conj (c i)).toMonoidHom := by
    rw [← hclosure i]
    exact (Subgroup.zpowers (γ i)).le_topologicalClosure (Subgroup.mem_zpowers (γ i))
  have hzero := ProjectiveLine.conjugate_affineInertia_mem_arithmetic_kernel
    (realCyclotomicField N) 0 (c 0) (γ 0) (by simpa using hmem 0)
  have hone := ProjectiveLine.conjugate_affineInertia_mem_arithmetic_kernel
    (realCyclotomicField N) 1 (c 1) (γ 1) (by simpa using hmem 1)
  apply Monodromy.isIrreducible_specialization_of_standard_cusps L _ b
      ⟨Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ 0), hzero⟩
      ⟨Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ 1), hone⟩
      ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1)
  · change coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ
      ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) ≠ 2
    rw [coefficientTensorEmbedding_tmul, map_one, one_mul]
    intro h
    exact tau_ne_two N 1 hN (Nat.coprime_one_left N)
      (σ.injective (h.trans (map_ofNat σ 2).symm))
  · intro v
    change (b.repr (GroupScheme.coefficientTateMonodromy
      (RatFunc (realCyclotomicField N)) A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) _ v) :
        Fin 2 → ℚ_[p] ⊗[ℚ] realCyclotomicField N) = _
    rw [GroupScheme.coefficientTateMonodromy_apply]
    with_reducible simpa [Monodromy.standardTriple] using hb 0 v
  · intro v
    change (b.repr (GroupScheme.coefficientTateMonodromy
      (RatFunc (realCyclotomicField N)) A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) _ v) :
        Fin 2 → ℚ_[p] ⊗[ℚ] realCyclotomicField N) = _
    rw [GroupScheme.coefficientTateMonodromy_apply]
    with_reducible simpa [Monodromy.standardTriple] using hb 1 v

end HilbertModularity.Hypergeometric
