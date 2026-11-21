/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricIrreducibility
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Fixed-label cusp matrices of the Darmon family

The coefficient tensor basis in [DarmonFibres, §3, Propositions 3.2 and 3.4]
is specialized along the prescribed embedding, not along its inverse. This
implements the scalar-label step in [TripathiGoswami, proof of RMgeneral].
The inertia generators retain their conjugacy choices; no density assertion
about these choices is made here.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj NumberField

namespace HilbertModularity.Monodromy

/-- Entrywise specialization preserves the entire standard cusp triple. -/
theorem standardTriple_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) (i : Fin 3) :
    (standardTriple t i : Matrix (Fin 2) (Fin 2) R).map f =
      (standardTriple (f t) i : Matrix (Fin 2) (Fin 2) S) := by
  have h0 : (U0 : Matrix (Fin 2) (Fin 2) R).map f = U0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U0]
  have h1 : (U1 t).map f = U1 (f t) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U1, map_ofNat]
  fin_cases i
  · exact h0
  · exact h1
  · change (Uinf t).map f = Uinf (f t)
    apply Eq.symm
    apply Matrix.inv_eq_right_inv
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M.map f)
      (U0_mul_U1_mul_Uinf t)
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one, h0, h1] using h

end HilbertModularity.Monodromy

namespace Representation

/-- A coordinate action determines the matrix without expanding its carrier. -/
theorem toMatrix_of_coordinate_action
    {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (b : Module.Basis (Fin 2) R V) (g : G)
    (M : Matrix (Fin 2) (Fin 2) R)
    (h : ∀ v, (b.repr (ρ g v) : Fin 2 → R) = M *ᵥ b.repr v) :
    LinearMap.toMatrix b b (ρ g) = M := by
  ext i j
  have hv := congrFun (h (b j)) i
  simpa only [LinearMap.toMatrix_apply, Module.Basis.repr_self,
    Finsupp.single_eq_pi_single, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply] using hv

/-- Scalar extension specializes the matrix in the scalar-extended basis. -/
theorem toMatrix_baseChange_basis
    {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
    (L : Type*) [CommRing L] [Algebra R L] (ρ : Representation R G V)
    (b : Module.Basis (Fin 2) R V) (g : G) :
    LinearMap.toMatrix (b.baseChange L) (b.baseChange L) ((ρ.baseChange L) g) =
      (LinearMap.toMatrix b b (ρ g)).map (algebraMap R L) := by
  ext i j
  simp [LinearMap.toMatrix_apply, baseChange_tmul, Algebra.smul_def]

/-- A standard cusp matrix specializes with its parameter. -/
theorem toMatrix_baseChange_standardTriple
    {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
    (L : Type*) [CommRing L] [Algebra R L] (ρ : Representation R G V)
    (b : Module.Basis (Fin 2) R V) (g : G) (t : R) (s : L) (i : Fin 3)
    (h : LinearMap.toMatrix b b (ρ g) = HilbertModularity.Monodromy.standardTriple t i)
    (ht : algebraMap R L t = s) :
    LinearMap.toMatrix (b.baseChange L) (b.baseChange L) ((ρ.baseChange L) g) =
      HilbertModularity.Monodromy.standardTriple s i := by
  rw [toMatrix_baseChange_basis, h, HilbertModularity.Monodromy.standardTriple_map, ht]

/-- Coordinate matrices specialize entrywise under extension of scalars. -/
theorem toMatrix_baseChange_of_coordinate_action
    {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
    (L : Type*) [CommRing L] [Algebra R L] (ρ : Representation R G V)
    (b : Module.Basis (Fin 2) R V) (g : G)
    (M : Matrix (Fin 2) (Fin 2) R)
    (h : ∀ v, (b.repr (ρ g v) : Fin 2 → R) = M *ᵥ b.repr v) :
    LinearMap.toMatrix (b.baseChange L) (b.baseChange L) ((ρ.baseChange L) g) =
      M.map (algebraMap R L) := by
  rw [toMatrix_baseChange_basis, toMatrix_of_coordinate_action ρ b g M h]

end Representation

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic Algebra.TensorProduct

attribute [local irreducible] GroupScheme.geometricTensorTateAction
  GroupScheme.coefficientTateMonodromy GroupScheme.rationalTateMonodromy

/-- The native coefficient-tensor representation has the prescribed cusp matrices. -/
theorem HasStandardInertiaRealization.coefficient_matrices
    (N : ℕ) [NeZero N]
    (A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))))
    (φ : 𝓞 (realCyclotomicField N) →+* End A)
    (hfinite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 A).hom.hom.hom.left)
    (hetale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 A).hom.hom.hom.left)
    (hreal : HasStandardInertiaRealization N A φ hfinite hetale)
    (p : ℕ) [Fact p.Prime]
    :
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
    let ρ := (GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
      A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
    ∃ (γ c : Fin 3 →
        (AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[RatFunc (realCyclotomicField N)]
          AlgebraicClosure (RatFunc (realCyclotomicField N))))
      (b : Module.Basis (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V),
      ((∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map (MulAut.conj (c i)).toMonoidHom) ∧
        ∃ ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N)),
          ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ ∧
          ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1)) ∧
      ∀ i, LinearMap.toMatrix b b (ρ
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ i))) =
        (Monodromy.standardTriple ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) i :
          Matrix (Fin 2) (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N)) := by
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
  let γ := hr.choose
  let c := hr.choose_spec.choose
  have hclosure := hr.choose_spec.choose_spec.1
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
  refine ⟨γ, c, b, hclosure, ?_⟩
  intro i
  apply Representation.toMatrix_of_coordinate_action
  intro v
  have hv := GroupScheme.coefficientTateMonodromy_apply
    (RatFunc (realCyclotomicField N)) A p (realCyclotomicField N) φ
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))
    (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ i)) v
  exact (congrArg (fun w : V => (b.repr w : Fin 2 →
    ℚ_[p] ⊗[ℚ] realCyclotomicField N)) hv).trans (hb i v)

/-- The prescribed coefficient specialization has the three standard cusp
matrices in one basis, at the actual inertia generators of the realization. -/
theorem HasStandardInertiaRealization.specialization_matrices
    (N : ℕ) [NeZero N]
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
    let ρ := (GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
      A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).baseChange L
    ∃ (γ c : Fin 3 →
        (AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[RatFunc (realCyclotomicField N)]
          AlgebraicClosure (RatFunc (realCyclotomicField N))))
      (b : Module.Basis (Fin 2) L (L ⊗[ℚ_[p] ⊗[ℚ] realCyclotomicField N] V)),
      ((∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map (MulAut.conj (c i)).toMonoidHom) ∧
        ∃ ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N)),
          ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ ∧
          ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1)) ∧
      ∀ i, LinearMap.toMatrix b b (ρ
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ i))) =
        (Monodromy.standardTriple (σ (tau N 1)) i : Matrix (Fin 2) (Fin 2) L) := by
  let : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left :=
    fun n => hfinite (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
  let : ∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left :=
    fun n => hetale (p ^ n) (pow_pos (Fact.out : p.Prime).pos n)
  intro V ρ
  let : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
    Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
      A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
  let : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
  have hm := HasStandardInertiaRealization.coefficient_matrices N A φ hfinite hetale hreal p
  let γ := hm.choose
  let c := hm.choose_spec.choose
  let b : Module.Basis (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V := by
    with_reducible exact hm.choose_spec.choose_spec.choose
  have hc := hm.choose_spec.choose_spec.choose_spec.1
  have hb : ∀ i, LinearMap.toMatrix b b
      (GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
        A p (realCyclotomicField N) φ
        (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))
        (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
          (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ i))) =
      (Monodromy.standardTriple ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) i :
        Matrix (Fin 2) (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N)) := by
    with_reducible exact hm.choose_spec.choose_spec.choose_spec.2
  have ht : coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ
      ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) = σ (tau N 1) := by
    rw [coefficientTensorEmbedding_tmul, map_one, one_mul]
  with_reducible refine ⟨γ, c, b.baseChange L, hc, ?_⟩
  intro i
  have h := Representation.toMatrix_baseChange_standardTriple L
    (GroupScheme.coefficientTateMonodromy (RatFunc (realCyclotomicField N))
      A p (realCyclotomicField N) φ
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)))
    b (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N))
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) (γ i))
    ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) (σ (tau N 1)) i (hb i) ht
  with_reducible exact h

end HilbertModularity.Hypergeometric
