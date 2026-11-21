/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Topology.TateModule
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Algebra

/-! # Group actions on Tate modules

An action by additive automorphisms acts covariantly on compatible torsion
families and on their rational scalar extension. The integral topology is the
subspace topology inherited from the product of the torsion levels.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (G A : Type*) [Monoid G] [AddCommGroup A]
    [DistribMulAction G A]

/-- The covariant integral Tate representation of an additive action. -/
def representation : Representation ℤ_[p] G (integral p A) where
  toFun g := map p (DistribSMul.toAddMonoidHom A g)
  map_one' := by
    ext x n
    exact one_smul G (x.val n : A)
  map_mul' g h := by
    ext x n
    exact mul_smul g h (x.val n : A)

/-- Galois acts on each torsion point of a compatible family. -/
@[simp]
theorem representation_projection (g : G) (x : integral p A) (n : ℕ) :
    (projection p A n (representation p G A g x) : A) =
      g • (projection p A n x : A) := rfl

/-- The covariant rational Tate representation. -/
def rationalRepresentation : Representation ℚ_[p] G (rational p A) where
  toFun g := (representation p G A g).baseChange ℚ_[p]
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' g h := by rw [map_mul, LinearMap.baseChange_mul]

/-- The action fixes rational coefficients and acts on the integral Tate factor. -/
@[simp]
theorem rationalRepresentation_tmul (g : G) (c : ℚ_[p]) (x : integral p A) :
    rationalRepresentation p G A g (c ⊗ₜ x) = c ⊗ₜ representation p G A g x := rfl

variable [TopologicalSpace A]

/-- Finite-level projection is continuous for the inverse-limit topology. -/
theorem continuous_projection (n : ℕ) : Continuous (projection p A n) :=
  (continuous_apply n).comp continuous_subtype_val

variable [TopologicalSpace G] [ContinuousSMul G A]

/-- Continuity on the torsion points implies continuity on each integral Tate vector. -/
theorem continuous_representation (x : integral p A) :
    Continuous (fun g => representation p G A g x) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  apply Continuous.subtype_mk
  exact continuous_id.smul continuous_const

/-- The induced action on the integral inverse limit is jointly continuous. -/
theorem continuous_representation_apply :
    Continuous (fun gx : G × integral p A => representation p G A gx.1 gx.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  apply Continuous.subtype_mk
  exact continuous_fst.smul
    (continuous_subtype_val.comp ((continuous_apply n).comp
      (continuous_subtype_val.comp continuous_snd)))

/-- Each rational Tate vector has a continuous orbit map. -/
theorem continuous_rationalRepresentation (x : rational p A) :
    Continuous (fun g => rationalRepresentation p G A g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x =>
    have h := (continuous_toRational p A).comp (continuous_representation p G A x)
    apply (h.const_smul c).congr
    intro g
    change c • ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] representation p G A g x) = _
    rw [rationalRepresentation_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

variable [LocallyCompactSpace G]

/-- The orbit maps form a linear map into the compact-open continuous-function space. -/
def orbitLinearMap : rational p A →ₗ[ℚ_[p]] C(G, rational p A) where
  toFun x := ⟨fun g => rationalRepresentation p G A g x,
    continuous_rationalRepresentation p G A x⟩
  map_add' x y := by
    ext g
    exact map_add (rationalRepresentation p G A g) x y
  map_smul' c x := by
    ext g
    exact map_smul (rationalRepresentation p G A g) c x

/-- The rational Tate action is jointly continuous for a locally compact acting group. -/
theorem continuous_rationalRepresentation_apply :
    Continuous (fun gx : G × rational p A => rationalRepresentation p G A gx.1 gx.2) := by
  have h : Continuous (orbitLinearMap p G A) := by
    apply (continuous_linearMap_iff p A _).mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hc := (continuous_toRational p A).comp
      ((continuous_representation_apply p G A).comp continuous_swap)
    exact hc
  exact (h.comp continuous_snd).eval continuous_fst

end TateModule
