/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.ResidualDeterminant
public import HilbertModularity.RepresentationTheory.CoefficientDual
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import HilbertModularity.RepresentationTheory.DeterminantCharacter
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Integral dual lattices and contragredient representations

The dual of a finite free full lattice extends canonically to the dual of its
coefficient vector space. Its image is a full lattice and is stable under the
contragredient action. This is the integral covariant/dual convention used for
labelled Tate factors in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {R G M : Type*} [CommRing R] [Group G] [AddCommMonoid M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- Finite free dual representations commute equivariantly with scalar extension. -/
def dualBaseChangeEquiv (A : Type*) [CommRing A] [Algebra R A]
    (ρ : Representation R G M) : (ρ.dual.baseChange A).Equiv (ρ.baseChange A).dual := by
  let ibc : IsBaseChange A (_root_.TensorProduct.mk R A M 1) :=
    IsBaseChange.of_equiv (LinearEquiv.refl A (A ⊗[R] M)) (fun _ => rfl)
  exact .mk ibc.toDualBaseChange (by
    intro g
    apply LinearMap.ext
    intro u
    induction u using _root_.TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, LinearMap.comp_apply] using congrArg₂ (· + ·) hx hy
    | tmul a f =>
      apply ibc.algHom_ext
      intro v
      change ibc.toDualBaseChange (a ⊗ₜ[R] ρ.dual g f) ((1 : A) ⊗ₜ[R] v) =
        ibc.toDualBaseChange (a ⊗ₜ[R] f) ((1 : A) ⊗ₜ[R] ρ g⁻¹ v)
      exact (ibc.toDualBaseChange_tmul a (ρ.dual g f) v).trans
        (ibc.toDualBaseChange_tmul a f (ρ g⁻¹ v)).symm)

/-- The extended dual pairing has the expected scalar-extension formula. -/
theorem dualBaseChangeEquiv_tmul (A : Type*) [CommRing A] [Algebra R A]
    (ρ : Representation R G M) (a : A) (f : Module.Dual R M) (v : M) :
    dualBaseChangeEquiv A ρ (a ⊗ₜ[R] f) ((1 : A) ⊗ₜ[R] v) = a * algebraMap R A (f v) :=
  IsBaseChange.toDualBaseChange_tmul
    (IsBaseChange.of_equiv (f := _root_.TensorProduct.mk R A M 1)
      (LinearEquiv.refl A (A ⊗[R] M)) (fun _ => rfl)) a f v

end Representation

namespace Submodule

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
  (M : Submodule R V) [IsLattice K M] [Module.Free R M]

/-- The inclusion of a full free lattice exhibits its ambient space as scalar extension. -/
theorem isBaseChange_of_isLattice : IsBaseChange K M.subtype := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  exact IsBaseChange.of_equiv (latticeScalarExtensionEquiv M (Module.Free.chooseBasis R M))
    (fun v => by simp [latticeScalarExtensionEquiv_tmul])

/-- Extend an integral linear functional uniquely to the coefficient vector space. -/
def dualLatticeMap : Module.Dual R M →ₗ[R] Module.Dual K V :=
  (isBaseChange_of_isLattice M).toDual

@[simp]
theorem dualLatticeMap_apply (f : Module.Dual R M) (v : M) :
    dualLatticeMap M f (v : V) = algebraMap R K (f v) :=
  (isBaseChange_of_isLattice M).toDual_comp_apply f v

/-- The integral dual lattice inside the coefficient-space dual. -/
def dualLattice : Submodule R (Module.Dual K V) := LinearMap.range (dualLatticeMap M)

/-- Extending integral functionals loses no information. -/
theorem dualLatticeMap_injective : Function.Injective (dualLatticeMap M) := by
  intro f h he
  apply LinearMap.ext
  intro v
  apply IsFractionRing.injective R K
  simpa only [dualLatticeMap_apply] using congrArg (fun ell => ell (v : V)) he

/-- The extended integral dual is a full lattice in the coefficient-space dual. -/
instance dualLattice_isLattice : IsLattice K (dualLattice M) := by
  let : Module.Finite R M := Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := M))
  refine ⟨Submodule.fg_range _, ?_⟩
  apply top_unique
  intro f hf
  clear hf
  induction f using (isBaseChange_of_isLattice M).dual.inductionOn with
  | tmul f => exact Submodule.subset_span ⟨f, rfl⟩
  | smul a f hf => exact Submodule.smul_mem _ a hf
  | add f h hf hh => exact Submodule.add_mem _ hf hh

/-- The lattice of extended functionals is the actual integral module dual. -/
def dualLatticeEquiv : Module.Dual R M ≃ₗ[R] dualLattice M :=
  LinearEquiv.ofInjective (dualLatticeMap M) (dualLatticeMap_injective M)

/-- The dual lattice consists exactly of coefficient-linear functionals integral on the original lattice. -/
theorem mem_dualLattice_iff (f : Module.Dual K V) :
    f ∈ dualLattice M ↔ ∀ v : M, ∃ r : R, algebraMap R K r = f (v : V) := by
  constructor
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, (dualLatticeMap_apply M h v).symm⟩
  · intro hf
    choose a ha using hf
    let h : Module.Dual R M :=
      { toFun := a
        map_add' := by
          intro v w
          apply IsFractionRing.injective R K
          rw [ha, map_add, ha, ha]
          exact f.map_add _ _
        map_smul' := by
          intro r v
          apply IsFractionRing.injective R K
          change algebraMap R K (a (r • v)) = algebraMap R K (r * a v)
          rw [ha, map_mul, ha]
          change f (r • (v : V)) = algebraMap R K r * f (v : V)
          rw [← algebraMap_smul K r (v : V), map_smul, smul_eq_mul] }
    refine ⟨h, ?_⟩
    apply (isBaseChange_of_isLattice M).algHom_ext
    intro v
    exact (dualLatticeMap_apply M h v).trans (ha v)

end Submodule

namespace Representation

variable {R K G V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Group G] [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
  (ρ : Representation K G V) (S : Subrepresentation (ρ.restrictScalars R))
  [Submodule.IsLattice K S.toSubmodule] [Module.Free R S.toSubmodule]

/-- Extending integral dual functionals intertwines the actual contragredient actions. -/
def dualLatticeIntertwiner :
    S.toRepresentation.dual.IntertwiningMap (ρ.dual.restrictScalars R) where
  toLinearMap := Submodule.dualLatticeMap S.toSubmodule
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply (Submodule.isBaseChange_of_isLattice S.toSubmodule).algHom_ext
    intro v
    change Submodule.dualLatticeMap S.toSubmodule (S.toRepresentation.dual g f) (v : V) =
      Submodule.dualLatticeMap S.toSubmodule f (ρ g⁻¹ (v : V))
    rw [Submodule.dualLatticeMap_apply]
    exact (Submodule.dualLatticeMap_apply S.toSubmodule f (S.toRepresentation g⁻¹ v)).symm

/-- The integral dual lattice is stable under the contragredient representation. -/
def dualLatticeSubrepresentation : Subrepresentation (ρ.dual.restrictScalars R) :=
  (dualLatticeIntertwiner ρ S).range

/-- A full stable lattice gives a full stable contragredient lattice. -/
instance dualLatticeSubrepresentation_isLattice :
    Submodule.IsLattice K (dualLatticeSubrepresentation ρ S).toSubmodule :=
  Submodule.dualLattice_isLattice S.toSubmodule

/-- The action on the constructed dual image lattice is exactly the integral contragredient action. -/
def dualLatticeRepresentationEquiv :
    S.toRepresentation.dual.Equiv (dualLatticeSubrepresentation ρ S).toRepresentation :=
  .mk (Submodule.dualLatticeEquiv S.toSubmodule) (by
    intro g
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact congrArg (fun l => l f) ((dualLatticeIntertwiner ρ S).isIntertwining' g))

/-- Reducing the constructed dual lattice gives the contragredient of the original lattice reduction. -/
def dualLatticeReductionEquiv (k : Type*) [CommRing k] [Algebra R k] :
    ((dualLatticeSubrepresentation ρ S).toRepresentation.baseChange k).Equiv
      (S.toRepresentation.baseChange k).dual :=
  let : Module.Finite R S.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := S.toSubmodule))
  let e := (dualLatticeRepresentationEquiv ρ S).symm
  let ek : ((dualLatticeSubrepresentation ρ S).toRepresentation.baseChange k).Equiv
      (S.toRepresentation.dual.baseChange k) :=
    .mk (e.toLinearEquiv.baseChange R k _ _)
      (e.toIntertwiningMap.baseChange k).isIntertwining'
  ek.trans (dualBaseChangeEquiv k S.toRepresentation)

end Representation

namespace Representation

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- Passing from the covariant representation to its contragredient inverts its actual determinant character. -/
theorem determinantCharacter_dual (ρ : Representation R G V) :
    determinantCharacter ρ.dual = (determinantCharacter ρ)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change LinearMap.det ((ρ g⁻¹).dualMap) = (((determinantCharacter ρ g)⁻¹ : Rˣ) : R)
  rw [LinearMap.det_dualMap]
  exact congrArg (fun u : Rˣ => (u : R)) ((determinantCharacter ρ).map_inv g)

end Representation

namespace Representation

variable {R K G V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Group G] [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
  (ρ : Representation K G V) (S : Subrepresentation (ρ.restrictScalars R))
  [Submodule.IsLattice K S.toSubmodule] [Module.Free R S.toSubmodule]

/-- The determinant of the actual dual lattice reduction is the inverse residual determinant. -/
theorem dualLatticeReduction_det (k : Type*) [Field k] [Algebra R k] (g : G) :
    LinearMap.det (((dualLatticeSubrepresentation ρ S).toRepresentation.baseChange k) g) =
      (LinearMap.det ((S.toRepresentation.baseChange k) g))⁻¹ := by
  let : Module.Finite R S.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := S.toSubmodule))
  let e := dualLatticeReductionEquiv ρ S k
  have he :
      e.toLinearEquiv.toLinearMap ∘ₗ
          ((dualLatticeSubrepresentation ρ S).toRepresentation.baseChange k) g ∘ₗ
            e.toLinearEquiv.symm.toLinearMap = (S.toRepresentation.baseChange k).dual g := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun l => l (e.toLinearEquiv.symm v)) (e.isIntertwining' g)
    change e.toLinearEquiv
      (((dualLatticeSubrepresentation ρ S).toRepresentation.baseChange k) g (e.toLinearEquiv.symm v)) =
      (S.toRepresentation.baseChange k).dual g (e.toLinearEquiv (e.toLinearEquiv.symm v)) at h
    change e.toLinearEquiv
      (((dualLatticeSubrepresentation ρ S).toRepresentation.baseChange k) g (e.toLinearEquiv.symm v)) =
      (S.toRepresentation.baseChange k).dual g v
    simpa only [LinearEquiv.apply_symm_apply] using h
  calc
    _ = LinearMap.det ((S.toRepresentation.baseChange k).dual g) := by
      rw [← he]
      exact (LinearMap.det_conj _ e.toLinearEquiv).symm
    _ = _ := by
      have h := congrArg (fun χ : G →* kˣ => (χ g : k))
        (determinantCharacter_dual (S.toRepresentation.baseChange k))
      change LinearMap.det ((S.toRepresentation.baseChange k).dual g) =
        (((determinantCharacter (S.toRepresentation.baseChange k) g)⁻¹ : kˣ) : k) at h
      simpa only [Units.val_inv_eq_inv_val, determinantCharacter_coe] using h

end Representation
