/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.FiniteCharacterPeriods
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Periods with a coefficient field

A twisted orbit sum gives a unit in the split coefficient tensor. Its components
can be made simultaneously nonzero by independence of field embeddings and
avoidance of finitely many proper subspaces over an infinite ground field.
This retains the permutation of coefficient labels in [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Classical

namespace FiniteCharacter

variable {R K E L : Type*} [Field R] [Field K] [Field E] [Field L]
  [Algebra R K] [Algebra K E] [Algebra R E] [IsScalarTower R K E] [Algebra R L]
  (F : FiniteGaloisIntermediateField K E) (χ : Gal(F/K) →* Lˣ)

/-- The character-weighted sum of the Galois conjugates of an element. -/
def orbitTensor (a : F) : E ⊗[R] L :=
  ∑ g : Gal(F/K), (g a : E) ⊗ₜ[R] (χ g : L)

/-- Evaluation of a twisted orbit sum at one coefficient embedding. -/
def orbitEvaluation (τ : L →ₐ[R] E) : F →ₗ[R] E :=
  ∑ g : Gal(F/K), τ (χ g : L) •
    ((F.toIntermediateField.val.comp g.toAlgHom).restrictScalars R).toLinearMap

@[simp]
theorem orbitEvaluation_apply (τ : L →ₐ[R] E) (a : F) :
    orbitEvaluation F χ τ a = ∑ g : Gal(F/K), (g a : E) * τ (χ g : L) := by
  simp [orbitEvaluation, mul_comm]

/-- Independence of distinct embeddings prevents an orbit evaluation from vanishing identically. -/
theorem orbitEvaluation_ne_zero (τ : L →ₐ[R] E) : orbitEvaluation F χ τ ≠ 0 := by
  have hinj : Function.Injective (fun g : Gal(F/K) =>
      (F.toIntermediateField.val.comp g.toAlgHom).restrictScalars R) := by
    intro g h he
    ext a
    exact DFunLike.congr_fun he a
  have hlin := (linearIndependent_algHom_toLinearMap R F E).comp _ hinj
  intro hz
  have h := (Fintype.linearIndependent_iff.mp hlin) (fun g => τ (χ g : L)) hz 1
  simp at h

/-- The orbit tensor transforms by the inverse of its coefficient character. -/
theorem orbitTensor_equivariance (a : F) (g : Gal(E/K)) :
    Algebra.TensorProduct.map (g.restrictScalars R).toAlgHom (AlgHom.id R L) (orbitTensor (R := R) F χ a) *
      ((1 : E) ⊗ₜ[R] (χ (AlgEquiv.restrictNormalHom F g) : L)) = orbitTensor (R := R) F χ a := by
  let r := AlgEquiv.restrictNormalHom F g
  have hact (σ : Gal(F/K)) : g (σ a : E) = ((r * σ) a : E) :=
    (AlgEquiv.restrictNormalHom_apply F.toIntermediateField g (σ a)).symm
  simp only [orbitTensor, map_sum, Finset.sum_mul, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  calc
    _ = ∑ σ : Gal(F/K), ((r * σ) a : E) ⊗ₜ[R] (χ (r * σ) : L) := by
      apply Finset.sum_congr rfl
      intro σ _
      change g (σ a : E) ⊗ₜ[R] ((χ σ : L) * (χ r : L)) = _
      rw [hact, map_mul, Units.val_mul, mul_comm (χ σ : L)]
    _ = _ := Fintype.sum_bijective (fun σ => r * σ) (Group.mulLeft_bijective r) _ _
      (fun _ => rfl)

variable [Infinite R] [FiniteDimensional R L]

/-- One element makes every coefficient evaluation of its twisted orbit sum nonzero. -/
theorem exists_orbitEvaluation_ne_zero :
    ∃ a : F, ∀ τ : L →ₐ[R] E, orbitEvaluation F χ τ a ≠ 0 := by
  have h (τ : L →ₐ[R] E) : (orbitEvaluation F χ τ).ker ≠ ⊤ := by
    intro htop
    apply orbitEvaluation_ne_zero F χ τ
    ext a
    exact (LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top))
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun τ : L →ₐ[R] E => (orbitEvaluation F χ τ).ker) h
  exact ⟨a, ha⟩

/-- A splitting equivalence turns simultaneous nonvanishing into an actual tensor unit. -/
theorem exists_isUnit_orbitTensor
    (e : E ⊗[R] L ≃ₐ[E] ((L →ₐ[R] E) → E))
    (he : ∀ a b τ, e (a ⊗ₜ[R] b) τ = a * τ b) :
    ∃ a : F, IsUnit (orbitTensor (R := R) F χ a) := by
  obtain ⟨a, ha⟩ := exists_orbitEvaluation_ne_zero (R := R) F χ
  refine ⟨a, ?_⟩
  have hu : IsUnit (e (orbitTensor (R := R) F χ a)) := by
    apply Pi.isUnit_iff.mpr
    intro τ
    apply isUnit_iff_ne_zero.mpr
    simpa [orbitTensor, he] using ha τ
  simpa using hu.map e.symm.toAlgHom

variable [IsGalois K E]

/-- A coefficient-valued open-kernel character has an invertible algebraic tensor period. -/
theorem exists_tensor_period_of_isOpen_ker
    (χ : Gal(E/K) →* Lˣ) (hopen : IsOpen (χ.ker : Set Gal(E/K)))
    (e : E ⊗[R] L ≃ₐ[E] ((L →ₐ[R] E) → E))
    (he : ∀ a b τ, e (a ⊗ₜ[R] b) τ = a * τ b) :
    ∃ c : (E ⊗[R] L)ˣ, ∀ g : Gal(E/K),
      Algebra.TensorProduct.map (g.restrictScalars R).toAlgHom (AlgHom.id R L) (c : E ⊗[R] L) *
        ((1 : E) ⊗ₜ[R] (χ g : L)) = c := by
  obtain ⟨F, ψ, hψ⟩ := exists_finite_galois_factor χ hopen
  obtain ⟨a, ha⟩ := exists_isUnit_orbitTensor F ψ e he
  refine ⟨ha.unit, fun g => ?_⟩
  simpa only [IsUnit.unit_spec, hψ] using orbitTensor_equivariance (R := R) F ψ a g

/-- Continuous finite-image coefficient characters possess invertible tensor periods. -/
theorem exists_tensor_period_of_continuous_finite_range
    [TopologicalSpace Lˣ] [T1Space Lˣ]
    (χ : Gal(E/K) →* Lˣ) (hχ : Continuous χ) (hfin : (Set.range χ).Finite)
    (e : E ⊗[R] L ≃ₐ[E] ((L →ₐ[R] E) → E))
    (he : ∀ a b τ, e (a ⊗ₜ[R] b) τ = a * τ b) :
    ∃ c : (E ⊗[R] L)ˣ, ∀ g : Gal(E/K),
      Algebra.TensorProduct.map (g.restrictScalars R).toAlgHom (AlgHom.id R L) (c : E ⊗[R] L) *
        ((1 : E) ⊗ₜ[R] (χ g : L)) = c :=
  exists_tensor_period_of_isOpen_ker χ (χ.isOpen_ker_of_finite_range hχ hfin) e he

/-- A positive finite-order bound supplies the finite-image hypothesis for tensor periods. -/
theorem exists_tensor_period_of_continuous_pow_eq_one
    [TopologicalSpace Lˣ] [T1Space Lˣ]
    (χ : Gal(E/K) →* Lˣ) (hχ : Continuous χ) {n : ℕ} (hn : n ≠ 0)
    (hpow : ∀ g, χ g ^ n = 1)
    (e : E ⊗[R] L ≃ₐ[E] ((L →ₐ[R] E) → E))
    (he : ∀ a b τ, e (a ⊗ₜ[R] b) τ = a * τ b) :
    ∃ c : (E ⊗[R] L)ˣ, ∀ g : Gal(E/K),
      Algebra.TensorProduct.map (g.restrictScalars R).toAlgHom (AlgHom.id R L) (c : E ⊗[R] L) *
        ((1 : E) ⊗ₜ[R] (χ g : L)) = c :=
  exists_tensor_period_of_continuous_finite_range χ hχ
    (χ.finite_range_of_pow_eq_one hn hpow) e he

omit [Infinite R] [FiniteDimensional R L] [IsGalois K E] in
/-- Equivariant embeddings commute with the action on a coefficient tensor. -/
theorem tensor_map_equivariant {C : Type*} [Field C] [Algebra R C]
    (j : E →ₐ[R] C) (g : Gal(E/K)) (γ : C →ₐ[R] C)
    (hγ : ∀ x, γ (j x) = j (g x)) (x : E ⊗[R] L) :
    Algebra.TensorProduct.map γ (AlgHom.id R L)
        (Algebra.TensorProduct.map j (AlgHom.id R L) x) =
      Algebra.TensorProduct.map j (AlgHom.id R L)
        (Algebra.TensorProduct.map (g.restrictScalars R).toAlgHom (AlgHom.id R L) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.map_tmul, hγ]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Algebraic coefficient-tensor periods remain units and periods in an equivariant overfield. -/
theorem exists_tensor_period_in_overfield {C : Type*} [Field C] [Algebra R C]
    (j : E →ₐ[R] C) (ρ : Gal(E/K) → (C →ₐ[R] C))
    (hρ : ∀ g x, ρ g (j x) = j (g x))
    (χ : Gal(E/K) →* Lˣ) (hopen : IsOpen (χ.ker : Set Gal(E/K)))
    (e : E ⊗[R] L ≃ₐ[E] ((L →ₐ[R] E) → E))
    (he : ∀ a b τ, e (a ⊗ₜ[R] b) τ = a * τ b) :
    ∃ c : (C ⊗[R] L)ˣ, ∀ g : Gal(E/K),
      Algebra.TensorProduct.map (ρ g) (AlgHom.id R L) (c : C ⊗[R] L) *
        ((1 : C) ⊗ₜ[R] (χ g : L)) = c := by
  obtain ⟨c, hc⟩ := exists_tensor_period_of_isOpen_ker χ hopen e he
  let f : E ⊗[R] L →ₐ[R] C ⊗[R] L :=
    Algebra.TensorProduct.map j (AlgHom.id R L)
  refine ⟨Units.map f.toMonoidHom c, fun g => ?_⟩
  change Algebra.TensorProduct.map (ρ g) (AlgHom.id R L) (f (c : E ⊗[R] L)) *
    ((1 : C) ⊗ₜ[R] (χ g : L)) = f (c : E ⊗[R] L)
  rw [tensor_map_equivariant j g (ρ g) (hρ g)]
  simpa [f] using congrArg f (hc g)

end FiniteCharacter
