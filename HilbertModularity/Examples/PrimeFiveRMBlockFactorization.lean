/- Assembled by AxiomProver. -/

module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RepresentationTheory.Character
public import HilbertModularity.RepresentationTheory.CoefficientDecomposition
public import Mathlib.Tactic.Ring

/-! # Characteristic polynomial of the two RM summands

The selected curve's real-multiplication action splits its four-dimensional
Tate space into two rank-two coefficient factors. Once the specialization map
and the two labels provide an intertwining equivalence, the polynomial product
is elementary linear algebra. The specialization and labels must still be
constructed on the selected Jacobian.
-/

public noncomputable section

namespace HilbertModularity.Examples

open Polynomial

/-- An ordered pair of coefficient embeddings can start with any prescribed
embedding when the coefficient field has exactly two embeddings. -/
theorem exists_finTwo_equiv_with_first
    {I : Type*} [Fintype I] (hcard : Fintype.card I = 2) (i : I) :
    ∃ e : Fin 2 ≃ I, e 0 = i := by
  let e : Fin 2 ≃ I := Fintype.equivOfCardEq (by simpa using hcard.symm)
  obtain ⟨j, hj⟩ := e.surjective i
  fin_cases j
  · exact ⟨e, hj⟩
  · refine ⟨(Equiv.swap (0 : Fin 2) 1).trans e, ?_⟩
    simpa using hj

/-- The reverse characteristic polynomial of a rank-two operator, over any
field containing the RM traces. -/
theorem charpolyRev_fin_two_general {L : Type*} [Field L]
    (M : Matrix (Fin 2) (Fin 2) L) :
    M.charpolyRev = 1 - C M.trace * X + C M.det * X ^ 2 := by
  simp [Matrix.charpolyRev, Matrix.det_fin_two, Matrix.trace_fin_two,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply]
  ring

/-- A Frobenius operator conjugate to two labelled operators has their product
characteristic polynomial. This is the algebraic step needed after the
coefficient-labelled good-reduction comparison. -/
theorem charpoly_of_two_labelled_factors
    {L V W₁ W₂ : Type*} [Field L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [AddCommGroup W₁] [Module L W₁] [FiniteDimensional L W₁]
    [AddCommGroup W₂] [Module L W₂] [FiniteDimensional L W₂]
    (f : Module.End L V) (f₁ : Module.End L W₁) (f₂ : Module.End L W₂)
    (e : V ≃ₗ[L] W₁ × W₂)
    (he : e.conj f = f₁.prodMap f₂) :
    f.charpoly = f₁.charpoly * f₂.charpoly := by
  calc
    f.charpoly = (e.conj f).charpoly := (e.charpoly_conj f).symm
    _ = (f₁.prodMap f₂).charpoly := by rw [he]
    _ = f₁.charpoly * f₂.charpoly := LinearMap.charpoly_prodMap f₁ f₂

/-- In chosen bases, the reverse characteristic polynomial has the same
product decomposition. Its constant term is one, matching the convention of
the worked finite-field polynomials. -/
theorem charpolyRev_of_two_labelled_factors
    {L V W₁ W₂ : Type*} [Field L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [AddCommGroup W₁] [Module L W₁] [FiniteDimensional L W₁]
    [AddCommGroup W₂] [Module L W₂] [FiniteDimensional L W₂]
    {ι ι₁ ι₂ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (f : Module.End L V) (f₁ : Module.End L W₁) (f₂ : Module.End L W₂)
    (e : V ≃ₗ[L] W₁ × W₂)
    (he : e.conj f = f₁.prodMap f₂)
    (b : Module.Basis ι L V) (b₁ : Module.Basis ι₁ L W₁)
    (b₂ : Module.Basis ι₂ L W₂) :
    (LinearMap.toMatrix b b f).charpolyRev =
      (LinearMap.toMatrix b₁ b₁ f₁).charpolyRev *
        (LinearMap.toMatrix b₂ b₂ f₂).charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly,
    ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
  rw [charpoly_of_two_labelled_factors f f₁ f₂ e he]
  exact Polynomial.reverse_mul_of_domain f₁.charpoly f₂.charpoly

/-- Once the *actual* full polynomial and the two determinant-q RM factors
are available, their traces give the numerical product expected by the worked
example. The full polynomial and operator decomposition remain genuine
premises; no numerical factor or label is assumed. -/
theorem polynomial_factorization_of_two_labelled_factors
    {L V W₁ W₂ : Type*} [Field L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [AddCommGroup W₁] [Module L W₁] [FiniteDimensional L W₁]
    [AddCommGroup W₂] [Module L W₂] [FiniteDimensional L W₂]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Module.End L V) (f₁ : Module.End L W₁) (f₂ : Module.End L W₂)
    (e : V ≃ₗ[L] W₁ × W₂) (he : e.conj f = f₁.prodMap f₂)
    (b : Module.Basis ι L V)
    (b₁ : Module.Basis (Fin 2) L W₁) (b₂ : Module.Basis (Fin 2) L W₂)
    (q : L) (R : L[X])
    (h₁ : (LinearMap.toMatrix b₁ b₁ f₁).det = q)
    (h₂ : (LinearMap.toMatrix b₂ b₂ f₂).det = q)
    (hfull : (LinearMap.toMatrix b b f).charpolyRev = R) :
    (1 - C (LinearMap.toMatrix b₁ b₁ f₁).trace * X + C q * X ^ 2) *
      (1 - C (LinearMap.toMatrix b₂ b₂ f₂).trace * X + C q * X ^ 2) = R := by
  have hprod := charpolyRev_of_two_labelled_factors f f₁ f₂ e he b b₁ b₂
  rw [charpolyRev_fin_two_general, charpolyRev_fin_two_general, h₁, h₂] at hprod
  exact hprod.symm.trans hfull

/-- The two-coordinate version applies directly to a coefficient-labelled
idempotent decomposition indexed by `Fin 2`. -/
theorem charpolyRev_of_two_coordinate_factors
    {L : Type*} [Field L]
    (W : Fin 2 → Type*)
    [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)]
    [∀ i, FiniteDimensional L (W i)]
    (f : ∀ i, Module.End L (W i))
    (F : Module.End L (∀ i, W i))
    (hF : ∀ v i, F v i = f i (v i))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι L (∀ i, W i))
    (b₀ : Module.Basis (Fin 2) L (W 0))
    (b₁ : Module.Basis (Fin 2) L (W 1)) :
    (LinearMap.toMatrix b b F).charpolyRev =
      (LinearMap.toMatrix b₀ b₀ (f 0)).charpolyRev *
        (LinearMap.toMatrix b₁ b₁ (f 1)).charpolyRev := by
  let e := LinearEquiv.piFinTwo L W
  have he : e.conj F = (f 0).prodMap (f 1) := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change F (e.symm v) 0 = f 0 v.1
      rw [hF]
      simp [e, LinearEquiv.piFinTwo_symm_apply]
    · change F (e.symm v) 1 = f 1 v.2
      rw [hF]
      simp [e, LinearEquiv.piFinTwo_symm_apply]
  exact charpolyRev_of_two_labelled_factors F (f 0) (f 1) e he b b₀ b₁

/-- Any two-element index of coefficient embeddings can be oriented by an
explicit equivalence from `Fin 2`; the two factors retain that order. -/
theorem charpolyRev_of_two_embedding_factors
    {L I : Type*} [Field L] [Fintype I]
    (W : I → Type*)
    [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)]
    [∀ i, FiniteDimensional L (W i)]
    (labels : Fin 2 ≃ I)
    (f : ∀ i, Module.End L (W i))
    (F : Module.End L (∀ i, W i))
    (hF : ∀ v i, F v i = f i (v i))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι L (∀ i, W i))
    (b₀ : Module.Basis (Fin 2) L (W (labels 0)))
    (b₁ : Module.Basis (Fin 2) L (W (labels 1))) :
    (LinearMap.toMatrix b b F).charpolyRev =
      (LinearMap.toMatrix b₀ b₀ (f (labels 0))).charpolyRev *
        (LinearMap.toMatrix b₁ b₁ (f (labels 1))).charpolyRev := by
  let r := (LinearEquiv.piCongrLeft L W labels).symm
  let t := LinearEquiv.piFinTwo L (fun j => W (labels j))
  let e := r.trans t
  have he : e.conj F = (f (labels 0)).prodMap (f (labels 1)) := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change F (e.symm v) (labels 0) = f (labels 0) v.1
      rw [hF]
      change f (labels 0) ((LinearEquiv.piCongrLeft L W labels)
        (Fin.cons v.1 (Fin.cons v.2 finZeroElim)) (labels 0)) = f (labels 0) v.1
      congr 1
      exact Equiv.piCongrLeft_apply_apply W labels _ 0
    · change F (e.symm v) (labels 1) = f (labels 1) v.2
      rw [hF]
      change f (labels 1) ((LinearEquiv.piCongrLeft L W labels)
        (Fin.cons v.1 (Fin.cons v.2 finZeroElim)) (labels 1)) = f (labels 1) v.2
      congr 1
      exact Equiv.piCongrLeft_apply_apply W labels _ 1
  exact charpolyRev_of_two_labelled_factors
    F (f (labels 0)) (f (labels 1)) e he b b₀ b₁

/-- An equivariant change of basis preserves the actual Frobenius matrix. -/
theorem toMatrix_map_representationEquiv
    {L G V W ι : Type*} [Field L] [Group G]
    [AddCommGroup V] [Module L V]
    [AddCommGroup W] [Module L W]
    [Fintype ι] [DecidableEq ι]
    {ρ : Representation L G V} {τ : Representation L G W}
    (e : ρ.Equiv τ) (b : Module.Basis ι L V) (g : G) :
    LinearMap.toMatrix (b.map e.toLinearEquiv) (b.map e.toLinearEquiv) (τ g) =
      LinearMap.toMatrix b b (ρ g) := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  ext v
  change e.toLinearEquiv.symm (τ g (e.toLinearEquiv v)) = ρ g v
  have h := e.toIntertwiningMap.isIntertwining ρ τ g v
  change e.toLinearEquiv (ρ g v) = τ g (e.toLinearEquiv v) at h
  rw [← h, LinearEquiv.symm_apply_apply]

/-- An equivariant decomposition into a two-element family transports the
full Frobenius polynomial to the two labelled factors in the chosen order. -/
theorem charpolyRev_of_two_factorRepresentation
    {L G V I : Type*} [Field L] [Group G] [Fintype I]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (W : I → Type*)
    [∀ i, AddCommGroup (W i)] [∀ i, Module L (W i)]
    [∀ i, FiniteDimensional L (W i)]
    (ρ : Representation L G V)
    (τ : ∀ i, Representation L G (W i))
    (e : ρ.Equiv (Representation.pi τ))
    (labels : Fin 2 ≃ I) (g : G)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι L V)
    (b₀ : Module.Basis (Fin 2) L (W (labels 0)))
    (b₁ : Module.Basis (Fin 2) L (W (labels 1))) :
    (LinearMap.toMatrix b b (ρ g)).charpolyRev =
      (LinearMap.toMatrix b₀ b₀ (τ (labels 0) g)).charpolyRev *
        (LinearMap.toMatrix b₁ b₁ (τ (labels 1) g)).charpolyRev := by
  have hm : LinearMap.toMatrix (b.map e.toLinearEquiv)
      (b.map e.toLinearEquiv) ((Representation.pi τ) g) =
        LinearMap.toMatrix b b (ρ g) := by
    rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
    congr 1
    ext v
    change e.toLinearEquiv.symm ((Representation.pi τ) g (e.toLinearEquiv v)) = ρ g v
    have h := e.toIntertwiningMap.isIntertwining ρ (Representation.pi τ) g v
    change e.toLinearEquiv (ρ g v) =
      (Representation.pi τ) g (e.toLinearEquiv v) at h
    rw [← h, LinearEquiv.symm_apply_apply]
  rw [← hm]
  exact charpolyRev_of_two_embedding_factors W labels
    (fun i => τ i g) ((Representation.pi τ) g)
    (by intro v i; rfl) (b.map e.toLinearEquiv) b₀ b₁

end HilbertModularity.Examples
