/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule

/-! # Additive equivalences on actual Tate modules -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace TateModule
variable (p : ℕ) [Fact p.Prime] {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- An additive group equivalence induces the covariant equivalence on actual integral Tate modules. -/
def mapEquiv (e : A ≃+ B) : integral p A ≃ₗ[ℤ_[p]] integral p B :=
  LinearEquiv.ofLinearMap (map p e.toAddMonoidHom) (map p e.symm.toAddMonoidHom)
    (by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      funext n
      apply Subtype.ext
      exact e.apply_symm_apply _)
    (by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      funext n
      apply Subtype.ext
      exact e.symm_apply_apply _)

/-- The integral equivalence acts by the original point map at every torsion level. -/
@[simp]
theorem mapEquiv_projection (e : A ≃+ B) (v : integral p A) (n : ℕ) :
    ((mapEquiv p e v).val n).val = e (v.val n).val := rfl

/-- Scalar extension gives the covariant equivalence of rational Tate modules. -/
def rationalMapEquiv (e : A ≃+ B) : rational p A ≃ₗ[ℚ_[p]] rational p B :=
  LinearEquiv.baseChange ℤ_[p] ℚ_[p] _ _ (mapEquiv p e)

/-- The rational equivalence fixes coefficients and applies the integral equivalence. -/
@[simp]
theorem rationalMapEquiv_tmul (e : A ≃+ B) (c : ℚ_[p]) (v : integral p A) :
    rationalMapEquiv p e (c ⊗ₜ v) = c ⊗ₜ mapEquiv p e v := rfl

variable {A' B' : Type*} [AddCommGroup A'] [AddCommGroup B']

/-- A commuting square of point maps gives a commuting square of integral Tate maps. -/
theorem mapEquiv_natural (eA : A ≃+ A') (eB : B ≃+ B')
    (f : A →+ B) (g : A' →+ B') (h : ∀ a, eB (f a) = g (eA a)) :
    (mapEquiv p eB).toLinearMap.comp (map p f) =
      (map p g).comp (mapEquiv p eA).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact h (v.val n).val

/-- Rational Tate equivalences preserve commuting squares of the original point maps. -/
theorem rationalMapEquiv_natural (eA : A ≃+ A') (eB : B ≃+ B')
    (f : A →+ B) (g : A' →+ B') (h : ∀ a, eB (f a) = g (eA a)) :
    (rationalMapEquiv p eB).toLinearMap.comp (rationalMap p f) =
      (rationalMap p g).comp (rationalMapEquiv p eA).toLinearMap := by
  have he := congrArg (fun z : integral p A →ₗ[ℤ_[p]] integral p B' =>
    z.baseChange ℚ_[p]) (mapEquiv_natural p eA eB f g h)
  change ((mapEquiv p eB).toLinearMap.baseChange ℚ_[p]).comp
      ((map p f).baseChange ℚ_[p]) =
    ((map p g).baseChange ℚ_[p]).comp ((mapEquiv p eA).toLinearMap.baseChange ℚ_[p])
  simpa only [LinearMap.baseChange_comp] using he

end TateModule
