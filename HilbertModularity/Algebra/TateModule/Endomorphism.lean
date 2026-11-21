/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule

/-! # Endomorphisms of Tate modules

An endomorphism of an additive group acts on its compatible torsion families.
The action preserves addition and composition, and therefore gives ring maps
on integral and rational Tate modules. Commuting endomorphisms remain commuting
on these modules.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (A : Type*) [AddCommGroup A]

/-- Endomorphisms act on the integral Tate module as a ring of linear maps. -/
def endomorphismMap : AddMonoid.End A →+* Module.End ℤ_[p] (integral p A) where
  toFun f := map p f
  map_one' := map_id p
  map_mul' f g := map_comp p g f
  map_zero' := by ext x n; rfl
  map_add' f g := by ext x n; rfl

@[simp]
theorem endomorphismMap_apply (f : AddMonoid.End A) : endomorphismMap p A f = map p f := rfl

/-- Endomorphisms act on the rational Tate module after extension of scalars. -/
def rationalEndomorphismMap : AddMonoid.End A →+* Module.End ℚ_[p] (rational p A) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (integral p A)).toRingHom.comp (endomorphismMap p A)

@[simp]
theorem rationalEndomorphismMap_apply (f : AddMonoid.End A) :
    rationalEndomorphismMap p A f = rationalMap p f := rfl

@[simp]
theorem rationalMap_id : rationalMap p (AddMonoidHom.id A) = LinearMap.id := by
  simp only [rationalMap, map_id, LinearMap.baseChange_id]

/-- Covariant maps on rational Tate modules preserve composition. -/
theorem rationalMap_comp {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) :
    rationalMap p (g.comp f) = (rationalMap p g).comp (rationalMap p f) := by
  simp only [rationalMap, map_comp, LinearMap.baseChange_comp]

end TateModule
