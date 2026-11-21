/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod

/-! # Representations on torsion groups

Every additive automorphism of a `ZMod n`-module is linear. Consequently an
action by additive automorphisms gives a representation over `ZMod n`.
-/

@[expose] public section

namespace Representation

variable {G A : Type*} [Monoid G] [AddCommGroup A] (n : ℕ) [Module (ZMod n) A]

/-- An action by additive automorphisms is linear over the natural residue coefficient ring. -/
def ofAddAutZMod (ρ : G →* Multiplicative (AddAut A)) : Representation (ZMod n) G A where
  toFun g := (ρ g).toAdd.toAddMonoidHom.toZModLinearMap n
  map_one' := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun e => e.toAdd v) (map_one ρ)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun e => e.toAdd v) (map_mul ρ g h)

/-- Linearization preserves the original additive action on every vector. -/
@[simp]
theorem ofAddAutZMod_apply (ρ : G →* Multiplicative (AddAut A)) (g : G) (v : A) :
    ofAddAutZMod n ρ g v = (ρ g).toAdd v := rfl

end Representation
