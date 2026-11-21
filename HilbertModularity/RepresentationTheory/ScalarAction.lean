/- Assembled by AxiomProver. -/

module

public import Mathlib.RepresentationTheory.Basic

/-! # Linear representations for a commuting coefficient action -/

@[expose] public section
namespace Representation
variable {R S G V : Type*} [Semiring R] [Semiring S] [Monoid G]
  [AddCommMonoid V] [Module R V]

/-- A commuting coefficient-ring action makes the same representation linear over that ring. -/
def withScalarAction (ρ : Representation R G V) (a : S →+* Module.End R V)
    (ha : ∀ g s, Commute (ρ g) (a s)) :
    letI : Module S V := Module.compHom V a
    Representation S G V := by
  letI : Module S V := Module.compHom V a
  refine
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := (ρ g).map_add
          map_smul' := ?_ }
      map_one' := ?_
      map_mul' := ?_ }
  · intro s v
    change ρ g (a s v) = a s (ρ g v)
    exact LinearMap.congr_fun (ha g s) v
  · apply LinearMap.ext
    intro v
    change ρ 1 v = v
    exact congrArg (fun f : Module.End R V => f v) ρ.map_one
  · intro g h
    apply LinearMap.ext
    intro v
    change ρ (g * h) v = ρ g (ρ h v)
    exact congrArg (fun f : Module.End R V => f v) (ρ.map_mul g h)

/-- Changing to a commuting coefficient action preserves the actual action on vectors. -/
@[simp] theorem withScalarAction_apply (ρ : Representation R G V)
    (a : S →+* Module.End R V) (ha : ∀ g s, Commute (ρ g) (a s)) (g : G) (v : V) :
    withScalarAction ρ a ha g v = ρ g v := rfl

end Representation
