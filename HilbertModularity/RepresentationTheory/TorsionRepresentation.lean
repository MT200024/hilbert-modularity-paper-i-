/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.TateModule

/-! # Tate representations from compatible finite-level actions

An action on every torsion level, commuting with the transition maps, acts on
the integral Tate module. This construction does not require an action on the
entire ambient group of geometric points.
-/

@[expose] public noncomputable section

namespace TateModule

section
variable (p : ℕ) [Fact p.Prime] {G A : Type*} [Monoid G] [AddCommGroup A]

/-- Additive automorphisms of a torsion level preserve its canonical `p`-adic scalar action. -/
def torsionRepresentationOfAddAut (n : ℕ)
    (ρ : G →* Multiplicative (AddAut (Torsion p A n))) :
    Representation ℤ_[p] G (Torsion p A n) where
  toFun g := {
    __ := (ρ g).toAdd.toAddMonoidHom
    map_smul' := fun r v => by
      change (ρ g).toAdd.toAddMonoidHom (r.toZModPow n • v) =
        r.toZModPow n • (ρ g).toAdd.toAddMonoidHom v
      exact ZMod.map_smul (ρ g).toAdd.toAddMonoidHom _ _ }
  map_one' := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun e => e.toAdd v) (map_one ρ)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun e => e.toAdd v) (map_mul ρ g h)

/-- The linear torsion action evaluates to the given additive automorphism. -/
@[simp]
theorem torsionRepresentationOfAddAut_apply (n : ℕ)
    (ρ : G →* Multiplicative (AddAut (Torsion p A n))) (g : G) (v : Torsion p A n) :
    torsionRepresentationOfAddAut p n ρ g v = (ρ g).toAdd v := rfl

end


variable (p : ℕ) [Fact p.Prime] (G A : Type*) [Monoid G] [AddCommGroup A]
  (ρ : ∀ n, Representation ℤ_[p] G (Torsion p A n))
  (hρ : ∀ g n v, transition p A n (ρ (n + 1) g v) = ρ n g (transition p A n v))

/-- Compatible linear actions on the finite torsion levels act on the integral inverse limit. -/
def representationOfTorsion : Representation ℤ_[p] G (integral p A) where
  toFun g := {
    toFun := fun x => ⟨fun n => ρ n g (x.val n), by
      intro n
      rw [hρ, x.property n]⟩
    map_add' := fun x y => by
      apply Subtype.ext
      funext n
      exact map_add (ρ n g) _ _
    map_smul' := fun r x => by
      apply Subtype.ext
      funext n
      exact map_smul (ρ n g) _ _ }
  map_one' := by
    ext x n
    exact congrArg Subtype.val (LinearMap.congr_fun (map_one (ρ n)) (x.val n))
  map_mul' g h := by
    ext x n
    exact congrArg Subtype.val (LinearMap.congr_fun (map_mul (ρ n) g h) (x.val n))

/-- The induced integral action is the prescribed action on every torsion coordinate. -/
@[simp]
theorem representationOfTorsion_projection (g : G) (x : integral p A) (n : ℕ) :
    projection p A n (representationOfTorsion p G A ρ hρ g x) =
      ρ n g (projection p A n x) := rfl

variable [TopologicalSpace A] [TopologicalSpace G]

/-- Joint continuity at every torsion level implies joint continuity on the inverse limit. -/
theorem continuous_representationOfTorsion
    (hcont : ∀ n, Continuous (fun gv : G × Torsion p A n => ρ n gv.1 gv.2)) :
    Continuous (fun gx : G × integral p A =>
      representationOfTorsion p G A ρ hρ gx.1 gx.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (hcont n).comp (continuous_fst.prodMk
    ((continuous_projection p A n).comp continuous_snd))

end TateModule
