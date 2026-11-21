/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination

/-! # Dihedral algebra behind the Darmon–Mestre correspondence

For the covers `D₂(s) → C₂(s)` and `D₂(s) → C₂(-s)`, the transfer and
pushforward maps satisfy `π*π_* = 1 + τ₂` and `α*α_* = 1 - τ₂` on rational
homology. The latter sign is the hyperelliptic involution in
[DarmonMestre, Proposition 2.3, proof, printed pp. 307–308]. The lemmas below
deduce the conjugation sign and commutation with the trace correspondence
from these identities, before choosing a Jacobian or a Tate realization.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric

/-- Algebraic data of the two quotient maps and cyclic rotation on a common
cover. The hypotheses are the pointwise forms of the source's two transfer
identities, its dihedral relation, and the invariant/anti-invariant quotient
maps. `a` satisfies `2a=1` modulo the conductor. -/
structure DarmonMestreDihedralData (p : ℕ)
    (V W U : Type*) [AddCommGroup V] [AddCommGroup W] [AddCommGroup U] where
  a : ZMod p
  double_a : (2 : ZMod p) * a = 1
  rotate : ZMod p → V →+ V
  rotate_add : ∀ b c v, rotate (b + c) v = rotate b (rotate c v)
  tau : V →+ V
  tau_rotate : ∀ b v, tau (rotate b v) = rotate (-b) (tau v)
  piPull : W →+ V
  piPush : V →+ W
  pi_transfer : ∀ v, piPull (piPush v) = v + tau v
  pi_invariant : ∀ w, tau (piPull w) = piPull w
  alphaPull : U →+ V
  alphaPush : V →+ U
  alpha_transfer : ∀ v, alphaPull (alphaPush v) = v - tau v
  alpha_antiInvariant : ∀ v, alphaPush (tau v) = -alphaPush v

namespace DarmonMestreDihedralData

variable {p : ℕ} {V W U : Type*}
  [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
  (D : DarmonMestreDihedralData p V W U)

/-- Darmon–Mestre's correspondence `α_* [ζ^a] π*`. -/
def eta : W →+ U := D.alphaPush.comp ((D.rotate D.a).comp D.piPull)

/-- The source trace correspondence attached to `ζ + ζ⁻¹`. -/
def sourceTrace : W →+ W := D.piPush.comp ((D.rotate 1).comp D.piPull)

/-- The target trace correspondence attached to the same rotation class. -/
def targetTrace : U →+ U := D.alphaPush.comp ((D.rotate 1).comp D.alphaPull)

private theorem one_sub_a : (1 : ZMod p) - D.a = D.a := by
  have h := D.double_a
  linear_combination -h

private theorem a_sub_one : D.a - (1 : ZMod p) = -D.a := by
  have h := D.double_a
  linear_combination h

/-- Conjugation sends `[ζ^a]` to `[ζ⁻ᵃ]`, which negates the correspondence
because `α_* τ₂ = -α_*` and `τ₂ π* = π*`. This is the sign relevant to the
quadratic full/real cyclotomic extension. -/
theorem conjugate_eta_apply (w : W) :
    D.alphaPush (D.rotate (-D.a) (D.piPull w)) = -D.eta w := by
  calc
    D.alphaPush (D.rotate (-D.a) (D.piPull w)) =
        D.alphaPush (D.tau (D.rotate D.a (D.piPull w))) := by
          rw [D.tau_rotate, D.pi_invariant]
    _ = -D.alphaPush (D.rotate D.a (D.piPull w)) :=
      D.alpha_antiInvariant _
    _ = -D.eta w := rfl

/-- The same correspondence intertwines the two trace actions. The only
index arithmetic is `2a=1`: the second term on the source is the negative
of the second term on the target by `conjugate_eta_apply`. -/
theorem eta_intertwines_trace (w : W) :
    D.eta (D.sourceTrace w) = D.targetTrace (D.eta w) := by
  have hleft : D.eta (D.sourceTrace w) =
      D.alphaPush (D.rotate (D.a + 1) (D.piPull w)) +
        D.alphaPush (D.rotate (-D.a) (D.piPull w)) := by
    simp only [eta, sourceTrace, AddMonoidHom.comp_apply, D.pi_transfer,
      map_add, D.tau_rotate, D.pi_invariant, ← D.rotate_add]
    have ha : D.a + (-1 : ZMod p) = -D.a := by
      simpa only [sub_eq_add_neg] using D.a_sub_one
    rw [ha]
  have hright : D.targetTrace (D.eta w) =
      D.alphaPush (D.rotate (D.a + 1) (D.piPull w)) -
        D.alphaPush (D.rotate D.a (D.piPull w)) := by
    simp only [eta, targetTrace, AddMonoidHom.comp_apply, D.alpha_transfer,
      map_sub, D.tau_rotate, D.pi_invariant, ← D.rotate_add]
    have ha : (1 : ZMod p) + -D.a = D.a := by
      simpa only [sub_eq_add_neg] using D.one_sub_a
    rw [ha, add_comm (1 : ZMod p) D.a]
  rw [hleft, hright, D.conjugate_eta_apply]
  simp only [eta, AddMonoidHom.comp_apply, sub_eq_add_neg]

/-- The source correspondence is equivariant or anti-equivariant according
to the action on the primitive `p`-th root. The hypotheses say precisely
that `π₂` and `α` are defined over the real field and that Galois conjugates
rotation by `ζ^b` to rotation by `ζ^(ε(g)b)`. This is the arithmetic content
of [DarmonMestre, Proposition 2.3, proof, printed pp. 307--308]. -/
theorem eta_galois_sign {G : Type*} [Group G]
    (ε : G →* (ZMod p)ˣ) (g : G)
    (actV : G → V →+ V) (actW : G → W →+ W)
    (actU : G → U →+ U)
    (hπ : ∀ w, D.piPull (actW g w) = actV g (D.piPull w))
    (hα : ∀ v, D.alphaPush (actV g v) = actU g (D.alphaPush v))
    (hrotate : ∀ b v,
      D.rotate b (actV g v) =
        actV g (D.rotate ((ε g : ZMod p) * b) v))
    (w : W) :
    (ε g = 1 → D.eta (actW g w) = actU g (D.eta w)) ∧
    (ε g = -1 → D.eta (actW g w) = -actU g (D.eta w)) := by
  constructor
  · intro hε
    simp only [eta, AddMonoidHom.comp_apply, hπ, hrotate, hε,
      Units.val_one, one_mul, hα]
  · intro hε
    simp only [eta, AddMonoidHom.comp_apply, hπ, hrotate, hε,
      Units.val_neg, Units.val_one, neg_mul, one_mul, hα]
    exact congrArg (actU g) (D.conjugate_eta_apply w) |>.trans (map_neg (actU g) _)

end DarmonMestreDihedralData

end HilbertModularity.Hypergeometric
