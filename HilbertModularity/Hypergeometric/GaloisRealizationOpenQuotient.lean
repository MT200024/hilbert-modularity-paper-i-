/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationInvolution

/-! # Orbits of the Euler real-descent involution

The point-level orbit quotient of the branch-open exponent-`m` Euler curve
is defined over any field containing the parameter.  It precedes the choice
of an ℓ-adic coefficient place.  The smooth proper scheme quotient and its
cohomology, used in [GPRV, Theorem 9.2 and Proposition 9.5], require separate
geometric construction.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric.EulerCover

variable {F : Type*} [Field F]

/-- Two branch-open points have the same reflection orbit. -/
def openEulerReflectionSetoid (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) : Setoid (OpenEulerPoint N m t) where
  r p q := q = p ∨ q = reflectOpenEulerPoint N m hm ht p
  iseqv := by
    constructor
    · intro p
      exact Or.inl rfl
    · intro p q hpq
      rcases hpq with h | h
      · exact Or.inl h.symm
      · right
        rw [h, reflectOpenEulerPoint_involutive]
    · intro p q r hpq hqr
      rcases hpq with h | h
      · subst q
        exact hqr
      · rcases hqr with h' | h'
        · right
          rw [h']
          exact h
        · left
          rw [h', h, reflectOpenEulerPoint_involutive]

/-- The orbit space of branch-open field-valued Euler points.  This type is
the point-level quotient, without a claim that it represents a scheme. -/
def OpenEulerReflectionQuotient (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) :=
  Quotient (openEulerReflectionSetoid N m hm ht)

/-- The canonical map from a branch-open point to its reflection orbit. -/
def openEulerReflectionQuotientMk (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) (p : OpenEulerPoint N m t) :
    OpenEulerReflectionQuotient N m hm ht :=
  Quotient.mk (openEulerReflectionSetoid N m hm ht) p

/-- Prove a property of orbits by checking it on branch-open points. -/
theorem OpenEulerReflectionQuotient.inductionOn (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0)
    {motive : OpenEulerReflectionQuotient N m hm ht → Prop}
    (q : OpenEulerReflectionQuotient N m hm ht)
    (h : ∀ p, motive (openEulerReflectionQuotientMk N m hm ht p)) : motive q := by
  unfold OpenEulerReflectionQuotient at q
  induction q using Quotient.inductionOn with
  | _ p => exact h p

/-- A point and its reflection give the same orbit. -/
theorem openEulerReflectionQuotientMk_reflect (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) (p : OpenEulerPoint N m t) :
    openEulerReflectionQuotientMk N m hm ht
        (reflectOpenEulerPoint N m hm ht p) =
      openEulerReflectionQuotientMk N m hm ht p := by
  apply Quotient.sound
  exact Or.inr (reflectOpenEulerPoint_involutive N m hm ht p).symm

/-- A reflection-invariant function factors through the orbit quotient. -/
def openEulerReflectionQuotientLift (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) {A : Type*}
    (f : OpenEulerPoint N m t → A)
    (hf : ∀ p, f (reflectOpenEulerPoint N m hm ht p) = f p) :
    OpenEulerReflectionQuotient N m hm ht → A :=
  Quotient.lift f (by
    intro p q hpq
    rcases hpq with h | h
    · rw [h]
    · rw [h, hf])

theorem openEulerReflectionQuotientLift_mk (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) {A : Type*}
    (f : OpenEulerPoint N m t → A)
    (hf : ∀ p, f (reflectOpenEulerPoint N m hm ht p) = f p)
    (p : OpenEulerPoint N m t) :
    openEulerReflectionQuotientLift N m hm ht f hf
        (openEulerReflectionQuotientMk N m hm ht p) = f p :=
  (rfl)

/-- The symmetric base coordinate is invariant under reflection. -/
def reflectionInvariantX (t x : F) : F := x + reflectionX t x

/-- The rational formula for the first reflection invariant. -/
theorem reflectionInvariantX_eq (t x : F) :
    reflectionInvariantX t x = x + (t * x)⁻¹ := by
  unfold reflectionInvariantX
  rw [reflectionX_eq]

theorem reflectionInvariantX_reflect {t x : F}
    (ht : t ≠ 0) (hx : x ≠ 0) :
    reflectionInvariantX t (reflectionX t x) = reflectionInvariantX t x := by
  simp only [reflectionInvariantX, reflectionX_reflectionX ht hx]
  exact add_comm _ _

/-- The symmetric covering coordinate is invariant under reflection on the
branch-open chart. -/
def reflectionInvariantY (t x y : F) : F := y + reflectionY t x y

/-- The rational formula for the second reflection invariant. -/
theorem reflectionInvariantY_eq (t x y : F) :
    reflectionInvariantY t x y =
      y - (1 - x) * (1 - t * x) / (t * x * y) := by
  unfold reflectionInvariantY
  rw [reflectionY_eq]
  ring

/-- The first invariant coordinate is defined over the field of parameters. -/
theorem map_reflectionInvariantX {E : Type*} [Field E]
    (φ : F →+* E) (t x : F) :
    φ (reflectionInvariantX t x) =
      reflectionInvariantX (φ t) (φ x) := by
  simp [reflectionInvariantX]

/-- The second invariant coordinate is defined over the field of parameters. -/
theorem map_reflectionInvariantY {E : Type*} [Field E]
    (φ : F →+* E) (t x y : F) :
    φ (reflectionInvariantY t x y) =
      reflectionInvariantY (φ t) (φ x) (φ y) := by
  simp [reflectionInvariantY]

theorem reflectionInvariantY_reflect {t x y : F}
    (ht : t ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h1x : 1 - x ≠ 0) (h1tx : 1 - t * x ≠ 0) :
    reflectionInvariantY t (reflectionX t x) (reflectionY t x y) =
      reflectionInvariantY t x y := by
  simp only [reflectionInvariantY,
    reflectionY_reflectionY ht hx hy h1x h1tx]
  exact add_comm _ _

/-- Two explicit invariant rational coordinates on the branch-open curve. -/
def openEulerReflectionCoordinates {N m : ℕ} {t : F}
    (p : OpenEulerPoint N m t) : F × F :=
  (reflectionInvariantX t p.x, reflectionInvariantY t p.x p.y)

@[simp] theorem openEulerReflectionCoordinates_fst {N m : ℕ} {t : F}
    (p : OpenEulerPoint N m t) :
    (openEulerReflectionCoordinates p).1 = reflectionInvariantX t p.x :=
  (rfl)

@[simp] theorem openEulerReflectionCoordinates_snd {N m : ℕ} {t : F}
    (p : OpenEulerPoint N m t) :
    (openEulerReflectionCoordinates p).2 = reflectionInvariantY t p.x p.y :=
  (rfl)

theorem openEulerReflectionCoordinates_reflect (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) (p : OpenEulerPoint N m t) :
    openEulerReflectionCoordinates (reflectOpenEulerPoint N m hm ht p) =
      openEulerReflectionCoordinates p := by
  apply Prod.ext
  · simpa only [openEulerReflectionCoordinates, reflectOpenEulerPoint_x,
      Prod.fst] using reflectionInvariantX_reflect ht p.x_ne_zero
  · simpa only [openEulerReflectionCoordinates, reflectOpenEulerPoint_x,
      reflectOpenEulerPoint_y, Prod.snd] using
      reflectionInvariantY_reflect ht p.x_ne_zero p.y_ne_zero
        p.one_sub_x_ne_zero p.one_sub_tx_ne_zero

/-- The invariant coordinates factor through the point-level orbit quotient. -/
def openEulerReflectionQuotientCoordinates (N m : ℕ) (hm : m ≤ N)
    {t : F} (ht : t ≠ 0) :
    OpenEulerReflectionQuotient N m hm ht → F × F :=
  openEulerReflectionQuotientLift N m hm ht
    openEulerReflectionCoordinates
    (openEulerReflectionCoordinates_reflect N m hm ht)

@[simp] theorem openEulerReflectionQuotientCoordinates_mk
    (N m : ℕ) (hm : m ≤ N) {t : F} (ht : t ≠ 0)
    (p : OpenEulerPoint N m t) :
    openEulerReflectionQuotientCoordinates N m hm ht
        (openEulerReflectionQuotientMk N m hm ht p) =
      openEulerReflectionCoordinates p := by
  unfold openEulerReflectionQuotientCoordinates
  exact openEulerReflectionQuotientLift_mk N m hm ht
    openEulerReflectionCoordinates
    (openEulerReflectionCoordinates_reflect N m hm ht) p

end HilbertModularity.Hypergeometric.EulerCover
