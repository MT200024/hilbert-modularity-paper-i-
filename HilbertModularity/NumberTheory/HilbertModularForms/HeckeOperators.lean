/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.AdelicGroups

/-! # Finite double-coset Hecke operators

We use actual right-coset representatives of `K a K`, not a freely chosen
linear operator. This is the adelic Hecke action used for Hilbert eigenforms;
its character-twist calculation is the elementary input to the finite-twist
correspondence of [SkinnerWiles, §4.5].
-/

public noncomputable section

namespace HilbertModularity.HilbertModularForms

variable {G : Type*} [Group G]

/-- The double coset of `a` under a subgroup `K`. -/
def doubleCoset (K : Subgroup G) (a : G) : Set G :=
  {x | ∃ k l : G, k ∈ K ∧ l ∈ K ∧ x = k * a * l}

/-- A finite decomposition of `K a K` into distinct right `K`-cosets.
The representatives are mathematical data with coverage and disjointness
certificates, as in the standard double-coset definition of a Hecke operator. -/
structure DoubleCosetRepresentatives (K : Subgroup G) (a : G) where
  reps : Finset G
  mem_doubleCoset : ∀ r ∈ reps, r ∈ doubleCoset K a
  cover : ∀ x ∈ doubleCoset K a, ∃ r ∈ reps, ∃ k ∈ K, x = r * k
  distinct : ∀ r ∈ reps, ∀ s ∈ reps,
    (∃ k ∈ K, r = s * k) → r = s

/-- The finite double-coset Hecke action on a complex function. -/
def heckeAction {K : Subgroup G} {a : G}
    (d : DoubleCosetRepresentatives K a) (φ : G → ℂ) : G → ℂ :=
  fun g => ∑ r ∈ d.reps, φ (g * r)

/-- Twist a function by an actual group character. -/
def twistByCharacter (χ : G →* ℂˣ) (φ : G → ℂ) : G → ℂ :=
  fun g => (χ g : ℂ) * φ g

@[simp]
theorem twistByCharacter_apply (χ : G →* ℂˣ) (φ : G → ℂ) (g : G) :
    twistByCharacter χ φ g = (χ g : ℂ) * φ g := (rfl)

/-- A character trivial on `K` has its value at every representative of
`K a K` equal to its value at `a`. -/
theorem character_on_doubleCoset (K : Subgroup G) (a : G)
    (χ : G →* ℂˣ) (hχ : ∀ k ∈ K, χ k = 1)
    {r : G} (hr : r ∈ doubleCoset K a) : χ r = χ a := by
  rcases hr with ⟨k, l, hk, hl, rfl⟩
  simp [hχ k hk, hχ l hl]

/-- Twisting a function commutes with the actual Hecke sum, multiplying its
value at `a` by the character value there. -/
theorem heckeAction_twist {K : Subgroup G} {a : G}
    (d : DoubleCosetRepresentatives K a)
    (χ : G →* ℂˣ) (hχ : ∀ k ∈ K, χ k = 1)
    (φ : G → ℂ) (g : G) :
    heckeAction d (twistByCharacter χ φ) g =
      (χ g : ℂ) * (χ a : ℂ) * heckeAction d φ g := by
  simp only [heckeAction, twistByCharacter]
  calc
    ∑ r ∈ d.reps, (χ (g * r) : ℂ) * φ (g * r) =
        ∑ r ∈ d.reps, ((χ g : ℂ) * (χ a : ℂ)) * φ (g * r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [map_mul, character_on_doubleCoset K a χ hχ (d.mem_doubleCoset r hr)]
          simp only [Units.val_mul]
    _ = (χ g : ℂ) * (χ a : ℂ) * ∑ r ∈ d.reps, φ (g * r) := by
      rw [Finset.mul_sum]

/-- A right-`K`-invariant eigenfunction for one double coset. -/
structure HeckeEigencondition (K : Subgroup G) (a : G)
    (d : DoubleCosetRepresentatives K a) (φ : G → ℂ) where
  eigenvalue : ℂ
  eigen : ∀ g, heckeAction d φ g = eigenvalue * φ g

/-- Twisting multiplies a double-coset eigenvalue by the character of `a`. -/
def HeckeEigencondition.twist {K : Subgroup G} {a : G}
    {d : DoubleCosetRepresentatives K a} {φ : G → ℂ}
    (h : HeckeEigencondition K a d φ)
    (χ : G →* ℂˣ) (hχ : ∀ k ∈ K, χ k = 1) :
    HeckeEigencondition K a d (twistByCharacter χ φ) where
  eigenvalue := (χ a : ℂ) * h.eigenvalue
  eigen g := by
    rw [heckeAction_twist d χ hχ φ g, h.eigen g]
    simp only [twistByCharacter]
    ring

end HilbertModularity.HilbertModularForms
