/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.DeterminantCharacter
public import HilbertModularity.Hypergeometric.FamilyComparison
import HilbertModularity.NumberTheory.FiniteCharacterPeriods
public import Mathlib.Tactic.Group

/-! # Determinant bound for a rank-two comparison character

The fourth-power calculation isolates the determinant step in the prime-level
route to finite order. The required determinant and purity identities are
explicit hypotheses; they must be established for the actual two families.
-/

public section

namespace HilbertModularity.Hypergeometric

/-- If two representations agree on the geometric kernel of a split quotient,
the finite-exponent bound for their normalized determinant ratio need only be
checked at the section. This is the one-fibre reduction used in
[TripathiGoswamiRevised, Theorem RMgeneral, step 5]. -/
theorem determinant_power_eq_one_of_section
    {G Γ L V W : Type*} [Group G] [Group Γ] [Field L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (π : G →* Γ) (s : Γ →* G) (hs : ∀ γ, π (s γ) = γ)
    (ρRM : Representation L G V) (ρEff : Representation L G W)
    (eGeom : Representation.Equiv (ρRM.comp π.ker.subtype) (ρEff.comp π.ker.subtype))
    (ε : G →* Lˣ) (hRM : ∀ g, ρRM.determinantCharacter g * ε g = 1)
    (n : ℕ)
    (hsection : ∀ γ, (ρEff.determinantCharacter (s γ) * ε (s γ)) ^ n = 1) :
    ∀ g, (ρEff.determinantCharacter g * ε g) ^ n = 1 := by
  let δ : G →* Lˣ := ρEff.determinantCharacter * ε
  have hker : ∀ k : π.ker, δ k = 1 := by
    intro k
    have he : ρRM.determinantCharacter k = ρEff.determinantCharacter k := by
      apply Units.ext
      exact eGeom.determinant_eq k
    change ρEff.determinantCharacter k * ε k = 1
    rw [← he]
    exact hRM k
  intro g
  have hk : g * (s (π g))⁻¹ ∈ π.ker := by
    change π (g * (s (π g))⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]
  have hδ := hker ⟨g * (s (π g))⁻¹, hk⟩
  change δ (g * (s (π g))⁻¹) = 1 at hδ
  rw [map_mul, map_inv, mul_inv_eq_one] at hδ
  change (δ g) ^ n = 1
  rw [hδ]
  exact hsection (π g)

/-- If the effective determinant times the cyclotomic character is quadratic,
the covariant RM determinant is cyclotomic, and the rank-two comparison has
the expected determinant relation with the *dual* RM representation, then the
comparison character has exponent dividing four. -/
theorem comparisonCharacter_fourth_power_eq_one
    {G L : Type*} [Group G] [Field L]
    (δeff δcov ε ν : G →* Lˣ)
    (hpurity : ∀ g, (δeff g * ε g) ^ 2 = 1)
    (hcov : δcov = ε)
    (hdual : ∀ g, δeff g = (ν g) ^ 2 * (δcov g)⁻¹) :
    ∀ g, (ν g) ^ 4 = 1 := by
  intro g
  have hdet : δeff g * ε g = (ν g) ^ 2 := by
    rw [hdual g, hcov]
    group
  calc
    (ν g) ^ 4 = ((ν g) ^ 2) ^ 2 := by group
    _ = (δeff g * ε g) ^ 2 := by rw [hdet]
    _ = 1 := hpurity g

/-- A fourth-power determinant bound gives finite image of the comparison
character over any coefficient field. The arithmetic determinant identities
needed to obtain the bound remain separate inputs. -/
theorem comparisonCharacter_finite_range_of_fourth_power
    {G L : Type*} [Group G] [Field L] (ν : G →* Lˣ)
    (hfourth : ∀ g, (ν g) ^ 4 = 1) : (Set.range ν).Finite := by
  exact MonoidHom.finite_range_of_pow_eq_one ν (by decide) hfourth

/-- The determinant relation for a comparison of two actual rank-two
representations follows from their intertwiner. When the cohomological RM
determinant is inverse cyclotomic and the effective determinant has the
specified quadratic purity bound, the *same* comparison character has finite
image. These two arithmetic determinant inputs are explicit. -/
theorem comparisonCharacter_finite_range_of_tensor_equiv
    {G L V W : Type*} [Group G] [Field L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρRM : Representation L G V) (ρEff : Representation L G W)
    (ν ε : G →* Lˣ)
    (e : ((Representation.ofCharacter ν).tprod ρRM).Equiv ρEff)
    (hdim : Module.finrank L V = 2)
    (hRM : ∀ g, ρRM.determinantCharacter g * ε g = 1)
    (hpurity : ∀ g, (ρEff.determinantCharacter g * ε g) ^ 2 = 1) :
    (Set.range ν).Finite := by
  let e' := (Representation.characterTwistTensorEquiv ρRM ν).symm.trans e
  apply comparisonCharacter_finite_range_of_fourth_power ν
  intro g
  have he := e'.determinant_eq g
  change LinearMap.det ((ν g : L) • ρRM g) = LinearMap.det (ρEff g) at he
  rw [LinearMap.det_smul, hdim] at he
  have hdet : ρEff.determinantCharacter g =
      (ν g) ^ 2 * ρRM.determinantCharacter g := by
    apply Units.ext
    change LinearMap.det (ρEff g) =
      (ν g : L) ^ 2 * LinearMap.det (ρRM g)
    exact he.symm
  have hcombine : ρEff.determinantCharacter g * ε g = (ν g) ^ 2 := by
    rw [hdet, mul_assoc, hRM g, mul_one]
  calc
    (ν g) ^ 4 = ((ν g) ^ 2) ^ 2 := by group
    _ = (ρEff.determinantCharacter g * ε g) ^ 2 := by rw [hcombine]
    _ = 1 := hpurity g

/-- The same rank-two determinant calculation works with any fixed positive
exponent for the normalized effective determinant. This is the form needed if
purity supplies a finite-order determinant of order other than two. The bound
on the actual effective family remains an explicit arithmetic premise. -/
theorem comparisonCharacter_finite_range_of_tensor_equiv_and_power
    {G L V W : Type*} [Group G] [Field L]
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (ρRM : Representation L G V) (ρEff : Representation L G W)
    (ν ε : G →* Lˣ)
    (e : ((Representation.ofCharacter ν).tprod ρRM).Equiv ρEff)
    (hdim : Module.finrank L V = 2)
    (hRM : ∀ g, ρRM.determinantCharacter g * ε g = 1)
    (n : ℕ) (hn : 0 < n)
    (hpurity : ∀ g, (ρEff.determinantCharacter g * ε g) ^ n = 1) :
    (Set.range ν).Finite := by
  let e' := (Representation.characterTwistTensorEquiv ρRM ν).symm.trans e
  apply MonoidHom.finite_range_of_pow_eq_one (n := 2 * n) ν
    (Nat.ne_of_gt (Nat.mul_pos (by decide : 0 < (2 : ℕ)) hn))
  intro g
  have he := e'.determinant_eq g
  change LinearMap.det ((ν g : L) • ρRM g) = LinearMap.det (ρEff g) at he
  rw [LinearMap.det_smul, hdim] at he
  have hdet : ρEff.determinantCharacter g =
      (ν g) ^ 2 * ρRM.determinantCharacter g := by
    apply Units.ext
    change LinearMap.det (ρEff g) =
      (ν g : L) ^ 2 * LinearMap.det (ρRM g)
    exact he.symm
  have hcombine : ρEff.determinantCharacter g * ε g = (ν g) ^ 2 := by
    rw [hdet, mul_assoc, hRM g, mul_one]
  calc
    (ν g) ^ (2 * n) = ((ν g) ^ 2) ^ n := pow_mul (ν g) 2 n
    _ = (ρEff.determinantCharacter g * ε g) ^ n := by rw [hcombine]
    _ = 1 := hpurity g

end HilbertModularity.Hypergeometric
