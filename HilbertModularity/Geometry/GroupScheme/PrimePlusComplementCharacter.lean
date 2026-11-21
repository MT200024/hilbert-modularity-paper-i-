/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicLocalGalois
public import HilbertModularity.NumberTheory.CyclotomicLocalCharacter
public import HilbertModularity.Hypergeometric.ModularityHypotheses
public import HilbertModularity.Topology.TateModule.FiniteGeneration
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricRanks
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Tactic.LinearCombination

/-! # The quadratic sign of the full/real cyclotomic extension

An automorphism over the real cyclotomic field acts on the chosen primitive
root with exponent `1` or `-1`. The character below extracts that sign from
the finite residual cyclotomic action and maps it into characteristic-zero
coefficient units. This is separate from Darmon–Mestre's geometric isogeny.
-/

public noncomputable section

open HilbertModularity.Cyclotomic
open scoped NumberField

namespace HilbertModularity.Hypergeometric

attribute [local instance] realPrimePowerCompletionPadicAlgebra

private theorem zmod_units_one_ne_neg_one (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) : (1 : (ZMod p)ˣ) ≠ -1 := by
  intro h
  have hv : (1 : ZMod p) = -1 :=
    congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
  have htwo : (2 : ZMod p) = 0 := by linear_combination hv
  have hd : p ∣ 2 := by
    change ((2 : ℕ) : ZMod p) = 0 at htwo
    exact (ZMod.natCast_eq_zero_iff 2 p).mp htwo
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- Extract the sign from a residual cyclotomic character whose image is
the two-element subgroup `{1,-1}`. The image condition is the exact
quadratic full/real field restriction, not an arbitrary finite twist. -/
def residualQuadraticSign (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {G : Type*} [Group G] (ε : G →* (ZMod p)ˣ)
    (hε : ∀ g, ε g = 1 ∨ ε g = -1) : G →* ℤˣ where
  toFun g := if ε g = 1 then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    have hne : (-1 : (ZMod p)ˣ) ≠ 1 :=
      (zmod_units_one_ne_neg_one p hp).symm
    rcases hε g with hg | hg <;> rcases hε h with hh | hh
    · simp [hg, hh]
    · simp [hg, hh, hne]
    · simp [hg, hh, hne]
    · simp [hg, hh, hne]

/-- The extracted integer sign is explicitly `1` or `-1` on each element. -/
theorem residualQuadraticSign_eq_one_or_neg_one
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {G : Type*} [Group G] (ε : G →* (ZMod p)ˣ)
    (hε : ∀ g, ε g = 1 ∨ ε g = -1) (g : G) :
    residualQuadraticSign p hp ε hε g = 1 ∨
      residualQuadraticSign p hp ε hε g = -1 := by
  by_cases h : ε g = 1
  · exact Or.inl (by simp [residualQuadraticSign, h])
  · exact Or.inr (by simp [residualQuadraticSign, h])

/-- The actual local residual cyclotomic action, pulled back from the
canonical-prime residual character of the chosen real cyclotomic field.
Its values are in `ZMod p`, so no independent quadratic character is selected
at the complementary fibre. -/
def primePlusLocalResidualCyclotomicCharacter (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →* (ZMod p)ˣ :=
  (Units.map (realPrimeResidueEquiv p (by omega)).toMonoidHom).comp
    ((AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
      (realCyclotomicField p) p (by omega)).comp
        (primePlusLocalGaloisRestriction p))

/-- Every local residual value is one of the two full/real cyclotomic
conjugation signs. -/
theorem primePlusLocalResidualCyclotomicCharacter_eq_one_or_neg_one
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) :
    primePlusLocalResidualCyclotomicCharacter p hp g = 1 ∨
      primePlusLocalResidualCyclotomicCharacter p hp g = -1 := by
  change Units.map (realPrimeResidueEquiv p (by omega)).toMonoidHom
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega)
        (primePlusLocalGaloisRestriction p g)) = 1 ∨
    Units.map (realPrimeResidueEquiv p (by omega)).toMonoidHom
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega)
        (primePlusLocalGaloisRestriction p g)) = -1
  rcases realPrimeResidualCharacter_eq_one_or_neg_one p (by omega)
      (primePlusLocalGaloisRestriction p g) with h | h
  · left
    simp [h]
  · right
    simp [h]

/-- Reduction of `p`-adic units is continuous into the finite discrete
residue-unit group. -/
private theorem continuous_padicUnitReduction (p : ℕ) [Fact p.Prime] :
    Continuous (Units.map (PadicInt.toZMod (p := p)).toMonoidHom :
      ℤ_[p]ˣ → (ZMod p)ˣ) := by
  let : UniformSpace (ZMod p) := ⊥
  have hred : Continuous (PadicInt.toZMod (p := p) : ℤ_[p] → ZMod p) := by
    have hr : (p : ℝ) ^ (-(1 : ℤ)) ≠ 0 :=
      ne_of_gt (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _)
    apply UniformContinuous.continuous
    apply IsUniformAddGroup.uniformContinuous_iff_isOpen_ker.mpr
    change IsOpen (RingHom.ker (PadicInt.toZMod (p := p) : ℤ_[p] →+* ZMod p) : Set ℤ_[p])
    have hker : RingHom.ker (PadicInt.toZMod (p := p) : ℤ_[p] →+* ZMod p) =
        RingHom.ker (PadicInt.toZModPow (p := p) 1) := by
      rw [PadicInt.ker_toZMod, PadicInt.ker_toZModPow,
        PadicInt.maximalIdeal_eq_span_p]
      simp
    rw [hker, PadicInt.ker_toZModPow]
    convert IsUltrametricDist.isOpen_closedBall (0 : ℤ_[p]) hr using 1
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (p := p) (n := 1) (x := x)).symm
  apply Units.continuous_iff.mpr
  constructor
  · exact hred.comp Units.continuous_val
  · convert hred.comp (Units.continuous_val.comp continuous_inv) using 1
    funext u
    simp

/-- The chosen local quadratic character is the reduction of the native
cyclotomic action; the equality fixes its normalization for the residual
ordering at the real conductor prime. -/
theorem primePlusLocalResidualCyclotomicCharacter_eq_reduction
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0)) :
    primePlusLocalResidualCyclotomicCharacter p hp g =
      Units.map (PadicInt.toZMod (p := p)).toMonoidHom
        (Field.cyclotomicCharacter (realCyclotomicField p) p
          (primePlusLocalGaloisRestriction p g)) := by
  apply Units.ext
  change realPrimeResidueEquiv p (by omega)
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega)
        (primePlusLocalGaloisRestriction p g) :
          𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) =
    PadicInt.toZMod
      ((Field.cyclotomicCharacter (realCyclotomicField p) p
        (primePlusLocalGaloisRestriction p g) : ℤ_[p]))
  exact (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter_residue
    (realCyclotomicField p) p (by omega) (primePlusLocalGaloisRestriction p g))

/-- Continuity follows from the native cyclotomic character, continuous
local restriction, and continuous reduction of `p`-adic units. -/
theorem primePlusLocalResidualCyclotomicCharacter_continuous
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    Continuous (primePlusLocalResidualCyclotomicCharacter p hp) := by
  have hc := (continuous_padicUnitReduction p).comp
    ((Field.cyclotomicCharacter (realCyclotomicField p) p).continuous.comp
      (continuous_primePlusLocalGaloisRestriction p))
  convert hc using 1
  funext g
  exact primePlusLocalResidualCyclotomicCharacter_eq_reduction p hp g

/-- The actual unit-valued local character obtained from the sign of the
full/real cyclotomic extension. Its coefficient field is the native real
completion used by the selected plus Tate factor. -/
def primePlusLocalQuadraticCharacter (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ε : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →* (ZMod p)ˣ)
    (hε : ∀ g, ε g = 1 ∨ ε g = -1) :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ :=
  (Units.map (Int.castRingHom (RealPrimePowerCompletion p 0)).toMonoidHom).comp
    (residualQuadraticSign p hp ε hε)

/-- The local sign has order dividing two, including at the conductor
prime. The proof uses the explicit `{1,-1}` range and no auxiliary-prime
torsion restriction. -/
theorem primePlusLocalQuadraticCharacter_sq (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p)
    (ε : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →* (ZMod p)ˣ)
    (hε : ∀ g, ε g = 1 ∨ ε g = -1) :
    primePlusLocalQuadraticCharacter p hp ε hε ^ 2 = 1 := by
  apply MonoidHom.ext
  intro g
  change (Units.map (Int.castRingHom (RealPrimePowerCompletion p 0)).toMonoidHom
    (residualQuadraticSign p hp ε hε g)) ^ 2 = 1
  rw [← map_pow]
  rcases residualQuadraticSign_eq_one_or_neg_one p hp ε hε g with h | h
  · simp [h]
  · simp [h]

theorem primePlusLocalQuadraticCharacter_isOfFinOrder (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p)
    (ε : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →* (ZMod p)ˣ)
    (hε : ∀ g, ε g = 1 ∨ ε g = -1) :
    IsOfFinOrder (primePlusLocalQuadraticCharacter p hp ε hε) :=
  isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2, by decide, primePlusLocalQuadraticCharacter_sq p hp ε hε⟩

/-- Continuity is inherited from the finite residual cyclotomic action.
The two sign maps have discrete finite sources. -/
theorem primePlusLocalQuadraticCharacter_continuous (p : ℕ) [Fact p.Prime]
    [TopologicalSpace (ZMod p)ˣ] [DiscreteTopology (ZMod p)ˣ]
    (hp : 5 ≤ p)
    (ε : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →* (ZMod p)ˣ)
    (hε : ∀ g, ε g = 1 ∨ ε g = -1)
    (hcontinuous : Continuous ε) :
    Continuous (primePlusLocalQuadraticCharacter p hp ε hε) := by
  have hs : Continuous (fun u : (ZMod p)ˣ =>
      if u = 1 then (1 : ℤˣ) else -1) := continuous_of_discreteTopology
  have hm : Continuous
      (Units.map (Int.castRingHom (RealPrimePowerCompletion p 0)).toMonoidHom) :=
    continuous_of_discreteTopology
  change Continuous ((Units.map
    (Int.castRingHom (RealPrimePowerCompletion p 0)).toMonoidHom) ∘
      (fun u : (ZMod p)ˣ => if u = 1 then (1 : ℤˣ) else -1) ∘ ε)
  exact hm.comp (hs.comp hcontinuous)

/-- The particular quadratic character cut out by the actual full/real
cyclotomic extension at the conductor completion. -/
def primePlusComplementQuadraticCharacter (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) :
    Gal(PadicAlgCl p/RealPrimePowerCompletion p 0) →*
      (RealPrimePowerCompletion p 0)ˣ :=
  primePlusLocalQuadraticCharacter p hp
    (primePlusLocalResidualCyclotomicCharacter p hp)
    (primePlusLocalResidualCyclotomicCharacter_eq_one_or_neg_one p hp)

/-- The actual complementary-cusp character has order dividing two. -/
theorem primePlusComplementQuadraticCharacter_sq (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) : primePlusComplementQuadraticCharacter p hp ^ 2 = 1 :=
  primePlusLocalQuadraticCharacter_sq p hp
    (primePlusLocalResidualCyclotomicCharacter p hp)
    (primePlusLocalResidualCyclotomicCharacter_eq_one_or_neg_one p hp)

theorem primePlusComplementQuadraticCharacter_isOfFinOrder (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p) :
    IsOfFinOrder (primePlusComplementQuadraticCharacter p hp) :=
  primePlusLocalQuadraticCharacter_isOfFinOrder p hp
    (primePlusLocalResidualCyclotomicCharacter p hp)
    (primePlusLocalResidualCyclotomicCharacter_eq_one_or_neg_one p hp)

theorem primePlusComplementQuadraticCharacter_continuous (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p) :
    Continuous (primePlusComplementQuadraticCharacter p hp) :=
  primePlusLocalQuadraticCharacter_continuous p hp
    (primePlusLocalResidualCyclotomicCharacter p hp)
    (primePlusLocalResidualCyclotomicCharacter_eq_one_or_neg_one p hp)
    (primePlusLocalResidualCyclotomicCharacter_continuous p hp)

theorem primePlusComplementQuadraticCharacter_of_residual_one (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (h : primePlusLocalResidualCyclotomicCharacter p hp g = 1) :
    primePlusComplementQuadraticCharacter p hp g = 1 := by
  simp [primePlusComplementQuadraticCharacter, primePlusLocalQuadraticCharacter,
    residualQuadraticSign, h]

theorem primePlusComplementQuadraticCharacter_of_residual_neg_one (p : ℕ)
    [Fact p.Prime] (hp : 5 ≤ p)
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p 0))
    (h : primePlusLocalResidualCyclotomicCharacter p hp g = -1) :
    primePlusComplementQuadraticCharacter p hp g = -1 := by
  have hne : (-1 : (ZMod p)ˣ) ≠ 1 := (zmod_units_one_ne_neg_one p hp).symm
  simp [primePlusComplementQuadraticCharacter, primePlusLocalQuadraticCharacter,
    residualQuadraticSign, h, hne]

end HilbertModularity.Hypergeometric
