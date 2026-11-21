/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.CoprimeEulerGenericMonodromy
public import HilbertModularity.Hypergeometric.EffectiveEulerRealization
public import HilbertModularity.Hypergeometric.RMComparison

/-! # Generic monodromy of the effective Euler family

The one GPRV κ character is pulled back from the base-field Galois
group to the punctured-line arithmetic fundamental group. It is
therefore trivial on the geometric kernel, so the selected raw Euler
quotient and its effective normalization have identical geometric
local classes and irreducibility. The raw classes are the cited
GPRV input [GPRV, Proposition 3.12 and Theorem 8.20].
-/

public noncomputable section

open AlgebraicGeometry
open HilbertModularity.Cyclotomic

namespace HilbertModularity.Hypergeometric

/-- The arithmetic monodromy of the same chosen Euler quotient, with
the base-field κ_N^m character pulled back along the actual arithmetic
projection. Specialization at any rational fibre uses this one action. -/
def chosenEffectiveEulerMonodromy
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    let D := R.placeDescent N m 𝒞 p L ι
    Representation L
      (Scheme.etaleFundamentalGroup (realCyclotomicField N)
        (ProjectiveLine.puncturedPoint (realCyclotomicField N) ξ))
      (D.localSystem.toFunctor.obj
        (Scheme.etaleFiberPoint _ _ (ProjectiveLine.puncturedPoint _ ξ))) :=
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  (puncturedFiberMonodromy (realCyclotomicField N) ξ
    D.localSystem).characterTwist
      ((gprvKappaLocal N h3 m L).comp
        (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ))

/-- Restricting this one arithmetic monodromy action along the
section at a rational parameter gives the previously defined
effective arithmetic fibre, with the same κ value. -/
theorem chosenEffectiveEulerMonodromy_arithmetic_eq
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    (chosenEffectiveEulerMonodromy N m p h3 hm hmN hcop L ι ξ).comp
        (Scheme.galoisToEtaleFundamentalGroup
          (realCyclotomicField N) (ProjectiveLine.puncturedPoint _ ξ)) =
      chosenEffectiveEulerAction N m p h3 hm hmN hcop L ι ξ := by
  ext g v
  rw [chosenEffectiveEulerAction_apply]
  change (gprvKappaLocal N h3 m L
      (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ
        (Scheme.galoisToEtaleFundamentalGroup
          (realCyclotomicField N) (ProjectiveLine.puncturedPoint _ ξ) g)) : L) •
    (puncturedFiberMonodromy (realCyclotomicField N) ξ
      ((chosenCoprimeRawEulerRealization N m h3 hm hmN hcop).placeDescent
        N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop) p L ι).localSystem)
      (Scheme.galoisToEtaleFundamentalGroup
        (realCyclotomicField N) (ProjectiveLine.puncturedPoint _ ξ) g) v =
    (gprvKappaLocal N h3 m L g : L) •
      ((chosenCoprimeRawEulerRealization N m h3 hm hmN hcop).placeDescent
        N m (chosenCoprimeEulerFamily N m h3 hm hmN hcop) p L ι).localSystem.arithmeticRepresentation
          (ProjectiveLine.puncturedPoint _ ξ) g v
  rw [show puncturedArithmeticProjectionHom (realCyclotomicField N) ξ
      (Scheme.galoisToEtaleFundamentalGroup
        (realCyclotomicField N) (ProjectiveLine.puncturedPoint _ ξ) g) = g from
    puncturedArithmeticProjection_galois (realCyclotomicField N) ξ g]
  rfl

/-- The effective and raw selected quotient have exactly the same
action on the geometric kernel of the arithmetic projection.
This is a proved consequence of the actual base-field character,
not an extra geometric-monodromy premise. -/
theorem chosenEffectiveEulerMonodromy_geometric_eq_raw
    (N m p : ℕ) [NeZero N] [Fact p.Prime]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N) (hcop : m.Coprime N)
    (L : Type) [NontriviallyNormedField L] [CompleteSpace L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [Algebra ℚ L]
    (ι : cyclotomicField N →+* L)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField N)) :
    let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
    let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
    let D := R.placeDescent N m 𝒞 p L ι
    let k := (puncturedArithmeticProjectionHom (realCyclotomicField N) ξ).ker.subtype
    (chosenEffectiveEulerMonodromy N m p h3 hm hmN hcop L ι ξ).comp k =
      (puncturedFiberMonodromy (realCyclotomicField N) ξ D.localSystem).comp k := by
  let 𝒞 := chosenCoprimeEulerFamily N m h3 hm hmN hcop
  let R := chosenCoprimeRawEulerRealization N m h3 hm hmN hcop
  let D := R.placeDescent N m 𝒞 p L ι
  let β := puncturedArithmeticProjectionHom (realCyclotomicField N) ξ
  let k := β.ker.subtype
  ext g v
  have hg : β (k g) = 1 := g.property
  change (gprvKappaLocal N h3 m L (β (k g)) : L) •
    (puncturedFiberMonodromy (realCyclotomicField N) ξ D.localSystem)
      (k g) v =
    (puncturedFiberMonodromy (realCyclotomicField N) ξ D.localSystem)
      (k g) v
  rw [hg]
  simp

end HilbertModularity.Hypergeometric
