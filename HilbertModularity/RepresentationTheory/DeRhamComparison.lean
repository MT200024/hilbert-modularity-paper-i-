/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.PadicDeRham
public import HilbertModularity.RepresentationTheory.HodgeTateComparison
public import HilbertModularity.RepresentationTheory.FiniteCharacterTwist

/-! # De Rham admissibility on the actual period ring

The invariant tensor is built on `BDeRham (PadicComplexInt p) p`.
Admissibility is a dimension condition on that tensor, independent of the
Hodge--Tate comparison. The literature selects its Galois structure and the
standard comparison together, before any representation is chosen.
-/

public noncomputable section

open scoped TensorProduct

namespace DeRham

variable (p : ℕ) [Fact p.Prime]

/-- Functorial Galois actions through the integral, tilt, and Witt stages
of Fontaine's construction, pinned by their coordinate formulas. -/
structure WittGaloisStructure where
  integerAction : Gal(PadicAlgCl p/ℚ_[p]) →* RingAut (PadicComplexInt p)
  integerAction_coe : ∀ g x,
    (integerAction g x : ℂ_[p]) = PadicComplex.galoisEquiv p g x
  tiltAction : Gal(PadicAlgCl p/ℚ_[p]) →* RingAut (PadicComplex.fontaineTilt p)
  tiltAction_coeff : ∀ g x n (z : PadicComplexInt p),
    Ideal.Quotient.mk (Ideal.span {(p : PadicComplexInt p)}) z = PreTilt.coeff n x →
      PreTilt.coeff n (tiltAction g x) =
        Ideal.Quotient.mk (Ideal.span {(p : PadicComplexInt p)}) (integerAction g z)
  wittAction : Gal(PadicAlgCl p/ℚ_[p]) →* RingAut (PadicComplex.fontaineWitt p)
  wittAction_coeff : ∀ g x n, (wittAction g x).coeff n = tiltAction g (x.coeff n)
  localizedWittAction : Gal(PadicAlgCl p/ℚ_[p]) →*
    RingAut (PadicComplex.fontaineWittInvertP p)
  localizedWittAction_algebraMap : ∀ g x,
    localizedWittAction g (algebraMap (PadicComplex.fontaineWitt p)
      (PadicComplex.fontaineWittInvertP p) x) =
        algebraMap (PadicComplex.fontaineWitt p) (PadicComplex.fontaineWittInvertP p)
          (wittAction g x)

/-- Coordinate characterization of the canonical action on the completion. -/
def PositiveActionCompatible (W : WittGaloisStructure p)
    (A : Gal(PadicAlgCl p/ℚ_[p]) → PadicComplex.deRhamPlus p → PadicComplex.deRhamPlus p) : Prop :=
  ∀ g n b (z : PadicComplex.fontaineWittInvertP p),
    PadicComplex.deRhamCoefficient p n b =
      PadicComplex.deRhamCoefficient p n (PadicComplex.wittToDeRhamPlus p z) →
    PadicComplex.deRhamCoefficient p n (A g b) =
      PadicComplex.deRhamCoefficient p n
        (PadicComplex.wittToDeRhamPlus p (W.localizedWittAction g z))

/-- The residue map is the canonical extension of the rational Fontaine map. -/
def ThetaCompatible (θ : PadicComplex.deRhamPlus p → ℂ_[p]) : Prop :=
  ∀ b (z : PadicComplex.fontaineWittInvertP p),
    PadicComplex.deRhamCoefficient p 1 b =
      PadicComplex.deRhamCoefficient p 1 (PadicComplex.wittToDeRhamPlus p z) →
      θ b = PadicComplex.fontaineToComplex p z

/-- Algebraic constants lift their specified residues in the actual `Cp`. -/
def AlgebraicLiftCompatible (θ : PadicComplex.deRhamPlus p → ℂ_[p])
    (e : PadicAlgCl p → PadicComplex.deRhamPlus p) : Prop :=
  ∀ x, θ (e x) = algebraMap (PadicAlgCl p) ℂ_[p] x

/-- The coordinatewise action on the Fontaine completion and the residue
characterization of its algebraic constants. -/
abbrev PositivePeriodStructure :=
  WittGaloisStructure p ×
    (Gal(PadicAlgCl p/ℚ_[p]) → PadicComplex.deRhamPlus p → PadicComplex.deRhamPlus p) ×
    (PadicComplex.deRhamPlus p → ℂ_[p]) ×
    (PadicAlgCl p → PadicComplex.deRhamPlus p)

namespace PositivePeriodStructure
variable {p}

def witt (D : PositivePeriodStructure p) : WittGaloisStructure p := D.1

def plusAction (D : PositivePeriodStructure p) :
    Gal(PadicAlgCl p/ℚ_[p]) → PadicComplex.deRhamPlus p → PadicComplex.deRhamPlus p := D.2.1

def theta (D : PositivePeriodStructure p) : PadicComplex.deRhamPlus p → ℂ_[p] := D.2.2.1

def algebraicEmbeddingPlus (D : PositivePeriodStructure p) :
    PadicAlgCl p → PadicComplex.deRhamPlus p := D.2.2.2

end PositivePeriodStructure

/-- The positive period maps agree with the actual defining completion
coordinates and algebraic residues. -/
def PositivePeriodStructure.IsCanonical (D : PositivePeriodStructure p) : Prop :=
  PositiveActionCompatible p D.witt D.plusAction ∧
    ThetaCompatible p D.theta ∧ AlgebraicLiftCompatible p D.theta D.algebraicEmbeddingPlus

/-- The rational p-adic coefficient and Galois structure on the actual
localized period ring, compatible with its positive construction. -/
structure PeriodStructure where
  coefficients : Algebra ℚ_[p] (PadicComplex.deRhamRing p)
  isField : IsField (PadicComplex.deRhamRing p)
  action : letI := coefficients
    Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) (PadicComplex.deRhamRing p)
  algebraicEmbedding : letI := coefficients
    PadicAlgCl p →ₐ[ℚ_[p]] PadicComplex.deRhamRing p
  action_one : letI := coefficients
    ∀ g, action g 1 = 1
  action_mul : letI := coefficients
    ∀ g x y, action g (x * y) = action g x * action g y
  algebraic_equivariant : letI := coefficients
    ∀ g x, action g (algebraicEmbedding x) = algebraicEmbedding (g x)
  positive : PositivePeriodStructure p
  positive_canonical : PositivePeriodStructure.IsCanonical p positive
  action_algebraMap : letI := coefficients
    ∀ g b, action g (PadicComplex.plusToDeRhamRing p b) =
      PadicComplex.plusToDeRhamRing p (positive.plusAction g b)
  rational_fixedField : letI := coefficients
    ∀ b, (∀ g, action g b = b) ↔ ∃ q : ℚ_[p], algebraMap ℚ_[p] _ q = b
  algebraicEmbeddingPlus_map : letI := coefficients
    ∀ x, PadicComplex.plusToDeRhamRing p
      (positive.algebraicEmbeddingPlus x) = algebraicEmbedding x


variable {p}

/-- The actual diagonal action on the de Rham period tensor, restricted to
the local Galois group through its given algebraic embedding. -/
def PeriodStructure.periodRepresentation (D : PeriodStructure p)
    {G V : Type} [Group G] [AddCommGroup V] [Module ℚ_[p] V]
    (ι : G →* Gal(PadicAlgCl p/ℚ_[p])) (ρ : Representation ℚ_[p] G V) :
    letI := D.coefficients
    Representation ℚ_[p] G (PadicComplex.deRhamRing p ⊗[ℚ_[p]] V) := by
  letI := D.coefficients
  exact Representation.tprod (D.action.comp ι) ρ

/-- The fixed vectors in the actual de Rham period tensor, as a rational
p-adic subspace. -/
def PeriodStructure.invariantSpace (D : PeriodStructure p)
    {G V : Type} [Group G] [AddCommGroup V] [Module ℚ_[p] V]
    (ι : G →* Gal(PadicAlgCl p/ℚ_[p])) (ρ : Representation ℚ_[p] G V) :
    letI := D.coefficients
    Submodule ℚ_[p] (PadicComplex.deRhamRing p ⊗[ℚ_[p]] V) := by
  letI := D.coefficients
  let P := D.periodRepresentation ι ρ
  exact {
    carrier := {x | ∀ g, P g x = x}
    zero_mem' := fun g => map_zero (P g)
    add_mem' := fun hx hy g => by rw [map_add, hx g, hy g]
    smul_mem' := fun a _ hx g => by rw [map_smul, hx g] }

/-- De Rham admissibility expressed after restricting scalars to `Qp`.
For the finite local field `K`, this is the usual condition
`dim_K D_dR(V) = dim_Qp V`; the left-hand dimension here is multiplied by
`[K : Qp]`. Finiteness is explicit, so infinite invariant spaces cannot
accidentally satisfy a `finrank` equality. -/
def PeriodStructure.IsDeRham (D : PeriodStructure p)
    (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    {V : Type} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V) : Prop :=
  letI := D.coefficients
  let P := D.invariantSpace (AlgEquiv.restrictScalarsHom ℚ_[p]) ρ
  Module.Finite ℚ_[p] P ∧
    Module.finrank ℚ_[p] P =
      Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] V

/-- **Named literature input.** Fontaine's canonical construction supplies
the Galois action and algebraic-constant embedding on the actual library
period ring. [src_brinon_conrad, section 4.4: Proposition 4.4.2,
Proposition 4.4.6, Definition 4.4.7, and Theorem 4.4.13, pp.57--65]
gives the equivariant Fontaine map, complete valuation ring, period field,
and its local fixed fields. [src_brinon_conrad, Proposition 6.3.2, p.76]
then states that de Rham representations are Hodge--Tate. Its comparison
uses `gr(B_dR)=B_HT` with the usual cyclotomic grading. Our existing
comparison uses weight `n` for the `cyclotomic^(-n)` eigenspace.

The action is pinned through the actual integral, tilt, Witt, localization,
and adic quotient-coordinate maps. The algebraic constants lift their given
`Cp` residues through the canonical Fontaine map. These conditions describe
the functorial Fontaine action, rather than merely an arbitrary action that
extends constants. The structure and comparison are selected together. The
dimension condition is the ordinary invariant-tensor definition, expressed
over `Qp` by restriction of scalars. Finite-dimensional Hausdorff continuous
`Qp`-module topologies are the usual ones. No finite inertia, global character
algebraization, weight-zero assertion, or manuscript conclusion occurs here. -/
theorem exists_periodStructure_with_hodgeTateComparison (p : ℕ) [Fact p.Prime] :
    ∃ D : PeriodStructure p,
      ∀ (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
        [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
        [Algebra K ℂ_[p]] [@IsScalarTower K (PadicAlgCl p) ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
        [@IsScalarTower ℚ_[p] K ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul],
      ∀ (V : Type) [AddCommGroup V] [Module ℚ_[p] V]
        [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℚ_[p] V]
        [T2Space V] [FiniteDimensional ℚ_[p] V],
      ∀ (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V),
        (∀ v, Continuous (fun g => ρ g v)) → D.IsDeRham K ρ →
        Function.Bijective (HodgeTate.comparison p
          (AlgEquiv.restrictScalarsHom ℚ_[p])
          (PadicComplex.localGalois_fixes_base p (K := K)) ρ) := by
  sorry

/-- One Fontaine Galois structure, selected before the base field or representation. -/
def periodStructure (p : ℕ) [Fact p.Prime] : PeriodStructure p :=
  (exists_periodStructure_with_hodgeTateComparison p).choose

/-- De Rham admissibility for the actual selected Fontaine period structure. -/
def IsDeRham (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    {V : Type} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V) : Prop :=
  (periodStructure p).IsDeRham K ρ

/-- The cited comparison applies to the same selected period structure used
in the de Rham predicate, with the original local Galois embedding. -/
theorem comparison_bijective_of_isDeRham (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    [Algebra K ℂ_[p]] [@IsScalarTower K (PadicAlgCl p) ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower ℚ_[p] K ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    (V : Type) [AddCommGroup V] [Module ℚ_[p] V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℚ_[p] V]
    [T2Space V] [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)
    (hρ : ∀ v, Continuous (fun g => ρ g v)) (h : IsDeRham p K ρ) :
    Function.Bijective (HodgeTate.comparison p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) ρ) :=
  (exists_periodStructure_with_hodgeTateComparison p).choose_spec K V ρ hρ h

end DeRham
