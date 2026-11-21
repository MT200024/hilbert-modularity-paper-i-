/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Perfectoid.BDeRham
public import HilbertModularity.NumberTheory.PadicGalois

/-! # The actual Fontaine de Rham period ring

The carrier is mathlib's Witt-vector/Fontaine-kernel completion and localization
for the actual valuation integers of `Cp`. Only the standard completeness
preconditions are imported from the literature here.
-/

public noncomputable section

namespace PadicComplex

/-- **Named literature input.** The valuation integers in the completed
algebraic closure are p-adically complete and p is not a unit.
This is the standard completeness used for `O_C` in [src_brinon_conrad,
section 4.3, p.52, before Proposition 4.3.1] and in the period construction
of section 4.4, pp.56--60. Indeed `p^n O_C` is the closed norm ball of radius
`p^(-n)`; these balls give the same complete topology as the norm on `O_C`,
and `|p|=p^(-1)<1`. This admission supplies no representation or period
comparison and is not a claim that the cited proposition states this
specialization verbatim. -/
theorem integerRing_period_hypotheses (p : ℕ) [Fact p.Prime] :
    ¬IsUnit (p : PadicComplexInt p) ∧
      IsAdicComplete (Ideal.span {(p : PadicComplexInt p)}) (PadicComplexInt p) := by
  sorry

instance integerRing_prime_not_unit (p : ℕ) [Fact p.Prime] :
    Fact (¬IsUnit (p : PadicComplexInt p)) := ⟨(integerRing_period_hypotheses p).1⟩

instance integerRing_adicComplete (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (Ideal.span {(p : PadicComplexInt p)}) (PadicComplexInt p) :=
  (integerRing_period_hypotheses p).2

/-- Fontaine's period ring on the actual p-adic complex valuation integers,
using the library's completion of Witt vectors and localization at the
Fontaine-kernel generators. -/
abbrev deRhamRing (p : ℕ) [Fact p.Prime] := BDeRham (PadicComplexInt p) p

/-- The ring structure is the existing localization ring structure. -/
instance deRhamRing_commRing (p : ℕ) [Fact p.Prime] : CommRing (deRhamRing p) := by
  unfold deRhamRing BDeRham
  infer_instance

/-- The actual tilt used in the Fontaine construction. -/
abbrev fontaineTilt (p : ℕ) [Fact p.Prime] := PreTilt (PadicComplexInt p) p

/-- Witt vectors on the actual tilt. -/
abbrev fontaineWitt (p : ℕ) [Fact p.Prime] := WittVector p (fontaineTilt p)

/-- The rational Witt ring completed in the definition of `B_dR^+`. -/
abbrev fontaineWittInvertP (p : ℕ) [Fact p.Prime] :=
  Localization.Away (p : fontaineWitt p)

/-- The kernel of the actual rational Fontaine map. -/
abbrev fontaineIdeal (p : ℕ) [Fact p.Prime] :=
  RingHom.ker (fontaineThetaInvertP (PadicComplexInt p) p)

/-- The actual completed positive de Rham period ring. -/
@[expose] def deRhamPlus (p : ℕ) [Fact p.Prime] := BDeRhamPlus (PadicComplexInt p) p

instance deRhamPlus_commRing (p : ℕ) [Fact p.Prime] : CommRing (deRhamPlus p) := by
  unfold deRhamPlus
  infer_instance

/-- The canonical map into the Fontaine-kernel completion. -/
def wittToDeRhamPlus (p : ℕ) [Fact p.Prime] : fontaineWittInvertP p → deRhamPlus p :=
  AdicCompletion.of (fontaineIdeal p) (fontaineWittInvertP p)

/-- The canonical localization map from the positive period ring. -/
def plusToDeRhamRing (p : ℕ) [Fact p.Prime] : deRhamPlus p → deRhamRing p := by
  unfold deRhamPlus deRhamRing BDeRham
  intro b
  exact algebraMap (BDeRhamPlus (PadicComplexInt p) p) _ b

/-- A defining quotient in the Fontaine-kernel completion. -/
def deRhamQuotient (p : ℕ) [Fact p.Prime] (n : ℕ) : Type :=
  fontaineWittInvertP p ⧸ ((fontaineIdeal p) ^ n • ⊤ :
    Submodule (fontaineWittInvertP p) (fontaineWittInvertP p))

/-- Projection onto a defining quotient of the Fontaine-kernel completion. -/
def deRhamCoefficient (p : ℕ) [Fact p.Prime] (n : ℕ) (b : deRhamPlus p) :
    deRhamQuotient p n :=
  (show AdicCompletion (fontaineIdeal p) (fontaineWittInvertP p) from b).val n

/-- The canonical map from the localized valuation integers to `Cp`. -/
def localizedIntegersToComplex (p : ℕ) [Fact p.Prime] :
    Localization.Away (p : PadicComplexInt p) →+* ℂ_[p] :=
  Localization.awayLift (PadicComplexInt p).subtype (p : PadicComplexInt p) (by
    apply isUnit_iff_ne_zero.mpr
    change (p : ℂ_[p]) ≠ 0
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- The rational Fontaine map with its actual `Cp` target. -/
def fontaineToComplex (p : ℕ) [Fact p.Prime] : fontaineWittInvertP p →+* ℂ_[p] :=
  (localizedIntegersToComplex p).comp (fontaineThetaInvertP (PadicComplexInt p) p)

end PadicComplex
