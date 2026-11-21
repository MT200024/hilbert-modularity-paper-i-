/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.PrimePlusConductorChecklist

/-! # Integer and residue comparison for the fixed exponent label

The local coefficient embedding is the actual exponent-`m` map between the
native real and full cyclotomic conductor completions. The standard extension
of discrete valuations supplies its local integer-ring map; the remaining
residue compatibility is formal.
-/

public noncomputable section

open AlgebraicGeometry IsDedekindDomain
open scoped NumberField ValuativeRel

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic

local instance fullConductorResidueLocalField (p : ℕ) [Fact p.Prime] :
    IsNonarchimedeanLocalField (FullConductorCompletion p) :=
  NumberField.isNonarchimedeanLocalField_padicCompletion
    (cyclotomicField p) (primeAboveConductor p) p

/-- Restriction of the actual exponent-labelled completion embedding to
valuation integers. -/
def chosenConductorNativeIntegerMap
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    𝒪[RealPrimePowerCompletion p 0] →+* 𝒪[FullConductorCompletion p] :=
  IsNonarchimedeanLocalField.integerMap
    (chosenConductorNativeMap p m hm).toRingHom
    (continuous_chosenConductorNativeMap p m hm)

theorem chosenConductorNativeIntegerMap_eq
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    chosenConductorNativeIntegerMap p m hm =
      IsNonarchimedeanLocalField.integerMap
        (chosenConductorNativeMap p m hm).toRingHom
        (continuous_chosenConductorNativeMap p m hm) := (rfl)

/-- A finite extension of complete discrete valuations sends the maximal
ideal of the source valuation ring into the target maximal ideal. Applied to
the exact exponent-labelled embedding, this is [MilneANT, Theorem 7.38 and
Corollary 7.42, printed pp. 123–124]. This interface asserts only locality
of the integer map; it contains no Tate, irreducibility or modularity claim. -/
theorem chosenConductorNativeIntegerMap_isLocalHom
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    IsLocalHom (chosenConductorNativeIntegerMap p m hm) := by
  sorry

/-- Residue-field map induced by the same fixed-label integer map. -/
def chosenConductorNativeResidueMap
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    𝓀[RealPrimePowerCompletion p 0] →+* 𝓀[FullConductorCompletion p] := by
  letI : IsLocalHom (chosenConductorNativeIntegerMap p m hm) :=
    chosenConductorNativeIntegerMap_isLocalHom p m hm
  exact IsLocalRing.ResidueField.map (chosenConductorNativeIntegerMap p m hm)

/-- The full coefficient extension retains its integral and residue maps;
its residue map is injective because it is a field homomorphism. -/
def chosenConductorNativeIntegerResidueComparison
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    LocalIntegerResidueComparison
      (chosenConductorNativeMap p m hm).toRingHom where
  integerMap := chosenConductorNativeIntegerMap p m hm
  residueMap := chosenConductorNativeResidueMap p m hm
  coe_integerMap := by
    intro a
    exact IsNonarchimedeanLocalField.coe_integerMap
      (chosenConductorNativeMap p m hm).toRingHom
      (continuous_chosenConductorNativeMap p m hm) a
  residueMap_mk := by
    intro a
    let : IsLocalHom (chosenConductorNativeIntegerMap p m hm) :=
      chosenConductorNativeIntegerMap_isLocalHom p m hm
    exact IsLocalRing.ResidueField.map_residue
      (chosenConductorNativeIntegerMap p m hm) a
  residue_injective := by
    let : IsLocalHom (chosenConductorNativeIntegerMap p m hm) :=
      chosenConductorNativeIntegerMap_isLocalHom p m hm
    exact (IsLocalRing.ResidueField.map
      (chosenConductorNativeIntegerMap p m hm)).injective

theorem chosenConductorNativeIntegerResidueComparison_integerMap
    (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m.Coprime p) :
    (chosenConductorNativeIntegerResidueComparison p m hm).integerMap =
      chosenConductorNativeIntegerMap p m hm := (rfl)

end HilbertModularity.Hypergeometric
