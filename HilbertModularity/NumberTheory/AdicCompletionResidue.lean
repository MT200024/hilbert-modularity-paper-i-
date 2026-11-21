/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicLocalField

/-! # Global integers and the native completion residue

The global integer ring maps to the native valuation ring of its completion.
Its residue map has precisely the chosen prime as kernel; approximation gives
the canonical identification of global and completed residues used for the
coefficient lattice in [TripathiGoswami].
-/

@[expose] public noncomputable section
open IsDedekindDomain
open scoped NumberField WithZero ValuativeRel Topology
namespace NumberField
variable (K : Type*) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The canonical global-integer map into the native integers of the completion. -/
def adicCompletionIntegerMap : 𝓞 K →+* 𝒪[w.adicCompletion K] :=
  (algebraMap (𝓞 K) (w.adicCompletion K)).codRestrict _ fun a => by
    change ValuativeRel.valuation (w.adicCompletion K)
      (algebraMap (𝓞 K) (w.adicCompletion K) a) ≤ 1
    apply (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion K))
      (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)).le_one_iff_le_one.mpr
    change (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) ((a : K) : w.adicCompletion K) ≤ 1
    rw [w.valuedAdicCompletion_eq_valuation' (a : K)]
    exact w.valuation_le_one a

/-- The map on completion integers retains the original field embedding. -/
@[simp] theorem coe_adicCompletionIntegerMap (a : 𝓞 K) :
    (adicCompletionIntegerMap K w a : w.adicCompletion K) =
      algebraMap (𝓞 K) (w.adicCompletion K) a := rfl

/-- Reduction of global integers through the actual native completion. -/
def adicCompletionResidueMap : 𝓞 K →+* 𝓀[w.adicCompletion K] :=
  (IsLocalRing.residue 𝒪[w.adicCompletion K]).comp (adicCompletionIntegerMap K w)

/-- The native completion residue kills exactly the chosen global prime. -/
theorem adicCompletionResidueMap_eq_zero_iff (a : 𝓞 K) :
    adicCompletionResidueMap K w a = 0 ↔ a ∈ w.asIdeal := by
  change IsLocalRing.residue _ (adicCompletionIntegerMap K w a) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion K))
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)).lt_one_iff_lt_one]
  rw [coe_adicCompletionIntegerMap]
  change (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) ((a : K) : w.adicCompletion K) < 1 ↔ _
  rw [w.valuedAdicCompletion_eq_valuation' (a : K)]
  exact w.valuation_lt_one_iff_mem a

/-- The kernel of the native completion residue map is the actual prime of global integers. -/
theorem ker_adicCompletionResidueMap : RingHom.ker (adicCompletionResidueMap K w) = w.asIdeal := by
  ext a
  exact adicCompletionResidueMap_eq_zero_iff K w a

/-- Every integral completion element is congruent modulo the maximal ideal to a global integer. -/
theorem exists_integer_valuation_sub_lt_one
    (x : w.adicCompletion K)
    (hx : (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) x ≤ 1) :
    ∃ a : 𝓞 K, (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)
      (algebraMap (𝓞 K) (w.adicCompletion K) a - x) < 1 := by
  let v : Valuation (w.adicCompletion K) ℤᵐ⁰ := Valued.v
  have hn : {z | v (z - x) < 1} ∈ 𝓝 x := by
    apply v.mem_nhds_iff.mpr
    refine ⟨1, ?_⟩
    intro z hz
    simpa only [Units.val_one, Valuation.restrict_lt_one_iff] using hz
  obtain ⟨z, hz, y, rfl⟩ := mem_closure_iff_nhds.mp (w.denseRange_algebraMap K x) _ hn
  change v (algebraMap K (w.adicCompletion K) y - x) < 1 at hz
  have hy : w.valuation K y ≤ 1 := by
    rw [← w.valuedAdicCompletion_eq_valuation' y]
    change v (algebraMap K (w.adicCompletion K) y) ≤ 1
    calc
      v (algebraMap K (w.adicCompletion K) y) =
          v ((algebraMap K (w.adicCompletion K) y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (v (algebraMap K (w.adicCompletion K) y - x)) (v x) := v.map_add _ _
      _ ≤ 1 := max_le hz.le hx
  obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer hy (1 : (ℤᵐ⁰)ˣ)
  refine ⟨a, ?_⟩
  have ha' : v (algebraMap (𝓞 K) (w.adicCompletion K) a -
      algebraMap K (w.adicCompletion K) y) < 1 := by
    change v (FinitePlace.embedding w (a : K) - FinitePlace.embedding w y) < 1
    rw [← map_sub]
    change v (((a : K) - y : K) : w.adicCompletion K) < 1
    rw [w.valuedAdicCompletion_eq_valuation' ((a : K) - y)]
    exact ha
  change v (algebraMap (𝓞 K) (w.adicCompletion K) a - x) < 1
  calc
    v (algebraMap (𝓞 K) (w.adicCompletion K) a - x) =
        v ((algebraMap (𝓞 K) (w.adicCompletion K) a - algebraMap K (w.adicCompletion K) y) +
          (algebraMap K (w.adicCompletion K) y - x)) := by rw [sub_add_sub_cancel]
    _ ≤ max (v (algebraMap (𝓞 K) (w.adicCompletion K) a - algebraMap K (w.adicCompletion K) y))
        (v (algebraMap K (w.adicCompletion K) y - x)) := v.map_add _ _
    _ < 1 := max_lt ha' hz

/-- Every actual completed residue is represented by a global algebraic integer. -/
theorem adicCompletionResidueMap_surjective : Function.Surjective (adicCompletionResidueMap K w) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  have hx : (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) (x : w.adicCompletion K) ≤ 1 :=
    (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion K))
      (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)).le_one_iff_le_one.mp x.property
  obtain ⟨a, ha⟩ := exists_integer_valuation_sub_lt_one K w x hx
  refine ⟨a, ?_⟩
  change IsLocalRing.residue _ (adicCompletionIntegerMap K w a) = IsLocalRing.residue _ x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  apply (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion K))
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)).lt_one_iff_lt_one.mpr
  exact ha

/-- The global residue at the chosen prime is canonically the native completion residue field. -/
def adicCompletionResidueEquiv : (𝓞 K ⧸ w.asIdeal) ≃+* 𝓀[w.adicCompletion K] :=
  (Ideal.quotEquivOfEq (ker_adicCompletionResidueMap K w).symm).trans
    ((adicCompletionResidueMap K w).quotientKerEquivOfSurjective
      (adicCompletionResidueMap_surjective K w))

/-- The canonical residue identification is induced by the actual integer embedding. -/
@[simp] theorem adicCompletionResidueEquiv_mk (a : 𝓞 K) :
    adicCompletionResidueEquiv K w (Ideal.Quotient.mk w.asIdeal a) =
      adicCompletionResidueMap K w a := rfl

end NumberField
