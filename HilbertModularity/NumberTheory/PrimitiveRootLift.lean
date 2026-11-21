/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.ZMod.Units

@[expose] public section

/-! # Lifting primitive roots through power maps -/

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If `N ∣ M`, any primitive `N`th root is the `(M/N)`th power of a
primitive `M`th root, provided the coefficient domain contains one primitive
`M`th root. The lift uses surjectivity of the reduction map on residue-class units. -/
theorem exists_primitiveRoot_pow_eq {N M : ℕ} [NeZero N] [NeZero M]
    {ζ ξ : R} (hζ : IsPrimitiveRoot ζ M) (hξ : IsPrimitiveRoot ξ N) (hd : N ∣ M) :
    ∃ η : R, IsPrimitiveRoot η M ∧ η ^ (M / N) = ξ := by
  classical
  have hbase : IsPrimitiveRoot (ζ ^ (M / N)) N :=
    hζ.pow (NeZero.pos M) (Nat.div_mul_cancel hd).symm
  obtain ⟨i, _, hi, hξi⟩ := hbase.isPrimitiveRoot_iff.mp hξ
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hd (ZMod.unitOfCoprime i hi)
  have hc : ((u : ZMod M).val : ZMod N) = (i : ZMod N) := by
    simpa [ZMod.unitsMap_def] using congrArg Units.val hu
  rw [ZMod.natCast_eq_natCast_iff] at hc
  refine ⟨ζ ^ (u : ZMod M).val, hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u), ?_⟩
  rw [pow_right_comm, ← hξi]
  apply ((hbase.isOfFinOrder (NeZero.ne N)).pow_eq_pow_iff_modEq).mpr
  simpa only [← hbase.eq_orderOf] using hc

end IsPrimitiveRoot
