/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization

/-! # Quotients with equal local specializations

An integral numerator and a unit denominator with the same residue have quotient
congruent to one. This connects residual determinant equality to the local
specialization criterion in [TripathiGoswami, determinant rigidity].
-/

@[expose] public noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] (P : HeightOneSpectrum R)

/-- Dividing two elements with equal residue, the denominator a local unit, gives residue one. -/
theorem specialization_div_eq_one (x y : K) (hx : P.valuation K x ≤ 1)
    (hy : P.valuation K y = 1)
    (h : P.specialization x hx = P.specialization y hy.le) :
    ∃ hxy : P.valuation K (x / y) ≤ 1, P.specialization (x / y) hxy = 1 := by
  have hy0 : y ≠ 0 := by
    intro he
    simp [he] at hy
  have hxy : P.valuation K (x / y) ≤ 1 := by
    rw [map_div₀, hy, div_one]
    exact hx
  refine ⟨hxy, ?_⟩
  have he : P.localElement (x / y) hxy * P.localElement y hy.le = P.localElement x hx :=
    Subtype.ext (div_mul_cancel₀ x hy0)
  have hr := congrArg P.localResidue he
  rw [map_mul] at hr
  change P.specialization (x / y) hxy * P.specialization y hy.le = P.specialization x hx at hr
  apply mul_right_cancel₀ (P.specialization_ne_zero y hy)
  rw [one_mul, hr, h]

end IsDedekindDomain.HeightOneSpectrum
