/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.OddInvolutionContinuity

/-! # Frobenius polynomials under odd-involution coefficient descent

The fixed basis change of [src_skinner_hilbert_2009, pp. 255–256]
preserves trace and determinant. Thus descent to a specified coefficient
subfield retains the independently given geometric-Frobenius polynomial.
This does not construct the Galois actions attached to a Hilbert eigenform.
-/

public noncomputable section

namespace HilbertModularity

variable {G L : Type*} [Group G] [Field L] [CharZero L]

/-- The descended matrix has the original trace after extension of scalars. -/
theorem oddTraceDescendedMatrix_trace
    (K : Subfield L) (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g : G) :
    Matrix.trace ((oddTraceDescendedMatrix K ρ (fun x y => ρ.map_mul x y)
      c hc htrace g₀ h₀ hb ht g).map (Subfield.subtype K)) =
        Matrix.trace (ρ g) := by
  rw [oddTraceDescendedMatrix_map]
  simp [Matrix.trace_fin_two]

/-- The descended matrix has the original determinant after extension of
scalars. The scaling parameter is fixed and nonzero for the entire action. -/
theorem oddTraceDescendedMatrix_det
    (K : Subfield L) (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g : G) :
    Matrix.det ((oddTraceDescendedMatrix K ρ (fun x y => ρ.map_mul x y)
      c hc htrace g₀ h₀ hb ht g).map (Subfield.subtype K)) =
        Matrix.det (ρ g) := by
  rw [oddTraceDescendedMatrix_map]
  simp only [Matrix.det_fin_two]
  simp
  field_simp

/-- The polynomial of the original two-dimensional action descends to the
same coefficient subfield as its fixed-basis matrices. This applies in
particular to geometric Frobenius whenever the independently supplied action
and its trace have the stated descent data. -/
theorem oddTraceDescendedMatrix_charpoly
    (K : Subfield L) (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g : G) :
    (oddTraceDescendedMatrix K ρ (fun x y => ρ.map_mul x y)
      c hc htrace g₀ h₀ hb ht g).charpoly.map (Subfield.subtype K) =
        (ρ g).charpoly := by
  rw [← Matrix.charpoly_map, Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  rw [oddTraceDescendedMatrix_trace, oddTraceDescendedMatrix_det]

end HilbertModularity
