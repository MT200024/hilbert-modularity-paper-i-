/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem

/-! # Matrix coefficients from an odd involution

The elementary coefficient-descent calculation used in [src_skinner_hilbert_2009,
pp. 255–256]. This module works in a fixed basis in which an odd involution
is diagonal. Existence and normalization of the Hilbert eigenform's Galois
representation are separate arithmetic inputs.
-/

public noncomputable section

namespace HilbertModularity

variable {G L : Type*} [Group G] [Field L] [CharZero L]

/-- Traces in a subfield determine the two diagonal matrix coefficients once
an odd involution is diagonalized. The argument is valid also in residue
characteristic two, since the coefficient field has characteristic zero. -/
theorem diagonal_coefficients_mem_of_odd_trace
    (K : Subfield L) (ρ : G → Matrix (Fin 2) (Fin 2) L)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g : G) :
    (ρ g) 0 0 ∈ K ∧ (ρ g) 1 1 ∈ K := by
  have hsum : (ρ g) 0 0 + (ρ g) 1 1 ∈ K := by
    simpa only [Matrix.trace_fin_two] using htrace g
  have hdiff : (ρ g) 0 0 - (ρ g) 1 1 ∈ K := by
    have h := htrace (c * g)
    rw [hmul, hc] at h
    simpa [sub_eq_add_neg, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two] using h
  have htwo : (2 : L) ∈ K := by
    simpa only [one_add_one_eq_two] using K.add_mem K.one_mem K.one_mem
  constructor
  · have heq : (ρ g) 0 0 =
        ((ρ g) 0 0 + (ρ g) 1 1 + ((ρ g) 0 0 - (ρ g) 1 1)) / 2 := by ring
    rw [heq]
    exact K.div_mem (K.add_mem hsum hdiff) htwo
  · have heq : (ρ g) 1 1 =
        ((ρ g) 0 0 + (ρ g) 1 1 - ((ρ g) 0 0 - (ρ g) 1 1)) / 2 := by ring
    rw [heq]
    exact K.div_mem (K.sub_mem hsum hdiff) htwo

/-- Every product of an upper-right and a lower-left coefficient lies in
the trace field. This is the matrix-multiplication step of [src_skinner_hilbert_2009,
p. 256]. -/
theorem offDiagonal_product_mem_of_odd_trace
    (K : Subfield L) (ρ : G → Matrix (Fin 2) (Fin 2) L)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g h : G) :
    (ρ g) 0 1 * (ρ h) 1 0 ∈ K := by
  have hgh := (diagonal_coefficients_mem_of_odd_trace K ρ hmul c hc htrace (g * h)).1
  have hg := (diagonal_coefficients_mem_of_odd_trace K ρ hmul c hc htrace g).1
  have hh := (diagonal_coefficients_mem_of_odd_trace K ρ hmul c hc htrace h).1
  have heq : (ρ g) 0 1 * (ρ h) 1 0 =
      (ρ (g * h)) 0 0 - (ρ g) 0 0 * (ρ h) 0 0 := by
    rw [hmul]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [heq]
  exact K.sub_mem hgh (K.mul_mem hg hh)

/-- Scaling the second basis vector by a nonzero lower-left coefficient puts
all matrix entries in the specified subfield. The two nonzero off-diagonal
coefficients are the exact algebraic consequence needed from irreducibility;
no unproved irreducibility assertion is hidden in this lemma. -/
theorem scaled_coefficients_mem_of_odd_trace
    (K : Subfield L) (ρ : G → Matrix (Fin 2) (Fin 2) L)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g : G) :
    (ρ g) 0 0 ∈ K ∧
    (ρ g) 0 1 * (ρ h₀) 1 0 ∈ K ∧
    (ρ g) 1 0 / (ρ h₀) 1 0 ∈ K ∧
    (ρ g) 1 1 ∈ K := by
  have hdiag := diagonal_coefficients_mem_of_odd_trace K ρ hmul c hc htrace g
  have hupper := offDiagonal_product_mem_of_odd_trace K ρ hmul c hc htrace g h₀
  have hnum := offDiagonal_product_mem_of_odd_trace K ρ hmul c hc htrace g₀ g
  have hden := offDiagonal_product_mem_of_odd_trace K ρ hmul c hc htrace g₀ h₀
  have hquot : (ρ g) 1 0 / (ρ h₀) 1 0 =
      ((ρ g₀) 0 1 * (ρ g) 1 0) /
        ((ρ g₀) 0 1 * (ρ h₀) 1 0) := by
    field_simp
  exact ⟨hdiag.1, hupper, hquot ▸ K.div_mem hnum hden, hdiag.2⟩

/-- The descended matrix has entries in the one fixed coefficient subfield.
The entry formula retains the original coefficient embedding and basis
labels; it does not choose a different coefficient field for each element. -/
def oddTraceDescendedMatrix
    (K : Subfield L) (ρ : G → Matrix (Fin 2) (Fin 2) L)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g : G) : Matrix (Fin 2) (Fin 2) K := by
  let h := scaled_coefficients_mem_of_odd_trace K ρ hmul c hc htrace g₀ h₀ hb ht g
  exact !![⟨(ρ g) 0 0, h.1⟩,
           ⟨(ρ g) 0 1 * (ρ h₀) 1 0, h.2.1⟩;
           ⟨(ρ g) 1 0 / (ρ h₀) 1 0, h.2.2.1⟩,
           ⟨(ρ g) 1 1, h.2.2.2⟩]

/-- The four entries after the basis change, viewed in the ambient field. -/
theorem oddTraceDescendedMatrix_map
    (K : Subfield L) (ρ : G → Matrix (Fin 2) (Fin 2) L)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g : G) :
    (oddTraceDescendedMatrix K ρ hmul c hc htrace g₀ h₀ hb ht g).map
      (Subfield.subtype K) =
      !![(ρ g) 0 0, (ρ g) 0 1 * (ρ h₀) 1 0;
         (ρ g) 1 0 / (ρ h₀) 1 0, (ρ g) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oddTraceDescendedMatrix]

/-- The fixed basis change preserves multiplication, so the descended
matrices form an actual representation over the chosen subfield. -/
theorem oddTraceDescendedMatrix_mul
    (K : Subfield L) (ρ : G → Matrix (Fin 2) (Fin 2) L)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g h : G) :
    oddTraceDescendedMatrix K ρ hmul c hc htrace g₀ h₀ hb ht (g * h) =
      oddTraceDescendedMatrix K ρ hmul c hc htrace g₀ h₀ hb ht g *
        oddTraceDescendedMatrix K ρ hmul c hc htrace g₀ h₀ hb ht h := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [oddTraceDescendedMatrix, hmul, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp

theorem oddTraceDescendedMatrix_one
    (K : Subfield L) (ρ : G → Matrix (Fin 2) (Fin 2) L)
    (hone : ρ 1 = 1)
    (hmul : ∀ g h, ρ (g * h) = ρ g * ρ h)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0) :
    oddTraceDescendedMatrix K ρ hmul c hc htrace g₀ h₀ hb ht 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oddTraceDescendedMatrix, hone]

/-- Algebraic rank-two coefficient descent from a trace field and an odd
involution, in Skinner's fixed-basis normalization. Continuity of the
descended action follows separately from continuity of the original matrix
coefficients in the induced subfield topology. -/
def oddTraceDescendedMonoidHom
    (K : Subfield L) (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0) :
    G →* Matrix (Fin 2) (Fin 2) K where
  toFun := oddTraceDescendedMatrix K ρ (fun g h => ρ.map_mul g h)
    c hc htrace g₀ h₀ hb ht
  map_one' := oddTraceDescendedMatrix_one K ρ ρ.map_one
    (fun g h => ρ.map_mul g h) c hc htrace g₀ h₀ hb ht
  map_mul' := oddTraceDescendedMatrix_mul K ρ
    (fun g h => ρ.map_mul g h) c hc htrace g₀ h₀ hb ht

/-- The descended action is the fixed-basis matrix constructed above. -/
@[simp] theorem oddTraceDescendedMonoidHom_apply
    (K : Subfield L) (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (g : G) :
    oddTraceDescendedMonoidHom K ρ c hc htrace g₀ h₀ hb ht g =
      oddTraceDescendedMatrix K ρ (fun g h => ρ.map_mul g h)
        c hc htrace g₀ h₀ hb ht g := by
  rfl

end HilbertModularity
