/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.OddInvolutionCoefficientDescent

/-! # Continuity of odd-involution coefficient descent

The fixed diagonal basis change in [src_skinner_hilbert_2009, pp. 255–256]
preserves continuity of each matrix coefficient. The coefficient subfield has
its induced topology; no closedness assumption is needed for this descent.
-/

public noncomputable section

namespace HilbertModularity

variable {G L : Type*} [Group G] [TopologicalSpace G]
  [Field L] [TopologicalSpace L] [IsTopologicalRing L]

/-- Trace values in a closed coefficient subfield on a dense set determine
trace values on the whole group. In the arithmetic application the dense set
comes from Chebotarev and the subfield is the chosen local coefficient field. -/
theorem oddTrace_mem_of_dense
    (K : Subfield L) (hK : IsClosed (K : Set L))
    (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (hρ : ∀ i j : Fin 2, Continuous (fun g : G => (ρ g) i j))
    (D : Set G) (hD : closure D = Set.univ)
    (htrace : ∀ g ∈ D, Matrix.trace (ρ g) ∈ K)
    (g : G) : Matrix.trace (ρ g) ∈ K := by
  have hcontinuous : Continuous (fun g : G => Matrix.trace (ρ g)) := by
    have hsum : Continuous (fun g : G => (ρ g) 0 0 + (ρ g) 1 1) :=
      (hρ 0 0).add (hρ 1 1)
    simpa only [Matrix.trace_fin_two] using hsum
  have hclosed : IsClosed ((fun g : G => Matrix.trace (ρ g)) ⁻¹' (K : Set L)) :=
    hK.preimage hcontinuous
  have hsubset : D ⊆ (fun g : G => Matrix.trace (ρ g)) ⁻¹' (K : Set L) := by
    intro x hx
    exact htrace x hx
  have hclosure := closure_minimal hsubset hclosed
  apply hclosure
  rw [hD]
  trivial

variable [CharZero L]

/-- The matrix coefficients of the fixed-basis descent are continuous in the
induced topology on the coefficient subfield. -/
theorem oddTraceDescendedMatrix_continuous
    (K : Subfield L) (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (hρ : ∀ i j : Fin 2, Continuous (fun g : G => (ρ g) i j)) :
    Continuous (fun g : G =>
      oddTraceDescendedMatrix K ρ (fun g h => ρ.map_mul g h)
        c hc htrace g₀ h₀ hb ht g) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  have heq (g : G) :
      ((oddTraceDescendedMatrix K ρ (fun g h => ρ.map_mul g h)
          c hc htrace g₀ h₀ hb ht g i j : K) : L) =
        (!![(ρ g) 0 0, (ρ g) 0 1 * (ρ h₀) 1 0;
           (ρ g) 1 0 / (ρ h₀) 1 0, (ρ g) 1 1] : Matrix (Fin 2) (Fin 2) L) i j := by
    have h := congrFun (congrFun
      (oddTraceDescendedMatrix_map K ρ (fun g h => ρ.map_mul g h)
        c hc htrace g₀ h₀ hb ht g) i) j
    calc
      ((oddTraceDescendedMatrix K ρ (fun g h => ρ.map_mul g h)
          c hc htrace g₀ h₀ hb ht g i j : K) : L) =
          Subfield.subtype K
            (oddTraceDescendedMatrix K ρ (fun g h => ρ.map_mul g h)
              c hc htrace g₀ h₀ hb ht g i j) := rfl
      _ = _ := by simpa only [Matrix.map_apply] using h
  simp_rw [heq]
  fin_cases i <;> fin_cases j
  · simpa using hρ 0 0
  · simpa using (hρ 0 1).mul_const ((ρ h₀) 1 0)
  · simpa using (hρ 1 0).div_const ((ρ h₀) 1 0)
  · simpa using hρ 1 1

/-- The descended monoid homomorphism is continuous whenever the original
matrix coefficients are continuous. -/
theorem oddTraceDescendedMonoidHom_continuous
    (K : Subfield L) (ρ : G →* Matrix (Fin 2) (Fin 2) L)
    (c : G) (hc : ρ c = !![1, 0; 0, -1])
    (htrace : ∀ g, Matrix.trace (ρ g) ∈ K)
    (g₀ h₀ : G) (hb : (ρ g₀) 0 1 ≠ 0) (ht : (ρ h₀) 1 0 ≠ 0)
    (hρ : ∀ i j : Fin 2, Continuous (fun g : G => (ρ g) i j)) :
    Continuous (oddTraceDescendedMonoidHom K ρ c hc htrace g₀ h₀ hb ht) := by
  change Continuous (fun g : G =>
    oddTraceDescendedMonoidHom K ρ c hc htrace g₀ h₀ hb ht g)
  simpa only [oddTraceDescendedMonoidHom_apply] using
    oddTraceDescendedMatrix_continuous K ρ c hc htrace g₀ h₀ hb ht hρ

end HilbertModularity
