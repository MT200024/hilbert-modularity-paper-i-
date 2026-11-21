/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.HodgeTateInjectivity
public import HilbertModularity.RepresentationTheory.DeterminantCharacter

/-! # Labelled weights of a determinant and its Tate twist

The standard tensor compatibility of Hodge–Tate comparison is the literature
boundary. The rank-two specialization below proves the weight calculation used
in [TripathiGoswamiRevised, Proposition 2.5].
-/

public noncomputable section

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
  [Algebra K ℂ_[p]] [@IsScalarTower K (PadicAlgCl p) ℂ_[p]
    Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [@IsScalarTower ℚ_[p] K ℂ_[p]
    Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  {E V : Type*} [NontriviallyNormedField E] [CompleteSpace E]
  [NormedAlgebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
  [AddCommGroup V] [Module E V] [Module ℚ_[p] V] [IsScalarTower ℚ_[p] E V]
  [FiniteDimensional E V] [FiniteDimensional ℚ_[p] V]
  [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]

/-- The local determinant times the actual cyclotomic character. In our
cohomological convention the cyclotomic character has weight `-1`. -/
def normalizedDeterminant (ρ : Representation E Gal(PadicAlgCl p/K) V) :
    Gal(PadicAlgCl p/K) →* Eˣ :=
  ρ.determinantCharacter *
    (Field.cyclotomicCharacterWithCoefficients ℚ_[p] p E).toMonoidHom.comp
      (AlgEquiv.restrictScalarsHom ℚ_[p])

omit [FiniteDimensional ℚ_[p] K] [Algebra K ℂ_[p]]
  [@IsScalarTower K (PadicAlgCl p) ℂ_[p]
    Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [@IsScalarTower ℚ_[p] K ℂ_[p]
    Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [CompleteSpace E] [FiniteDimensional ℚ_[p] E]
  [Module ℚ_[p] V] [IsScalarTower ℚ_[p] E V] [FiniteDimensional E V]
  [FiniteDimensional ℚ_[p] V] [TopologicalSpace V]
  [IsModuleTopology ℚ_[p] V] in
/-- Evaluation uses the actual determinant and cyclotomic action. -/
@[simp] theorem normalizedDeterminant_apply
    (ρ : Representation E Gal(PadicAlgCl p/K) V) (g : Gal(PadicAlgCl p/K)) :
    normalizedDeterminant p K ρ g = ρ.determinantCharacter g *
      Field.cyclotomicCharacterWithCoefficients ℚ_[p] p E
        (AlgEquiv.restrictScalarsHom ℚ_[p] g) := (rfl)

/-- **Hodge–Tate determinant and Tate-twist compatibility.**
[src_brinon_conrad, Theorem 2.4.11, p.23; Definition 2.4.12 and following
paragraph, p.24] states exact tensor compatibility and stability under
subquotients. Apply it to the top alternating summand over `E`, then tensor
with `Qp(1)`. The coefficient action is retained by functoriality; splitting
the commuting local-field action gives precisely the displayed labels.
At each label the determinant weight is the sum of the input weights, and
the twist subtracts one. Only comparison bijectivity and off-weight vanishing
are asserted, as needed downstream. This is a named literature admission.

`weights τ` lists all multiplicities, including repeats. The actual local
absolute Galois group, continuous action, finite coefficient extension and
every embedding of the local field are explicit. No geometric realization
or manuscript-specific comparison is asserted. -/
theorem normalizedDeterminant_comparison_and_weights
    (ρ : Representation E Gal(PadicAlgCl p/K) V)
    (hρ : Continuous fun gv : Gal(PadicAlgCl p/K) × V => ρ gv.1 gv.2)
    (d : ℕ) (hd : Module.finrank E V = d)
    (weights : (K →ₐ[ℚ_[p]] AlgebraicClosure E) → Fin d → ℤ)
    (hHT : Function.Bijective (comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) (ρ.restrictScalars ℚ_[p])))
    (hmult : ∀ τ n, Module.finrank (AlgebraicClosure E)
      (labelledWeightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K)) ρ n τ) =
          ∑ i, if weights τ i = n then 1 else 0) :
    Function.Bijective (comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K))
      ((Representation.ofCharacter (normalizedDeterminant p K ρ)).restrictScalars ℚ_[p])) ∧
    ∀ τ n, n ≠ (∑ i, weights τ i) - 1 →
      labelledWeightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K))
        (Representation.ofCharacter (normalizedDeterminant p K ρ)) n τ = ⊥ := by
  sorry

/-- Weights `{0,1}` make every labelled weight of the normalized determinant
zero. This is the arithmetic `0 + 1 - 1 = 0` specialization in the manuscript,
using the general cited determinant compatibility rather than admitting the
manuscript's finite-order determinant conclusion. -/
theorem normalizedDeterminant_weights_zero_of_weights_zero_one
    (ρ : Representation E Gal(PadicAlgCl p/K) V)
    (hρ : Continuous fun gv : Gal(PadicAlgCl p/K) × V => ρ gv.1 gv.2)
    (hd : Module.finrank E V = 2)
    (hHT : Function.Bijective (comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K)) (ρ.restrictScalars ℚ_[p])))
    (hmult : ∀ τ n, Module.finrank (AlgebraicClosure E)
      (labelledWeightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K)) ρ n τ) =
          (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0)) :
    Function.Bijective (comparison p (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K))
      ((Representation.ofCharacter (normalizedDeterminant p K ρ)).restrictScalars ℚ_[p])) ∧
    ∀ τ n, n ≠ 0 → labelledWeightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K))
      (Representation.ofCharacter (normalizedDeterminant p K ρ)) n τ = ⊥ := by
  obtain ⟨hbij, hw⟩ := normalizedDeterminant_comparison_and_weights p K ρ hρ 2 hd
    (fun _ => ![0, 1]) hHT (by
      intro τ n
      rw [hmult, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm])
  refine ⟨hbij, fun τ n hn => hw τ n ?_⟩
  simpa using hn

end HodgeTate
