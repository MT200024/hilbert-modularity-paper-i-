/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteCharacterTwist

/-! # Labelled Hodge–Tate weights under finite character twists

A finite character becomes trivial after a finite local extension. Its
actual tensor period identifies the canonical comparisons, and finite
extension descent preserves each labelled Hodge–Tate multiplicity
[src_brinon_conrad, Theorem 2.4.6, p.20; Theorem 2.4.11 and
Definition 2.4.12, pp.23–24].
-/

public noncomputable section

namespace HodgeTate

variable (p : ℕ) [Fact p.Prime]
  {K E V : Type*} [Field K] [Algebra ℚ_[p] K] [Algebra K (PadicAlgCl p)]
  [IsScalarTower ℚ_[p] K (PadicAlgCl p)] [Algebra K ℂ_[p]]
  [hKC : @IsScalarTower K (PadicAlgCl p) ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [hQKC : @IsScalarTower ℚ_[p] K ℂ_[p] Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [FiniteDimensional ℚ_[p] K]
  [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
  [TopologicalSpace Eˣ] [T1Space Eˣ]
  [AddCommGroup V] [Module E V] [Module ℚ_[p] V]
  [IsScalarTower ℚ_[p] E V] [FiniteDimensional E V]
  (ρ : Representation E Gal(PadicAlgCl p/K) V)
  (χ : Gal(PadicAlgCl p/K) →* Eˣ)
  (hχ : Continuous χ) (horder : IsOfFinOrder χ)

include hχ horder hKC hQKC

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional E V] in
/-- The existing finite-character tensor period transports bijectivity of
the actual canonical Hodge–Tate comparison. -/
theorem finiteCharacterTwist_comparison_bijective_iff :
    Function.Bijective (comparison p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K))
      (ρ.restrictScalars ℚ_[p])) ↔
    Function.Bijective (comparison p
      (AlgEquiv.restrictScalarsHom ℚ_[p])
      (PadicComplex.localGalois_fixes_base p (K := K))
      ((ρ.characterTwist χ).restrictScalars ℚ_[p])) := by
  obtain ⟨c, hc⟩ :=
    PadicComplex.exists_local_tensor_period_of_continuous_isOfFinOrder
      p χ hχ horder
  exact coefficientTwist_comparison_bijective_iff p
    (AlgEquiv.restrictScalarsHom ℚ_[p])
    (PadicComplex.localGalois_fixes_base p (K := K)) ρ χ c hc

/-- Finite local characters have weight zero at every local label, so
tensoring preserves the labelled multiplicity of every weight.
This is the standard finite-extension invariance of Hodge–Tate weights
[src_brinon_conrad, Theorem 2.4.6, p.20; Theorem 2.4.11 and
Definition 2.4.12, pp.23–24], stated for the
actual coefficient and local-field embeddings. It is a generic
literature interface and makes no Euler, RM, Frobenius or modularity
assertion. -/
theorem finiteCharacterTwist_labelledWeightSpace_finrank
    (n : ℤ) (τ : K →ₐ[ℚ_[p]] AlgebraicClosure E) :
    Module.finrank (AlgebraicClosure E)
        (labelledWeightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
          (PadicComplex.localGalois_fixes_base p (K := K))
          (ρ.characterTwist χ) n τ) =
      Module.finrank (AlgebraicClosure E)
        (labelledWeightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p])
          (PadicComplex.localGalois_fixes_base p (K := K))
          ρ n τ) := by
  sorry

end HodgeTate
