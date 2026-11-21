/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteCharacterTwist

/-! # Injectivity of the local Hodge–Tate comparison

The Serre–Tate lemma [src_brinon_conrad, Lemma 2.3.1, p.16;
Remark 2.3.2, p.17] applies to the completed period tensor of a continuous
finite-dimensional representation of the actual local absolute Galois group.
This named literature input does not assert that the representation is
Hodge–Tate or that its comparison map is surjective.
-/

public noncomputable section

namespace HodgeTate

/-- **Serre–Tate injectivity**, in the untwisted-eigenspace formulation of
[src_brinon_conrad, Lemma 2.3.1 and Remark 2.3.2, pp.16–17]. Apply that result
to `W = Cp ⊗[Qp] V`. Our weight `q` uses the eigencharacter `χ^(-q)`, exactly
the source's `W[q]`; each summand map sends `c ⊗ x` to `c • x`.

The hypotheses retain a finite embedded local base field, the actual absolute
Galois group with its Krull topology, and a finite-dimensional continuous
representation. No such assertion is made for an arbitrary abstract group.
This is an admitted literature theorem, not a proof of the Serre–Tate lemma. -/
theorem comparison_injective
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    [Algebra K ℂ_[p]] [@IsScalarTower K (PadicAlgCl p) ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower ℚ_[p] K ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)
    (hρ : Continuous fun gv : Gal(PadicAlgCl p/K) × V => ρ gv.1 gv.2) :
    Function.Injective (comparison p (K := K)
      (AlgEquiv.restrictScalarsHom ℚ_[p] :
        Gal(PadicAlgCl p/K) →* Gal(PadicAlgCl p/ℚ_[p]))
      (PadicComplex.localGalois_fixes_base p (K := K)) ρ) := by
  sorry

/-- For an actual continuous local representation, fixed periods span exactly
when the comparison is bijective and every nonzero weight space vanishes.
This proves the fixed-period reformulation used by the ordinary-quotient APIs,
using the named Serre–Tate input above. It does not supply a geometric quotient. -/
theorem local_zeroWeightSpan_eq_top_iff_comparison_bijective_and_weights_zero
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra K (PadicAlgCl p)] [IsScalarTower ℚ_[p] K (PadicAlgCl p)]
    [Algebra K ℂ_[p]] [@IsScalarTower K (PadicAlgCl p) ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower ℚ_[p] K ℂ_[p]
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)
    (hρ : Continuous fun gv : Gal(PadicAlgCl p/K) × V => ρ gv.1 gv.2) :
    zeroWeightSpan (ι := AlgEquiv.restrictScalarsHom ℚ_[p]) ρ = ⊤ ↔
      Function.Bijective (comparison p (K := K) (AlgEquiv.restrictScalarsHom ℚ_[p])
        (PadicComplex.localGalois_fixes_base p (K := K)) ρ) ∧
        ∀ q : ℤ, q ≠ 0 →
          weightSpace p (AlgEquiv.restrictScalarsHom ℚ_[p]) ρ q = ⊥ := by
  exact zeroWeightSpan_eq_top_iff_comparison_bijective_and_weights_zero p
    (AlgEquiv.restrictScalarsHom ℚ_[p])
    (PadicComplex.localGalois_fixes_base p (K := K)) ρ
    (comparison_injective p K ρ hρ)

end HodgeTate
