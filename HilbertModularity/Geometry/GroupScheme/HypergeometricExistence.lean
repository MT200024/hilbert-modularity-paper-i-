/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.CoefficientMonodromy
public import HilbertModularity.Geometry.GroupScheme.TateMonodromy
public import HilbertModularity.Geometry.GroupScheme.Fiber
public import HilbertModularity.Geometry.ProjectiveLine.NormalizedCuspGenerators
public import HilbertModularity.NumberTheory.Cyclotomic
public import HilbertModularity.Monodromy.Admissible
public import Mathlib.Topology.Algebra.Group.Subgroup

/-! # The hypergeometric abelian scheme attached to the integral base triple

We follow [DarmonFibres, Section 3, Propositions 3.2 and 3.4].
The monodromy statement uses actual rational-function inertia and the actual
Tate action of the one abelian scheme. The local generators retain their usual conjugacy choices and share the
compatible root-of-unity orientation fixed on printed p. 2, with the specified
real cyclotomic trace label. No global generation or arithmetic exact-sequence
conclusion is included, and no descent to ℚ is asserted.

The convention is covariant Tate monodromy. The geometric rank-two
determinant-one representation is self-dual; this identifies the dual convention
by one simultaneous change of basis for all three local monodromy matrices.
The all-prime comparison uses Proposition 3.4 as well as the Tate-module
discussion in Section 3. Positive multiplication being finite, étale and
surjective is exposed standard characteristic-zero abelian-scheme geometry;
these are obligations of the stated existence theorem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj NumberField TensorProduct MatrixGroups ModuleCat.Algebra
namespace HilbertModularity.Hypergeometric
open _root_.HilbertModularity.Cyclotomic

/-- Simultaneous standard cusp matrices on the actual coefficient Tate module.
The family and integral multiplication are fixed before choosing the prime. -/
def HasStandardInertiaRealization (N : ℕ) [NeZero N]
    (A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))))
    (φ : 𝓞 (realCyclotomicField N) →+* End A)
    (hfinite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 A).hom.hom.hom.left)
    (hetale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 A).hom.hom.hom.left) : Prop :=
      ∃ γ c : Fin 3 →
          (AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[RatFunc (realCyclotomicField N)]
            AlgebraicClosure (RatFunc (realCyclotomicField N))),
      ((∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map (MulAut.conj (c i)).toMonoidHom) ∧
        ∃ ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N)),
          ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ ∧
          ζ N + (ζ N)⁻¹ =
            algebraMap (realCyclotomicField N) _ (tau N 1)) ∧
      ∀ (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        letI : ∀ n : ℕ, IsFinite (p ^ n • 𝟙 A).hom.hom.hom.left :=
          fun n => hfinite (p ^ n) (pow_pos hp.pos n)
        letI : ∀ n : ℕ, Etale (p ^ n • 𝟙 A).hom.hom.hom.left :=
          fun n => hetale (p ^ n) (pow_pos hp.pos n)
        let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
        let V := TateModule.rational p
          (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N)) x ⟶ A.X))
        let Θ := GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
          A p (realCyclotomicField N) φ x
        letI : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V := Module.compHom V Θ.toRingHom
        ∃ b : Module.Basis (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V,
          ∀ (i : Fin 3) (v : V),
            (b.repr (GroupScheme.rationalTateMonodromy (RatFunc (realCyclotomicField N)) x A p
              (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N)) x (γ i)) v) :
                Fin 2 → ℚ_[p] ⊗[ℚ] realCyclotomicField N) =
            ((Monodromy.standardTriple ((1 : ℚ_[p]) ⊗ₜ[ℚ] tau N 1) i :
              Matrix (Fin 2) (Fin 2) (ℚ_[p] ⊗[ℚ] realCyclotomicField N)) *ᵥ b.repr v)

set_option maxHeartbeats 1000000 in
/-- The integral base triple is realized by one abelian scheme with real multiplication.
The basis is over the actual coefficient tensor algebra, and its local monodromy is the
standard triple through actual generators of the three geometric inertia groups.
We use [DarmonFibres, Section 3, Propositions 3.2 and 3.4].
The coefficient basis implements the covariant, determinant-one simultaneous
conjugacy convention for all three matrices. -/
theorem exists_darmon_abelianScheme (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ∃ D : Σ A : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField N))),
        𝓞 (realCyclotomicField N) →+* End A,
      let A := D.1
      let φ := D.2
      Function.Injective φ ∧ IsProper A.X.hom ∧
      SmoothOfRelativeDimension (Module.finrank ℚ (realCyclotomicField N)) A.X.hom ∧
      GeometricallyConnected A.X.hom ∧
      ∃ (hfinite : ∀ n : ℕ, 0 < n → IsFinite (n • 𝟙 A).hom.hom.hom.left)
        (hetale : ∀ n : ℕ, 0 < n → Etale (n • 𝟙 A).hom.hom.hom.left)
        (hsurjective : ∀ n : ℕ, 0 < n → Surjective (n • 𝟙 A).hom.hom.hom.left),
      HasStandardInertiaRealization N A φ hfinite hetale := by
  sorry

end HilbertModularity.Hypergeometric
