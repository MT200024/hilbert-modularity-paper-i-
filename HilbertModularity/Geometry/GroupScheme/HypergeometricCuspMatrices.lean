/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.StandardInertiaMatrices

/-! # Cusp matrices on the chosen coefficient-labelled Darmon local system

The same prescribed coefficient embedding is used in the native tensor factor
and the local system. This is the matrix specialization in
[TripathiGoswami, proof of RMgeneral, Step 2], using the realization supplied
by [DarmonFibres, Propositions 3.2 and 3.4].
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Representation

/-- An equivariant change of carrier preserves the matrix in the transported basis. -/
theorem Equiv.toMatrix_map_basis
    {R G V W : Type*} [CommRing R] [Monoid G]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {ρ' : Representation R G W}
    (e : ρ.Equiv ρ') (b : Module.Basis (Fin 2) R V) (g : G) :
    LinearMap.toMatrix (b.map e.toLinearEquiv) (b.map e.toLinearEquiv) (ρ' g) =
      LinearMap.toMatrix b b (ρ g) := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  ext v
  change e.toLinearEquiv.symm (ρ' g (e.toLinearEquiv v)) = ρ g v
  have h : e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) :=
    e.toIntertwiningMap.isIntertwining ρ ρ' g v
  rw [← h, LinearEquiv.symm_apply_apply]

end Representation

namespace HilbertModularity.Hypergeometric

open _root_.HilbertModularity.Cyclotomic Algebra.TensorProduct

/-- In one basis of the actual labelled local-system fibre, the chosen Darmon
inertia generators have the standard matrices specialized at the fixed label.
The statement retains their inertia conjugacy choices and asserts no density. -/
theorem darmonLabelledMonodromy_cusp_matrices
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [Algebra ℚ_[p] L] [Algebra ℚ L] [IsScalarTower ℚ ℚ_[p] L]
    (hL : ∀ a : realCyclotomicField N, ((minpoly ℚ a).map (algebraMap ℚ L)).Splits)
    (σ : realCyclotomicField N →ₐ[ℚ] L) :
    let F := GroupScheme.labelledTateLocalSystem (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p L (realCyclotomicField N)
      (darmonRealMultiplication N hN) hL σ
    let x := ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)
    ∃ (γ c : Fin 3 →
        (AlgebraicClosure (RatFunc (realCyclotomicField N)) ≃ₐ[RatFunc (realCyclotomicField N)]
          AlgebraicClosure (RatFunc (realCyclotomicField N))))
      (b : Module.Basis (Fin 2) L (F.obj (Scheme.etaleFiberPoint
        (RatFunc (realCyclotomicField N)) (ProjectiveLine.punctured (realCyclotomicField N)) x))),
      ((∀ i, (Subgroup.zpowers (γ i)).topologicalClosure =
        (![RatFunc.affineInertia (realCyclotomicField N) 0,
           RatFunc.affineInertia (realCyclotomicField N) 1,
           RatFunc.infinityInertia (realCyclotomicField N)] i).map (MulAut.conj (c i)).toMonoidHom) ∧
        ∃ ζ : ℕ → AlgebraicClosure (RatFunc (realCyclotomicField N)),
          ProjectiveLine.HasCommonCuspOrientation (realCyclotomicField N) γ ζ ∧
          ζ N + (ζ N)⁻¹ = algebraMap (realCyclotomicField N) _ (tau N 1)) ∧
      ∀ i, LinearMap.toMatrix b b
        (Scheme.fiberMonodromy (RatFunc (realCyclotomicField N))
          (ProjectiveLine.punctured (realCyclotomicField N)) F x
          (Scheme.galoisToEtaleFundamentalGroup (RatFunc (realCyclotomicField N)) x (γ i))) =
        (Monodromy.standardTriple (σ (tau N 1)) i : Matrix (Fin 2) (Fin 2) L) := by
  let V := TateModule.rational p
    (Additive (Scheme.geometricPointOver (RatFunc (realCyclotomicField N))
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) ⟶ (darmonFamily N hN).X))
  let : Module (ℚ_[p] ⊗[ℚ] realCyclotomicField N) V :=
    Module.compHom V (GroupScheme.geometricTensorTateAction (RatFunc (realCyclotomicField N))
      (darmonFamily N hN) p (realCyclotomicField N) (darmonRealMultiplication N hN)
      (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N))).toRingHom
  let : Algebra (ℚ_[p] ⊗[ℚ] realCyclotomicField N) L :=
    (coefficientTensorEmbedding ℚ ℚ_[p] (realCyclotomicField N) L σ).toAlgebra
  obtain ⟨γ, c, b, hc, hb⟩ := HasStandardInertiaRealization.specialization_matrices N
    (darmonFamily N hN) (darmonRealMultiplication N hN)
    (fun n hn => @darmonFamily_multiplication_isFinite N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (fun n hn => @darmonFamily_multiplication_etale N _ hN n ⟨Nat.ne_of_gt hn⟩)
    (darmonFamily_inertia_realization N hN) p L σ
  let e := GroupScheme.coefficientTateMonodromyLabelledEquiv
    (RatFunc (realCyclotomicField N)) (darmonFamily N hN)
    (ProjectiveLine.puncturedRationalPoint (realCyclotomicField N)) p
    (realCyclotomicField N) (darmonRealMultiplication N hN) L hL σ
    (ProjectiveLine.puncturedRationalPoint_galoisToEtaleFundamentalGroup_surjective
      (realCyclotomicField N))
  refine ⟨γ, c, b.map e.toLinearEquiv, hc, ?_⟩
  intro i
  rw [Representation.Equiv.toMatrix_map_basis]
  exact hb i

end HilbertModularity.Hypergeometric
