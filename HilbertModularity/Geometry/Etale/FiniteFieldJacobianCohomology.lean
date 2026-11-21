/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.Etale.FiniteFieldGenusTwoFrobenius
public import HilbertModularity.Geometry.GroupScheme.PlusCurveJacobian

/-! # First cohomology of a pointed curve and its actual Jacobian

The standard Abel–Jacobi and Kummer comparison is recorded on the existing
geometric pro-étale cohomology and covariant rational Tate module. The
Galois action is contragredient on the latter; no Tate twist is inserted.
-/

public noncomputable section

open CategoryTheory Limits Polynomial
open AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.Hyperelliptic

/-- [MilneJacobian2021, Corollary 9.6, printed p.32] identifies the first
étale cohomology of a pointed smooth curve with that of its Jacobian by the
actual Abel–Jacobi map. [MilneAV, Chapter I, Theorem 12.1(a), printed p.55]
identifies the latter with the dual of the covariant Tate module. The
comparison is Galois equivariant and has no Tate twist; for geometric
Frobenius this agrees with [src_milne_lec, Remark 29.11, printed p.168].
[proetale2015, Corollary 5.1.5, Lemma 6.8.2(1), Proposition 6.8.4(1)]
passes from the classical continuous ℓ-adic system to the actual pro-étale
cohomology carrier used here. This standard composite interface asserts no
point count, RM decomposition, character value or numeric polynomial. -/
theorem geometricH1_equiv_dualTate_of_pointedJacobian
    (k : Type*) [Field k] [Fintype k]
    (f : k[X]) (hdeg : f.natDegree = 2 * 3)
    (hmonic : f.Monic) (hsep : f.Separable) (h2 : (2 : k) ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk (toSpec f 3 hdeg))
    (hJ : PointedCurveJacobian k (Over.mk (toSpec f 3 hdeg)) b J) :
    Nonempty ((Scheme.rationalEllAdicCohomologyGaloisRepresentation
      k (toSpec f 3 hdeg) ℓ 1).Equiv (tateRepresentation k J.X ℓ).dual) := by
  sorry

private theorem toMatrix_map_basis_four
    {R G V W : Type*} [CommRing R] [Monoid G]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {ρ' : Representation R G W}
    (e : ρ.Equiv ρ') (b : Module.Basis (Fin 4) R V) (g : G) :
    LinearMap.toMatrix (b.map e.toLinearEquiv) (b.map e.toLinearEquiv) (ρ' g) =
      LinearMap.toMatrix b b (ρ g) := by
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  ext v
  change e.toLinearEquiv.symm (ρ' g (e.toLinearEquiv v)) = ρ g v
  have h : e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) :=
    e.toIntertwiningMap.isIntertwining ρ ρ' g v
  rw [← h, LinearEquiv.symm_apply_apply]

/-- The same general two-count polynomial acts on the dual Tate module of
the actual pointed Jacobian. This is deduced from the two named standard
cohomological comparisons; it introduces no third source admission. -/
theorem genusTwoPointedJacobian_geometricFrobeniusPolynomial
    (k : Type*) [Field k] [Fintype k]
    (f : k[X]) (hdeg : f.natDegree = 2 * 3)
    {k₂ : Type*} [Field k₂] [Fintype k₂] [Algebra k k₂]
    (hmonic : f.Monic) (hsep : f.Separable) (h2 : (2 : k) ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (hdeg₂ : (f.map (algebraMap k k₂)).natDegree = 2 * 3)
    (hcard₂ : Fintype.card k₂ = (Fintype.card k) ^ 2)
    (J : CommGrp (Over (Spec (CommRingCat.of k))))
    (b₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk (toSpec f 3 hdeg))
    (hJ : PointedCurveJacobian k (Over.mk (toSpec f 3 hdeg)) b₀ J) :
    ∃ b : Module.Basis (Fin 4) ℚ_[ℓ] (Module.Dual ℚ_[ℓ] (rationalTate k J.X ℓ)),
      let q : ℚ_[ℓ] := Fintype.card k
      let s₁ : ℚ_[ℓ] := q + 1 - Nat.card (Scheme.RationalPoint (toSpec f 3 hdeg))
      let s₂ : ℚ_[ℓ] := q ^ 2 + 1 -
        Nat.card (Scheme.RationalPoint (toSpec (f.map (algebraMap k k₂)) 3 hdeg₂))
      (LinearMap.toMatrix b b
        ((tateRepresentation k J.X ℓ).dual (finiteFieldGeometricFrobenius k))).charpolyRev =
        1 - C s₁ * X + C ((s₁ ^ 2 - s₂) / 2) * X ^ 2 -
          C (q * s₁) * X ^ 3 + C (q ^ 2) * X ^ 4 := by
  obtain ⟨b, hb⟩ := genusTwoGeometricFrobeniusPolynomial k f hdeg ℓ
    hmonic hsep h2 hℓ hdeg₂ hcard₂
  obtain ⟨e⟩ := geometricH1_equiv_dualTate_of_pointedJacobian
    k f hdeg hmonic hsep h2 ℓ hℓ J b₀ hJ
  refine ⟨b.map e.toLinearEquiv, ?_⟩
  rw [toMatrix_map_basis_four e b (finiteFieldGeometricFrobenius k)]
  rw [genusTwoGeometricFrobeniusAction_eq] at hb
  exact hb

end AlgebraicGeometry.Hyperelliptic
