/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricTorsion
public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricRanks
public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicResidual
public import HilbertModularity.Geometry.GroupScheme.RealCyclotomicRank
public import HilbertModularity.Geometry.GroupScheme.HypergeometricResidual

/-! # Residual kernel of the explicit prime plus family

The rational point of [DarmonRigid, Theorem 2.6(2)] gives a fixed point in the
canonical-prime kernel of every nonsingular fibre of the same plus family.
The residual constituent deduction follows [TripathiGoswamiRevised,
Proposition `primeresidual`], with its rank and determinant inputs visible.
-/

public section
noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField

namespace AlgebraicGeometry.GroupScheme

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
  (A : CommGrp (Over (Spec (CommRingCat.of K))))
  (φ : 𝓞 (HilbertModularity.Cyclotomic.realCyclotomicField p) →+* End A)

include hp

/-- Total ramification sends a nonzero fixed rational `p`-torsion point to
a nonzero fixed point of the canonical-prime scheme kernel. -/
theorem exists_realPrimeKernel_fixed_of_pTorsion
    (x : Points K (AlgebraicClosure K) A.X)
    (hx : x ≠ 0) (hpx : p • x = 0)
    (hfix : ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • x = x) :
    ∃ v : Points K (AlgebraicClosure K)
      (CommGrp.pullbackKernel (φ (HilbertModularity.Cyclotomic.realPrimeGenerator p))).X,
      v ≠ 0 ∧ ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • v = v := by
  let R := 𝓞 (HilbertModularity.Cyclotomic.realCyclotomicField p)
  let a : R := HilbertModularity.Cyclotomic.realPrimeGenerator p
  let e := (p - 1) / 2
  let := pointsCoefficientModule K A R φ
  let : SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) R
      (Points K (AlgebraicClosure K) A.X) :=
    points_coefficient_galois_comm K A.X R
      (pointsCoefficientModule_realized K A R φ)
  have hmem : a ^ e ∈ (Ideal.span {a}) ^ e := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (by simp)
  have hdiv : (p : R) ∣ a ^ e := by
    rw [HilbertModularity.Cyclotomic.span_realPrimeGenerator_pow p (by omega)] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  obtain ⟨u, hu⟩ := hdiv
  have hkill : a ^ e • x = 0 := by
    calc
      a ^ e • x = (u * (p : R)) • x := by rw [hu, mul_comm]
      _ = u • ((p : R) • x) := mul_smul _ _ _
      _ = 0 := by rw [Nat.cast_smul_eq_nsmul, hpx, smul_zero]
  have auxiliary : ∀ n : ℕ, ∀ z : Points K (AlgebraicClosure K) A.X,
      z ≠ 0 →
      (∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • z = z) →
      a ^ n • z = 0 →
      ∃ y : Points K (AlgebraicClosure K) A.X,
        y ≠ 0 ∧ a • y = 0 ∧
          ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, g • y = y := by
    intro n
    induction n with
    | zero =>
        intro z hz _ hzero
        simp only [pow_zero, one_smul] at hzero
        exact (hz hzero).elim
    | succ n ih =>
        intro z hz hzfix hzero
        by_cases haz : a • z = 0
        · exact ⟨z, hz, haz, hzfix⟩
        · apply ih (a • z) haz
          · intro g
            calc
              g • (a • z) = a • (g • z) := smul_comm g a z
              _ = a • z := by rw [hzfix g]
          · simpa only [pow_succ, mul_smul] using hzero
  obtain ⟨y, hy, hay, hyfix⟩ := auxiliary e x hx hfix hkill
  let q : coefficientTorsion K A.X R a := ⟨y, hay⟩
  let E := coefficientKernelPointsEquiv K A R φ a
  let v := E.symm q
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hy
    have hq : q = 0 := by
      calc
        q = E v := (E.apply_symm_apply q).symm
        _ = E 0 := congrArg E hv
        _ = 0 := map_zero E
    exact congrArg Subtype.val hq
  · intro g
    apply E.injective
    apply Subtype.ext
    change (E (g • v) : Points K (AlgebraicClosure K) A.X) =
      (E v : Points K (AlgebraicClosure K) A.X)
    calc
      (E (g • v) : Points K (AlgebraicClosure K) A.X) =
          g • (E v : Points K (AlgebraicClosure K) A.X) :=
        coefficientKernelPointsEquiv_galois K A R φ a g v
      _ = (E v : Points K (AlgebraicClosure K) A.X) := by
        simpa only [v, E.apply_symm_apply] using hyfix g

end AlgebraicGeometry.GroupScheme

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
  (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

local notation "Kₚ" => realCyclotomicField p
local notation "Rₚ" => 𝓞 Kₚ
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "kₚ" => Rₚ ⧸ Pₚ

/-- The actual nonsingular fibre of the selected plus family. -/
@[expose] def primePlusFiber : CommGrp (Over (Spec (CommRingCat.of Kₚ))) :=
  parameterFiber Kₚ (primePlusFamily p hp) ξ

/-- The fibre used by the residual representation is the Jacobian of the
displayed pointed plus curve. Its RM action below is on this same group scheme. -/
def primePlusFiberJacobian : GroupScheme.PlusCurveJacobian Kₚ p
    (primePlusData p hp).p_odd ξ.val (primePlusFiber p hp ξ) :=
  primePlusRationalFiberJacobian p hp ξ

instance primePlusFiber_multiplication_isFinite (n : ℕ) [NeZero n] :
    IsFinite (multiplicationMap Kₚ (primePlusFiber p hp ξ).X n).left :=
  fiber_multiplication_isFinite Kₚ (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint Kₚ ξ) n

instance primePlusFiber_multiplication_etale (n : ℕ) [NeZero n] :
    Etale (multiplicationMap Kₚ (primePlusFiber p hp ξ).X n).left :=
  fiber_multiplication_etale Kₚ (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint Kₚ ξ) n

instance primePlusFiber_multiplication_surjective (n : ℕ) [NeZero n] :
    Surjective (multiplicationMap Kₚ (primePlusFiber p hp ξ).X n).left :=
  fiber_multiplication_surjective Kₚ (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint Kₚ ξ) n

/-- Its integral RM action is obtained from the fixed action on the family. -/
@[expose] def primePlusFiberRealMultiplication : Rₚ →+* End (primePlusFiber p hp ξ) :=
  (fiberEndomorphismMap Kₚ (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint Kₚ ξ)).comp
      (primePlusRealMultiplication p hp)

/-- The canonical-prime kernel belongs to the same fibre and RM action. -/
@[expose] def primePlusKernel : CommGrp (Over (Spec (CommRingCat.of Kₚ))) :=
  CommGrp.pullbackKernel (primePlusFiberRealMultiplication p hp ξ (realPrimeGenerator p))

/-- Residue coefficients on the actual canonical-prime kernel of this fibre. -/
@[expose, instance_reducible] def primePlusKernelModule :
    Module kₚ (Points Kₚ (AlgebraicClosure Kₚ) (primePlusKernel p hp ξ).X) :=
  coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
    (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)

/-- The Galois representation on the same plus-family kernel points. -/
@[expose] def primePlusKernelRepresentation :
    letI := primePlusKernelModule p hp ξ
    Representation kₚ (AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ)
      (Points Kₚ (AlgebraicClosure Kₚ) (primePlusKernel p hp ξ).X) :=
  coefficientKernelRepresentation Kₚ (primePlusFiber p hp ξ) Rₚ
    (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)

@[simp]
theorem primePlusKernelRepresentation_apply
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ)
    (x : Points Kₚ (AlgebraicClosure Kₚ) (primePlusKernel p hp ξ).X) :
    letI := primePlusKernelModule p hp ξ
    primePlusKernelRepresentation p hp ξ g x = g • x :=
  coefficientKernelRepresentation_apply Kₚ (primePlusFiber p hp ξ) Rₚ
    (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p) g x

/-- The selected-fibre representation has the determinant of its defining
coefficient-kernel action on the same kernel points. -/
theorem det_primePlusKernelRepresentation :
    letI := primePlusKernelModule p hp ξ
    ∀ g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ,
      LinearMap.det (primePlusKernelRepresentation p hp ξ g) =
        (letI := coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
          (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
        LinearMap.det (coefficientKernelRepresentation Kₚ
          (primePlusFiber p hp ξ) Rₚ
          (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p) g)) := by
  intro g
  rfl

include hp in
/-- The canonical-prime kernel of every nonsingular plus-family fibre has rank two. -/
theorem finrank_primePlusKernel :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := primePlusKernelModule p hp ξ
    Module.finrank kₚ (Points Kₚ (AlgebraicClosure Kₚ)
      (primePlusKernel p hp ξ).X) = 2 := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := primePlusKernelModule p hp ξ
  have hT : Module.finrank ℚ_[p]
      (rationalTate Kₚ (primePlusFiber p hp ξ).X p) = ((p - 1) / 2) * 2 := by
    unfold primePlusFiber parameterFiber
    rw [← finrank_realCyclotomicField p (by omega)]
    with_reducible
      exact finrank_primePlusRationalTate_at p hp Kₚ
        (ProjectiveLine.puncturedPoint Kₚ ξ)
  exact finrank_realPrimeKernel_of_rational_rank Kₚ (primePlusFiber p hp ξ)
    p (by omega) (primePlusFiberRealMultiplication p hp ξ) 2 hT

/-- The source-backed rational point yields a nonzero Galois-fixed point of
the actual canonical-prime kernel on every nonsingular plus-family fibre. -/
theorem exists_primePlusKernel_fixed :
    ∃ v : Points Kₚ (AlgebraicClosure Kₚ) (primePlusKernel p hp ξ).X,
      v ≠ 0 ∧ ∀ g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ,
        g • v = v := by
  exact exists_realPrimeKernel_fixed_of_pTorsion Kₚ p (by omega)
    (primePlusFiber p hp ξ) (primePlusFiberRealMultiplication p hp ξ)
    (primePlusGeometricFiberPoint p hp ξ)
    (primePlusGeometricFiberPoint_ne_zero p hp ξ)
    (primePlusGeometricFiberPoint_torsion p hp ξ)
    (primePlusGeometricFiberPoint_fixed p hp ξ)

/-- Residual constituents of the explicit plus-family kernel. The actual
rank-two property is proved from its rational Tate rank; the exact residual
determinant of this same fibre remains an explicit premise. -/
theorem exists_primePlusKernel_factors
    (hdet : letI := realPrimeGenerator_isMaximal p (by omega)
      letI := Ideal.Quotient.field Pₚ
      letI := coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
        (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
      ∀ g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ,
        realPrimeResidueEquiv p (by omega)
          (LinearMap.det (coefficientKernelRepresentation Kₚ
            (primePlusFiber p hp ξ) Rₚ
              (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p) g)) =
            (Field.cyclotomicCharacter Kₚ p g : ℤ_[p]).toZMod) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    letI := coefficientKernelModule Kₚ (primePlusFiber p hp ξ) Rₚ
      (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
    let ρ := coefficientKernelRepresentation Kₚ (primePlusFiber p hp ξ) Rₚ
      (primePlusFiberRealMultiplication p hp ξ) (realPrimeGenerator p)
    ∃ S : Subrepresentation ρ,
      Module.finrank kₚ S.toSubmodule = 1 ∧
      Module.finrank kₚ ((Points Kₚ (AlgebraicClosure Kₚ)
        (primePlusKernel p hp ξ).X) ⧸ S.toSubmodule) = 1 ∧
      S.toRepresentation.IsIrreducible ∧
      (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule).IsIrreducible ∧
      Nonempty ((S.toRepresentation.prod
        (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) →* kₚˣ)).prod
              (Representation.ofCharacter
                (realPrimeResidualCyclotomicCharacter Kₚ p (by omega))))) := by
  obtain ⟨v, hv, hfix⟩ := exists_primePlusKernel_fixed p hp ξ
  exact exists_realPrimeKernel_factors Kₚ p (by omega)
    (primePlusFiber p hp ξ) (primePlusFiberRealMultiplication p hp ξ)
    v hv hfix (finrank_primePlusKernel p hp ξ) hdet

end HilbertModularity.Hypergeometric
