/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.ModularityHypotheses
public import HilbertModularity.Geometry.GroupScheme.HypergeometricDeterminant
public import HilbertModularity.Geometry.GroupScheme.HypergeometricPrimeTorsion
public import HilbertModularity.NumberTheory.HilbertModularForms.SkinnerWilesInput
public import HilbertModularity.RepresentationTheory.ScalarConjugationInvariants
import HilbertModularity.Geometry.GroupScheme.HypergeometricResidual

/-! # Residual ratio in the prime-level lifting checklist

The chosen prime-kernel character supplies the odd residual ratio required by
[SkinnerWiles, §4.5, Theorem A] after the same integral lattice is identified.
-/

public section
noncomputable section

open scoped NumberField Pointwise ValuativeRel
open scoped IsMulCommutative
open ValuativeRel
open NumberField
open AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open IsDedekindDomain

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic
open HilbertModularity.HilbertModularForms

attribute [local instance] realFieldAlgebra

/-- A fixed nonzero vector in a two-dimensional matrix action makes one an
eigenvalue, so its trace is one plus its determinant. -/
theorem matrix_trace_eq_one_add_det_of_fixedVector
    {k : Type*} [Field k] (M : Matrix (Fin 2) (Fin 2) k)
    (v : Fin 2 → k) (hv : v ≠ 0) (hfix : M.mulVec v = v) :
    M.trace = 1 + M.det := by
  have hzero : (1 - M).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]
  have hdet : (1 - M).det = 1 - M.trace + M.det := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply]
    ring
  rw [hdet] at hzero
  linear_combination -hzero

/-- A fixed vector after reduction determines the reduced trace of a
rank-two integral endomorphism from its determinant. -/
theorem linearMap_trace_eq_one_add_det_of_fixed_reduction
    {R k : Type*} [CommRing R] [Field k] (q : R →+* k)
    (f : (Fin 2 → R) →ₗ[R] (Fin 2 → R))
    (v : Fin 2 → k) (hv : v ≠ 0)
    (hfix : ((LinearMap.toMatrix' f).map q).mulVec v = v) :
    q (LinearMap.trace R (Fin 2 → R) f) = 1 + q (LinearMap.det f) := by
  let M := LinearMap.toMatrix' f
  have ht : q (LinearMap.trace R (Fin 2 → R) f) = (M.map q).trace := by
    rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin 2)),
      LinearMap.toMatrix_eq_toMatrix', AddMonoidHom.map_trace]
  have hd : q (LinearMap.det f) = (M.map q).det := by
    rw [← LinearMap.det_toMatrix' f]
    change q M.det = (M.map q).det
    rw [← RingHom.mapMatrix_apply]
    exact q.map_det M
  rw [ht, hd]
  exact matrix_trace_eq_one_add_det_of_fixedVector (M.map q) v hv hfix

/-- Build the residual semisimplification data of a rank-two integral
representation from a fixed line and its determinant. The characters are
ordered with the determinant character first, as required when the ordinary
quotient has trivial residual character. See
[TripathiGoswamiRevised, Proposition `primeresidual`]. -/
noncomputable def skinnerWilesResidualData_of_fixedVector
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (integralAction : Representation (𝒪[E]) (AbsoluteGalois F) (Fin 2 → 𝒪[E]))
    (integral_spec : ∀ g i j,
      ((integralAction g (Pi.single j 1) i : 𝒪[E]) : E) =
        ρ g (Pi.single j 1) i)
    (ε : AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (v : Fin 2 → 𝒪[E] ⧸ 𝓂[E]) (hv : v ≠ 0)
    (hfix : ∀ g : AbsoluteGalois F,
      ((LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec v = v)
    (hdet : ∀ g : AbsoluteGalois F,
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E])) :
    HilbertModularForms.SkinnerWilesResidualData ρ := by
  let := Ideal.Quotient.field (𝓂[E])
  exact
    { integralAction := integralAction
      integral_spec := integral_spec
      chi₁ := ε
      chi₂ := 1
      residual_trace := by
        intro g
        rw [linearMap_trace_eq_one_add_det_of_fixed_reduction
          (Ideal.Quotient.mk (𝓂[E])) (integralAction g) v hv (hfix g), hdet g]
        simp [add_comm]
      residual_det := by
        intro g
        simpa using hdet g }

/-- The fixed-vector construction orders the trivial residual character in
the second position, matching the ordinary quotient convention. -/
theorem skinnerWilesResidualData_of_fixedVector_chi₂_eq_one
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (integralAction : Representation (𝒪[E])
      (AbsoluteGalois F) (Fin 2 → 𝒪[E]))
    (integral_spec : ∀ g i j,
      ((integralAction g (Pi.single j 1) i : 𝒪[E]) : E) =
        ρ g (Pi.single j 1) i)
    (ε : AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (v : Fin 2 → 𝒪[E] ⧸ 𝓂[E]) (hv : v ≠ 0)
    (hfix : ∀ g : AbsoluteGalois F,
      ((LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec v = v)
    (hdet : ∀ g : AbsoluteGalois F,
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E])) :
    (skinnerWilesResidualData_of_fixedVector ρ integralAction integral_spec
      ε v hv hfix hdet).chi₂ = 1 := by
  unfold skinnerWilesResidualData_of_fixedVector
  rfl

/-- A fixed vector of the reduction of the actual Skinner--Wiles lattice
determines its reduced trace from its reduced determinant. The fixed-vector
premise uses the same integral action as the residual semisimplification data.
See [TripathiGoswamiRevised, Lemma `RMtorsion` and Proposition
`SW-checklist`]. -/
theorem residualTrace_eq_one_add_det_of_fixedVector
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (v : Fin 2 → 𝒪[E] ⧸ 𝓂[E]) (hv : v ≠ 0)
    (hfix : ∀ g : AbsoluteGalois F,
      ((LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec v = v)
    (g : AbsoluteGalois F) :
    Ideal.Quotient.mk (𝓂[E])
      (LinearMap.trace (𝒪[E]) (Fin 2 → 𝒪[E]) (D.integralAction g)) =
        1 + Ideal.Quotient.mk (𝓂[E])
          (LinearMap.det (D.integralAction g)) := by
  let := Ideal.Quotient.field (𝓂[E])
  let q : 𝒪[E] →+* (𝒪[E] ⧸ 𝓂[E]) := Ideal.Quotient.mk (𝓂[E])
  let f := D.integralAction g
  change q (LinearMap.trace (𝒪[E]) (Fin 2 → 𝒪[E]) f) =
    1 + q (LinearMap.det f)
  apply linearMap_trace_eq_one_add_det_of_fixed_reduction q f v hv
  exact hfix g

/-- Trace and determinant on one integral lattice determine its residual
character ratio when the proposed determinant character is quadratic.  The
trace and determinant equalities refer to the actual integral action stored
in `D`; in applications they come from a fixed torsion line and the exact
Tate determinant. See [TripathiGoswamiRevised, Proposition
`SW-checklist`]. -/
theorem residualRatio_eq_quadratic_of_integral_trace_det
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (ε : AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (hquad : ∀ g, ε g = 1 ∨ ε g = -1)
    (htrace : ∀ g,
      Ideal.Quotient.mk (𝓂[E])
        (LinearMap.trace (𝒪[E]) (Fin 2 → 𝒪[E]) (D.integralAction g)) =
          1 + (ε g : 𝒪[E] ⧸ 𝓂[E]))
    (hdet : ∀ g,
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E])) :
    HilbertModularForms.residualRatio D = ε := by
  apply MonoidHom.ext
  intro g
  let a := D.chi₁ g
  let b := D.chi₂ g
  let u := ε g
  have ht : (a : 𝒪[E] ⧸ 𝓂[E]) + (b : 𝒪[E] ⧸ 𝓂[E]) =
      1 + (u : 𝒪[E] ⧸ 𝓂[E]) := by
    exact (D.residual_trace g).symm.trans (htrace g)
  have hd : (a : 𝒪[E] ⧸ 𝓂[E]) * (b : 𝒪[E] ⧸ 𝓂[E]) =
      (u : 𝒪[E] ⧸ 𝓂[E]) := by
    exact (D.residual_det g).symm.trans (hdet g)
  have hprod : ((a : 𝒪[E] ⧸ 𝓂[E]) - 1) *
      ((a : 𝒪[E] ⧸ 𝓂[E]) - (u : 𝒪[E] ⧸ 𝓂[E])) = 0 := by
    calc
      _ = (a : 𝒪[E] ⧸ 𝓂[E]) *
            ((a : 𝒪[E] ⧸ 𝓂[E]) + (b : 𝒪[E] ⧸ 𝓂[E]) -
              (1 + (u : 𝒪[E] ⧸ 𝓂[E]))) -
            ((a : 𝒪[E] ⧸ 𝓂[E]) * (b : 𝒪[E] ⧸ 𝓂[E]) -
              (u : 𝒪[E] ⧸ 𝓂[E])) := by ring
      _ = 0 := by rw [ht, hd]; ring
  have hchoices : a = 1 ∨ a = u := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (Units.ext (sub_eq_zero.mp h))
    · exact Or.inr (Units.ext (sub_eq_zero.mp h))
  have hdUnits : a * b = u := Units.ext (by simpa only [Units.val_mul] using hd)
  have huinv : u⁻¹ = u := by
    rcases hquad g with h | h
    · simp [u, h]
    · simp [u, h]
  rw [HilbertModularForms.residualRatio_apply]
  change a * b⁻¹ = u
  rcases hchoices with ha | ha
  · have hb : b = u := by simpa [ha] using hdUnits
    simp [ha, hb, huinv]
  · have hb : b = 1 := by
      apply mul_left_cancel (a := u)
      simpa [ha] using hdUnits
    simp [ha, hb]

/-- A fixed vector in the reduced integral lattice and its quadratic
determinant identify the Skinner--Wiles residual ratio on that same lattice.
See [TripathiGoswamiRevised, Proposition `SW-checklist`]. -/
theorem residualRatio_eq_quadratic_of_fixed_reduction
    {F : Type*} [Field F] [NumberField F]
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois F) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (ε : AbsoluteGalois F →* (𝒪[E] ⧸ 𝓂[E])ˣ)
    (hquad : ∀ g, ε g = 1 ∨ ε g = -1)
    (v : Fin 2 → 𝒪[E] ⧸ 𝓂[E]) (hv : v ≠ 0)
    (hfix : ∀ g : AbsoluteGalois F,
      ((LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec v = v)
    (hdet : ∀ g,
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E])) :
    HilbertModularForms.residualRatio D = ε := by
  apply residualRatio_eq_quadratic_of_integral_trace_det ρ D ε hquad
  · intro g
    rw [residualTrace_eq_one_add_det_of_fixedVector ρ D v hv hfix g, hdet g]
  · exact hdet

/-- A nonzero fixed point of the chosen Darmon prime kernel determines the
residual ratio on a specified Skinner--Wiles lattice.  The additive equivalence
identifies the two residual actions; the separate determinant comparison
identifies the chosen kernel's determinant with the reduction of that same
integral lattice.  These comparisons remain arithmetic inputs.  See
[TripathiGoswamiRevised, Lemma `RMtorsion` and Proposition `SW-checklist`]. -/
theorem residualRatio_eq_chosenPrime_of_fixedKernelPoint
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (j : Points (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p))
        (darmonPrimeKernel p hp ξ).X ≃+ (Fin 2 → 𝒪[E] ⧸ 𝓂[E]))
    (hequiv : ∀ (g : AbsoluteGalois (realCyclotomicField p)) v,
      j (g • v) =
        ((LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v))
    (v : Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p))
      (darmonPrimeKernel p hp ξ).X)
    (hv : v ≠ 0)
    (hfix : ∀ g : AbsoluteGalois (realCyclotomicField p), g • v = v)
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hdetCompare : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeKernelModule p hp ξ
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        κ (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g))) :
    HilbertModularForms.residualRatio D =
      (Units.map κ.toMonoidHom).comp
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  let := darmonPrimeKernelModule p hp ξ
  have hkernelDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g) =
        (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega) g :
            𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
    intro g
    have h := congrArg (fun f => f g)
      (darmonPrimeResidualDeterminantCharacter_of_integralTate p hp ξ E hTateDet)
    exact congrArg Units.val h
  let ε := (Units.map κ.toMonoidHom).comp
    (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
      (realCyclotomicField p) p (by omega))
  have hquad : ∀ g, ε g = 1 ∨ ε g = -1 := by
    intro g
    rcases realPrimeResidualCharacter_eq_one_or_neg_one p hp g with h | h
    · left
      simp [ε, h]
    · right
      simp [ε, h]
  let w := j v
  have hw : w ≠ 0 := by
    intro h
    apply hv
    apply j.injective
    simpa [w] using h
  have hwfix : ∀ g : AbsoluteGalois (realCyclotomicField p),
      ((LinearMap.toMatrix' (D.integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec w = w := by
    intro g
    calc
      _ = j (g • v) := (hequiv g v).symm
      _ = w := by rw [hfix g]
  have hdet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E]) := by
    intro g
    calc
      _ = κ (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g)) :=
        hdetCompare g
      _ = κ (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega) g :
            𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
        rw [hkernelDet g]
      _ = (ε g : 𝒪[E] ⧸ 𝓂[E]) := (rfl)
  exact residualRatio_eq_quadratic_of_fixed_reduction ρ D ε hquad w hw hwfix hdet

/-- A rational point of order `p` on the same chosen Darmon fibre supplies
the fixed kernel point needed to identify the residual ratio. The comparison
with the Skinner--Wiles integral lattice and the exact Tate determinant remain
explicit inputs. See [TripathiGoswamiRevised, Lemma `RMtorsion` and
Proposition `SW-checklist`]. -/
theorem residualRatio_eq_chosenPrime_of_fiber_pTorsion
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (j : Points (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p))
        (darmonPrimeKernel p hp ξ).X ≃+ (Fin 2 → 𝒪[E] ⧸ 𝓂[E]))
    (hequiv : ∀ (g : AbsoluteGalois (realCyclotomicField p)) v,
      j (g • v) =
        ((LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v))
    (x : Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p))
      (darmonPrimeFiber p hp ξ).X)
    (hx : x ≠ 0) (hpx : p • x = 0)
    (hfix : ∀ g : AbsoluteGalois (realCyclotomicField p), g • x = x)
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hdetCompare : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeKernelModule p hp ξ
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        κ (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g))) :
    HilbertModularForms.residualRatio D =
      (Units.map κ.toMonoidHom).comp
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega)) := by
  obtain ⟨v, hv, hvfix⟩ :=
    exists_darmonPrimeKernel_fixed_of_fiber_pTorsion p hp ξ x hx hpx hfix
  exact residualRatio_eq_chosenPrime_of_fixedKernelPoint
    p hp ξ ρ D κ j hequiv v hv hvfix hTateDet hdetCompare

/-- Construct the residual semisimplification data on the chosen integral
lattice directly from a rational `p`-torsion point on the same Darmon fibre.
The action and determinant comparisons specify the actual Skinner--Wiles
lattice; its two residual characters are then consequences, not supplied
semisimplification data. See [TripathiGoswamiRevised, Lemma `RMtorsion`
and Proposition `primeresidual`]. -/
noncomputable def skinnerWilesResidualData_of_fiber_pTorsion
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    {E : Type*} [Field E] [ValuativeRel E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (integralAction : Representation (𝒪[E])
      (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → 𝒪[E]))
    (integral_spec : ∀ g i j,
      ((integralAction g (Pi.single j 1) i : 𝒪[E]) : E) =
        ρ g (Pi.single j 1) i)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (j : Points (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p))
        (darmonPrimeKernel p hp ξ).X ≃+ (Fin 2 → 𝒪[E] ⧸ 𝓂[E]))
    (hequiv : ∀ (g : AbsoluteGalois (realCyclotomicField p)) v,
      j (g • v) =
        ((LinearMap.toMatrix' (integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v))
    (x : Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p))
      (darmonPrimeFiber p hp ξ).X)
    (hx : x ≠ 0) (hpx : p • x = 0)
    (hfix : ∀ g : AbsoluteGalois (realCyclotomicField p), g • x = x)
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hdetCompare : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeKernelModule p hp ξ
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g)) =
        κ (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g))) :
    HilbertModularForms.SkinnerWilesResidualData ρ := by
  let := darmonPrimeKernelModule p hp ξ
  let fixedPoint :=
    exists_darmonPrimeKernel_fixed_of_fiber_pTorsion p hp ξ x hx hpx hfix
  let v := Classical.choose fixedPoint
  have hv := (Classical.choose_spec fixedPoint).1
  have hvfix := (Classical.choose_spec fixedPoint).2
  have hkernelDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g) =
        (realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega) g :
            𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
    intro g
    have h := congrArg (fun f => f g)
      (darmonPrimeResidualDeterminantCharacter_of_integralTate p hp ξ E hTateDet)
    exact congrArg Units.val h
  let ε := (Units.map κ.toMonoidHom).comp
    (realPrimeResidualCyclotomicCharacter
      (realCyclotomicField p) p (by omega))
  have hw : j v ≠ 0 := by
    intro h
    apply hv
    apply j.injective
    simpa using h
  have hwfix : ∀ g : AbsoluteGalois (realCyclotomicField p),
      ((LinearMap.toMatrix' (integralAction g)).map
        (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v) = j v := by
    intro g
    calc
      _ = j (g • v) := (hequiv g v).symm
      _ = j v := by rw [hvfix g]
  have hdet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (integralAction g)) =
        (ε g : 𝒪[E] ⧸ 𝓂[E]) := by
    intro g
    calc
      _ = κ (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g)) :=
        hdetCompare g
      _ = κ (realPrimeResidualCyclotomicCharacter
          (realCyclotomicField p) p (by omega) g :
            𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
        rw [hkernelDet g]
      _ = (ε g : 𝒪[E] ⧸ 𝓂[E]) := (rfl)
  exact skinnerWilesResidualData_of_fixedVector
    ρ integralAction integral_spec ε (j v) hw hwfix hdet

/-- An isomorphism of residue fields detects the kernel of the residual
character ratio. The actual character comparison remains an explicit
same-lattice premise. -/
theorem residualRatio_eq_one_iff_chosenCharacter
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g))
    (g : AbsoluteGalois (realCyclotomicField p)) :
    HilbertModularForms.residualRatio D g = 1 ↔
      AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega) g = 1 := by
  rw [hchar g]
  constructor
  · intro h
    apply Units.ext
    apply κ.injective
    simpa using congrArg Units.val h
  · intro h
    simp [h]

/-- On the fixed cyclotomic closure, the kernel of the residual character
fixes exactly the cyclotomic field. -/
theorem residualCharacter_eq_one_iff_fix_cyclotomic
    (p : ℕ) [Fact p.Prime]
    (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) :
    residualCharacter p g = 1 ↔
      ∀ x : cyclotomicField p, g (x : Qbar) = (x : Qbar) := by
  constructor
  · intro h x
    have hx : (x : Qbar) ∈
        (IntermediateField.fixedField (residualCharacter p).ker).restrictScalars ℚ := by
      rw [fixedField_ker_residualCharacter p]
      exact x.property
    exact (IntermediateField.mem_fixedField_iff _ _).mp hx g
      (show g ∈ (residualCharacter p).ker from h)
  · intro h
    change (zeta_isPrimitiveRoot p).autToPow (realCyclotomicField p) g = 1
    rw [(zeta_isPrimitiveRoot p).autToPow_eq_one_iff]
    exact h ⟨zeta p, zeta_mem p⟩

/-- The explicit same-lattice comparison identifies the kernel of the
residual ratio with the fixed-closure cyclotomic character kernel. -/
theorem residualRatio_eq_one_iff_fixedClosureCharacter
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g))
    (g : AbsoluteGalois (realCyclotomicField p))
    (g' : Qbar ≃ₐ[realCyclotomicField p] Qbar)
    (hg : realCyclotomicGaloisEquiv p g' = g) :
    HilbertModularForms.residualRatio D g = 1 ↔
      residualCharacter p g' = 1 := by
  have ht := realPrimeResidualCharacter_transport p hp g'
  have hg' : (((realCyclotomicClosureEquiv p).trans g').trans
      (realCyclotomicClosureEquiv p).symm) = g := by
    simpa only [realCyclotomicGaloisEquiv_apply] using hg
  have ht' : realPrimeResidueEquiv p (by omega)
      (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega) g :
          𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) =
        (residualCharacter p g' : ZMod p) := by
    simpa only [hg'] using ht
  rw [residualRatio_eq_one_iff_chosenCharacter p hp ρ D κ hchar g]
  constructor
  · intro h
    apply Units.ext
    rw [← ht', h]
    simp
  · intro h
    apply Units.ext
    apply (realPrimeResidueEquiv p (by omega)).injective
    rw [ht', h]
    simp

/-- The cyclotomic extension embedded in the algebraic closure chosen for
the real cyclotomic base. -/
def cyclotomicFieldInRealClosure (p : ℕ) [Fact p.Prime] :
    cyclotomicField p →ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p) := by
  letI : IsScalarTower (realCyclotomicField p) (cyclotomicField p) Qbar :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact (realCyclotomicClosureEquiv p).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom (realCyclotomicField p) (cyclotomicField p) Qbar)

/-- The embedded cyclotomic extension has the prescribed image under the
chosen closure equivalence. -/
theorem realCyclotomicClosureEquiv_cyclotomicFieldInRealClosure
    (p : ℕ) [Fact p.Prime] (x : cyclotomicField p) :
    realCyclotomicClosureEquiv p (cyclotomicFieldInRealClosure p x) = (x : Qbar) := by
  simp [cyclotomicFieldInRealClosure]

/-- Conjugation by the closure equivalence preserves the assertion that an
automorphism fixes every element of the cyclotomic extension. -/
theorem fixes_cyclotomic_iff_fixes_realClosure
    (p : ℕ) [Fact p.Prime]
    (g' : Qbar ≃ₐ[realCyclotomicField p] Qbar) :
    (∀ x : cyclotomicField p, g' (x : Qbar) = (x : Qbar)) ↔
      ∀ x : cyclotomicField p,
        (realCyclotomicGaloisEquiv p g') (cyclotomicFieldInRealClosure p x) =
          cyclotomicFieldInRealClosure p x := by
  let e := realCyclotomicClosureEquiv p
  constructor
  · intro h x
    apply e.injective
    calc
      e ((realCyclotomicGaloisEquiv p g') (cyclotomicFieldInRealClosure p x)) =
          g' (e (cyclotomicFieldInRealClosure p x)) := by
            simp [realCyclotomicGaloisEquiv_apply, e]
      _ = g' (x : Qbar) := by rw [realCyclotomicClosureEquiv_cyclotomicFieldInRealClosure]
      _ = (x : Qbar) := h x
      _ = e (cyclotomicFieldInRealClosure p x) :=
        (realCyclotomicClosureEquiv_cyclotomicFieldInRealClosure p x).symm
  · intro h x
    calc
      g' (x : Qbar) = g' (e (cyclotomicFieldInRealClosure p x)) := by
        rw [realCyclotomicClosureEquiv_cyclotomicFieldInRealClosure]
      _ = e ((realCyclotomicGaloisEquiv p g') (cyclotomicFieldInRealClosure p x)) := by
        simp [realCyclotomicGaloisEquiv_apply, e]
      _ = e (cyclotomicFieldInRealClosure p x) := congrArg e (h x)
      _ = (x : Qbar) := realCyclotomicClosureEquiv_cyclotomicFieldInRealClosure p x

/-- The residual ratio of the chosen integral lattice cuts out the full
cyclotomic field over the real cyclotomic base, once the same-lattice
character comparison is supplied. In particular this ratio field is abelian
over `ℚ`, as required by [SkinnerWiles, §4.5, Theorem A]. See
[TripathiGoswamiRevised, Proposition `SW-checklist`]. -/
def skinnerWilesRatioField_of_chosenPrime
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g)) :
    HilbertModularForms.SkinnerWilesRatioField D (cyclotomicField p) := by
  letI : IsAbelianGalois ℚ (cyclotomicField p) :=
    cyclotomicField_isAbelianGalois p
  refine ⟨cyclotomicFieldInRealClosure p, inferInstance,
    (fun σ τ => mul_comm σ τ), ?_⟩
  intro g
  let g' := (realCyclotomicGaloisEquiv p).symm g
  have hg : realCyclotomicGaloisEquiv p g' = g :=
    (realCyclotomicGaloisEquiv p).apply_symm_apply g
  rw [residualRatio_eq_one_iff_fixedClosureCharacter p hp ρ D κ hchar g g' hg,
    residualCharacter_eq_one_iff_fix_cyclotomic p g']
  simpa only [hg] using (fixes_cyclotomic_iff_fixes_realClosure p g')

/-- A residue-field identification carries the chosen prime-kernel character's
oddness into the residual-character ratio used by the weight-two
Skinner--Wiles input. The character comparison is an explicit same-lattice
arithmetic premise. See [TripathiGoswamiRevised, Proposition
`SW-checklist`]. -/
theorem skinnerWilesRatio_odd_of_chosenPrime
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g))
    (c : AbsoluteGalois (realCyclotomicField p))
    (hc : ∃ ι : AlgebraicClosure (realCyclotomicField p) →+* ℂ,
      ∀ x, ι (c x) = star (ι x)) :
    (HilbertModularForms.residualRatio D c : 𝒪[E] ⧸ 𝓂[E]) = -1 := by
  obtain ⟨ι, hc⟩ := hc
  let e := realCyclotomicClosureEquiv p
  let c' : Qbar ≃ₐ[realCyclotomicField p] Qbar :=
    ((e.symm.trans c).trans e)
  let ι' : Qbar →+* ℂ := ι.comp e.symm.toRingHom
  have hc' : ∀ x : Qbar, ι' (c' x) = star (ι' x) := by
    intro x
    simpa [ι', c', e] using hc (e.symm x)
  have he : ((e.trans c').trans e.symm) = c := by
    ext x
    simp [c', e]
  have hodd := realPrimeResidualCharacter_complexConjugation p hp ι' c' hc'
  change AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
    (realCyclotomicField p) p (by omega) ((e.trans c').trans e.symm) = -1 at hodd
  have hodd' : AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
      (realCyclotomicField p) p (by omega) c = -1 := by
    simpa only [he] using hodd
  rw [hchar, hodd']
  simp

/-- The conductor-prime character supplies a nontrivial ratio on the local
decomposition group. The prime-comparison premise says that conjugation by
the chosen closure identification carries the specified stabilizer into the
decomposition group of the integral lattice's prime. This is the local
distinguishedness entry of [TripathiGoswamiRevised, Proposition
`SW-checklist`]. -/
theorem skinnerWilesRatio_distinguished_of_chosenPrime_mem_p
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g))
    (Q₀ : Ideal (𝓞 Qbar)) [Q₀.IsPrime]
    (hpQ₀ : (p : 𝓞 Qbar) ∈ Q₀)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal]
    (hprime : ∀ g : MulAction.stabilizer
        (Qbar ≃ₐ[realCyclotomicField p] Qbar) Q₀,
      realCyclotomicGaloisEquiv p (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) ∈
        HilbertModularForms.primeDecompositionGroup Q) :
    ∃ g : HilbertModularForms.primeDecompositionGroup Q,
      HilbertModularForms.residualRatio D
        (g : AbsoluteGalois (realCyclotomicField p)) ≠ 1 := by
  obtain ⟨g₀, hg₀⟩ := exists_residualCharacter_eq_neg_one_in_stabilizer
    p Q₀ hpQ₀
  let g : HilbertModularForms.primeDecompositionGroup Q :=
    ⟨realCyclotomicGaloisEquiv p (g₀ : Qbar ≃ₐ[realCyclotomicField p] Qbar),
      hprime g₀⟩
  refine ⟨g, ?_⟩
  have hchosen :
      AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
        (realCyclotomicField p) p (by omega)
          (realCyclotomicGaloisEquiv p
            (g₀ : Qbar ≃ₐ[realCyclotomicField p] Qbar)) = -1 := by
    rw [realCyclotomicGaloisEquiv_apply]
    apply Units.ext
    apply (realPrimeResidueEquiv p (by omega)).injective
    rw [realPrimeResidualCharacter_transport p hp _, hg₀]
    simp
  have hne : (-1 : 𝓞 (realCyclotomicField p) ⧸
      Ideal.span {realPrimeGenerator p}) ≠ 1 := by
    intro h
    have h' : (-1 : ZMod p) = 1 := by
      simpa using congrArg (realPrimeResidueEquiv p (by omega)) h
    exact @ZMod.neg_one_ne_one p ⟨by omega⟩ h'
  have hne' : Units.map κ.toMonoidHom
      (-1 : (𝓞 (realCyclotomicField p) ⧸
        Ideal.span {realPrimeGenerator p})ˣ) ≠ 1 := by
    intro h
    apply hne
    apply κ.injective
    simpa using congrArg Units.val h
  change HilbertModularForms.residualRatio D
    (realCyclotomicGaloisEquiv p
      (g₀ : Qbar ≃ₐ[realCyclotomicField p] Qbar)) ≠ 1
  rw [hchar, hchosen]
  exact hne'

/-- The original chosen conductor-prime form follows from membership of `p`
in the prime of `Qbar`. -/
theorem skinnerWilesRatio_distinguished_of_chosenPrime
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g))
    (Q₀ : Ideal (𝓞 Qbar)) [Q₀.IsPrime]
    [Q₀.LiesOver (realPrimeAboveConductor p).asIdeal]
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal]
    (hprime : ∀ g : MulAction.stabilizer
        (Qbar ≃ₐ[realCyclotomicField p] Qbar) Q₀,
      realCyclotomicGaloisEquiv p (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) ∈
        HilbertModularForms.primeDecompositionGroup Q) :
    ∃ g : HilbertModularForms.primeDecompositionGroup Q,
      HilbertModularForms.residualRatio D
        (g : AbsoluteGalois (realCyclotomicField p)) ≠ 1 := by
  have hpQ₀ : (p : 𝓞 Qbar) ∈ Q₀ := by
    have hp₀ : (p : 𝓞 (realCyclotomicField p)) ∈
        (realPrimeAboveConductor p).asIdeal := by
      change (p : 𝓞 (realCyclotomicField p)) ∈
        RingHom.ker (realCyclotomicReduction p)
      simp
    simpa only [map_natCast] using
      (Ideal.mem_of_liesOver Q₀ (realPrimeAboveConductor p).asIdeal
        (p : 𝓞 (realCyclotomicField p))).mp hp₀
  exact skinnerWilesRatio_distinguished_of_chosenPrime_mem_p
    p hp ρ D κ hchar Q₀ hpQ₀ Q hprime

/-- A prime of the chosen algebraic closure is transported separately for each
prime used in the local Skinner--Wiles condition. The closure equivalence then
identifies its stabilizer with the decomposition group of that prime. -/
theorem skinnerWilesRatio_distinguished_at_prime
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    {E : Type*} [Field E] [ValuativeRel E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g))
    (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal]
    (hpP : (p : 𝓞 (realCyclotomicField p)) ∈ P)
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
    [Q.IsMaximal] [Q.LiesOver P] :
    ∃ g : HilbertModularForms.primeDecompositionGroup Q,
      HilbertModularForms.residualRatio D
        (g : AbsoluteGalois (realCyclotomicField p)) ≠ 1 := by
  let e := realCyclotomicClosureEquiv p
  let eO := NumberField.RingOfIntegers.mapAlgEquiv e
  let Q₀ : Ideal (𝓞 Qbar) := Q.map eO
  let : Q₀.IsPrime := Ideal.map_isPrime_of_equiv eO
  have hpQ : (p : 𝓞 (AlgebraicClosure (realCyclotomicField p))) ∈ Q := by
    exact (Ideal.mem_of_liesOver Q P _).mp hpP
  have hpQ₀ : (p : 𝓞 Qbar) ∈ Q₀ := by
    apply (Ideal.mem_map_of_equiv eO _).2
    exact ⟨p, hpQ, by simp [eO]⟩
  have hmem (x : 𝓞 (AlgebraicClosure (realCyclotomicField p))) :
      x ∈ Q ↔ eO x ∈ Q₀ := by
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact (eO.injective hxy).symm ▸ hy
  have hprime : ∀ g : MulAction.stabilizer
      (Qbar ≃ₐ[realCyclotomicField p] Qbar) Q₀,
      realCyclotomicGaloisEquiv p
        (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) ∈
        HilbertModularForms.primeDecompositionGroup Q := by
    intro g
    apply (HilbertModularForms.mem_primeDecompositionGroup_iff Q _).2
    intro x
    rw [hmem x, hmem]
    have htransport : eO ((realCyclotomicGaloisEquiv p g) • x) = g • eO x := by
      apply Subtype.ext
      change e ((realCyclotomicGaloisEquiv p g) (x :
        AlgebraicClosure (realCyclotomicField p))) =
          (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) (e x)
      simp [realCyclotomicGaloisEquiv_apply, e]
    rw [htransport]
    have hgQ : (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) • Q₀ = Q₀ :=
      MulAction.mem_stabilizer_iff.mp g.property
    calc
      eO x ∈ Q₀ ↔ (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) • eO x ∈
          (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) • Q₀ :=
        Ideal.smul_mem_pointwise_smul_iff.symm
      _ ↔ (g : Qbar ≃ₐ[realCyclotomicField p] Qbar) • eO x ∈ Q₀ := by rw [hgQ]
  have hne := skinnerWilesRatio_distinguished_of_chosenPrime_mem_p
    p hp ρ D κ hchar Q₀ hpQ₀ Q hprime
  exact hne

/-- Transport the determinant of the chosen completed Tate factor through an
equivariant identification with the covariant representation used in the
weight-two lifting theorem. The coefficient-map equality is an explicit
compatibility of the completed RM prime with the selected `p`-adic embedding;
it is separate from the exact Tate determinant assertion of
[TripathiGoswamiRevised, Lemma `det-rigidity`]. -/
theorem skinnerWilesDeterminant_of_chosenTateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [NormedField E] [ValuativeRel E] [NormedAlgebra ℚ_[p] E]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (e : letI := darmonPrimeIntegralTateModule p hp ξ
      ρ.Equiv ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p])) :
    ∀ g : AbsoluteGalois (realCyclotomicField p),
      LinearMap.det (ρ g) =
        (Field.cyclotomicCharacterWithCoefficients
          (realCyclotomicField p) p E g : E) := by
  let : Module
      (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p)))
      (AlgebraicGeometry.GroupScheme.integralTate
        (realCyclotomicField p) (darmonPrimeFiber p hp ξ).X p) :=
    darmonPrimeIntegralTateModule p hp ξ
  intro g
  calc
    LinearMap.det (ρ g) =
        LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E g) :=
      (e.det_eq g).symm
    _ = _ := hTateDet g
    _ = algebraMap ℚ_[p] E
        ((Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]) : ℚ_[p]) :=
      hcoeff _
    _ = _ := (Field.cyclotomicCharacterWithCoefficients_coe
      (realCyclotomicField p) p E g).symm

/-- Assemble the weight-two lifting input for the actual chosen Darmon Tate
factor. The equivariance, arithmetic residual lattice, ordinary quotients,
ramification and completed-coefficient compatibility are separate premises;
the ratio field, oddness, local distinguishedness and finite-order determinant
are deduced here. See [TripathiGoswamiRevised, Proposition
`SW-checklist`] and [SkinnerWiles, §4.5, Theorem A]. -/
noncomputable def skinnerWilesWeightTwoInput_of_chosenTateEquiv
    (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (ξ : ProjectiveLine.Parameter (realCyclotomicField p))
    (E : Type*) [NormedField E] [ValuativeRel E] [NormedAlgebra ℚ_[p] E]
    [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
    [CharP (𝒪[E] ⧸ 𝓂[E]) p]
    [Algebra (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    [IsFractionRing (AdicCompletion (Ideal.span {realPrimeGenerator p})
      (𝓞 (realCyclotomicField p))) E]
    (ρ : Representation E (AbsoluteGalois (realCyclotomicField p)) (Fin 2 → E))
    (e : letI := darmonPrimeIntegralTateModule p hp ξ
      ρ.Equiv ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E))
    (hTateDet : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeIntegralTateModule p hp ξ
      LinearMap.det ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange E g) =
        algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
          (𝓞 (realCyclotomicField p))) E
          (TateModule.coefficientPrimeRingEquiv p
            (𝓞 (realCyclotomicField p))
            (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
            (realPrimeRamification_pos p (by omega))
            (span_realPrimeGenerator_pow p (by omega))
              (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p))
                (Field.cyclotomicCharacter (realCyclotomicField p) p g : ℤ_[p]))))
    (hcoeff : ∀ z : ℤ_[p],
      algebraMap (AdicCompletion (Ideal.span {realPrimeGenerator p})
        (𝓞 (realCyclotomicField p))) E
        (TateModule.coefficientPrimeRingEquiv p
          (𝓞 (realCyclotomicField p))
          (Ideal.span {realPrimeGenerator p}) ((p - 1) / 2)
          (realPrimeRamification_pos p (by omega))
          (span_realPrimeGenerator_pow p (by omega))
            (PadicInt.toAdicCompletion p (𝓞 (realCyclotomicField p)) z)) =
        algebraMap ℚ_[p] E (z : ℚ_[p]))
    (hreal : NumberField.IsTotallyReal (realCyclotomicField p))
    (hcontinuous : ∀ i j : Fin 2,
      Continuous (fun g : AbsoluteGalois (realCyclotomicField p) =>
        ρ g (Pi.single j 1) i))
    (hirred : (Representation.baseChange (AlgebraicClosure E) ρ).IsIrreducible)
    (ramified : Set (HeightOneSpectrum (𝓞 (realCyclotomicField p))))
    (hramified : ramified.Finite)
    (hunramified : ∀ q, q ∉ ramified →
      ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal], P = q.asIdeal →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      ∀ g : AbsoluteGalois (realCyclotomicField p),
        g ∈ Q.inertia (AbsoluteGalois (realCyclotomicField p)) → ρ g = 1)
    (D : HilbertModularForms.SkinnerWilesResidualData ρ)
    (κ : (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) ≃+*
      (𝒪[E] ⧸ 𝓂[E]))
    (j : Points (realCyclotomicField p)
        (AlgebraicClosure (realCyclotomicField p))
        (darmonPrimeKernel p hp ξ).X ≃+ (Fin 2 → 𝒪[E] ⧸ 𝓂[E]))
    (hequiv : ∀ (g : AbsoluteGalois (realCyclotomicField p)) v,
      j (g • v) =
        ((LinearMap.toMatrix' (D.integralAction g)).map
          (Ideal.Quotient.mk (𝓂[E]))).mulVec (j v))
    (v : Points (realCyclotomicField p)
      (AlgebraicClosure (realCyclotomicField p))
      (darmonPrimeKernel p hp ξ).X)
    (hv : v ≠ 0)
    (hfix : ∀ g : AbsoluteGalois (realCyclotomicField p), g • v = v)
    (hdetCompare : ∀ g : AbsoluteGalois (realCyclotomicField p),
      letI := darmonPrimeKernelModule p hp ξ
      Ideal.Quotient.mk (𝓂[E]) (LinearMap.det (D.integralAction g)) =
        κ (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g)))
    (hordinary : ∀ (P : Ideal (𝓞 (realCyclotomicField p))) [P.IsMaximal],
      (p : 𝓞 (realCyclotomicField p)) ∈ P →
      ∀ (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField p))))
        [Q.IsMaximal] [Q.LiesOver P],
      HilbertModularForms.SkinnerWilesOrdinaryAt p ρ D Q) :
    HilbertModularForms.SkinnerWilesWeightTwoInput p ρ (cyclotomicField p) := by
  have hchar : ∀ g : AbsoluteGalois (realCyclotomicField p),
      HilbertModularForms.residualRatio D g =
        Units.map κ.toMonoidHom
          (AlgebraicGeometry.GroupScheme.realPrimeResidualCyclotomicCharacter
            (realCyclotomicField p) p (by omega) g) := by
    intro g
    exact congrArg (fun f => f g)
      (residualRatio_eq_chosenPrime_of_fixedKernelPoint
        p hp ξ ρ D κ j hequiv v hv hfix hTateDet hdetCompare)
  have hdet := skinnerWilesDeterminant_of_chosenTateEquiv
    p hp ξ E ρ e hTateDet hcoeff
  haveI : IsAbelianGalois ℚ (realCyclotomicField p) :=
    realCyclotomicField_isAbelianGalois p
  refine
    { p_odd := ?_
      totally_real := hreal
      galois_over_rat := inferInstance
      abelian_over_rat := fun σ τ => mul_comm σ τ
      continuous := hcontinuous
      absolutely_irreducible := hirred
      ramified := ramified
      ramified_finite := hramified
      unramified := hunramified
      residual := D
      ratio_field := skinnerWilesRatioField_of_chosenPrime p hp ρ D κ hchar
      ratio_odd := skinnerWilesRatio_odd_of_chosenPrime p hp ρ D κ hchar
      local_ordinary := hordinary
      ratio_distinguished := ?_
      finite_det_character := 1
      finite_det_range := by
        apply (Set.finite_singleton (1 : Eˣ)).subset
        rintro x ⟨g, rfl⟩
        simp
      determinant := ?_ }
  · exact (Fact.out : p.Prime).odd_of_ne_two (by omega)
  · intro P _ hpP Q _ _
    exact skinnerWilesRatio_distinguished_at_prime
      p hp ρ D κ hchar P hpP Q
  · intro g
    simpa using hdet g

end HilbertModularity.Hypergeometric
