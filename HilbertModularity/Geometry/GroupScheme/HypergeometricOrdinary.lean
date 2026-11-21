/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricScalarConjugate
public import HilbertModularity.NumberTheory.CyclotomicLocalGalois
public import HilbertModularity.RepresentationTheory.WeightZeroQuotient
public import HilbertModularity.RepresentationTheory.OrdinaryHodgeTate
public import HilbertModularity.Geometry.GroupScheme.HypergeometricRanks
public import HilbertModularity.Geometry.GroupScheme.TateLocalSystem.LocalCoefficientTopology
public import HilbertModularity.Geometry.GroupScheme.FiberCoefficients

/-! # Deep ordinary quotients of the chosen Darmon family

The local action is the restriction of the same chosen native Tate
representation along the actual completion-to-global Galois homomorphism.
Its ordinary quotient witnesses use the genuine `Cp` comparison and every
local-field label. We follow [TripathiGoswami, Definition DO].
-/

@[expose] public noncomputable section

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry

attribute [local instance] realPrimePowerCompletionPadicAlgebra
  realPrimePowerCompletionPadicTower realPrimePowerCompletion_uniformContinuousConstSMul
  realPrimePowerCompletionComplexTower

variable (p k : ℕ) [Fact p.Prime] (hN : 3 ≤ p ^ (k + 1))
  (ξ : ProjectiveLine.Parameter ℚ)

/-- The actual chosen Tate representation restricted to the Galois group of the specified completion. -/
def darmonDecompositionRepresentation :
    Rep (RealPrimePowerCompletion p k) Gal(PadicAlgCl p/RealPrimePowerCompletion p k) :=
  Rep.of ((darmonLocalTateRepresentation p k hN ξ).ρ.comp
    (realPrimePowerLocalGaloisRestriction p k))

/-- Local Galois acts through the actual restriction homomorphism on the original Tate fibre. -/
@[simp] theorem darmonDecompositionRepresentation_apply
    (g : Gal(PadicAlgCl p/RealPrimePowerCompletion p k))
    (v : darmonDecompositionRepresentation p k hN ξ) :
    (darmonDecompositionRepresentation p k hN ξ).ρ g v =
      (darmonLocalTateRepresentation p k hN ξ).ρ (realPrimePowerLocalGaloisRestriction p k g) v := rfl

/-- Rational p-adic scalars are restricted from the actual completed coefficient action. -/
@[instance_reducible] def darmonDecompositionRationalModule :
    Module ℚ_[p] (darmonDecompositionRepresentation p k hN ξ) :=
  Module.compHom _ (algebraMap ℚ_[p] (RealPrimePowerCompletion p k))

attribute [local instance] darmonDecompositionRationalModule

/-- The rational and completed coefficient actions form the canonical scalar tower. -/
theorem darmonDecompositionScalarTower :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
      (darmonDecompositionRepresentation p k hN ξ) where
  smul_assoc r a v := by
    change (algebraMap ℚ_[p] (RealPrimePowerCompletion p k) r * a) • v =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) r • (a • v)
    exact mul_smul _ _ _

attribute [local instance] darmonDecompositionScalarTower

/-- The local coefficient label of the actual restricted chosen Tate representation. -/
def darmonDecompositionScalarConjugate (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :=
  Rep.localCoefficientConjugate p k m hm (darmonDecompositionRepresentation p k hN ξ)

/-- Coefficient conjugation commutes with the actual local Galois restriction. -/
theorem darmonDecompositionScalarConjugate_eq (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ =
      (darmonLocalScalarConjugate p k hN ξ m hm).ρ.comp
        (realPrimePowerLocalGaloisRestriction p k) := rfl

/-- Rational scalars on a coefficient-conjugate local Tate representation. -/
@[instance_reducible] def darmonDecompositionConjugateRationalModule
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Module ℚ_[p] (darmonDecompositionScalarConjugate p k hN ξ m hm) :=
  Module.compHom _ (algebraMap ℚ_[p] (RealPrimePowerCompletion p k))

attribute [local instance] darmonDecompositionConjugateRationalModule

/-- Rational scalars remain compatible with the conjugated completed coefficients. -/
theorem darmonDecompositionConjugateScalarTower (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
      (darmonDecompositionScalarConjugate p k hN ξ m hm) where
  smul_assoc r a v := by
    change (algebraMap ℚ_[p] (RealPrimePowerCompletion p k) r * a) • v =
      algebraMap ℚ_[p] (RealPrimePowerCompletion p k) r • (a • v)
    exact mul_smul _ _ _

attribute [local instance] darmonDecompositionConjugateScalarTower

/-- A deep ordinary quotient of the actual local coefficient conjugate.
Existence is `Nonempty` of this concrete quotient-witness type. -/
def DarmonOrdinaryQuotient (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :=
  HodgeTate.WeightZeroQuotient p (realPrimePowerLocalPeriodAction p k)
    (realPrimePowerLocalPeriodAction_fixes p k)
    (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ

/-- The chosen-family witness is exactly the rank-one all-labelled Hodge–Tate quotient criterion. -/
theorem nonempty_darmonOrdinaryQuotient_iff_labelled
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Nonempty (DarmonOrdinaryQuotient p k hN ξ m hm) ↔
      ∃ S : Subrepresentation (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ,
        Module.finrank (RealPrimePowerCompletion p k)
          (darmonDecompositionScalarConjugate p k hN ξ m hm ⧸ S.toSubmodule) = 1 ∧
        Function.Bijective (HodgeTate.comparison p (realPrimePowerLocalPeriodAction p k)
          (realPrimePowerLocalPeriodAction_fixes p k)
          (((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ.quotient
            S.toSubmodule S.apply_mem_toSubmodule).restrictScalars ℚ_[p])) ∧
        ∀ τ, ∀ q : ℤ, q ≠ 0 → HodgeTate.labelledWeightSpace p
          (realPrimePowerLocalPeriodAction p k) (realPrimePowerLocalPeriodAction_fixes p k)
          ((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ.quotient
            S.toSubmodule S.apply_mem_toSubmodule) q τ = ⊥ :=
  HodgeTate.nonempty_weightZeroQuotient_iff_labelled p
    (realPrimePowerLocalPeriodAction p k) (realPrimePowerLocalPeriodAction_fixes p k)
    (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ

/-- Deep ordinariness of the same chosen fibre is independent of its coprime coefficient label. -/
theorem nonempty_darmonOrdinaryQuotient_iff (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Nonempty (DarmonOrdinaryQuotient p k hN ξ m hm) ↔
      Nonempty (DarmonOrdinaryQuotient p k hN ξ 1 (Nat.coprime_one_left _)) := by
  let : Module ℚ_[p]
      (Rep.localCoefficientConjugate p k m hm (darmonDecompositionRepresentation p k hN ξ)) :=
    darmonDecompositionConjugateRationalModule p k hN ξ m hm
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
      (Rep.localCoefficientConjugate p k m hm (darmonDecompositionRepresentation p k hN ξ)) :=
    darmonDecompositionConjugateScalarTower p k hN ξ m hm
  let : Module ℚ_[p] (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _)
      (darmonDecompositionRepresentation p k hN ξ)) :=
    darmonDecompositionConjugateRationalModule p k hN ξ 1 (Nat.coprime_one_left _)
  let : IsScalarTower ℚ_[p] (RealPrimePowerCompletion p k)
      (Rep.localCoefficientConjugate p k 1 (Nat.coprime_one_left _)
        (darmonDecompositionRepresentation p k hN ξ)) :=
    darmonDecompositionConjugateScalarTower p k hN ξ 1 (Nat.coprime_one_left _)
  exact HodgeTate.nonempty_weightZeroQuotient_localCoefficientConjugate_independent p
    (realPrimePowerLocalPeriodAction p k) (realPrimePowerLocalPeriodAction_fixes p k)
    k m hm (darmonDecompositionRepresentation p k hN ξ)


/-- The actual local Galois restriction retains the completed-coefficient rank two. -/
theorem finrank_darmonDecompositionRepresentation :
    Module.finrank (RealPrimePowerCompletion p k)
      (darmonDecompositionRepresentation p k hN ξ) = 2 := by
  change Module.finrank (RealPrimePowerCompletion p k)
    (darmonLocalTateRepresentation p k hN ξ) = 2
  exact finrank_darmonLocalTateRepresentation p k hN ξ

/-- Every coefficient conjugate of the actual decomposition-group representation has rank two. -/
theorem finrank_darmonDecompositionScalarConjugate
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Module.finrank (RealPrimePowerCompletion p k)
      (darmonDecompositionScalarConjugate p k hN ξ m hm) = 2 := by
  unfold darmonDecompositionScalarConjugate
  exact (Rep.finrank_localCoefficientConjugate p k m hm
    (darmonDecompositionRepresentation p k hN ξ)).trans
      (finrank_darmonDecompositionRepresentation p k hN ξ)

/-- The actual local conjugate has its completed-coefficient module topology. -/
@[instance_reducible] def darmonDecompositionConjugateTopology
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    TopologicalSpace (darmonDecompositionScalarConjugate p k hN ξ m hm) :=
  moduleTopology (RealPrimePowerCompletion p k) _

attribute [local instance] darmonDecompositionConjugateTopology

/-- The chosen topology is the same module topology used for the native coefficient conjugate. -/
theorem darmonDecompositionConjugateModuleTopology
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    IsModuleTopology (RealPrimePowerCompletion p k)
      (darmonDecompositionScalarConjugate p k hN ξ m hm) := ⟨rfl⟩

attribute [local instance] darmonDecompositionConjugateModuleTopology

/-- Restricting the native continuous Tate action to the actual local Galois group is continuous. -/
theorem continuous_darmonDecompositionScalarConjugate
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    Continuous fun y : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) ×
        darmonDecompositionScalarConjugate p k hN ξ m hm =>
      (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ y.1 y.2 := by
  unfold darmonDecompositionScalarConjugate Rep.localCoefficientConjugate
    darmonDecompositionRepresentation
  apply Rep.continuous_scalarConjugate_comp
    (realPrimePowerCompletionAutomorphism p k m hm).toRingEquiv
    (darmonLocalTateRepresentation p k hN ξ) (realPrimePowerLocalGaloisRestriction p k)
    (continuous_realPrimePowerLocalGaloisRestriction p k)
  unfold darmonLocalTateRepresentation
  have h := GroupScheme.continuous_localConjugateTateRep
    (realCyclotomicField (p ^ (k + 1))) (darmonFamily (p ^ (k + 1)) hN)
    (ProjectiveLine.puncturedPoint (realCyclotomicField (p ^ (k + 1)))
      (darmonRationalParameter (p ^ (k + 1)) ξ)) p k
    (darmonRealMultiplication (p ^ (k + 1)) hN) m hm
  with_reducible simpa only [GroupScheme.localConjugateTateRepTopology] using h

/-- Every orbit of the actual local coefficient-conjugate action is continuous. -/
theorem continuous_darmonDecompositionScalarConjugate_apply
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1)))
    (v : darmonDecompositionScalarConjugate p k hN ξ m hm) :
    Continuous (fun g : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) =>
      (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ g v) := by
  have h := continuous_darmonDecompositionScalarConjugate p k hN ξ m hm
  have hf : Continuous (fun g : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) => (g, v)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using h.comp hf

/-- Deep ordinariness of the chosen family yields an actual continuous triangular basis.
The lower character is the given quotient, has every labelled weight zero, and its fixed
periods span the full completed tensor. -/
theorem DarmonOrdinaryQuotient.exists_continuous_characters_upperTriangular
    (m : ℕ) (hm : m.Coprime (p ^ (k + 1))) (W : DarmonOrdinaryQuotient p k hN ξ m hm) :
    ∃ (b : Module.Basis (Fin 2) (RealPrimePowerCompletion p k)
        (darmonDecompositionScalarConjugate p k hN ξ m hm))
      (χ₁ χ₂ : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) →*
        (RealPrimePowerCompletion p k)ˣ)
      (a : Gal(PadicAlgCl p/RealPrimePowerCompletion p k) → RealPrimePowerCompletion p k),
      Continuous χ₁ ∧ Continuous χ₂ ∧ b 0 ∈ W.kernel ∧
      Nonempty (((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ.quotient
        W.kernel.toSubmodule W.kernel.apply_mem_toSubmodule).Equiv
          (Representation.ofCharacter χ₂)) ∧
      (∀ τ, ∀ q : ℤ, q ≠ 0 → HodgeTate.labelledWeightSpace p
        (realPrimePowerLocalPeriodAction p k) (realPrimePowerLocalPeriodAction_fixes p k)
        (Representation.ofCharacter χ₂) q τ = ⊥) ∧
      HodgeTate.zeroWeightSpan (ι := realPrimePowerLocalPeriodAction p k)
        ((Representation.ofCharacter χ₂).restrictScalars ℚ_[p]) = ⊤ ∧
      ∀ g, LinearMap.toMatrix b b ((darmonDecompositionScalarConjugate p k hN ξ m hm).ρ g) =
        !![(χ₁ g : RealPrimePowerCompletion p k), a g; 0, (χ₂ g : RealPrimePowerCompletion p k)] := by
  let := Valued.toNontriviallyNormedField (RealPrimePowerCompletion p k) (WithZero (Multiplicative ℤ))
  let : Module.Finite (RealPrimePowerCompletion p k)
      (darmonDecompositionScalarConjugate p k hN ξ m hm) :=
    Module.finite_of_finrank_eq_succ (finrank_darmonDecompositionScalarConjugate p k hN ξ m hm)
  unfold DarmonOrdinaryQuotient at W
  with_reducible
    exact HodgeTate.WeightZeroQuotient.exists_continuous_characters_upperTriangular p
      (K := RealPrimePowerCompletion p k)
      (E := RealPrimePowerCompletion p k)
      (G := Gal(PadicAlgCl p/RealPrimePowerCompletion p k))
      (V := darmonDecompositionScalarConjugate p k hN ξ m hm)
      (realPrimePowerLocalPeriodAction p k) (realPrimePowerLocalPeriodAction_fixes p k)
      (ρ := (darmonDecompositionScalarConjugate p k hN ξ m hm).ρ) W
      (finrank_darmonDecompositionScalarConjugate p k hN ξ m hm)
      (continuous_darmonDecompositionScalarConjugate_apply p k hN ξ m hm)

end HilbertModularity.Hypergeometric
