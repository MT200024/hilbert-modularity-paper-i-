/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.CyclotomicPadic
public import HilbertModularity.NumberTheory.CyclotomicPrimePower
public import HilbertModularity.NumberTheory.CyclotomicEmbeddings
public import HilbertModularity.NumberTheory.RealCyclotomicResidue
public import HilbertModularity.NumberTheory.PadicCompletion

/-! # Completion of the real cyclotomic coefficient field

At the prime conductor, the real cyclotomic tensor is a single field, canonically
isomorphic to the completion at its unique prime. The labelled global coefficient
automorphisms extend continuously to this completion, as used in
the coefficient-label lemma of [TripathiGoswami].
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HilbertModularity.Cyclotomic

variable (p : ℕ) [Fact p.Prime]

/-- The completion of the real cyclotomic field at its unique prime above the conductor. -/
abbrev RealCompletion := (realPrimeAboveConductor p).adicCompletion (realCyclotomicField p)

/-- Extending rational scalars to `Q_p` gives exactly the real cyclotomic completion. -/
def realCompletionTensorEquiv :
    ℚ_[p] ⊗[ℚ] realCyclotomicField p ≃ₐ[ℚ_[p]] RealCompletion p :=
  NumberField.padicCompletionTensorEquiv p (realCyclotomicField p)
    (realPrimeAboveConductor p) (realPadicTensor_isField p)

@[simp] theorem realCompletionTensorEquiv_tmul (a : ℚ_[p]) (x : realCyclotomicField p) :
    realCompletionTensorEquiv p (a ⊗ₜ[ℚ] x) =
      a • algebraMap (realCyclotomicField p) (RealCompletion p) x := rfl

/-- The same identification with the coefficient factors in manuscript order. -/
def realCompletionTensorRightEquiv :
    realCyclotomicField p ⊗[ℚ] ℚ_[p] ≃+* RealCompletion p :=
  (Algebra.TensorProduct.comm ℚ (realCyclotomicField p) ℚ_[p]).toRingEquiv.trans
    (realCompletionTensorEquiv p).toRingEquiv

@[simp] theorem realCompletionTensorRightEquiv_tmul (x : realCyclotomicField p) (a : ℚ_[p]) :
    realCompletionTensorRightEquiv p (x ⊗ₜ[ℚ] a) =
      a • algebraMap (realCyclotomicField p) (RealCompletion p) x := rfl

/-- The coefficient automorphism labelled by `m` on the actual ramified completion. -/
def realCompletionAutomorphism (m : ℕ) (hm : m.Coprime p) :
    RealCompletion p ≃ₐ[ℚ_[p]] RealCompletion p :=
  NumberField.padicCompletionAutomorphism p (realCyclotomicField p)
    (realPrimeAboveConductor p) (realPadicTensor_isField p) (realPowerAutomorphism p m hm)

/-- The local coefficient automorphism extends the labelled global automorphism. -/
@[simp] theorem realCompletionAutomorphism_algebraMap (m : ℕ) (hm : m.Coprime p)
    (x : realCyclotomicField p) :
    realCompletionAutomorphism p m hm (algebraMap _ (RealCompletion p) x) =
      algebraMap _ (RealCompletion p) (realPowerAutomorphism p m hm x) :=
  NumberField.padicCompletionAutomorphism_algebraMap _ _ _ _ _ _

/-- The first trace parameter is sent to the trace parameter labelled by `m`. -/
theorem realCompletionAutomorphism_tau_one (m : ℕ) (hm : m.Coprime p) :
    realCompletionAutomorphism p m hm (algebraMap _ (RealCompletion p) (tau p 1)) =
      algebraMap _ (RealCompletion p) (tau p m) := by
  rw [realCompletionAutomorphism_algebraMap, realPowerAutomorphism_tau_one]

/-- The labelled automorphism is continuous in the actual completion topology. -/
theorem continuous_realCompletionAutomorphism (m : ℕ) (hm : m.Coprime p) :
    Continuous (realCompletionAutomorphism p m hm) :=
  NumberField.continuous_padicCompletionAutomorphism _ _ _ _ _

/-- Completion of the real cyclotomic field of prime-power conductor at its unique prime above `p`. -/
abbrev RealPrimePowerCompletion (k : ℕ) :=
  (realPrimeAbovePrimePower p k).adicCompletion (realCyclotomicField (p ^ (k + 1)))

/-- The real prime-power coefficient tensor is canonically the local coefficient field. -/
def realPrimePowerCompletionTensorEquiv (k : ℕ) :
    ℚ_[p] ⊗[ℚ] realCyclotomicField (p ^ (k + 1)) ≃ₐ[ℚ_[p]] RealPrimePowerCompletion p k :=
  NumberField.padicCompletionTensorEquiv p (realCyclotomicField (p ^ (k + 1)))
    (realPrimeAbovePrimePower p k) (realPrimePowerPadicTensor_isField p k)

@[simp] theorem realPrimePowerCompletionTensorEquiv_tmul (k : ℕ) (a : ℚ_[p])
    (x : realCyclotomicField (p ^ (k + 1))) :
    realPrimePowerCompletionTensorEquiv p k (a ⊗ₜ[ℚ] x) =
      a • algebraMap _ (RealPrimePowerCompletion p k) x := rfl

/-- The labelled coefficient automorphism on the actual prime-power completion. -/
def realPrimePowerCompletionAutomorphism (k m : ℕ) (hm : m.Coprime (p ^ (k + 1))) :
    RealPrimePowerCompletion p k ≃ₐ[ℚ_[p]] RealPrimePowerCompletion p k :=
  NumberField.padicCompletionAutomorphism p (realCyclotomicField (p ^ (k + 1)))
    (realPrimeAbovePrimePower p k) (realPrimePowerPadicTensor_isField p k)
    (realPowerAutomorphism (p ^ (k + 1)) m hm)

@[simp] theorem realPrimePowerCompletionAutomorphism_algebraMap (k m : ℕ)
    (hm : m.Coprime (p ^ (k + 1))) (x : realCyclotomicField (p ^ (k + 1))) :
    realPrimePowerCompletionAutomorphism p k m hm (algebraMap _ (RealPrimePowerCompletion p k) x) =
      algebraMap _ (RealPrimePowerCompletion p k) (realPowerAutomorphism (p ^ (k + 1)) m hm x) :=
  NumberField.padicCompletionAutomorphism_algebraMap _ _ _ _ _ _

/-- The local prime-power label sends the first trace parameter to the `m`-th one. -/
theorem realPrimePowerCompletionAutomorphism_tau_one (k m : ℕ)
    (hm : m.Coprime (p ^ (k + 1))) :
    realPrimePowerCompletionAutomorphism p k m hm
      (algebraMap _ (RealPrimePowerCompletion p k) (tau (p ^ (k + 1)) 1)) =
      algebraMap _ (RealPrimePowerCompletion p k) (tau (p ^ (k + 1)) m) := by
  rw [realPrimePowerCompletionAutomorphism_algebraMap, realPowerAutomorphism_tau_one]

/-- Prime-power coefficient labels extend continuously to the local field. -/
theorem continuous_realPrimePowerCompletionAutomorphism (k m : ℕ)
    (hm : m.Coprime (p ^ (k + 1))) :
    Continuous (realPrimePowerCompletionAutomorphism p k m hm) :=
  NumberField.continuous_padicCompletionAutomorphism _ _ _ _ _

end HilbertModularity.Cyclotomic
