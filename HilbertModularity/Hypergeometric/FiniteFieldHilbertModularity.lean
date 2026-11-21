/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.Specialization
public import HilbertModularity.NumberTheory.HilbertModularForms.CohomologicalCompatibleSystem
public import HilbertModularity.LinearAlgebra.RankTwoTrace
public import HilbertModularity.NumberTheory.RealCyclotomic

/-! # Hilbert modularity of a finite-field hypergeometric family

The root formulation in [TripathiGoswamiRevised,
Definition `def:ff-hilbert-modular`] fixes one eigenform and one algebraic
coefficient embedding before the good prime. The power-trace lemma below
recovers the cohomological formulation at every coefficient place away from
that prime. The exponent is the residue degree, not a symmetric power.
-/

public noncomputable section

open IsDedekindDomain Polynomial
open scoped NumberField

namespace HilbertModularity.HilbertModularForms

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- Algebraic Hecke roots compute every geometric-Frobenius power trace,
in every coefficient completion compatible with the fixed algebraic embedding.
Repeated roots are allowed. -/
theorem EigenformCohomologicalActions.map_trace_frobenius_pow_of_roots
    {φ : AlgebraicGoodPrimeEigenform level μ E}
    (D : EigenformCohomologicalActions φ)
    (j : E →+* Cyclotomic.Qbar)
    (w : HeightOneSpectrum (𝓞 E))
    (ι : Cyclotomic.Qbar →+* AlgebraicClosure (w.adicCompletion E))
    (hι : ι.comp j =
      (algebraMap (w.adicCompletion E) (AlgebraicClosure (w.adicCompletion E))).comp
        (algebraMap E (w.adicCompletion E)))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ φ.form.bad)
    (hp : (D.residueCharacteristic w : 𝓞 F) ∉ q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver q.asIdeal]
    (α β : Cyclotomic.Qbar)
    (hroots : (X - C α) * (X - C β) = (φ.heckePolynomial q hq).map j)
    (n : ℕ) :
    algebraMap (w.adicCompletion E) (AlgebraicClosure (w.adicCompletion E))
      (LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (D.action w
          ((NumberField.geometricFrobenius F (AlgebraicClosure F) q.asIdeal Q) ^ n))) =
      ι (α ^ n + β ^ n) := by
  let f := D.action w
    (NumberField.geometricFrobenius F (AlgebraicClosure F) q.asIdeal Q)
  have hpoly : f.charpoly.map
      (algebraMap (w.adicCompletion E) (AlgebraicClosure (w.adicCompletion E))) =
      (X - C (ι α)) * (X - C (ι β)) := by
    rw [D.frobenius_charpoly w q hq q.asIdeal rfl hp Q, Polynomial.map_map, ← hι]
    rw [← Polynomial.map_map, ← hroots]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have ht := linearMap_trace_pow_eq_sum_roots
    (algebraMap (w.adicCompletion E) (AlgebraicClosure (w.adicCompletion E)))
    (Pi.basisFun (w.adicCompletion E) (Fin 2)) f (ι α) (ι β) hpoly n
  simpa only [map_pow, map_add] using ht

end HilbertModularity.HilbertModularForms

namespace HilbertModularity.Cyclotomic

open HilbertModularForms

attribute [local instance] Ideal.Quotient.field

local instance (N : ℕ) [NeZero N] :
    Algebra (realCyclotomicField N) (cyclotomicField N) :=
  (IntermediateField.inclusion (realCyclotomicField_le N)).toRingHom.toAlgebra

/-- One eigenform's algebraic Hecke roots give the prescribed McCarthy values
at every eligible prime, with one fixed coefficient embedding. -/
@[expose] def HasFiniteFieldHeckeTraces (N m : ℕ) [NeZero N]
    (ξ : realCyclotomicField N)
    {B : Type*} [Field B] [NumberField B]
    {level : FiniteLevel (realCyclotomicField N)}
    {μ : AdditiveQuotientMeasure (realCyclotomicField N)}
    (ψ : AlgebraicGoodPrimeEigenform level μ B) (j : B →+* Qbar) : Prop :=
  ∀ (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hx : P.GoodUnit (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ))
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar), θ ≠ 1 →
    ∀ (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
      [P.asIdeal.LiesOver q.asIdeal],
    ∃ (hψ : q ∉ ψ.form.bad) (α β : Qbar),
      (X - C α) * (X - C β) = (ψ.heckePolynomial q hψ).map j ∧
      mccarthyValue N P hP m θ
        (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ) hx =
        α ^ P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N)) +
          β ^ P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N))

/-- The root formulation gives the manuscript's cohomological trace identity
at every coefficient place away from the geometric prime, not just one
auxiliary realization. -/
theorem HasFiniteFieldHeckeTraces.cohomological_trace
    {N m : ℕ} [NeZero N] {ξ : realCyclotomicField N}
    {B : Type*} [Field B] [NumberField B]
    {level : FiniteLevel (realCyclotomicField N)}
    {μ : AdditiveQuotientMeasure (realCyclotomicField N)}
    {ψ : AlgebraicGoodPrimeEigenform level μ B} {j : B →+* Qbar}
    (h : HasFiniteFieldHeckeTraces N m ξ ψ j)
    (D : EigenformCohomologicalActions ψ)
    (P : HeightOneSpectrum (𝓞 (cyclotomicField N)))
    (hP : (N : 𝓞 (cyclotomicField N)) ∉ P.asIdeal)
    (hx : P.GoodUnit (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ))
    (θ : AddChar (𝓞 (cyclotomicField N) ⧸ P.asIdeal) Qbar) (hθ : θ ≠ 1)
    (q : HeightOneSpectrum (𝓞 (realCyclotomicField N)))
    [P.asIdeal.LiesOver q.asIdeal]
    (w : HeightOneSpectrum (𝓞 B))
    (hp : (D.residueCharacteristic w : 𝓞 (realCyclotomicField N)) ∉ q.asIdeal)
    (ι : Qbar →+* AlgebraicClosure (w.adicCompletion B))
    (hι : ι.comp j =
      (algebraMap (w.adicCompletion B) (AlgebraicClosure (w.adicCompletion B))).comp
        (algebraMap B (w.adicCompletion B)))
    (Q : Ideal (𝓞 (AlgebraicClosure (realCyclotomicField N))))
    [Q.IsMaximal] [Q.LiesOver q.asIdeal] :
    ι (mccarthyValue N P hP m θ
      (algebraMap (realCyclotomicField N) (cyclotomicField N) ξ) hx) =
      algebraMap (w.adicCompletion B) (AlgebraicClosure (w.adicCompletion B))
        (LinearMap.trace (w.adicCompletion B) (Fin 2 → w.adicCompletion B)
          (D.action w
            ((NumberField.geometricFrobenius (realCyclotomicField N)
              (AlgebraicClosure (realCyclotomicField N)) q.asIdeal Q) ^
                P.asIdeal.inertiaDeg (𝓞 (realCyclotomicField N))))) := by
  obtain ⟨hq, α, β, hroots, hvalue⟩ := h P hP hx θ hθ q
  rw [hvalue]
  exact (D.map_trace_frobenius_pow_of_roots j w ι hι q hq hp Q α β hroots _).symm

/-- Finite-field Hilbert modularity at a specialization, in the equivalent
root formulation of [TripathiGoswamiRevised,
Definition `def:ff-hilbert-modular`]. The common algebraic field and embeddings
are chosen before any good prime. -/
@[expose] def FiniteFieldHilbertModularAt (N m : ℕ) [NeZero N]
    (ξ : realCyclotomicField N) : Prop :=
  ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
    letI := hB
    ∃ (jF : cyclotomicField N →+* B) (j : B →+* Qbar),
      j.comp jF = (cyclotomicField N).val.toRingHom ∧
      ∃ (level : FiniteLevel (realCyclotomicField N))
        (μ : AdditiveQuotientMeasure (realCyclotomicField N))
        (ψ : AlgebraicGoodPrimeEigenform level μ B),
        ψ.complexEmbedding = B.val.toRingHom ∧ HasFiniteFieldHeckeTraces N m ξ ψ j

/-- Hilbert modularity on a set of nonsingular rational parameters.
The eigenform and its common coefficient field may depend on the parameter,
as in [TripathiGoswamiRevised, Definition `def:ff-hilbert-modular`]. -/
def FiniteFieldHilbertModularOn (N m : ℕ) [NeZero N] (S : Set ℚ) : Prop :=
  S ⊆ {ξ | ξ ≠ 0 ∧ ξ ≠ 1} ∧
    ∀ ξ ∈ S, FiniteFieldHilbertModularAt N m (algebraMap ℚ (realCyclotomicField N) ξ)

end HilbertModularity.Cyclotomic
