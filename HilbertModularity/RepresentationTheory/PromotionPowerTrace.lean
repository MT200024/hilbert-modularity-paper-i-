/- Assembled by AxiomProver. -/

module

public import HilbertModularity.LinearAlgebra.RankTwoTrace
public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter

/-! # Power traces in compatible-system promotion

Equality of rank-two characteristic polynomials determines the traces of all
powers. Applied to the actual geometric Frobenius operators, this supplies
the residue-degree-one and residue-degree-two traces required in
[TripathiGoswami, Lemma “Promotion from one realization”].
-/

public noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace HilbertModularity

/-- Equal characteristic polynomials of two rank-two matrices give equal
traces of every power, including repeated-root and inseparable cases. -/
theorem matrix_trace_pow_eq_of_charpoly_eq {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (h : A.charpoly = B.charpoly)
    (n : ℕ) : (A ^ n).trace = (B ^ n).trace := by
  have ht : A.trace = B.trace := by
    rw [Matrix.trace_eq_neg_charpoly_coeff,
      Matrix.trace_eq_neg_charpoly_coeff, h]
  have hd : A.det = B.det := by
    have hcoeff := congrArg (fun p : K[X] => p.coeff 0) h
    rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two] at hcoeff
    simpa using hcoeff
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simpa using ht
  | more n ih₀ ih₁ =>
      rw [trace_pow_recurrence, trace_pow_recurrence, ht, hd, ih₀, ih₁]

/-- The preceding power-trace comparison is independent of the chosen
two-element basis. -/
theorem linearMap_trace_pow_eq_of_charpoly_eq
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Free K V] [Module.Finite K V]
    (b : Module.Basis (Fin 2) K V) (A B : Module.End K V)
    (h : A.charpoly = B.charpoly) (n : ℕ) :
    LinearMap.trace K V (A ^ n) = LinearMap.trace K V (B ^ n) := by
  rw [LinearMap.trace_eq_matrix_trace K b,
    LinearMap.trace_eq_matrix_trace K b,
    ← LinearMap.toMatrix_pow, ← LinearMap.toMatrix_pow]
  exact matrix_trace_pow_eq_of_charpoly_eq
    (LinearMap.toMatrix b b A) (LinearMap.toMatrix b b B)
    (by simpa only [LinearMap.charpoly_toMatrix] using h) n

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]

/-- The scalar in a character twist is raised to the same power as the
Frobenius operator. This distinguishes a residue-degree-two Frobenius trace
from the symmetric-square trace. -/
theorem NumberFieldCompatibleSystem.characterTwist_trace_pow
    (σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w : HeightOneSpectrum (𝓞 E))
    (g : HilbertModularForms.AbsoluteGalois F) (n : ℕ) :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (((σ.action w).characterTwist (χ.local w) g) ^ n) =
      (χ.toMonoidHom g : w.adicCompletion E) ^ n *
        LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
          ((σ.action w g) ^ n) := by
  let b := Pi.basisFun (w.adicCompletion E) (Fin 2)
  change LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
    (((χ.local w g : w.adicCompletion E) • (σ.action w g)) ^ n) = _
  rw [smul_pow, LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b,
    LinearMap.trace_eq_matrix_trace (w.adicCompletion E) b, map_smul,
    Matrix.trace_smul]
  change (χ.local w g : w.adicCompletion E) ^ n *
    Matrix.trace (LinearMap.toMatrix b b ((σ.action w g) ^ n)) = _
  have hχ : (χ.local w g : w.adicCompletion E) =
      (χ.toMonoidHom g : w.adicCompletion E) := by
    rw [χ.local_eq_composition]
    rfl
  rw [hχ]

/-- One-place equivariance gives equality of the actual power traces of
geometric Frobenius at another coefficient place. The finite comparison set
contains both coefficient-characteristic exclusions and the character's
ramification set. -/
theorem NumberFieldCompatibleSystem.frobenius_powerTrace_characterTwist_eq_of_good
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (σ.action w₀)))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad σ χ w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (n : ℕ) :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        ((ρ.action w (NumberField.geometricFrobenius F
          (AlgebraicClosure F) P Q)) ^ n) =
      LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        (((σ.action w).characterTwist (χ.local w)
          (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)) ^ n) := by
  let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
  have hq' := ρ.not_mem_comparisonBad_of_characterGood σ χ w₀ w q hq
  have hpoly : (ρ.action w g).charpoly =
      (((Representation.ofCharacter (χ.local w)).tprod (σ.action w)) g).charpoly := by
    simpa only [χ.local_eq_composition] using
      (ρ.charpoly_characterTensor_eq_of_good σ χ.toMonoidHom w₀ w
        (by simpa only [χ.local_eq_composition] using e) q hq' P hP Q)
  have hpoly' : (ρ.action w g).charpoly =
      ((σ.action w).characterTwist (χ.local w) g).charpoly :=
    hpoly.trans
      ((Representation.characterTwistTensorEquiv (σ.action w) (χ.local w)).charpoly_eq g)
  exact linearMap_trace_pow_eq_of_charpoly_eq
    (Pi.basisFun (w.adicCompletion E) (Fin 2)) _ _ hpoly' n

/-- The same power trace is expressed through the one algebraic character
at every coefficient place. In particular `n = 1` and `n = 2` give the two
residue degrees used in the manuscript's trace comparison. -/
theorem NumberFieldCompatibleSystem.frobenius_powerTrace_eq_of_characterGood
    (ρ σ : NumberFieldCompatibleSystem F E)
    (χ : FiniteAlgebraicGaloisCharacter F E)
    (w₀ w : HeightOneSpectrum (𝓞 E))
    (e : (ρ.action w₀).Equiv
      ((Representation.ofCharacter (χ.local w₀)).tprod (σ.action w₀)))
    (q : HeightOneSpectrum (𝓞 F))
    (hq : q ∉ ρ.characterComparisonBad σ χ w₀ w)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (n : ℕ) :
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
        ((ρ.action w (NumberField.geometricFrobenius F
          (AlgebraicClosure F) P Q)) ^ n) =
      (χ.toMonoidHom
        (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) :
          w.adicCompletion E) ^ n *
        LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E)
          ((σ.action w (NumberField.geometricFrobenius F
            (AlgebraicClosure F) P Q)) ^ n) := by
  rw [ρ.frobenius_powerTrace_characterTwist_eq_of_good σ χ w₀ w e q hq P hP Q n,
    σ.characterTwist_trace_pow χ w
      (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q) n]

end HilbertModularity
