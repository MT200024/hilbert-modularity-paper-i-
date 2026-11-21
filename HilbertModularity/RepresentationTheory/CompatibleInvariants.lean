/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.NumberFieldCompatibleSystem

/-! # Algebraic trace and determinant of a rank-two compatible system -/

public noncomputable section

open scoped NumberField

namespace HilbertModularity

/-- The first two coefficients of a common rank-two polynomial recover the
trace and determinant under the same coefficient embedding. -/
theorem trace_det_of_rankTwo_charpoly_map
    {E L V : Type*} [Field E] [Field L] [AddCommGroup V] [Module L V]
    [Module.Free L V] [Module.Finite L V]
    (b : Module.Basis (Fin 2) L V) (f : Module.End L V)
    (R : Polynomial E) (j : E →+* L) (h : f.charpoly = R.map j) :
    LinearMap.trace L V f = j (-R.coeff 1) ∧ f.det = j (R.coeff 0) := by
  have hm : (LinearMap.toMatrix b b f).charpoly = R.map j := by
    simpa only [LinearMap.charpoly_toMatrix] using h
  constructor
  · rw [LinearMap.trace_eq_matrix_trace L b, Matrix.trace_eq_neg_charpoly_coeff,
      hm]
    simp
  · have hc := congrArg (fun S : Polynomial L => S.coeff 0) hm
    rw [Matrix.charpoly_fin_two] at hc
    simpa using hc


/-- At every permissible coefficient place, trace and determinant come from the
same algebraic polynomial. This is the coefficient extraction in
[TripathiGoswamiRevised, Lemma `labelled-RM-compat`]. -/
theorem NumberFieldCompatibleSystem.frobenius_trace_det
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    (ρ : NumberFieldCompatibleSystem F E)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hq : q ∉ ρ.bad)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = q.asIdeal)
    (hp : (ρ.residueCharacteristic w : 𝓞 F) ∉ P)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P] :
    let g := NumberField.geometricFrobenius F (AlgebraicClosure F) P Q
    LinearMap.trace (w.adicCompletion E) (Fin 2 → w.adicCompletion E) (ρ.action w g) =
        algebraMap E (w.adicCompletion E) (-(ρ.polynomial q).coeff 1) ∧
      (ρ.action w g).det = algebraMap E (w.adicCompletion E) ((ρ.polynomial q).coeff 0) := by
  exact trace_det_of_rankTwo_charpoly_map (Pi.basisFun _ (Fin 2)) _ _ _
    (ρ.frobenius_charpoly w q hq P hP hp Q)

end HilbertModularity
