/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.PrimeCompletion
public import HilbertModularity.Algebra.AdicCompletion.Padic
public import HilbertModularity.NumberTheory.CyclotomicCharacter

/-! # Residues of rational-prime scalars at an RM prime

The canonical map from the p-adic integers to the completed RM coefficients
reduces to the ordinary mod-p map. Thus specializing a cyclotomic determinant
uses the actual residue character; see [TripathiGoswami].
-/

@[expose] public noncomputable section

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R]

/-- Canonical p-adic scalars at a ramified principal coefficient prime have the usual mod-p residue. -/
theorem coefficientPrimeRingEquiv_padic_residue
    (a b : R) (hab : a * b = (p : R))
    (e : ℕ) (he : 0 < e) (hJ : (Ideal.span {a}) ^ e = Ideal.span {(p : R)})
    (ι : ZMod p →+* R ⧸ Ideal.span {a}) (z : ℤ_[p]) :
    AdicCompletion.evalOneₐ (Ideal.span {a})
      (coefficientPrimeRingEquiv p R (Ideal.span {a}) e he hJ
        (PadicInt.toAdicCompletion p R z)) = ι z.toZMod := by
  rw [coefficientPrimeRingEquiv_residue p R a b hab]
  let q : R ⧸ (Ideal.span {(p : R)}) ^ 1 →+* R ⧸ Ideal.span {a} :=
    (Ideal.Quotient.factor (show Ideal.span {(p : R)} ≤ Ideal.span {a} from by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      exact ⟨b, hab.symm⟩)).comp
        (Ideal.Quotient.factor (show (Ideal.span {(p : R)}) ^ 1 ≤ Ideal.span {(p : R)} by simp))
  change q (AdicCompletion.evalₐ (Ideal.span {(p : R)}) 1
    (PadicInt.toAdicCompletion p R z)) = _
  rw [PadicInt.evalₐ_toAdicCompletion]
  have h : q.comp (AdicCompletion.zmodToQuotient p R 1) =
      ι.comp (ZMod.castHom (show p ∣ p ^ 1 by simp) (ZMod p)) := Subsingleton.elim _ _
  exact (RingHom.congr_fun h (z.toZModPow 1)).trans
    (congrArg ι (PadicInt.cast_toZModPow_one p z))

end TateModule
