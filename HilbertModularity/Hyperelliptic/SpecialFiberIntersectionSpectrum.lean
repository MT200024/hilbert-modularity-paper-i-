/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingDecomposition
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Spectrum of the finite crossing divisor

The Chinese remainder equivalence identifies the underlying topological space
of the finite intersection with a disjoint union of spectra of the residue
field. This uses the actual branch quotient of the scaled special fibre.
It does not assert that the ambient curve is nodal at those points.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

/-- Every point of the split finite branch divisor lies on exactly one of
the listed field factors, with the spectrum topology transported by CRT. -/
def quotientSpanProdXSubC_spectrumHomeomorph (S : Finset k) :
    PrimeSpectrum (k[X] ⧸ Ideal.span {∏ x ∈ S, (X - C x)}) ≃ₜ
      (Σ _ : S, PrimeSpectrum k) :=
  (PrimeSpectrum.homeomorphOfRingEquiv (quotientSpanProdXSubCEquiv S)).trans
    (PrimeSpectrum.sigmaToPiHomeo (fun _ : S => k)).symm

/-- The actual cyclotomic finite intersection has one field-spectrum factor
for the origin and for each nonzero residue root. -/
def reducedLocalFiniteComponentIntersection_spectrumHomeomorph
    (p : ℕ) [Fact p.Prime] :
    PrimeSpectrum (componentIntersectionRing (finiteComponentPolynomial
      ((localScaledRootPolynomial p (Cyclotomic.realPrimeAboveConductor p)).map
        (Cyclotomic.realLocalReduction p)))) ≃ₜ
      (Σ _ : ↥(insert (0 : ZMod p) (residueRootSet p)), PrimeSpectrum (ZMod p)) :=
  (PrimeSpectrum.homeomorphOfRingEquiv
    (reducedLocalFiniteComponentIntersectionEquiv p)).trans
      (PrimeSpectrum.sigmaToPiHomeo
        (fun _ : ↥(insert (0 : ZMod p) (residueRootSet p)) => ZMod p)).symm

end HilbertModularity.Hyperelliptic
