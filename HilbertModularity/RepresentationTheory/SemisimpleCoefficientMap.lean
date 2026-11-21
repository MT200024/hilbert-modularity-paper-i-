/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.CoefficientMap
public import Mathlib.RepresentationTheory.Semisimple

/-! # Semisimplicity under coefficient extension

The finite-dimensional image algebra, rather than finiteness of the group,
controls extension of scalars. This is the standard perfect-field separability
input used when enlarging the coefficient field in compatible-system promotion.
-/

public section

namespace Representation

/-- A finite-dimensional semisimple representation in characteristic zero remains
semisimple under extension of its coefficient field.

Literature input: [Sharafdini2008, p. 5, Theorem 2.6], explicitly citing
[NagaoTsushima1989, Theorem II.5.4]: a finite-dimensional semisimple algebra over
a perfect field is separable. Apply this to the image of the group algebra in
`End_K(K^n)`. The original faithful semisimple module forces that image algebra's
radical to vanish. Characteristic zero makes `K` perfect; separability makes the
extended image algebra semisimple, so its extended module is semisimple.
In the displayed coordinates its group action is exactly `mapCoefficients`.
This standard representation corollary, including the image-algebra argument,
is admitted here; the cited theorem itself is an algebra statement.
No finiteness assumption on `G` is imposed or used. -/
theorem isSemisimple_mapCoefficients
    {K L G n : Type*} [Field K] [CharZero K] [Field L] [Group G]
    [Fintype n] [DecidableEq n]
    (f : K →+* L) (ρ : Representation K G (n → K))
    (hρ : ρ.IsSemisimpleRepresentation) :
    (ρ.mapCoefficients f).IsSemisimpleRepresentation := by
  sorry

end Representation
