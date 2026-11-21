/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Adelic groups for Hilbert modular forms

The diagonal rational group, additive quotient and upper unipotent subgroup are
the groups used in the adelic definition of Hilbert cusp forms. The coefficient
ring is the actual number-field adele ring of Mathlib. See [SkinnerWiles,
§4.5] for the automorphic objects used in the modularity argument.
-/

public noncomputable section

open NumberField

namespace HilbertModularity.HilbertModularForms

variable (F : Type*) [Field F] [NumberField F]

/-- The full adele ring of a number field. -/
abbrev AdeleRing := NumberField.AdeleRing (𝓞 F) F

/-- The adelic general linear group in rank two. -/
abbrev AdelicGL2 := GL (Fin 2) (AdeleRing F)

/-- The diagonal copy of the rational general linear group in the adelic group. -/
def rationalDiagonal : GL (Fin 2) F →* AdelicGL2 F :=
  Matrix.GeneralLinearGroup.map (algebraMap F (AdeleRing F))

/-- The additive subgroup of principal adeles. -/
def principalAdeles : AddSubgroup (AdeleRing F) :=
  (algebraMap F (AdeleRing F)).toAddMonoidHom.range

/-- The additive adelic quotient used in the cuspidal constant term. -/
abbrev AdditiveAdeleQuotient := AdeleRing F ⧸ principalAdeles F

/-- The matrix `[[1,x],[0,1]]` over the adele ring. -/
def upperUnipotentMatrix (x : AdeleRing F) :
    Matrix (Fin 2) (Fin 2) (AdeleRing F) :=
  1 + Matrix.single 0 1 x

@[simp]
theorem upperUnipotentMatrix_det (x : AdeleRing F) :
    (upperUnipotentMatrix F x).det = 1 := by
  simp [upperUnipotentMatrix, Matrix.det_fin_two]

/-- The upper unipotent element associated to an adele. -/
def upperUnipotent (x : AdeleRing F) : AdelicGL2 F :=
  Matrix.GeneralLinearGroup.mk' (upperUnipotentMatrix F x) (by
    rw [upperUnipotentMatrix_det]
    exact ⟨1, by simp, by simp⟩)

/-- The determinant of an adelic invertible matrix, as an idele. -/
def adelicDeterminant : AdelicGL2 F →* (AdeleRing F)ˣ :=
  Matrix.GeneralLinearGroup.det

/-- Central scalar matrices in the adelic general linear group. -/
def centralScalar : (AdeleRing F)ˣ →* AdelicGL2 F :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)

@[simp]
theorem adelicDeterminant_centralScalar (z : (AdeleRing F)ˣ) :
    adelicDeterminant F (centralScalar F z) = z ^ 2 := by
  exact Matrix.GeneralLinearGroup.det_scalar z

@[simp]
theorem adelicDeterminant_upperUnipotent (x : AdeleRing F) :
    adelicDeterminant F (upperUnipotent F x) = 1 := by
  apply Units.ext
  simp [adelicDeterminant, upperUnipotent, upperUnipotentMatrix_det]

end HilbertModularity.HilbertModularForms
