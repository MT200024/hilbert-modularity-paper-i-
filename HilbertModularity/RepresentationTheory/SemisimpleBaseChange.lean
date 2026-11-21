/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.SemisimpleCoefficientMap
public import HilbertModularity.RepresentationTheory.SemisimpleTransport
public import HilbertModularity.RepresentationTheory.ScalarExtension
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Semisimplicity of the actual scalar extension

Basis coordinates identify tensor extension with the coefficient-map construction.
The sole literature premise is the existing perfect-field separability input.
-/

public noncomputable section

open scoped TensorProduct

namespace Representation

variable {K G V ι : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

/-- The action written in a specified basis. -/
def inBasis (ρ : Representation K G V) (b : Module.Basis ι K V) :
    Representation K G (ι → K) :=
  b.equivFun.conjRingEquiv.toMonoidHom.comp ρ

/-- The standard function basis leaves an action on its coordinates unchanged. -/
theorem inBasis_pi
    {K G : Type*} [Field K] [Group G]
    (ρ : Representation K G (Fin 2 → K)) :
    ρ.inBasis (Pi.basisFun K (Fin 2)) = ρ := by
  ext g v i
  simp [inBasis]

/-- Basis coordinates intertwine the actual action and its matrix action. -/
def inBasisEquiv (ρ : Representation K G V) (b : Module.Basis ι K V) :
    ρ.Equiv (ρ.inBasis b) :=
  .mk b.equivFun (by intro g; ext v; simp [inBasis])

/-- Extending basis coordinates gives exactly entrywise extension of the matrices. -/
def baseChangeInBasisEquiv (L : Type*) [Field L] [Algebra K L]
    (ρ : Representation K G V) (b : Module.Basis ι K V) :
    (ρ.baseChange L).Equiv ((ρ.inBasis b).mapCoefficients (algebraMap K L)) := by
  refine .mk (b.baseChange L).equivFun ?_
  intro g
  apply (b.baseChange L).ext
  intro i
  have hb : (b.baseChange L).equivFun ((b.baseChange L) i) = Pi.single i 1 := by
    ext j
    simp only [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  have hb' : b.equivFun.symm (Pi.single i 1) = b i := by
    apply b.equivFun.injective
    ext j
    simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_self,
      Pi.single_apply, eq_comm]
  change (b.baseChange L).equivFun ((ρ.baseChange L g) ((b.baseChange L) i)) =
    (ρ.inBasis b).mapCoefficients (algebraMap K L) g
      ((b.baseChange L).equivFun ((b.baseChange L) i))
  rw [hb]
  ext j
  rw [mapCoefficients_apply_single, Module.Basis.baseChange_apply]
  change (b.baseChange L).repr (1 ⊗ₜ[K] (ρ g (b i))) j =
    algebraMap K L (b.equivFun (ρ g (b.equivFun.symm (Pi.single i 1))) j)
  rw [hb', Module.Basis.baseChange_repr_tmul]
  simp only [Module.Basis.equivFun_apply, Algebra.smul_def, mul_one]

/-- Finite-dimensional semisimple actions in characteristic zero remain
semisimple on their actual tensor extension, by [Sharafdini2008, Theorem 2.6]
as applied in `isSemisimple_mapCoefficients`. -/
theorem isSemisimple_baseChange (L : Type*) [Field L] [Algebra K L]
    [CharZero K] [FiniteDimensional K V]
    (ρ : Representation K G V) (hρ : ρ.IsSemisimpleRepresentation) :
    (ρ.baseChange L).IsSemisimpleRepresentation := by
  classical
  let b := Module.finBasis K V
  have hc := isSemisimple_mapCoefficients (algebraMap K L) (ρ.inBasis b)
    ((ρ.inBasisEquiv b).isSemisimple_iff.mp hρ)
  exact (ρ.baseChangeInBasisEquiv L b).isSemisimple_iff.mpr hc

end Representation
