/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.HypergeometricPrimeTorsion
public import HilbertModularity.Geometry.GroupScheme.KernelBaseChange
public import HilbertModularity.Geometry.GroupScheme.CoefficientKernelAction
public import HilbertModularity.Geometry.Etale.GroupSchemeCoefficients
public import HilbertModularity.Geometry.GroupScheme.KernelLocalSystem
public import HilbertModularity.Geometry.Etale.FiniteCoefficientLocalSystem
public import HilbertModularity.Geometry.Etale.LocalSystem.Dual
public import HilbertModularity.RepresentationTheory.Duality

/-! # The finite étale canonical-prime kernel of the chosen family

The canonical-prime torsion is one actual finite étale group scheme over the
punctured parameter line. Its actual fibre is isomorphic to the canonical-prime
kernel of the same chosen fibre. The comparison commutes with the kernel
inclusions. The existing named Darmon existence dependency remains explicit.
See [TripathiGoswami].
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NumberField TensorProduct

namespace HilbertModularity.Hypergeometric

open HilbertModularity.Cyclotomic AlgebraicGeometry.GroupScheme

variable (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)

/-- The actual canonical-prime kernel of the one chosen Darmon family over its parameter scheme. -/
def darmonPrimeKernelFamily : CommGrp (Over (ProjectiveLine.punctured (realCyclotomicField p))) :=
  CommGrp.pullbackKernel (darmonRealMultiplication p hp (realPrimeGenerator p))

/-- The chosen canonical-prime torsion family is finite over the punctured parameter line. -/
instance darmonPrimeKernelFamily_isFinite : IsFinite (darmonPrimeKernelFamily p hp).X.hom :=
  coefficientKernel_isFinite (darmonFamily p hp) (𝓞 (realCyclotomicField p))
    (darmonRealMultiplication p hp) p (realPrimeGenerator p) (realPrimeCofactor p (by omega))
      (realPrimeGenerator_mul_cofactor p (by omega))

/-- The chosen canonical-prime torsion family is étale over the punctured parameter line. -/
instance darmonPrimeKernelFamily_etale : Etale (darmonPrimeKernelFamily p hp).X.hom :=
  coefficientKernel_etale (darmonFamily p hp) (𝓞 (realCyclotomicField p))
    (darmonRealMultiplication p hp) p (realPrimeGenerator p) (realPrimeCofactor p (by omega))
      (realPrimeGenerator_mul_cofactor p (by omega))

section FiniteEtale

attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory

/-- The actual chosen canonical-prime kernel as a finite étale group object. -/
def darmonPrimeFiniteEtaleKernelFamily :
    CommGrp (ProjectiveLine.punctured (realCyclotomicField p)).FiniteEtale :=
  Scheme.finiteEtaleGroupObject (darmonPrimeKernelFamily p hp)

end FiniteEtale

/-- The actual canonical-prime kernel family carries its canonical residue-ring action by scheme endomorphisms. -/
def darmonPrimeKernelFamilyResidueAction :
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) →+*
      End (darmonPrimeKernelFamily p hp) :=
  coefficientKernelResidueAction (darmonFamily p hp) (𝓞 (realCyclotomicField p))
    (darmonRealMultiplication p hp) (realPrimeGenerator p)

variable (ξ : ProjectiveLine.Parameter (realCyclotomicField p))

/-- The fibre of the actual canonical-prime kernel family is the kernel of the actual chosen fibre. -/
def darmonPrimeKernelFamilyFiberIso :
    parameterFiber (realCyclotomicField p) (darmonPrimeKernelFamily p hp) ξ ≅
      darmonPrimeKernel p hp ξ :=
  kernelBaseChangeIso (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    (darmonRealMultiplication p hp (realPrimeGenerator p))

/-- The actual base-change comparison at this chosen parameter preserves the kernel inclusion. -/
theorem darmonPrimeKernelFamilyFiberIso_inclusion :
    (kernelBaseChangeIso (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
      (darmonRealMultiplication p hp (realPrimeGenerator p))).hom.hom.hom.hom ≫
        Grp.kernelInclusion
          ((Over.pullback (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).mapCommGrp.map
            (darmonRealMultiplication p hp (realPrimeGenerator p))).hom =
      (Over.pullback (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).map
        (Grp.kernelInclusion (darmonRealMultiplication p hp (realPrimeGenerator p)).hom) :=
  kernelBaseChangeIso_inclusion (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)
    (darmonRealMultiplication p hp (realPrimeGenerator p))

/-- The residue-ring action on the actual chosen fibre kernel is induced by its actual real multiplication. -/
def darmonPrimeKernelResidueAction :
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) →+*
      End (darmonPrimeKernel p hp ξ) :=
  coefficientKernelResidueAction (darmonPrimeFiber p hp ξ) (𝓞 (realCyclotomicField p))
    (darmonPrimeFiberRealMultiplication p hp ξ) (realPrimeGenerator p)

/-- On geometric points the actual scheme action agrees with the canonical residual module action. -/
theorem darmonPrimeKernelResidueAction_points
    (c : 𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
    (x : Points (realCyclotomicField p) (AlgebraicClosure (realCyclotomicField p))
      (darmonPrimeKernel p hp ξ).X) :
    letI := darmonPrimeKernelModule p hp ξ
    pointsMap (realCyclotomicField p) (AlgebraicClosure (realCyclotomicField p))
      (darmonPrimeKernelResidueAction p hp ξ c).hom.hom.hom x = c • x :=
  coefficientKernelResidueAction_points (𝓞 (realCyclotomicField p)) (realPrimeGenerator p)
    (realCyclotomicField p) (darmonPrimeFiber p hp ξ)
      (darmonPrimeFiberRealMultiplication p hp ξ) c x

/-- The canonical-prime kernel comparison intertwines the actual residue-ring scheme actions. -/
theorem darmonPrimeKernelResidueAction_fiber
    (c : 𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) :
    let x := ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ
    let ψ := (fiberEndomorphismMap (realCyclotomicField p) (darmonFamily p hp) x).comp
      (darmonRealMultiplication p hp)
    (Over.pullback x).mapCommGrp.map
        (coefficientKernelResidueAction (darmonFamily p hp) (𝓞 (realCyclotomicField p))
          (darmonRealMultiplication p hp) (realPrimeGenerator p) c) ≫
        (kernelBaseChangeIso x (darmonRealMultiplication p hp (realPrimeGenerator p))).hom =
      (kernelBaseChangeIso x (darmonRealMultiplication p hp (realPrimeGenerator p))).hom ≫
        coefficientKernelResidueAction (fiber (realCyclotomicField p) (darmonFamily p hp) x)
          (𝓞 (realCyclotomicField p)) ψ (realPrimeGenerator p) c :=
  coefficientKernelResidueAction_fiber (darmonFamily p hp) (𝓞 (realCyclotomicField p))
    (darmonRealMultiplication p hp) (realPrimeGenerator p) (realCyclotomicField p)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) c

/-- The actual canonical-prime kernel family gives one residue-coefficient-linear local system. -/
def darmonPrimeKernelLocalSystem :
    Scheme.EtaleFiberGroupoid (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p)) ⥤
        ModuleCat (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) :=
  Scheme.finiteEtaleCoefficientLocalSystem (realCyclotomicField p) (darmonPrimeKernelFamily p hp)
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
      (darmonPrimeKernelFamilyResidueAction p hp)

/-- Arithmetic loops in the actual canonical-prime local system act by the original Galois action on its points. -/
theorem darmonPrimeKernelLocalSystem_arithmetic
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p))
    (v : Additive (Scheme.geometricPointOver (realCyclotomicField p)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) ⟶ (darmonPrimeKernelFamily p hp).X)) :
    ((darmonPrimeKernelLocalSystem p hp).map
      (Scheme.arithmeticFiberLoop (realCyclotomicField p)
        (ProjectiveLine.punctured (realCyclotomicField p))
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) g) v).toMul =
      Scheme.arithmeticFiberPointMap (realCyclotomicField p)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) g ≫ v.toMul :=
  Scheme.finiteEtaleCoefficientLocalSystem_arithmetic (realCyclotomicField p)
    (darmonPrimeKernelFamily p hp) (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
    (darmonPrimeKernelFamilyResidueAction p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) g v

/-- The linear local-system fibre is the actual point module of the pulled-back canonical-prime kernel family. -/
def darmonPrimeKernelLocalSystemFiberEquiv :
    let x := ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ
    letI := pointsCoefficientModule (realCyclotomicField p)
      (fiber (realCyclotomicField p) (darmonPrimeKernelFamily p hp) x)
      (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
      ((fiberEndomorphismMap (realCyclotomicField p) (darmonPrimeKernelFamily p hp) x).comp
        (darmonPrimeKernelFamilyResidueAction p hp))
    (darmonPrimeKernelLocalSystem p hp).obj x ≃ₗ[
      𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}]
      Points (realCyclotomicField p) (AlgebraicClosure (realCyclotomicField p))
        (fiber (realCyclotomicField p) (darmonPrimeKernelFamily p hp) x).X :=
  Scheme.finiteEtaleCoefficientFiberEquiv (realCyclotomicField p) (darmonPrimeKernelFamily p hp)
    (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
    (darmonPrimeKernelFamilyResidueAction p hp)
    (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)

/-- The arithmetic fibre of the chosen kernel local system is the actual chosen canonical-prime kernel representation. -/
def darmonPrimeKernelLocalSystemRepresentationEquiv :
    letI := darmonPrimeKernelModule p hp ξ
    (Scheme.arithmeticFiberRepresentation (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p)) (darmonPrimeKernelLocalSystem p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
        (darmonPrimeKernelRepresentation p hp ξ) := by
  letI : IsFinite (CommGrp.pullbackKernel
      (darmonRealMultiplication p hp (realPrimeGenerator p))).X.hom :=
    darmonPrimeKernelFamily_isFinite p hp
  letI : Etale (CommGrp.pullbackKernel
      (darmonRealMultiplication p hp (realPrimeGenerator p))).X.hom :=
    darmonPrimeKernelFamily_etale p hp
  exact coefficientKernelLocalSystemRepresentationEquiv (darmonFamily p hp)
    (𝓞 (realCyclotomicField p)) (darmonRealMultiplication p hp) (realPrimeGenerator p)
    (realCyclotomicField p) (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)

/-- Reduction of the actual chosen integral Tate lattice is the arithmetic fibre of its actual canonical-prime kernel local system. -/
def darmonPrimeResidualLocalSystemEquiv :
    letI := darmonPrimeIntegralTateModule p hp ξ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p})).toRingHom.toAlgebra
    ((darmonPrimeIntegralTateRepresentation p hp ξ).baseChange
      (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})).Equiv
      (Scheme.arithmeticFiberRepresentation (realCyclotomicField p)
        (ProjectiveLine.punctured (realCyclotomicField p)) (darmonPrimeKernelLocalSystem p hp)
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
  letI := darmonPrimeIntegralTateModule p hp ξ
  letI := darmonPrimeKernelModule p hp ξ
  letI := (AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p})).toRingHom.toAlgebra
  exact (darmonPrimeResidualKernelEquiv p hp ξ).trans
    (darmonPrimeKernelLocalSystemRepresentationEquiv p hp ξ).symm

/-- The determinant of the actual chosen kernel local system is the residue of the determinant on the actual integral Tate lattice. -/
theorem det_darmonPrimeKernelLocalSystem
    (g : AlgebraicClosure (realCyclotomicField p) ≃ₐ[realCyclotomicField p]
      AlgebraicClosure (realCyclotomicField p)) :
    letI := darmonPrimeIntegralTateModule p hp ξ
    LinearMap.det (Scheme.arithmeticFiberRepresentation (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p)) (darmonPrimeKernelLocalSystem p hp)
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) g) =
      AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p})
        (LinearMap.det (darmonPrimeIntegralTateRepresentation p hp ξ g)) := by
  let := darmonPrimeIntegralTateModule p hp ξ
  let := darmonPrimeKernelModule p hp ξ
  let : IsFinite (CommGrp.pullbackKernel
      (darmonRealMultiplication p hp (realPrimeGenerator p))).X.hom :=
    darmonPrimeKernelFamily_isFinite p hp
  let : Etale (CommGrp.pullbackKernel
      (darmonRealMultiplication p hp (realPrimeGenerator p))).X.hom :=
    darmonPrimeKernelFamily_etale p hp
  exact (det_coefficientKernelLocalSystem (darmonFamily p hp)
    (𝓞 (realCyclotomicField p)) (darmonRealMultiplication p hp) (realPrimeGenerator p)
    (realCyclotomicField p) (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) g).trans
      (det_darmonPrimeKernel p hp ξ g)

/-- The actual canonical-prime kernel family is a continuous finite-dimensional étale local system over its canonical residue field. -/
def darmonPrimeKernelEtaleLocalSystem :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
    Scheme.EtaleLocalSystem (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p))
      (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
  letI := realPrimeGenerator_isMaximal p (by omega)
  letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
  letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
  letI : DiscreteTopology (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⟨rfl⟩
  exact Scheme.finiteCoefficientEtaleLocalSystem (realCyclotomicField p)
    (darmonPrimeKernelFamily p hp) (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
    (darmonPrimeKernelFamilyResidueAction p hp)

/-- The continuous chosen kernel family retains exactly its actual residue-coefficient point functor. -/
theorem darmonPrimeKernelEtaleLocalSystem_algebraicFunctor :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
    (darmonPrimeKernelEtaleLocalSystem p hp).algebraicFunctor =
      darmonPrimeKernelLocalSystem p hp := rfl

/-- Arithmetic specialization of the continuous chosen kernel family is the same actual canonical-prime kernel representation. -/
def darmonPrimeKernelEtaleLocalSystemRepresentationEquiv :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
    letI := darmonPrimeKernelModule p hp ξ
    ((darmonPrimeKernelEtaleLocalSystem p hp).arithmeticRepresentation
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
        (darmonPrimeKernelRepresentation p hp ξ) :=
  darmonPrimeKernelLocalSystemRepresentationEquiv p hp ξ

/-- The actual contragredient continuous family of the canonical-prime kernel. This definition does not identify it with étale cohomology. -/
def darmonPrimeKernelDualEtaleLocalSystem :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
    Scheme.EtaleLocalSystem (realCyclotomicField p)
      (ProjectiveLine.punctured (realCyclotomicField p))
      (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := by
  letI := realPrimeGenerator_isMaximal p (by omega)
  letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
  letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
  letI : DiscreteTopology (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⟨rfl⟩
  letI : Finite (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) :=
    Finite.of_equiv (ZMod p) (realPrimeResidueEquiv p (by omega)).symm.toEquiv
  exact (darmonPrimeKernelEtaleLocalSystem p hp).dual

/-- Arithmetic specialization of the actual dual family is the actual canonical-prime kernel dual. -/
def darmonPrimeKernelDualEtaleLocalSystemRepresentationEquiv :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
    letI := darmonPrimeKernelModule p hp ξ
    ((darmonPrimeKernelDualEtaleLocalSystem p hp).arithmeticRepresentation
      (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)).Equiv
        (darmonPrimeKernelRepresentation p hp ξ).dual := by
  letI := realPrimeGenerator_isMaximal p (by omega)
  letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
  letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
  letI : DiscreteTopology (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⟨rfl⟩
  letI : Finite (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) :=
    Finite.of_equiv (ZMod p) (realPrimeResidueEquiv p (by omega)).symm.toEquiv
  letI := darmonPrimeKernelModule p hp ξ
  let e := representationDualEquiv (darmonPrimeKernelEtaleLocalSystemRepresentationEquiv p hp ξ)
  refine .mk e.toLinearEquiv ?_
  intro g
  change e.toLinearEquiv.toLinearMap ∘ₗ
      ((darmonPrimeKernelEtaleLocalSystem p hp).dual.arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ) g) = _
  rw [Scheme.EtaleLocalSystem.dual_arithmeticRepresentation]
  exact e.isIntertwining' g

/-- Reduction of the actual integral Tate dual is the arithmetic fibre of the same continuous contragredient kernel family. -/
def darmonPrimeResidualDualLocalSystemEquiv :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
    letI := darmonPrimeIntegralTateModule p hp ξ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p})).toRingHom.toAlgebra
    ((darmonPrimeIntegralTateRepresentation p hp ξ).dual.baseChange
      (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})).Equiv
      ((darmonPrimeKernelDualEtaleLocalSystem p hp).arithmeticRepresentation
        (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) := by
  letI := realPrimeGenerator_isMaximal p (by omega)
  letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
  letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
  letI := darmonPrimeIntegralTateModule p hp ξ
  letI := darmonPrimeKernelModule p hp ξ
  letI := (AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p})).toRingHom.toAlgebra
  exact (darmonPrimeResidualDualKernelEquiv p hp ξ).trans
    (darmonPrimeKernelDualEtaleLocalSystemRepresentationEquiv p hp ξ).symm

/-- The two actual local-system reduction comparisons preserve the integral Tate evaluation pairing after taking its residue. -/
theorem darmonPrimeResidualDualLocalSystemEquiv_tmul
    (c : 𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
    (f : letI := darmonPrimeIntegralTateModule p hp ξ
      Module.Dual (AdicCompletion (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p)))
        (integralTate (realCyclotomicField p) (darmonPrimeFiber p hp ξ).X p))
    (x : integralTate (realCyclotomicField p) (darmonPrimeFiber p hp ξ).X p) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
    letI : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
    letI := darmonPrimeIntegralTateModule p hp ξ
    letI := (AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p})).toRingHom.toAlgebra
    (show Module.Dual (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
        ((darmonPrimeKernelLocalSystem p hp).obj
          (ProjectiveLine.puncturedPoint (realCyclotomicField p) ξ)) from
      darmonPrimeResidualDualLocalSystemEquiv p hp ξ
        (c ⊗ₜ[AdicCompletion (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))] f))
      (darmonPrimeResidualLocalSystemEquiv p hp ξ
        ((1 : 𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p})
          ⊗ₜ[AdicCompletion (Ideal.span {realPrimeGenerator p}) (𝓞 (realCyclotomicField p))] x)) =
      c * AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p}) (f x) := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field (Ideal.span {realPrimeGenerator p})
  let : TopologicalSpace (𝓞 (realCyclotomicField p) ⧸ Ideal.span {realPrimeGenerator p}) := ⊥
  let := darmonPrimeIntegralTateModule p hp ξ
  let := darmonPrimeKernelModule p hp ξ
  let := (AdicCompletion.evalOneₐ (Ideal.span {realPrimeGenerator p})).toRingHom.toAlgebra
  change darmonPrimeResidualDualKernelEquiv p hp ξ (c ⊗ₜ[_] f)
    ((darmonPrimeKernelLocalSystemRepresentationEquiv p hp ξ)
      ((darmonPrimeKernelLocalSystemRepresentationEquiv p hp ξ).symm
        (darmonPrimeResidualKernelEquiv p hp ξ ((1 : _) ⊗ₜ[_] x)))) = _
  have h := (darmonPrimeKernelLocalSystemRepresentationEquiv p hp ξ).apply_symm_apply
    (darmonPrimeResidualKernelEquiv p hp ξ ((1 : _) ⊗ₜ[_] x))
  exact (congrArg (fun z => darmonPrimeResidualDualKernelEquiv p hp ξ (c ⊗ₜ[_] f) z) h).trans
    (realPrimeResidualDualKernelEquiv_tmul (realCyclotomicField p)
      (darmonPrimeFiber p hp ξ) p (by omega) (darmonPrimeFiberRealMultiplication p hp ξ) c f x)

local notation "Fₚ" => realCyclotomicField p
local notation "Rₚ" => 𝓞 Fₚ
local notation "Pₚ" => Ideal.span {realPrimeGenerator p}
local notation "kₚ" => Rₚ ⧸ Pₚ


/-- Actual kernel fixed-point, rank and cyclotomic-determinant inputs give the inverse-cyclotomic flag on the actual dual family fibre. -/
theorem exists_darmonPrimeKernelLocalSystem_dual_factors
    (v : Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X) (hv : v ≠ 0)
    (hfix : ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ, g • v = v)
    (hrank : letI := realPrimeGenerator_isMaximal p (by omega)
      letI := Ideal.Quotient.field Pₚ
      letI := darmonPrimeKernelModule p hp ξ
      Module.finrank kₚ (Points Fₚ (AlgebraicClosure Fₚ) (darmonPrimeKernel p hp ξ).X) = 2)
    (hdet : letI := darmonPrimeKernelModule p hp ξ
      ∀ g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ,
        realPrimeResidueEquiv p (by omega)
          (LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g)) =
            (Field.cyclotomicCharacter Fₚ p g : ℤ_[p]).toZMod) :
    letI := realPrimeGenerator_isMaximal p (by omega)
    letI := Ideal.Quotient.field Pₚ
    let ρ := Scheme.arithmeticFiberRepresentation Fₚ (ProjectiveLine.punctured Fₚ)
      (darmonPrimeKernelLocalSystem p hp) (ProjectiveLine.puncturedPoint Fₚ ξ)
    ∃ T : Subrepresentation ρ.dual,
      Module.finrank kₚ T.toSubmodule = 1 ∧
      Module.finrank kₚ (Module.Dual kₚ ((darmonPrimeKernelLocalSystem p hp).obj (ProjectiveLine.puncturedPoint Fₚ ξ)) ⧸ T.toSubmodule) = 1 ∧
      Representation.IsIrreducible (k := kₚ)
        (G := AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) (V := T.toSubmodule)
        T.toRepresentation ∧
      Representation.IsIrreducible (k := kₚ)
        (G := AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
        (V := Module.Dual kₚ ((darmonPrimeKernelLocalSystem p hp).obj (ProjectiveLine.puncturedPoint Fₚ ξ)) ⧸ T.toSubmodule)
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule) ∧
      Representation.IsSemisimpleRepresentation (k := kₚ)
        (G := AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ)
        (V := T.toSubmodule × (Module.Dual kₚ ((darmonPrimeKernelLocalSystem p hp).obj (ProjectiveLine.puncturedPoint Fₚ ξ)) ⧸ T.toSubmodule))
        (T.toRepresentation.prod
          (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)) ∧
      Nonempty ((T.toRepresentation.prod
        (ρ.dual.quotient T.toSubmodule T.apply_mem_toSubmodule)).Equiv
          ((Representation.ofCharacter (K := kₚ) (1 :
            (AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) →* kₚˣ)).prod
              (Representation.ofCharacter (K := kₚ)
                (realPrimeResidualCyclotomicCharacter Fₚ p (by omega))⁻¹))) := by
  let := realPrimeGenerator_isMaximal p (by omega)
  let := Ideal.Quotient.field Pₚ
  let := darmonPrimeKernelModule p hp ξ
  let := darmonPrimeIntegralTateModule p hp ξ
  let ρ := Scheme.arithmeticFiberRepresentation Fₚ (ProjectiveLine.punctured Fₚ)
    (darmonPrimeKernelLocalSystem p hp) (ProjectiveLine.puncturedPoint Fₚ ξ)
  let E := darmonPrimeKernelLocalSystemRepresentationEquiv p hp ξ
  have hr : Module.finrank kₚ ((darmonPrimeKernelLocalSystem p hp).obj (ProjectiveLine.puncturedPoint Fₚ ξ)) = 2 := E.toLinearEquiv.finrank_eq.trans hrank
  have := Module.finite_of_finrank_eq_succ hr
  let w := E.symm v
  have hw : w ≠ 0 := by
    intro h
    have := congrArg E h
    exact hv (by simpa only [w, Representation.Equiv.apply_symm_apply, map_zero] using this)
  have hfw (g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) : ρ g w = w := by
    have h := E.symm.toIntertwiningMap.isIntertwining
      (darmonPrimeKernelRepresentation p hp ξ) ρ g v
    change E.symm (g • v) = ρ g w at h
    rw [hfix g] at h
    exact h.symm
  have hd (g : AlgebraicClosure Fₚ ≃ₐ[Fₚ] AlgebraicClosure Fₚ) :
      LinearMap.det (ρ g) = LinearMap.det (darmonPrimeKernelRepresentation p hp ξ g) :=
    (det_darmonPrimeKernelLocalSystem p hp ξ g).trans (det_darmonPrimeKernel p hp ξ g).symm
  have hχ : ρ.determinantCharacter = realPrimeResidualCyclotomicCharacter Fₚ p (by omega) := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply (realPrimeResidueEquiv p (by omega)).injective
    change realPrimeResidueEquiv p (by omega) (LinearMap.det (ρ g)) = _
    rw [hd g]
    exact (hdet g).trans (realPrimeResidualCyclotomicCharacter_residue Fₚ p (by omega) g).symm
  simpa only [hχ] using ρ.exists_dual_fixedLine_factors hr w hw hfw

end HilbertModularity.Hypergeometric
