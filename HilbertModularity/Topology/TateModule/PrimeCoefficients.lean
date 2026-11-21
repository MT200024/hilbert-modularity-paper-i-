/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Algebra.TateModule.CoefficientFinite
public import HilbertModularity.Topology.TateModule.FiniteFree

/-! # Continuity of specialized integral Tate coordinates

Completed RM coordinates, after a compatible specialization, are linear over
the native p-adic integers. Their continuity therefore follows from the actual
finite Tate module topology, without choosing a topology on the RM completion.
-/

public section
noncomputable section

namespace TateModule

variable (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R]
  [AddCommGroup A] [Module R A]
  (J : Ideal R) (e : ℕ) (he : 0 < e)
  (hJ : J ^ e = Ideal.span {(p : R)})

/-- The canonical p-adic scalars act natively after changing to the RM prime. -/
theorem coefficientPrime_smul_padic (z : ℤ_[p]) (x : integral p A) :
    letI := coefficientPrimeModule p R A J e he hJ
    coefficientPrimeRingEquiv p R J e he hJ
      (PadicInt.toAdicCompletion p R z) • x = z • x := by
  let := completedCoefficientModule p R A
  change (coefficientPrimeRingEquiv p R J e he hJ).symm
    (coefficientPrimeRingEquiv p R J e he hJ
      (PadicInt.toAdicCompletion p R z)) • x = z • x
  rw [AlgEquiv.symm_apply_apply]
  exact completedCoefficient_smul_padic p R A z x

variable [TopologicalSpace A] [DiscreteTopology A]
  [Module.Finite ℤ_[p] (integral p A)]
  {E : Type*} [CommRing E] [Algebra ℤ_[p] E]
  [TopologicalSpace E] [IsTopologicalRing E] [ContinuousSMul ℤ_[p] E]

/-- Coordinate continuity uses only compatibility of coefficient scalars with
native p-adic scalars on a finite Tate module. -/
theorem continuous_coordinate_of_padic_smul
    {S : Type*} [CommRing S] [Module S (integral p A)]
    (c : ℤ_[p] → S)
    (hc : ∀ z : ℤ_[p], ∀ x : integral p A, c z • x = z • x)
    (α : S →+* E) (hα : ∀ z, α (c z) = algebraMap ℤ_[p] E z)
    {ι : Type*} (b : Module.Basis ι S (integral p A)) (i : ι) :
    Continuous (fun x : integral p A => α (b.repr x i)) := by
  let f : integral p A →ₗ[ℤ_[p]] E :=
    { toFun := fun x => α (b.repr x i)
      map_add' := fun x y => by simp
      map_smul' := fun z x => by
        rw [← hc z x, map_smul]
        simp only [Finsupp.smul_apply, smul_eq_mul, map_mul, hα,
          RingHom.id_apply, Algebra.smul_def] }
  exact IsModuleTopology.continuous_of_linearMap f

/-- A specialized RM coordinate is continuous if the specialization preserves
the native p-adic scalars. No topology on `AdicCompletion J R` is required. -/
theorem continuous_coefficientPrime_coordinate
    (α : AdicCompletion J R →+* E)
    (hα : ∀ z : ℤ_[p], α (coefficientPrimeRingEquiv p R J e he hJ
      (PadicInt.toAdicCompletion p R z)) = algebraMap ℤ_[p] E z)
    {ι : Type*}
    (b : letI := coefficientPrimeModule p R A J e he hJ
      Module.Basis ι (AdicCompletion J R) (integral p A)) (i : ι) :
    letI := coefficientPrimeModule p R A J e he hJ
    Continuous (fun x : integral p A => α (b.repr x i)) := by
  let := coefficientPrimeModule p R A J e he hJ
  let f : integral p A →ₗ[ℤ_[p]] E :=
    { toFun := fun x => α (b.repr x i)
      map_add' := fun x y => by simp
      map_smul' := fun z x => by
        rw [← coefficientPrime_smul_padic p R A J e he hJ z x,
          map_smul]
        simp only [Finsupp.smul_apply, smul_eq_mul, map_mul, hα,
          RingHom.id_apply, Algebra.smul_def] }
  exact IsModuleTopology.continuous_of_linearMap f

end TateModule
