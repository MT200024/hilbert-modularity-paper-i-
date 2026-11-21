/- Assembled by AxiomProver. -/

module

public import HilbertModularity.RepresentationTheory.FiniteAlgebraicCharacter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Continuity of finite characters at every coefficient embedding

One continuous faithful completion realization of a finite character makes the
algebraic character locally constant. Every other coefficient realization is
therefore continuous, without continuity of the coefficient embedding itself.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity

variable {F A : Type*} [Field F] [NumberField F] [Field A] [NumberField A]

/-- A finite algebraic character is locally constant, using any one of its
faithful continuous completion realizations. -/
theorem FiniteAlgebraicGaloisCharacter.isLocallyConstant
    (χ : FiniteAlgebraicGaloisCharacter F A) :
    IsLocallyConstant χ.toMonoidHom := by
  let e := Rat.HeightOneSpectrum.primesEquiv (R := ℤ)
  let : Nontrivial (HeightOneSpectrum ℤ) := ⟨⟨e.symm ⟨2, by decide⟩,
    e.symm ⟨3, by decide⟩, fun h => by
      have : (2 : ℕ) = 3 := congrArg Subtype.val (e.symm.injective h)
      exact (by decide : (2 : ℕ) ≠ 3) this⟩⟩
  let : Nontrivial (HeightOneSpectrum (𝓞 A)) :=
    Algebra.IsIntegral.nontrivial_heightOneSpectrum (R := ℤ) (A := 𝓞 A)
  let w : HeightOneSpectrum (𝓞 A) := Classical.choice inferInstance
  let j : Aˣ → w.adicCompletion A := fun u => algebraMap A (w.adicCompletion A) u
  have hj : Function.Injective j := (algebraMap A (w.adicCompletion A)).injective.comp
    Units.val_injective
  have hf : (Set.range (j ∘ χ.toMonoidHom)).Finite := by
    rw [Set.range_comp]
    exact χ.finite_range.image j
  let : Finite (Set.range (j ∘ χ.toMonoidHom)) := hf.to_subtype
  have hc : Continuous (j ∘ χ.toMonoidHom) := χ.local_continuous w
  have hlc : IsLocallyConstant
      (fun g => (⟨j (χ.toMonoidHom g), Set.mem_range_self g⟩ :
        Set.range (j ∘ χ.toMonoidHom))) :=
    (IsLocallyConstant.iff_continuous _).mpr (hc.subtype_mk _)
  have h := hlc.comp (fun u => Function.invFun j u.val)
  have heq : (fun g => Function.invFun j (j (χ.toMonoidHom g))) = χ.toMonoidHom :=
    funext (fun g => Function.leftInverse_invFun hj (χ.toMonoidHom g))
  simpa only [Function.comp_def, heq] using h

/-- Finite-character continuity does not require a topological coefficient
embedding: local constancy is preserved by every function on the finite image. -/
theorem FiniteAlgebraicGaloisCharacter.continuous_embedding
    (χ : FiniteAlgebraicGaloisCharacter F A)
    {E : Type*} [Field E] [TopologicalSpace E] (ι : A →+* E) :
    Continuous (fun g => ι (χ.toMonoidHom g : A)) :=
  (χ.isLocallyConstant.comp (fun u : Aˣ => ι (u : A))).continuous

end HilbertModularity
