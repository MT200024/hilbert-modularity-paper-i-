/- Assembled by AxiomProver. -/

module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Integral closure in the generic fibre of a smooth algebra

For an integrally closed domain, smooth base change identifies integral elements
in the generic fibre with elements of the original algebra. This is the ring
comparison used to extend maps of finite étale generic fibres.
-/

@[expose] public section
open scoped TensorProduct
namespace Algebra.TensorProduct
variable (R S F : Type*) [CommRing R] [IsIntegrallyClosed R]
  [CommRing S] [Algebra R S] [Algebra.Smooth R S]
  [Field F] [Algebra R F] [IsFractionRing R F]

omit [IsIntegrallyClosed R] in
/-- The original smooth algebra embeds in its fraction-field base change. -/
theorem includeLeft_injective_of_fractionField :
    Function.Injective (includeLeft : S →ₐ[R] S ⊗[R] F) :=
  includeLeft_injective (IsFractionRing.injective R F)

/-- No new integral elements over the smooth algebra appear in its generic fibre. -/
theorem isIntegral_iff_exists_includeLeft (z : S ⊗[R] F) :
    IsIntegral S z ↔ ∃ s : S, (includeLeft : S →ₐ[R] S ⊗[R] F) s = z := by
  constructor
  · intro hz
    have h (w : S ⊗[R] integralClosure R F) :
        ∃ s : S, (includeLeft : S →ₐ[R] S ⊗[R] F) s =
          ((TensorProduct.toIntegralClosure R S F w : integralClosure S (S ⊗[R] F)) : S ⊗[R] F) := by
      induction w using TensorProduct.inductionOn with
      | tmul s c =>
        obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff (R := R) F).mp inferInstance c.property
        refine ⟨r • s, ?_⟩
        change (r • s) ⊗ₜ[R] (1 : F) = s ⊗ₜ[R] (c : F)
        rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hr]
      | add w v hw hv =>
        obtain ⟨s, hs⟩ := hw
        obtain ⟨t, ht⟩ := hv
        refine ⟨s + t, ?_⟩
        simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (fun a b : S ⊗[R] F => a + b) hs ht
    obtain ⟨w, hw⟩ := TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := F) |>.surjective ⟨z, hz⟩
    obtain ⟨s, hs⟩ := h w
    exact ⟨s, hs.trans (congrArg Subtype.val hw)⟩
  · rintro ⟨s, rfl⟩
    apply isIntegral_algebraMap

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra.IsIntegral R T]

/-- Maps from integral algebras to the generic fibre of a smooth algebra over a normal
domain extend uniquely to the original smooth algebra. -/
theorem existsUnique_algHom_includeLeft (f : T →ₐ[R] S ⊗[R] F) :
    ∃! g : T →ₐ[R] S, (includeLeft : S →ₐ[R] S ⊗[R] F).comp g = f := by
  let j : S →ₐ[R] S ⊗[R] F := includeLeft
  have hj : Function.Injective j := includeLeft_injective_of_fractionField R S F
  let e := AlgEquiv.ofInjective j hj
  have hf (t : T) : f t ∈ j.range := by
    apply (isIntegral_iff_exists_includeLeft R S F (f t)).mp
    exact ((Algebra.IsIntegral.isIntegral (R := R) t).map f).tower_top (A := S)
  let f' := f.codRestrict j.range hf
  let g : T →ₐ[R] S := e.symm.toAlgHom.comp f'
  have hg : j.comp g = f := by
    ext t
    exact congrArg Subtype.val (e.apply_symm_apply (f' t))
  refine ⟨g, hg, ?_⟩
  intro h hh
  apply AlgHom.ext
  intro t
  exact hj ((AlgHom.congr_fun hh t).trans (AlgHom.congr_fun hg t).symm)

/-- Fraction-field base change is bijective on homomorphisms from an integral algebra
to a smooth algebra over an integrally closed domain. -/
theorem genericFiber_map_bijective :
    Function.Bijective (fun g : T →ₐ[R] S =>
      (map (AlgHom.id F F) g : F ⊗[R] T →ₐ[F] F ⊗[R] S)) := by
  constructor
  · intro g h heq
    apply AlgHom.ext
    intro t
    apply includeRight_injective (R := R) (A := F) (B := S) (IsFractionRing.injective R F)
    have ht := AlgHom.congr_fun heq ((1 : F) ⊗ₜ[R] t)
    simpa only [map_tmul, AlgHom.id_apply, includeRight_apply] using ht
  · intro φ
    let c := Algebra.TensorProduct.comm R S F
    let f : T →ₐ[R] S ⊗[R] F :=
      c.symm.toAlgHom.comp ((φ.restrictScalars R).comp includeRight)
    obtain ⟨g, hg, _⟩ := existsUnique_algHom_includeLeft R S F f
    refine ⟨g, ?_⟩
    apply Algebra.TensorProduct.ext'
    intro a t
    have ht : (1 : F) ⊗ₜ[R] g t = φ ((1 : F) ⊗ₜ[R] t) := by
      have h := congrArg c (AlgHom.congr_fun hg t)
      simpa [f, c] using h
    simpa only [map_tmul, AlgHom.id_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (congrArg (fun z : F ⊗[R] S => a • z) ht).trans
        (map_smul φ a ((1 : F) ⊗ₜ[R] t)).symm

end Algebra.TensorProduct
