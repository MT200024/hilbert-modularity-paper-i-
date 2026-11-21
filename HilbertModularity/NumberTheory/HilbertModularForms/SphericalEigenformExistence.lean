/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.HilbertModularForms.EigenformCohomologicalExistence
public import Mathlib.FieldTheory.IntermediateField.Basic

/-! # A simultaneous spherical eigenvector

This named literature boundary replaces the finite exceptional set of a chosen
vector by a level spherical at every unramified local factor. It supplies an
actual adelic eigenform and permits enlargement of its coefficient number field.
It does not assert modularity of an independently specified Galois system.
-/

public noncomputable section

open NumberField IsDedekindDomain

namespace HilbertModularity.HilbertModularForms

variable {F A : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
  [Field A] [NumberField A]
  {level : FiniteLevel F} {μ : AdditiveQuotientMeasure F}

/-- Simultaneous spherical replacement with algebraic coefficients, combining
[src_skinner_hilbert_2009, §1, (1), p. 242] with
[SkinnerWiles, §3.1, pp. 29–30]. The former is the full away-ℓ
Weil–Deligne compatibility, including monodromy, with geometric Artin
normalization; its Theorem 1 concerns primes above ℓ and is not used here.
The latter gives the cuspidal decomposition, restricted tensor product,
one-dimensional spherical invariant lines, rational finite-level cusp spaces
and rational Hecke operators.

Here is the correspondence included in this admission, rather than a verbatim
quotation. Choose a nonzero irreducible cuspidal constituent of the original
vector. Its common-good Hecke parameters are those of the original vector.
The semisimple Galois action of that constituent agrees with `D` by Frobenius
detection. Full local compatibility implies that a place with trivial inertia
away from ℓ has an unramified local parameter with zero monodromy, hence a
spherical local factor. Choose spherical vectors at all those places in the
restricted tensor product, and fixed vectors at the finitely many others.
Rationality of the finite-level Hecke action puts their eigenvalues in some
number field; take its compositum with the original coefficient field inside
ℂ. This does not claim preservation of the original field. Boundedness and the
finite central character are preserved in this weight-two cuspidal constituent.
The normalized polynomial is `X² - a_q X + Nq ω_q` for geometric Frobenius.
The unramified local parameter also identifies the Hecke polynomial. If its
polynomial in the original completion comes from `f : Polynomial A`, injectivity
of coefficient embeddings identifies the new Hecke polynomial with `f.map i`.
This records the same local compatibility, without constructing scalar extension
of an independently supplied compatible system. -/
theorem exists_sphericalEigenform
    (φ : AlgebraicGoodPrimeEigenform level μ A)
    (hbounded : ∃ C : ℝ, ∀ g, ‖φ.form.toFun g‖ ≤ C)
    (hcentral : (Set.range φ.form.central_character).Finite)
    (D : EigenformCohomologicalActions φ) :
    ∃ (B : IntermediateField ℚ ℂ) (hB : NumberField B),
      letI := hB
      ∃ (i : A →+* B) (level' : FiniteLevel F)
        (ψ : AlgebraicGoodPrimeEigenform level' μ B),
        B.val.toRingHom.comp i = φ.complexEmbedding ∧
        ψ.complexEmbedding = B.val.toRingHom ∧
        ψ.form.central_character = φ.form.central_character ∧
        (∃ C : ℝ, ∀ g, ‖ψ.form.toFun g‖ ≤ C) ∧
        (∀ q (hφ : q ∉ φ.form.bad) (hψ : q ∉ ψ.form.bad),
          (φ.heckePolynomial q hφ).map i = ψ.heckePolynomial q hψ) ∧
        ∀ (q : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 A))
          (P : Ideal (𝓞 F)) [P.IsMaximal], P = q.asIdeal →
          (D.residueCharacteristic w : 𝓞 F) ∉ P →
          ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
            (∀ g : AbsoluteGalois F,
              g ∈ Q.inertia (AbsoluteGalois F) → D.action w g = 1) →
            q ∉ ψ.form.bad ∧
            ∀ (hψ : q ∉ ψ.form.bad) (f : Polynomial A),
              (D.action w
                (NumberField.geometricFrobenius F (AlgebraicClosure F) P Q)).charpoly =
                f.map (algebraMap A (w.adicCompletion A)) →
              f.map i = ψ.heckePolynomial q hψ := by
  sorry

end HilbertModularity.HilbertModularForms
