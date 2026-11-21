/- Assembled by AxiomProver. -/

module

public import HilbertModularity.NumberTheory.LocalSpecialization.GoodPrimes
public import HilbertModularity.NumberTheory.HilbertModularForms.GaloisRealization

/-! # Finite ramification from good upstairs specializations

An inertia theorem at each good upstairs prime gives a finite ramification set
over the extension field. The contracted exceptional set also gives the same
conclusion simultaneously at every prime above a good base prime.
-/

public noncomputable section

open scoped NumberField
open IsDedekindDomain

namespace HilbertModularity.LocalSpecialization

variable {K F L V : Type*} [Field K] [NumberField K] [Field F] [NumberField F]
  [Algebra K F] [Field L] [AddCommGroup V] [Module L V]

/-- Trivial inertia at each good specialization makes an action unramified
outside the explicit finite set of upstairs bad primes. -/
theorem inertia_trivial_outside_badPrimesAbove
    (x : F) (n : ℕ)
    (ρ : Representation L (HilbertModularity.HilbertModularForms.AbsoluteGalois F) V)
    (hgood : ∀ p : HeightOneSpectrum (𝓞 F), p.GoodUnit x →
      (n : 𝓞 F) ∉ p.asIdeal →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = p.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularity.HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularity.HilbertModularForms.AbsoluteGalois F) →
              ρ g = 1)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ badPrimesAbove x n)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = p.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (g : HilbertModularity.HilbertModularForms.AbsoluteGalois F)
    (hg : g ∈ Q.inertia (HilbertModularity.HilbertModularForms.AbsoluteGalois F)) :
    ρ g = 1 := by
  have hprime : p.GoodUnit x ∧ (n : 𝓞 F) ∉ p.asIdeal := by
    exact (not_mem_badPrimesAbove_iff x n p).mp hp
  exact hgood p hprime.1 hprime.2 P hP Q g hg

omit [NumberField K] in
/-- The contracted bad set works for every upper prime over a good base
prime, without choosing one upper prime in advance. -/
theorem inertia_trivial_above_prime_outside_badPrimesBelow
    (x : F) (n : ℕ)
    (ρ : Representation L (HilbertModularity.HilbertModularForms.AbsoluteGalois F) V)
    (hgood : ∀ p : HeightOneSpectrum (𝓞 F), p.GoodUnit x →
      (n : 𝓞 F) ∉ p.asIdeal →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = p.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularity.HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularity.HilbertModularForms.AbsoluteGalois F) →
              ρ g = 1)
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ badPrimesBelow (K := K) x n)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p.under (𝓞 K) = q)
    (P : Ideal (𝓞 F)) [P.IsMaximal] (hP : P = p.asIdeal)
    (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P]
    (g : HilbertModularity.HilbertModularForms.AbsoluteGalois F)
    (hg : g ∈ Q.inertia (HilbertModularity.HilbertModularForms.AbsoluteGalois F)) :
    ρ g = 1 := by
  have hprime := goodUnit_and_integer_away_of_under_not_bad x n p (hp ▸ hq)
  exact hgood p hprime.1 hprime.2 P hP Q g hg

/-- Good-reduction inertia at primes avoiding the level and the coefficient
characteristic gives a finite ramification set for the actual action. -/
theorem finite_ramification_of_good_reduction
    (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (N ell : ℕ) (hN : N ≠ 0) (hell : ell ≠ 0)
    (ρ : Representation L (HilbertModularity.HilbertModularForms.AbsoluteGalois F) V)
    (hgood : ∀ p : HeightOneSpectrum (𝓞 F), p.GoodUnit x →
      (N : 𝓞 F) ∉ p.asIdeal → (ell : 𝓞 F) ∉ p.asIdeal →
      ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = p.asIdeal →
        ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
          ∀ g : HilbertModularity.HilbertModularForms.AbsoluteGalois F,
            g ∈ Q.inertia (HilbertModularity.HilbertModularForms.AbsoluteGalois F) →
              ρ g = 1) :
    (badPrimesAbove x (N * ell)).Finite ∧
      ∀ p : HeightOneSpectrum (𝓞 F), p ∉ badPrimesAbove x (N * ell) →
        ∀ (P : Ideal (𝓞 F)) [P.IsMaximal], P = p.asIdeal →
          ∀ (Q : Ideal (𝓞 (AlgebraicClosure F))) [Q.IsMaximal] [Q.LiesOver P],
            ∀ g : HilbertModularity.HilbertModularForms.AbsoluteGalois F,
              g ∈ Q.inertia (HilbertModularity.HilbertModularForms.AbsoluteGalois F) →
                ρ g = 1 := by
  refine ⟨badPrimesAbove_finite x hx0 hx1 (N * ell) (mul_ne_zero hN hell), ?_⟩
  intro p hp P instP hP Q instQ instOver g hg
  have hprime := (not_mem_badPrimesAbove_iff x (N * ell) p).mp hp
  have hfactors := factors_away_of_product_away p N ell hprime.2
  exact hgood p hprime.1 hfactors.1 hfactors.2 P hP Q g hg

end HilbertModularity.LocalSpecialization
