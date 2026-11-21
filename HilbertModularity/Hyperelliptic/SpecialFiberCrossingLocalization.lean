/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hyperelliptic.SpecialFiberCrossingPrime
public import HilbertModularity.Geometry.QuadraticLocalization

/-! # Localization at a crossing of the square-branch chart

The quadratic norm detects units after localizing the coefficient line at a
branch zero. This is the algebraic step that relates the coefficient-localized
node equation to the actual point of the special-fibre chart.
-/

public noncomputable section

open Polynomial

namespace HilbertModularity.Hyperelliptic

variable {k : Type*} [Field k]

instance finiteCrossingPrime_isPrime_instance (P : k[X]) (x : k) :
    (RingHom.ker (finiteCrossingEvaluation P x).toRingHom).IsPrime :=
  finiteCrossingPrime_isPrime P x

/-- Multiplication by the conjugate is the scalar quadratic norm. -/
theorem squareBranch_mul_conj {R : Type*} [CommRing R] (H : R)
    (z : QuadraticAlgebra R (H ^ 2) 0) :
    z * (⟨z.re, -z.im⟩ : QuadraticAlgebra R (H ^ 2) 0) =
      algebraMap R _ (z.re ^ 2 - (z.im * H) ^ 2) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re]
    ring
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_im]
    ring

/-- At a branch zero the norm of a chart element has residue equal to the
square of its scalar coefficient. -/
theorem squareBranch_norm_eval (H : k[X]) (x : k) (hx : H.eval x = 0)
    (z : QuadraticAlgebra k[X] (H ^ 2) 0) :
    (z.re ^ 2 - (z.im * H) ^ 2).eval x = (z.re.eval x) ^ 2 := by
  simp [hx]

/-- Every element outside the crossing prime becomes a unit after localizing
the coefficient line at the corresponding evaluation prime. -/
theorem squareBranch_baseChange_isUnit_of_re_eval_ne_zero
    (H : k[X]) (x : k) (hx : H.eval x = 0)
    {a : k[X]} (ha : a = H ^ 2)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))]
    (z : QuadraticAlgebra k[X] a 0) (hz : z.re.eval x ≠ 0) :
    IsUnit (QuadraticAlgebra.baseChange (S := S) a 0 z) := by
  subst a
  let n : k[X] := z.re ^ 2 - (z.im * H) ^ 2
  have hn_eval : n.eval x ≠ 0 := by
    rw [show n.eval x = (z.re.eval x) ^ 2 from squareBranch_norm_eval H x hx z]
    exact pow_ne_zero _ hz
  have hn : IsUnit (algebraMap k[X] S n) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff S
      (RingHom.ker (evalRingHom x)) _).2
    simpa [RingHom.mem_ker, evalRingHom] using hn_eval
  let w := QuadraticAlgebra.baseChange (S := S) (H ^ 2) 0 z
  have hprod : w * (⟨w.re, -w.im⟩ : QuadraticAlgebra S
      (algebraMap k[X] S (H ^ 2)) (algebraMap k[X] S 0)) =
      algebraMap S _ (algebraMap k[X] S n) := by
    calc
      w * (⟨w.re, -w.im⟩ : QuadraticAlgebra S
          (algebraMap k[X] S (H ^ 2)) (algebraMap k[X] S 0)) =
          QuadraticAlgebra.baseChange (S := S) (H ^ 2) 0
            (z * (⟨z.re, -z.im⟩ : QuadraticAlgebra k[X] (H ^ 2) 0)) := by
        rw [map_mul]
        congr 1
        ext <;> simp [w, QuadraticAlgebra.baseChange, QuadraticAlgebra.mapCoeffs]
      _ = algebraMap S _ (algebraMap k[X] S n) := by
        rw [squareBranch_mul_conj, QuadraticAlgebra.baseChange_algebraMap]
  exact isUnit_of_mul_isUnit_left (hprod ▸ hn.map (algebraMap S _))

/-- A localization at a smaller set of denominators is also a localization at
a larger set when the additional denominators are already units. -/
theorem isLocalization_of_le_of_isUnit
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M N : Submonoid A} [IsLocalization M B] (hMN : M ≤ N)
    (hunit : ∀ n : N, IsUnit (algebraMap A B n.1)) :
    IsLocalization N B := by
  obtain ⟨_, hsurj, hker⟩ := (isLocalization_iff M B).mp
    (inferInstance : IsLocalization M B)
  apply (isLocalization_iff N B).mpr
  refine ⟨hunit, ?_, ?_⟩
  · intro z
    obtain ⟨⟨a, m⟩, hm⟩ := hsurj z
    exact ⟨⟨a, ⟨m.1, hMN m.2⟩⟩, hm⟩
  · intro a b hab
    obtain ⟨m, hm⟩ := hker hab
    exact ⟨⟨m.1, hMN m.2⟩, hm⟩

/-- At a branch zero, localizing the coefficient line already localizes the
actual finite quadratic chart at its crossing prime. -/
theorem finiteCrossing_baseChange_isLocalization_atPrime
    (P : k[X]) (x : k) (hx : (finiteComponentPolynomial P).eval x = 0)
    (S : Type*) [CommRing S] [Algebra k[X] S]
    [(RingHom.ker (evalRingHom x)).IsPrime]
    [IsLocalization.AtPrime S (RingHom.ker (evalRingHom x))] :
    IsLocalization.AtPrime
      (QuadraticAlgebra S
        (algebraMap k[X] S (finiteBranchPolynomial P 0))
        (algebraMap k[X] S 0))
      (RingHom.ker (finiteCrossingEvaluation P x).toRingHom) := by
  let := finiteCrossingPrime_isPrime P x
  let B := AlgebraicGeometry.DoubleCover.ChartRing (finiteBranchPolynomial P 0)
  let T := QuadraticAlgebra S
    (algebraMap k[X] S (finiteBranchPolynomial P 0)) (algebraMap k[X] S 0)
  let p := RingHom.ker (evalRingHom x)
  let q := RingHom.ker (finiteCrossingEvaluation P x).toRingHom
  let M : Submonoid B := p.primeCompl.map (algebraMap k[X] B).toMonoidHom
  let : IsLocalization M T :=
    QuadraticAlgebra.isLocalization (S := S) (finiteBranchPolynomial P 0) 0
      p.primeCompl
  have hMN : M ≤ q.primeCompl := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hz
    change algebraMap k[X] B a ∉ q
    intro hq
    have hp : a ∈ p := by
      change a ∈ RingHom.ker (evalRingHom x)
      rw [← finiteCrossingPrime_comap P x]
      exact hq
    exact ha hp
  have hunit : ∀ z : q.primeCompl, IsUnit (algebraMap B T z.1) := by
    rintro ⟨z, hz⟩
    have hne : z.re.eval x ≠ 0 := by
      intro hzero
      exact hz ((mem_finiteCrossingPrime_iff P x hx z).2 hzero)
    change IsUnit (QuadraticAlgebra.baseChange (S := S)
      (finiteBranchPolynomial P 0) 0 z)
    exact squareBranch_baseChange_isUnit_of_re_eval_ne_zero
      (finiteComponentPolynomial P) x hx (finiteBranchPolynomial_zero P) S z hne
  exact isLocalization_of_le_of_isUnit hMN hunit

end HilbertModularity.Hyperelliptic
