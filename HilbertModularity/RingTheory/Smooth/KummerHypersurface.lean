/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Smooth.Basic

/-! # Smooth localized Kummer hypersurfaces

A two-coordinate Jacobian identity gives smoothness for a root equation over a
principal open in the affine line over any commutative ring. The criterion applies
even when the covering degree is not invertible. Its use for the Euler cover is described
in [TripathiGoswamiRevised, Definition 2.3].
-/

@[expose] public noncomputable section

open Polynomial

namespace HilbertModularity.RingTheory.Smooth

/-- The principal-open coefficient ring for a Kummer equation. -/
abbrev localizedKummerBase {K : Type*} [CommRing K] (g : K[X]) :=
  Localization.Away g

/-- The equation of the Kummer cover on the principal open. -/
abbrev localizedKummerEquation {K : Type*} [CommRing K] (g P : K[X]) (n : ℕ) :
    (localizedKummerBase g)[X] :=
  X ^ n - C (algebraMap K[X] (localizedKummerBase g) P)

/-- The actual localized Kummer root algebra. -/
abbrev localizedKummerAlgebra {K : Type*} [CommRing K] (g P : K[X]) (n : ℕ) :=
  AdjoinRoot (localizedKummerEquation g P n)

/-- The affine-line coordinate in the localized Kummer root algebra. -/
abbrev localizedKummerX {K : Type*} [CommRing K] (g P : K[X]) (n : ℕ) :
    localizedKummerAlgebra g P n :=
  AdjoinRoot.of (localizedKummerEquation g P n)
    (algebraMap K[X] (localizedKummerBase g) X)

/-- The root coordinate in the localized Kummer root algebra. -/
abbrev localizedKummerZ {K : Type*} [CommRing K] (g P : K[X]) (n : ℕ) :
    localizedKummerAlgebra g P n :=
  AdjoinRoot.root (localizedKummerEquation g P n)

private theorem aeval_localizedKummerX {K : Type*} [CommRing K]
    (g P Q : K[X]) (n : ℕ) :
    aeval (localizedKummerX g P n) Q =
      AdjoinRoot.of (localizedKummerEquation g P n)
        (algebraMap K[X] (localizedKummerBase g) Q) := by
  have heval : aeval (algebraMap K[X] (localizedKummerBase g) X) Q =
      algebraMap K[X] (localizedKummerBase g) Q := by
    have hX : (Algebra.algHom K K[X] (localizedKummerBase g)) X =
        algebraMap K[X] (localizedKummerBase g) X :=
      Algebra.algHom_apply K K[X] (localizedKummerBase g) X
    have hQ : (Algebra.algHom K K[X] (localizedKummerBase g)) Q =
        algebraMap K[X] (localizedKummerBase g) Q :=
      Algebra.algHom_apply K K[X] (localizedKummerBase g) Q
    calc
      aeval (algebraMap K[X] (localizedKummerBase g) X) Q =
          aeval ((Algebra.algHom K K[X] (localizedKummerBase g)) X) Q := by
        rw [hX]
      _ = (Algebra.algHom K K[X] (localizedKummerBase g))
          (aeval (X : K[X]) Q) :=
        Polynomial.aeval_algHom_apply _ _ _
      _ = algebraMap K[X] (localizedKummerBase g) Q := by
        rw [Polynomial.aeval_X_left, AlgHom.id_apply]
        exact hQ
  calc
    aeval (localizedKummerX g P n) Q =
        AdjoinRoot.of (localizedKummerEquation g P n)
          (aeval (algebraMap K[X] (localizedKummerBase g) X) Q) :=
      Polynomial.aeval_algHom_apply
        (AdjoinRoot.ofAlgHom K (localizedKummerEquation g P n)) _ Q
    _ = _ := by rw [heval]

private theorem localizedKummer_relation {K : Type*} [CommRing K]
    (g P : K[X]) (n : ℕ) :
    (localizedKummerZ g P n) ^ n = aeval (localizedKummerX g P n) P := by
  have h := AdjoinRoot.eval₂_root (localizedKummerEquation g P n)
  simpa only [localizedKummerEquation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    sub_eq_zero, aeval_localizedKummerX] using h

/-- A first-order power expansion along a square-zero increment. -/
theorem pow_add_of_sq_eq_zero {B : Type*} [CommRing B]
    (n : ℕ) (z d : B) (hd : d ^ 2 = 0) :
    (z + d) ^ n = z ^ n + (n : B) * z ^ (n - 1) * d := by
  simpa [Polynomial.derivative_X_pow, mul_assoc] using
    (Polynomial.aeval_add_of_sq_eq_zero (X ^ n : B[X]) z d hd)

/-- Simultaneous Newton correction of the two coordinates of a Kummer equation. -/
theorem kummer_newton {K B : Type*} [CommRing K] [CommRing B] [Algebra K B]
    (P : K[X]) (n : ℕ) (x z e p q c u : B)
    (he2 : e ^ 2 = 0) (he : z ^ n - aeval x P = e)
    (hc : p * aeval x P.derivative + q * (n : B) * z ^ (n - 1) = c)
    (hcu : c * u = 1) :
    (z - q * e * u) ^ n = aeval (x + p * e * u) P := by
  have hdx : (p * e * u) ^ 2 = 0 := by
    rw [mul_pow, mul_pow, he2]
    ring
  have hdz : (-(q * e * u)) ^ 2 = 0 := by
    calc
      (-(q * e * u)) ^ 2 = (q * e * u) ^ 2 := by ring
      _ = 0 := by rw [mul_pow, mul_pow, he2]; ring
  calc
    (z - q * e * u) ^ n = z ^ n + (n : B) * z ^ (n - 1) * (-(q * e * u)) := by
      simpa only [sub_eq_add_neg] using pow_add_of_sq_eq_zero n z _ hdz
    z ^ n + (n : B) * z ^ (n - 1) * -(q * e * u) =
        aeval x P + e - q * (n : B) * z ^ (n - 1) * e * u := by rw [← he]; ring
    _ = aeval x P + aeval x P.derivative * (p * e * u) +
        (e - c * e * u) := by rw [← hc]; ring
    _ = aeval (x + p * e * u) P := by
      have : e - c * e * u = 0 := by
        calc
          e - c * e * u = e - e * (c * u) := by ring
          _ = 0 := by rw [hcu]; ring
      rw [this, add_zero, Polynomial.aeval_add_of_sq_eq_zero P x _ hdx]

/-- Evaluation of a localized Kummer algebra at a solution with invertible denominator. -/
noncomputable def localizedKummerEval {K B : Type*} [CommRing K] [CommRing B]
    [Algebra K B] (g P : K[X]) (n : ℕ) (x z : B)
    (hg : IsUnit (aeval x g)) (hroot : z ^ n = aeval x P) :
    localizedKummerAlgebra g P n →ₐ[K] B := by
  let ψ : localizedKummerBase g →ₐ[K] B :=
    IsLocalization.Away.liftAlgHom g (f := aeval x) hg
  have hψP : ψ (algebraMap K[X] (localizedKummerBase g) P) = aeval x P := by
    simp [ψ, IsLocalization.Away.liftAlgHom_apply]
  apply AdjoinRoot.liftAlgHom (localizedKummerEquation g P n) ψ z
  simp only [localizedKummerEquation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    sub_eq_zero]
  exact hroot.trans hψP.symm

@[simp] theorem localizedKummerEval_X {K B : Type*} [CommRing K] [CommRing B]
    [Algebra K B] (g P : K[X]) (n : ℕ) (x z : B)
    (hg : IsUnit (aeval x g)) (hroot : z ^ n = aeval x P) :
    localizedKummerEval g P n x z hg hroot (localizedKummerX g P n) = x := by
  simp [localizedKummerEval, localizedKummerX, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem localizedKummerEval_Z {K B : Type*} [CommRing K] [CommRing B]
    [Algebra K B] (g P : K[X]) (n : ℕ) (x z : B)
    (hg : IsUnit (aeval x g)) (hroot : z ^ n = aeval x P) :
    localizedKummerEval g P n x z hg hroot (localizedKummerZ g P n) = z := by
  simp [localizedKummerEval, localizedKummerZ]

/-- A Kummer algebra map is determined by the affine and root coordinates. -/
theorem localizedKummer_algHom_ext {K B : Type*} [CommRing K] [CommRing B]
    [Algebra K B] (g P : K[X]) (n : ℕ)
    {φ ψ : localizedKummerAlgebra g P n →ₐ[K] B}
    (hx : φ (localizedKummerX g P n) = ψ (localizedKummerX g P n))
    (hz : φ (localizedKummerZ g P n) = ψ (localizedKummerZ g P n)) : φ = ψ := by
  apply AdjoinRoot.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers g)
    apply Polynomial.algHom_ext
    change φ (AdjoinRoot.of (localizedKummerEquation g P n)
        ((Algebra.algHom K K[X] (localizedKummerBase g)) X)) =
      ψ (AdjoinRoot.of (localizedKummerEquation g P n)
        ((Algebra.algHom K K[X] (localizedKummerBase g)) X))
    have hX : (Algebra.algHom K K[X] (localizedKummerBase g)) X =
        algebraMap K[X] (localizedKummerBase g) X :=
      Algebra.algHom_apply K K[X] (localizedKummerBase g) X
    rw [hX]
    exact hx
  · exact hz

/-- The localized Kummer hypersurface is smooth when its two partial derivatives
generate the unit ideal in its actual coordinate algebra. -/
theorem smooth_localizedKummer {K : Type*} [CommRing K]
    (g P : K[X]) (n : ℕ) (_hn : 0 < n)
    (p q : localizedKummerAlgebra g P n)
    (hjac : p * aeval (localizedKummerX g P n) P.derivative +
      q * (n : localizedKummerAlgebra g P n) *
        (localizedKummerZ g P n) ^ (n - 1) = 1) :
    Algebra.Smooth K (localizedKummerAlgebra g P n) := by
  have hform : Algebra.FormallySmooth K (localizedKummerAlgebra g P n) := by
    apply Algebra.FormallySmooth.of_comp_surjective
    intro B _ _ I hI φ
    let π := Ideal.Quotient.mkₐ K I
    obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (φ (localizedKummerX g P n))
    obtain ⟨z₀, hz₀⟩ := Ideal.Quotient.mk_surjective (φ (localizedKummerZ g P n))
    obtain ⟨p₀, hp₀⟩ := Ideal.Quotient.mk_surjective (φ p)
    obtain ⟨q₀, hq₀⟩ := Ideal.Quotient.mk_surjective (φ q)
    change π x₀ = _ at hx₀
    change π z₀ = _ at hz₀
    change π p₀ = _ at hp₀
    change π q₀ = _ at hq₀
    let e := z₀ ^ n - aeval x₀ P
    have heq : π e = 0 := by
      have hrel : (φ (localizedKummerZ g P n)) ^ n =
          aeval (φ (localizedKummerX g P n)) P := by
        simpa only [map_pow, Polynomial.aeval_algHom_apply] using
          congrArg φ (localizedKummer_relation g P n)
      simp only [e, map_sub, map_pow, ← Polynomial.aeval_algHom_apply, hx₀, hz₀]
      exact sub_eq_zero.mpr hrel
    have heI : e ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp heq
    have he2 : e ^ 2 = 0 := by
      have h := Ideal.pow_mem_pow heI 2
      rw [hI] at h
      exact h
    let c := p₀ * aeval x₀ P.derivative + q₀ * (n : B) * z₀ ^ (n - 1)
    have hcQ : π c = 1 := by
      simpa only [c, map_add, map_mul, map_pow, map_natCast,
        ← Polynomial.aeval_algHom_apply, hp₀, hq₀, hx₀, hz₀, map_one] using
        congrArg φ hjac
    have hcunit : IsUnit c := by
      apply (IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩).mp
      change IsUnit (π c)
      rw [hcQ]
      exact isUnit_one
    obtain ⟨u, hcu⟩ := hcunit.exists_right_inv
    let x₁ := x₀ + p₀ * e * u
    let z₁ := z₀ - q₀ * e * u
    have hroot : z₁ ^ n = aeval x₁ P :=
      kummer_newton P n x₀ z₀ e p₀ q₀ c u he2 rfl rfl hcu
    have hx₁ : π x₁ = φ (localizedKummerX g P n) := by
      simp [x₁, map_add, map_mul, heq, hx₀]
    have hz₁ : π z₁ = φ (localizedKummerZ g P n) := by
      simp [z₁, map_sub, map_mul, heq, hz₀]
    have hφg : IsUnit (aeval (φ (localizedKummerX g P n)) g) := by
      have hu : IsUnit (algebraMap K[X] (localizedKummerBase g) g) :=
        IsLocalization.Away.algebraMap_isUnit g
      have := (hu.map (AdjoinRoot.of (localizedKummerEquation g P n))).map φ
      simpa only [← aeval_localizedKummerX g P g n,
        ← Polynomial.aeval_algHom_apply] using this
    have hπg : IsUnit (π (aeval x₁ g)) := by
      rw [← Polynomial.aeval_algHom_apply, hx₁]
      exact hφg
    have hg : IsUnit (aeval x₁ g) := by
      apply (IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩).mp
      change IsUnit (π (aeval x₁ g))
      exact hπg
    refine ⟨localizedKummerEval g P n x₁ z₁ hg hroot, ?_⟩
    apply localizedKummer_algHom_ext g P n
    · simpa only [AlgHom.comp_apply, localizedKummerEval_X] using hx₁
    · simpa only [AlgHom.comp_apply, localizedKummerEval_Z] using hz₁
  exact ⟨hform, inferInstance⟩

end HilbertModularity.RingTheory.Smooth
