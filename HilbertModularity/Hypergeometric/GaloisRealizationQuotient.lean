/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisDescent
public import HilbertModularity.Hypergeometric.GaloisRealizationFibreChart
public import HilbertModularity.Geometry.ProjectiveLine.CoordinateRing

/-! # The common geometric quotient behind real Euler descent

[GPRV, Proposition 9.5 and proof of Theorem 9.2, pp. 40–41] discuss the
involution and quotient motive. [SGA1, Exposé V, Propositions 1.1, 1.3,
1.8 and 1.9] give the finite nonfree scheme quotient under
the affine-orbit hypothesis and its flat base change. The selected Euler
family now records an affine open around every pair of points, and the
real-to-cyclotomic field extension is flat. Extension of the explicit
reflection to the selected proper *relative* model and smooth proper
real descent remain separate source applications. They are now isolated in
`exists_realEulerReflectionData_of_coprime` and the generic tame-curve
quotient interface, rather than hidden in the final Euler theorem.

The formula `y ↦ 1/y` printed in [GPRV, (73), p. 40] is the formula in
the Kummer coordinate `w = y/(1-x)`. For the Euler coordinate in this
library the checked branch-open formula is
`y ↦ -(1-x)(1-tx)/(txy)`. The theorem
`EulerCover.reflectionNormalizedRoot_inverse` proves the coordinate
transport directly, so the two formulas are not conflated.
Its cohomological realization is a separate construction.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace HilbertModularity.Hypergeometric

universe u

/-- The actual extension from the real cyclotomic field to the cyclotomic
field is flat. This is the field-extension hypothesis needed for the finite
invariant quotient base-change theorem; it does not assert that the quotient
has been constructed. -/
theorem realEulerCoefficientInclusion_flat (N : ℕ) [NeZero N] :
    Flat (Spec.map (CommRingCat.ofHom (realEulerCoefficientInclusion N))) := by
  apply Flat.SpecMap_iff.mpr
  let : Algebra (Cyclotomic.realCyclotomicField N)
      (Cyclotomic.cyclotomicField N) := (realEulerCoefficientInclusion N).toAlgebra
  change Module.Flat (Cyclotomic.realCyclotomicField N)
    (Cyclotomic.cyclotomicField N)
  infer_instance

/-- The normalized Kummer coordinate `w = y/(1-x)` conjugates the checked
reflection of the displayed Euler equation to `w ↦ 1/w`, the coordinate
formula printed in [GPRV, Proposition 9.5, (73), p. 40]. The factor in the
`y` formula is therefore a coordinate change, not a second involution. -/
theorem EulerCover.reflectionNormalizedRoot_inverse
    {F : Type*} [Field F] {t x y : F}
    (ht : t ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h1x : 1 - x ≠ 0) (h1tx : 1 - t * x ≠ 0) :
    EulerCover.reflectionY t x y /
        (1 - EulerCover.reflectionX t x) = (y / (1 - x))⁻¹ := by
  rw [EulerCover.reflectionY_eq, EulerCover.reflectionX_eq]
  have hden : -1 + x * t ≠ 0 := by
    intro hz
    apply h1tx
    calc
      1 - t * x = -(-1 + x * t) := by ring
      _ = 0 := by rw [hz]; ring
  field_simp [hden]
  have hden' : x * t - 1 ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hden
  rw [show 1 - x * t = -(x * t - 1) by ring]
  field_simp [hden']

/-- The finite, possibly nonfree, scheme quotient of an involution whose
two-point orbits lie in affine opens. This is the order-two case of
[SGA1, Exposé V, Propositions 1.1, 1.3 and 1.8]; the exact scheme
statement and its invariant-affine hypothesis are also indexed as
`AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant`
in `fermats_last_theorem` v4_33_1. Neither theorem assumes a free action.

The conclusion is only the absolute quotient and its universal property.
Smoothness over a parameter scheme, real descent, and flat base change are
separate applications. -/
theorem exists_involutionQuotient_of_affineOrbits
    (X : Scheme) (j : Aut X) (hjj : j.hom ≫ j.hom = 𝟙 X)
    (hadm : ∀ x : X, ∃ U : X.Opens,
      IsAffineOpen U ∧ x ∈ U ∧ j.hom.base x ∈ U) :
    ∃ (Y : Scheme) (π : X ⟶ Y),
      j.hom ≫ π = π ∧ IsIntegralHom π ∧ IsAffineHom π ∧
        ∀ (T : Scheme) (f : X ⟶ T),
          j.hom ≫ f = f → ∃! g : Y ⟶ T, π ≫ g = f := by
  sorry

/-- Once the GPRV reflection has been extended to the chosen proper Euler
family, its two-point orbits have affine neighborhoods and the
cyclotomic scheme quotient follows from the standard nonfree quotient
theorem. This statement does not descend the quotient to the real field. -/
theorem exists_cyclotomicEulerInvolutionQuotient
    (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (j : Aut (Over.mk 𝒞.projection))
    (hjj : j.hom.left ≫ j.hom.left = 𝟙 𝒞.curve) :
    ∃ (Y : Scheme) (π : 𝒞.curve ⟶ Y),
      j.hom.left ≫ π = π ∧ IsIntegralHom π ∧ IsAffineHom π ∧
        ∀ (T : Scheme) (f : 𝒞.curve ⟶ T),
          j.hom.left ≫ f = f → ∃! g : Y ⟶ T, π ≫ g = f :=
  exists_involutionQuotient_of_affineOrbits 𝒞.curve
    { hom := j.hom.left, inv := j.inv.left,
      hom_inv_id := congrArg Over.Hom.left j.hom_inv_id,
      inv_hom_id := congrArg Over.Hom.left j.inv_hom_id }
    hjj (fun x => 𝒞.pair_affineOpen x (j.hom.left.base x))

/-- The actual real-form reflection of one selected Euler model. The real
curve and its cyclotomic base-change isomorphism are fields of the Euler
family, supplied by the same normalized cyclic-cover construction. The
family's real affine inclusion and its commuting coefficient-change square
pin this isomorphism to the original `x,y` Euler chart, excluding a deck
rotation of the base-change identification. This
record adds the reflection and its compatibility with that fixed real form;
it contains no quotient scheme or quotient map. -/
structure RealEulerReflectionData (N m : ℕ) [NeZero N]
    (𝒞 : SmoothProperEulerFamily N m) where
  realInvolution : Aut (Over.mk 𝒞.realProjection)
  realInvolution_sq : realInvolution ≪≫ realInvolution = Iso.refl _
  involution : Aut (Over.mk 𝒞.projection)
  involution_sq : involution ≪≫ involution = Iso.refl _
  involution_nontrivial : involution ≠ Iso.refl _
  baseChange_compatibility :
    involution.hom.left ≫ 𝒞.realBaseChangeIso.hom =
      𝒞.realBaseChangeIso.hom ≫
        ((Over.pullback
          (puncturedCoefficientMap (realEulerCoefficientInclusion N))).mapIso
            realInvolution).hom.left
  involution_affineChart :
    ∀ (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
      (h1t : IsUnit (1 - t)) (hmPos : 1 ≤ m) (hmN : m < N)
      (hcop : m.Coprime N),
      (EulerCover.reflectionChartSchemeIso N m t (NeZero.ne N)
          hmPos hmN hcop ht.ne_zero).hom ≫
        smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t =
      smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t ≫
        (smoothProperEulerFibreAutomorphism N m 𝒞 involution t ht h1t).hom

/-- [EsnaultViehweg, §3, (3.5)–(3.13)] constructs the same cyclic cover
over the real field, and the family record fixes its cyclotomic base
change. The branch-open involution is `w ↦ 1/w` in the normalized
coordinate, exactly [GPRV, Proposition 9.5, (73), p. 40], as proved by
`reflectionNormalizedRoot_inverse`. Each proper geometric fibre has genus
`N-1 ≥ 2`: density of the generic Euler chart identifies the geometric
generic curve, and proper smooth comparison preserves geometric connectedness
and genus along the connected parameter line [src_milne_lec, Theorem 20.4].
Riemann–Hurwitz for its four primitive branch points gives genus `N-1`.
[DeligneMumford1969, Theorem 1.11 and Lemma 1.12, pp. 84–85] then extend
the generic automorphism uniquely over the smooth stable family. The
parenthetical after Lemma 1.12 explicitly extends its statement to arbitrary
valuation rings; the parameter line is regular. Uniqueness
identifies its cyclotomic base change with the reflection on `𝒞` because
`realBaseChangeIso_affineInclusion` fixes the same dense Euler chart on both
models. An arbitrary over-base isomorphism without that chart equality would
not suffice.

This named source-application interface supplies only the reflection and
the specified model comparison, not a quotient or cohomological claim. -/
theorem exists_realEulerReflectionData_of_coprime
    (N m : ℕ) [NeZero N]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N) (𝒞 : SmoothProperEulerFamily N m) :
    Nonempty (RealEulerReflectionData N m 𝒞) := by
  sorry

/-- The real reflection has order two on the underlying scheme. -/
theorem RealEulerReflectionData.realInvolution_sq_left
    (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (ℛ : RealEulerReflectionData N m 𝒞) :
    ℛ.realInvolution.hom.left ≫ ℛ.realInvolution.hom.left = 𝟙 𝒞.realCurve := by
  have h := congrArg Iso.hom ℛ.realInvolution_sq
  change ℛ.realInvolution.hom ≫ ℛ.realInvolution.hom = 𝟙 _ at h
  exact congrArg Over.Hom.left h

/-- The standard nonfree quotient theorem applies on the real form itself.
This is the categorical quotient stage before the relative properness,
smoothness and specified cyclotomic comparison are supplied. -/
theorem exists_realEulerInvolutionQuotient
    (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (ℛ : RealEulerReflectionData N m 𝒞) :
    ∃ (Y : Scheme) (π : 𝒞.realCurve ⟶ Y),
      ℛ.realInvolution.hom.left ≫ π = π ∧
        IsIntegralHom π ∧ IsAffineHom π ∧
          ∀ (T : Scheme) (f : 𝒞.realCurve ⟶ T),
            ℛ.realInvolution.hom.left ≫ f = f →
              ∃! g : Y ⟶ T, π ≫ g = f :=
  exists_involutionQuotient_of_affineOrbits 𝒞.realCurve
    { hom := ℛ.realInvolution.hom.left,
      inv := ℛ.realInvolution.inv.left,
      hom_inv_id := congrArg Over.Hom.left ℛ.realInvolution.hom_inv_id,
      inv_hom_id := congrArg Over.Hom.left ℛ.realInvolution.inv_hom_id }
    (ℛ.realInvolution_sq_left N m 𝒞)
    (fun x => 𝒞.realPair_affineOpen x (ℛ.realInvolution.hom.left.base x))

/-- Relative properties of a **selected** finite involution quotient of a
smooth proper curve over a characteristic-zero punctured parameter line.
The selected real quotient `(Y, πReal)` is already categorical; its
existence is supplied separately by the checked application of [SGA1,
Exposé V, Propositions 1.1, 1.3 and 1.8]. Corollary 1.5 and the
finite-surjective/proper argument give properness. Since two is invertible,
averaging splits the
invariants from the source algebra and makes them commute even with field
extension; flatness of the quotient follows from the source's flatness.
Each geometric fibre is the quotient of a smooth curve by an involution,
whose invariant local rings are DVRs; the quotient fibres are smooth. The
flat, finitely presented, smooth-fibre criterion is
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField` in mathlib
v4_34_0. Properness follows from the finite surjective quotient map and
properness of the source. These standard geometric deductions are retained
as a visible literature interface; it is independent of the Euler equation.

The isomorphism `e` identifies the chosen field-extended curve `X` with the
actual base change of `C`; the compatibility hypothesis forces the quotient
map below to use the same involution on `X`. -/
theorem exists_smoothProperPuncturedCurveInvolutionQuotient
    {K F : Type u} [Field K] [CharZero K] [Field F]
    (σ : K →+* F) (C X : Scheme)
    (p : C ⟶ ProjectiveLine.punctured K)
    (pX : X ⟶ ProjectiveLine.punctured F)
    (hproper : IsProper p) (hsmooth : Smooth p)
    (hcurve : SmoothOfRelativeDimension 1 p)
    (hpair : ∀ x y : C, ∃ U : C.Opens,
      IsAffineOpen U ∧ x ∈ U ∧ y ∈ U)
    (j : Aut (Over.mk p)) (hjsq : j ≪≫ j = Iso.refl _)
    (Y : Scheme) (πReal : C ⟶ Y)
    (hπReal : j.hom.left ≫ πReal = πReal)
    (hπIntegral : IsIntegralHom πReal)
    (hπAffine : IsAffineHom πReal)
    (hπUniversal : ∀ (T : Scheme) (f : C ⟶ T),
      j.hom.left ≫ f = f → ∃! g : Y ⟶ T, πReal ≫ g = f)
    (jX : Aut (Over.mk pX))
    (e : X ≅ pullback p (puncturedCoefficientMap σ))
    (he : e.hom ≫ pullback.snd _ _ = pX)
    (hcompat : jX.hom.left ≫ e.hom =
      e.hom ≫ ((Over.pullback (puncturedCoefficientMap σ)).mapIso j).hom.left) :
    ∃ (q : Y ⟶ ProjectiveLine.punctured K),
      IsProper q ∧ Smooth q ∧
        ∃ π : X ⟶ pullback q (puncturedCoefficientMap σ),
          π ≫ pullback.snd _ _ = pX ∧
            jX.hom.left ≫ π = π ∧
              ∀ (T : Scheme) (f : X ⟶ T),
                jX.hom.left ≫ f = f →
                  ∃! g : pullback q (puncturedCoefficientMap σ) ⟶ T,
                    π ≫ g = f := by
  sorry

/-- A single geometric quotient over the real parameter line. Its base
change to the cyclotomic parameter line is the categorical quotient of the
chosen proper Euler family by a nontrivial involution over that line. The
quotient and cover map are schemes and morphisms, not representation data. -/
structure SmoothProperRealEulerQuotient (N m : ℕ) [NeZero N]
    (𝒞 : SmoothProperEulerFamily N m) where
  curve : Scheme
  projection : curve ⟶ ProjectiveLine.punctured (Cyclotomic.realCyclotomicField N)
  isProper : IsProper projection
  isSmooth : Smooth projection
  involution : Aut (Over.mk 𝒞.projection)
  involution_sq : involution ≪≫ involution = Iso.refl _
  involution_nontrivial : involution ≠ Iso.refl _
  involution_affineChart :
    ∀ (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
      (h1t : IsUnit (1 - t)) (hmPos : 1 ≤ m) (hmN : m < N)
      (hcop : m.Coprime N),
      (EulerCover.reflectionChartSchemeIso N m t (NeZero.ne N)
          hmPos hmN hcop ht.ne_zero).hom ≫
        smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t =
      smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t ≫
        (smoothProperEulerFibreAutomorphism N m 𝒞 involution t ht h1t).hom
  coverToQuotient : 𝒞.curve ⟶
    pullback projection
      (puncturedCoefficientMap (realEulerCoefficientInclusion N))
  coverToQuotient_overBase :
    coverToQuotient ≫ pullback.snd _ _ = 𝒞.projection
  coverToQuotient_invariant :
    involution.hom.left ≫ coverToQuotient = coverToQuotient
  coverToQuotient_universal :
    ∀ (T : Scheme) (f : 𝒞.curve ⟶ T),
      involution.hom.left ≫ f = f →
      ∃! g : pullback projection
          (puncturedCoefficientMap (realEulerCoefficientInclusion N)) ⟶ T,
        coverToQuotient ≫ g = f

/-- Two maps out of the selected quotient agree if they agree after the
selected Euler cover map.  This follows from the categorical quotient
property, without a finiteness or geometric-orbit assertion. -/
theorem SmoothProperRealEulerQuotient.hom_ext (N m : ℕ) [NeZero N]
    (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    {T : Scheme}
    {f g : pullback 𝒬.projection
        (puncturedCoefficientMap (realEulerCoefficientInclusion N)) ⟶ T}
    (h : 𝒬.coverToQuotient ≫ f = 𝒬.coverToQuotient ≫ g) : f = g := by
  have hinv : 𝒬.involution.hom.left ≫ (𝒬.coverToQuotient ≫ f) =
      𝒬.coverToQuotient ≫ f := by
    rw [← Category.assoc, 𝒬.coverToQuotient_invariant]
  obtain ⟨u, hu, hunique⟩ :=
    𝒬.coverToQuotient_universal T (𝒬.coverToQuotient ≫ f) hinv
  exact (hunique f rfl).trans (hunique g h.symm).symm

/-- Assemble the selected Euler quotient record from an actual real
reflection model and the generic tame relative-curve quotient interface.
The selected cyclotomic cover map is the base change of one real quotient
map, so no coefficient-place or fibrewise quotient is chosen afresh. -/
theorem exists_smoothProperRealEulerQuotient_of_reflectionData
    (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (ℛ : RealEulerReflectionData N m 𝒞) :
    Nonempty (SmoothProperRealEulerQuotient N m 𝒞) := by
  obtain ⟨Y, πReal, hπReal, hπIntegral, hπAffine, hπUniversal⟩ :=
    exists_realEulerInvolutionQuotient N m 𝒞 ℛ
  obtain ⟨q, hproper, hsmooth, π, hπbase, hπinv, hπuniv⟩ :=
    exists_smoothProperPuncturedCurveInvolutionQuotient
      (realEulerCoefficientInclusion N)
      𝒞.realCurve 𝒞.curve 𝒞.realProjection 𝒞.projection
      𝒞.realIsProper 𝒞.realIsSmooth 𝒞.realRelDimOne
      𝒞.realPair_affineOpen ℛ.realInvolution ℛ.realInvolution_sq
      Y πReal hπReal hπIntegral hπAffine hπUniversal
      ℛ.involution 𝒞.realBaseChangeIso
      𝒞.realBaseChangeIso_overBase ℛ.baseChange_compatibility
  exact ⟨{
    curve := Y
    projection := q
    isProper := hproper
    isSmooth := hsmooth
    involution := ℛ.involution
    involution_sq := ℛ.involution_sq
    involution_nontrivial := ℛ.involution_nontrivial
    involution_affineChart := ℛ.involution_affineChart
    coverToQuotient := π
    coverToQuotient_overBase := hπbase
    coverToQuotient_invariant := hπinv
    coverToQuotient_universal := hπuniv
  }⟩

/-- The actual relative quotient of the fixed exponent-`m` Euler model is
assembled from three named geometry interfaces. The family itself contains
the real cyclic model and its cyclotomic base-change isomorphism from
[EsnaultViehweg, §3, (3.5)–(3.13)].
`exists_realEulerReflectionData_of_coprime` supplies the extension of
the checked branch-open reflection using [GPRV, Proposition 9.5, (73)]
and the stable-curve extension theorem of [DeligneMumford1969, Theorem
1.11 and Lemma 1.12].
`exists_smoothProperPuncturedCurveInvolutionQuotient` supplies the
standard nonfree tame relative quotient with [SGA1, Exposé V, §1,
Propositions 1.1, 1.3, 1.8 and 1.9, Corollary 1.5] and the smooth-fibre criterion.
The displayed conclusion is proved by composing those inputs; it is not
itself a literature admission. The `w=y/(1-x)` transport to GPRV's
printed `1/w` formula is proved above. The three source interfaces retain
visible sorry bodies, so this result remains conditional and its axiom
cone is unconditionally open. No quotient-motive/cohomology comparison
is included in these geometric interfaces.
The chart reflection itself is proved in
`GaloisRealizationChartScheme`.
The source's `(Irr)` is verified by `symmetricParameters_irreducible` from
`m.Coprime N` and GPRV Lemma 8.5, p. 30. This is the RAW quotient for
even `N`; κ normalization is separate. -/
theorem exists_smoothProperRealEulerQuotient_of_coprime
    (N m : ℕ) [NeZero N]
    (h3 : 3 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m) :
    Nonempty (SmoothProperRealEulerQuotient N m 𝒞) := by
  obtain ⟨ℛ⟩ := exists_realEulerReflectionData_of_coprime N m h3 hm hmN hcop 𝒞
  exact exists_smoothProperRealEulerQuotient_of_reflectionData N m 𝒞 ℛ

/-- The checked odd quotient interface is the same general coprime
geometric quotient; oddness is used only later to trivialize κ_N. -/
theorem exists_smoothProperRealEulerQuotient_of_odd_coprime
    (N m : ℕ) [NeZero N]
    (h3 : 3 ≤ N) (_hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m) :
    Nonempty (SmoothProperRealEulerQuotient N m 𝒞) :=
  exists_smoothProperRealEulerQuotient_of_coprime N m h3 hm hmN hcop 𝒞

/-- The prime-level quotient is the same geometric object supplied by the
odd coprime source interface. -/
theorem exists_smoothProperRealEulerQuotient (N m : ℕ) [NeZero N]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m) :
    Nonempty (SmoothProperRealEulerQuotient N m 𝒞) := by
  have hOdd : Odd N := hN.odd_of_ne_two (by omega)
  have hcop : m.Coprime N :=
    (hN.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hmN)).symm
  exact exists_smoothProperRealEulerQuotient_of_odd_coprime N m
    (le_trans (by decide : 3 ≤ 5) h5) hOdd hm hmN hcop 𝒞

/-- Select one odd coprime quotient before all coefficient places. -/
def chosenSmoothProperRealEulerQuotient_of_odd_coprime
    (N m : ℕ) [NeZero N]
    (h3 : 3 ≤ N) (hOdd : Odd N) (hm : 0 < m) (hmN : m < N)
    (hcop : m.Coprime N)
    (𝒞 : SmoothProperEulerFamily N m) :
    SmoothProperRealEulerQuotient N m 𝒞 :=
  Classical.choice (exists_smoothProperRealEulerQuotient_of_odd_coprime N m
    h3 hOdd hm hmN hcop 𝒞)

/-- Select the same geometric quotient for every later coefficient place. -/
def chosenSmoothProperRealEulerQuotient (N m : ℕ) [NeZero N]
    (hN : N.Prime) (h5 : 5 ≤ N) (hm : 0 < m) (hmN : m < N)
    (𝒞 : SmoothProperEulerFamily N m) :
    SmoothProperRealEulerQuotient N m 𝒞 :=
  Classical.choice (exists_smoothProperRealEulerQuotient N m hN h5 hm hmN 𝒞)

/-- The selected proper involution restricts to the explicit affine Euler
reflection after specialization. This is the family-level projection of the
chart compatibility in the cited quotient construction. -/
theorem SmoothProperRealEulerQuotient.involution_affineSpecialization
    (N m : ℕ) [NeZero N] (𝒞 : SmoothProperEulerFamily N m)
    (𝒬 : SmoothProperRealEulerQuotient N m 𝒞)
    (t : Cyclotomic.cyclotomicField N) (ht : IsUnit t)
    (h1t : IsUnit (1 - t)) (hmPos : 1 ≤ m) (hmN : m < N)
    (hcop : m.Coprime N) :
    (EulerCover.reflectionChartSchemeIso N m t (NeZero.ne N)
        hmPos hmN hcop ht.ne_zero).hom ≫
        EulerCover.affineFamilySpecialization
          (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
          N m t ht h1t ≫ 𝒞.affineInclusion =
      EulerCover.affineFamilySpecialization
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        N m t ht h1t ≫ 𝒞.affineInclusion ≫ 𝒬.involution.hom.left := by
  let j := smoothProperEulerFibreChartInclusion N m 𝒞 t ht h1t
  let p := smoothProperEulerFibreToCurve N m 𝒞 t ht h1t
  let r := (EulerCover.reflectionChartSchemeIso N m t (NeZero.ne N)
    hmPos hmN hcop ht.ne_zero).hom
  let a := (smoothProperEulerFibreAutomorphism N m 𝒞 𝒬.involution t ht h1t).hom
  have hj : j ≫ p = EulerCover.affineFamilySpecialization
      (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
      N m t ht h1t ≫ 𝒞.affineInclusion :=
    smoothProperEulerFibreChartInclusion_fst N m 𝒞 t ht h1t
  have ha : a ≫ p = p ≫ 𝒬.involution.hom.left :=
    smoothProperEulerFibreAutomorphism_fst N m 𝒞 𝒬.involution t ht h1t
  have hr : r ≫ j = j ≫ a :=
    𝒬.involution_affineChart t ht h1t hmPos hmN hcop
  calc
    r ≫ (EulerCover.affineFamilySpecialization
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        N m t ht h1t ≫ 𝒞.affineInclusion) = r ≫ (j ≫ p) := by rw [hj]
    _ = (r ≫ j) ≫ p := (Category.assoc _ _ _).symm
    _ = (j ≫ a) ≫ p := by rw [hr]
    _ = j ≫ (a ≫ p) := Category.assoc _ _ _
    _ = j ≫ (p ≫ 𝒬.involution.hom.left) := by rw [ha]
    _ = (j ≫ p) ≫ 𝒬.involution.hom.left := (Category.assoc _ _ _).symm
    _ = (EulerCover.affineFamilySpecialization
        (Cyclotomic.cyclotomicField N) (Cyclotomic.cyclotomicField N)
        N m t ht h1t ≫ 𝒞.affineInclusion) ≫ 𝒬.involution.hom.left := by rw [hj]

end HilbertModularity.Hypergeometric
