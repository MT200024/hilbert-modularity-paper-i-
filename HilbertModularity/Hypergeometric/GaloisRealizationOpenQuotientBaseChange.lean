/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Hypergeometric.GaloisRealizationOpenQuotient

/-! # Field extension of the branch-open reflection quotient

Field embeddings induce maps of reflection orbits, and the invariant coordinates
respect those maps.  This remains a point-level statement; the relative scheme quotient
of [GPRV, Proposition 9.5] is a separate geometric step.
-/

public noncomputable section

namespace HilbertModularity.Hypergeometric.EulerCover

variable {F E : Type*} [Field F] [Field E]

/-- Extend an exponent-`m` Euler point along a field embedding. -/
def mapOpenEulerPoint (φ : F →+* E) (N m : ℕ) {t : F}
    (p : OpenEulerPoint N m t) : OpenEulerPoint N m (φ t) where
  x := φ p.x
  y := φ p.y
  x_ne_zero := (map_ne_zero φ).mpr p.x_ne_zero
  y_ne_zero := (map_ne_zero φ).mpr p.y_ne_zero
  one_sub_x_ne_zero := by
    simpa only [map_one, map_sub] using (map_ne_zero φ).mpr p.one_sub_x_ne_zero
  one_sub_tx_ne_zero := by
    simpa only [map_one, map_sub, map_mul] using
      (map_ne_zero φ).mpr p.one_sub_tx_ne_zero
  equation := by
    simpa only [map_pow, map_mul, map_sub, map_one] using
      congrArg φ p.equation

@[simp] theorem mapOpenEulerPoint_x (φ : F →+* E) (N m : ℕ)
    {t : F} (p : OpenEulerPoint N m t) :
    (mapOpenEulerPoint φ N m p).x = φ p.x :=
  (rfl)

@[simp] theorem mapOpenEulerPoint_y (φ : F →+* E) (N m : ℕ)
    {t : F} (p : OpenEulerPoint N m t) :
    (mapOpenEulerPoint φ N m p).y = φ p.y :=
  (rfl)

/-- Reflection is defined over the parameter field, before coefficient-place
choices. -/
theorem mapOpenEulerPoint_reflect (φ : F →+* E) (N m : ℕ)
    (hm : m ≤ N) {t : F} (ht : t ≠ 0)
    (p : OpenEulerPoint N m t) :
    mapOpenEulerPoint φ N m (reflectOpenEulerPoint N m hm ht p) =
      reflectOpenEulerPoint N m hm ((map_ne_zero φ).mpr ht)
        (mapOpenEulerPoint φ N m p) := by
  apply OpenEulerPoint.ext
  · simpa only [mapOpenEulerPoint_x, reflectOpenEulerPoint_x] using
      map_reflectionX φ t p.x
  · simpa only [mapOpenEulerPoint_x, mapOpenEulerPoint_y,
      reflectOpenEulerPoint_x, reflectOpenEulerPoint_y] using
      map_reflectionY φ t p.x p.y

/-- A field embedding induces a map of the branch-open reflection orbits. -/
def mapOpenEulerReflectionQuotient (φ : F →+* E) (N m : ℕ)
    (hm : m ≤ N) {t : F} (ht : t ≠ 0) :
    OpenEulerReflectionQuotient N m hm ht →
      OpenEulerReflectionQuotient N m hm ((map_ne_zero φ).mpr ht) :=
  openEulerReflectionQuotientLift N m hm ht
    (fun p => openEulerReflectionQuotientMk N m hm ((map_ne_zero φ).mpr ht)
      (mapOpenEulerPoint φ N m p))
    (by
      intro p
      rw [mapOpenEulerPoint_reflect]
      exact openEulerReflectionQuotientMk_reflect N m hm
        ((map_ne_zero φ).mpr ht) (mapOpenEulerPoint φ N m p))

@[simp] theorem mapOpenEulerReflectionQuotient_mk (φ : F →+* E)
    (N m : ℕ) (hm : m ≤ N) {t : F} (ht : t ≠ 0)
    (p : OpenEulerPoint N m t) :
    mapOpenEulerReflectionQuotient φ N m hm ht
        (openEulerReflectionQuotientMk N m hm ht p) =
      openEulerReflectionQuotientMk N m hm ((map_ne_zero φ).mpr ht)
        (mapOpenEulerPoint φ N m p) :=
  openEulerReflectionQuotientLift_mk N m hm ht _ _ p

/-- The two invariant coordinates commute with field extension. -/
theorem openEulerReflectionCoordinates_map (φ : F →+* E)
    (N m : ℕ) {t : F} (p : OpenEulerPoint N m t) :
    openEulerReflectionCoordinates (mapOpenEulerPoint φ N m p) =
      (φ (openEulerReflectionCoordinates p).1,
        φ (openEulerReflectionCoordinates p).2) := by
  apply Prod.ext
  · simpa only [openEulerReflectionCoordinates_fst, mapOpenEulerPoint_x] using
      (map_reflectionInvariantX φ t p.x).symm
  · simpa only [openEulerReflectionCoordinates_snd, mapOpenEulerPoint_x,
      mapOpenEulerPoint_y] using
      (map_reflectionInvariantY φ t p.x p.y).symm

/-- The common point-level quotient has coefficient-independent invariant
coordinates; extending the parameter field applies the same embedding to
both coordinates. -/
theorem openEulerReflectionQuotientCoordinates_map (φ : F →+* E)
    (N m : ℕ) (hm : m ≤ N) {t : F} (ht : t ≠ 0)
    (q : OpenEulerReflectionQuotient N m hm ht) :
    openEulerReflectionQuotientCoordinates N m hm ((map_ne_zero φ).mpr ht)
        (mapOpenEulerReflectionQuotient φ N m hm ht q) =
      (φ (openEulerReflectionQuotientCoordinates N m hm ht q).1,
        φ (openEulerReflectionQuotientCoordinates N m hm ht q).2) := by
  induction q using OpenEulerReflectionQuotient.inductionOn N m hm ht with
  | _ p =>
    simpa only [mapOpenEulerReflectionQuotient_mk,
      openEulerReflectionQuotientCoordinates_mk]
      using openEulerReflectionCoordinates_map φ N m p

end HilbertModularity.Hypergeometric.EulerCover
