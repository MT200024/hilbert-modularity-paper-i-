/- Assembled by AxiomProver. -/

module

public import HilbertModularity.Geometry.GroupScheme.PrimeHypergeometricExistence
public import HilbertModularity.Geometry.GroupScheme.FiberPoints
public import HilbertModularity.Geometry.ProjectiveLine.GenericEtale
public import HilbertModularity.Geometry.Etale.ConnectedHom

/-! # The rational prime torsion point of the explicit plus family

The generic point in [DarmonRigid, Theorem 2.6(2)] is carried to the geometric
generic fibre of the very same abelian scheme. These maps preserve the point,
its order and its arithmetic Galois invariance.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.GroupScheme HilbertModularity.Cyclotomic
open scoped CategoryTheory.MonObj NumberField

attribute [local instance] Scheme.finiteEtaleCartesianMonoidalCategory
  Scheme.finiteEtaleBraidedCategory

namespace AlgebraicGeometry.GroupScheme
universe u

variable (K : Type u) [Field K] {S : Scheme.{u}}
  (x : Spec (CommRingCat.of K) ⟶ S) (A : CommGrp (Over S))

/-- A rational point stays fixed by the arithmetic action after extension to
the algebraic closure. -/
theorem geometricPointsFieldMap_arithmetic_fixed
    (v : Additive (Over.mk x ⟶ A.X))
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Additive.ofMul (Scheme.arithmeticFiberPointMap K x g ≫
      (geometricPointsFieldMap K (AlgebraicClosure K) x A v).toMul) =
        geometricPointsFieldMap K (AlgebraicClosure K) x A v := by
  let q := Over.homMk (U := Scheme.geometricPointOver K x) (V := Over.mk x)
    (Spec.algebraMap K (AlgebraicClosure K)) rfl
  have hq : Scheme.arithmeticFiberPointMap K x g ≫ q = q := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.algebraMap K (AlgebraicClosure K) =
        Spec.algebraMap K (AlgebraicClosure K)
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact g.commutes a
  change Scheme.arithmeticFiberPointMap K x g ≫ (q ≫ v.toMul) = q ≫ v.toMul
  rw [← Category.assoc, hq]

end AlgebraicGeometry.GroupScheme

namespace AlgebraicGeometry.Scheme
universe u

variable {S : Scheme.{u}} (K : Type u) [Field K]
  (x : Spec (CommRingCat.of K) ⟶ S)

/-- Regard a rational generic point of a finite étale cover as a morphism
between the generic fibres of the terminal cover and that cover. -/
def finiteEtaleGenericPointMap (Y : S.FiniteEtale)
    (y : Over.mk x ⟶ (finiteEtaleForget S).obj Y) :
    (finiteEtalePullback x).obj (finiteEtaleTerminal S) ⟶
      (finiteEtalePullback x).obj Y := by
  let U := (finiteEtaleForget (Spec (CommRingCat.of K))).obj
    ((finiteEtalePullback x).obj (finiteEtaleTerminal S))
  let q : (Over.map x).obj U ⟶ Over.mk x :=
    Over.homMk U.hom (by rfl)
  let e : U ⟶ (finiteEtaleForget (Spec (CommRingCat.of K))).obj
      ((finiteEtalePullback x).obj Y) :=
    (Over.mapPullbackAdj x).homEquiv U ((finiteEtaleForget S).obj Y) (q ≫ y)
  exact (finiteEtaleForget (Spec (CommRingCat.of K))).preimage e

/-- Full faithfulness of the actual generic-fibre functor extends the
rational point to a section of the finite étale cover. -/
def extendFiniteEtaleGenericPoint (K : Type u) [Field K]
    (Y : (ProjectiveLine.punctured K).FiniteEtale)
    (y : Over.mk (ProjectiveLine.puncturedRationalPoint K) ⟶
      (finiteEtaleForget (ProjectiveLine.punctured K)).obj Y) :
    finiteEtaleTerminal (ProjectiveLine.punctured K) ⟶ Y :=
  (finiteEtalePullback (ProjectiveLine.puncturedRationalPoint K)).preimage
    (finiteEtaleGenericPointMap (RatFunc K)
      (ProjectiveLine.puncturedRationalPoint K) Y y)

/-- The extended section restricts to the map specified at the rational
generic point. -/
theorem extendFiniteEtaleGenericPoint_spec (K : Type u) [Field K]
    (Y : (ProjectiveLine.punctured K).FiniteEtale)
    (y : Over.mk (ProjectiveLine.puncturedRationalPoint K) ⟶
      (finiteEtaleForget (ProjectiveLine.punctured K)).obj Y) :
    (finiteEtalePullback (ProjectiveLine.puncturedRationalPoint K)).map
        (extendFiniteEtaleGenericPoint K Y y) =
      finiteEtaleGenericPointMap (RatFunc K)
        (ProjectiveLine.puncturedRationalPoint K) Y y := by
  exact Functor.map_preimage _ _

/-- The extension evaluates to the prescribed rational point on the generic fibre. -/
theorem extendFiniteEtaleGenericPoint_eval (K : Type u) [Field K]
    (Y : (ProjectiveLine.punctured K).FiniteEtale)
    (y : Over.mk (ProjectiveLine.puncturedRationalPoint K) ⟶
      (finiteEtaleForget (ProjectiveLine.punctured K)).obj Y) :
    (Over.homMk (ProjectiveLine.puncturedRationalPoint K) (by
      change ProjectiveLine.puncturedRationalPoint K ≫ 𝟙 _ =
        ProjectiveLine.puncturedRationalPoint K
      exact Category.comp_id _) :
      Over.mk (ProjectiveLine.puncturedRationalPoint K) ⟶
        (finiteEtaleForget (ProjectiveLine.punctured K)).obj
          (finiteEtaleTerminal (ProjectiveLine.punctured K))) ≫
      (finiteEtaleForget (ProjectiveLine.punctured K)).map
        (extendFiniteEtaleGenericPoint K Y y) = y := by
  let S := ProjectiveLine.punctured K
  let x := ProjectiveLine.puncturedRationalPoint K
  let s := extendFiniteEtaleGenericPoint K Y y
  have hs := extendFiniteEtaleGenericPoint_spec K Y y
  have hm := congrArg
    (fun m => ((finiteEtaleForget (Spec (CommRingCat.of (RatFunc K)))).map m).left) hs
  let u : Spec (CommRingCat.of (RatFunc K)) ⟶ pullback (𝟙 S) x :=
    pullback.lift x (𝟙 _) (by simp)
  have hu₁ : u ≫ pullback.fst (𝟙 S) x = x := by
    simp only [u, pullback.lift_fst]
  have hu₂ : u ≫ pullback.snd (𝟙 S) x = 𝟙 _ := by
    simp only [u, pullback.lift_snd]
  let U := (finiteEtaleForget (Spec (CommRingCat.of (RatFunc K)))).obj
    ((finiteEtalePullback x).obj (finiteEtaleTerminal S))
  let q : (Over.map x).obj U ⟶ Over.mk x := Over.homMk U.hom (by rfl)
  let e : U ⟶ (finiteEtaleForget (Spec (CommRingCat.of (RatFunc K)))).obj
      ((finiteEtalePullback x).obj Y) :=
    (Over.mapPullbackAdj x).homEquiv U ((finiteEtaleForget S).obj Y) (q ≫ y)
  have hm' : ((Over.pullback x).map ((finiteEtaleForget S).map s)).left = e.left := by
    change ((Over.pullback x).map ((finiteEtaleForget S).map s)).left =
      ((finiteEtaleForget (Spec (CommRingCat.of (RatFunc K)))).map
        ((finiteEtaleForget (Spec (CommRingCat.of (RatFunc K)))).preimage e)).left at hm
    simpa only [Functor.map_preimage] using hm
  have he : e.left ≫ pullback.fst ((finiteEtaleForget S).obj Y).hom x =
      U.hom ≫ y.left := by
    have h := congrArg Over.Hom.left
      (((Over.mapPullbackAdj x).homEquiv U ((finiteEtaleForget S).obj Y)).symm_apply_apply
        (q ≫ y))
    change e.left ≫ pullback.fst ((finiteEtaleForget S).obj Y).hom x =
      U.hom ≫ y.left at h
    exact h
  have hb : pullback.fst ((finiteEtaleForget S).obj (finiteEtaleTerminal S)).hom x ≫
      ((finiteEtaleForget S).map s).left = U.hom ≫ y.left := by
    have h := congrArg (fun f => f ≫ pullback.fst ((finiteEtaleForget S).obj Y).hom x) hm'
    simpa only [Over.pullback_map_left, pullback.lift_fst] using h.trans he
  change pullback.fst (𝟙 S) x ≫ ((finiteEtaleForget S).map s).left =
    pullback.snd (𝟙 S) x ≫ y.left at hb
  apply Over.OverMorphism.ext
  have h := congrArg (fun f => u ≫ f) hb
  have hf : x ≫ ((finiteEtaleForget S).map s).left = y.left := by
    have h' : (u ≫ pullback.fst (𝟙 S) x) ≫ ((finiteEtaleForget S).map s).left =
        (u ≫ pullback.snd (𝟙 S) x) ≫ y.left := by
      exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
    simpa only [hu₁, hu₂, Category.id_comp] using h'
  change x ≫ ((finiteEtaleForget S).map s).left = y.left
  exact hf

end AlgebraicGeometry.Scheme

namespace HilbertModularity.Hypergeometric
universe u

variable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
local notation "Kₚ" => realCyclotomicField p

/-- The same rational order-`p` point on the geometric generic fibre. -/
def primePlusGeometricGenericPoint :
    Additive (Scheme.geometricPointOver (RatFunc Kₚ)
      (ProjectiveLine.puncturedRationalPoint Kₚ) ⟶ (primePlusFamily p hp).X) :=
  geometricPointsFieldMap (RatFunc Kₚ) (AlgebraicClosure (RatFunc Kₚ))
    (ProjectiveLine.puncturedRationalPoint Kₚ) (primePlusFamily p hp)
    (primePlusData p hp).genericPoint

/-- The geometric generic point is killed by the prime. -/
theorem primePlusGeometricGenericPoint_torsion :
    p • primePlusGeometricGenericPoint p hp = 0 := by
  unfold primePlusGeometricGenericPoint
  change p • geometricPointsFieldMap (RatFunc Kₚ) (AlgebraicClosure (RatFunc Kₚ))
    (ProjectiveLine.puncturedRationalPoint Kₚ) (primePlusFamily p hp)
      (primePlusData p hp).genericPoint = 0
  have hkill : p • (primePlusData p hp).genericPoint = 0 := by
    have h := addOrderOf_nsmul_eq_zero (primePlusData p hp).genericPoint
    rw [(primePlusData p hp).genericPoint_order] at h
    exact h
  let f := geometricPointsFieldMap (RatFunc Kₚ) (AlgebraicClosure (RatFunc Kₚ))
    (ProjectiveLine.puncturedRationalPoint Kₚ) (primePlusFamily p hp)
  have hmap := f.map_nsmul p (primePlusData p hp).genericPoint
  calc
    p • f (primePlusData p hp).genericPoint =
        f (p • (primePlusData p hp).genericPoint) := hmap.symm
    _ = 0 := by
      rw [hkill]
      exact f.map_zero

/-- The rational order-`p` point does not vanish after extension to the
algebraic closure because prime multiplication has finite étale kernel. -/
theorem primePlusGeometricGenericPoint_ne_zero :
    primePlusGeometricGenericPoint p hp ≠ 0 := by
  let D := primePlusData p hp
  let A := primePlusFamily p hp
  let x := ProjectiveLine.puncturedRationalPoint Kₚ
  let : IsFinite (p ^ 1 • 𝟙 A).hom.hom.hom.left := by
    change IsFinite (p ^ 1 • 𝟙 D.family).hom.hom.hom.left
    exact D.multiplication_finite (p ^ 1) (by positivity)
  let : Etale (p ^ 1 • 𝟙 A).hom.hom.hom.left := by
    change Etale (p ^ 1 • 𝟙 D.family).hom.hom.hom.left
    exact D.multiplication_etale (p ^ 1) (by positivity)
  have hP : D.genericPoint ≠ 0 := by
    intro hz
    have h : 1 = p := by simpa [hz] using D.genericPoint_order
    omega
  have hkill : p • D.genericPoint = 0 := by
    have h := addOrderOf_nsmul_eq_zero D.genericPoint
    rw [D.genericPoint_order] at h
    exact h
  let P : AddSubgroup.torsionBy (Additive (Over.mk x ⟶ A.X)) (p ^ 1) :=
    ⟨D.genericPoint, by
      apply (AddSubgroup.torsionBy.nsmul_iff).2
      change p ^ 1 • D.genericPoint = 0
      simpa only [pow_one] using hkill⟩
  have hinj := torsionMap_geometricPointsFieldMap_injective
    (RatFunc Kₚ) (AlgebraicClosure (RatFunc Kₚ)) x A p 1
  intro hz
  have hzero : TateModule.torsionMap p
      (geometricPointsFieldMap (RatFunc Kₚ) (AlgebraicClosure (RatFunc Kₚ)) x A) 1 P = 0 := by
    apply Subtype.ext
    exact hz
  have hPzero : P = 0 := hinj hzero
  exact hP (congrArg Subtype.val hPzero)

/-- The prime torsion point is arithmetically fixed on the geometric generic
fibre; this uses its rational origin, not geometric monodromy. -/
theorem primePlusGeometricGenericPoint_fixed
    (g : AlgebraicClosure (RatFunc Kₚ) ≃ₐ[RatFunc Kₚ]
      AlgebraicClosure (RatFunc Kₚ)) :
    Additive.ofMul (Scheme.arithmeticFiberPointMap (RatFunc Kₚ)
      (ProjectiveLine.puncturedRationalPoint Kₚ) g ≫
        (primePlusGeometricGenericPoint p hp).toMul) =
      primePlusGeometricGenericPoint p hp :=
  geometricPointsFieldMap_arithmetic_fixed (RatFunc Kₚ)
    (ProjectiveLine.puncturedRationalPoint Kₚ) (primePlusFamily p hp)
    (primePlusData p hp).genericPoint g

/-- The cited abelian scheme has a finite multiplication map at the
denominator prime. -/
instance primePlusPrimeMultiplicationFinite :
    IsFinite (p • 𝟙 (primePlusFamily p hp)).hom.hom.hom.left :=
  (primePlusData p hp).multiplication_finite p (by omega)

/-- The denominator-prime multiplication map is étale in characteristic zero. -/
instance primePlusPrimeMultiplicationEtale :
    Etale (p • 𝟙 (primePlusFamily p hp)).hom.hom.hom.left :=
  (primePlusData p hp).multiplication_etale p (by omega)

/-- The cited rational point lifted to the actual finite étale multiplication
kernel of the same plus family. -/
def primePlusGenericTorsionPoint :
    Additive (Over.mk (ProjectiveLine.puncturedRationalPoint Kₚ) ⟶
      (CommGrp.torsionObject (primePlusFamily p hp) p).X) := by
  let D := primePlusData p hp
  have hkill : p • D.genericPoint = 0 := by
    have h := addOrderOf_nsmul_eq_zero D.genericPoint
    rw [D.genericPoint_order] at h
    exact h
  exact (CommGrp.torsionPointAddEquiv (primePlusFamily p hp) p
    (Over.mk (ProjectiveLine.puncturedRationalPoint Kₚ))).symm
      ⟨D.genericPoint, (AddSubgroup.torsionBy.nsmul_iff).2 hkill⟩

/-- Full faithfulness at the rational generic point extends the rational
prime torsion point to a section over every nonsingular parameter. -/
def primePlusTorsionSection :
    Scheme.finiteEtaleTerminal (ProjectiveLine.punctured Kₚ) ⟶
      (finiteEtaleTorsionObject (primePlusFamily p hp) p).X := by
  apply Scheme.extendFiniteEtaleGenericPoint Kₚ
    (finiteEtaleTorsionObject (primePlusFamily p hp) p).X
  exact (primePlusGenericTorsionPoint p hp).toMul

/-- Evaluating the extended section at the rational generic point recovers
the chosen point of exact order `p`. -/
theorem primePlusTorsionSection_generic :
    (Over.homMk (ProjectiveLine.puncturedRationalPoint Kₚ) (by
      change ProjectiveLine.puncturedRationalPoint Kₚ ≫ 𝟙 _ =
        ProjectiveLine.puncturedRationalPoint Kₚ
      exact Category.comp_id _) :
        Over.mk (ProjectiveLine.puncturedRationalPoint Kₚ) ⟶
          (Scheme.finiteEtaleForget (ProjectiveLine.punctured Kₚ)).obj
            (Scheme.finiteEtaleTerminal (ProjectiveLine.punctured Kₚ))) ≫
      (Scheme.finiteEtaleForget (ProjectiveLine.punctured Kₚ)).map
        (primePlusTorsionSection p hp) =
      (primePlusGenericTorsionPoint p hp).toMul := by
  exact Scheme.extendFiniteEtaleGenericPoint_eval Kₚ
    (finiteEtaleTorsionObject (primePlusFamily p hp) p).X
    (primePlusGenericTorsionPoint p hp).toMul

/-- The generic point of the finite étale torsion cover is nonzero. -/
theorem primePlusGenericTorsionPoint_ne_zero :
    primePlusGenericTorsionPoint p hp ≠ 0 := by
  intro hz
  let A := primePlusFamily p hp
  let x := ProjectiveLine.puncturedRationalPoint Kₚ
  let e := CommGrp.torsionPointAddEquiv A p (Over.mk x)
  have h : (primePlusData p hp).genericPoint = 0 := by
    have h' : e (primePlusGenericTorsionPoint p hp) = 0 := by
      rw [hz]
      exact e.map_zero
    have hv := congrArg Subtype.val h'
    have heval : (e (primePlusGenericTorsionPoint p hp)).val =
        (primePlusData p hp).genericPoint := by
      unfold primePlusGenericTorsionPoint
      exact congrArg Subtype.val (e.apply_symm_apply _)
    exact heval.symm.trans hv
  have ho := (primePlusData p hp).genericPoint_order
  rw [h, addOrderOf_zero] at ho
  omega

/-- The section of the finite étale torsion scheme remains nonzero over every
nonsingular rational or geometric parameter point. -/
theorem primePlusTorsionSection_fiber_ne_zero
    (L : Type) [Field L]
    (z : Spec (CommRingCat.of L) ⟶ ProjectiveLine.punctured Kₚ) :
    Additive.ofMul
      ((Over.homMk z (by
          change z ≫ 𝟙 _ = z
          exact Category.comp_id _) :
          Over.mk z ⟶
            (Scheme.finiteEtaleForget (ProjectiveLine.punctured Kₚ)).obj
              (Scheme.finiteEtaleTerminal (ProjectiveLine.punctured Kₚ))) ≫
        (Scheme.finiteEtaleForget (ProjectiveLine.punctured Kₚ)).map
          (primePlusTorsionSection p hp)) ≠
            (0 : Additive (Over.mk z ⟶
              (CommGrp.torsionObject (primePlusFamily p hp) p).X)) := by
  let S := ProjectiveLine.punctured Kₚ
  let A := primePlusFamily p hp
  let T := (CommGrp.torsionObject A p).X
  let s : Over.mk (𝟙 S) ⟶ T :=
    (Scheme.finiteEtaleForget S).map (primePlusTorsionSection p hp)
  let e : Over.mk (𝟙 S) ⟶ T := (0 : Additive (Over.mk (𝟙 S) ⟶ T)).toMul
  intro hz
  let q : Over.mk z ⟶ Over.mk (𝟙 S) := Over.homMk z (by
    change z ≫ 𝟙 S = z
    exact Category.comp_id _)
  have hz0 : q ≫ s = 1 := by
    change Additive.ofMul (q ≫ s) = 0 at hz
    exact congrArg Additive.toMul hz
  have he0 : q ≫ e = 1 := MonObj.comp_one q
  have hz' : z ≫ s.left = z ≫ e.left := by
    have he := congrArg Over.Hom.left (hz0.trans he0.symm)
    simpa only [q, Over.comp_left, Over.homMk_left] using he
  have hse : s.left = e.left := by
    let : PreconnectedSpace (Over.mk (𝟙 S)).left := inferInstanceAs (PreconnectedSpace S)
    let : Etale T.hom := by
      change Etale (finiteEtaleTorsionObject A p).X.obj.hom
      infer_instance
    let : IsFinite T.hom := by
      change IsFinite (finiteEtaleTorsionObject A p).X.obj.hom
      infer_instance
    exact Scheme.Hom.eq_of_comp_point T.hom s.left e.left
      ((Over.w s).trans (Over.w e).symm) L z hz'
  have hgeneric : primePlusGenericTorsionPoint p hp = 0 := by
    have hg := primePlusTorsionSection_generic p hp
    have hse' : s = e := Over.OverMorphism.ext hse
    let q : Over.mk (ProjectiveLine.puncturedRationalPoint Kₚ) ⟶
        Over.mk (𝟙 S) := Over.homMk (ProjectiveLine.puncturedRationalPoint Kₚ) (by
          change ProjectiveLine.puncturedRationalPoint Kₚ ≫ 𝟙 _ =
            ProjectiveLine.puncturedRationalPoint Kₚ
          exact Category.comp_id _)
    have he : q ≫ s = q ≫ e := congrArg (fun f => q ≫ f) hse'
    have he0 : q ≫ e = 1 := MonObj.comp_one q
    exact congrArg Additive.ofMul (hg.symm.trans (he.trans he0))
  exact primePlusGenericTorsionPoint_ne_zero p hp hgeneric

/-- The rational prime torsion section evaluated on one nonsingular fibre. -/
def primePlusTorsionValue
    (ξ : ProjectiveLine.Parameter Kₚ) :
    Additive (Over.mk (ProjectiveLine.puncturedPoint Kₚ ξ) ⟶
      (CommGrp.torsionObject (primePlusFamily p hp) p).X) :=
  Additive.ofMul
    ((Over.homMk (ProjectiveLine.puncturedPoint Kₚ ξ) (by
        change ProjectiveLine.puncturedPoint Kₚ ξ ≫ 𝟙 _ =
          ProjectiveLine.puncturedPoint Kₚ ξ
        exact Category.comp_id _) :
        Over.mk (ProjectiveLine.puncturedPoint Kₚ ξ) ⟶
          (Scheme.finiteEtaleForget (ProjectiveLine.punctured Kₚ)).obj
            (Scheme.finiteEtaleTerminal (ProjectiveLine.punctured Kₚ))) ≫
      (Scheme.finiteEtaleForget (ProjectiveLine.punctured Kₚ)).map
        (primePlusTorsionSection p hp))

/-- The extended torsion section has a nonzero value at every nonsingular
parameter over the ground field. -/
theorem primePlusTorsionValue_ne_zero
    (ξ : ProjectiveLine.Parameter Kₚ) :
    primePlusTorsionValue p hp ξ ≠ 0 :=
  primePlusTorsionSection_fiber_ne_zero p hp Kₚ
    (ProjectiveLine.puncturedPoint Kₚ ξ)

/-- The torsion-cover point gives a point on the actual plus-family fibre. -/
def primePlusRationalFiberPoint
    (ξ : ProjectiveLine.Parameter Kₚ) :
    Additive (Over.mk (ProjectiveLine.puncturedPoint Kₚ ξ) ⟶
      (primePlusFamily p hp).X) :=
  (CommGrp.torsionPointAddEquiv (primePlusFamily p hp) p
    (Over.mk (ProjectiveLine.puncturedPoint Kₚ ξ))
      (primePlusTorsionValue p hp ξ)).val

/-- The specialized rational point is killed by `p`. -/
theorem primePlusRationalFiberPoint_torsion
    (ξ : ProjectiveLine.Parameter Kₚ) :
    p • primePlusRationalFiberPoint p hp ξ = 0 := by
  exact (AddSubgroup.torsionBy.nsmul_iff).1
    (CommGrp.torsionPointAddEquiv (primePlusFamily p hp) p
      (Over.mk (ProjectiveLine.puncturedPoint Kₚ ξ))
        (primePlusTorsionValue p hp ξ)).property

/-- The rational point does not vanish on a nonsingular fibre. -/
theorem primePlusRationalFiberPoint_ne_zero
    (ξ : ProjectiveLine.Parameter Kₚ) :
    primePlusRationalFiberPoint p hp ξ ≠ 0 := by
  let e := CommGrp.torsionPointAddEquiv (primePlusFamily p hp) p
    (Over.mk (ProjectiveLine.puncturedPoint Kₚ ξ))
  intro h
  have he : e (primePlusTorsionValue p hp ξ) = 0 := by
    apply Subtype.ext
    exact h
  exact primePlusTorsionValue_ne_zero p hp ξ
    (e.injective (he.trans e.map_zero.symm))

/-- The actual geometric point on the same specialized plus-family fibre. -/
def primePlusGeometricFiberPoint
    (ξ : ProjectiveLine.Parameter Kₚ) :
    Points Kₚ (AlgebraicClosure Kₚ)
      (parameterFiber Kₚ (primePlusFamily p hp) ξ).X :=
  geometricFiberPointsAddEquiv Kₚ (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint Kₚ ξ)
      (geometricPointsFieldMap Kₚ (AlgebraicClosure Kₚ)
        (ProjectiveLine.puncturedPoint Kₚ ξ) (primePlusFamily p hp)
          (primePlusRationalFiberPoint p hp ξ))

/-- The specialized geometric point remains prime torsion. -/
theorem primePlusGeometricFiberPoint_torsion
    (ξ : ProjectiveLine.Parameter Kₚ) :
    p • primePlusGeometricFiberPoint p hp ξ = 0 := by
  unfold primePlusGeometricFiberPoint
  let E := geometricFiberPointsAddEquiv Kₚ (primePlusFamily p hp)
    (ProjectiveLine.puncturedPoint Kₚ ξ)
  let f := geometricPointsFieldMap Kₚ (AlgebraicClosure Kₚ)
    (ProjectiveLine.puncturedPoint Kₚ ξ) (primePlusFamily p hp)
  change p • E (f (primePlusRationalFiberPoint p hp ξ)) = 0
  calc
    p • E (f (primePlusRationalFiberPoint p hp ξ)) =
        E (p • f (primePlusRationalFiberPoint p hp ξ)) :=
          (E.toAddMonoidHom.map_nsmul p _).symm
    _ = E (f (p • primePlusRationalFiberPoint p hp ξ)) := by
      rw [f.map_nsmul]
    _ = 0 := by
      rw [primePlusRationalFiberPoint_torsion, f.map_zero]
      exact E.map_zero

/-- The rational section remains a nonzero point on the geometric fibre. -/
theorem primePlusGeometricFiberPoint_ne_zero
    (ξ : ProjectiveLine.Parameter Kₚ) :
    primePlusGeometricFiberPoint p hp ξ ≠ 0 := by
  let A := primePlusFamily p hp
  let z := ProjectiveLine.puncturedPoint Kₚ ξ
  let : IsFinite (p ^ 1 • 𝟙 A).hom.hom.hom.left :=
    (primePlusData p hp).multiplication_finite (p ^ 1) (by positivity)
  let : Etale (p ^ 1 • 𝟙 A).hom.hom.hom.left :=
    (primePlusData p hp).multiplication_etale (p ^ 1) (by positivity)
  let P : AddSubgroup.torsionBy (Additive (Over.mk z ⟶ A.X)) (p ^ 1) :=
    ⟨primePlusRationalFiberPoint p hp ξ, by
      apply (AddSubgroup.torsionBy.nsmul_iff).2
      simpa only [pow_one] using primePlusRationalFiberPoint_torsion p hp ξ⟩
  have hP : P ≠ 0 := by
    intro h
    exact primePlusRationalFiberPoint_ne_zero p hp ξ (congrArg Subtype.val h)
  let f := geometricPointsFieldMap Kₚ (AlgebraicClosure Kₚ) z A
  have hinj := torsionMap_geometricPointsFieldMap_injective
    Kₚ (AlgebraicClosure Kₚ) z A p 1
  intro h
  have hf : f (primePlusRationalFiberPoint p hp ξ) = 0 := by
    apply (geometricFiberPointsAddEquiv Kₚ A z).injective
    exact h.trans (geometricFiberPointsAddEquiv Kₚ A z).map_zero.symm
  have hzero : TateModule.torsionMap p f 1 P = 0 := by
    apply Subtype.ext
    exact hf
  exact hP (hinj hzero)

/-- The specialized geometric point is fixed by arithmetic Galois because
it comes from the actual rational section. -/
theorem primePlusGeometricFiberPoint_fixed
    (ξ : ProjectiveLine.Parameter Kₚ)
    (g : AlgebraicClosure Kₚ ≃ₐ[Kₚ] AlgebraicClosure Kₚ) :
    g • primePlusGeometricFiberPoint p hp ξ =
      primePlusGeometricFiberPoint p hp ξ := by
  let z := ProjectiveLine.puncturedPoint Kₚ ξ
  let A := primePlusFamily p hp
  let v := geometricPointsFieldMap Kₚ (AlgebraicClosure Kₚ) z A
    (primePlusRationalFiberPoint p hp ξ)
  have hv := geometricPointsFieldMap_arithmetic_fixed Kₚ z A
    (primePlusRationalFiberPoint p hp ξ) g
  change fieldPointMap Kₚ (AlgebraicClosure Kₚ) g ≫
      (geometricFiberPointsAddEquiv Kₚ A z v).toMul =
    (geometricFiberPointsAddEquiv Kₚ A z v).toMul
  calc
    fieldPointMap Kₚ (AlgebraicClosure Kₚ) g ≫
        (geometricFiberPointsAddEquiv Kₚ A z v).toMul =
      (geometricFiberPointsAddEquiv Kₚ A z
        (Additive.ofMul (Scheme.arithmeticFiberPointMap Kₚ z g ≫ v.toMul))).toMul :=
          (geometricFiberPointsAddEquiv_arithmetic Kₚ A z g v).symm
    _ = (geometricFiberPointsAddEquiv Kₚ A z v).toMul := by rw [hv]

end HilbertModularity.Hypergeometric
