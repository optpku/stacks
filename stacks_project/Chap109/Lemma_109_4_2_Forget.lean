module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap109.Lemma_109_4_1_PolarizedCurves

/-!
# The forgetful 1-morphism PolarizedCurves ⟶ Curves

A polarized curve family `(X ⟶ S, L)` forgets the line bundle and is viewed as
a family of curves over the terminal scheme. This module packages that functor
as a 1-morphism of categories fibred in groupoids over `Over (⊤_ Scheme)`, at
Hom-universe `u + 1`. PolarizedCurves itself has Hom-universe `u`, so the
groupoid-fibration packaging uses `ULiftHom`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open CategoryTheory.Limits CategoryTheory.ObjectProperty
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- Membership in PolarizedCurves is equivalent to the forgotten family having
relative dimension at most 1 as an object of Curves. -/
theorem mem_iff_toCurves (x : Polarized.Obj) :
    mem x ↔
      Curves.relativeDimensionLE (⊤_ Scheme.{u}) 1 (Polarized.toFpFlatProper.obj x) :=
  sorry

/-- Forgetting the line bundle of a polarized curve family yields an object of
relative dimension at most 1 in `FpFlatProperGroupoids`. -/
theorem toCurves_property (P : Obj) :
    Curves.relativeDimensionLE (⊤_ Scheme.{u}) 1 (Polarized.toFpFlatProper.obj P.obj) :=
  sorry

/-- The forgetful functor PolarizedCurves ⥤ Curves sending a polarized curve
family `(X ⟶ S, L)` to the underlying family `X ⟶ S` over the terminal
scheme. -/
def toCurves : Obj ⥤ Curves.Obj (⊤_ Scheme.{u}) where
  obj P :=
    { obj := Polarized.toFpFlatProper.obj P.obj
      property := toCurves_property P }
  map φ := homMk (Polarized.toFpFlatProper.map (inclusion.map φ))
  map_id := sorry
  map_comp := sorry

/-- The underlying `FpFlatProperGroupoids` object of `toCurves.obj P` is the
image of the underlying polarized object under `Polarized.toFpFlatProper`. -/
theorem toCurves_obj (P : Obj) :
    (toCurves.obj P).obj = Polarized.toFpFlatProper.obj P.obj :=
  sorry

/-- The morphism map of `toCurves` is `Polarized.toFpFlatProper` applied to the
underlying polarized morphism. -/
theorem toCurves_map {P Q : Obj} (φ : P ⟶ Q) :
    (toCurves.map φ).hom = Polarized.toFpFlatProper.map (inclusion.map φ) :=
  sorry

/-- `toCurves` sends `mk x` to the forgotten family of `x`. -/
theorem toCurves_obj_mk (x : Polarized.Obj) [Scheme.Hom.RelativeDimensionLE x.hom 1] :
    (toCurves.obj (mk x)).obj = Polarized.toFpFlatProper.obj x :=
  sorry

/-- The universe-lifted projection of PolarizedCurves to `Over (⊤_ Scheme)`. -/
def toGroupoidsProjection : ULiftHom.{u + 1} Obj ⥤ Over (⊤_ Scheme.{u}) :=
  (ULiftHom.down : ULiftHom.{u + 1} Obj ⥤ Obj) ⋙ p ⋙ Polarized.asOverTerminal

/-- The universe-lifted projection of PolarizedCurves is fibred in groupoids. -/
instance instIsFiberedInGroupoids_toGroupoids :
    Functor.IsFibered.InGroupoids toGroupoidsProjection :=
  sorry

/-- PolarizedCurves, bundled as a category fibred in groupoids over
`Over (⊤_ Scheme)` at Hom-universe `u + 1`. -/
def toGroupoids :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over (⊤_ Scheme.{u})) :=
  Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} toGroupoidsProjection

/-- The projection of `toGroupoids` is `toGroupoidsProjection`. -/
theorem toGroupoids_p : toGroupoids.p = toGroupoidsProjection :=
  sorry

/-- The universe-lifted total functor of the forgetful 1-morphism
PolarizedCurves ⟶ Curves. -/
def toCurvesFunctor : ULiftHom.{u + 1} Obj ⥤ Curves.Obj (⊤_ Scheme.{u}) :=
  (ULiftHom.down : ULiftHom.{u + 1} Obj ⥤ Obj) ⋙ toCurves

/-- The 1-morphism PolarizedCurves ⟶ Curves, packaged as a morphism of
categories fibred in groupoids over `Over (⊤_ Scheme)`. The underlying functor
is the universe lift of `toCurves`. -/
def toCurvesHom : toGroupoids ⟶ Curves.toGroupoids (⊤_ Scheme.{u}) :=
  Groupoids.ofBasedFunctor
    { toFunctor := toCurvesFunctor
      w := sorry }

/-- The underlying functor of `toCurvesHom` is the universe lift of `toCurves`. -/
theorem toCurvesHom_toFunctor : Groupoids.toFunctor toCurvesHom = toCurvesFunctor :=
  sorry

/-- `toCurvesHom` lies strictly over `Over (⊤_ Scheme)`. -/
theorem toCurvesHom_comm :
    Groupoids.toFunctor toCurvesHom ⋙ Curves.p (⊤_ Scheme.{u}) =
      toGroupoids.p :=
  sorry

end AlgebraicGeometry.PolarizedCurves
