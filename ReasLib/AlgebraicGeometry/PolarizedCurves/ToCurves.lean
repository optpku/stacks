/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Surjective
public import ReasLib.AlgebraicGeometry.Curve.Family
public import ReasLib.AlgebraicGeometry.PolarizedCurves.Family
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

/-!
# The forgetful 1-morphism PolarizedCurves ⟶ Curves

A polarized curve family `(X ⟶ S, L)` forgets the line bundle and is viewed as a family of
curves over the terminal scheme. This module packages that functor as a 1-morphism of
categories fibred in groupoids over `Over (⊤_ Scheme)`, at Hom-universe `u + 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open CategoryTheory.Limits
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- Forgetting the line bundle of a polarized curve family yields a proper flat finitely
presented scheme family of relative dimension at most 1. -/
theorem toCurves_property (P : Obj) :
    IsProper P.hom ∧ Flat P.hom ∧ Scheme.Hom.FinitePresentation P.hom ∧
      Scheme.Hom.RelativeDimensionLE P.hom 1 :=
  sorry

/-- The forgetful functor PolarizedCurves ⥤ Curves sending a polarized curve family
`(X ⟶ S, L)` to the underlying family `X ⟶ S` over the terminal scheme. -/
def toCurves : Obj ⥤ Curves.Obj (⊤_ Scheme.{u}) where
  obj P :=
    ⟨asOverTerminal.obj P.S, P.X, P.hom,
      ⟨P.isProper, ⟨P.isFlat, ⟨P.finitePresentation, P.relativeDimensionLE⟩⟩⟩⟩
  map φ :=
    ⟨Hom.map φ, asOverTerminal.map (Hom.base φ), ⟨sorry⟩⟩
  map_id := sorry
  map_comp := sorry

/-- The universe-lifted projection of PolarizedCurves to `Over (⊤_ Scheme)`. -/
def toGroupoidsProjection : ULiftHom.{u + 1} Obj ⥤ Over (⊤_ Scheme.{u}) :=
  (ULiftHom.down : ULiftHom.{u + 1} Obj ⥤ Obj) ⋙ p ⋙ asOverTerminal

/-- The universe-lifted projection of PolarizedCurves is fibred in groupoids. -/
instance instIsFiberedInGroupoids_toGroupoids :
    Functor.IsFibered.InGroupoids toGroupoidsProjection :=
  sorry

/-- PolarizedCurves, bundled as a category fibred in groupoids over `Over (⊤_ Scheme)` at
Hom-universe `u + 1`. -/
def toGroupoids :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over (⊤_ Scheme.{u})) :=
  Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} toGroupoidsProjection

/-- The projection of `toGroupoids` is `toGroupoidsProjection`. -/
theorem toGroupoids_p : toGroupoids.p = toGroupoidsProjection :=
  Groupoids.ofFunctor.p toGroupoidsProjection

/-- The universe-lifted total functor of the forgetful 1-morphism PolarizedCurves ⟶ Curves. -/
def toCurvesFunctor : ULiftHom.{u + 1} Obj ⥤ ULiftHom.{u + 1} (Curves.Obj (⊤_ Scheme.{u})) :=
  (ULiftHom.down : ULiftHom.{u + 1} Obj ⥤ Obj) ⋙ toCurves ⋙ ULiftHom.up

/-- The 1-morphism PolarizedCurves ⟶ Curves, packaged as a morphism of categories fibred in
groupoids over `Over (⊤_ Scheme)`. The underlying functor is the universe lift of `toCurves`. -/
def toCurvesHom : toGroupoids ⟶ Curves.toGroupoids (⊤_ Scheme.{u}) :=
  Groupoids.ofBasedFunctor
    { toFunctor := toCurvesFunctor
      w := sorry }

/-- The underlying functor of `toCurvesHom` is the universe lift of `toCurves`. -/
theorem toCurvesHom_toFunctor :
    Groupoids.toFunctor toCurvesHom = toCurvesFunctor :=
  Groupoids.ofBasedFunctor.toFunctor _

/-- `toCurvesHom` lies strictly over `Over (⊤_ Scheme)`. -/
theorem toCurvesHom_comm :
    Groupoids.toFunctor toCurvesHom ⋙ (Curves.toGroupoids (⊤_ Scheme.{u})).p =
      toGroupoids.p :=
  Groupoids.comm toCurvesHom

/-- The 1-morphism PolarizedCurves ⟶ Curves is smooth. -/
instance instSmooth_toCurvesHom : CohStack.Hom.Smooth toCurvesHom :=
  sorry

/-- The 1-morphism PolarizedCurves ⟶ Curves is surjective. -/
instance instSurjective_toCurvesHom : CohStack.Hom.Surjective toCurvesHom :=
  sorry

end AlgebraicGeometry.PolarizedCurves
