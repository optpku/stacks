/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein

/-!
# Base change of Gorenstein morphisms of algebraic spaces

In a cartesian square of algebraic spaces, Gorensteinness at a point ascends
along a locally finite-type base change when the original morphism has
locally Noetherian fibres, and descends if either the original morphism is
flat at the image point or the base morphism is flat at the image of the
chosen point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GorensteinAt

/-- If `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square
Gorensteinness of `f` at the image of `x'` implies Gorensteinness of the
base change `f'` at `x'`. -/
theorem pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hg : GorensteinAt f (Points.map g' x')) :
    GorensteinAt f' x' :=
  sorry

/-- If `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness
of `f` at the image of `x'` together with Gorensteinness of the base change
`f'` at `x'` imply Gorensteinness of `f` at that image. -/
theorem of_isPullback_of_flatAt {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt f (Points.map g' x'))
    (hg : GorensteinAt f' x') :
    GorensteinAt f (Points.map g' x') :=
  sorry

/-- If `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness
of `g` at the image of `x'` in `|Y'|` together with Gorensteinness of the
base change `f'` at `x'` imply Gorensteinness of `f` at the image of `x'`. -/
theorem of_isPullback_of_flatAt_base {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt g (Points.map f' x'))
    (hg : GorensteinAt f' x') :
    GorensteinAt f (Points.map g' x') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GorensteinAt
