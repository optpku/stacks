/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Isomorphism algebraic spaces of an algebraic stack

For fibre objects `x, y` of an algebraic stack `X` over a scheme `T`, the
isomorphism presheaf `Isom_X(x, y)` is transported along the iterated slice
equivalence to an algebraic space over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Isom

/-- The scheme `T` viewed as an algebraic space over itself. -/
abbrev selfSpace {S : Scheme.{u}} (T : Over S) : AlgebraicSpace T.left :=
  AlgebraicSpace.ofOver (Over.mk (𝟙 T.left))

/-- The isomorphism presheaf `Isom_X(x, y)` on schemes over `T`. -/
def isomOverLeft {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (x y : X.p.Fiber T) : (Over T.left)ᵒᵖ ⥤ Type u :=
  T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf X.p x y

/-- `isomOverLeft x y` is the slice transport of `Functor.isomorphismPresheaf X.p x y`. -/
theorem isomOverLeft_eq {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (x y : X.p.Fiber T) :
    isomOverLeft x y =
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf X.p x y :=
  sorry

/-- Universe-raised comparison of `isomOverLeft` with the `ULift` isomorphism presheaf. -/
def isomOverLeft_uliftIso {S : Scheme.{u}} {X : GroupoidsOver S} {T : Over S}
    (x y : X.p.Fiber T) :
    isomOverLeft x y ⋙ uliftFunctor.{u + 1, u} ≅
      T.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheafULift X.p x y :=
  Iso.refl _

/-- The algebraic space over `T` representing `Isom_X(x, y)`. -/
def isomSpace {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) : AlgebraicSpace T.left :=
  AlgebraicSpace.ofFunctor (isomOverLeft x y) sorry sorry sorry

/-- The functor of points of `isomSpace x y` is `isomOverLeft x y`. -/
theorem isomSpace_functorOfPoints {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) :
    (isomSpace x y).functorOfPoints = isomOverLeft x y :=
  sorry

/-- The unique structure morphism from `Isom_X(x, y)` to `T` as an algebraic
space over itself. -/
def isomOverHom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    isomSpace x y ⟶ selfSpace T where
  app W := ↾fun _ ↦ Over.homMk W.unop.hom
  naturality := sorry

/-- Evaluating `isomOverHom x y` at a test scheme returns the unique morphism
to `T`. -/
theorem isomOverHom_app {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {T : Over S} (x y : X.p.Fiber T) (W : (Over T.left)ᵒᵖ)
    (s : (isomSpace x y).functorOfPoints.obj W) :
    (isomOverHom x y).app W s = Over.homMk W.unop.hom :=
  sorry

/-- `Isom_X(x, y)` as an algebraic space over `T`, with unique structure morphism
to `T`. -/
def isomOver {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) : Over (selfSpace T) :=
  Over.mk (isomOverHom x y)

/-- The underlying algebraic space of `isomOver x y` is `isomSpace x y`. -/
theorem isomOver_left {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    (isomOver x y).left = isomSpace x y :=
  sorry

/-- The structure morphism of `isomOver x y` is `isomOverHom x y`. -/
theorem isomOver_hom {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T) :
    (isomOver x y).hom = isomOverHom x y :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Isom
