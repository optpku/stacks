/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay.BaseChange
import StacksCheckRecall

/-!
# Base change of Cohen--Macaulay morphisms of algebraic spaces

In a cartesian square of algebraic spaces, Cohen--Macaulayness at a point
ascends along a locally finite-type base change when the original morphism
has locally Noetherian fibres, and descends if either the original morphism
is flat at the image point or the base morphism is flat at the image of the
chosen point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 76.26.6 (1): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square Cohen--Macaulayness
of `f` at the image of `x'` implies Cohen--Macaulayness of the base change
`f'` at `x'`. -/
@[stacks 0E0Z] #check
  (AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt.pullback_of_isPullback :
    ∀ {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hcm : CohenMacaulayAt f (Points.map g' x')),
    CohenMacaulayAt f' x')

/- Lemma 76.26.6 (2): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness of
`f` at the image of `x'` together with Cohen--Macaulayness of the base change
`f'` at `x'` imply Cohen--Macaulayness of `f` at that image. -/
@[stacks 0E0Z] #check
  (AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt.of_isPullback_of_flatAt :
    ∀ {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt f (Points.map g' x'))
    (hcm : CohenMacaulayAt f' x'),
    CohenMacaulayAt f (Points.map g' x'))

/- Lemma 76.26.6 (3): if `f : X ⟶ Y` has locally Noetherian fibres and
`g : Y' ⟶ Y` is locally of finite type, then in a cartesian square flatness of
`g` at `Points.map f' x'` together with Cohen--Macaulayness of the base
change `f'` at `x'` imply Cohen--Macaulayness of `f` at `Points.map g' x'`. -/
@[stacks 0E0Z] #check
  (AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt.of_isPullback_of_flatAt_base :
    ∀ {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt g (Points.map f' x'))
    (hcm : CohenMacaulayAt f' x'),
    CohenMacaulayAt f (Points.map g' x'))
