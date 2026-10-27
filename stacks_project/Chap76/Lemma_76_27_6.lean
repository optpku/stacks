/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 76.27.6 (1): Gorensteinness at a point ascends along a locally
finite-type base change when the original morphism has locally Noetherian fibres. -/
@[stacks 0E18] #check
  (AlgebraicGeometry.AlgebraicSpace.GorensteinAt.pullback_of_isPullback :
    ∀ {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hg : GorensteinAt f (Points.map g' x')),
    GorensteinAt f' x')

/- Lemma 76.27.6 (2): Gorensteinness descends from a base change at a point
where the original morphism is flat. -/
@[stacks 0E18] #check
  (AlgebraicGeometry.AlgebraicSpace.GorensteinAt.of_isPullback_of_flatAt :
    ∀ {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt f (Points.map g' x'))
    (hg : GorensteinAt f' x'),
    GorensteinAt f (Points.map g' x'))

/- Lemma 76.27.6 (3): Gorensteinness descends from a base change when the base
morphism is flat at the image of the chosen point. -/
@[stacks 0E18] #check
  (AlgebraicGeometry.AlgebraicSpace.GorensteinAt.of_isPullback_of_flatAt_base :
    ∀ {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
    [LocallyNoetherianFibers f] [LocallyOfFiniteType g] (x' : Points X')
    (hflat : FlatAt g (Points.map f' x'))
    (hg : GorensteinAt f' x'),
    GorensteinAt f (Points.map g' x'))
