/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.25.8 (1): Gorensteinness at a point ascends through a locally
finite-type base change when the original morphism has locally Noetherian fibres. -/
@[stacks 0C07] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt.pullback_of_isPullback :
    ∀ {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
      (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
      (x' : X'), f.gorensteinAt (g' x') → f'.gorensteinAt x')

/- Lemma 48.25.8 (2): Gorensteinness descends from a base change at a point
where the original morphism is flat. -/
@[stacks 0C07] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt.of_isPullback_of_flatAt :
    ∀ {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
      (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
      (x' : X'), f.flatAt (g' x') → f'.gorensteinAt x' →
        f.gorensteinAt (g' x'))

/- Lemma 48.25.8 (3): Gorensteinness descends from a base change when the base
morphism is flat at the image of the chosen point. -/
@[stacks 0C07] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt.of_isPullback_of_flatAt_base :
    ∀ {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g)
      (h_fibers : LocallyNoetherianFibers f) [LocallyOfFiniteType g]
      (x' : X'), g.flatAt (f' x') → f'.gorensteinAt x' →
        f.gorensteinAt (g' x'))
