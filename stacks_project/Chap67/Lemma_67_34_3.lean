/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.BaseChange

/-! Fibre dimensions after base change of algebraic spaces. -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

/- Lemma 67.34.3 (1): Relative dimension is invariant under base change. -/
@[stacks 04NS] #check (AlgebraicGeometry.AlgebraicSpace.fiberDimensionAt_eq_of_isPullback :
  ∀ {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hpb : IsPullback g' f' f g)
    (x' : Points X'),
    fiberDimensionAt f' x' = fiberDimensionAt f (Points.map g' x'))

/- Lemma 67.34.3 (2): Fibre-stalk dimension and transcendence degree have a common natural increment. -/
@[stacks 04NS] #check (AlgebraicGeometry.AlgebraicSpace.FiberDimension.exists_increment_of_isPullback :
  ∀
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hpb : IsPullback g' f' f g) (x' : Points X'),
    ∃ n : ℕ,
      fiberStalkDimAt f' x' = fiberStalkDimAt f (Points.map g' x') + n ∧
        residueFieldTranscendenceDegreeAt f (Points.map g' x') =
          residueFieldTranscendenceDegreeAt f' x' + n)

/- Lemma 67.34.3 (3): Every compatible pair has a lift preserving both invariants. -/
@[stacks 04NS] #check (AlgebraicGeometry.AlgebraicSpace.FiberDimension.exists_lift_of_isPullback :
  ∀
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hpb : IsPullback g' f' f g) (x : Points X) (y' : Points Y')
    (hxy : Points.map f x = Points.map g y'),
    ∃ x' : Points X',
      Points.map g' x' = x ∧
        Points.map f' x' = y' ∧
          fiberStalkDimAt f' x' = fiberStalkDimAt f x ∧
            residueFieldTranscendenceDegreeAt f' x' = residueFieldTranscendenceDegreeAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.fiberStalkDimAt_le_of_isPullback :
  ∀ {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hpb : IsPullback g' f' f g)
    (x' : Points X'),
    fiberStalkDimAt f (Points.map g' x') ≤ fiberStalkDimAt f' x')

#check (AlgebraicGeometry.AlgebraicSpace.residueFieldTranscendenceDegreeAt_le_of_isPullback :
  ∀ {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hpb : IsPullback g' f' f g)
    (x' : Points X'),
    residueFieldTranscendenceDegreeAt f' x' ≤ residueFieldTranscendenceDegreeAt f (Points.map g' x'))

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimensionAt_eq_of_pullback_snd :
  ∀ {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) [HasPullback f g] (x' : Points (pullback f g)),
    fiberDimensionAt (pullback.snd f g) x' =
      fiberDimensionAt f (Points.map (pullback.fst f g) x'))
