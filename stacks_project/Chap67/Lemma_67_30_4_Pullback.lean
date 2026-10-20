/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange

/-!
# Base change of flat morphisms of algebraic spaces

Flat morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`Flat` class from Definition 67.30.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Flat.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → Flat g → Flat g')

#check (AlgebraicGeometry.AlgebraicSpace.Flat.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    Flat f → ∀ (g : Z ⟶ Y) [HasPullback f g], Flat (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.flat_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Flat f] [HasPullback f g],
    Flat (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
