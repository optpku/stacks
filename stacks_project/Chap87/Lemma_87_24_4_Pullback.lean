/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.BaseChange

/-!
# Base change of finite-type morphisms of formal algebraic spaces

Finite-type morphisms and locally-of-finite-type morphisms of formal algebraic
spaces are stable under arbitrary base change. This module records the
morphism-level pullback companions for `FiniteType` and the existing
`LocallyOfFiniteType` class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.FiniteType.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → FormalAlgebraicSpace.FiniteType g →
      FormalAlgebraicSpace.FiniteType g')

#check (AlgebraicGeometry.FormalAlgebraicSpace.FiniteType.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (_hf : FormalAlgebraicSpace.FiniteType f) (g : Z ⟶ Y) [HasPullback f g],
    FormalAlgebraicSpace.FiniteType (pullback.snd f g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.finiteType_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FormalAlgebraicSpace.FiniteType f] [HasPullback f g],
    FormalAlgebraicSpace.FiniteType (pullback.snd f g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : (Over S)ᵒᵖ ⥤ Type u}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → FormalAlgebraicSpace.LocallyOfFiniteType g →
      FormalAlgebraicSpace.LocallyOfFiniteType g')

#check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (_hf : FormalAlgebraicSpace.LocallyOfFiniteType f) (g : Z ⟶ Y) [HasPullback f g],
    FormalAlgebraicSpace.LocallyOfFiniteType (pullback.snd f g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.instPullbackSnd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Z ⟶ Y)
    [FormalAlgebraicSpace.LocallyOfFiniteType f],
    FormalAlgebraicSpace.LocallyOfFiniteType (pullback.snd f g))
