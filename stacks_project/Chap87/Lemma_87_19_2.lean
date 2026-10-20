/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory

/- Lemma 87.19.2 (1): A base change of a morphism representable by algebraic
spaces is representable by algebraic spaces. -/
@[stacks 0APZ] #check (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.isStableUnderBaseChange :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces S))

/- Companion schemes clause: A base change of a morphism representable by
schemes is representable by schemes. -/
#check (CategoryTheory.Functor.relativelyRepresentable.isStableUnderBaseChange
    (yoneda : Over _ ⥤ ((Over _)ᵒᵖ ⥤ Type u)) :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      ((yoneda : Over S ⥤ ((Over S)ᵒᵖ ⥤ Type u)).relativelyRepresentable))
