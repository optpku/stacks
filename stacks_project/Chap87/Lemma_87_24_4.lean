/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.BaseChange
import StacksCheckRecall

/-!
# Base change of finite-type morphisms of formal algebraic spaces

The base change of a finite-type morphism of formal algebraic spaces by any
morphism of formal algebraic spaces is again of finite type. The same holds
for morphisms locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 87.24.4: A base change of a finite type morphism is finite type.
The same holds for locally of finite type. -/
@[stacks 0AQ5] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.finiteType_isStableUnderBaseChange :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.FormalAlgebraicSpace.FiniteType S :
          CategoryTheory.MorphismProperty ((CategoryTheory.Over S)ᵒᵖ ⥤ Type u)))

#check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.instIsStableUnderBaseChange :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType S :
        CategoryTheory.MorphismProperty ((CategoryTheory.Over S)ᵒᵖ ⥤ Type u)))
